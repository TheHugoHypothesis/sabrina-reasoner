import Lean.Data.Json
import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.Normalize
import Sabrina.OWL2.Profile
import Sabrina.OWL2.FastLocality
import Sabrina.OWL2.EL
import Sabrina.OWL2.IncrementalABox
import Sabrina.OWL2.Classification
import Sabrina.OWL2.SROIQD.Termination.ExtendedQueryDecision

/-! Persistent JSON-lines session server (`sabrina-session`) for incremental
    ABox inference over a compiled TBox/RBox.

    Protocol (one JSON object per stdin line, one JSON object per stdout line):
      * `{"cmd": "load_tbox", "id": "...", "ofn": "...", "imports": {...}}`
      * `{"cmd": "assert", "id": "f1", "ofn": "ClassAssertion(...)"}`
      * `{"cmd": "retract", "id": "f1"}`
      * `{"cmd": "query", "ofn": "ClassAssertion(...)"}`
      * `{"cmd": "check_consistency"}`
      * `{"cmd": "status"}`
      * `{"cmd": "quit"}`

    Runs in `el-incremental` mode (true incremental delta propagation + DRed
    justification-tracked retraction) whenever the compiled TBox is in `EL++`
    and active assertions are ground `ABoxFact`s, and seamlessly uses cached
    TBox/RBox + ⊥-locality module extraction (`sroiqd-cached` mode) for full
    `SROIQ(D)` ontologies/assertions. -/

namespace Sabrina.CLI.SessionMain

open Lean Sabrina.OWL2 Sabrina.OWL2.FunctionalSyntax Sabrina.OWL2.Normalize
open Sabrina.OWL2.SROIQD Sabrina.OWL2.Profile Sabrina.OWL2.EL Sabrina.OWL2.IncrementalABox
open Sabrina.ALC (InclusionVerdict roleClosure)

private structure SessionState where
  loaded : Bool := false
  tboxId : String := ""
  prefixes : PrefixMap := []
  declarations : List EntityDecl := []
  baseOnt : Ontology := []
  baseIndex : Option FastLocality.LocalityIndex := none
  fullFragment : Fragment := .el
  elState : Option IncrementalState := none
  -- Active ABox assertions stored by caller string ID → (numeric Tag, Axiom)
  nextTag : Nat := 1
  aboxByName : List (String × Nat × Axiom) := []
  sroiqdOnlyCount : Nat := 0

private def toABoxFact? : Axiom → Option ABoxFact
  | .classAssertion (.named c) (.named a) => some (.cls c a)
  | .objectAssertion (.named r) (.named a) (.named b) =>
    if r == topObjectProperty || r == bottomObjectProperty then none else some (.obj r a b)
  | .negativeObjectAssertion (.named r) (.named a) (.named b) =>
    if r == topObjectProperty || r == bottomObjectProperty then none else some (.negObj r a b)
  | _ => none

private def checkRoleRestrictions (p : Problem) : Option String := Id.run do
  let closed := roleClosure p.rules
  for r in p.simpleRoles do
    if let some src := RoleChains.SimpleRoles.firstComposite closed p.chains r then
      let orient := if src.2 then "inverse of " else ""
      return some s!"non-simple role {r.1} used where a simple role is required; composite subrole: {orient}{src.1}"
  if !RoleChains.checkRegular (RoleChains.inferRank p.rules p.chains) p.rules p.chains then
    return some "no validated rank for this role hierarchy"
  return none

private def parseImportsField (obj : Std.TreeMap.Raw String Json compare) :
    Except String (List (IRI × String)) := do
  match obj.get? "imports" with
  | none | some .null => return []
  | some j =>
    let impObj ← j.getObj?
    let mut out : List (IRI × String) := []
    for (k, v) in impObj.toList do
      out := (k, ← v.getStr?) :: out
    return out.reverse

private def parseLimitsField (obj : Std.TreeMap.Raw String Json compare) : Limits := Id.run do
  let mut limits : Limits := {}
  if let some (.num n) := obj.get? "max_worlds" then
    if n.mantissa > 0 && n.exponent == 0 then limits := { limits with worlds := n.mantissa.toNat }
  if let some (.num n) := obj.get? "max_steps" then
    if n.mantissa > 0 && n.exponent == 0 then limits := { limits with visits := n.mantissa.toNat }
  return limits

private def currentMode (st : SessionState) : String :=
  if st.elState.isSome && st.sroiqdOnlyCount == 0 then "el-incremental" else "sroiqd-cached"

private def activeABox (st : SessionState) : Ontology :=
  st.aboxByName.map (fun (_, _, ax) => ax)

private def activeOnt (st : SessionState) : Ontology :=
  st.baseOnt ++ activeABox st

private def verdictName : InclusionVerdict → String
  | .entailed => "ENTAILED"
  | .refuted => "REFUTED"
  | .independent => "SENTENCE_INDEPENDENT"
  | .inconsistent => "INCONSISTENT_ONTOLOGY"

private def encodeABoxModel (m : ABoxModel) : Json :=
  Json.mkObj [
    ("kind", toJson "model"),
    ("basis", toJson "el-abox-model-v1"),
    ("worlds", toJson m.base.nodes.length),
    ("individuals", toJson (m.indMap.map fun (a, u) => #[toJson a, toJson u])),
    ("atoms", toJson (m.base.clsFacts.map fun (c, u) => #[toJson c, toJson u])),
    ("edges", toJson (m.base.edges.map fun (r, u, v) => #[toJson r, toJson u, toJson v]))]

private def encodeABoxProof (pf : ABoxProof) : Json :=
  Json.mkObj [
    ("kind", toJson "refutation"),
    ("basis", toJson "el-abox-proof-v1"),
    ("steps", toJson pf.size)]

private def encodeSROIQDEvidence (limits : Limits) : Evidence → Json
  | .model m =>
    Json.mkObj [
      ("kind", toJson "model"),
      ("basis", toJson "sroiqd-model-v1"),
      ("worlds", toJson (m.graph.additionalWorlds + 1)),
      ("atoms", toJson (m.graph.atoms.map fun (p, x) => #[toJson p, toJson x.val])),
      ("edges", toJson (m.graph.edges.map fun (r, x, y) => #[toJson r, toJson x.val, toJson y.val]))]
  | .refutation depth =>
    Json.mkObj [
      ("kind", toJson "refutation"),
      ("basis", toJson "sroiqd-tableau-v1"),
      ("depth", toJson depth),
      ("world_limit", toJson limits.worlds)]

private def handleLoadTBox (obj : Std.TreeMap.Raw String Json compare) : SessionState × Json := Id.run do
  let id := match obj.get? "id" with | some (.str s) => s | _ => "session-tbox"
  let ofnText ← match obj.get? "ofn", obj.get? "ontology" with
    | some (.str s), _ => pure s
    | _, some (.str s) => pure s
    | _, _ => return ({}, Json.mkObj [
      ("ok", toJson false), ("error", toJson "load_tbox requires string field 'ofn' or 'ontology'")])
  let lib ← match parseImportsField obj with
    | .ok l => pure l
    | .error err => return ({}, Json.mkObj [("ok", toJson false), ("error", toJson s!"invalid imports: {err}")])
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto ofnText lib false with
    | .ok r => pure r
    | .error err => return ({}, Json.mkObj [("ok", toJson false), ("error", toJson s!"parse/import error: {err}")])
  let prefixes := closure.prefixes
  let ont := closure.ontology
  let fp := profileOntology ont
  let frag := fp.leastFragment
  -- Validate global restrictions once at TBox load time
  let mut elState : Option IncrementalState := none
  if frag == .el then
    if let some elAxs := normalizeEL ont then
      let mut rules : Sabrina.ALC.RoleTheory := []
      let mut chains : List RoleChains.Chain := []
      for ax in elAxs do
        match ax with
        | .roleSub r s => rules := ⟨(r, false), (s, false)⟩ :: rules
        | .roleChain r1 r2 s => chains := RoleChains.Chain.named [r1, r2] s :: chains
        | _ => pure ()
      if !RoleChains.checkRegular (RoleChains.inferRank rules chains) rules chains then
        return ({}, Json.mkObj [("ok", toJson false), ("error", toJson "no validated rank for this role hierarchy")])
      elState := some (IncrementalState.init (compileEL elAxs))
  else
    match normalizeWithDefs ont with
    | none => return ({}, Json.mkObj [("ok", toJson false), ("error", toJson "unsupported constructors or cyclic datatype definitions")])
    | some (_, p) =>
      if let some err := checkRoleRestrictions p then
        return ({}, Json.mkObj [("ok", toJson false), ("error", toJson err)])
  let st : SessionState := {
    loaded := true
    tboxId := id
    prefixes := prefixes
    declarations := closure.declarations
    baseOnt := ont
    baseIndex := some (FastLocality.LocalityIndex.build ont)
    fullFragment := frag
    elState := elState
    nextTag := 1
    aboxByName := []
    sroiqdOnlyCount := 0
  }
  let res := Json.mkObj [
    ("ok", toJson true),
    ("cmd", toJson "load_tbox"),
    ("id", toJson id),
    ("tbox_axioms", toJson ont.length),
    ("fragment", toJson frag.name),
    ("mode", toJson (currentMode st))]
  return (st, res)

private def handleAssert (st : SessionState) (obj : Std.TreeMap.Raw String Json compare) : SessionState × Json := Id.run do
  if !st.loaded then
    return (st, Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")])
  let some (.str ofnText) := obj.get? "ofn" | return (st, Json.mkObj [
    ("ok", toJson false), ("error", toJson "assert requires string field 'ofn'")])
  let ax ← match parseQueryAxiom st.prefixes ofnText with
    | .ok a => pure a
    | .error err => return (st, Json.mkObj [("ok", toJson false), ("error", toJson s!"OFN assertion parse error: {err}")])
  let tag := st.nextTag
  let name := match obj.get? "id" with | some (.str s) => s | _ => s!"a{tag}"
  -- If an assertion with the same name already exists, reject to keep provenance unique
  if st.aboxByName.any (fun (n, _, _) => n == name) then
    return (st, Json.mkObj [("ok", toJson false), ("error", toJson s!"assertion id '{name}' already exists; retract it first")])
  let aboxByName := (name, tag, ax) :: st.aboxByName
  let mut st' := { st with nextTag := tag + 1, aboxByName }
  let mut deltaDerived : Nat := 0
  let mut consistentOpt : Option Bool := none
  match st'.elState, toABoxFact? ax with
  | some inc, some fact =>
    let (inc', d) := inc.assertFact tag fact
    deltaDerived := d
    consistentOpt := some inc'.clashProof.isNone
    st' := { st' with elState := some inc' }
  | _, _ =>
    st' := { st' with sroiqdOnlyCount := st'.sroiqdOnlyCount + 1 }
  let res := Json.mkObj [
    ("ok", toJson true),
    ("cmd", toJson "assert"),
    ("id", toJson name),
    ("mode", toJson (currentMode st')),
    ("active_abox_count", toJson st'.aboxByName.length),
    ("delta_derived_count", toJson deltaDerived),
    ("consistent_hint", match consistentOpt with | some b => toJson b | none => Json.null)]
  return (st', res)

private def handleRetract (st : SessionState) (obj : Std.TreeMap.Raw String Json compare) : SessionState × Json := Id.run do
  if !st.loaded then
    return (st, Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")])
  let some (.str name) := obj.get? "id" | return (st, Json.mkObj [
    ("ok", toJson false), ("error", toJson "retract requires string field 'id'")])
  let some (_, tag, ax) := st.aboxByName.find? (fun (n, _, _) => n == name) | return (st, Json.mkObj [
    ("ok", toJson false), ("error", toJson s!"assertion id '{name}' not found")])
  let remaining := st.aboxByName.filter (fun (n, _, _) => n != name)
  let mut st' := { st with aboxByName := remaining }
  let mut invalidated : Nat := 0
  let mut rederived : Nat := 0
  let mut consistentOpt : Option Bool := none
  match st'.elState, toABoxFact? ax with
  | some inc, some _ =>
    let (inc', inv, red) := inc.retractId tag
    invalidated := inv
    rederived := red
    consistentOpt := some inc'.clashProof.isNone
    st' := { st' with elState := some inc' }
  | _, _ =>
    st' := { st' with sroiqdOnlyCount := st'.sroiqdOnlyCount - 1 }
  let res := Json.mkObj [
    ("ok", toJson true),
    ("cmd", toJson "retract"),
    ("id", toJson name),
    ("mode", toJson (currentMode st')),
    ("active_abox_count", toJson st'.aboxByName.length),
    ("invalidated_count", toJson invalidated),
    ("rederived_count", toJson rederived),
    ("consistent_hint", match consistentOpt with | some b => toJson b | none => Json.null)]
  return (st', res)

private def handleCheckConsistency (st : SessionState) (obj : Std.TreeMap.Raw String Json compare) : Json := Id.run do
  if !st.loaded then
    return Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")]
  let limits := parseLimitsField obj
  if st.sroiqdOnlyCount == 0 then
    if let some inc := st.elState then
      if let some res := inc.checkConsistency then
        match res with
        | .inl m =>
          return Json.mkObj [
            ("ok", toJson true), ("cmd", toJson "check_consistency"),
            ("verdict", toJson "SATISFIABLE"), ("lean_verified", toJson true),
            ("mode", toJson "el-incremental"), ("certificate", encodeABoxModel m)]
        | .inr pf =>
          return Json.mkObj [
            ("ok", toJson true), ("cmd", toJson "check_consistency"),
            ("verdict", toJson "INCONSISTENT_ONTOLOGY"), ("lean_verified", toJson true),
            ("mode", toJson "el-incremental"), ("certificate", encodeABoxProof pf)]
  -- Cached SROIQ(D) path: extract ⊥-local module (provably equisatisfiable via FastLocality.extractBotModuleWithIndex_sat_iff)
  let ont := activeOnt st
  let mod := match st.baseIndex with
    | some baseIdx =>
      let idx := if st.aboxByName.isEmpty then baseIdx else baseIdx.extend (activeABox st)
      (FastLocality.extractBotModuleWithIndex idx ont Sig.empty).1
    | none => (FastLocality.extractBotModuleFast ont Sig.empty).1
  let some (_, p) := normalizeWithDefs mod | return Json.mkObj [
    ("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false),
    ("reason", toJson "active ontology outside normalized SROIQ(D)")]
  if let some err := checkRoleRestrictions p then
    return Json.mkObj [("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false), ("reason", toJson err)]
  let some ev := propose p limits | return Json.mkObj [
    ("ok", toJson true), ("cmd", toJson "check_consistency"),
    ("verdict", toJson "UNKNOWN"), ("lean_verified", toJson false),
    ("mode", toJson "sroiqd-cached"), ("reason", toJson "SROIQ(D) consistency search hit limits")]
  if !checkConsistency p limits.worlds ev then
    return Json.mkObj [("ok", toJson false), ("verdict", toJson "REJECTED"), ("lean_verified", toJson false)]
  let verdict := if ev.isModel then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
  return Json.mkObj [
    ("ok", toJson true), ("cmd", toJson "check_consistency"),
    ("verdict", toJson verdict), ("lean_verified", toJson true),
    ("mode", toJson "sroiqd-cached"), ("certificate", encodeSROIQDEvidence limits ev)]

private def handleQuery (st : SessionState) (obj : Std.TreeMap.Raw String Json compare) : Json := Id.run do
  if !st.loaded then
    return Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")]
  let some (.str qText) := obj.get? "ofn" | return Json.mkObj [
    ("ok", toJson false), ("error", toJson "query requires string field 'ofn'")]
  let qAx ← match parseQueryAxiom st.prefixes qText with
    | .ok a => pure a
    | .error err => return Json.mkObj [("ok", toJson false), ("error", toJson s!"OFN query parse error: {err}")]
  let limits := parseLimitsField obj
  -- Fast path: live EL++ incremental ABox state
  if st.sroiqdOnlyCount == 0 then
    if let some inc := st.elState then
      match qAx with
      | .classAssertion (.named c) (.named a) =>
        if let some res := inc.queryClassAssertion c a then
          match res with
          | .inl (.inl pf) =>
            return Json.mkObj [
              ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
              ("verdict", toJson "INCONSISTENT_ONTOLOGY"), ("lean_verified", toJson true),
              ("mode", toJson "el-incremental"), ("certificate", encodeABoxProof pf)]
          | .inl (.inr pf) =>
            return Json.mkObj [
              ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
              ("verdict", toJson "ENTAILED"), ("lean_verified", toJson true),
              ("mode", toJson "el-incremental"), ("certificate", encodeABoxProof pf)]
          | .inr cm =>
            -- Check if asserting ClassAssertion(c, a) causes inconsistency → REFUTED vs SENTENCE_INDEPENDENT
            let (incPlus, _) := inc.assertFact 0 (.cls c a)
            if let some pfClash := incPlus.clashProof then
              if checkABoxProof incPlus.compiled.tbox incPlus.activeFacts pfClash .clash then
                return Json.mkObj [
                  ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
                  ("verdict", toJson "REFUTED"), ("lean_verified", toJson true),
                  ("mode", toJson "el-incremental"),
                  ("certificate", Json.mkObj [("counterexample", encodeABoxModel cm), ("inclusion", encodeABoxProof pfClash)])]
            let mPlus := incPlus.extractModel [a]
            if checkABoxModel incPlus.compiled.tbox incPlus.activeFacts mPlus then
              return Json.mkObj [
                ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
                ("verdict", toJson "SENTENCE_INDEPENDENT"), ("lean_verified", toJson true),
                ("mode", toJson "el-incremental"),
                ("certificate", Json.mkObj [("counterexample", encodeABoxModel cm), ("inclusion", encodeABoxModel mPlus)])]
      | .objectAssertion (.named r) (.named a) (.named b) =>
        if let some pf := inc.clashProof then
          if checkABoxProof inc.compiled.tbox inc.activeFacts pf .clash then
            return Json.mkObj [
              ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
              ("verdict", toJson "INCONSISTENT_ONTOLOGY"), ("lean_verified", toJson true),
              ("mode", toJson "el-incremental"), ("certificate", encodeABoxProof pf)]
        else if let some pf := inc.derivedRel.get? (r, a, b) then
          if checkABoxProof inc.compiled.tbox inc.activeFacts pf (.edge r a b) then
            return Json.mkObj [
              ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
              ("verdict", toJson "ENTAILED"), ("lean_verified", toJson true),
              ("mode", toJson "el-incremental"), ("certificate", encodeABoxProof pf)]
      | _ => pure ()
  -- General cached SROIQ(D) path over ⊥-local module of (baseOnt ++ activeABox)
  let ont := activeOnt st
  let qp := match st.baseIndex with
    | some baseIdx =>
      let idx := if st.aboxByName.isEmpty then baseIdx else baseIdx.extend (activeABox st)
      FastLocality.profileQueryWithIndex idx ont (some qAx)
    | none => FastLocality.profileQueryFast ont (some qAx)
  let some (defs, p) := normalizeWithDefs qp.extractedModule | return Json.mkObj [
    ("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false),
    ("reason", toJson "active ontology outside normalized SROIQ(D)")]
  let some incs := queryToInclusions defs qAx | return Json.mkObj [
    ("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false),
    ("reason", toJson "unsupported query axiom form")]
  match incs with
  | [q] =>
    if let some err := checkRoleRestrictions (inclusionProblem p q) then
      return Json.mkObj [("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false), ("reason", toJson err)]
    let pair := do
      let a ← propose (counterProblem p q) limits
      let b ← propose (inclusionProblem p q) limits
      return (⟨a, b⟩ : InclusionEvidence)
    let some ev := pair | return Json.mkObj [
      ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
      ("verdict", toJson "UNKNOWN"), ("lean_verified", toJson false),
      ("mode", toJson "sroiqd-cached"), ("reason", toJson "SROIQ(D) search hit limits")]
    if !checkInclusion p q limits.worlds ev then
      return Json.mkObj [("ok", toJson false), ("verdict", toJson "REJECTED"), ("lean_verified", toJson false)]
    let cert := Json.mkObj [
      ("counterexample", encodeSROIQDEvidence limits ev.counterexample),
      ("inclusion", encodeSROIQDEvidence limits ev.inclusion)]
    return Json.mkObj [
      ("ok", toJson true), ("cmd", toJson "query"), ("query", toJson qText),
      ("verdict", toJson (verdictName ev.verdict)), ("lean_verified", toJson true),
      ("mode", toJson "sroiqd-cached"),
      ("module_axioms", toJson qp.moduleAxiomCount),
      ("certificate", cert)]
  | _ => return Json.mkObj [
    ("ok", toJson false), ("verdict", toJson "UNSUPPORTED"), ("lean_verified", toJson false),
    ("reason", toJson "session query expects single-inclusion query form")]

private def handleClassify (st : SessionState) : Json :=
  if !st.loaded then
    Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")]
  else
    let ont := activeOnt st
    match Classification.classifyOntologyRuntime ont st.declarations with
    | some h =>
      Json.mkObj [
        ("ok", toJson true), ("cmd", toJson "classify"),
        ("lean_verified", toJson true),
        ("consistent", toJson h.consistent),
        ("classes", toJson h.classes),
        ("unsatisfiable", toJson h.unsatisfiable),
        ("subsumptions", toJson (h.subsumptions.map fun (a, b) => #[toJson a, toJson b])),
        ("equivalences", toJson h.equivalences),
        ("direct_parents", Json.mkObj (h.directParents.map fun (c, ps) => (c, toJson ps)))]
    | none =>
      Json.mkObj [("ok", toJson false), ("cmd", toJson "classify"), ("lean_verified", toJson false),
        ("error", toJson "active ontology outside exact classification fragment")]

private def handleRealize (st : SessionState) : Json :=
  if !st.loaded then
    Json.mkObj [("ok", toJson false), ("error", toJson "no TBox loaded; call load_tbox first")]
  else
    let ont := activeOnt st
    match Classification.realizeOntologyRuntime ont st.declarations with
    | some r =>
      Json.mkObj [
        ("ok", toJson true), ("cmd", toJson "realize"),
        ("lean_verified", toJson true),
        ("consistent", toJson r.consistent),
        ("individuals", toJson r.individuals),
        ("entries", toJson (r.entries.map fun e => Json.mkObj [
          ("individual", toJson e.individual),
          ("all_types", toJson e.allTypes),
          ("direct_types", toJson e.directTypes)]))]
    | none =>
      Json.mkObj [("ok", toJson false), ("cmd", toJson "realize"), ("lean_verified", toJson false),
        ("error", toJson "active ontology outside exact realization fragment")]

private def handleStatus (st : SessionState) : Json :=
  let (dCls, dRel) := match st.elState with
    | some inc => (inc.derivedCls.size, inc.derivedRel.size)
    | none => (0, 0)
  Json.mkObj [
    ("ok", toJson true),
    ("cmd", toJson "status"),
    ("loaded", toJson st.loaded),
    ("id", toJson st.tboxId),
    ("mode", toJson (currentMode st)),
    ("tbox_axioms", toJson st.baseOnt.length),
    ("active_abox_count", toJson st.aboxByName.length),
    ("derived_cls_count", toJson dCls),
    ("derived_rel_count", toJson dRel)]

def run (_args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st : SessionState := {}
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    let j ← match Json.parse trimmed with
      | .ok v => pure v
      | .error err =>
        stdout.putStrLn (Json.mkObj [("ok", toJson false), ("error", toJson s!"JSON parse error: {err}")]).compress
        stdout.flush
        continue
    let obj ← match j.getObj? with
      | .ok o => pure o
      | .error err =>
        stdout.putStrLn (Json.mkObj [("ok", toJson false), ("error", toJson s!"expected JSON object: {err}")]).compress
        stdout.flush
        continue
    let cmd := match obj.get? "cmd" with | some (.str s) => s | _ => ""
    match cmd with
    | "quit" | "exit" =>
      stdout.putStrLn (Json.mkObj [("ok", toJson true), ("cmd", toJson "quit")]).compress
      stdout.flush
      break
    | "load_tbox" =>
      let (st', resp) := handleLoadTBox obj
      st := st'
      stdout.putStrLn resp.compress
      stdout.flush
    | "assert" =>
      let (st', resp) := handleAssert st obj
      st := st'
      stdout.putStrLn resp.compress
      stdout.flush
    | "retract" =>
      let (st', resp) := handleRetract st obj
      st := st'
      stdout.putStrLn resp.compress
      stdout.flush
    | "query" =>
      stdout.putStrLn (handleQuery st obj).compress
      stdout.flush
    | "check_consistency" =>
      stdout.putStrLn (handleCheckConsistency st obj).compress
      stdout.flush
    | "classify" =>
      stdout.putStrLn (handleClassify st).compress
      stdout.flush
    | "realize" =>
      stdout.putStrLn (handleRealize st).compress
      stdout.flush
    | "status" =>
      stdout.putStrLn (handleStatus st).compress
      stdout.flush
    | other =>
      stdout.putStrLn (Json.mkObj [("ok", toJson false), ("error", toJson s!"unknown command '{other}'")]).compress
      stdout.flush
  return 0

end Sabrina.CLI.SessionMain
