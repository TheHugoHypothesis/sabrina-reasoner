import Lean.Data.Json
import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.Normalize
import Sabrina.OWL2.Profile
import Sabrina.OWL2.EL
import Sabrina.OWL2.SROIQD.Termination.SourceImportConformance
import Sabrina.OWL2.SROIQD.Termination.ExactQueryDecision

/-! CLI JSON wire interface (`sabrina-ofn-query-v1`) accepting W3C OWL 2
    Functional-Style Syntax (`.ofn`) documents, optional multi-document
    `Import(...)` libraries, and standalone query axioms.

    At runtime, extracts the syntactically ⊥-local module (`Profile.extractBotModule`,
    proved conservative via `extractBotModule_entails_iff`), profiles both the full
    ontology and the minimal module into the least sufficient OWL 2 DL fragment,
    and dispatches to the fastest verified engine (`el-polynomial` for EL++ modules,
    `sroiqd-tableau` for ranked expressive problems). Consistency checks can
    also use verified grounding or ranked bounds on unranked object hierarchies. -/

namespace Sabrina.CLI.OFNQuery

open Lean Sabrina.OWL2 Sabrina.OWL2.FunctionalSyntax Sabrina.OWL2.Normalize
open Sabrina.OWL2.SROIQD Sabrina.OWL2.Datatypes Sabrina.OWL2.Profile Sabrina.OWL2.EL
open Sabrina.ALC (InclusionVerdict roleClosure)

def requestFormat := "sabrina-ofn-query-v1"

private def encodeFloatVal : FloatVal → Json
  | .negInf => toJson "-INF"
  | .posInf => toJson "INF"
  | .nan => toJson "NaN"
  | .negZero => toJson "-0.0"
  | .posZero => toJson "0.0"
  | .finite q => toJson s!"{q.num}/{q.den}"

private def encodeValue : Value → Json
  | .boolean b => toJson [toJson "boolean", toJson b]
  | .number q => toJson [toJson "number", toJson s!"{q.num}/{q.den}"]
  | .irrational q => toJson [toJson "irrational-witness", toJson s!"{q.num}/{q.den}"]
  | .float fv => toJson [toJson "float", encodeFloatVal fv]
  | .double fv => toJson [toJson "double", encodeFloatVal fv]
  | .plainLiteral s "" => toJson [toJson "string", toJson s]
  | .plainLiteral s lang => toJson [toJson "plain-literal", toJson s, toJson lang]
  | .anyURI s => toJson [toJson "anyURI", toJson s]
  | .hexBinary bs => toJson [toJson "hexBinary", toJson (bs.map fun b => toJson b.toNat)]
  | .base64Binary bs => toJson [toJson "base64Binary", toJson (bs.map fun b => toJson b.toNat)]
  | .dateTime dt => toJson [toJson "dateTime", toJson s!"{dt.epochSeconds.num}/{dt.epochSeconds.den}", toJson dt.hasTimezone, toJson dt.timezoneOffset]
  | .xmlLiteral s => toJson [toJson "xmlLiteral", toJson s]

private def encodeEvidence (limits : Limits) : Evidence → Json
  | .model m =>
    let base := [
      ("kind", toJson "model"),
      ("worlds", toJson (m.graph.additionalWorlds + 1)),
      ("atoms", toJson (m.graph.atoms.map fun (p, x) => #[toJson p, toJson x.val])),
      ("edges", toJson (m.graph.edges.map fun (r, x, y) => #[toJson r, toJson x.val, toJson y.val]))]
    let withNoms := if m.nominals.isEmpty then base
      else base ++ [("nominals", toJson (m.nominals.map fun (a, x) => #[toJson a, toJson x.val]))]
    let withAnons := if m.anons.isEmpty then withNoms
      else withNoms ++ [("anons", toJson (m.anons.map fun ((d, l), x) => #[toJson s!"{d}#_:{l}", toJson x.val]))]
    let withData := if m.dataEdges.isEmpty then withAnons
      else withAnons ++ [("data_edges", toJson (m.dataEdges.map fun (dp, x, v) => #[toJson dp, toJson x.val, encodeValue v]))]
    Json.mkObj withData
  | .refutation depth =>
    Json.mkObj [("kind", toJson "refutation"), ("basis", toJson "sroiqd-tableau-v1"),
      ("depth", toJson depth), ("world_limit", toJson limits.worlds)]

private def response (verdict : String) (verified : Bool) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("format", toJson "sabrina-alc-result-v1"), ("verdict", toJson verdict),
    ("lean_verified", toJson verified)] ++ fields)

private def verdictName : InclusionVerdict → String
  | .entailed => "ENTAILED"
  | .refuted => "REFUTED"
  | .independent => "SENTENCE_INDEPENDENT"
  | .inconsistent => "INCONSISTENT_ONTOLOGY"

private def checkRoleRestrictions (p : Problem) : Option String := Id.run do
  let closed := roleClosure p.rules
  for r in p.simpleRoles do
    if let some src := RoleChains.SimpleRoles.firstComposite closed p.chains r then
      let orient := if src.2 then "inverse of " else ""
      return some s!"non-simple role {r.1} used where a simple role is required; composite subrole: {orient}{src.1}"
  if !RoleChains.checkRegular (RoleChains.inferRank p.rules p.chains) p.rules p.chains then
    return some "no validated rank for this role hierarchy"
  return none

private def parseImportsObj (j : Json) : Except String (List (IRI × String)) := do
  let obj ← j.getObj?
  let mut out : List (IRI × String) := []
  for (k, v) in obj.toList do
    let text ← v.getStr?
    out := (k, text) :: out
  return out.reverse

private def parseLimitsObj (j : Json) : Except String Limits := do
  let obj ← j.getObj?
  let mut limits : Limits := {}
  if let some v := obj.get? "max_worlds" then
    limits := { limits with worlds := ← v.getNat? }
  if let some v := obj.get? "max_depth" then
    limits := { limits with depth := ← v.getNat? }
  if let some v := obj.get? "max_visits" then
    limits := { limits with visits := ← v.getNat? }
  else if let some v := obj.get? "max_steps" then
    limits := { limits with visits := ← v.getNat? }
  return limits

private def encodeLimits (limits : Limits) : Json :=
  Json.mkObj [
    ("worlds", toJson limits.worlds),
    ("depth", toJson limits.depth),
    ("visits", toJson limits.visits)]

private def isOptionsObj (j : Json) : Bool :=
  match j.getObj? with
  | .ok obj =>
    obj.contains "max_worlds" || obj.contains "max_depth" ||
    obj.contains "max_visits" || obj.contains "max_steps"
  | .error _ => false

private def encodeProfile (qp : QueryProfile) (engine : String) : Json :=
  Json.mkObj [
    ("full_fragment", toJson qp.fullFragment.name),
    ("module_fragment", toJson qp.moduleFragment.name),
    ("full_axioms", toJson qp.fullAxiomCount),
    ("module_axioms", toJson qp.moduleAxiomCount),
    ("engine_used", toJson engine),
    ("full_features", toJson qp.fullFeatures.activeNames),
    ("module_features", toJson qp.moduleFeatures.activeNames)]

private def elProofSize : ELProof → Nat
  | .refl _ | .top _ | .crRefl _ _ => 1
  | .bot _ _ p | .cr1 _ _ _ p | .cr3 _ _ _ _ p | .cr10 _ _ _ _ p => 1 + elProofSize p
  | .cr2 _ _ _ _ p1 p2 | .cr4 _ _ _ _ _ p1 p2 | .cr5 _ _ _ p1 p2 | .cr11 _ _ _ _ _ _ p1 p2 =>
    1 + elProofSize p1 + elProofSize p2

private def encodeELModel (m : ELModel) : Json :=
  Json.mkObj [
    ("kind", toJson "model"),
    ("basis", toJson "el-canonical-model-v1"),
    ("worlds", toJson m.nodes.length),
    ("nodes", toJson m.nodes),
    ("atoms", toJson (m.clsFacts.map fun (c, u) => #[toJson c, toJson u])),
    ("edges", toJson (m.edges.map fun (r, u, v) => #[toJson r, toJson u, toJson v]))]

private def encodeELProof (pf : ELProof) : Json :=
  Json.mkObj [
    ("kind", toJson "refutation"),
    ("basis", toJson "el-proof-v1"),
    ("steps", toJson (elProofSize pf))]

private def elVerdictToResult : ELVerdict → String × Json
  | .inconsistent pf => ("INCONSISTENT_ONTOLOGY", encodeELProof pf)
  | .entailed pf => ("ENTAILED", encodeELProof pf)
  | .refuted cm pf => ("REFUTED", Json.mkObj [("counterexample", encodeELModel cm), ("inclusion", encodeELProof pf)])
  | .independent cm inc => ("SENTENCE_INDEPENDENT", Json.mkObj [("counterexample", encodeELModel cm), ("inclusion", encodeELModel inc)])

private def elVerdictKind : ELVerdict → InclusionVerdict
  | .inconsistent _ => .inconsistent
  | .entailed _ => .entailed
  | .refuted _ _ => .refuted
  | .independent _ _ => .independent

private def checkELRoleRegularity (axs : List ELAxiom) : Option String := Id.run do
  let mut rules : Sabrina.ALC.RoleTheory := []
  let mut chains : List RoleChains.Chain := []
  for ax in axs do
    match ax with
    | .roleSub r s => rules := ⟨(r, false), (s, false)⟩ :: rules
    | .roleChain r1 r2 s => chains := RoleChains.Chain.named [r1, r2] s :: chains
    | _ => pure ()
  if !RoleChains.checkRegular (RoleChains.inferRank rules chains) rules chains then
    return some "no validated rank for this role hierarchy"
  return none

private def tryObjectConsistency (ofnText : String) (lib : List (IRI × String))
    (qp : QueryProfile) (context : List (String × Json)) : Option (UInt32 × Json) := do
  let (basis, (_, sat)) ←
    (SROIQD.Termination.SourceImport.decideUniversalSourceClosure? ofnText lib).map (("universal-grounding", ·)) <|>
    (SROIQD.Termination.SourceImport.decideObjectSourceClosure? ofnText lib).map (("ranked-role-bounds", ·))
  let verdict := if sat then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
  return (0, response verdict true
    (("decision_basis", toJson (basis ++ "-v1")) ::
      ("profile", encodeProfile qp basis) :: context))

private def usesReal (p : Problem) : Bool :=
  p.allDataAtoms.any fun
    | .datatype t | .restriction t _ => t == owlReal
    | _ => false

private def runConsistency (id ofnText : String) (lib : List (IRI × String))
    (limits : Limits := {}) (allowExact : Bool := true) : UInt32 × Json := Id.run do
  if id.isEmpty then return (2, response "UNSUPPORTED" false [("reason", toJson "empty ontology ID")])
  let scope := Json.mkObj [("semantics", toJson "owl2-ofn-sroiqd"), ("id", toJson id)]
  let context := [("scope", scope)]
  let (_, ont) ← match resolveImports ofnText lib with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"OFN parse/import error: {err}") :: context))
  let qp := profileQuery ont none
  -- Fast path: polynomial EL++ consequence-based classifier
  if qp.moduleFragment == .el then
    if let some elAxs := normalizeEL ont then
      if let some err := checkELRoleRegularity elAxs then
        if let some verdict := tryObjectConsistency ofnText lib qp context then return verdict
        return (2, response "UNSUPPORTED" false (("reason", toJson err) :: ("profile", encodeProfile qp "el-polynomial") :: context))
      if let some res := decideELConsistency elAxs then
        let ctx := ("profile", encodeProfile qp "el-polynomial") :: context
        match res with
        | .inl m => return (0, response "SATISFIABLE" true (("certificate", encodeELModel m) :: ctx))
        | .inr pf => return (0, response "INCONSISTENT_ONTOLOGY" true (("certificate", encodeELProof pf) :: ctx))
  let ctx := ("profile", encodeProfile qp "sroiqd-tableau") :: context
  let some (_, p) := normalizeWithDefs ont | return (2, response "UNSUPPORTED" false
    (("reason", toJson "ontology contains cyclic datatype definitions or constructors outside the normalized SROIQ(D) fragment") :: ctx))
  let hasReal := usesReal p
  let hasOrderedData := p.allDataAtoms.any SROIQD.Termination.WiderData.isOrderedExactAtom
  let hasStringFacets := p.allDataAtoms.any SROIQD.Termination.WiderData.isStringFacetExtraAtom
  let hasBuiltInDataProp := p.allDataProps.any fun dp => dp == topDataProperty || dp == bottomDataProperty
  if allowExact && (hasReal || hasOrderedData || hasStringFacets || hasBuiltInDataProp) then
    if let some (_, sat) := SROIQD.Termination.SourceImport.decideRealSourceClosure? ofnText lib then
      let basis :=
        if hasReal then "sroiqd-real-reduction"
        else if hasOrderedData then "sroiqd-ordered-data"
        else if hasStringFacets then "sroiqd-string-facets"
        else "sroiqd-builtin-data-prop"
      let verdict := if sat then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
      return (0, response verdict true
        (("decision_basis", toJson (basis ++ "-v1")) ::
          ("profile", encodeProfile qp basis) :: context))
  if let some err := checkRoleRestrictions p then
    if let some verdict := tryObjectConsistency ofnText lib qp context then return verdict
    return (2, response "UNSUPPORTED" false (("reason", toJson err) :: ctx))
  let some ev := propose p limits | return (2, response "UNKNOWN" false
    (("reason", toJson "SROIQ(D) search could not certify consistency within interactive limits") ::
     ("limits", encodeLimits limits) :: ctx))
  if !checkConsistency p limits.worlds ev then
    return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) evidence failed checking") :: ctx))
  let verdict := if ev.isModel then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
  return (0, response verdict true (("certificate", encodeEvidence limits ev) :: ctx))

private def tryELQuery (elAxs : List ELAxiom) (qAx : Axiom) : Option (String × Json) :=
  match qAx with
  | .subClassOf (.named a) (.named b) =>
    (decideELSub elAxs a b).map elVerdictToResult
  | .disjointClasses [.named a, .named b] =>
    let aux := s!"{elAuxPrefix}query_disj"
    let axs' := .sub2 a b aux :: .sub1 aux a :: .sub1 aux b :: elAxs
    (decideELSub axs' aux nothing).map elVerdictToResult
  | .equivalentClasses [.named a, .named b] => do
    let v1 ← decideELSub elAxs a b
    let v2 ← decideELSub elAxs b a
    let (_, c1) := elVerdictToResult v1
    let (_, c2) := elVerdictToResult v2
    let k := match elVerdictKind v1, elVerdictKind v2 with
      | .inconsistent, _ | _, .inconsistent => InclusionVerdict.inconsistent
      | .entailed, .entailed => .entailed
      | .refuted, _ | _, .refuted => .refuted
      | _, _ => .independent
    some (verdictName k, Json.mkObj [("forward", c1), ("backward", c2)])
  | _ => none

private def tryObjectSubclass (ofnText queryText : String) (lib : List (IRI × String))
    (qp : QueryProfile) (context : List (String × Json)) : Option (UInt32 × Json) := do
  let (basis, (_, _, verdict)) ←
    (SROIQD.Termination.SourceImport.decideUniversalSourceSubclass? ofnText queryText lib).map (("universal-grounding", ·)) <|>
    (SROIQD.Termination.SourceImport.decideObjectSourceSubclass? ofnText queryText lib).map (("ranked-role-bounds", ·))
  return (0, response (verdictName verdict) true
    (("decision_basis", toJson (basis ++ "-v1")) ::
      ("profile", encodeProfile qp basis) :: context))

private def tryExactQuery (ofnText queryText : String) (lib : List (IRI × String))
    (qp : QueryProfile) (context : List (String × Json)) (basis : String) : Option (UInt32 × Json) := do
  let (_, _, verdict) ← SROIQD.Termination.ExactQuery.decideRealSourceQuery? ofnText queryText lib
  return (0, response (verdictName verdict) true
    (("decision_basis", toJson (basis ++ "-v1")) ::
      ("profile", encodeProfile qp basis) :: context))

private def runQuery (id ofnText queryText : String) (lib : List (IRI × String))
    (limits : Limits := {}) (allowExact : Bool := true) : UInt32 × Json := Id.run do
  if id.isEmpty then return (2, response "UNSUPPORTED" false [("reason", toJson "empty ontology ID")])
  let scope := Json.mkObj [("semantics", toJson "owl2-ofn-sroiqd"), ("id", toJson id)]
  let context := [("scope", scope), ("query", toJson queryText)]
  let (prefixes, ont) ← match resolveImports ofnText lib with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"OFN parse/import error: {err}") :: context))
  let qAx ← match parseQueryAxiom prefixes queryText with
    | .ok a => pure a
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"OFN query parse error: {err}") :: context))
  let qp := profileQuery ont (some qAx)
  let tryGrounding := fun () => tryObjectSubclass ofnText queryText lib qp context
  -- Validate global OWL 2 DL structural/role restrictions on the full ontology
  -- (skipped only when full ontology is pure EL++, where regularity is checked directly in O(|RBox|))
  let fullCheck : Option (DatatypeDefs × Problem) ←
    if qp.fullFragment == .el then
      pure none
    else
      match normalizeWithDefs ont with
      | none => return (2, response "UNSUPPORTED" false
          (("reason", toJson "ontology contains cyclic datatype definitions or constructors outside the normalized SROIQ(D) fragment") ::
           ("profile", encodeProfile qp "sroiqd-tableau") :: context))
      | some dp =>
        if let some err := checkRoleRestrictions dp.2 then
          if let some verdict := tryGrounding () then return verdict
          return (2, response "UNSUPPORTED" false
            (("reason", toJson err) :: ("profile", encodeProfile qp "sroiqd-tableau") :: context))
        pure (some dp)
  -- Fast path: polynomial EL++ consequence-based classifier on the extracted ⊥-local module
  if qp.moduleFragment == .el then
    if let some elAxs := normalizeEL qp.extractedModule then
      if let some err := checkELRoleRegularity elAxs then
        if let some verdict := tryGrounding () then return verdict
        return (2, response "UNSUPPORTED" false
          (("reason", toJson err) :: ("profile", encodeProfile qp "el-polynomial") :: context))
      if let some (verdict, cert) := tryELQuery elAxs qAx then
        let ctx := ("profile", encodeProfile qp "el-polynomial") :: context
        return (0, response verdict true (("certificate", cert) :: ctx))
  -- General SROIQ(D) path on the extracted ⊥-local module (provably conservative via Profile.extractBotModule_entails_iff)
  let ctx := ("profile", encodeProfile qp "sroiqd-tableau") :: context
  let (defs, p) ← match normalizeWithDefs qp.extractedModule with
    | some dp => pure dp
    | none =>
      match fullCheck with
      | some dp => pure dp
      | none => return (2, response "UNSUPPORTED" false
          (("reason", toJson "ontology contains cyclic datatype definitions or constructors outside the normalized SROIQ(D) fragment") :: ctx))
  let some incs := queryToInclusions defs qAx | return (2, response "UNSUPPORTED" false
    (("reason", toJson "query must be SubClassOf, binary EquivalentClasses, binary DisjointClasses, ClassAssertion, (Negative)ObjectPropertyAssertion, (Negative)DataPropertyAssertion, binary SameIndividual, or binary DifferentIndividuals") :: ctx))
  -- Route wider datatypes, string/URI facets, and built-in data properties through
  -- the kernel-verified exact real/wider query solver before bounded search.
  let probeProblems : List Problem :=
    { p with tbox := incs ++ p.tbox } :: fullCheck.toList.map Prod.snd
  let hasReal := probeProblems.any usesReal
  let hasOrderedData := probeProblems.any fun pr =>
    pr.allDataAtoms.any SROIQD.Termination.WiderData.isOrderedExactAtom
  let hasStringFacets := probeProblems.any fun pr =>
    pr.allDataAtoms.any SROIQD.Termination.WiderData.isStringFacetExtraAtom
  let hasBuiltInDataProp := probeProblems.any fun pr =>
    pr.allDataProps.any fun dp => dp == topDataProperty || dp == bottomDataProperty
  if allowExact && (hasReal || hasOrderedData || hasStringFacets || hasBuiltInDataProp) then
    let basis :=
      if hasReal then "sroiqd-real-query"
      else if hasOrderedData then "sroiqd-ordered-data-query"
      else if hasStringFacets then "sroiqd-string-facets-query"
      else "sroiqd-builtin-data-prop-query"
    if let some res := tryExactQuery ofnText queryText lib qp context basis then
      return res
  match incs with
  | [q] =>
    if let some err := checkRoleRestrictions (inclusionProblem p q) then
      if let some verdict := tryGrounding () then return verdict
      return (2, response "UNSUPPORTED" false (("reason", toJson err) :: ctx))
    let pair := do
      let a ← propose (counterProblem p q) limits
      let b ← propose (inclusionProblem p q) limits
      return (⟨a, b⟩ : InclusionEvidence)
    let some ev := pair | do
      if allowExact then
        if let some res := tryExactQuery ofnText queryText lib qp context "sroiqd-exact-query" then
          return res
      return (2, response "UNKNOWN" false
        (("reason", toJson "SROIQ(D) search could not produce both certificates within interactive limits") ::
         ("limits", encodeLimits limits) :: ctx))
    if !checkInclusion p q limits.worlds ev then
      return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) inclusion evidence failed checking") :: ctx))
    let cert := Json.mkObj [
      ("counterexample", encodeEvidence limits ev.counterexample),
      ("inclusion", encodeEvidence limits ev.inclusion)]
    return (0, response (verdictName ev.verdict) true (("certificate", cert) :: ctx))
  | [q1, q2] =>
    for q in [q1, q2] do
      if let some err := checkRoleRestrictions (inclusionProblem p q) then
        return (2, response "UNSUPPORTED" false (("reason", toJson err) :: ctx))
    let pair1 := do
      return (⟨← propose (counterProblem p q1) limits, ← propose (inclusionProblem p q1) limits⟩ : InclusionEvidence)
    let pair2 := do
      return (⟨← propose (counterProblem p q2) limits, ← propose (inclusionProblem p q2) limits⟩ : InclusionEvidence)
    let (some ev1, some ev2) := (pair1, pair2) | do
      if allowExact then
        if let some res := tryExactQuery ofnText queryText lib qp context "sroiqd-exact-query" then
          return res
      return (2, response "UNKNOWN" false
        (("reason", toJson "SROIQ(D) search could not certify equivalence within interactive limits") ::
         ("limits", encodeLimits limits) :: ctx))
    if !checkInclusion p q1 limits.worlds ev1 || !checkInclusion p q2 limits.worlds ev2 then
      return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) equivalence evidence failed checking") :: ctx))
    let cert := Json.mkObj [
      ("forward", Json.mkObj [("counterexample", encodeEvidence limits ev1.counterexample),
                              ("inclusion", encodeEvidence limits ev1.inclusion)]),
      ("backward", Json.mkObj [("counterexample", encodeEvidence limits ev2.counterexample),
                               ("inclusion", encodeEvidence limits ev2.inclusion)])]
    let verdict := verdictName (equivVerdict ev1 ev2)
    return (0, response verdict true (("certificate", cert) :: ctx))
  | _ => return (2, response "UNSUPPORTED" false (("reason", toJson "unsupported query reduction arity") :: ctx))

def run (j : Json) : UInt32 × Json := Id.run do
  let .ok fields := j.getArr? | return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected JSON array [\"sabrina-ofn-query-v1\", ontologyID, ofnText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])
  match fields.toList with
  | [.str _, .str id, .str ofnText] =>
    return runConsistency id ofnText []
  | [.str _, .str id, .str ofnText, .str queryText] =>
    return runQuery id ofnText queryText []
  | [.str _, .str id, .str ofnText, obj@(.obj _)] =>
    if isOptionsObj obj then
      match parseLimitsObj obj with
      | .ok lim => return runConsistency id ofnText [] lim false
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
    else
      match parseImportsObj obj with
      | .ok lib => return runConsistency id ofnText lib
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
  | [.str _, .str id, .str ofnText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseLimitsObj optJson with
    | .ok lib, .ok lim => return runConsistency id ofnText lib lim false
    | .error err, _ => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
    | _, .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
  | [.str _, .str id, .str ofnText, .str queryText, obj@(.obj _)] =>
    if isOptionsObj obj then
      match parseLimitsObj obj with
      | .ok lim => return runQuery id ofnText queryText [] lim false
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
    else
      match parseImportsObj obj with
      | .ok lib => return runQuery id ofnText queryText lib
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
  | [.str _, .str id, .str ofnText, .str queryText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseLimitsObj optJson with
    | .ok lib, .ok lim => return runQuery id ofnText queryText lib lim false
    | .error err, _ => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
    | _, .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
  | _ => return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected [\"sabrina-ofn-query-v1\", id, ofnText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])

end Sabrina.CLI.OFNQuery
