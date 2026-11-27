import Lean.Data.Json
import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.Normalize
import Sabrina.OWL2.StrictOWL2DL
import Sabrina.OWL2.StrictTyping
import Sabrina.OWL2.Profile
import Sabrina.OWL2.FastLocality
import Sabrina.OWL2.EL
import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastClassification
import Sabrina.OWL2.Materialize
import Sabrina.OWL2.Justification
import Sabrina.OWL2.SWRLReduction
import Sabrina.OWL2.SROIQD.Termination.SourceImportConformance
import Sabrina.OWL2.SROIQD.Termination.ExactQueryDecision
import Sabrina.OWL2.SROIQD.Termination.ExtendedQueryDecision

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

def requestFormat     := "sabrina-ofn-query-v1"
def classifyFormat    := "sabrina-classify-v1"
def realizeFormat     := "sabrina-realize-v1"
def materializeFormat := "sabrina-materialize-v1"
def explainFormat     := "sabrina-explain-v1"

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
  if !RoleChains.checkInferredRank p.rules p.chains then
    return some "no validated rank for this role hierarchy"
  return none

private def parseImportsObj (j : Json) : Except String (List (IRI × String)) := do
  let obj ← j.getObj?
  let mut out : List (IRI × String) := []
  for (k, v) in obj.toList do
    let text ← v.getStr?
    out := (k, text) :: out
  return out.reverse

private structure QueryOptions where
  limits : Limits := {}
  hasAbsoluteWorldLimit : Bool := false
  hasCustomLimits : Bool := false
  strictOwl2DL : Bool := false

private def QueryOptions.limitsForProblem (opts : QueryOptions) (p : Problem) : Limits :=
  if opts.hasAbsoluteWorldLimit then opts.limits else Limits.forProblem p opts.limits

private def parseOptionsObj (j : Json) (cliStrict : Bool := false) : Except String QueryOptions := do
  let obj ← j.getObj?
  let mut limits : Limits := {}
  let mut hasCustomLimits := false
  let mut strictOwl2DL := cliStrict
  if let some v := obj.get? "max_worlds" then
    limits := { limits with worlds := ← v.getNat? }
    hasCustomLimits := true
  if let some v := obj.get? "max_depth" then
    limits := { limits with depth := ← v.getNat? }
    hasCustomLimits := true
  if let some v := obj.get? "max_visits" then
    limits := { limits with visits := ← v.getNat? }
    hasCustomLimits := true
  else if let some v := obj.get? "max_steps" then
    limits := { limits with visits := ← v.getNat? }
    hasCustomLimits := true
  if let some v := obj.get? "strict_owl2dl" then
    let b ← v.getBool?
    strictOwl2DL := strictOwl2DL || b
  return { limits, hasAbsoluteWorldLimit := obj.contains "max_worlds", hasCustomLimits, strictOwl2DL }

private def encodeLimits (limits : Limits) : Json :=
  Json.mkObj [
    ("worlds", toJson limits.worlds),
    ("depth", toJson limits.depth),
    ("visits", toJson limits.visits)]

private def isOptionsObj (j : Json) : Bool :=
  match j.getObj? with
  | .ok obj =>
    obj.contains "max_worlds" || obj.contains "max_depth" ||
    obj.contains "max_visits" || obj.contains "max_steps" ||
    obj.contains "strict_owl2dl"
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
  if !RoleChains.checkInferredRank rules chains then
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

private def declaredNamedInds (decls : List EntityDecl) : List IRI :=
  decls.filterMap fun d => if d.kind == .namedIndividual then some d.iri else none

private def lowerClosureSWRL (closure : ResolvedOFNClosure) (extraInds : List IRI := [])
    (extraForbidden : List IRI := []) :
    Except String (Ontology × List (Axiom × SWRL.SWRLRule) × Option IRI) := do
  if closure.rules.isEmpty then
    return (closure.ontology, [], none)
  let inds := SWRL.collectNamedIndividuals closure.ontology closure.rules
    (declaredNamedInds closure.declarations ++ extraInds)
  let (guardCls?, guardAxs, prov) ←
    SWRL.lowerSWRLRulesGuardedWithProvenance closure.ontology inds closure.rules extraForbidden
  return (closure.ontology ++ guardAxs ++ prov.map Prod.fst, prov, guardCls?)

private def renderJustificationWithRules (prov : List (Axiom × SWRL.SWRLRule))
    (guardCls? : Option IRI) (J : Ontology) : List String :=
  (J.filterMap fun ax =>
    if let some g := guardCls? then
      if SWRL.axiomHasClass g ax then
        (prov.lookup ax).map renderSWRLRule
      else
        some (match prov.lookup ax with | some r => renderSWRLRule r | none => renderAxiom ax)
    else
      some (match prov.lookup ax with | some r => renderSWRLRule r | none => renderAxiom ax)).eraseDups

private def runConsistency (id ofnText : String) (lib : List (IRI × String))
    (opts : QueryOptions) : UInt32 × Json := Id.run do
  let strictOwl2DL := opts.strictOwl2DL
  let allowExact := !opts.hasCustomLimits
  if id.isEmpty then return (2, response "UNSUPPORTED" false [("reason", toJson "empty ontology ID")])
  let scope := Json.mkObj [("semantics", toJson "owl2-ofn-sroiqd"), ("id", toJson id)]
  let baseContext := [("scope", scope)]
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto ofnText lib strictOwl2DL with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"parse/import error: {err}") :: baseContext))
  let ont := closure.ontology
  if strictOwl2DL then
    if let some err := StrictTyping.diagnoseStrictTypedOWL2DLWithRules closure.declarations closure.annotationAxioms ont closure.rules then
      return (2, response "UNSUPPORTED" false
        (("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson false) :: ("reason", toJson err) :: baseContext))
  let context := if strictOwl2DL then
      ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseContext
    else baseContext
  if !closure.rules.isEmpty then
    let swrlCtx := ("swrl_rules", toJson closure.rules.length) :: context
    let inds := SWRL.collectNamedIndividuals ont closure.rules (declaredNamedInds closure.declarations)
    match SWRL.decideWithSWRLFast? ont inds closure.rules with
    | .error err =>
      return (2, response "UNSUPPORTED" false (("reason", toJson err) :: swrlCtx))
    | .ok (some sat) =>
      let verdict := if sat then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
      return (0, response verdict true (("decision_basis", toJson "sroiqd-swrl-dl-safe-v1") :: swrlCtx))
    | .ok none =>
      return (2, response "UNKNOWN" false
        (("reason", toJson "SWRL + SROIQ(D) consistency check could not decide within limits") :: swrlCtx))
  let qp := FastLocality.profileQueryFast ont none
  -- Fast path: polynomial EL++ consequence-based classifier
  if qp.moduleFragment == .el then
    if let some elAxs := normalizeEL ont then
      if let some err := checkELRoleRegularity elAxs then
        if !strictOwl2DL then
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
  let limits := opts.limitsForProblem p
  let hasReal := usesReal p
  let hasOrderedData := p.allDataAtoms.any SROIQD.Termination.WiderData.isOrderedExactAtom
  let hasStringFacets := p.allDataAtoms.any SROIQD.Termination.WiderData.isStringFacetExtraAtom
  let hasBuiltInDataProp := p.allDataProps.any fun dp => dp == topDataProperty || dp == bottomDataProperty
  let widerAdmissibleForReal : Bool :=
    !hasReal ||
    (p.allDataLiterals.all (fun l => (Datatypes.decodeLiteral l).isSome) &&
     SROIQD.Termination.WiderData.widerAtomsAdmissible (.oneOf p.allDataLiterals :: p.allDataAtoms))
  let exactBasis? : Option String :=
    if hasReal then some "sroiqd-real-reduction"
    else if hasOrderedData then some "sroiqd-ordered-data"
    else if hasStringFacets then some "sroiqd-string-facets"
    else if hasBuiltInDataProp then some "sroiqd-builtin-data-prop"
    else none
  if allowExact && (hasBuiltInDataProp || !widerAdmissibleForReal) then
    let exactSat :=
      (SROIQD.Termination.SourceImport.decideRealSourceClosure? ofnText lib).map Prod.snd <|>
      SROIQD.Termination.WiderData.decideRealOntology? ont
    if let some sat := exactSat then
      let basis := exactBasis?.getD "sroiqd-exact-consistency"
      let verdict := if sat then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
      return (0, response verdict true
        (("decision_basis", toJson (basis ++ "-v1")) ::
          ("profile", encodeProfile qp basis) :: context))
  if let some err := checkRoleRestrictions p then
    if !strictOwl2DL then
      if let some verdict := tryObjectConsistency ofnText lib qp context then return verdict
    return (2, response "UNSUPPORTED" false (("reason", toJson err) :: ctx))
  let some ev := propose p limits | do
    if allowExact then
      let exactSat :=
        (SROIQD.Termination.SourceImport.decideRealSourceClosure? ofnText lib).map Prod.snd <|>
        SROIQD.Termination.WiderData.decideRealOntology? ont
      if let some sat := exactSat then
        let basis := exactBasis?.getD "sroiqd-exact-consistency"
        let verdict := if sat then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
        return (0, response verdict true
          (("decision_basis", toJson (basis ++ "-v1")) ::
            ("profile", encodeProfile qp basis) :: context))
    return (2, response "UNKNOWN" false
      (("reason", toJson "SROIQ(D) search could not certify consistency within interactive limits") ::
       ("limits", encodeLimits limits) :: ctx))
  if !checkConsistency p limits.worlds ev then
    return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) evidence failed checking") :: ctx))
  let verdict := if ev.isModel then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
  let basisFields := match exactBasis? with
    | some basis => [("decision_basis", toJson (basis ++ "-v1"))]
    | none => []
  return (0, response verdict true (basisFields ++ ("certificate", encodeEvidence limits ev) :: ctx))

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
    (ont : Ontology) (qAx : Axiom)
    (qp : QueryProfile) (context : List (String × Json)) (basis : String)
    (hasRules : Bool := false) : Option (UInt32 × Json) := do
  let verdict ←
    if hasRules then
      SROIQD.Termination.ExtendedQuery.classifyExtendedQueryWith Classification.fastConsistencyCheck ont qAx <|>
      SROIQD.Termination.ExtendedQuery.decideRealExtendedQuery? ont qAx
    else
      ((SROIQD.Termination.ExactQuery.decideRealSourceQuery? ofnText queryText lib).map fun (_, _, v) => v) <|>
      SROIQD.Termination.ExtendedQuery.decideRealExtendedQuery? ont qAx
  return (0, response (verdictName verdict) true
    (("decision_basis", toJson (basis ++ "-v1")) ::
      ("profile", encodeProfile qp basis) :: context))

private def runQuery (id ofnText queryText : String) (lib : List (IRI × String))
    (opts : QueryOptions) : UInt32 × Json := Id.run do
  let strictOwl2DL := opts.strictOwl2DL
  let allowExact := !opts.hasCustomLimits
  if id.isEmpty then return (2, response "UNSUPPORTED" false [("reason", toJson "empty ontology ID")])
  let scope := Json.mkObj [("semantics", toJson "owl2-ofn-sroiqd"), ("id", toJson id)]
  let baseContext := [("scope", scope), ("query", toJson queryText)]
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto ofnText lib strictOwl2DL with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"parse/import error: {err}") :: baseContext))
  let prefixes := closure.prefixes
  let rawOnt := closure.ontology
  let qAx ← match parseQueryAxiom prefixes queryText with
    | .ok a => pure a
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson s!"OFN query parse error: {err}") :: baseContext))
  if strictOwl2DL then
    if let some err := StrictTyping.diagnoseStrictTypedOWL2DLQuery closure.declarations closure.annotationAxioms rawOnt qAx <|>
          StrictTyping.diagnoseRuleTyping closure.declarations closure.annotationAxioms rawOnt closure.rules then
      return (2, response "UNSUPPORTED" false
        (("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson false) :: ("reason", toJson err) :: baseContext))
  let hasRules := !closure.rules.isEmpty
  let (ont, _, _) ← match lowerClosureSWRL closure (SWRL.axiomNamedInds qAx) (StrictTyping.axiomClasses qAx) with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false (("reason", toJson err) :: baseContext))
  let strictCtx := if strictOwl2DL then
      ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseContext
    else baseContext
  let context := if hasRules then ("swrl_rules", toJson closure.rules.length) :: strictCtx else strictCtx
  let qp := FastLocality.profileQueryFast ont (some qAx)
  let tryGrounding := fun () =>
    if strictOwl2DL || hasRules then none else tryObjectSubclass ofnText queryText lib qp context
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
  let limits := opts.limitsForProblem p
  let some incs := queryToInclusions defs qAx | do
    if allowExact then
      if let some verdict := SROIQD.Termination.ExtendedQuery.classifyExtendedQueryWith
          Classification.fastConsistencyCheck ont qAx then
        return (0, response (verdictName verdict) true
          (("decision_basis", toJson "sroiqd-extended-query-v1") ::
           ("profile", encodeProfile qp "sroiqd-extended-query") :: context))
    return (2, response "UNSUPPORTED" false
      (("reason", toJson "query axiom form is outside the supported exact query language") :: ctx))
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
  let widerAdmissibleForReal : Bool :=
    !hasReal ||
    probeProblems.all fun pr =>
      pr.allDataLiterals.all (fun l => (Datatypes.decodeLiteral l).isSome) &&
      SROIQD.Termination.WiderData.widerAtomsAdmissible (.oneOf pr.allDataLiterals :: pr.allDataAtoms)
  let exactBasis? : Option String :=
    if hasReal then some "sroiqd-real-query"
    else if hasOrderedData then some "sroiqd-ordered-data-query"
    else if hasStringFacets then some "sroiqd-string-facets-query"
    else if hasBuiltInDataProp then some "sroiqd-builtin-data-prop-query"
    else none
  let basisFields : List (String × Json) := match exactBasis? with
    | some b => [("decision_basis", toJson (b ++ "-v1"))]
    | none => []
  if allowExact && (hasBuiltInDataProp || !widerAdmissibleForReal) then
    if let some res := tryExactQuery ofnText queryText lib ont qAx qp context (exactBasis?.getD "sroiqd-exact-query") hasRules then
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
        if let some res := tryExactQuery ofnText queryText lib ont qAx qp context (exactBasis?.getD "sroiqd-exact-query") hasRules then
          return res
      return (2, response "UNKNOWN" false
        (("reason", toJson "SROIQ(D) search could not produce both certificates within interactive limits") ::
         ("limits", encodeLimits limits) :: ctx))
    if !checkInclusion p q limits.worlds ev then
      return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) inclusion evidence failed checking") :: ctx))
    let cert := Json.mkObj [
      ("counterexample", encodeEvidence limits ev.counterexample),
      ("inclusion", encodeEvidence limits ev.inclusion)]
    return (0, response (verdictName ev.verdict) true (basisFields ++ ("certificate", cert) :: ctx))
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
        if let some res := tryExactQuery ofnText queryText lib ont qAx qp context (exactBasis?.getD "sroiqd-exact-query") hasRules then
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

def run (j : Json) (cliStrict : Bool := false)
    (extraLib : List (IRI × String) := []) : UInt32 × Json := Id.run do
  let .ok fields := j.getArr? | return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected JSON array [\"sabrina-ofn-query-v1\", ontologyID, ofnText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])
  match fields.toList with
  | [.str _, .str id, .str ofnText] =>
    return runConsistency id ofnText extraLib { strictOwl2DL := cliStrict }
  | [.str _, .str id, .str ofnText, .str queryText] =>
    return runQuery id ofnText queryText extraLib { strictOwl2DL := cliStrict }
  | [.str _, .str id, .str ofnText, obj@(.obj _)] =>
    if isOptionsObj obj then
      match parseOptionsObj obj cliStrict with
      | .ok opts => return runConsistency id ofnText extraLib opts
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
    else
      match parseImportsObj obj with
      | .ok lib => return runConsistency id ofnText (lib ++ extraLib) { strictOwl2DL := cliStrict }
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
  | [.str _, .str id, .str ofnText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseOptionsObj optJson cliStrict with
    | .ok lib, .ok opts => return runConsistency id ofnText (lib ++ extraLib) opts
    | .error err, _ => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
    | _, .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
  | [.str _, .str id, .str ofnText, .str queryText, obj@(.obj _)] =>
    if isOptionsObj obj then
      match parseOptionsObj obj cliStrict with
      | .ok opts => return runQuery id ofnText queryText extraLib opts
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
    else
      match parseImportsObj obj with
      | .ok lib => return runQuery id ofnText queryText (lib ++ extraLib) { strictOwl2DL := cliStrict }
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
  | [.str _, .str id, .str ofnText, .str queryText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseOptionsObj optJson cliStrict with
    | .ok lib, .ok opts => return runQuery id ofnText queryText (lib ++ extraLib) opts
    | .error err, _ => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid imports map: {err}")])
    | _, .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"invalid options: {err}")])
  | _ => return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected [\"sabrina-ofn-query-v1\", id, ofnText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])

private def encodeClassHierarchy (h : Classification.ClassHierarchy) : Json :=
  Json.mkObj [
    ("consistent", toJson h.consistent),
    ("classes", toJson h.classes),
    ("unsatisfiable", toJson h.unsatisfiable),
    ("subsumptions", toJson (h.subsumptions.map fun (a, b) => #[toJson a, toJson b])),
    ("equivalences", toJson h.equivalences),
    ("direct_parents", Json.mkObj (h.directParents.map fun (c, ps) => (c, toJson ps)))]

private def encodeRealization (r : Classification.RealizationResult) : Json :=
  Json.mkObj [
    ("consistent", toJson r.consistent),
    ("individuals", toJson r.individuals),
    ("entries", toJson (r.entries.map fun e => Json.mkObj [
      ("individual", toJson e.individual),
      ("all_types", toJson e.allTypes),
      ("direct_types", toJson e.directTypes)]))]

private def parseServiceRequest (j : Json) (cliStrict : Bool) (extraLib : List (IRI × String)) :
    Except String (String × String × List (IRI × String) × Bool) := do
  let fields ← j.getArr?
  match fields.toList with
  | [.str _, .str id, .str docText] => return (id, docText, extraLib, cliStrict)
  | [.str _, .str id, .str docText, obj@(.obj _)] =>
    if isOptionsObj obj then
      let opts ← parseOptionsObj obj cliStrict
      return (id, docText, extraLib, opts.strictOwl2DL)
    else
      let lib ← parseImportsObj obj
      return (id, docText, lib ++ extraLib, cliStrict)
  | [.str _, .str id, .str docText, impJson@(.obj _), optJson@(.obj _)] =>
    let lib ← parseImportsObj impJson
    let opts ← parseOptionsObj optJson cliStrict
    return (id, docText, lib ++ extraLib, opts.strictOwl2DL)
  | _ => throw "expected [format, id, ontologyText, (optional importsObj), (optional optionsObj)]"

/-- Classify an OWL 2 document (FSS, RDF/XML, or Turtle) directly from CLI `--classify`.
    When `summaryOnly = true`, uses the compact parallel $\mathcal{EL}^{++}$ engine
    when applicable and outputs compact counts without serializing millions of JSON strings. -/
def runClassifyDocument (id docText : String) (lib : List (IRI × String))
    (strict : Bool) (numWorkers : Nat := 8) (summaryOnly : Bool := false) : UInt32 × Json := Id.run do
  let scope := Json.mkObj [("semantics", toJson "owl2-classify-v1"), ("id", toJson id)]
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto docText lib strict with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"parse/import error: {err}"), ("scope", scope)])
  if strict then
    if let some err := StrictTyping.diagnoseStrictTypedOWL2DLWithRules closure.declarations closure.annotationAxioms closure.ontology closure.rules then
      return (2, response "UNSUPPORTED" false [
        ("strict_owl2dl", toJson true), ("owl2dl_valid", toJson false),
        ("reason", toJson err), ("scope", scope)])
  let (ont, _, guardCls?) ← match lowerClosureSWRL closure with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err), ("scope", scope)])
  if summaryOnly && closure.rules.isEmpty then
    if let some ch := FastClassification.classifyOntologyCompactELRuntime ont closure.declarations numWorkers then
      let verdict := if ch.consistent then "CLASSIFIED" else "INCONSISTENT_ONTOLOGY"
      let subCount := ch.superClasses.foldl (fun acc arr => acc + arr.size) 0
      let dpCount := ch.directParents.foldl (fun acc arr => acc + if arr.isEmpty then 1 else arr.size) 0
      let summary := Json.mkObj [
        ("consistent", toJson ch.consistent),
        ("engine", toJson "fast-el-parallel"),
        ("workers", toJson numWorkers),
        ("class_count", toJson ch.classes.size),
        ("unsatisfiable_count", toJson ch.unsatisfiable.size),
        ("subsumption_count", toJson subCount),
        ("equivalence_count", toJson ch.equivalences.size),
        ("direct_parent_edges", toJson dpCount)]
      let base := [("classification_summary", summary), ("scope", scope)]
      let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: base else base
      return (0, response verdict true fields)
  match FastClassification.classifyOntologyFastRuntime ont closure.declarations numWorkers guardCls? with
  | some h =>
    let hier := if guardCls?.isSome then
        { h with equivalences := h.equivalences.filter (fun group => group.length ≥ 2) }
      else h
    let verdict := if hier.consistent then "CLASSIFIED" else "INCONSISTENT_ONTOLOGY"
    let base := if summaryOnly then
        let summary := Json.mkObj [
          ("consistent", toJson hier.consistent),
          ("engine", toJson "hybrid-fast"),
          ("workers", toJson numWorkers),
          ("class_count", toJson hier.classes.length),
          ("unsatisfiable_count", toJson hier.unsatisfiable.length),
          ("subsumption_count", toJson hier.subsumptions.length),
          ("equivalence_count", toJson hier.equivalences.length),
          ("direct_parent_edges", toJson (hier.directParents.foldl (fun acc (_, ps) => acc + ps.length) 0))]
        [("classification_summary", summary), ("scope", scope)]
      else
        [("classification", encodeClassHierarchy hier), ("scope", scope)]
    let baseWithSWRL := if closure.rules.isEmpty then base else ("swrl_rules", toJson closure.rules.length) :: base
    let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseWithSWRL else baseWithSWRL
    return (0, response verdict true fields)
  | none =>
    return (2, response "UNSUPPORTED" false [("reason", toJson "ontology outside exact classification fragment"), ("scope", scope)])

/-- Certified full TBox classification CLI handler (`sabrina-classify-v1`). -/
def runClassify (j : Json) (cliStrict : Bool := false)
    (extraLib : List (IRI × String) := []) : UInt32 × Json := Id.run do
  let (id, docText, lib, strict) ← match parseServiceRequest j cliStrict extraLib with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err)])
  return runClassifyDocument id docText lib strict 8 false

/-- Certified ABox realization CLI handler (`sabrina-realize-v1`). -/
def runRealize (j : Json) (cliStrict : Bool := false)
    (extraLib : List (IRI × String) := []) : UInt32 × Json := Id.run do
  let (id, docText, lib, strict) ← match parseServiceRequest j cliStrict extraLib with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err)])
  let scope := Json.mkObj [("semantics", toJson "owl2-realize-v1"), ("id", toJson id)]
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto docText lib strict with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson s!"parse/import error: {err}"), ("scope", scope)])
  if strict then
    if let some err := StrictTyping.diagnoseStrictTypedOWL2DLWithRules closure.declarations closure.annotationAxioms closure.ontology closure.rules then
      return (2, response "UNSUPPORTED" false [
        ("strict_owl2dl", toJson true), ("owl2dl_valid", toJson false),
        ("reason", toJson err), ("scope", scope)])
  let (ont, _, guardCls?) ← match lowerClosureSWRL closure with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err), ("scope", scope)])
  match FastClassification.realizeOntologyFastRuntime ont closure.declarations (auxiliaryClass? := guardCls?) with
  | some real =>
    let verdict := if real.consistent then "REALIZED" else "INCONSISTENT_ONTOLOGY"
    let base := [("realization", encodeRealization real), ("scope", scope)]
    let baseWithSWRL := if closure.rules.isEmpty then base else ("swrl_rules", toJson closure.rules.length) :: base
    let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseWithSWRL else baseWithSWRL
    return (0, response verdict true fields)
  | none =>
    return (2, response "UNSUPPORTED" false [("reason", toJson "ontology outside exact realization fragment"), ("scope", scope)])

/-- Materialize an OWL 2 document (FSS, RDF/XML, or Turtle) and render the
    inferred ontology in `.ofn`, `.ttl`, or `.owl` (RDF/XML). -/
def runMaterializeDocument (id docText : String) (lib : List (IRI × String))
    (strict : Bool) (fmt : Materialize.OutputFormat)
    (opts : Materialize.MaterializeOptions := {}) : UInt32 × Json × Option String := Id.run do
  let scope := Json.mkObj [("semantics", toJson "owl2-materialize-v1"), ("id", toJson id)]
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto docText lib strict with
    | .ok r => pure r
    | .error err =>
      return (2, response "UNSUPPORTED" false [("reason", toJson s!"parse/import error: {err}"), ("scope", scope)], none)
  if strict then
    if let some err := StrictTyping.diagnoseStrictTypedOWL2DLWithRules closure.declarations closure.annotationAxioms closure.ontology closure.rules then
      return (2, response "UNSUPPORTED" false [
        ("strict_owl2dl", toJson true), ("owl2dl_valid", toJson false),
        ("reason", toJson err), ("scope", scope)], none)
  let (ont, _, guardCls?) ← match lowerClosureSWRL closure with
    | .ok r => pure r
    | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err), ("scope", scope)], none)
  match Materialize.materializeOntologyRuntime ont closure.declarations opts (auxiliaryClass? := guardCls?) with
  | none =>
    return (2, response "UNSUPPORTED" false [
      ("reason", toJson "ontology outside exact materialization fragment"), ("scope", scope)], none)
  | some res =>
    if !res.consistent then
      let base := [("consistent", toJson false), ("scope", scope)]
      let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: base else base
      return (1, response "INCONSISTENT_ONTOLOGY" true fields, none)
    let assertedByKey : Std.HashMap String (List Axiom) := Id.run do
      let mut m : Std.HashMap String (List Axiom) := {}
      for a in closure.ontology do
        let k := FunctionalSyntax.renderAxiom a
        m := m.insert k (a :: m.getD k [])
      return m
    let freshInferred := res.inferredAxioms.filter fun ax =>
      !(assertedByKey.getD (FunctionalSyntax.renderAxiom ax) []).contains ax &&
      (match guardCls? with | some g => !SWRL.axiomHasClass g ax | none => true)
    let finalOnt := if opts.includeAsserted then closure.ontology ++ freshInferred else freshInferred
    let finalRules := if opts.includeAsserted then closure.rules else []
    let rendered := Materialize.renderMaterialized fmt closure.declarations
      closure.annotationAxioms finalOnt closure.prefixes
      closure.ontologyIRI closure.versionIRI finalRules
    let base := [
      ("consistent", toJson true),
      ("output_format", toJson fmt.name),
      ("asserted_axioms", toJson closure.ontology.length),
      ("inferred_axioms", toJson freshInferred.length),
      ("total_axioms", toJson finalOnt.length),
      ("scope", scope)]
    let baseWithSWRL := if closure.rules.isEmpty then base else ("swrl_rules", toJson closure.rules.length) :: base
    let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseWithSWRL else baseWithSWRL
    return (0, response "MATERIALIZED" true fields, some rendered)

private def isMaterializeOptionsObj (j : Json) : Bool :=
  match j.getObj? with
  | .ok obj =>
    isOptionsObj j || obj.contains "format" || obj.contains "include_asserted" ||
    obj.contains "all_subclasses" || obj.contains "all_types" || obj.contains "all_inferred" ||
    obj.contains "include_sub_object_properties" ||
    obj.contains "include_object_property_assertions" ||
    obj.contains "include_data_property_assertions" || obj.contains "include_same_individuals"
  | .error _ => false

private def parseMaterializeOptsObj (j : Json) (cliStrict : Bool) :
    Except String (Materialize.OutputFormat × Materialize.MaterializeOptions × Bool) := do
  let obj ← j.getObj?
  let mut fmt : Materialize.OutputFormat := .ofn
  let mut opts : Materialize.MaterializeOptions := {}
  let mut strict := cliStrict
  if let some v := obj.get? "strict_owl2dl" then
    strict := strict || (← v.getBool?)
  if let some v := obj.get? "format" then
    let s ← v.getStr?
    match Materialize.OutputFormat.ofString? s with
    | some f => fmt := f
    | none => throw s!"unsupported output format '{s}' (expected ofn, ttl, or rdfxml)"
  if let some v := obj.get? "include_asserted" then
    opts := { opts with includeAsserted := ← v.getBool? }
  if let some v := obj.get? "all_inferred" then
    if ← v.getBool? then
      opts := { opts with includeAllSubClass := true, includeAllTypes := true }
  if let some v := obj.get? "all_subclasses" then
    opts := { opts with includeAllSubClass := ← v.getBool? }
  if let some v := obj.get? "all_types" then
    opts := { opts with includeAllTypes := ← v.getBool? }
  if let some v := obj.get? "include_sub_object_properties" then
    opts := { opts with includeSubObjectProperties := ← v.getBool? }
  if let some v := obj.get? "include_object_property_assertions" then
    opts := { opts with includeObjectPropertyAssertions := ← v.getBool? }
  if let some v := obj.get? "include_data_property_assertions" then
    opts := { opts with includeDataPropertyAssertions := ← v.getBool? }
  if let some v := obj.get? "include_same_individuals" then
    opts := { opts with includeSameIndividuals := ← v.getBool? }
  return (fmt, opts, strict)

/-- Certified OWL 2 materialization CLI handler (`sabrina-materialize-v1`). -/
def runMaterialize (j : Json) (cliStrict : Bool := false)
    (extraLib : List (IRI × String) := []) : UInt32 × Json := Id.run do
  let .ok fields := j.getArr? | return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected [\"sabrina-materialize-v1\", id, ontologyText, (optional importsObj), (optional optionsObj)]")])
  let parsed : Except String (String × String × List (IRI × String) × Materialize.OutputFormat × Materialize.MaterializeOptions × Bool) :=
    match fields.toList with
    | [.str _, .str id, .str docText] => .ok (id, docText, extraLib, .ofn, {}, cliStrict)
    | [.str _, .str id, .str docText, obj@(.obj _)] =>
      if isMaterializeOptionsObj obj then
        match parseMaterializeOptsObj obj cliStrict with
        | .ok (fmt, opts, strict) => .ok (id, docText, extraLib, fmt, opts, strict)
        | .error e => .error e
      else
        match parseImportsObj obj with
        | .ok lib => .ok (id, docText, lib ++ extraLib, .ofn, {}, cliStrict)
        | .error e => .error e
    | [.str _, .str id, .str docText, impJson@(.obj _), optJson@(.obj _)] =>
      match parseImportsObj impJson, parseMaterializeOptsObj optJson cliStrict with
      | .ok lib, .ok (fmt, opts, strict) => .ok (id, docText, lib ++ extraLib, fmt, opts, strict)
      | .error e, _ => .error e
      | _, .error e => .error e
    | _ => .error "expected [\"sabrina-materialize-v1\", id, ontologyText, (optional importsObj), (optional optionsObj)]"
  match parsed with
  | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err)])
  | .ok (id, docText, lib, fmt, opts, strict) =>
    let (code, metaJson, rendered?) := runMaterializeDocument id docText lib strict fmt opts
    match rendered?, metaJson.getObj? with
    | some txt, .ok obj =>
      return (code, Json.mkObj (("output", toJson txt) :: obj.toList))
    | _, _ => return (code, metaJson)

private def encodeJustifications (justs : List Ontology)
    (prov : List (Axiom × SWRL.SWRLRule) := []) (guardCls? : Option IRI := none) : Json :=
  if prov.isEmpty then
    toJson (justs.map fun J => toJson (J.map renderAxiom))
  else
    toJson (justs.map fun J => toJson (renderJustificationWithRules prov guardCls? J))

/-- Explain inconsistency (`queryText? = none`) or entailment (`queryText? = some q`)
    with kernel-verified minimal justifications (Horridge–Kalyanpur–Parsia + Reiter HST). -/
def runExplainDocument (id docText : String) (queryText? : Option String)
    (lib : List (IRI × String)) (strict : Bool) (maxJusts : Nat := 5) : UInt32 × Json := Id.run do
  let baseScope := [("semantics", toJson "owl2-explain-v1"), ("id", toJson id)]
  let scope := Json.mkObj baseScope
  let closure ← match RDF.OWLMapping.resolveImportClosureAuto docText lib strict with
    | .ok r => pure r
    | .error err =>
      return (2, response "UNSUPPORTED" false [("reason", toJson s!"parse/import error: {err}"), ("scope", scope)])
  match queryText? with
  | none =>
    if strict then
      if let some err := StrictTyping.diagnoseStrictTypedOWL2DLWithRules closure.declarations closure.annotationAxioms closure.ontology closure.rules then
        return (2, response "UNSUPPORTED" false [
          ("strict_owl2dl", toJson true), ("owl2dl_valid", toJson false),
          ("reason", toJson err), ("scope", scope)])
    let (ont, prov, guardCls?) ← match lowerClosureSWRL closure with
      | .ok r => pure r
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err), ("scope", scope)])
    match Justification.explainInconsistencyRuntime ont maxJusts with
    | none =>
      return (2, response "UNSUPPORTED" false [("reason", toJson "ontology outside exact justification fragment"), ("scope", scope)])
    | some res =>
      let verdict := if res.inconsistent then "EXPLAINED" else "SATISFIABLE"
      let base := [
        ("kind", toJson "inconsistency"),
        ("inconsistent", toJson res.inconsistent),
        ("justification_count", toJson res.justifications.length),
        ("justifications", encodeJustifications res.justifications prov guardCls?),
        ("scope", scope)]
      let baseWithSWRL := if closure.rules.isEmpty then base else ("swrl_rules", toJson closure.rules.length) :: base
      let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseWithSWRL else baseWithSWRL
      return (0, response verdict true fields)
  | some qText =>
    let qAx ← match parseQueryAxiom closure.prefixes qText with
      | .ok a => pure a
      | .error err =>
        return (2, response "UNSUPPORTED" false [("reason", toJson s!"OFN query parse error: {err}"), ("query", toJson qText), ("scope", scope)])
    if strict then
      if let some err := StrictTyping.diagnoseStrictTypedOWL2DLQuery closure.declarations closure.annotationAxioms closure.ontology qAx <|>
          StrictTyping.diagnoseRuleTyping closure.declarations closure.annotationAxioms closure.ontology closure.rules then
        return (2, response "UNSUPPORTED" false [
          ("strict_owl2dl", toJson true), ("owl2dl_valid", toJson false),
          ("reason", toJson err), ("query", toJson qText), ("scope", scope)])
    let (ont, prov, guardCls?) ← match lowerClosureSWRL closure (SWRL.axiomNamedInds qAx) (StrictTyping.axiomClasses qAx) with
      | .ok r => pure r
      | .error err => return (2, response "UNSUPPORTED" false [("reason", toJson err), ("query", toJson qText), ("scope", scope)])
    match Justification.explainEntailmentRuntime ont qAx maxJusts with
    | none =>
      return (2, response "UNSUPPORTED" false [("reason", toJson "query/ontology outside exact justification fragment"), ("query", toJson qText), ("scope", scope)])
    | some res =>
      let verdict := if res.entailed then "EXPLAINED" else "NOT_ENTAILED"
      let base := [
        ("kind", toJson "entailment"),
        ("query", toJson qText),
        ("entailed", toJson res.entailed),
        ("justification_count", toJson res.justifications.length),
        ("justifications", encodeJustifications res.justifications prov guardCls?),
        ("scope", scope)]
      let baseWithSWRL := if closure.rules.isEmpty then base else ("swrl_rules", toJson closure.rules.length) :: base
      let fields := if strict then ("strict_owl2dl", toJson true) :: ("owl2dl_valid", toJson true) :: baseWithSWRL else baseWithSWRL
      return (0, response verdict true fields)

private def isExplainOptionsObj (j : Json) : Bool :=
  match j.getObj? with
  | .ok obj => isOptionsObj j || obj.contains "max_justifications"
  | .error _ => false

private def parseExplainOptsObj (j : Json) (cliStrict : Bool) : Except String (Nat × Bool) := do
  let obj ← j.getObj?
  let mut maxJ : Nat := 5
  let mut strict := cliStrict
  if let some v := obj.get? "strict_owl2dl" then
    strict := strict || (← v.getBool?)
  if let some v := obj.get? "max_justifications" then
    maxJ ← v.getNat?
  return (maxJ, strict)

/-- Certified minimal justification CLI handler (`sabrina-explain-v1`). -/
def runExplain (j : Json) (cliStrict : Bool := false)
    (extraLib : List (IRI × String) := []) : UInt32 × Json := Id.run do
  let .ok fields := j.getArr? | return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected [\"sabrina-explain-v1\", id, ontologyText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])
  match fields.toList with
  | [.str _, .str id, .str docText] =>
    return runExplainDocument id docText none extraLib cliStrict 5
  | [.str _, .str id, .str docText, .str qText] =>
    return runExplainDocument id docText (some qText) extraLib cliStrict 5
  | [.str _, .str id, .str docText, obj@(.obj _)] =>
    if isExplainOptionsObj obj then
      match parseExplainOptsObj obj cliStrict with
      | .ok (maxJ, strict) => return runExplainDocument id docText none extraLib strict maxJ
      | .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
    else
      match parseImportsObj obj with
      | .ok lib => return runExplainDocument id docText none (lib ++ extraLib) cliStrict 5
      | .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
  | [.str _, .str id, .str docText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseExplainOptsObj optJson cliStrict with
    | .ok lib, .ok (maxJ, strict) => return runExplainDocument id docText none (lib ++ extraLib) strict maxJ
    | .error e, _ | _, .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
  | [.str _, .str id, .str docText, .str qText, obj@(.obj _)] =>
    if isExplainOptionsObj obj then
      match parseExplainOptsObj obj cliStrict with
      | .ok (maxJ, strict) => return runExplainDocument id docText (some qText) extraLib strict maxJ
      | .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
    else
      match parseImportsObj obj with
      | .ok lib => return runExplainDocument id docText (some qText) (lib ++ extraLib) cliStrict 5
      | .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
  | [.str _, .str id, .str docText, .str qText, impJson@(.obj _), optJson@(.obj _)] =>
    match parseImportsObj impJson, parseExplainOptsObj optJson cliStrict with
    | .ok lib, .ok (maxJ, strict) => return runExplainDocument id docText (some qText) (lib ++ extraLib) strict maxJ
    | .error e, _ | _, .error e => return (2, response "UNSUPPORTED" false [("reason", toJson e)])
  | _ => return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected [\"sabrina-explain-v1\", id, ontologyText, (optional queryOfn), (optional importsObj), (optional optionsObj)]")])

end Sabrina.CLI.OFNQuery
