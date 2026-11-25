import Lean.Data.Json
import Sabrina.ALCH.Query
import Sabrina.RoleChains.Search
import Sabrina.Graded.Search
import Sabrina.CLI.DataQuery
import Sabrina.CLI.SROIQDQuery
import Sabrina.CLI.OFNQuery
import Sabrina.CLI.ImportCatalog

namespace Sabrina.CLI.Query

open Lean Sabrina.ALC

private def parseName (j : Json) : Except String String := do
  let name ← j.getStr?
  if name.isEmpty then throw "empty ALC name" else return name

private partial def parseConcept (j : Json) : Except String Concept := do
  match (← j.getArr?).toList with
  | [.str "top"] => return .top
  | [.str "bottom"] => return .bottom
  | [.str "atom", name] => return .atom (← parseName name)
  | [.str "neg", body] => return .neg (← parseConcept body)
  | [.str "and", left, right] => return .conj (← parseConcept left) (← parseConcept right)
  | [.str "or", left, right] => return .disj (← parseConcept left) (← parseConcept right)
  | [.str "some", role, body] => return .some (← parseName role) (← parseConcept body)
  | [.str "all", role, body] => return .all (← parseName role) (← parseConcept body)
  | .str tag :: _ => throw s!"unsupported or malformed ALC concept: {tag}"
  | _ => throw "expected a tagged ALC concept array"

private def parseInclusion (j : Json) : Except String Inclusion := do
  match (← j.getArr?).toList with
  | [.str "sub", sub, sup] => return ⟨← parseConcept sub, ← parseConcept sup⟩
  | .str tag :: _ => throw s!"unsupported or malformed ALC inclusion: {tag}"
  | _ => throw "expected an ALC inclusion [\"sub\", sub, sup]"

private partial def parseGradedConcept (j : Json) : Except String Graded.Concept := do
  match (← j.getArr?).toList with
  | [.str "top"] => return .top
  | [.str "bottom"] => return .bottom
  | [.str "atom", name] => return .atom (← parseName name)
  | [.str "neg", body] => return (← parseGradedConcept body).dual
  | [.str "and", left, right] => return .conj (← parseGradedConcept left) (← parseGradedConcept right)
  | [.str "or", left, right] => return .disj (← parseGradedConcept left) (← parseGradedConcept right)
  | [.str "some", role, body] => return .some (← parseName role) (← parseGradedConcept body)
  | [.str "all", role, body] => return .all (← parseName role) (← parseGradedConcept body)
  | [.str "min", count, role, body] =>
    return .min (← count.getNat?) (← parseName role) (← parseGradedConcept body)
  | [.str "max", count, role, body] =>
    return .max (← count.getNat?) (← parseName role) (← parseGradedConcept body)
  | [.str "exact", count, role, body] =>
    return .exact (← count.getNat?) (← parseName role) (← parseGradedConcept body)
  | [.str "nominal", ind] => return .nom (← parseName ind) true
  | [.str "one-of", inds] =>
    let names ← (← inds.getArr?).toList.mapM parseName
    if names.isEmpty then throw "one-of requires at least one individual"
    return .oneOf names
  | [.str "has-value", role, ind] =>
    return .hasValue (← parseName role) (← parseName ind)
  | [.str "self", role] =>
    return .self (← parseName role) true
  | .str tag :: _ => throw s!"unsupported or malformed graded concept: {tag}"
  | _ => throw "expected a tagged graded concept array"

private def parseGradedInclusion (j : Json) : Except String Graded.Inclusion := do
  match (← j.getArr?).toList with
  | [.str "sub", sub, sup] => return ⟨← parseGradedConcept sub, ← parseGradedConcept sup⟩
  | [.str "functional", role] => return ⟨.top, .max 1 (← parseName role) .top⟩
  | _ => throw "expected a graded inclusion"

private inductive Fragment where
  | alc | alch | alchi | chains | graded
  deriving BEq

private structure ParsedOntology (α : Type) where
  tbox : List α
  hierarchy : ALCH.Hierarchy
  rules : RoleTheory
  chains : List RoleChains.Chain
  chars : Graded.RoleChars := {}

private structure Request (α : Type) where
  scope : Json
  query : Json
  ontology : ParsedOntology α
  inclusion : α
  fragment : Fragment

private inductive ParsedRequest where
  | ordinary (request : Request Inclusion)
  | graded (request : Request Graded.Inclusion)

private def parseOntology {α : Type} (parse : Json → Except String α)
    (fragment : Fragment) (axioms : Array Json) : Except String (ParsedOntology α) := do
  let mut tbox := []
  let mut hierarchy := []
  let mut rules : RoleTheory := []
  let mut chains : List RoleChains.Chain := []
  let mut reflexive : List String := []
  let mut irreflexive : List String := []
  let mut asymmetric : List String := []
  let mut disjoint : List (OrientedRole × OrientedRole) := []
  for ax in axioms do
    match (← ax.getArr?).toList with
    | [.str "subrole", sub, sup] =>
      let r ← parseName sub
      let s ← parseName sup
      match fragment with
      | .alc => throw "subrole requires sabrina-alch-query-v1 or sabrina-alchi-query-v1"
      | .alch => hierarchy := (r, s) :: hierarchy
      | .alchi | .chains | .graded => rules := ((r, false), (s, false)) :: rules
    | [.str "inverse", left, right] =>
      if fragment != .alchi && fragment != .chains && fragment != .graded then
        throw "inverse requires sabrina-alchi-query-v1 or sabrina-role-chains-query-v1"
      rules := (ALCHI.inverseRules (← parseName left) (← parseName right)).reverse ++ rules
    | [.str "symmetric", role] =>
      if fragment != .graded then throw "symmetric requires sabrina-graded-query-v1"
      let r ← parseName role
      rules := ((r, true), (r, false)) :: rules
    | [.str "reflexive", role] =>
      if fragment != .graded then throw "reflexive requires sabrina-graded-query-v1"
      reflexive := (← parseName role) :: reflexive
    | [.str "irreflexive", role] =>
      if fragment != .graded then throw "irreflexive requires sabrina-graded-query-v1"
      irreflexive := (← parseName role) :: irreflexive
    | [.str "asymmetric", role] =>
      if fragment != .graded then throw "asymmetric requires sabrina-graded-query-v1"
      asymmetric := (← parseName role) :: asymmetric
    | [.str "disjoint-roles", left, right] =>
      if fragment != .graded then throw "disjoint-roles requires sabrina-graded-query-v1"
      let l ← parseName left
      let r ← parseName right
      disjoint := ((l, false), (r, false)) :: disjoint
    | [.str "transitive", role] =>
      if fragment != .chains && fragment != .graded then throw "transitive requires sabrina-role-chains-query-v1"
      let r ← parseName role
      chains := RoleChains.Chain.named [r, r] r :: chains
    | [.str "chain", word, head] =>
      if fragment != .chains && fragment != .graded then throw "chain requires sabrina-role-chains-query-v1"
      let word ← (← word.getArr?).toList.mapM parseName
      if word.length < 2 then throw "chain must contain at least two roles"
      chains := RoleChains.Chain.named word (← parseName head) :: chains
    | _ => tbox := (← parse ax) :: tbox
  let chars : Graded.RoleChars := ⟨reflexive.reverse, irreflexive.reverse, asymmetric.reverse, disjoint.reverse⟩
  return ⟨tbox.reverse,hierarchy.reverse,rules.reverse,chains.reverse,chars⟩

private def parseRequest (j : Json) : Except String ParsedRequest := do
  let shape := "expected a JSON array [request format, ontology ID, axioms, query]"
  let .ok fields := j.getArr? | throw shape
  let [ .str version, id, axioms, query ] := fields.toList | throw shape
  let fragment : Fragment ← match version with
    | "sabrina-alc-query-v1" => pure .alc
    | "sabrina-alch-query-v1" => pure .alch
    | "sabrina-alchi-query-v1" => pure .alchi
    | "sabrina-role-chains-query-v1" => pure .chains
    | "sabrina-graded-query-v1" => pure .graded
    | _ => throw s!"unsupported request format: {version}"
  let id ← parseName id
  let ax ← axioms.getArr?
  let semantics := match fragment with
    | .alc => "alc-tbox"
    | .alch => "alch-tbox"
    | .alchi => "alchi-tbox"
    | .chains => "role-chain-tbox"
    | .graded => "graded-role-chain-tbox"
  let scope := Json.mkObj [("semantics", toJson semantics), ("id", toJson id), ("axioms", axioms)]
  if fragment == .graded then
    return .graded ⟨scope,query,← parseOntology parseGradedInclusion fragment ax,
      ← parseGradedInclusion query,fragment⟩
  else
    return .ordinary ⟨scope,query,← parseOntology parseInclusion fragment ax,
      ← parseInclusion query,fragment⟩

private def encodeConcept : Concept → Json
  | .top => .arr #[.str "top"]
  | .atom name => .arr #[.str "atom", .str name]
  | .neg c => .arr #[.str "neg", encodeConcept c]
  | .conj a b => .arr #[.str "and", encodeConcept a, encodeConcept b]
  | .some role body => .arr #[.str "some", .str role, encodeConcept body]

private def encodeInclusion (q : Inclusion) : Json :=
  .arr #[.str "sub", encodeConcept q.sub, encodeConcept q.sup]

private def encodeCertificate (cert : Certificate) (extra : List (String × Json) := []) : Json :=
  match cert with
  | .model pool =>
    Json.mkObj ([("kind", toJson "model"), ("rows", toJson (pool.map (List.map encodeConcept)))] ++ extra)
  | .refutation rounds =>
    Json.mkObj ([("kind", toJson "refutation"), ("rounds", toJson rounds)] ++ extra)

private def verdictName : InclusionVerdict → String
  | .entailed => "ENTAILED"
  | .refuted => "REFUTED"
  | .independent => "SENTENCE_INDEPENDENT"
  | .inconsistent => "INCONSISTENT_TBOX"

private def response (verdict : String) (verified : Bool) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("format", toJson "sabrina-alc-result-v1"), ("verdict", toJson verdict),
    ("lean_verified", toJson verified)] ++ fields)

private def encodeGraph (g : RoleChains.Graph) : Json :=
  Json.mkObj [("kind", toJson "model"), ("worlds", toJson (g.additionalWorlds + 1)),
    ("atoms", toJson (g.atoms.map fun (p,x) => #[toJson p, toJson x.val])),
    ("edges", toJson (g.edges.map fun (r,x,y) => #[toJson r, toJson x.val, toJson y.val]))]

private def encodeChainEvidence : RoleChains.Evidence → Json
  | .refutation rounds => encodeCertificate (.refutation rounds)
  | .guarded cert => encodeCertificate cert [("basis", toJson "transitive-automaton-guards-v1")]
  | .ranked cert => encodeCertificate cert [("basis", toJson "ranked-automaton-guards-v1")]
  | .graph g => encodeGraph g

private def encodeNominalGraph (m : Graded.NominalGraph) : Json :=
  let base := [("kind", toJson "model"), ("worlds", toJson (m.graph.additionalWorlds + 1)),
    ("atoms", toJson (m.graph.atoms.map fun (p,x) => #[toJson p, toJson x.val])),
    ("edges", toJson (m.graph.edges.map fun (r,x,y) => #[toJson r, toJson x.val, toJson y.val]))]
  let fields := if m.nominals.isEmpty then base
    else base ++ [("nominals", toJson (m.nominals.map fun (a,x) => #[toJson a, toJson x.val]))]
  Json.mkObj fields

private def encodeGradedEvidence (limits : Graded.Limits) : Graded.Evidence → Json
  | .model m => encodeNominalGraph m
  | .refutation depth =>
    Json.mkObj [("kind",toJson "refutation"),("basis",toJson "graded-tableau-v1"),
      ("depth",toJson depth),("world_limit",toJson limits.worlds)]

private def solveGraded (req : Request Graded.Inclusion) : UInt32 × Json := Id.run do
  let context := [("scope",req.scope),("query",req.query)]
  let reject := fun reason => (2,response "UNSUPPORTED" false (("reason",toJson (reason : String)) :: context))
  let ⟨tbox,_,rules,chains,chars⟩ := req.ontology
  let q := req.inclusion
  let closed := roleClosure rules
  for role in Graded.countedRoles tbox q do
    if let some src := RoleChains.SimpleRoles.firstComposite closed chains (role,false) then
      let orientation := if src.2 then "inverse of " else ""
      return reject s!"number restriction or self uses non-simple role {role}; composite subrole: {orientation}{src.1}"
  for role in chars.simpleRoles do
    if let some src := RoleChains.SimpleRoles.firstComposite closed chains role then
      let orientation := if src.2 then "inverse of " else ""
      return reject s!"role characteristic or disjointness uses non-simple role {role.1}; composite subrole: {orientation}{src.1}"
  let names := (q :: tbox).flatMap (fun ax => ax.sub.roles ++ ax.sup.roles) ++
    rules.flatMap (fun (r,s) => [r.1,s.1]) ++ chains.flatMap (fun c => c.head :: c.bodyNames) ++
    chars.roles
  if names.any (RoleChains.SimpleRoles.builtinRoles.contains ·) then
    return reject "built-in OWL object properties are outside the typed graded semantics"
  if !RoleChains.checkRegular (RoleChains.inferRank rules chains) rules chains then
    return reject "no validated rank for this role hierarchy"
  let limits : Graded.Limits := {}
  let pair := do
    let a ← Graded.propose (Graded.counterProblem rules chains tbox q chars) limits
    let b ← Graded.propose (Graded.inclusionProblem rules chains tbox q chars) limits
    return (⟨a,b⟩ : Graded.InclusionEvidence)
  let some evidence := pair | return (2,response "UNKNOWN" false
    (("reason",toJson "graded search could not produce both certificates within the interactive limits") :: context))
  if !Graded.checkInclusion rules chains tbox q limits.worlds evidence chars then
    return (1,response "REJECTED" false (("reason",toJson "graded evidence failed checking") :: context))
  let certificate := Json.mkObj [
    ("counterexample",encodeGradedEvidence limits evidence.counterexample),
    ("inclusion",encodeGradedEvidence limits evidence.inclusion)]
  return (0,response (verdictName evidence.verdict) true (("certificate",certificate) :: context))

private def solveChains (req : Request Inclusion) : UInt32 × Json := Id.run do
  let context := [("scope", req.scope), ("query", req.query)]
  let tbox := req.ontology.tbox
  let rules := req.ontology.rules
  let chains := req.ontology.chains
  if !RoleChains.checkRegular (RoleChains.inferRank rules chains) rules chains then
    return (2, response "UNSUPPORTED" false
      (("reason", toJson "no validated rank for this role hierarchy") :: context))
  let query := req.inclusion
  let counter := RoleChains.counterRoot query
  let maxClosure := 18
  let maxWorlds := 16
  let pair := do
    let a ← RoleChains.proposeWithin rules chains tbox counter maxWorlds maxClosure
    let b ← RoleChains.proposeWithin rules chains (query :: tbox) .top maxWorlds maxClosure
    return (⟨a,b⟩ : RoleChains.InclusionEvidence)
  let some evidence := pair | return (2, response "UNKNOWN" false
    (("reason", toJson "role-chain search could not produce both certificates within the interactive limits") :: context))
  if !RoleChains.checkInclusion rules chains tbox query evidence then
    return (1, response "REJECTED" false (("reason", toJson "role-chain evidence failed checking") :: context))
  let certificate := Json.mkObj [
    ("counterexample", encodeChainEvidence evidence.counterexample),
    ("inclusion", encodeChainEvidence evidence.inclusion)]
  return (0, response (verdictName evidence.verdict) true (("certificate", certificate) :: context))

private def solve (req : Request Inclusion) : UInt32 × Json := Id.run do
  if req.fragment == .chains then return solveChains req
  let context := [("scope", req.scope), ("query", req.query)]
  let (tbox, inclusion) := if req.fragment == .alch then ALCH.compile ⟨req.ontology.tbox,req.ontology.hierarchy⟩ req.inclusion
    else (req.ontology.tbox, req.inclusion)
  let counterRoot := Concept.conj inclusion.sub (.neg inclusion.sup)
  -- The executable enumerates powersets of these closures. Bound the size of
  -- the allocation in an interactive call before either search starts.
  let maxClosure := 18
  if (closure tbox counterRoot).length > maxClosure ||
      (closure (inclusion :: tbox) .top).length > maxClosure then
    return (2, response "UNKNOWN" false
      (("reason", toJson s!"ALC closure exceeds the interactive limit of {maxClosure}") :: context))
  let evidence := ALCHI.searchInclusion req.ontology.rules tbox inclusion
  if !ALCHI.checkInclusion req.ontology.rules tbox inclusion evidence then
    return (1, response "REJECTED" false (("reason", toJson "ALC evidence failed checking") :: context))
  let certificate := Json.mkObj [
    ("counterexample", encodeCertificate evidence.counterexample),
    ("inclusion", encodeCertificate evidence.inclusion)]
  let fields := ("certificate", certificate) :: context
  let fields := if req.fragment == .alch then
      ("certificate_input", Json.mkObj [
        ("semantics", toJson "alc-tbox"), ("axioms", toJson (tbox.map encodeInclusion)),
        ("query", encodeInclusion inclusion)]) :: fields
    else fields
  return (0, response (verdictName evidence.verdict) true fields)

private def solveJSON (j : Json) (cliStrict : Bool := false)
    (extraLib : List (Sabrina.OWL2.IRI × String) := []) : UInt32 × Json :=
  let version : Option Json := j.getArr?.toOption.bind fun fields => fields[0]?
  match version with
  | some (.str format) =>
    if format == DataQuery.requestFormat then DataQuery.run j
    else if format == SROIQDQuery.requestFormat then SROIQDQuery.run j
    else if format == OFNQuery.requestFormat then OFNQuery.run j cliStrict extraLib
    else if format == OFNQuery.classifyFormat then OFNQuery.runClassify j cliStrict extraLib
    else if format == OFNQuery.realizeFormat then OFNQuery.runRealize j cliStrict extraLib
    else if format == OFNQuery.materializeFormat then OFNQuery.runMaterialize j cliStrict extraLib
    else if format == OFNQuery.explainFormat then OFNQuery.runExplain j cliStrict extraLib
    else solveInclusion j
  | _ => solveInclusion j
where
  solveInclusion j := match parseRequest j with
    | .error reason => (2, response "UNSUPPORTED" false [("reason", toJson reason)])
    | .ok (.ordinary request) => solve request
    | .ok (.graded request) => solveGraded request

private structure CliConfig where
  strictOwl2DL : Bool := false
  extraLib : List (Sabrina.OWL2.IRI × String) := []
  materializeInput : Option String := none
  explainInput : Option String := none
  explainQuery : Option String := none
  maxJustifications : Nat := 5
  outputPath : Option String := none
  outputFormat : Option Sabrina.OWL2.Materialize.OutputFormat := none
  matOpts : Sabrina.OWL2.Materialize.MaterializeOptions := {}

private def parseCliArgs (args : List String) : IO (Except String CliConfig) := do
  let mut cfg : CliConfig := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--strict-owl2dl" :: tail =>
      cfg := { cfg with strictOwl2DL := true }
      rest := tail
    | "--catalog" :: path :: tail =>
      match ← ImportCatalog.loadOasisCatalog (System.FilePath.mk path) with
      | .ok lib => cfg := { cfg with extraLib := cfg.extraLib ++ lib }
      | .error err => return .error err
      rest := tail
    | "--import-dir" :: dir :: tail =>
      match ← ImportCatalog.loadImportDir (System.FilePath.mk dir) with
      | .ok lib => cfg := { cfg with extraLib := cfg.extraLib ++ lib }
      | .error err => return .error err
      rest := tail
    | "--materialize" :: path :: tail =>
      cfg := { cfg with materializeInput := some path }
      rest := tail
    | "--explain" :: path :: tail =>
      cfg := { cfg with explainInput := some path }
      rest := tail
    | "--query" :: qText :: tail =>
      cfg := { cfg with explainQuery := some qText }
      rest := tail
    | "--max-justifications" :: nStr :: tail =>
      match nStr.toNat? with
      | some n => cfg := { cfg with maxJustifications := n }
      | none => return .error s!"expected natural number for --max-justifications, got '{nStr}'"
      rest := tail
    | "-o" :: path :: tail | "--output" :: path :: tail =>
      cfg := { cfg with outputPath := some path }
      rest := tail
    | "--format" :: fmtStr :: tail =>
      match Sabrina.OWL2.Materialize.OutputFormat.ofString? fmtStr with
      | some f => cfg := { cfg with outputFormat := some f }
      | none => return .error s!"unsupported --format '{fmtStr}' (expected: ofn, ttl, rdfxml)"
      rest := tail
    | "--inferred-only" :: tail =>
      cfg := { cfg with matOpts := { cfg.matOpts with includeAsserted := false } }
      rest := tail
    | "--all-inferred" :: tail =>
      cfg := { cfg with matOpts := { cfg.matOpts with includeAllSubClass := true, includeAllTypes := true } }
      rest := tail
    | flag :: _ =>
      return .error s!"unknown or incomplete CLI flag: {flag} (supported: --strict-owl2dl, --catalog <path>, --import-dir <dir>, --materialize <in>, --explain <in>, --query <ofn>, --max-justifications <n>, -o <out>, --format <ofn|ttl|rdfxml>, --inferred-only, --all-inferred)"
    | [] => break
  return .ok cfg

def run (args : List String) : IO UInt32 := do
  let cfg ← match ← parseCliArgs args with
    | .ok res => pure res
    | .error err =>
      IO.println (response "UNSUPPORTED" false [("reason", toJson err)]).compress
      return 2
  if let some inPath := cfg.explainInput then
    let docText ← try
        IO.FS.readFile (System.FilePath.mk inPath)
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to read '{inPath}': {e}")]).compress
        return 2
    let (code, outJson) := OFNQuery.runExplainDocument inPath docText cfg.explainQuery
      cfg.extraLib cfg.strictOwl2DL cfg.maxJustifications
    IO.println outJson.compress
    return code
  if let some inPath := cfg.materializeInput then
    let docText ← try
        IO.FS.readFile (System.FilePath.mk inPath)
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to read '{inPath}': {e}")]).compress
        return 2
    let fmt := match cfg.outputFormat, cfg.outputPath with
      | some f, _ => f
      | none, some outP => Sabrina.OWL2.Materialize.OutputFormat.fromPath outP
      | none, none => Sabrina.OWL2.Materialize.OutputFormat.fromPath inPath
    let (code, metaJson, rendered?) :=
      OFNQuery.runMaterializeDocument inPath docText cfg.extraLib cfg.strictOwl2DL fmt cfg.matOpts
    match rendered?, cfg.outputPath with
    | some txt, some outP =>
      try
        IO.FS.writeFile (System.FilePath.mk outP) txt
      catch e =>
        IO.println (response "UNSUPPORTED" false [("reason", toJson s!"failed to write '{outP}': {e}")]).compress
        return 2
      let outJson := match metaJson.getObj? with
        | .ok obj => Json.mkObj (("output_path", toJson outP) :: obj.toList)
        | .error _ => metaJson
      IO.println outJson.compress
      return code
    | some txt, none =>
      IO.print txt
      return code
    | none, _ =>
      IO.println metaJson.compress
      return code
  let input ← (← IO.getStdin).readToEnd
  let (code, result) := match Json.parse input with
    | .ok j => solveJSON j cfg.strictOwl2DL cfg.extraLib
    | .error reason => (2, response "UNSUPPORTED" false [("reason", toJson reason)])
  IO.println result.compress
  return code

end Sabrina.CLI.Query
