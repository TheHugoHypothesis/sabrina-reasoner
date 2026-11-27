import Lean.Data.Json
import Sabrina.OWL2.SROIQD.Search
import Sabrina.RoleChains.Regularity
import Sabrina.ALCHI.Query

/-! CLI JSON wire interface for the unified SROIQ(D) engine
    (`sabrina-sroiqd-query-v1`), supporting both consistency checking and
    class-inclusion entailment over mixed object + nominal + ABox + 33-datatype
    ontologies. -/

namespace Sabrina.CLI.SROIQDQuery

open Lean Sabrina.OWL2 Sabrina.OWL2.SROIQD Sabrina.OWL2.Datatypes
open Sabrina.ALC (OrientedRole RoleTheory InclusionVerdict roleClosure)

def requestFormat := "sabrina-sroiqd-query-v1"

private def parseName (j : Json) : Except String String := do
  let s ← j.getStr?
  if s.isEmpty then throw "empty SROIQ(D) name" else return s

private def parseLiteral (j : Json) : Except String Literal := do
  match (← j.getArr?).toList with
  | [.str raw, dt] => return ⟨raw, ← parseName dt⟩
  | _ => throw "typed literal must be [lexical, datatypeIRI]"

private def parseFacet (j : Json) : Except String Facet := do
  match (← j.getArr?).toList with
  | [facet, bound] => return ⟨← parseName facet, ← parseLiteral bound⟩
  | _ => throw "facet must be [facetIRI, typedLiteral]"

private partial def parseDataRange (j : Json) : Except String DataRange := do
  match (← j.getArr?).toList with
  | [.str "datatype", t] => return .datatype (← parseName t)
  | [.str "not", r] => return .complement (← parseDataRange r)
  | [.str "and", l, r] => return .intersection (← parseDataRange l) (← parseDataRange r)
  | [.str "or", l, r] => return .union (← parseDataRange l) (← parseDataRange r)
  | [.str "one-of", ls] => return .oneOf (← (← ls.getArr?).toList.mapM parseLiteral)
  | [.str "restriction", t, fs] =>
    return .restriction (← parseName t) (← (← fs.getArr?).toList.mapM parseFacet)
  | _ => throw "unsupported data range syntax"

private partial def parseConcept (j : Json) : Except String Concept := do
  match (← j.getArr?).toList with
  | [.str "top"] => return .top
  | [.str "bottom"] => return .bottom
  | [.str "atom", n] => return .atom (← parseName n)
  | [.str "neg", c] => return (← parseConcept c).dual
  | [.str "and", l, r] => return .conj (← parseConcept l) (← parseConcept r)
  | [.str "or", l, r] => return .disj (← parseConcept l) (← parseConcept r)
  | [.str "some", r, c] => return .some (← parseName r, false) (← parseConcept c)
  | [.str "all", r, c] => return .all (← parseName r, false) (← parseConcept c)
  | [.str "min", n, r, c] => return .min (← n.getNat?) (← parseName r, false) (← parseConcept c)
  | [.str "max", n, r, c] => return .max (← n.getNat?) (← parseName r, false) (← parseConcept c)
  | [.str "exact", n, r, c] => return .exact (← n.getNat?) (← parseName r, false) (← parseConcept c)
  | [.str "nominal", a] => return .nom (.named (← parseName a)) true
  | [.str "one-of", inds] =>
    let names ← (← inds.getArr?).toList.mapM parseName
    if names.isEmpty then throw "one-of requires at least one individual"
    return .oneOf (names.map Individual.named)
  | [.str "has-value", r, a] => return .hasValue (← parseName r, false) (.named (← parseName a))
  | [.str "self", r] => return .self (← parseName r, false) true
  | [.str "data-some", dp, d] => return .dataSome (← parseName dp) (← parseDataRange d)
  | [.str "data-all", dp, d] => return .dataAll (← parseName dp) (← parseDataRange d)
  | [.str "data-value", dp, l] => return .dataValue (← parseName dp) (← parseLiteral l) true
  | [.str "data-min", n, dp, d] => return .dataMin (← n.getNat?) (← parseName dp) (← parseDataRange d)
  | [.str "data-max", n, dp, d] => return .dataMax (← n.getNat?) (← parseName dp) (← parseDataRange d)
  | [.str "data-exact", n, dp, d] => return .dataExact (← n.getNat?) (← parseName dp) (← parseDataRange d)
  | .str tag :: _ => throw s!"unsupported or malformed SROIQ(D) concept: {tag}"
  | _ => throw "expected a tagged SROIQ(D) concept array"

private def allPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ allPairs xs

private def parseProblem (axioms : Array Json) : Except String Problem := do
  let mut tbox : List Inclusion := []
  let mut rules : RoleTheory := []
  let mut chains : List RoleChains.Chain := []
  let mut reflexive : List IRI := []
  let mut irreflexive : List IRI := []
  let mut asymmetric : List IRI := []
  let mut disjoint : List (OrientedRole × OrientedRole) := []
  let mut funcData : List IRI := []
  let mut dataRanges : List (IRI × DataRange) := []
  let mut keys : List KeyAxiom := []
  let mut classAssertions : List (Individual × Concept) := []
  let mut objAssertions : List (IRI × Individual × Individual) := []
  let mut negObjAssertions : List (IRI × Individual × Individual) := []
  let mut sameInds : List (Individual × Individual) := []
  let mut diffInds : List (Individual × Individual) := []
  let mut dataAssertions : List (IRI × Individual × Literal) := []
  let mut negDataAssertions : List (IRI × Individual × Literal) := []
  for ax in axioms do
    match (← ax.getArr?).toList with
    | [.str "sub", s, t] => tbox := ⟨← parseConcept s, ← parseConcept t⟩ :: tbox
    | [.str "subrole", r, s] => rules := ((← parseName r, false), (← parseName s, false)) :: rules
    | [.str "inverse", r, s] =>
      rules := (ALCHI.inverseRules (← parseName r) (← parseName s)).reverse ++ rules
    | [.str "symmetric", r] =>
      let rn ← parseName r
      rules := ((rn, true), (rn, false)) :: rules
    | [.str "functional", r] =>
      tbox := ⟨.top, .max 1 (← parseName r, false) .top⟩ :: tbox
    | [.str "reflexive", r] => reflexive := (← parseName r) :: reflexive
    | [.str "irreflexive", r] => irreflexive := (← parseName r) :: irreflexive
    | [.str "asymmetric", r] => asymmetric := (← parseName r) :: asymmetric
    | [.str "disjoint-roles", l, r] =>
      disjoint := ((← parseName l, false), (← parseName r, false)) :: disjoint
    | [.str "transitive", r] =>
      let rn ← parseName r
      chains := RoleChains.Chain.named [rn, rn] rn :: chains
    | [.str "chain", word, head] =>
      let w ← (← word.getArr?).toList.mapM parseName
      if w.length < 2 then throw "chain must contain at least two roles"
      chains := RoleChains.Chain.named w (← parseName head) :: chains
    | [.str "functional-data", dp] => funcData := (← parseName dp) :: funcData
    | [.str "data-range", dp, d] => dataRanges := (← parseName dp, ← parseDataRange d) :: dataRanges
    | [.str "has-key", cls, objPs, dataPs] =>
      let c ← parseConcept cls
      let os ← (← objPs.getArr?).toList.mapM fun r => do
        return (← parseName r, false)
      let ds ← (← dataPs.getArr?).toList.mapM parseName
      keys := ⟨c, os, ds⟩ :: keys
    | [.str "class-assertion", cls, a] =>
      classAssertions := (.named (← parseName a), ← parseConcept cls) :: classAssertions
    | [.str "object-assertion", r, a, b] =>
      objAssertions := (← parseName r, .named (← parseName a), .named (← parseName b)) :: objAssertions
    | [.str "negative-object-assertion", r, a, b] =>
      negObjAssertions := (← parseName r, .named (← parseName a), .named (← parseName b)) :: negObjAssertions
    | [.str "same-individuals", inds] =>
      let ns ← (← inds.getArr?).toList.mapM parseName
      sameInds := (allPairs (ns.map Individual.named)).reverse ++ sameInds
    | [.str "different-individuals", inds] =>
      let ns ← (← inds.getArr?).toList.mapM parseName
      diffInds := (allPairs (ns.map Individual.named)).reverse ++ diffInds
    | [.str "data-assertion", dp, a, l] =>
      dataAssertions := (← parseName dp, .named (← parseName a), ← parseLiteral l) :: dataAssertions
    | [.str "negative-data-assertion", dp, a, l] =>
      negDataAssertions := (← parseName dp, .named (← parseName a), ← parseLiteral l) :: negDataAssertions
    | .str tag :: _ => throw s!"unsupported SROIQ(D) axiom: {tag}"
    | _ => throw "expected a tagged SROIQ(D) axiom array"
  return {
    tbox := tbox.reverse
    rules := rules.reverse
    chains := chains.reverse
    chars := ⟨reflexive.reverse, irreflexive.reverse, asymmetric.reverse, disjoint.reverse⟩
    funcData := funcData.reverse
    dataRanges := dataRanges.reverse
    keys := keys.reverse
    classAssertions := classAssertions.reverse
    objAssertions := objAssertions.reverse
    negObjAssertions := negObjAssertions.reverse
    sameInds := sameInds.reverse
    diffInds := diffInds.reverse
    dataAssertions := dataAssertions.reverse
    negDataAssertions := negDataAssertions.reverse
    root := .top
  }

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
    let withData := if m.dataEdges.isEmpty then withNoms
      else withNoms ++ [("data_edges", toJson (m.dataEdges.map fun (dp, x, v) => #[toJson dp, toJson x.val, encodeValue v]))]
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

def run (j : Json) : UInt32 × Json := Id.run do
  let .ok fields := j.getArr? | return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected JSON array [\"sabrina-sroiqd-query-v1\", ontologyID, axioms, (optional query)]")])
  match fields.toList with
  | [.str _, idJson, axJson] =>
    let .ok id := parseName idJson | return (2, response "UNSUPPORTED" false [("reason", toJson "invalid ontology ID")])
    let .ok axArr := axJson.getArr? | return (2, response "UNSUPPORTED" false [("reason", toJson "axioms must be a JSON array")])
    let scope := Json.mkObj [("semantics", toJson "owl2-sroiqd"), ("id", toJson id), ("axioms", axJson)]
    let context := [("scope", scope)]
    let p ← match parseProblem axArr with
      | .ok p => pure p
      | .error msg => return (2, response "UNSUPPORTED" false (("reason", toJson msg) :: context))
    if let some err := checkRoleRestrictions p then
      return (2, response "UNSUPPORTED" false (("reason", toJson err) :: context))
    let limits : Limits := {}
    let some ev := propose p limits | return (2, response "UNKNOWN" false
      (("reason", toJson "SROIQ(D) search could not certify consistency within interactive limits") :: context))
    if !checkConsistency p limits.worlds ev then
      return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) evidence failed checking") :: context))
    let verdict := if ev.isModel then "SATISFIABLE" else "INCONSISTENT_ONTOLOGY"
    return (0, response verdict true (("certificate", encodeEvidence limits ev) :: context))
  | [.str _, idJson, axJson, queryJson] =>
    let .ok id := parseName idJson | return (2, response "UNSUPPORTED" false [("reason", toJson "invalid ontology ID")])
    let .ok axArr := axJson.getArr? | return (2, response "UNSUPPORTED" false [("reason", toJson "axioms must be a JSON array")])
    let scope := Json.mkObj [("semantics", toJson "owl2-sroiqd"), ("id", toJson id), ("axioms", axJson)]
    let context := [("scope", scope), ("query", queryJson)]
    let p ← match parseProblem axArr with
      | .ok p => pure p
      | .error msg => return (2, response "UNSUPPORTED" false (("reason", toJson msg) :: context))
    let q ← match queryJson.getArr? with
      | .ok arr =>
        match arr.toList with
        | [.str "sub", s, t] =>
          match parseConcept s, parseConcept t with
          | .ok cs, .ok ct => pure (⟨cs, ct⟩ : Inclusion)
          | .error e, _ | _, .error e => return (2, response "UNSUPPORTED" false (("reason", toJson e) :: context))
        | [.str "class-assertion", cls, a] =>
          match parseConcept cls, parseName a with
          | .ok c, .ok ind => pure (⟨.nom (.named ind) true, c⟩ : Inclusion)
          | .error e, _ | _, .error e => return (2, response "UNSUPPORTED" false (("reason", toJson e) :: context))
        | _ => return (2, response "UNSUPPORTED" false (("reason", toJson "query must be [\"sub\", sub, sup] or [\"class-assertion\", cls, individual]") :: context))
      | .error e => return (2, response "UNSUPPORTED" false (("reason", toJson e) :: context))
    if let some err := checkRoleRestrictions (inclusionProblem p q) then
      return (2, response "UNSUPPORTED" false (("reason", toJson err) :: context))
    let limits : Limits := {}
    let pair := do
      let a ← propose (counterProblem p q) limits
      let b ← propose (inclusionProblem p q) limits
      return (⟨a, b⟩ : InclusionEvidence)
    let some ev := pair | return (2, response "UNKNOWN" false
      (("reason", toJson "SROIQ(D) search could not produce both certificates within interactive limits") :: context))
    if !checkInclusion p q limits.worlds ev then
      return (1, response "REJECTED" false (("reason", toJson "SROIQ(D) inclusion evidence failed checking") :: context))
    let cert := Json.mkObj [
      ("counterexample", encodeEvidence limits ev.counterexample),
      ("inclusion", encodeEvidence limits ev.inclusion)]
    return (0, response (verdictName ev.verdict) true (("certificate", cert) :: context))
  | _ => return (2, response "UNSUPPORTED" false
    [("reason", toJson "expected 3 or 4 elements in sabrina-sroiqd-query-v1 request")])

end Sabrina.CLI.SROIQDQuery
