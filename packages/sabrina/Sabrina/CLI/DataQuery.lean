import Lean.Data.Json
import Sabrina.OWL2.DataCertificates

namespace Sabrina.CLI.DataQuery

open Lean Sabrina.OWL2 Sabrina.OWL2.DataCertificates Sabrina.OWL2.Datatypes

def requestFormat := "sabrina-data-consistency-v1"

private def name (j : Json) : Except String String := do
  let s ← j.getStr?
  if s.isEmpty then throw "empty data ontology name" else return s

private def parseLiteral (j : Json) : Except String Literal := do
  match (← j.getArr?).toList with
  | [.str raw, datatype] => return ⟨raw, ← name datatype⟩
  | _ => throw "a typed literal must be [lexical string, datatype IRI]"

private def parseFacet (j : Json) : Except String Facet := do
  match (← j.getArr?).toList with
  | [facet, bound] => return ⟨← name facet, ← parseLiteral bound⟩
  | _ => throw "a facet must be [facet IRI, typed literal]"

private partial def parseRange (j : Json) : Except String DataRange := do
  match (← j.getArr?).toList with
  | [.str "datatype", t] => return .datatype (← name t)
  | [.str "not", r] => return .complement (← parseRange r)
  | [.str "and", r, s] => return .intersection (← parseRange r) (← parseRange s)
  | [.str "or", r, s] => return .union (← parseRange r) (← parseRange s)
  | [.str "one-of", ls] => return .oneOf (← (← ls.getArr?).toList.mapM parseLiteral)
  | [.str "restriction", t, fs] =>
    return .restriction (← name t) (← (← fs.getArr?).toList.mapM parseFacet)
  | _ => throw "unsupported data range syntax"

private def parseClassExpr (j : Json) : Except String ClassExpr := do
  match (← j.getArr?).toList with
  | [.str "named", c] => return .named (← name c)
  | [.str "data-some", r, t] => return .dataSome (← name r) (← parseRange t)
  | [.str "data-min", n, r, t] => return .dataMin (← n.getNat?) (← name r) (← parseRange t)
  | [.str "data-max", n, r, t] => return .dataMax (← n.getNat?) (← name r) (← parseRange t)
  | [.str "data-exact", n, r, t] => return .dataExact (← n.getNat?) (← name r) (← parseRange t)
  | _ => throw "unsupported class expression syntax in data ontology"

private def parseAxiom (j : Json) : Except String Axiom := do
  match (← j.getArr?).toList with
  | [.str "data-assertion", r, a, l] => return .dataAssertion (← name r) (.named (← name a)) (← parseLiteral l)
  | [.str "negative-data-assertion", r, a, l] =>
    return .negativeDataAssertion (← name r) (.named (← name a)) (← parseLiteral l)
  | [.str "functional-data", r] => return .functionalDataProperty (← name r)
  | [.str "data-range", r, t] => return .dataPropertyRange (← name r) (← parseRange t)
  | [.str "class-assertion", c, a] => return .classAssertion (← parseClassExpr c) (.named (← name a))
  | [.str "sub-class", sub, sup] => return .subClassOf (← parseClassExpr sub) (← parseClassExpr sup)
  | [.str "different-individuals", inds] =>
    return .differentIndividuals ((← (← inds.getArr?).toList.mapM name).map Individual.named)
  | [.str "has-key", c, ds] =>
    return .hasKey (.named (← name c)) [] (← (← ds.getArr?).toList.mapM name)
  | [.str "datatype-definition", d, t] =>
    return .datatypeDefinition (← name d) (← parseRange t)
  | _ => throw "unsupported data ontology axiom syntax"

private def encodeFloatVal : FloatVal → Json
  | .negInf => toJson "-INF"
  | .posInf => toJson "INF"
  | .nan => toJson "NaN"
  | .negZero => toJson "-0.0"
  | .posZero => toJson "0.0"
  | .finite q => toJson s!"{q.num}/{q.den}"

private def parseFloatValJson (j : Json) : Except String FloatVal := do
  let s ← j.getStr?
  if s == "-INF" then return .negInf
  else if s == "INF" then return .posInf
  else if s == "NaN" then return .nan
  else if s == "-0.0" then return .negZero
  else if s == "0.0" then return .posZero
  else
    let some (.number q) := decodeLiteral ⟨s, owlRational⟩ | throw "invalid float value in model edge"
    return .finite q

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

private def parseBytes (j : Json) : Except String (List UInt8) := do
  let arr ← j.getArr?
  arr.toList.mapM fun x => do
    let n ← x.getNat?
    if n < 256 then return UInt8.ofNat n else throw "byte out of range in model edge"

private def parseValue (j : Json) : Except String Value := do
  match (← j.getArr?).toList with
  | [.str "boolean", b] => return .boolean (← b.getBool?)
  | [.str "number", .str q] => do
    let some v := decodeLiteral ⟨q,owlRational⟩ | throw "invalid rational value in model edge"
    return v
  | [.str "float", fv] => return .float (← parseFloatValJson fv)
  | [.str "double", fv] => return .double (← parseFloatValJson fv)
  | [.str "string", .str s] => return .string s
  | [.str "plain-literal", .str s, .str lang] => return .plainLiteral s lang
  | [.str "anyURI", .str s] => return .anyURI s
  | [.str "hexBinary", bs] => return .hexBinary (← parseBytes bs)
  | [.str "base64Binary", bs] => return .base64Binary (← parseBytes bs)
  | [.str "dateTime", .str q, tz, offset] => do
    let some (.number r) := decodeLiteral ⟨q, owlRational⟩ | throw "invalid dateTime value in model edge"
    let seconds ← fromJson? (α := Option Int) offset
    if (← tz.getBool?) != seconds.isSome then
      throw "dateTime timezone flag and offset disagree"
    if seconds.any (fun n => n.natAbs > 50400 || n % 60 != 0) then
      throw "invalid dateTime timezone offset"
    return .dateTime ⟨r, seconds⟩
  | [.str "dateTime", .str q, tz] => do
    let some (.number r) := decodeLiteral ⟨q, owlRational⟩ | throw "invalid dateTime value in model edge"
    -- Older certificates encode a zoned value by its UTC timeline position.
    return .dateTime ⟨r, if ← tz.getBool? then some 0 else none⟩
  | [.str "xmlLiteral", .str s] => return .xmlLiteral s
  | _ => throw "unsupported value in model edge"

private def parseEdge (j : Json) : Except String Edge := do
  match (← j.getArr?).toList with
  | [r, a, v] => return ⟨← name r, ← name a, ← parseValue v⟩
  | _ => throw "a model edge must be [property IRI, individual IRI, value]"

private def parseClassFact (j : Json) : Except String ClassFact := do
  match (← j.getArr?).toList with
  | [c, a] => return ⟨← name c, ← name a⟩
  | _ => throw "a model class fact must be [class IRI, individual IRI]"

private def parseNatPair (j : Json) : Except String (Nat × Nat) := do
  match (← j.getArr?).toList with
  | [a, b] => return (← a.getNat?, ← b.getNat?)
  | _ => throw "a key clash pair must be [first assertion index, second assertion index]"

private def parseCertificate (j : Json) : Except String Certificate := do
  match (← j.getArr?).toList with
  | [.str "model", edges] => return .model (← (← edges.getArr?).toList.mapM parseEdge) []
  | [.str "model", edges, classFacts] =>
    return .model (← (← edges.getArr?).toList.mapM parseEdge)
      (← (← classFacts.getArr?).toList.mapM parseClassFact)
  | [.str "functional-clash", k, n, m] => return .functionalClash (← k.getNat?) (← n.getNat?) (← m.getNat?)
  | [.str "range-clash", k, n] => return .rangeClash (← k.getNat?) (← n.getNat?)
  | [.str "assertion-clash", n, m] => return .assertionClash (← n.getNat?) (← m.getNat?)
  | [.str "empty-range-clash", n, lo, hi] =>
    return .emptyRangeClash (← n.getNat?) (← lo.getInt?) (← hi.getInt?)
  | [.str "existential-range-clash", n, k, lo, hi] =>
    return .existentialRangeClash (← n.getNat?) (← k.getNat?) (← lo.getInt?) (← hi.getInt?)
  | [.str "functional-existential-clash", k, n, m] =>
    return .functionalExistentialClash (← k.getNat?) (← n.getNat?) (← m.getNat?)
  | [.str "negative-existential-clash", n, negs, lo, hi] =>
    return .negativeExistentialClash (← n.getNat?)
      (← (← negs.getArr?).toList.mapM Json.getNat?) (← lo.getInt?) (← hi.getInt?)
  | [.str "subclass-empty-range-clash", k, n, lo, hi] =>
    return .subclassEmptyRangeClash (← k.getNat?) (← n.getNat?) (← lo.getInt?) (← hi.getInt?)
  | [.str "empty-solved-range-clash", n] =>
    return .emptySolvedRangeClash (← n.getNat?)
  | [.str "existential-solved-range-clash", n, k] =>
    return .existentialSolvedRangeClash (← n.getNat?) (← k.getNat?)
  | [.str "data-max-clash", k, assertions] =>
    return .dataMaxClash (← k.getNat?) (← (← assertions.getArr?).toList.mapM Json.getNat?)
  | [.str "data-min-finite-clash", k] =>
    return .dataMinFiniteClash (← k.getNat?)
  | [.str "key-clash", k, d, ma, mb, pairs] =>
    return .keyClash (← k.getNat?) (← d.getNat?) (← ma.getNat?) (← mb.getNat?)
      (← (← pairs.getArr?).toList.mapM parseNatPair)
  | _ => throw "unsupported data certificate syntax"

private def encodeCertificate : Certificate → Json
  | .model edges [] => toJson [toJson "model", toJson (edges.map fun e =>
      toJson [toJson e.role, toJson e.subject, encodeValue e.value])]
  | .model edges classFacts => toJson [toJson "model",
      toJson (edges.map fun e => toJson [toJson e.role, toJson e.subject, encodeValue e.value]),
      toJson (classFacts.map fun f => toJson [toJson f.cls, toJson f.subject])]
  | .functionalClash k n m => toJson [toJson "functional-clash", toJson k, toJson n, toJson m]
  | .rangeClash k n => toJson [toJson "range-clash", toJson k, toJson n]
  | .assertionClash n m => toJson [toJson "assertion-clash", toJson n, toJson m]
  | .emptyRangeClash n lo hi => toJson [toJson "empty-range-clash", toJson n, toJson lo, toJson hi]
  | .existentialRangeClash n k lo hi =>
    toJson [toJson "existential-range-clash", toJson n, toJson k, toJson lo, toJson hi]
  | .functionalExistentialClash k n m =>
    toJson [toJson "functional-existential-clash", toJson k, toJson n, toJson m]
  | .negativeExistentialClash n negs lo hi =>
    toJson [toJson "negative-existential-clash", toJson n, toJson negs, toJson lo, toJson hi]
  | .subclassEmptyRangeClash k n lo hi =>
    toJson [toJson "subclass-empty-range-clash", toJson k, toJson n, toJson lo, toJson hi]
  | .emptySolvedRangeClash n => toJson [toJson "empty-solved-range-clash", toJson n]
  | .existentialSolvedRangeClash n k => toJson [toJson "existential-solved-range-clash", toJson n, toJson k]
  | .dataMaxClash k assertions => toJson [toJson "data-max-clash", toJson k, toJson assertions]
  | .dataMinFiniteClash k => toJson [toJson "data-min-finite-clash", toJson k]
  | .keyClash k d ma mb pairs =>
    toJson [toJson "key-clash", toJson k, toJson d, toJson ma, toJson mb,
      toJson (pairs.map fun (a, b) => toJson [toJson a, toJson b])]

private structure Request where
  id : String
  source : Json
  ontology : Ontology
  certificate : Option Certificate

private def parseRequest (j : Json) : Except String Request := do
  let .str format :: id :: axioms :: extra := (← j.getArr?).toList
    | throw "expected [format, ontology ID, axioms, optional certificate]"
  if format != requestFormat then throw "unsupported data consistency format"
  let cert ← match extra with
    | [] => pure none
    | [cert] => some <$> parseCertificate cert
    | _ => throw "expected at most one certificate"
  return ⟨← name id, axioms, ← (← axioms.getArr?).toList.mapM parseAxiom, cert⟩

private def response (verdict : String) (checked : Bool) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("format", toJson "sabrina-alc-result-v1"), ("verdict", toJson verdict),
    ("lean_verified", toJson checked)] ++ fields)

private def report (req : Request) (cert : Certificate) : UInt32 × Json :=
  let verdict := match cert with
    | .model _ _ => "SATISFIABLE"
    | _ => "INCONSISTENT_ONTOLOGY"
  (0, response verdict true [
    ("scope", Json.mkObj [
      ("semantics", toJson "owl2-boolean-exact-numeric-ground-data"),
      ("id", toJson req.id), ("axioms", req.source)]),
    ("certificate", encodeCertificate cert)])

private def failure (verdict reason : String) : UInt32 × Json :=
  (2, response verdict false [("reason", toJson reason)])

def run (j : Json) : UInt32 × Json :=
  match parseRequest j with
  | .error reason => failure "UNSUPPORTED" reason
  | .ok req =>
    match req.certificate with
    | some cert =>
      if check req.ontology cert then report req cert
      else failure "REJECTED_CERTIFICATE" "certificate failed against the supplied data ontology"
    | none =>
      match solve req.ontology with
      | .checked cert => report req cert
      | .unsupported => failure "UNSUPPORTED"
        "data axioms require ordinary data properties, supported datatypes, valid literals and supported facets"
      | .unknown => failure "UNKNOWN" "no accepted data certificate found"

end Sabrina.CLI.DataQuery
