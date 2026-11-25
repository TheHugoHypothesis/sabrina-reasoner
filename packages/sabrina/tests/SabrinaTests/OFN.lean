import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.Normalize
import Sabrina.OWL2.WellFormed
import Sabrina.CLI.OFNQuery

/-! Regression tests for M2/M3/M10: W3C OWL 2 Functional-Style Syntax parsing,
    multi-document Import(...) closure with version IRIs and document-scoped
    anonymous individuals, two-way verified normalization (ObjectInverseOf,
    InverseFunctionalObjectProperty, SubDataPropertyOf/EquivalentDataProperties/
    DisjointDataProperties, acyclic DatatypeDefinition unfolding, xsd:pattern,
    rdf:langRange, anonymous individuals), and M10 query services. -/

namespace SabrinaTests.OFN

open Sabrina.OWL2 Sabrina.OWL2.FunctionalSyntax Sabrina.OWL2.Normalize Sabrina.OWL2.SROIQD Sabrina.OWL2.WellFormed

private def checkOFNSat (ofn : String) (lib : List (IRI × String) := []) : Bool :=
  match resolveImports ofn lib with
  | .ok (_, ont) =>
    match normalizeWithDefs ont with
    | some (_, p) =>
      match propose p {} with
      | some (.model m) => checkConsistency p 16 (.model m)
      | _ => false
    | none => false
  | .error _ => false

private def checkOFNUnsat (ofn : String) (lib : List (IRI × String) := []) : Bool :=
  match resolveImports ofn lib with
  | .ok (_, ont) =>
    match normalizeWithDefs ont with
    | some (_, p) =>
      match propose p {} with
      | some (.refutation d) => checkConsistency p 16 (.refutation d)
      | _ => false
    | none => false
  | .error _ => false

private def checkOFNEntails (ofn query : String) (lib : List (IRI × String) := []) : Bool :=
  match resolveImports ofn lib with
  | .ok (pfxs, ont) =>
    match normalizeWithDefs ont, parseQueryAxiom pfxs query with
    | some (defs, p), .ok qAx =>
      match queryToInclusions defs qAx with
      | some [q] =>
        match propose (counterProblem p q) {}, propose (inclusionProblem p q) {} with
        | some c, some inc =>
          let ev : InclusionEvidence := ⟨c, inc⟩
          checkInclusion p q 16 ev && ev.verdict == .entailed
        | _, _ => false
      | _ => false
    | _, _ => false
  | .error _ => false

private def employeeOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(<http://example.org/org>
  Declaration(Class(ex:Employee))
  Declaration(Class(ex:Manager))
  Declaration(ObjectProperty(ex:inDept))
  Declaration(DataProperty(ex:badgeId))
  HasKey(ex:Employee (ex:inDept) (ex:badgeId))
  EquivalentClasses(ex:Staff ex:Employee)
  DisjointClasses(ex:Manager ex:Intern)
  ClassAssertion(ex:Employee ex:alice)
  ClassAssertion(ex:Staff ex:bob)
  ClassAssertion(ex:Manager ex:alice)
  ObjectPropertyAssertion(ex:inDept ex:alice ex:dept1)
  ObjectPropertyAssertion(ex:inDept ex:bob ex:dept1)
  DataPropertyAssertion(ex:badgeId ex:alice \"01\"^^xsd:integer)
  DataPropertyAssertion(ex:badgeId ex:bob \"1.0\"^^xsd:decimal)
)
"

-- 1. Consistency + HasKey entailment + DisjointClasses + SameIndividual + NegativeAssertions
#guard checkOFNSat employeeOFN
#guard checkOFNEntails employeeOFN "ClassAssertion(ex:Manager ex:bob)"
#guard checkOFNEntails employeeOFN "DisjointClasses(ex:Manager ex:Intern)"
#guard checkOFNEntails employeeOFN "SameIndividual(ex:alice ex:bob)"
#guard checkOFNEntails employeeOFN "ObjectPropertyAssertion(ex:inDept ex:bob ex:dept1)"
#guard checkOFNEntails employeeOFN "DataPropertyAssertion(ex:badgeId ex:bob \"1\"^^xsd:integer)"

-- 2. DisjointUnion + string length facet clash
private def disjointUnionClashOFN : String := "
Prefix(:=<http://example.org/>)
Ontology(
  DisjointUnion(:Status :Active :Archived)
  SubClassOf(:Active DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:minLength \"5\"^^xsd:nonNegativeInteger xsd:maxLength \"3\"^^xsd:nonNegativeInteger)))
  ClassAssertion(:Status :item1)
  ClassAssertion(ObjectComplementOf(:Archived) :item1)
)
"
#guard checkOFNUnsat disjointUnionClashOFN

-- 3. ObjectInverseOf directly inside class expressions + InverseFunctionalObjectProperty
private def inverseOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  InverseFunctionalObjectProperty(ex:hasSSN)
  SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(ex:hasSSN) ex:Citizen) ex:ValidSSN)
  ClassAssertion(ex:Citizen ex:alice)
  ClassAssertion(ex:VIP ex:alice)
  ObjectPropertyAssertion(ex:hasSSN ex:alice ex:ssn1)
  ObjectPropertyAssertion(ex:hasSSN ex:bob ex:ssn1)
)
"
#guard checkOFNEntails inverseOFN "ClassAssertion(ex:ValidSSN ex:ssn1)"
#guard checkOFNEntails inverseOFN "ClassAssertion(ex:VIP ex:bob)"

-- 4. SubDataPropertyOf, EquivalentDataProperties, and DisjointDataProperties
private def dataPropHierOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubDataPropertyOf(ex:workEmail ex:email)
  EquivalentDataProperties(ex:email ex:contactEmail)
  DataPropertyAssertion(ex:workEmail ex:alice \"a@b.org\"^^xsd:string)
)
"
#guard checkOFNEntails dataPropHierOFN "DataPropertyAssertion(ex:contactEmail ex:alice \"a@b.org\"^^xsd:string)"

private def negAssertionQueryOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  FunctionalDataProperty(ex:age)
  DisjointObjectProperties(ex:likes ex:dislikes)
  DifferentIndividuals(ex:alice ex:charlie)
  ObjectPropertyAssertion(ex:likes ex:alice ex:charlie)
  DataPropertyAssertion(ex:age ex:alice \"30\"^^xsd:integer)
)
"
#guard checkOFNEntails negAssertionQueryOFN "DifferentIndividuals(ex:alice ex:charlie)"
#guard checkOFNEntails negAssertionQueryOFN "NegativeObjectPropertyAssertion(ex:dislikes ex:alice ex:charlie)"
#guard checkOFNEntails negAssertionQueryOFN "NegativeDataPropertyAssertion(ex:age ex:alice \"31\"^^xsd:integer)"

private def dataPropDisjClashOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubDataPropertyOf(ex:workEmail ex:email)
  DisjointDataProperties(ex:email ex:personalEmail)
  DataPropertyAssertion(ex:workEmail ex:alice \"a@b.org\"^^xsd:string)
  DataPropertyAssertion(ex:personalEmail ex:alice \"a@b.org\"^^xsd:string)
)
"
#guard checkOFNUnsat dataPropDisjClashOFN

-- 5. Acyclic DatatypeDefinition unfolding (chained) + cycle rejection
private def datatypeDefOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DatatypeDefinition(ex:AdultAge DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer))
  DatatypeDefinition(ex:WorkingAge DataIntersectionOf(ex:AdultAge DatatypeRestriction(xsd:integer xsd:maxInclusive \"65\"^^xsd:integer)))
  DataPropertyRange(ex:age ex:WorkingAge)
  DataPropertyAssertion(ex:age ex:alice \"12\"^^xsd:integer)
)
"
#guard checkOFNUnsat datatypeDefOFN

private def cyclicDatatypeDefOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DatatypeDefinition(ex:A ex:B)
  DatatypeDefinition(ex:B ex:A)
)
"
#guard match parseDocument cyclicDatatypeDefOFN with
  | .ok doc => (normalizeWithDefs doc.ontology).isNone
  | .error _ => false

-- 6. xsd:pattern and rdf:langRange facets
private def patternMatchOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DataPropertyRange(ex:code DatatypeRestriction(xsd:string xsd:pattern \"[A-Z]{2}-[0-9]+\"^^xsd:string))
  DataPropertyAssertion(ex:code ex:item1 \"AB-42\"^^xsd:string)
)
"
#guard checkOFNSat patternMatchOFN

private def patternMismatchOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DataPropertyRange(ex:code DatatypeRestriction(xsd:string xsd:pattern \"[A-Z]{2}-[0-9]+\"^^xsd:string))
  DataPropertyAssertion(ex:code ex:item1 \"ab-42\"^^xsd:string)
)
"
#guard checkOFNUnsat patternMismatchOFN

private def langRangeClashOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DataPropertyRange(ex:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string))
  DataPropertyAssertion(ex:label ex:item1 \"Bonjour\"@fr)
)
"
#guard checkOFNUnsat langRangeClashOFN

private def langRangeMatchOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DataPropertyRange(ex:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string))
  DataPropertyAssertion(ex:label ex:item1 \"Hello\"@en-US)
)
"
#guard checkOFNSat langRangeMatchOFN

-- 7. Anonymous individuals (_:x) do NOT trigger HasKey (OWL 2 Direct Semantics),
--    while still participating in class/property/data reasoning.
private def anonNoKeyOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  HasKey(ex:Employee () (ex:badgeId))
  DisjointClasses(ex:Manager ex:Intern)
  ClassAssertion(ex:Employee ex:alice)
  ClassAssertion(ex:Manager ex:alice)
  DataPropertyAssertion(ex:badgeId ex:alice \"1\"^^xsd:integer)
  ClassAssertion(ex:Employee _:anon1)
  ClassAssertion(ex:Intern _:anon1)
  DataPropertyAssertion(ex:badgeId _:anon1 \"1\"^^xsd:integer)
)
"
#guard checkOFNSat anonNoKeyOFN

-- 8. Multi-document Import(...) closure with version IRI, cycle handling,
--    missing-import rejection, and document-scoped anonymous individuals.
private def impDocA : String := "
Prefix(ex:=<http://example.org/>)
Ontology(<http://example.org/a> <http://example.org/a/v1>
  Import(<http://example.org/b>)
  SubClassOf(ex:A ex:Shared)
  ClassAssertion(ex:OnlyA _:x)
)
"
private def impDocB : String := "
Prefix(ex:=<http://example.org/>)
Ontology(<http://example.org/b>
  Import(<http://example.org/a/v1>)
  DisjointClasses(ex:OnlyA ex:OnlyB)
  ClassAssertion(ex:OnlyB _:x)
)
"
private def impRoot : String := "
Prefix(ex:=<http://example.org/>)
Ontology(<http://example.org/root>
  Import(<http://example.org/a/v1>)
  ClassAssertion(ex:A ex:item)
)
"
-- Cyclic import + version IRI + document-scoped _:x (disjoint OnlyA/OnlyB on _:x in A vs B stays SAT!)
#guard checkOFNSat impRoot [("http://example.org/a", impDocA), ("http://example.org/b", impDocB)]
#guard checkOFNEntails impRoot "ClassAssertion(ex:Shared ex:item)" [("http://example.org/a", impDocA), ("http://example.org/b", impDocB)]
-- Missing import is rejected
#guard match resolveImports impRoot [] with | .error _ => true | .ok _ => false

-- 9. Structural well-formedness validator (checkWellFormedOntology) & document scoping check
#guard match parseDocument employeeOFN with
  | .ok doc => checkWellFormedOntology doc.ontology && docInScope "doc:0" doc.ontology
  | .error _ => false

-- Reserved vocabulary redefinition & arity < 2 are rejected by checkWellFormedOntology
#guard !checkWellFormedOntology [.equivalentClasses [.named "http://example.org/A"]]
#guard !checkWellFormedOntology [.classAssertion (.named "http://www.w3.org/2002/07/owl# Forbidden") (.named "http://example.org/a")]
#guard !checkWellFormedOntology [.hasKey (.named "http://example.org/A") [] []]

-- 10. Existential witness synthesis (DataSomeValuesFrom) over xsd:pattern, rdf:langRange,
--     xsd:float, xsd:dateTimeStamp, xsd:hexBinary, and disjoint DataIntersectionOf emptiness
private def patternExistentialSatOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubClassOf(ex:Item DataSomeValuesFrom(ex:code DatatypeRestriction(xsd:string xsd:pattern \"[A-Z]{2}-[0-9]+\"^^xsd:string)))
  SubClassOf(ex:Item DataSomeValuesFrom(ex:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string)))
  SubClassOf(ex:Item DataSomeValuesFrom(ex:weight xsd:float))
  SubClassOf(ex:Item DataSomeValuesFrom(ex:createdAt xsd:dateTimeStamp))
  SubClassOf(ex:Item DataSomeValuesFrom(ex:rawBytes xsd:hexBinary))
  ClassAssertion(ex:Item ex:item1)
)
"
#guard checkOFNSat patternExistentialSatOFN

private def disjointIntersectionExistentialUnsatOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubClassOf(ex:Impossible DataSomeValuesFrom(ex:val DataIntersectionOf(xsd:integer xsd:string)))
  ClassAssertion(ex:Impossible ex:item1)
)
"
#guard checkOFNUnsat disjointIntersectionExistentialUnsatOFN

-- 11. M2 Canonical .ofn rendering & structural S-expression round-trip verification
private def checkOFNRoundTrip (ofn : String) : Bool :=
  match parseDocument ofn with
  | .ok doc1 =>
    let rendered := renderOntology doc1.ontology doc1.ontologyIRI doc1.versionIRI doc1.imports
    let sexprOk := decodeOntology (encodeOntology doc1.ontology) == some doc1.ontology
    match parseDocument rendered with
    | .ok doc2 => sexprOk && doc2.ontology == doc1.ontology && doc2.ontologyIRI == doc1.ontologyIRI
    | .error _ => false
  | .error _ => false

#guard checkOFNRoundTrip employeeOFN
#guard checkOFNRoundTrip disjointUnionClashOFN
#guard checkOFNRoundTrip inverseOFN
#guard checkOFNRoundTrip dataPropHierOFN
#guard checkOFNRoundTrip negAssertionQueryOFN
#guard checkOFNRoundTrip datatypeDefOFN
#guard checkOFNRoundTrip patternMatchOFN
#guard checkOFNRoundTrip anonNoKeyOFN
#guard checkOFNRoundTrip patternExistentialSatOFN

-- 12. M3 Fresh-class allocation & Worked Proof Checkpoint (A ⊑ ∃R.(B ⊓ ∃S.C))
private def m3WorkedSourceOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubClassOf(ex:A ObjectSomeValuesFrom(ex:R ObjectIntersectionOf(ex:B ObjectSomeValuesFrom(ex:S ex:C))))
  SubClassOf(ObjectSomeValuesFrom(ex:R ObjectSomeValuesFrom(ex:S ex:C)) ex:Target)
)
"
private def m3WorkedFlattenedOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  EquivalentClasses(ex:AuxX ObjectIntersectionOf(ex:B ObjectSomeValuesFrom(ex:S ex:C)))
  SubClassOf(ex:A ObjectSomeValuesFrom(ex:R ex:AuxX))
  SubClassOf(ObjectSomeValuesFrom(ex:R ObjectSomeValuesFrom(ex:S ex:C)) ex:Target)
)
"
#guard checkOFNEntails m3WorkedSourceOFN "SubClassOf(ex:A ex:Target)"
#guard checkOFNEntails m3WorkedFlattenedOFN "SubClassOf(ex:A ex:Target)"
#guard match parseDocument m3WorkedSourceOFN with
  | .ok doc =>
    let fresh := freshClassIRI doc.ontology [.subClassOf (.named "http://example.org/A") (.named "http://example.org/Target")]
    checkFreshClass fresh doc.ontology [.subClassOf (.named "http://example.org/A") (.named "http://example.org/Target")]
  | .error _ => false

-- 13. M12 W3C OWL 2 Conformance & Adversarial Mutation Suite

-- W3C Conformance: ObjectOneOf + ObjectMinCardinality pigeonhole clash
private def w3cNominalPigeonholeOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubClassOf(ex:Test ObjectMinCardinality(3 ex:hasPart ObjectOneOf(ex:p1 ex:p2)))
  ClassAssertion(ex:Test ex:t1)
)
"
#guard checkOFNUnsat w3cNominalPigeonholeOFN

-- W3C Conformance: ObjectHasSelf + IrreflexiveObjectProperty clash
private def w3cSelfIrreflexiveOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  IrreflexiveObjectProperty(ex:properPartOf)
  ClassAssertion(ObjectHasSelf(ex:properPartOf) ex:x)
)
"
#guard checkOFNUnsat w3cSelfIrreflexiveOFN

-- W3C Conformance: Role chain + InverseObjectProperties + TransitiveObjectProperty entailment
private def w3cRoleChainInverseOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  InverseObjectProperties(ex:hasParent ex:hasChild)
  SubObjectPropertyOf(ObjectPropertyChain(ex:hasParent ex:hasBrother) ex:hasUncle)
  ObjectPropertyAssertion(ex:hasChild ex:parent1 ex:alice)
  ObjectPropertyAssertion(ex:hasBrother ex:parent1 ex:bob)
)
"
#guard checkOFNEntails w3cRoleChainInverseOFN "ObjectPropertyAssertion(ex:hasUncle ex:alice ex:bob)"

private def orientedChainOFN (extra : String) : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(ex:r) ex:s) ObjectInverseOf(ex:t))
  ObjectPropertyAssertion(ex:r ex:b ex:a)
  ObjectPropertyAssertion(ex:s ex:b ex:c)
  " ++ extra ++ "
)
"

#guard match parseDocument (orientedChainOFN "") with
  | .ok doc => checkWellFormedOntology doc.ontology
  | .error _ => false
#guard checkOFNEntails (orientedChainOFN "") "ObjectPropertyAssertion(ex:t ex:c ex:a)"
#guard match parseDocument (orientedChainOFN "FunctionalObjectProperty(ex:t)") with
  | .ok doc => !checkWellFormedOntology doc.ontology
  | .error _ => false

-- W3C Conformance: DataExactCardinality(2) over xsd:boolean is satisfiable, DataMinCardinality(3) is inconsistent
private def w3cBooleanExact2OFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  ClassAssertion(DataExactCardinality(2 ex:flag xsd:boolean) ex:item1)
)
"
#guard checkOFNSat w3cBooleanExact2OFN

private def w3cBooleanMin3OFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  ClassAssertion(DataMinCardinality(3 ex:flag xsd:boolean) ex:item1)
)
"
#guard checkOFNUnsat w3cBooleanMin3OFN

-- Distinct spellings of the same offset or decimal value preserve functionality.
private def w3cCrossTypeValueEqOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  FunctionalDataProperty(ex:timestamp)
  FunctionalDataProperty(ex:codeNum)
  DataPropertyAssertion(ex:timestamp ex:e1 \"2026-05-01T00:00:00Z\"^^xsd:dateTimeStamp)
  DataPropertyAssertion(ex:timestamp ex:e1 \"2026-05-01T00:00:00+00:00\"^^xsd:dateTimeStamp)
  DataPropertyAssertion(ex:codeNum ex:e1 \"42\"^^xsd:byte)
  DataPropertyAssertion(ex:codeNum ex:e1 \"+42.00\"^^xsd:decimal)
)
"
#guard checkOFNSat w3cCrossTypeValueEqOFN

-- Adversarial Mutations: non-simple role in cardinality, non-simple role in IrreflexiveObjectProperty,
-- cyclic role hierarchy violating regularity, redefining built-in datatype, and malformed literals.
private def advNonSimpleCardOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  TransitiveObjectProperty(ex:anc)
  ClassAssertion(ObjectMinCardinality(2 ex:anc ex:Person) ex:alice)
)
"
#guard match parseDocument advNonSimpleCardOFN with
  | .ok doc => !checkWellFormedOntology doc.ontology
  | .error _ => false

private def advNonSimpleIrreflOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubObjectPropertyOf(ObjectPropertyChain(ex:r1 ex:r2) ex:comp)
  IrreflexiveObjectProperty(ex:comp)
)
"
#guard match parseDocument advNonSimpleIrreflOFN with
  | .ok doc => !checkWellFormedOntology doc.ontology
  | .error _ => false

private def advIrregularRoleChainOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  SubObjectPropertyOf(ObjectPropertyChain(ex:r ex:s) ex:s)
  SubObjectPropertyOf(ObjectPropertyChain(ex:s ex:r) ex:r)
)
"
#guard match parseDocument advIrregularRoleChainOFN with
  | .ok doc => !checkWellFormedOntology doc.ontology
  | .error _ => false

private def advBuiltinRedefOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DatatypeDefinition(xsd:integer DatatypeRestriction(xsd:integer xsd:minInclusive \"0\"^^xsd:integer))
)
"
#guard match parseDocument advBuiltinRedefOFN with
  | .ok doc => (normalizeWithDefs doc.ontology).isNone && !checkWellFormedOntology doc.ontology
  | .error _ => false

private def advBadLiteralOFN : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  DataPropertyAssertion(ex:age ex:alice \"notAnInteger\"^^xsd:integer)
)
"
#guard match parseDocument advBadLiteralOFN with
  | .ok doc => !checkWellFormedOntology doc.ontology
  | .error _ => false

private def advAnonQueryOFN : String := "ClassAssertion(ex:Employee _:anonQuery)"
#guard match parseDocument employeeOFN with
  | .ok doc =>
    match normalizeWithDefs doc.ontology, parseQueryAxiom doc.prefixes advAnonQueryOFN with
    | some (defs, _), .ok qAx => (queryToInclusions defs qAx).isNone
    | _, _ => false
  | .error _ => false

private def unrankedOFNResponse (extra : String) : UInt32 × Lean.Json :=
  Sabrina.CLI.OFNQuery.run (Lean.Json.arr #[
    Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "unranked-role-chain",
    Lean.toJson (r#"Prefix(:=<http://example.org/>)
Ontology(
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
  ObjectPropertyAssertion(:r :b :a)
  ObjectPropertyAssertion(:r :b :b)
  DifferentIndividuals(:a :b)
"# ++ extra ++ ")")])

private def unrankedOFNReports (extra verdict : String) (basis := "universal-grounding-v1") : Bool :=
  let (code, body) := unrankedOFNResponse extra
  code == 0 &&
    (body.getObjValAs? String "verdict").toOption == some verdict &&
    (body.getObjValAs? Bool "lean_verified").toOption == some true &&
    (body.getObjValAs? String "decision_basis").toOption == some basis

#guard unrankedOFNReports "" "SATISFIABLE"
#guard unrankedOFNReports
  "ClassAssertion(ObjectAllValuesFrom(:r owl:Nothing) :a)" "INCONSISTENT_ONTOLOGY"
#guard unrankedOFNReports "ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :a)"
  "SATISFIABLE" "ranked-role-bounds-v1"

private def twoSuccessors :=
  "SubObjectPropertyOf(:s :r) ClassAssertion(ObjectMinCardinality(2 :s :C) :a)"

#guard unrankedOFNReports twoSuccessors "SATISFIABLE" "ranked-role-bounds-v1"
#guard unrankedOFNReports (twoSuccessors ++ " ClassAssertion(ObjectMaxCardinality(1 :s :C) :a)")
  "INCONSISTENT_ONTOLOGY" "ranked-role-bounds-v1"
-- The original non-simple chain head cannot be used in a number restriction.
#guard (unrankedOFNResponse "ClassAssertion(ObjectMinCardinality(2 :r :C) :a)").1 == 2

private def realOFNReports (range verdict : String) (basis := "sroiqd-real-reduction-v1") : Bool :=
  let ofn := r#"Prefix(:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(2 :p "# ++ range ++ ") :a))"
  let (code, body) := Sabrina.CLI.OFNQuery.run (Lean.Json.arr #[
    Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "irrational-cardinality", Lean.toJson ofn])
  code == 0 &&
    (body.getObjValAs? String "verdict").toOption == some verdict &&
    (body.getObjValAs? Bool "lean_verified").toOption == some true &&
    (body.getObjValAs? String "decision_basis").toOption == some basis

#guard realOFNReports "DataIntersectionOf(owl:real DataComplementOf(owl:rational))" "SATISFIABLE"
#guard realOFNReports
  r#"DataIntersectionOf(DatatypeRestriction(owl:real xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "1"^^xsd:integer) DataComplementOf(owl:rational))"#
  "INCONSISTENT_ONTOLOGY"

#guard realOFNReports
  r#"DatatypeRestriction(xsd:float xsd:minInclusive "0"^^xsd:float xsd:maxInclusive "0"^^xsd:float)"#
  "SATISFIABLE" "sroiqd-ordered-data-v1"
#guard realOFNReports
  r#"DatatypeRestriction(xsd:dateTime xsd:minInclusive "2026-01-01T12:00:00"^^xsd:dateTime
    xsd:maxInclusive "2026-01-01T12:00:00"^^xsd:dateTime)"#
  "INCONSISTENT_ONTOLOGY" "sroiqd-ordered-data-v1"

#guard realOFNReports
  r#"DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)"#
  "SATISFIABLE" "sroiqd-string-facets-v1"
#guard realOFNReports
  r#"DatatypeRestriction(xsd:string xsd:pattern "only"^^xsd:string)"#
  "INCONSISTENT_ONTOLOGY" "sroiqd-string-facets-v1"
#guard realOFNReports
  r#"DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string xsd:length "0"^^xsd:integer)"#
  "SATISFIABLE" "sroiqd-string-facets-v1"
#guard realOFNReports
  r#"DataIntersectionOf(DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string) xsd:string)"#
  "INCONSISTENT_ONTOLOGY" "sroiqd-string-facets-v1"
#guard realOFNReports
  r#"DatatypeRestriction(xsd:anyURI xsd:pattern "http://(a|b)"^^xsd:string)"#
  "SATISFIABLE" "sroiqd-string-facets-v1"

private def builtInDataOFNReports (body verdict : String) (basis := "sroiqd-builtin-data-prop-v1") : Bool :=
  let ofn := "Prefix(:=<http://example.org/>)\nOntology(\n" ++ body ++ "\n)"
  let (code, resp) := Sabrina.CLI.OFNQuery.run (Lean.Json.arr #[
    Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "builtin-data-prop", Lean.toJson ofn])
  code == 0 &&
    (resp.getObjValAs? String "verdict").toOption == some verdict &&
    (resp.getObjValAs? Bool "lean_verified").toOption == some true &&
    (resp.getObjValAs? String "decision_basis").toOption == some basis

#guard builtInDataOFNReports
  "Declaration(NamedIndividual(:a)) ClassAssertion(DataMinCardinality(1 owl:bottomDataProperty xsd:integer) :a)"
  "INCONSISTENT_ONTOLOGY"
#guard builtInDataOFNReports
  "Declaration(NamedIndividual(:a)) ClassAssertion(DataExactCardinality(0 owl:bottomDataProperty xsd:integer) :a)"
  "SATISFIABLE"
#guard builtInDataOFNReports
  "Declaration(NamedIndividual(:a)) ClassAssertion(DataAllValuesFrom(owl:topDataProperty xsd:integer) :a)"
  "INCONSISTENT_ONTOLOGY"
#guard builtInDataOFNReports
  "Declaration(NamedIndividual(:a)) ClassAssertion(DataMinCardinality(3 owl:topDataProperty DataComplementOf(xsd:integer)) :a)"
  "SATISFIABLE"
#guard builtInDataOFNReports
  "Declaration(DataProperty(:p)) SubDataPropertyOf(owl:topDataProperty :p) FunctionalDataProperty(:p)"
  "INCONSISTENT_ONTOLOGY"

private def exactQueryOFNReports (body query verdict basis : String)
    (imports : List (String × String) := []) : Bool :=
  let ofn := "Prefix(:=<http://example.org/>)\nOntology(\n" ++ body ++ "\n)"
  let args :=
    if imports.isEmpty then
      #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "exact-data-query",
        Lean.toJson ofn, Lean.toJson query]
    else
      #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "exact-data-query",
        Lean.toJson ofn, Lean.toJson query,
        Lean.Json.mkObj (imports.map fun (k, s) => (k, Lean.toJson s))]
  let (code, resp) := Sabrina.CLI.OFNQuery.run (Lean.Json.arr args)
  code == 0 &&
    (resp.getObjValAs? String "verdict").toOption == some verdict &&
    (resp.getObjValAs? Bool "lean_verified").toOption == some true &&
    (resp.getObjValAs? String "decision_basis").toOption == some basis

-- Exact owl:real query entailment
#guard exactQueryOFNReports
  "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(DataProperty(:x))
   SubClassOf(:A DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
   SubClassOf(DataSomeValuesFrom(:x owl:real) :B)"
  "SubClassOf(:A :B)" "ENTAILED" "sroiqd-real-query-v1"

-- Exact xsd:float order-facet query entailment
#guard exactQueryOFNReports
  "Declaration(Class(:ZeroSensor)) Declaration(DataProperty(:v)) Declaration(NamedIndividual(:s))
   EquivalentClasses(:ZeroSensor DataMinCardinality(2 :v
     DatatypeRestriction(xsd:float xsd:minInclusive \"-0.0\"^^xsd:float xsd:maxInclusive \"0.0\"^^xsd:float)))
   DataPropertyAssertion(:v :s \"-0.0\"^^xsd:float)
   DataPropertyAssertion(:v :s \"0.0\"^^xsd:float)"
  "ClassAssertion(:ZeroSensor :s)" "ENTAILED" "sroiqd-ordered-data-query-v1"

-- Exact xsd:pattern / rdf:langRange query entailment & refutation
#guard exactQueryOFNReports
  "Declaration(Class(:EnDoc)) Declaration(Class(:FrDoc)) Declaration(DataProperty(:label))
   FunctionalDataProperty(:label)
   SubClassOf(:EnDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string)))
   SubClassOf(:FrDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"fr\"^^xsd:string)))"
  "DisjointClasses(:EnDoc :FrDoc)" "ENTAILED" "sroiqd-string-facets-query-v1"

#guard exactQueryOFNReports
  "Declaration(Class(:A)) Declaration(DataProperty(:tag))
   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
   HasKey(:A () (:tag))
   DataPropertyRange(:tag DatatypeRestriction(xsd:string xsd:pattern \"only\"^^xsd:string))
   ClassAssertion(:A :a) ClassAssertion(:A :b)
   ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :a)
   ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :b)"
  "DifferentIndividuals(:a :b)" "REFUTED" "sroiqd-string-facets-query-v1"

-- Exact built-in data property query entailment & independence
#guard exactQueryOFNReports
  "Declaration(NamedIndividual(:a))"
  "DataPropertyAssertion(owl:topDataProperty :a \"42\"^^xsd:integer)"
  "ENTAILED" "sroiqd-builtin-data-prop-query-v1"

#guard exactQueryOFNReports
  "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(DataProperty(:p))
   SubDataPropertyOf(:p owl:bottomDataProperty)
   SubClassOf(:A DataSomeValuesFrom(:p xsd:integer))"
  "SubClassOf(:A :B)" "ENTAILED" "sroiqd-builtin-data-prop-query-v1"

#guard exactQueryOFNReports
  "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(DataProperty(:p))
   SubDataPropertyOf(owl:topDataProperty :p)
   SubClassOf(:A DataMinCardinality(2 :p xsd:integer))"
  "SubClassOf(:A :B)" "SENTENCE_INDEPENDENT" "sroiqd-builtin-data-prop-query-v1"

-- Exact fallback on an infinite-model ontology (no finite model exists for bounded propose)
#guard exactQueryOFNReports
  "Declaration(Class(:A)) Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a))
   InverseFunctionalObjectProperty(:r)
   SubClassOf(:A ObjectSomeValuesFrom(:r :A))
   ClassAssertion(:A :a)
   ClassAssertion(ObjectComplementOf(ObjectSomeValuesFrom(ObjectInverseOf(:r) owl:Thing)) :a)"
  "ClassAssertion(ObjectSomeValuesFrom(:r :A) :a)" "ENTAILED" "sroiqd-exact-query-v1"

-- Exact query with finite import resolution
#guard exactQueryOFNReports
  "Import(<http://example.org/codes>) Declaration(Class(:Item)) Declaration(DataProperty(:code))
   SubClassOf(:Item DataSomeValuesFrom(:code :TwoLetter))"
  "SubClassOf(:Item DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:length \"2\"^^xsd:integer)))"
  "ENTAILED" "sroiqd-string-facets-query-v1"
  [("http://example.org/codes",
    "Prefix(:=<http://example.org/>)\nOntology(<http://example.org/codes>
     Declaration(Datatype(:TwoLetter))
     DatatypeDefinition(:TwoLetter DatatypeRestriction(xsd:string xsd:pattern \"[a-z]{2}\"^^xsd:string)))")]

private def subclassPrefix : String := "Prefix(:=<http://example.org/>)\n"

private def converseHierarchy : String :=
  "SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)\n"

private def subclassResponse (extra query : String) (imports : List (String × String) := []) :
    UInt32 × Lean.Json :=
  let ofn := subclassPrefix ++ "Ontology(\n" ++ converseHierarchy ++ extra ++ "\n)"
  Sabrina.CLI.OFNQuery.run (Lean.Json.arr #[
    Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "unranked-subclass", Lean.toJson ofn, Lean.toJson query,
    Lean.Json.mkObj (imports.map fun (key, source) => (key, Lean.toJson source))])

private def subclassReports (extra query verdict : String) (imports : List (String × String) := [])
    (basis := "universal-grounding-v1") : Bool :=
  let (code, body) := subclassResponse extra query imports
  code == 0 &&
    (body.getObjValAs? String "verdict").toOption == some verdict &&
    (body.getObjValAs? Bool "lean_verified").toOption == some true &&
    (body.getObjValAs? String "decision_basis").toOption == some basis

#guard subclassReports "SubClassOf(:C :E) SubClassOf(:E :D)" "SubClassOf(:C :D)" "ENTAILED"
#guard subclassReports "" "SubClassOf(:C :D)" "SENTENCE_INDEPENDENT"
#guard subclassReports "SubClassOf(owl:Thing owl:Nothing)" "SubClassOf(:C :D)" "INCONSISTENT_ONTOLOGY"

-- The unranked chain supplies the forbidden edge r(a,b).
#guard subclassReports
  "ClassAssertion(:C :a) ObjectPropertyAssertion(:r :b :a) ObjectPropertyAssertion(:r :b :b)"
  "SubClassOf(:C ObjectAllValuesFrom(:r owl:Nothing))" "REFUTED"

-- Only the counterexample extension is universal here.
#guard subclassReports "ReflexiveObjectProperty(:r)"
  "SubClassOf(ObjectAllValuesFrom(:r owl:Nothing) owl:Nothing)" "ENTAILED"

#guard subclassReports ""
  "SubClassOf(ObjectSomeValuesFrom(:r :C) ObjectAllValuesFrom(:r :D))"
  "SENTENCE_INDEPENDENT" [] "ranked-role-bounds-v1"
#guard subclassReports twoSuccessors
  "SubClassOf(ObjectMinCardinality(2 :s :C) ObjectSomeValuesFrom(:r :C))"
  "ENTAILED" [] "ranked-role-bounds-v1"
#guard subclassReports twoSuccessors
  "SubClassOf(ObjectExactCardinality(2 :s :C) ObjectMinCardinality(2 :s :C))"
  "ENTAILED" [] "ranked-role-bounds-v1"
-- A directed edge need not be symmetric under the converse-square axiom.
-- Relaxation has a model and strengthening contradicts the negative edge.
#guard (subclassResponse
  "ObjectPropertyAssertion(:r :a :b) NegativeObjectPropertyAssertion(:r :b :a) ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :a)"
  "SubClassOf(:C :D)").1 == 2

-- A checked counterexample can settle entailment even when the four-way
-- classification needs another solver.
#guard match parseDocument (subclassPrefix ++ "Ontology(" ++ converseHierarchy ++ ")") with
  | .error _ => false
  | .ok doc => OWLUniversal.decideUniversalEntails? doc.ontology
      (.objectAll (.named "http://example.org/r") (.named nothing)) (.named nothing) == some false

-- The decisive subclass axiom comes from an imported document.
#guard subclassReports "Import(<http://example.org/class-rules>)" "SubClassOf(:C :D)" "ENTAILED"
  [("http://example.org/class-rules",
    subclassPrefix ++ "Ontology(<http://example.org/class-rules> SubClassOf(:C :D))")]
#guard (subclassResponse "Import(<http://example.org/class-rules>)" "SubClassOf(:C :D)").1 == 2

end SabrinaTests.OFN
