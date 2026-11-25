import Sabrina.OWL2.StrictTyping
import Sabrina.CLI.OFNQuery
import Sabrina.CLI.ImportCatalog

/-! Milestone B regression tests:
1. Entity `Declaration(...)` and annotation-axiom parsing in `FunctionalSyntax`.
2. Enhanced FSS grammar: prefixed ontology/version IRIs, Unicode identifiers,
   `PN_LOCAL_ESC` escaping, and rejection of invalid `<IRI>` whitespace.
3. W3C OWL 2 DL §5.8.1 reserved-vocabulary declaration checks.
4. W3C OWL 2 DL §5.8.2 entity typing completeness & punning rules:
   - Forbidden clashes: Class/Datatype, ObjectProperty/DataProperty,
     ObjectProperty/AnnotationProperty, DataProperty/AnnotationProperty.
   - Permitted punning: Class/NamedIndividual, Class/ObjectProperty,
     NamedIndividual/DataProperty.
   - Optional `NamedIndividual` declarations vs mandatory Class, Datatype,
     ObjectProperty, DataProperty, and AnnotationProperty declarations.
   - Cross-document declaration sharing across `Import(...)` closures.
5. OASIS XML Catalog (`catalog-v001.xml`) pure parser tests. -/

namespace SabrinaTests.TypingAndCatalog

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.StrictTyping
open Sabrina.CLI.ImportCatalog

private def checkStrictDoc (ofn : String) (lib : List (IRI × String) := []) : Bool :=
  match resolveImportClosure ofn lib with
  | .ok c => checkStrictTypedOWL2DL c.declarations c.annotationAxioms c.ontology
  | .error _ => false

/-! ### 1. Declarations, Annotations & Enhanced FSS Grammar -/

private def fullHeaderAndAnnotsOFN : String := "
Prefix(:=<http://example.org/b#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(:ont :v1
  Annotation(rdfs:comment \"Ontology header comment\")
  Declaration(Annotation(rdfs:label \"Class A\") Class(:A))
  Declaration(Class(:SãoPaulo))
  Declaration(ObjectProperty(:has\\/part))
  Declaration(AnnotationProperty(:note))
  Declaration(NamedIndividual(:a))
  AnnotationAssertion(:note :A \"annotated\"@en)
  SubAnnotationPropertyOf(:note rdfs:comment)
  AnnotationPropertyDomain(:note :A)
  AnnotationPropertyRange(:note xsd:string)
  SubClassOf(:A :SãoPaulo)
  ObjectPropertyAssertion(:has\\/part :a :a)
)"

#guard
  match parseDocument fullHeaderAndAnnotsOFN with
  | .ok doc =>
    doc.ontologyIRI == some "http://example.org/b#ont" &&
    doc.versionIRI == some "http://example.org/b#v1" &&
    doc.declarations.length == 5 &&
    doc.annotationAxioms.length == 4 &&
    doc.ontology.length == 2
  | .error _ => false

#guard checkStrictDoc fullHeaderAndAnnotsOFN

-- Whitespace inside <IRI> is rejected by tokenizer
#guard (parseDocument "Ontology(<http://example.org/bad iri>)").isOk == false

-- Malformed Declaration kind is rejected
#guard (parseDocument "Prefix(:=<http://example.org/b#>) Ontology(Declaration(Bogus(:A)))").isOk == false

/-! ### 2. W3C §5.8.1 Reserved-Vocabulary Declaration Rules -/

-- Declaring built-in entities with their standard kind is allowed
#guard checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Ontology(
  Declaration(Class(owl:Thing))
  Declaration(AnnotationProperty(rdfs:label))
  Declaration(Class(:A))
  AnnotationAssertion(rdfs:label :A \"A\")
  SubClassOf(:A owl:Thing)
)"

-- Declaring a reserved IRI with the wrong kind or non-built-in owl: IRI is rejected
#guard !checkStrictDoc "
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(Declaration(Class(owl:topObjectProperty)))"

#guard !checkStrictDoc "
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(Declaration(ObjectProperty(owl:customProp)))"

#guard !checkStrictDoc "
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(Declaration(NamedIndividual(owl:Thing)))"

/-! ### 3. W3C §5.8.2 Mandatory Declarations & Optional Individuals -/

-- NamedIndividual declarations are OPTIONAL in W3C OWL 2 DL §5.8.2
#guard checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(Class(:Person))
  ClassAssertion(:Person :alice)
)"

-- Undeclared Class is rejected
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(Class(:A))
  SubClassOf(:A :UndeclaredB)
)"

-- Undeclared ObjectProperty is rejected
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(Class(:A))
  SubClassOf(:A ObjectSomeValuesFrom(:undeclaredR :A))
)"

-- Undeclared DataProperty is rejected
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
  DataPropertyAssertion(:undeclaredDP :a \"1\"^^xsd:integer)
)"

-- Undeclared custom Datatype in DatatypeDefinition is rejected (§5.8.2)
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
  DatatypeDefinition(:AdultAge DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer))
)"

-- Declared custom Datatype in DatatypeDefinition is accepted
#guard checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
  Declaration(Datatype(:AdultAge))
  DatatypeDefinition(:AdultAge DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer))
)"

-- Undeclared AnnotationProperty is rejected
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(Class(:A))
  AnnotationAssertion(:undeclaredNote :A \"hi\")
)"

/-! ### 4. W3C §5.8.2 Legal vs Illegal Punning -/

-- LEGAL punning: Class + NamedIndividual, Class + ObjectProperty, NamedIndividual + DataProperty
#guard checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
  Declaration(Class(:Eagle))
  Declaration(NamedIndividual(:Eagle))
  Declaration(Class(:Species))
  Declaration(ObjectProperty(:Eagle))
  Declaration(DataProperty(:tag))
  Declaration(NamedIndividual(:tag))
  ClassAssertion(:Species :Eagle)
  ObjectPropertyAssertion(:Eagle :Eagle :tag)
  DataPropertyAssertion(:tag :tag \"ok\"^^xsd:string)
)"

-- ILLEGAL punning: Class + Datatype
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(Class(:Clash))
  Declaration(Datatype(:Clash))
)"

-- ILLEGAL punning: ObjectProperty + DataProperty
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(ObjectProperty(:p))
  Declaration(DataProperty(:p))
)"

-- ILLEGAL punning: ObjectProperty + AnnotationProperty
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(ObjectProperty(:p))
  Declaration(AnnotationProperty(:p))
)"

-- ILLEGAL punning: DataProperty + AnnotationProperty
#guard !checkStrictDoc "
Prefix(:=<http://example.org/b#>)
Ontology(
  Declaration(DataProperty(:p))
  Declaration(AnnotationProperty(:p))
)"

/-! ### 5. Cross-Document Import-Closure Typing & CLI Strict Mode -/

private def baseVocabOFN : String := "
Prefix(:=<http://example.org/lib#>)
Ontology(<http://example.org/lib>
  Declaration(Class(:Animal))
  Declaration(ObjectProperty(:eats))
)"

private def childImpOFN : String := "
Prefix(:=<http://example.org/lib#>)
Ontology(<http://example.org/child>
  Import(<http://example.org/lib>)
  Declaration(Class(:Cat))
  SubClassOf(:Cat :Animal)
  SubClassOf(:Cat ObjectSomeValuesFrom(:eats :Animal))
)"

#guard checkStrictDoc childImpOFN [("http://example.org/lib", baseVocabOFN)]

-- CLI end-to-end: strict mode rejects undeclared class in query and accepts declared closure
#guard
  let req := Lean.Json.arr #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "imp-ok",
    Lean.toJson childImpOFN, Lean.toJson "SubClassOf(:Cat :Animal)",
    Lean.Json.mkObj [("http://example.org/lib", Lean.toJson baseVocabOFN)],
    Lean.Json.mkObj [("strict_owl2dl", Lean.toJson true)]]
  let (code, res) := Sabrina.CLI.OFNQuery.run req false
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED" &&
    (res.getObjValAs? Bool "owl2dl_valid").toOption == some true

#guard
  let req := Lean.Json.arr #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "imp-undecl-q",
    Lean.toJson childImpOFN, Lean.toJson "SubClassOf(:Cat :NotDeclared)",
    Lean.Json.mkObj [("http://example.org/lib", Lean.toJson baseVocabOFN)],
    Lean.Json.mkObj [("strict_owl2dl", Lean.toJson true)]]
  let (code, res) := Sabrina.CLI.OFNQuery.run req false
  code == 2 && (res.getObjValAs? String "verdict").toOption == some "UNSUPPORTED" &&
    (res.getObjValAs? Bool "owl2dl_valid").toOption == some false

/-! ### 6. OASIS XML Catalog (`catalog-v001.xml`) Pure Parser -/

private def sampleCatalogXML : String := "
<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>
<catalog prefer=\"public\" xmlns=\"urn:oasis:names:tc:entity:xmlns:xml:catalog\">
  <!-- Commented out entry: <uri name=\"http://ignored\" uri=\"ignored.ofn\"/> -->
  <uri name=\"http://example.org/root\" uri=\"root.ofn\"/>
  <group id=\"Folder Repository\" prefer=\"public\" xml:base=\"imports\">
    <uri id=\"u1\" name=\"http://example.org/lib\" uri=\"lib.ofn\"/>
    <uri id=\"u2\" name=\"http://example.org/sub\" uri=\"nested/sub.ofn\"/>
  </group>
</catalog>"

#guard parseOasisCatalogEntries sampleCatalogXML == [
  ("http://example.org/root", "root.ofn"),
  ("http://example.org/lib", "imports/lib.ofn"),
  ("http://example.org/sub", "imports/nested/sub.ofn")
]

end SabrinaTests.TypingAndCatalog
