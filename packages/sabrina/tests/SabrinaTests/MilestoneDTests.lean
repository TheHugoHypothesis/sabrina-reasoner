import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.Classification
import Sabrina.CLI.OFNQuery

/-! Regression tests for Milestone D:
    - Native W3C RDF/XML parser & OWL 2 RDF-to-Structural mapping
    - Native W3C Turtle 1.1 parser & OWL 2 RDF-to-Structural mapping
    - Extended exact query entailment (property axioms, chains, n-ary, anonymous individuals)
    - Certified TBox classification & ABox realization via API and CLI wire handlers. -/

namespace SabrinaTests.MilestoneD

open Lean
open Sabrina.OWL2
open Sabrina.OWL2.RDF
open Sabrina.OWL2.RDF.OWLMapping
open Sabrina.OWL2.Classification
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

/-! ### 1. Native RDF/XML Parser & OWL 2 Mapping -/

private def sampleRDFXML : String := "<?xml version=\"1.0\"?>
<!DOCTYPE rdf:RDF [
  <!ENTITY xsd \"http://www.w3.org/2001/XMLSchema#\">
  <!ENTITY ex \"http://example.org/bio#\">
]>
<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"
         xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"
         xmlns:owl=\"http://www.w3.org/2002/07/owl#\"
         xmlns:ex=\"http://example.org/bio#\"
         xml:base=\"http://example.org/bio\">
  <owl:Ontology rdf:about=\"http://example.org/bio\"/>
  <owl:Class rdf:about=\"&ex;Animal\"/>
  <owl:Class rdf:about=\"&ex;Mammal\">
    <rdfs:subClassOf rdf:resource=\"&ex;Animal\"/>
  </owl:Class>
  <owl:Class rdf:about=\"&ex;Dog\">
    <rdfs:subClassOf rdf:resource=\"&ex;Mammal\"/>
  </owl:Class>
  <owl:Class rdf:about=\"&ex;Cat\">
    <rdfs:subClassOf rdf:resource=\"&ex;Mammal\"/>
    <owl:disjointWith rdf:resource=\"&ex;Dog\"/>
  </owl:Class>
  <owl:ObjectProperty rdf:about=\"&ex;parentOf\"/>
  <owl:ObjectProperty rdf:about=\"&ex;ancestorOf\">
    <rdf:type rdf:resource=\"http://www.w3.org/2002/07/owl#TransitiveProperty\"/>
    <owl:propertyChainAxiom rdf:parseType=\"Collection\">
      <rdf:Description rdf:about=\"&ex;parentOf\"/>
      <rdf:Description rdf:about=\"&ex;ancestorOf\"/>
    </owl:propertyChainAxiom>
  </owl:ObjectProperty>
  <owl:NamedIndividual rdf:about=\"&ex;fido\">
    <rdf:type rdf:resource=\"&ex;Dog\"/>
  </owl:NamedIndividual>
</rdf:RDF>"

#guard
  match parseDocumentAuto sampleRDFXML true with
  | .ok doc =>
    doc.ontologyIRI == some "http://example.org/bio" &&
    doc.declarations.length == 7 &&
    doc.ontology.length == 7
  | .error _ => false

-- Live strict OWL 2 DL entailment directly on RDF/XML input
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "rdfxml-sub",
    toJson sampleRDFXML,
    toJson "Prefix(ex:=<http://example.org/bio#>) SubClassOf(ex:Dog ex:Animal)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

-- Live RDF/XML inconsistency rejection (Cat & Dog disjoint)
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "rdfxml-disj",
    toJson sampleRDFXML,
    toJson "Prefix(ex:=<http://example.org/bio#>) ClassAssertion(ex:Cat ex:fido)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "REFUTED"

/-! ### 2. Native Turtle 1.1 Parser & OWL 2 Mapping -/

private def sampleTurtle : String := "
@prefix : <http://example.org/org#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<http://example.org/org> a owl:Ontology .

:Person a owl:Class .
:Employee a owl:Class ; rdfs:subClassOf :Person .
:Manager a owl:Class ;
  owl:equivalentClass [
    a owl:Class ;
    owl:intersectionOf ( :Employee [ a owl:Restriction ; owl:onProperty :manages ; owl:someValuesFrom :Person ] )
  ] .
:Ghost a owl:Class ;
  rdfs:subClassOf :Employee , [ a owl:Class ; owl:complementOf :Person ] .

:manages a owl:ObjectProperty ;
  rdfs:domain :Employee ;
  rdfs:range :Person .

:alice a owl:NamedIndividual , :Employee ;
  :manages :bob .
:bob a owl:NamedIndividual , :Person .
"

#guard
  match parseDocumentAuto sampleTurtle true with
  | .ok doc => doc.ontologyIRI == some "http://example.org/org" && doc.ontology.length >= 7
  | .error _ => false

-- Manager entailment from Turtle existential restriction
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "ttl-mgr",
    toJson sampleTurtle,
    toJson "Prefix(:=<http://example.org/org#>) ClassAssertion(:Manager :alice)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

-- Strict RDF unconsumed-triple rejection (dangling malformed owl:Restriction)
private def malformedTurtle : String := "
@prefix : <http://example.org/bad#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
_:b1 rdf:first :X .
"

#guard
  match parseDocumentAuto malformedTurtle true with
  | .error _ => true
  | .ok _ => false

/-! ### 3. Extended Query Entailment (Property Axioms, N-ary, Anonymous Individuals) -/

private def propAxiomOFN : String := "
Prefix(:=<http://example.org/prop#>)
Ontology(<http://example.org/prop>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  Declaration(ObjectProperty(:t))
  Declaration(NamedIndividual(:a))
  SubObjectPropertyOf(:r :s)
  SubObjectPropertyOf(:s :t)
  SymmetricObjectProperty(:r)
  ObjectPropertyDomain(:s :A)
  ClassAssertion(:A :a)
  ObjectPropertyAssertion(:r :a :a)
)"

-- Transitive sub-property entailment: SubObjectPropertyOf(:r :t)
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "ext-subprop",
    toJson propAxiomOFN,
    toJson "SubObjectPropertyOf(:r :t)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

-- Domain inheritance: ObjectPropertyDomain(:r :A)
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "ext-dom",
    toJson propAxiomOFN,
    toJson "ObjectPropertyDomain(:r :A)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

-- Existential anonymous-individual query: ClassAssertion(:A _:x)
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "ext-anon",
    toJson propAxiomOFN,
    toJson "ClassAssertion(:A _:x)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

-- Existential anonymous self-loop query: ObjectPropertyAssertion(:s _:x _:x)
#guard
  let req := Json.arr #[
    toJson "sabrina-ofn-query-v1", toJson "ext-anon-self",
    toJson propAxiomOFN,
    toJson "ObjectPropertyAssertion(:s _:x _:x)"]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "ENTAILED"

/-! ### 4. Certified TBox Classification & ABox Realization -/

#guard
  let req := Json.arr #[toJson "sabrina-classify-v1", toJson "ttl-classify", toJson sampleTurtle]
  let (code, res) := Sabrina.CLI.OFNQuery.runClassify req true
  let okVerdict := (res.getObjValAs? String "verdict").toOption == some "CLASSIFIED"
  let unsatOk := match res.getObjVal? "classification" >>= fun c => c.getObjValAs? (List String) "unsatisfiable" with
    | .ok us => us == ["http://example.org/org#Ghost"]
    | .error _ => false
  code == 0 && okVerdict && unsatOk

#guard
  let req := Json.arr #[toJson "sabrina-realize-v1", toJson "ttl-realize", toJson sampleTurtle]
  let (code, res) := Sabrina.CLI.OFNQuery.runRealize req true
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "REALIZED"

end SabrinaTests.MilestoneD
