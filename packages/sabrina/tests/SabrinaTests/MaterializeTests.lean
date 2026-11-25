import Sabrina.OWL2.Materialize
import Sabrina.OWL2.RDF.TurtleParser
import Sabrina.OWL2.RDF.XMLParser

/-! End-to-end regression tests for `Sabrina.OWL2.Materialize` and
    `Sabrina.OWL2.RDF.Serialize`:
    - Class hierarchy (`SubClassOf`, `EquivalentClasses`, unsatisfiable classes)
    - Object property hierarchy (`SubObjectPropertyOf`)
    - Individual class & object-property realization (`ClassAssertion`, `ObjectPropertyAssertion`)
    - Individual equality inference (`SameIndividual` via `FunctionalObjectProperty`)
    - Full round-trip serialization & strict re-parsing in `.ofn`, `.ttl`, and `.owl` (RDF/XML). -/

namespace SabrinaTests.MaterializeTests

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.RDF
open Sabrina.OWL2.RDF.OWLMapping
open Sabrina.OWL2.Materialize

private def ex : String := "http://example.org/ont#"

private def sampleDecls : List EntityDecl := [
  ⟨.cls, ex ++ "Dog"⟩,
  ⟨.cls, ex ++ "Canine"⟩,
  ⟨.cls, ex ++ "Mammal"⟩,
  ⟨.cls, ex ++ "Animal"⟩,
  ⟨.cls, ex ++ "Impossible"⟩,
  ⟨.objectProperty, ex ++ "hasBrother"⟩,
  ⟨.objectProperty, ex ++ "hasSibling"⟩,
  ⟨.objectProperty, ex ++ "ancestorOf"⟩,
  ⟨.objectProperty, ex ++ "hasMother"⟩,
  ⟨.namedIndividual, ex ++ "fido"⟩,
  ⟨.namedIndividual, ex ++ "alice"⟩,
  ⟨.namedIndividual, ex ++ "bob"⟩,
  ⟨.namedIndividual, ex ++ "carol"⟩,
  ⟨.namedIndividual, ex ++ "m1"⟩,
  ⟨.namedIndividual, ex ++ "m2"⟩
]

private def sampleAnnots : List AnnotationAxiom := [
  .assertion rdfsLabel (.iri (ex ++ "Dog")) (.literal ⟨"Domestic Dog@en", rdfPlainLiteral⟩)
]

private def sampleOnt : Ontology := [
  -- Class hierarchy + equivalence + unsatisfiable class
  .subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Mammal")),
  .subClassOf (.named (ex ++ "Mammal")) (.named (ex ++ "Animal")),
  .subClassOf (.named (ex ++ "Canine")) (.named (ex ++ "Dog")),
  .subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Canine")),
  .subClassOf (.named (ex ++ "Impossible"))
    (.intersection (.named (ex ++ "Dog")) (.complement (.named (ex ++ "Dog")))),
  -- Property hierarchy + transitivity + functionality
  .subObjectProperty (.named (ex ++ "hasBrother")) (.named (ex ++ "hasSibling")),
  .transitiveObjectProperty (.named (ex ++ "ancestorOf")),
  .functionalObjectProperty (.named (ex ++ "hasMother")),
  -- ABox facts
  .classAssertion (.named (ex ++ "Dog")) (.named (ex ++ "fido")),
  .objectAssertion (.named (ex ++ "hasBrother")) (.named (ex ++ "alice")) (.named (ex ++ "bob")),
  .objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "alice")) (.named (ex ++ "bob")),
  .objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "bob")) (.named (ex ++ "carol")),
  .objectAssertion (.named (ex ++ "hasMother")) (.named (ex ++ "alice")) (.named (ex ++ "m1")),
  .objectAssertion (.named (ex ++ "hasMother")) (.named (ex ++ "alice")) (.named (ex ++ "m2"))
]

private def allOpts : MaterializeOptions := {
  includeAllSubClass := true
  includeAllTypes := true
}

-- 1. Materialization computes class, property, assertion, unsatisfiable, and SameIndividual inferences
#guard
  match materializeOntologyRuntime sampleOnt sampleDecls allOpts with
  | some res =>
    res.consistent &&
    res.inferredAxioms.contains (.subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Animal"))) &&
    res.inferredAxioms.contains (.subClassOf (.named (ex ++ "Impossible")) (.named nothing)) &&
    res.inferredAxioms.contains (.classAssertion (.named (ex ++ "Animal")) (.named (ex ++ "fido"))) &&
    res.inferredAxioms.contains (.objectAssertion (.named (ex ++ "hasSibling")) (.named (ex ++ "alice")) (.named (ex ++ "bob"))) &&
    res.inferredAxioms.contains (.objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "alice")) (.named (ex ++ "carol"))) &&
    (res.inferredAxioms.contains (.sameIndividuals [.named (ex ++ "m1"), .named (ex ++ "m2")]) ||
     res.inferredAxioms.contains (.sameIndividuals [.named (ex ++ "m2"), .named (ex ++ "m1")]))
  | none => false

-- 2. Round-trip materialized `.ofn` document preserves declarations, annotations, asserted & inferred axioms
#guard
  match materializeOntologyRuntime sampleOnt sampleDecls allOpts with
  | some res =>
    let txt := renderMaterialized .ofn sampleDecls sampleAnnots res.materializedOntology
      [("ex", ex)] (some "http://example.org/ont") (some "http://example.org/ont/v1")
    match parseDocument txt with
    | .ok doc =>
      doc.ontologyIRI == some "http://example.org/ont" &&
      doc.versionIRI == some "http://example.org/ont/v1" &&
      doc.declarations.length == sampleDecls.length &&
      doc.annotationAxioms.length == 1 &&
      doc.ontology.contains (.subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Animal"))) &&
      doc.ontology.contains (.classAssertion (.named (ex ++ "Animal")) (.named (ex ++ "fido"))) &&
      doc.ontology.contains (.objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "alice")) (.named (ex ++ "carol")))
    | .error _ => false
  | none => false

-- 3. Round-trip materialized `.ttl` (Turtle 1.1) passes strict W3C RDF mapping with zero unconsumed triples
#guard
  match materializeOntologyRuntime sampleOnt sampleDecls allOpts with
  | some res =>
    let ttl := renderMaterialized .ttl sampleDecls sampleAnnots res.materializedOntology
      [("ex", ex)] (some "http://example.org/ont") (some "http://example.org/ont/v1")
    match Turtle.parseTurtle ttl with
    | .ok g =>
      match mapRDFGraph "d0" g true with
      | .ok doc =>
        doc.ontologyIRI == some "http://example.org/ont" &&
        doc.versionIRI == some "http://example.org/ont/v1" &&
        doc.ontology.contains (.subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Animal"))) &&
        doc.ontology.contains (.classAssertion (.named (ex ++ "Animal")) (.named (ex ++ "fido"))) &&
        doc.ontology.contains (.objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "alice")) (.named (ex ++ "carol")))
      | .error _ => false
    | .error _ => false
  | none => false

-- 4. Round-trip materialized `.owl` (RDF/XML 1.1) passes strict W3C RDF mapping with zero unconsumed triples
#guard
  match materializeOntologyRuntime sampleOnt sampleDecls allOpts with
  | some res =>
    let xml := renderMaterialized .rdfxml sampleDecls sampleAnnots res.materializedOntology
      [("ex", ex)] (some "http://example.org/ont") (some "http://example.org/ont/v1")
    match XML.parseRDFXML xml with
    | .ok g =>
      match mapRDFGraph "d0" g true with
      | .ok doc =>
        doc.ontologyIRI == some "http://example.org/ont" &&
        doc.versionIRI == some "http://example.org/ont/v1" &&
        doc.ontology.contains (.subClassOf (.named (ex ++ "Dog")) (.named (ex ++ "Animal"))) &&
        doc.ontology.contains (.classAssertion (.named (ex ++ "Animal")) (.named (ex ++ "fido"))) &&
        doc.ontology.contains (.objectAssertion (.named (ex ++ "ancestorOf")) (.named (ex ++ "alice")) (.named (ex ++ "carol")))
      | .error _ => false
    | .error _ => false
  | none => false

-- 5. Inconsistent ontology is reported as inconsistent rather than producing spurious inferences
#guard
  let badOnt : Ontology := [
    .disjointClasses [.named (ex ++ "A"), .named (ex ++ "B")],
    .classAssertion (.named (ex ++ "A")) (.named (ex ++ "x")),
    .classAssertion (.named (ex ++ "B")) (.named (ex ++ "x"))
  ]
  match materializeOntologyRuntime badOnt with
  | some res => !res.consistent && res.inferredAxioms.isEmpty
  | none => false

end SabrinaTests.MaterializeTests
