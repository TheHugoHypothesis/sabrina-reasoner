import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.DataRanges
import Sabrina.OWL2.SROIQD.Termination.DataRangeExact
import Sabrina.OWL2.SROIQD.Termination.WiderDataReduction
import Sabrina.OWL2.SROIQD.Termination.RealDecision
import Sabrina.OWL2.FastClassification

/-!
Regression tests for RDF/Turtle ontology-header metadata mapping, cross-file
import-closure declaration sharing (`AllDecl(G)`), and exact multi-datatype
preparation scaling:

1. Ontology-header metadata (`owl:Ontology` with undeclared `dcterms:modified` or
   custom `xsd:date` annotations, both named IRI and blank-node headers) must remain
   ontology annotations rather than leaking into logical `dataAssertion` axioms.
2. Two-phase import-closure declaration sharing (`AllDecl(G)` per W3C OWL 2 RDF Mapping
   §3.1.2 Table 5): an `owl:AnnotationProperty` declared in an imported document prevents
   logical assertion leaks in importing documents.
3. Family-, subtype-, and interval-pruned Venn partitions (`prunedWiderPartitions` and
   `prunedExactPartitions`), empty-interval filtering in `subtractRatBoundsOne` /
   `subtractNatBoundsOne` / `subtractBoundsOne`, and bounded `SolvedRange.finiteValues?`
   prevent exponential/memory blowups across 28+ datatype atoms and wide integer subtypes
   (`xsd:int`, `xsd:long`).
-/

namespace SabrinaTests.RDFAndDatatypeScalingTests

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.DataRanges
open Sabrina.OWL2.RDF.OWLMapping
open Sabrina.OWL2.SROIQD.Termination
open Sabrina.OWL2.SROIQD.Termination.WiderData

private def namedHeaderDateTTL : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix ex: <http://example.org/> .

<http://example.org/ont> a owl:Ontology ;
    dcterms:modified \"2026-11-17\"^^xsd:date ;
    ex:customHeaderDate \"2024-06-15\"^^xsd:date .

ex:Device a owl:Class .
ex:Sensor a owl:Class ;
    rdfs:subClassOf ex:Device ;
    dcterms:modified \"2026-11-18\"^^xsd:date .
"

private def bnodeHeaderDateTTL : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix ex: <http://example.org/> .

[] a owl:Ontology ;
    ex:releasedOn \"2026-11-17\"^^xsd:date .

ex:A a owl:Class .
"

private def importedVocabTTL : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix ex: <http://example.org/> .

<http://example.org/vocab> a owl:Ontology .
ex:myCustomDate a owl:AnnotationProperty .
"

private def importingRootTTL : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix ex: <http://example.org/> .

<http://example.org/root> a owl:Ontology ;
    owl:imports <http://example.org/vocab> .

ex:Component a owl:Class ;
    ex:myCustomDate \"2026-11-17\"^^xsd:date .
"

private def hasNoDataAssertions (ont : Ontology) : Bool :=
  ont.all fun
    | .dataAssertion _ _ _ => false
    | _ => true

#guard match resolveImportClosureAuto namedHeaderDateTTL [] false with
  | .ok cl => hasNoDataAssertions cl.ontology && decideRealOntology? cl.ontology == some true
  | .error _ => false

#guard match resolveImportClosureAuto bnodeHeaderDateTTL [] false with
  | .ok cl => hasNoDataAssertions cl.ontology && decideRealOntology? cl.ontology == some true
  | .error _ => false

#guard match resolveImportClosureAuto importingRootTTL
    [("http://example.org/vocab", importedVocabTTL)] false with
  | .ok cl => hasNoDataAssertions cl.ontology && decideRealOntology? cl.ontology == some true
  | .error _ => false

-- 28 distinct OWL 2 datatype atoms across all families: prunedWiderPartitions must stay compact
private def all28Atoms : List DataRange :=
  [ xsd "string", xsd "normalizedString", xsd "token", xsd "Name", xsd "NCName",
    xsd "integer", xsd "int", xsd "long", xsd "short", xsd "byte",
    xsd "nonNegativeInteger", xsd "positiveInteger", xsd "unsignedInt",
    xsd "decimal", owlReal, owlRational, xsd "double", xsd "float",
    xsd "boolean", xsd "dateTime", xsd "dateTimeStamp", xsd "anyURI",
    xsd "hexBinary", xsd "base64Binary", rdf "XMLLiteral", rdf "PlainLiteral",
    xsd "nonPositiveInteger", xsd "negativeInteger" ].map DataRange.datatype

#guard (prunedWiderPartitions all28Atoms).length ≤ 100

-- 25 pairwise-disjoint integer intervals: prunedExactPartitions must produce exactly 26 cells (not 2^25)
private def disjoint25Intervals : List DataRange :=
  (List.range 25).map fun k => intIntervalDR (2 * k) (2 * k + 1)

#guard (prunedExactPartitions disjoint25Intervals).length == 26

-- Wide integer subtypes (`xsd:int`, `xsd:long`) must not materialize 2^32 / 2^64 elements in finiteValues?
#guard match compileSolvedRange (.datatype (xsd "int")) with
  | some sr => sr.finiteValues?.isNone
  | none => false

#guard match compileSolvedRange (.datatype (xsd "long")) with
  | some sr => sr.finiteValues?.isNone
  | none => false

-- Small bounded integer subtypes (`xsd:byte`, 256 values) still enumerate cleanly
#guard match compileSolvedRange (.datatype (xsd "byte")) with
  | some sr => (sr.finiteValues?.map List.length) == some 256
  | none => false

-- Shared blank-node class expression referenced by multiple axioms + owl:Axiom annotation
private def sharedBNodeTTL : String :=
"@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix ex: <http://example.org/> .

<http://example.org/shared> a owl:Ontology .
ex:r a owl:ObjectProperty .
ex:A a owl:Class ;
    owl:equivalentClass _:r1 ;
    rdfs:subClassOf _:r1 .
ex:B a owl:Class ;
    rdfs:subClassOf _:r1 .
ex:C a owl:Class .
_:r1 a owl:Restriction ;
    owl:onProperty ex:r ;
    owl:someValuesFrom ex:C .
[] a owl:Axiom ;
    owl:annotatedSource ex:B ;
    owl:annotatedProperty rdfs:subClassOf ;
    owl:annotatedTarget _:r1 ;
    rdfs:comment \"annotated shared restriction\" .
"

#guard match resolveImportClosureAuto sharedBNodeTTL [] false with
  | .ok cl =>
    let hasSubB := cl.ontology.any fun
      | .subClassOf (.named "http://example.org/B") (.objectSome (.named "http://example.org/r") (.named "http://example.org/C")) => true
      | _ => false
    let hasEqA := cl.ontology.any fun
      | .equivalentClasses [.named "http://example.org/A", .objectSome (.named "http://example.org/r") (.named "http://example.org/C")] => true
      | _ => false
    hasSubB && hasEqA && decideRealOntology? cl.ontology == some true
  | .error _ => false

end SabrinaTests.RDFAndDatatypeScalingTests
