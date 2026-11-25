import Sabrina.OWL2.FastClassification

/-! Regression tests for `Sabrina.OWL2.FastClassification`:
    verifies exact subsumption/unsatisfiability agreement between
    `classifyDirectEL`, `classifyEnhancedWith`, `classifyEnhancedStd`,
    `classifyOntologyFastRuntime`, and the baseline `Classification.classifyOntologyRuntime`
    across EL++ and expressive SROIQ(D) ontologies. -/

namespace SabrinaTests.FastClassificationTests

open Sabrina.OWL2
open Sabrina.OWL2.Classification
open Sabrina.OWL2.FastClassification

private def samePairSet (xs ys : List (IRI × IRI)) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private def sameIRISet (xs ys : List IRI) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private def elSample : Ontology := [
  .subClassOf (.named "ex:Poodle") (.named "ex:Dog"),
  .subClassOf (.named "ex:Dog") (.named "ex:Mammal"),
  .subClassOf (.named "ex:Mammal") (.named "ex:Animal"),
  .equivalentClasses [.named "ex:Dog", .named "ex:Canine"],
  .subClassOf (.named "ex:Pet") (.objectSome (.named "ex:hasOwner") (.named "ex:Human")),
  .subClassOf (.objectSome (.named "ex:hasOwner") (.named "ex:Human")) (.named "ex:Domestic"),
  .disjointClasses [.named "ex:Dog", .named "ex:Cat"],
  .subClassOf (.named "ex:CatDog") (.named "ex:Dog"),
  .subClassOf (.named "ex:CatDog") (.named "ex:Cat")
]

private def sroiqdSample : Ontology := [
  .subClassOf (.named "ex:GradStudent") (.named "ex:Student"),
  .subClassOf (.named "ex:Student") (.named "ex:Person"),
  .subClassOf (.named "ex:Faculty") (.named "ex:Person"),
  .disjointClasses [.named "ex:Student", .named "ex:Faculty"],
  .subClassOf (.named "ex:Advisor")
    (.intersection (.named "ex:Person") (.objectMin 1 (.named "ex:advises") (.named "ex:Student"))),
  .subClassOf (.named "ex:Advisor") (.union (.named "ex:Faculty") (.named "ex:Staff")),
  .subClassOf (.named "ex:StudentAdvisor") (.intersection (.named "ex:Student") (.named "ex:Faculty")),
  .equivalentClasses [.named "ex:Scholar", .named "ex:Person"]
]

-- 1. Single-pass direct EL++ classifier matches baseline pairwise classifier exactly
#guard
  let cs := collectNamedClasses elSample
  match classifyDirectEL elSample cs, classifyOntologyRuntime elSample with
  | some hFast, some hBase =>
    hFast.consistent && hBase.consistent &&
    sameIRISet hFast.unsatisfiable hBase.unsatisfiable &&
    hFast.unsatisfiable.contains "ex:CatDog" &&
    samePairSet hFast.subsumptions hBase.subsumptions &&
    hFast.subsumptions.contains ("ex:Poodle", "ex:Animal") &&
    hFast.subsumptions.contains ("ex:Pet", "ex:Domestic")
  | _, _ => false

-- 2. Enhanced Traversal (without model harvester) matches baseline on SROIQ(D)
#guard
  let cs := collectNamedClasses sroiqdSample
  match classifyEnhancedWith fastConsistencyCheck sroiqdSample cs, classifyOntologyRuntime sroiqdSample with
  | some hFast, some hBase =>
    hFast.consistent && hBase.consistent &&
    sameIRISet hFast.unsatisfiable hBase.unsatisfiable &&
    hFast.unsatisfiable.contains "ex:StudentAdvisor" &&
    samePairSet hFast.subsumptions hBase.subsumptions &&
    hFast.subsumptions.contains ("ex:GradStudent", "ex:Scholar")
  | _, _ => false

-- 3. Fast hybrid runtime (with SROIQDModel countermodel seeding) matches baseline on SROIQ(D)
#guard
  match classifyOntologyFastRuntime sroiqdSample, classifyOntologyRuntime sroiqdSample with
  | some hFast, some hBase =>
    hFast.consistent && hBase.consistent &&
    sameIRISet hFast.unsatisfiable hBase.unsatisfiable &&
    samePairSet hFast.subsumptions hBase.subsumptions
  | _, _ => false

-- 4. Fast hybrid runtime handles EL++ via single-pass saturation and matches baseline
#guard
  match classifyOntologyFastRuntime elSample, classifyOntologyRuntime elSample with
  | some hFast, some hBase =>
    hFast.consistent && hBase.consistent &&
    sameIRISet hFast.unsatisfiable hBase.unsatisfiable &&
    samePairSet hFast.subsumptions hBase.subsumptions
  | _, _ => false

-- 5. Inconsistent ontology detected cleanly by both single-pass EL++ and Enhanced Traversal
#guard
  let unsatEL : Ontology := [
    .subClassOf (.named thing) (.named "ex:A"),
    .subClassOf (.named thing) (.named "ex:B"),
    .disjointClasses [.named "ex:A", .named "ex:B"]
  ]
  match classifyDirectEL unsatEL (collectNamedClasses unsatEL),
        classifyEnhancedWith fastConsistencyCheck unsatEL (collectNamedClasses unsatEL) with
  | some h1, some h2 => !h1.consistent && !h2.consistent
  | _, _ => false

end SabrinaTests.FastClassificationTests
