import Sabrina.OWL2.Justification

/-! Regression tests for `Sabrina.OWL2.Justification`:
    - Single & multiple (diamond) minimal justifications for entailment
    - Single & multiple minimal justifications for inconsistency
    - Stripping noisy irrelevant axioms via `FastLocality` + QuickXplain
    - Non-entailed queries / satisfiable ontologies cleanly return empty justification lists
    - Verifies strict minimality (removing any single axiom breaks entailment/inconsistency). -/

namespace SabrinaTests.JustificationTests

open Sabrina.OWL2
open Sabrina.OWL2.Classification
open Sabrina.OWL2.Materialize
open Sabrina.OWL2.Justification

-- Diamond entailment: A ⊑ C has TWO distinct minimal justifications:
--   J1 = {A ⊑ B1, B1 ⊑ C}  and  J2 = {A ⊑ B2, B2 ⊑ C}, plus irrelevant noise axioms.
private def diamondOnt : Ontology := [
  .subClassOf (.named "ex:Noise1") (.named "ex:Noise2"),
  .subClassOf (.named "ex:A") (.named "ex:B1"),
  .subClassOf (.named "ex:B1") (.named "ex:C"),
  .subClassOf (.named "ex:Noise3") (.named "ex:Noise4"),
  .subClassOf (.named "ex:A") (.named "ex:B2"),
  .subClassOf (.named "ex:B2") (.named "ex:C"),
  .subClassOf (.named "ex:C") (.named "ex:D")
]

private def checkStrictMinimalEntails (J : Ontology) (qAx : Axiom) : Bool :=
  decidesAxiomEntails fastConsistencyCheck J qAx == some true &&
  J.all fun a => decidesAxiomEntails fastConsistencyCheck (J.filter (· != a)) qAx == some false

private def checkStrictMinimalUnsat (J : Ontology) : Bool :=
  fastConsistencyCheck J == some false &&
  J.all fun a => fastConsistencyCheck (J.filter (· != a)) == some true

-- 1. Single minimal justification for A ⊑ C has exact size 2 and is strictly minimal
#guard
  let q := Axiom.subClassOf (.named "ex:A") (.named "ex:C")
  match explainEntailmentRuntime diamondOnt q 1 with
  | some res =>
    res.entailed && res.justifications.length == 1 &&
    match res.justifications with
    | [J] => J.length == 2 && checkStrictMinimalEntails J q
    | _ => false
  | none => false

-- 2. Reiter HST finds BOTH distinct minimal justifications for diamond A ⊑ C
#guard
  let q := Axiom.subClassOf (.named "ex:A") (.named "ex:C")
  match explainEntailmentRuntime diamondOnt q 5 with
  | some res =>
    res.entailed && res.justifications.length == 2 &&
    res.justifications.all fun J => J.length == 2 && checkStrictMinimalEntails J q
  | none => false

-- 3. Non-entailed query D ⊑ A returns entailed = false and empty justifications
#guard
  let q := Axiom.subClassOf (.named "ex:D") (.named "ex:A")
  match explainEntailmentRuntime diamondOnt q 5 with
  | some res => !res.entailed && res.justifications.isEmpty
  | none => false

-- 4. Multiple independent inconsistency causes: two separate clashes + noise
private def twoClashOnt : Ontology := [
  .subClassOf (.named "ex:NoiseA") (.named "ex:NoiseB"),
  .disjointClasses [.named "ex:Cat", .named "ex:Dog"],
  .classAssertion (.named "ex:Cat") (.named "ex:fido"),
  .classAssertion (.named "ex:Dog") (.named "ex:fido"),
  .functionalObjectProperty (.named "ex:hasMother"),
  .objectAssertion (.named "ex:hasMother") (.named "ex:alice") (.named "ex:m1"),
  .objectAssertion (.named "ex:hasMother") (.named "ex:alice") (.named "ex:m2"),
  .differentIndividuals [.named "ex:m1", .named "ex:m2"]
]

#guard
  match explainInconsistencyRuntime twoClashOnt 5 with
  | some res =>
    res.inconsistent && res.justifications.length == 2 &&
    res.justifications.all checkStrictMinimalUnsat &&
    res.justifications.any (fun J => J.length == 3) &&
    res.justifications.any (fun J => J.length == 4)
  | none => false

-- 5. Satisfiable ontology returns inconsistent = false and empty justifications
#guard
  match explainInconsistencyRuntime diamondOnt 5 with
  | some res => !res.inconsistent && res.justifications.isEmpty
  | none => false

end SabrinaTests.JustificationTests
