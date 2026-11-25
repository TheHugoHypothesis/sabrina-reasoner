import Sabrina.OWL2.SROIQD.Termination.UniversalRoleRestrictions

/-! Live fuel-free regressions for universal-role class restrictions
(`∃ owl:topObjectProperty.C`, `∀ owl:topObjectProperty.C`, their inverses,
nested occurrences, interaction with `HasKey` and named individuals, and
composition with top-headed chains, chain aliases, and bottom properties). -/

namespace Sabrina.OWL2.SROIQD.Termination.BlockedForest.UniversalRoleExamples

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes (datatypeMap)

private def clsA : IRI := "urn:univ:A"
private def clsB : IRI := "urn:univ:B"
private def clsC : IRI := "urn:univ:C"
private def clsK : IRI := "urn:univ:K"
private def propR : IRI := "urn:univ:r"
private def propS : IRI := "urn:univ:s"
private def propT : IRI := "urn:univ:t"
private def dataP : IRI := "urn:univ:dp"
private def indA : Individual := .named "urn:univ:a"
private def indB : Individual := .named "urn:univ:b"
private def indC : Individual := .named "urn:univ:c"
private def topProp : ObjectProperty := .named topObjectProperty
private def invTopProp : ObjectProperty := .inverse topObjectProperty
private def intLit (s : String) : Literal := ⟨s, Datatypes.xsd "integer"⟩

/-! ### 1. Non-local witness outside any local branch -/

/-- `a ∈ A`, `b ∈ B` (disconnected from `a` by any ordinary role),
`A ⊓ ∃ U.B ⊑ C`, and `a ∈ ¬C` is unsatisfiable because `b` globally witnesses `∃ U.B`. -/
private def nonLocalWitnessUnsat : Ontology :=
  [.classAssertion (.named clsA) indA,
   .classAssertion (.named clsB) indB,
   .subClassOf (.intersection (.named clsA) (.objectSome topProp (.named clsB))) (.named clsC),
   .classAssertion (.complement (.named clsC)) indA]

#guard decideAdmittedOntology? nonLocalWitnessUnsat == none
#guard decideWithUniversalRole? nonLocalWitnessUnsat == some false

/-- Without `b ∈ B`, `B` can be globally empty so `∃ U.B` is false and the ontology is satisfiable. -/
private def nonLocalWitnessSat : Ontology :=
  [.classAssertion (.named clsA) indA,
   .subClassOf (.intersection (.named clsA) (.objectSome topProp (.named clsB))) (.named clsC),
   .classAssertion (.complement (.named clsC)) indA]

#guard decideWithUniversalRole? nonLocalWitnessSat == some true

/-- TBox-only non-local clash: `⊤ ⊑ ∃r.B` forces some object (outside the local node)
to satisfy `B`, contradicting `a ∈ ∀ U.(¬B)`. -/
private def nonLocalTBoxUnsat : Ontology :=
  [.subClassOf (.named thing) (.objectSome (.named propR) (.named clsB)),
   .classAssertion (.objectAll topProp (.complement (.named clsB))) indA]

#guard decideWithUniversalRole? nonLocalTBoxUnsat == some false

/-- Replacing `⊤ ⊑ ∃r.B` by `A ⊑ ∃r.B` allows `A` and `B` to be empty while `a ∈ ∀ U.(¬B)`. -/
private def nonLocalTBoxSat : Ontology :=
  [.subClassOf (.named clsA) (.objectSome (.named propR) (.named clsB)),
   .classAssertion (.objectAll topProp (.complement (.named clsB))) indA]

#guard decideWithUniversalRole? nonLocalTBoxSat == some true

/-! ### 2. Inverse of the universal object property -/

/-- `∃ U⁻.B` and `∀ U⁻.(¬B)` contradict each other globally. -/
private def inverseTopUnsat : Ontology :=
  [.classAssertion (.objectSome invTopProp (.named clsB)) indA,
   .classAssertion (.objectAll invTopProp (.complement (.named clsB))) indB]

#guard decideAdmittedOntology? inverseTopUnsat == none
#guard decideWithUniversalRole? inverseTopUnsat == some false

/-- `a ∈ ∃ U⁻.B` together with `a ∈ ¬B` is satisfiable: another object satisfies `B`. -/
private def inverseTopSat : Ontology :=
  [.classAssertion (.objectSome invTopProp (.named clsB)) indA,
   .classAssertion (.complement (.named clsB)) indA]

#guard decideWithUniversalRole? inverseTopSat == some true

/-! ### 3. Nested universal-role restrictions -/

/-- Nested `∃ U.(A ⊓ ∀ U.(¬A ⊔ B))` forces an `A`-element and globally `A ⊑ B`,
which clashes with `∀ U.(¬B)`. -/
private def nestedTopUnsat : Ontology :=
  [.classAssertion
      (.objectSome topProp (.intersection (.named clsA)
        (.objectAll invTopProp (.union (.complement (.named clsA)) (.named clsB)))))
      indA,
   .classAssertion (.objectAll topProp (.complement (.named clsB))) indB]

#guard decideWithUniversalRole? nestedTopUnsat == some false

/-- Removing the global `¬B` constraint makes the nested universal restriction satisfiable. -/
private def nestedTopSat : Ontology :=
  [.classAssertion
      (.objectSome topProp (.intersection (.named clsA)
        (.objectAll invTopProp (.union (.complement (.named clsA)) (.named clsB)))))
      indA,
   .classAssertion (.complement (.named clsA)) indB]

#guard decideWithUniversalRole? nestedTopSat == some true

/-- Deeply nested `∀ U.(¬(∃ U.A) ⊔ B)` with `a ∈ A` and `b ∈ ¬B` is unsatisfiable. -/
private def nestedImplicationUnsat : Ontology :=
  [.classAssertion
      (.objectAll topProp (.union (.complement (.objectSome topProp (.named clsA))) (.named clsB)))
      indA,
   .classAssertion (.named clsA) indA,
   .classAssertion (.complement (.named clsB)) indB]

#guard decideWithUniversalRole? nestedImplicationUnsat == some false

/-- With `b ∈ B`, the same deeply nested implication is satisfiable. -/
private def nestedImplicationSat : Ontology :=
  [.classAssertion
      (.objectAll topProp (.union (.complement (.objectSome topProp (.named clsA))) (.named clsB)))
      indA,
   .classAssertion (.named clsA) indA,
   .classAssertion (.named clsB) indB]

#guard decideWithUniversalRole? nestedImplicationSat == some true

/-! ### 4. Interaction with `HasKey` and named individuals -/

/-- `HasKey(∃ U.A ⊓ K, (r), (dp))` activates only when `∃ U.A` holds globally.
With `c ∈ A`, `a` and `b` share key `(r → c, dp → 7)` and must merge, clashing with
`DifferentIndividuals(a, b)`. -/
private def hasKeyWithTopUnsat : Ontology :=
  [.hasKey (.intersection (.objectSome topProp (.named clsA)) (.named clsK))
      [.named propR] [dataP],
   .classAssertion (.named clsA) indC,
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .objectAssertion (.named propR) indA indC,
   .objectAssertion (.named propR) indB indC,
   .dataAssertion dataP indA (intLit "7"),
   .dataAssertion dataP indB (intLit "7"),
   .differentIndividuals [indA, indB]]

#guard decideWithUniversalRole? hasKeyWithTopUnsat == some false

/-- Without `c ∈ A`, `A` can be empty, so the key class `∃ U.A ⊓ K` is empty and
`a ≠ b` remains satisfiable; the fresh witness role does not disturb named individuals. -/
private def hasKeyWithTopSat : Ontology :=
  [.hasKey (.intersection (.objectSome topProp (.named clsA)) (.named clsK))
      [.named propR] [dataP],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .objectAssertion (.named propR) indA indC,
   .objectAssertion (.named propR) indB indC,
   .dataAssertion dataP indA (intLit "7"),
   .dataAssertion dataP indB (intLit "7"),
   .differentIndividuals [indA, indB]]

#guard decideWithUniversalRole? hasKeyWithTopSat == some true

/-- Satisfiable `HasKey` where `∃ U.A` IS forced true via a fresh witness role `w`,
confirming that `withUniversalRole` preserves named individuals and `HasKey` models. -/
private def hasKeyWithActiveTopSat : Ontology :=
  [.hasKey (.named clsK) [.named propR] [dataP],
   .classAssertion (.objectSome topProp (.named clsA)) indA,
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .objectAssertion (.named propR) indA indC,
   .objectAssertion (.named propR) indB indC,
   .dataAssertion dataP indA (intLit "7"),
   .dataAssertion dataP indB (intLit "8"),
   .differentIndividuals [indA, indB]]

#guard decideWithUniversalRole? hasKeyWithActiveTopSat == some true

/-! ### 5. Combined pipeline: top-headed chain + chain alias + bottom property + universal restriction -/

private def combinedPipelineUnsat : Ontology :=
  [.subObjectPropertyChain [.named propR, .named propS] topProp,
   .subObjectProperty (.named propR) (.named propT),
   .subObjectProperty (.named propT) (.named propR),
   .subObjectPropertyChain [.named propT, .named propS] (.named propR),
   .subClassOf (.objectSome (.named bottomObjectProperty) (.named thing)) (.named clsA),
   .objectAssertion (.named propT) indA indB,
   .objectAssertion (.named propS) indB indC,
   .subClassOf (.objectSome (.named propR) (.named clsB)) (.named clsC),
   .classAssertion (.named clsB) indC,
   .classAssertion (.objectAll invTopProp (.complement (.named clsC))) indB]

#guard decideAdmittedOntology? combinedPipelineUnsat == none
#guard decideWithUniversalRole? combinedPipelineUnsat == some false

/-! ### 6. Functional-Style Syntax regressions & rejection of non-simple universal uses -/

private def decideOFNWithUniversal (text : String) : Option Bool :=
  match FunctionalSyntax.parseDocument text with
  | .ok doc => decideWithUniversalRole? doc.ontology
  | .error _ => none

private def ofnUniversalUnsat : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(Class(ex:A))
  Declaration(Class(ex:B))
  Declaration(NamedIndividual(ex:a))
  Declaration(NamedIndividual(ex:b))
  ClassAssertion(ObjectSomeValuesFrom(owl:topObjectProperty ex:A) ex:a)
  ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(owl:topObjectProperty) ObjectComplementOf(ex:A)) ex:b)
)"

#guard decideOFNWithUniversal ofnUniversalUnsat == some false

private def ofnUniversalDomainRangeUnsat : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(Class(ex:A))
  Declaration(NamedIndividual(ex:a))
  ObjectPropertyRange(owl:topObjectProperty ex:A)
  ClassAssertion(ObjectComplementOf(ex:A) ex:a)
)"

#guard decideOFNWithUniversal ofnUniversalDomainRangeUnsat == some false

/-- Non-simple uses of `owl:topObjectProperty` (`ObjectMinCardinality`, `ObjectHasSelf`)
remain rejected by the verified adapter. -/
private def nonSimpleTopCardinality : Ontology :=
  [.classAssertion (.objectMin 2 topProp (.named clsA)) indA]

private def nonSimpleTopSelf : Ontology :=
  [.classAssertion (.objectSelf topProp) indA]

#guard decideWithUniversalRole? nonSimpleTopCardinality == none
#guard decideWithUniversalRole? nonSimpleTopSelf == none

end Sabrina.OWL2.SROIQD.Termination.BlockedForest.UniversalRoleExamples
