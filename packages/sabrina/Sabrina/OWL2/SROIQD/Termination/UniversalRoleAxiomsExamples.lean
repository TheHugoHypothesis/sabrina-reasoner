import Sabrina.OWL2.SROIQD.Termination.UniversalRoleAxioms

/-! Live fuel-free regressions for `owl:topObjectProperty` in OWL 2 DL role
axioms: unary role inclusions (`R ⊑ U`, `U ⊑ R`, transitive universal closure,
`EquivalentObjectProperties`, `InverseObjectProperties`), role characteristics,
ABox assertions, `HasKey`, chain bodies (`R ∘ U ∘ S ⊑ T`, multi-`U` chains),
Functional-Style Syntax integration, and OWL 2 DL §11.1–§11.2 simplicity
rejections. -/

namespace Sabrina.OWL2.SROIQD.Termination.BlockedForest.UniversalRoleAxiomsExamples

open Sabrina.OWL2

private def clsA : IRI := "urn:topax:A"
private def clsB : IRI := "urn:topax:B"
private def clsK : IRI := "urn:topax:K"
private def propP : IRI := "urn:topax:p"
private def propR : IRI := "urn:topax:r"
private def propS : IRI := "urn:topax:s"
private def propT : IRI := "urn:topax:t"
private def propM : IRI := "urn:topax:m"
private def dataP : IRI := "urn:topax:dp"
private def indA : Individual := .named "urn:topax:a"
private def indB : Individual := .named "urn:topax:b"
private def indC : Individual := .named "urn:topax:c"
private def topProp : ObjectProperty := .named topObjectProperty
private def invTopProp : ObjectProperty := .inverse topObjectProperty
private def intLit (s : String) : Literal := ⟨s, Datatypes.xsd "integer"⟩

/-! ### 1. Unary role inclusions & universal-role closure -/

/-- `r ⊑ U` is tautological. -/
private def subTopSat : Ontology :=
  [.subObjectProperty (.named propR) topProp,
   .classAssertion (.named clsA) indA]

#guard decideWithTopRoleAxioms? subTopSat == some true

/-- `U ⊑ r` forces `r` to be universal, so `a : ∀r.B` and `b : ¬B` clash. -/
private def superTopUnsat : Ontology :=
  [.subObjectProperty topProp (.named propR),
   .classAssertion (.objectAll (.named propR) (.named clsB)) indA,
   .classAssertion (.complement (.named clsB)) indB]

private def superTopSat : Ontology :=
  [.subObjectProperty topProp (.named propR),
   .classAssertion (.objectAll (.named propR) (.named clsB)) indA,
   .classAssertion (.named clsB) indB]

#guard decideWithUniversalRole? superTopUnsat == none
#guard decideWithTopRoleAxioms? superTopUnsat == some false
#guard decideWithTopRoleAxioms? superTopSat == some true

/-- `U ⊑ r⁻` forces `r` universal, contradicting `¬r(a, b)`. -/
private def superTopInverseUnsat : Ontology :=
  [.subObjectProperty topProp (.inverse propR),
   .negativeObjectAssertion (.named propR) indA indB]

#guard decideWithTopRoleAxioms? superTopInverseUnsat == some false

/-- Transitive universal propagation: `U ⊑ r` and `r ⊑ s` makes `s` universal. -/
private def transitiveUnivUnsat : Ontology :=
  [.subObjectProperty topProp (.named propR),
   .subObjectProperty (.named propR) (.named propS),
   .classAssertion (.objectAll (.named propS) (.named clsB)) indA,
   .classAssertion (.complement (.named clsB)) indB]

#guard decideWithTopRoleAxioms? transitiveUnivUnsat == some false

/-- All-universal chain `U ∘ U ⊑ r` forces `r` universal, clashing with `¬r(a, b)`. -/
private def allUnivChainUnsat : Ontology :=
  [.subObjectPropertyChain [topProp, invTopProp] (.named propR),
   .negativeObjectAssertion (.named propR) indA indB]

#guard decideWithTopRoleAxioms? allUnivChainUnsat == some false

/-- `EquivalentObjectProperties(U, r)` makes `r` universal. -/
private def equivTopUnsat : Ontology :=
  [.equivalentObjectProperties [topProp, .named propR],
   .classAssertion (.objectAll (.named propR) (.named clsA)) indA,
   .classAssertion (.complement (.named clsA)) indB]

#guard decideWithTopRoleAxioms? equivTopUnsat == some false

/-! ### 2. Role characteristics & ABox assertions on `owl:topObjectProperty` -/

private def topCharsAndAssertionSat : Ontology :=
  [.reflexiveObjectProperty topProp,
   .symmetricObjectProperty topProp,
   .transitiveObjectProperty topProp,
   .objectAssertion topProp indA indB]

private def topNegAssertionUnsat : Ontology :=
  [.negativeObjectAssertion invTopProp indA indB]

#guard decideWithTopRoleAxioms? topCharsAndAssertionSat == some true
#guard decideWithTopRoleAxioms? topNegAssertionUnsat == some false

/-! ### 3. `HasKey` axioms with `owl:topObjectProperty` -/

/-- `HasKey(K, (U), ())` forces any two named instances of `K` to merge. -/
private def hasKeyTopUnsat : Ontology :=
  [.hasKey (.named clsK) [topProp] [],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .differentIndividuals [indA, indB]]

private def hasKeyTopSat : Ontology :=
  [.hasKey (.named clsK) [topProp] [],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB]

#guard decideWithUniversalRole? hasKeyTopUnsat == none
#guard decideWithTopRoleAxioms? hasKeyTopUnsat == some false
#guard decideWithTopRoleAxioms? hasKeyTopSat == some true

/-- Mixed `HasKey(K, (U, r), (dp))` drops `U` and checks remaining object + data keys. -/
private def hasKeyMixedTopUnsat : Ontology :=
  [.hasKey (.named clsK) [topProp, .named propR] [dataP],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .objectAssertion (.named propR) indA indC,
   .objectAssertion (.named propR) indB indC,
   .dataAssertion dataP indA (intLit "7"),
   .dataAssertion dataP indB (intLit "7"),
   .differentIndividuals [indA, indB]]

private def hasKeyMixedTopSat : Ontology :=
  [.hasKey (.named clsK) [topProp, .named propR] [dataP],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .objectAssertion (.named propR) indA indC,
   .objectAssertion (.named propR) indB indC,
   .dataAssertion dataP indA (intLit "7"),
   .dataAssertion dataP indB (intLit "8"),
   .differentIndividuals [indA, indB]]

#guard decideWithTopRoleAxioms? hasKeyMixedTopUnsat == some false
#guard decideWithTopRoleAxioms? hasKeyMixedTopSat == some true

/-- `U ⊑ r` combined with `HasKey(K, (r), ())` collapses `r` to `U` and forces merge. -/
private def hasKeySuperTopUnsat : Ontology :=
  [.subObjectProperty topProp (.named propR),
   .hasKey (.named clsK) [.named propR] [],
   .classAssertion (.named clsK) indA,
   .classAssertion (.named clsK) indB,
   .differentIndividuals [indA, indB]]

#guard decideWithTopRoleAxioms? hasKeySuperTopUnsat == some false

/-! ### 4. Chain bodies with `owl:topObjectProperty` ("All Elephants are Bigger than All Mice") -/

/-- `r ∘ U ∘ s ⊑ t` with `r(a, a)`, `s(b, b)`, and `¬t(a, b)` is unsatisfiable
even though `a` and `b` have no ordinary role path connecting them. -/
private def elephantChainUnsat : Ontology :=
  [.subObjectPropertyChain [.named propR, topProp, .named propS] (.named propT),
   .objectAssertion (.named propR) indA indA,
   .objectAssertion (.named propS) indB indB,
   .negativeObjectAssertion (.named propT) indA indB]

/-- Reversing the negative assertion to `¬t(b, a)` is satisfiable. -/
private def elephantChainSat : Ontology :=
  [.subObjectPropertyChain [.named propR, topProp, .named propS] (.named propT),
   .objectAssertion (.named propR) indA indA,
   .objectAssertion (.named propS) indB indB,
   .negativeObjectAssertion (.named propT) indB indA]

#guard decideWithUniversalRole? elephantChainUnsat == none
#guard decideWithTopRoleAxioms? elephantChainUnsat == some false
#guard decideWithTopRoleAxioms? elephantChainSat == some true

/-- Prefix-only chain `r ∘ U ⊑ t`: `r(a, a)` forces `t(a, y)` for every `y`. -/
private def prefixTopChainUnsat : Ontology :=
  [.subObjectPropertyChain [.named propR, topProp] (.named propT),
   .objectAssertion (.named propR) indA indA,
   .classAssertion (.objectAll (.named propT) (.named clsB)) indA,
   .classAssertion (.complement (.named clsB)) indB]

/-- Suffix-only chain `U ∘ s ⊑ t`: `s(b, b)` forces `t(a, b)` for every `a`. -/
private def suffixTopChainUnsat : Ontology :=
  [.subObjectPropertyChain [invTopProp, .named propS] (.named propT),
   .objectAssertion (.named propS) indB indB,
   .classAssertion (.objectAll (.named propT) (.complement (.named clsB))) indA,
   .classAssertion (.named clsB) indB]

#guard decideWithTopRoleAxioms? prefixTopChainUnsat == some false
#guard decideWithTopRoleAxioms? suffixTopChainUnsat == some false

/-- Multi-`U` chain `r ∘ U ∘ m ∘ U ∘ s ⊑ t` requires a global `m`-edge in the middle. -/
private def multiTopChainUnsat : Ontology :=
  [.subObjectPropertyChain [.named propR, topProp, .named propM, topProp, .named propS] (.named propT),
   .objectAssertion (.named propR) indA indA,
   .objectAssertion (.named propM) indA indA,
   .objectAssertion (.named propS) indB indB,
   .negativeObjectAssertion (.named propT) indA indB]

/-- Without any `m`-edge, `m` can be empty so the multi-`U` chain is vacuous. -/
private def multiTopChainSat : Ontology :=
  [.subObjectPropertyChain [.named propR, topProp, .named propM, topProp, .named propS] (.named propT),
   .objectAssertion (.named propR) indA indA,
   .objectAssertion (.named propS) indB indB,
   .negativeObjectAssertion (.named propT) indA indB]

#guard decideWithTopRoleAxioms? multiTopChainUnsat == some false
#guard decideWithTopRoleAxioms? multiTopChainSat == some true

/-- Combined universal closure + chain body: `U ⊑ r` and `p ∘ r ∘ s ⊑ t`. -/
private def univClosureIntoChainUnsat : Ontology :=
  [.subObjectProperty topProp (.named propR),
   .subObjectPropertyChain [.named propP, .named propR, .named propS] (.named propT),
   .objectAssertion (.named propP) indA indA,
   .objectAssertion (.named propS) indB indB,
   .negativeObjectAssertion (.named propT) indA indB]

#guard decideWithTopRoleAxioms? univClosureIntoChainUnsat == some false

/-! ### 5. W3C OWL 2 DL §11.1–§11.2 simplicity rejections (`none`) -/

#guard decideWithTopRoleAxioms? [.irreflexiveObjectProperty topProp] == none
#guard decideWithTopRoleAxioms? [.asymmetricObjectProperty topProp] == none
#guard decideWithTopRoleAxioms? [.disjointObjectProperties [topProp, .named propR]] == none
#guard decideWithTopRoleAxioms? [.functionalObjectProperty topProp] == none
#guard decideWithTopRoleAxioms?
  [.subObjectProperty topProp (.named propR), .functionalObjectProperty (.named propR)] == none
#guard decideWithTopRoleAxioms?
  [.subObjectProperty topProp (.named propR), .irreflexiveObjectProperty (.named propR)] == none
#guard decideWithTopRoleAxioms?
  [.subObjectProperty topProp (.named propR), .disjointObjectProperties [.named propR, .named propS]] == none
#guard decideWithTopRoleAxioms?
  [.subObjectProperty topProp (.named propR),
   .classAssertion (.objectMin 2 (.named propR) (.named clsA)) indA] == none
#guard decideWithTopRoleAxioms?
  [.subObjectPropertyChain [.named propR, topProp] (.named propT),
   .functionalObjectProperty (.named propT)] == none

/-! ### 6. End-to-end Functional-Style Syntax regression -/

private def decideOFNWithTopAxioms (text : String) : Option Bool :=
  match FunctionalSyntax.parseDocument text with
  | .ok doc => decideWithTopRoleAxioms? doc.ontology
  | .error _ => none

private def ofnTopRoleChainUnsat : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(Class(ex:Elephant))
  Declaration(Class(ex:Mouse))
  Declaration(ObjectProperty(ex:hasEl))
  Declaration(ObjectProperty(ex:hasMo))
  Declaration(ObjectProperty(ex:biggerThan))
  Declaration(NamedIndividual(ex:dumbo))
  Declaration(NamedIndividual(ex:jerry))
  SubObjectPropertyOf(ObjectPropertyChain(ex:hasEl owl:topObjectProperty ex:hasMo) ex:biggerThan)
  ObjectPropertyAssertion(ex:hasEl ex:dumbo ex:dumbo)
  ObjectPropertyAssertion(ex:hasMo ex:jerry ex:jerry)
  NegativeObjectPropertyAssertion(ex:biggerThan ex:dumbo ex:jerry)
)"

#guard decideOFNWithTopAxioms ofnTopRoleChainUnsat == some false

end Sabrina.OWL2.SROIQD.Termination.BlockedForest.UniversalRoleAxiomsExamples
