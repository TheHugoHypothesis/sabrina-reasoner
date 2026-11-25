import Sabrina.OWL2.FastLocality
import Sabrina.OWL2.FunctionalSyntax

/-! Regression tests for `Sabrina.OWL2.FastLocality`:
    verifies exact agreement between `extractBotModuleFast` / `extractBotModuleWithIndex`
    and `Profile.extractBotModule` across diverse OWL 2 DL axiom forms, always-non-local
    axioms, `LocalityIndex.extend`, and stale-index fallback certification. -/

namespace SabrinaTests.FastLocalityTests

open Sabrina.OWL2 Sabrina.OWL2.Profile Sabrina.OWL2.FastLocality

private def sameAxiomSet (xs ys : Ontology) : Bool :=
  xs.all (fun a => ys.contains a) && ys.all (fun a => xs.contains a)

private def sampleOntology : Ontology := [
  -- Component 1: Clinical EL++ chain (A ⊑ B ⊑ C, D ⊑ ∃r.A, r ⊑ s, r ∘ s ⊑ t)
  .subClassOf (.named "ex:A") (.named "ex:B"),
  .subClassOf (.named "ex:B") (.named "ex:C"),
  .subClassOf (.named "ex:D") (.objectSome (.named "ex:r") (.named "ex:A")),
  .subObjectProperty (.named "ex:r") (.named "ex:s"),
  .subObjectPropertyChain [.named "ex:r", .named "ex:s"] (.named "ex:t"),
  .objectPropertyDomain (.named "ex:r") (.named "ex:DomR"),
  .objectPropertyRange (.named "ex:s") (.named "ex:RngS"),
  .disjointClasses [.named "ex:C", .named "ex:DisjC"],
  -- Component 2: Disconnected expressive SROIQ(D) component (P ⊑ Q ⊔ ¬R, card, HasKey, data)
  .subClassOf (.named "ex:P") (.union (.named "ex:Q") (.complement (.named "ex:R"))),
  .subClassOf (.named "ex:Q") (.objectMin 2 (.named "ex:k") (.named "ex:S")),
  .hasKey (.named "ex:P") [.named "ex:k"] ["ex:dp1"],
  .dataPropertyDomain "ex:dp1" (.named "ex:P"),
  .subClassOf (.named "ex:P") (.dataSome "ex:dp1" (.datatype "http://www.w3.org/2001/XMLSchema#integer")),
  -- Component 3: Disconnected RBox/TBox cluster
  .transitiveObjectProperty (.named "ex:tr"),
  .symmetricObjectProperty (.named "ex:sym"),
  .functionalObjectProperty (.named "ex:fn"),
  .subClassOf (.named "ex:U") (.named "ex:V"),
  .subClassOf (.named "ex:V") (.named "ex:W")
]

private def sampleWithAlwaysNonLocal : Ontology :=
  sampleOntology ++ [
    -- Always-non-local under empty signature: ⊤ ⊑ GlobalRoot, nominal equiv, ClassAssertion, Reflexive
    .subClassOf (.named thing) (.named "ex:GlobalRoot"),
    .subClassOf (.named "ex:GlobalRoot") (.named "ex:GlobalSuper"),
    .equivalentClasses [.named "ex:NomC", .oneOf [.named "ex:i1", .named "ex:i2"]],
    .classAssertion (.named "ex:U") (.named "ex:u1"),
    .reflexiveObjectProperty (.named "ex:tr")
  ]

-- 1. Seed {ex:A}: pulls only Component 1's relevant axioms (A ⊑ B ⊑ C)
#guard
  let seed := axiomSig (.subClassOf (.named "ex:A") (.named "ex:C"))
  let fast := (extractBotModuleFast sampleOntology seed).1
  let spec := (extractBotModule sampleOntology seed).1
  sameAxiomSet fast spec && fast.length == 2

-- 2. Seed {ex:D}: pulls D ⊑ ∃r.A, A ⊑ B, B ⊑ C, r ⊑ s, DomR, RngS, r∘s ⊑ t (never touches Component 2 or 3)
#guard
  let seed := axiomSig (.subClassOf (.named "ex:D") (.named "ex:C"))
  let fast := (extractBotModuleFast sampleOntology seed).1
  let spec := (extractBotModule sampleOntology seed).1
  sameAxiomSet fast spec && !fast.any (fun a => match a with | .hasKey .. => true | _ => false)

-- 3. Seed {ex:P}: pulls Component 2 (SROIQ(D)), leaves Component 1 & 3 out
#guard
  let seed := axiomSig (.subClassOf (.named "ex:P") (.named "ex:Q"))
  let fast := (extractBotModuleFast sampleOntology seed).1
  let spec := (extractBotModule sampleOntology seed).1
  sameAxiomSet fast spec && fast.length < sampleOntology.length

-- 4. Empty seed on sampleOntology: all axioms are ⊥-local -> empty module
#guard
  let fast := (extractBotModuleFast sampleOntology Sig.empty).1
  let spec := (extractBotModule sampleOntology Sig.empty).1
  fast.isEmpty && spec.isEmpty

-- 5. Always-non-local axioms (⊤ ⊑ GlobalRoot, ClassAssertion, Reflexive) pulled even for empty seed
#guard
  let fast := (extractBotModuleFast sampleWithAlwaysNonLocal Sig.empty).1
  let spec := (extractBotModule sampleWithAlwaysNonLocal Sig.empty).1
  sameAxiomSet fast spec && !fast.isEmpty

-- 6. Seed {ex:A} on sampleWithAlwaysNonLocal agrees exactly with extractBotModule
#guard
  let seed := axiomSig (.subClassOf (.named "ex:A") (.named "ex:C"))
  let fast := (extractBotModuleFast sampleWithAlwaysNonLocal seed).1
  let spec := (extractBotModule sampleWithAlwaysNonLocal seed).1
  sameAxiomSet fast spec

-- 7. LocalityIndex.extend agrees with fresh LocalityIndex.build
#guard
  let baseIdx := LocalityIndex.build sampleOntology
  let extra : Ontology := [
    .subClassOf (.named "ex:C") (.named "ex:Z"),
    .classAssertion (.named "ex:A") (.named "ex:a0")
  ]
  let combined := sampleOntology ++ extra
  let extIdx := baseIdx.extend extra
  let seed := axiomSig (.subClassOf (.named "ex:A") (.named "ex:Z"))
  let mExt := (extractBotModuleWithIndex extIdx combined seed).1
  let mSpec := (extractBotModule combined seed).1
  sameAxiomSet mExt mSpec

-- 8. Stale/wrong index passed to extractBotModuleWithIndex still produces exact result via fallback
#guard
  let emptyIdx := LocalityIndex.build []
  let seed := axiomSig (.subClassOf (.named "ex:D") (.named "ex:C"))
  let mFallback := (extractBotModuleWithIndex emptyIdx sampleOntology seed).1
  let mSpec := (extractBotModule sampleOntology seed).1
  sameAxiomSet mFallback mSpec

-- 9. profileQueryFast matches Profile.profileQuery on module count & least fragment
#guard
  let q := Axiom.subClassOf (.named "ex:A") (.named "ex:C")
  let qpFast := profileQueryFast sampleOntology (some q)
  let qpSpec := profileQuery sampleOntology (some q)
  qpFast.moduleAxiomCount == qpSpec.moduleAxiomCount &&
  qpFast.moduleFragment == .el &&
  qpFast.fullFragment == .sroiqd

end SabrinaTests.FastLocalityTests
