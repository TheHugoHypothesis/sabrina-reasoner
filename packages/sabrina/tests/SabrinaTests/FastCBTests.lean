import Sabrina.OWL2.FastCB

/-! Unit tests for `Sabrina.OWL2.FastCB` (H.1 Horn-$\mathcal{SHIQ}$ extraction +
    H.2 Horn-$\mathcal{SHI}$ saturation & kernel-verified derivation checker). -/

namespace SabrinaTests.FastCBTests

open Sabrina.OWL2
open Sabrina.OWL2.FastCB

private def hasSub (res : FastCBResult) (a b : IRI) : Bool :=
  res.verified && res.subs.contains (a, b)

private def hasUnsat (res : FastCBResult) (a : IRI) : Bool :=
  res.verified && res.unsats.contains a

-- 1. Conjunction + existential + universal (`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `B ⊓ C ⊑ D`, `∃r.D ⊑ E`)
private def ontExAll : Ontology := [
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectAll (.named "r") (.named "C")),
  .subClassOf (.intersection (.named "B") (.named "C")) (.named "D"),
  .subClassOf (.objectSome (.named "r") (.named "D")) (.named "E")
]

#guard hasSub (runFastCB ontExAll 1) "A" "E"
#guard (runFastCB ontExAll 1).isPureHornSHIQ

-- 2. Inverse universal (`A ⊑ ∃r.B`, `B ⊑ ∀r⁻.C` ⇒ `A ⊑ C`)
private def ontInvAll : Ontology := [
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "B") (.objectAll (.inverse "r") (.named "C"))
]

#guard hasSub (runFastCB ontInvAll 1) "A" "C"
#guard (runFastCB ontInvAll 1).isPureHornSHIQ

-- 3. Bottom propagation (`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `Disjoint(B, C)` ⇒ `A ⊑ ⊥`)
private def ontBotProp : Ontology := [
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectAll (.named "r") (.named "C")),
  .disjointClasses [.named "B", .named "C"]
]

#guard hasUnsat (runFastCB ontBotProp 1) "A"

-- 4. Role chain composition (`r1 ∘ r2 ⊑ s`)
private def ontChain : Ontology := [
  .subObjectPropertyChain [.named "r1", .named "r2"] (.named "s"),
  .subClassOf (.named "A") (.objectSome (.named "r1") (.named "B")),
  .subClassOf (.named "B") (.objectSome (.named "r2") (.named "C")),
  .subClassOf (.objectSome (.named "s") (.named "C")) (.named "D")
]

#guard hasSub (runFastCB ontChain 1) "A" "D"

-- 5. Transitive role + universal propagation (`Transitive(p)`, `A ⊑ ∀p.X`, `A ⊑ ∃p.B`, `B ⊑ ∃p.C`)
private def ontTransAll : Ontology := [
  .transitiveObjectProperty (.named "p"),
  .subClassOf (.named "A") (.objectAll (.named "p") (.named "X")),
  .subClassOf (.named "A") (.objectSome (.named "p") (.named "B")),
  .subClassOf (.named "B") (.objectSome (.named "p") (.named "C")),
  .subClassOf (.intersection (.named "C") (.named "X")) (.named "D"),
  .subClassOf (.objectSome (.named "p") (.named "D")) (.named "E")
]

#guard hasSub (runFastCB ontTransAll 1) "A" "E"

-- 6. Domain & range + inverse universal
private def ontDomRange : Ontology := [
  .objectPropertyDomain (.named "r") (.named "Dom"),
  .objectPropertyRange (.named "r") (.named "Rng"),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named thing)),
  .subClassOf (.named "Rng") (.objectAll (.inverse "r") (.named "Back"))
]

#guard hasSub (runFastCB ontDomRange 1) "A" "Dom"
#guard hasSub (runFastCB ontDomRange 1) "A" "Back"

-- 7. Reflexive role + universal (`Reflexive(r)`, `A ⊑ ∀r.B` ⇒ `A ⊑ B`)
private def ontReflAll : Ontology := [
  .reflexiveObjectProperty (.named "r"),
  .subClassOf (.named "A") (.objectAll (.named "r") (.named "B"))
]

#guard hasSub (runFastCB ontReflAll 1) "A" "B"

-- 8. Disjunctive complement Horn form (`A ⊑ ¬B ⊔ C`, `A ⊑ B` ⇒ `A ⊑ C`)
private def ontDisjComp : Ontology := [
  .subClassOf (.named "A") (.union (.complement (.named "B")) (.named "C")),
  .subClassOf (.named "A") (.named "B")
]

#guard hasSub (runFastCB ontDisjComp 1) "A" "C"

-- 9. `objectMax 0` (`A ⊑ ≤0 r.B`, `A ⊑ ∃r.B` ⇒ `A ⊑ ⊥`)
private def ontMaxZero : Ontology := [
  .subClassOf (.named "A") (.objectMax 0 (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B"))
]

#guard hasUnsat (runFastCB ontMaxZero 1) "A"

-- 10. Non-Horn ontology still yields verified Horn lower-bound (`isPureHornSHIQ = false`)
private def ontMixed : Ontology := [
  .subClassOf (.named "X") (.union (.named "Y") (.named "Z")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "B") (.objectAll (.inverse "r") (.named "C"))
]

#guard !(runFastCB ontMixed 1).isPureHornSHIQ
#guard hasSub (runFastCB ontMixed 1) "A" "C"

-- 11. 3-step property chain binarization (`r1 ∘ r2 ∘ r3 ⊑ s`)
private def ontChain3 : Ontology := [
  .subObjectPropertyChain [.named "r1", .named "r2", .named "r3"] (.named "s"),
  .subClassOf (.named "A") (.objectSome (.named "r1") (.named "B")),
  .subClassOf (.named "B") (.objectSome (.named "r2") (.named "C")),
  .subClassOf (.named "C") (.objectSome (.named "r3") (.named "D")),
  .subClassOf (.objectSome (.named "s") (.named "D")) (.named "E")
]

#guard hasSub (runFastCB ontChain3 1) "A" "E"

end SabrinaTests.FastCBTests
