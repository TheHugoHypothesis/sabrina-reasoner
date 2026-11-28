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

-- 12. H.4a FunctionalObjectProperty sibling merge (`Functional(r)`, `A ⊑ ∃r.B`, `A ⊑ ∃r.C`, `B ⊓ C ⊑ D`, `∃r.D ⊑ E`)
private def ontFuncSibling : Ontology := [
  .functionalObjectProperty (.named "r"),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "C")),
  .subClassOf (.intersection (.named "B") (.named "C")) (.named "D"),
  .subClassOf (.objectSome (.named "r") (.named "D")) (.named "E")
]

#guard hasSub (runFastCB ontFuncSibling 1) "A" "E"
#guard (runFastCB ontFuncSibling 1).isPureHornSHIQ

-- 13. H.4a Qualified `objectMax 1` sibling merge (`A ⊑ ≤1 r.B`, `A ⊑ ∃r.(B ⊓ C)`, `A ⊑ ∃r.(B ⊓ D)`, `C ⊓ D ⊑ E`)
private def ontMaxOneQCR : Ontology := [
  .subClassOf (.named "A") (.objectMax 1 (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.intersection (.named "B") (.named "C"))),
  .subClassOf (.named "A") (.objectSome (.named "r") (.intersection (.named "B") (.named "D"))),
  .subClassOf (.intersection (.named "C") (.named "D")) (.named "E"),
  .subClassOf (.objectSome (.named "r") (.named "E")) (.named "F")
]

#guard hasSub (runFastCB ontMaxOneQCR 1) "A" "F"
#guard (runFastCB ontMaxOneQCR 1).isPureHornSHIQ

-- 14. H.4a InverseFunctionalObjectProperty parent-child merge (`InverseFunctional(r)`, `A ⊑ ∃r.B`, `B ⊑ ∃r⁻.C` ⇒ `A ⊑ C`)
private def ontInvFuncParent : Ontology := [
  .inverseFunctionalObjectProperty (.named "r"),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "B") (.objectSome (.inverse "r") (.named "C"))
]

#guard hasSub (runFastCB ontInvFuncParent 1) "A" "C"
#guard (runFastCB ontInvFuncParent 1).isPureHornSHIQ

-- 15. H.4a `objectExact 1` sibling merge + bottom propagation (`A ⊑ =1 r.B`, `A ⊑ ∃r.C`, `C ⊑ B`, `Disjoint(B, C)` ⇒ `A ⊑ ⊥`)
private def ontExactOne : Ontology := [
  .subClassOf (.named "A") (.objectExact 1 (.named "r") (.named "B")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "C")),
  .subClassOf (.named "C") (.named "B"),
  .subClassOf (.intersection (.named "B") (.named "C")) (.named "D"),
  .subClassOf (.objectSome (.named "r") (.named "D")) (.named "E")
]

#guard hasSub (runFastCB ontExactOne 1) "A" "E"

-- 16. H.4b Zero-tableau complete classification (`classifyFastCB` returns `some h`) on pure Horn-SHI & Horn-SHIQ
private def checkCBComplete (o : Ontology) (cls : List IRI) (sub : IRI × IRI) (notSub : IRI × IRI) : Bool :=
  match classifyFastCB o cls 1 with
  | none => false
  | some h =>
    h.consistent &&
    h.subsumptions.contains sub &&
    !h.subsumptions.contains notSub

#guard checkCBComplete ontExAll ["A", "B", "C", "D", "E"] ("A", "E") ("E", "A")
#guard checkCBComplete ontInvAll ["A", "B", "C"] ("A", "C") ("C", "A")
#guard checkCBComplete ontTransAll ["A", "B", "C", "D", "E", "X"] ("A", "E") ("E", "A")
#guard checkCBComplete ontDomRange ["A", "Dom", "Rng", "Back"] ("A", "Back") ("Back", "A")
#guard checkCBComplete ontReflAll ["A", "B"] ("A", "B") ("B", "A")
#guard checkCBComplete ontFuncSibling ["A", "B", "C", "D", "E"] ("A", "E") ("E", "A")
#guard checkCBComplete ontMaxOneQCR ["A", "B", "C", "D", "E", "F"] ("A", "F") ("F", "A")
#guard checkCBComplete ontInvFuncParent ["A", "B", "C"] ("A", "C") ("C", "A")
#guard checkCBComplete ontExactOne ["A", "B", "C", "D", "E"] ("A", "E") ("E", "A")

-- 17. H.4b Unsatisfiable class handled completely by `classifyFastCB`
#guard match classifyFastCB ontBotProp ["A", "B", "C"] 1 with
  | some h => h.consistent && h.unsatisfiable.contains "A" && !h.unsatisfiable.contains "B"
  | none => false

-- 18. H.4b Non-Horn ontology returns `none` cleanly (falls back to KP)
#guard (classifyFastCB ontMixed ["X", "Y", "Z", "A", "B", "C"] 1).isNone

-- 19. Nearly-Horn countermodel harvesting (`runFastCBWithPartialModel`):
--     (a) On `ontMixed` (`X ⊑ Y ⊔ Z` + Horn-SHI), Horn-strengthened dual models
--         verify against the original `ontMixed` and cover BOTH `A/B/C` and `X`!
private def checkPartialMixed : Bool :=
  let cls := ["X", "Y", "Z", "A", "B", "C"]
  let clsSet : Std.HashSet IRI := cls.foldl (fun s c => s.insert c) {}
  let idx := Sabrina.OWL2.FastLocality.LocalityIndex.build ontMixed
  let (res, summary) := runFastCBWithPartialModel ontMixed idx cls clsSet 1
  let summaryHas (a : IRI) (sup : IRI) : Bool :=
    match summary.lookup a with
    | some cands => cands.contains sup
    | none => false
  let xEntries := summary.filterMap fun (k, v) => if k == "X" then some v else none
  let xInter := match xEntries with
    | e0 :: rest => e0.filter fun b => rest.all (·.contains b)
    | [] => []
  res.verified &&
  (summary.lookup "A").isSome &&
  summaryHas "A" "C" &&
  !summaryHas "A" "B" &&
  (summary.lookup "B").isSome &&
  (summary.lookup "C").isSome &&
  !xEntries.isEmpty &&
  !xInter.contains "Y" &&
  !xInter.contains "Z"

#guard checkPartialMixed

--     (b) On a mixed Horn + `ObjectHasValue` ontology (cannot be Horn-strengthened),
--         `checkCBPartialModel` shrinks to the maximal ⊥-local clean signature `fs`
--         harvesting `A/B/C` while excluding the nominal class `N`.
private def ontMixedNom : Ontology := [
  .subClassOf (.named "N") (.objectValue (.named "p") (.named "ind1")),
  .subClassOf (.named "A") (.objectSome (.named "r") (.named "B")),
  .subClassOf (.named "B") (.objectAll (.inverse "r") (.named "C"))
]

private def checkPartialNom : Bool :=
  let cls := ["N", "A", "B", "C"]
  let clsSet : Std.HashSet IRI := cls.foldl (fun s c => s.insert c) {}
  let idx := Sabrina.OWL2.FastLocality.LocalityIndex.build ontMixedNom
  let (res, summary) := runFastCBWithPartialModel ontMixedNom idx cls clsSet 1
  res.verified &&
  (summary.lookup "A").isSome &&
  (summary.lookup "B").isSome &&
  (summary.lookup "C").isSome &&
  (summary.lookup "N").isNone

#guard checkPartialNom

end SabrinaTests.FastCBTests
