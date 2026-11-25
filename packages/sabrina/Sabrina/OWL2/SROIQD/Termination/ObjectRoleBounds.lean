import Sabrina.OWL2.SROIQD.Termination.UniversalRoleAxioms
import Sabrina.OWL2.Profile
import Sabrina.OWL2.WellFormed

/-! Certified object reasoning when the input role box has no validated rank.
Locality preserves satisfiability exactly. For the remaining chains, a ranked
relaxation can certify inconsistency and a ranked strengthening can certify a
model. Inconclusive combinations have no verdict. -/
namespace Sabrina.OWL2.ObjectRoleBounds

open Datatypes (datatypeMap)
open SROIQD.Termination.BlockedForest (decideWithTopRoleAxioms? decideWithTopRoleAxioms_iff)

private def relax : Axiom → List Axiom
  | .subObjectPropertyChain .. => []
  | ax => [ax]

private def strengthen : Axiom → List Axiom
  | .subObjectPropertyChain [] h => [.reflexiveObjectProperty h]
  | .subObjectPropertyChain (r :: rs) h =>
    .transitiveObjectProperty h :: ((r :: rs).map fun s => .subObjectProperty s h)
  | ax => [ax]

private theorem path_sub_trans {d} (i : Interpretation d) (h r : ObjectProperty)
    (trans : axiomHolds i (.transitiveObjectProperty h)) (rs : List ObjectProperty)
    (sub : ∀ s ∈ r :: rs, axiomHolds i (.subObjectProperty s h)) (x y : i.Object)
    (hp : rolePath i (r :: rs) x y) : objectHolds i h x y := by
  induction rs generalizing r x with
  | nil =>
    obtain ⟨z, he, rfl⟩ := hp
    exact sub r (by simp) x z he
  | cons s ss ih =>
    obtain ⟨z, he, rest⟩ := hp
    exact trans x z y (sub r (by simp) x z he)
      (ih s (fun t ht => sub t (List.mem_cons_of_mem _ ht)) z rest)

private theorem strengthen_implies {d} (i : Interpretation d) (ax : Axiom)
    (hs : satisfies i (strengthen ax)) : axiomHolds i ax := by
  cases ax <;> try exact hs _ (List.mem_singleton_self _)
  case subObjectPropertyChain rs h =>
    cases rs with
    | nil =>
      intro x y he; cases he
      exact hs (.reflexiveObjectProperty h) (List.mem_singleton_self _) x
    | cons r rs =>
      exact path_sub_trans i h r (hs _ (List.mem_cons_self ..)) rs
        (fun s hm => hs _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hm)))

theorem roleBounds_sat {d : DatatypeMap} (o : Ontology) :
    (Satisfiable d (o.flatMap strengthen) → Satisfiable d o) ∧
    (Satisfiable d o → Satisfiable d (o.flatMap relax)) := by
  constructor
  · rintro ⟨i, assign, hi⟩
    exact ⟨i, assign, fun ax hm => strengthen_implies _ ax
      (fun a ha => hi a (List.mem_flatMap.mpr ⟨ax, hm, ha⟩))⟩
  · rintro ⟨i, assign, hi⟩
    refine ⟨i, assign, fun a ha => ?_⟩
    obtain ⟨ax, hm, ha⟩ := List.mem_flatMap.mp ha
    cases ax <;> simp only [relax, List.not_mem_nil, List.mem_singleton] at ha <;> subst_vars <;> exact hi _ hm

private def decideBounds? (o : Ontology) : Option Bool :=
  if decideWithTopRoleAxioms? (o.flatMap relax) = some false then some false
  else if decideWithTopRoleAxioms? (o.flatMap strengthen) = some true then some true
  else none

private theorem decideBounds_iff {o b} (hv : decideBounds? o = some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  unfold decideBounds? at hv
  split at hv
  · rename_i h
    cases hv
    exact ⟨Bool.noConfusion, fun hs => (decideWithTopRoleAxioms_iff h).mpr ((roleBounds_sat o).2 hs)⟩
  · split at hv
    · rename_i h
      cases hv
      exact ⟨fun _ => (roleBounds_sat o).1 ((decideWithTopRoleAxioms_iff h).mp rfl), fun _ => rfl⟩
    · contradiction

/-- Keep the original simplicity/structure checks before extracting a module.
Try the exact ranked model construction on a strictly smaller module first. -/
def decideObjectHierarchy? (o : Ontology) : Option Bool := do
  let (defs, p) ← Normalize.normalizeWithDefs o
  if (Profile.profileOntology o).hasData || !(o.all (WellFormed.checkAxiom defs) && p.checkSimpleWithTop) then none
  else
    let m := (Profile.extractBotModule o {}).1
    (if m.length < o.length then decideWithTopRoleAxioms? m else none) <|> decideBounds? m

theorem decideObjectHierarchy_iff {o b} (hv : decideObjectHierarchy? o = some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideObjectHierarchy?, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨⟨defs,p⟩, _, hv⟩ := hv
  split at hv
  · contradiction
  · let m := (Profile.extractBotModule o {}).1
    suffices b = true ↔ Satisfiable datatypeMap m from this.trans (Profile.extractBotModule_sat_iff o {}).symm
    by_cases hlen : m.length < o.length
    · cases hr : decideWithTopRoleAxioms? m with
      | none =>
        apply decideBounds_iff
        simpa [m, hlen, hr] using hv
      | some v =>
        have h : v = b := by simpa [m, hlen, hr] using hv
        exact h ▸ decideWithTopRoleAxioms_iff hr
    · apply decideBounds_iff
      simpa [m, hlen] using hv

#print axioms roleBounds_sat
#print axioms decideObjectHierarchy_iff

end Sabrina.OWL2.ObjectRoleBounds
