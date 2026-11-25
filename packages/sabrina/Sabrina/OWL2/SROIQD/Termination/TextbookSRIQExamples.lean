import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQDecision

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

open Sabrina.OWL2.Datatypes (datatypeMap)

private def collision : Concept :=
  .conj (.min 2 (.named "r") (.atom "A")) (.max 1 (.named "r") (.atom "A"))

def cardinalityCollision : TBoxRBox where
  tbox := [(.top, collision)]

theorem cardinalityCollision_unsat : ¬ cardinalityCollision.Sat := by
  rintro ⟨m, hm⟩
  obtain ⟨x⟩ := m.nonempty
  have h := hm.1 (.top, collision) (by simp [cardinalityCollision]) x trivial
  exact h.2 h.1

private def chainWitness : Concept :=
  .some (.named "w") (.some (.inverse "r") (.some (.named "s") .top))

private def emptyHead : Concept := .all (.named "t") .bottom

def inverseChain (first : Role) : TBoxRBox where
  tbox := [(.top, chainWitness), (.top, emptyHead)]
  hierarchy := [⟨first, [.named "s"], "t"⟩]

theorem inverseChain_unsat : ¬ (inverseChain (.inverse "r")).Sat := by
  rintro ⟨m, hm⟩
  obtain ⟨x⟩ := m.nonempty
  obtain ⟨a, _, b, hab, c, hbc, _⟩ := hm.1 (.top, chainWitness) (by simp [inverseChain]) x trivial
  have hpath : m.path [.inverse "r", .named "s"] a c := .cons hab (.cons hbc (.nil c))
  have ht := hm.2.1 ⟨.inverse "r", [.named "s"], "t"⟩ (by simp [inverseChain]) a c hpath
  exact hm.1 (.top, emptyHead) (by simp [inverseChain]) a trivial c ht

private def totalSuccessor : Concept := .some (.named "next") .top
private def uniquePredecessor : Concept := .max 1 (.inverse "next") .top
private def rootWitness : Concept := .some (.named "w") (.max 0 (.inverse "next") .top)

/-- Total successors, at most one predecessor, and a predecessor-free
object reached by a separate role. This version uses no individual names. -/
def infiniteSuccessors : TBoxRBox where
  tbox := [(.top, totalSuccessor), (.top, uniquePredecessor), (.top, rootWitness)]

private def naturalSuccessorModel : Model :=
  ⟨Nat, ⟨0⟩, fun _ _ => False,
    fun name x y => (name = "next" ∧ y = x + 1) ∨ (name = "w" ∧ y = 0)⟩

theorem infiniteSuccessors_sat : infiniteSuccessors.Sat := by
  refine ⟨naturalSuccessorModel, ?_, by simp [infiniteSuccessors], by simp [infiniteSuccessors]⟩
  intro gci hg x _
  change Nat at x
  simp only [infiniteSuccessors, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨x + 1, .inl ⟨rfl, rfl⟩, trivial⟩
  · apply mt cardinalityAtLeast_iff.mpr
    apply (atMostOne_iff _).mpr
    intro a b ha hb
    change Nat at a b
    have ha' : x = a + 1 := by
      simpa [Model.edge, naturalSuccessorModel] using ha.1
    have hb' : x = b + 1 := by
      simpa [Model.edge, naturalSuccessorModel] using hb.1
    exact Nat.add_right_cancel (ha'.symm.trans hb')
  · refine ⟨(0 : Nat), .inr ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨f, _, hf⟩
    change Fin 1 → Nat at f
    have hf' : 0 = f 0 + 1 := by
      simpa [Model.edge, naturalSuccessorModel] using (hf (0 : Fin 1)).1
    omega

private def orbit {α : Type} (f : α → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => f (orbit f x n)

private theorem orbit_injective {α : Type} {f : α → α} {x : α}
    (hinj : ∀ a b, f a = f b → a = b) (hroot : ∀ y, f y ≠ x) :
    ∀ a b, orbit f x a = orbit f x b → a = b := by
  intro a
  induction a with
  | zero =>
    rintro (_ | b) he
    · rfl
    · exact (hroot _ he.symm).elim
  | succ a ih =>
    rintro (_ | b) he
    · exact (hroot _ he).elim
    · exact congrArg Nat.succ (ih b (hinj _ _ he))

theorem infiniteSuccessors_no_finite_model (m : Model) (hm : m.Models infiniteSuccessors) :
    ¬ ∃ xs : List m.Object, ∀ x, x ∈ xs := by
  obtain ⟨x⟩ := m.nonempty
  have htotal (y : m.Object) : ∃ z, m.edge (.named "next") y z := by
    obtain ⟨z, hz, _⟩ := hm.1 (.top, totalSuccessor) (by simp [infiniteSuccessors]) y trivial
    exact ⟨z, hz⟩
  obtain ⟨root, _, hroot⟩ := hm.1 (.top, rootWitness) (by simp [infiniteSuccessors]) x trivial
  let f := fun y => Classical.choose (htotal y)
  have hf (y : m.Object) : m.edge (.named "next") y (f y) := Classical.choose_spec (htotal y)
  have hnoRoot (y : m.Object) : f y ≠ root := by
    intro he
    exact hroot ⟨fun _ => y, fun a b _ => Fin.ext (by omega), fun _ => ⟨he ▸ hf y, trivial⟩⟩
  have hfInj (a b : m.Object) (he : f a = f b) : a = b := by
    have hmax := hm.1 (.top, uniquePredecessor) (by simp [infiniteSuccessors]) (f b) trivial
    apply (atMostOne_iff _).mp (mt cardinalityAtLeast_iff.mp hmax) a b
    · exact ⟨he ▸ hf a, trivial⟩
    · exact ⟨hf b, trivial⟩
  rintro ⟨xs, hxs⟩
  have hg : HasCardinalityAtLeast (xs.length + 1) (fun _ : m.Object => True) := by
    refine ⟨fun i => orbit f root i.val, ?_, fun _ => trivial⟩
    intro a b h
    exact Fin.ext (orbit_injective hfInj hnoRoot _ _ h)
  obtain ⟨ys, hlen, hnodup, _⟩ := cardinalityAtLeast_iff.mpr hg
  have hle := hnodup.length_le_of_subset (fun {y} _ => hxs y)
  omega

def localReflexivity : TBoxRBox where
  tbox := [(.top, .all (.named "r") .bottom)]
  assertions := [.localReflexive (.named "r")]

theorem localReflexivity_sat : localReflexivity.Sat := by
  let m : Model := ⟨Unit, ⟨()⟩, fun _ _ => False, fun _ _ _ => False⟩
  refine ⟨m, ?_, by simp [localReflexivity], ?_⟩
  · intro c hc
    have hc' : c = (.top, .all (.named "r") .bottom) := by simpa [localReflexivity] using hc
    subst c
    exact fun _ _ _ h => h
  · intro a ha
    have ha' : a = .localReflexive (.named "r") := by simpa [localReflexivity] using ha
    subst a
    exact fun _ ⟨_, h⟩ => h

def owlGlobalReflexivity : Ontology :=
  [.subClassOf (.named thing) (.objectAll (.named (encodeName "r")) (.named nothing)),
    .reflexiveObjectProperty (.named (encodeName "r"))]

theorem owlGlobalReflexivity_unsat : ¬ Satisfiable datatypeMap owlGlobalReflexivity := by
  rintro ⟨i, assign, hi⟩
  let j := i.withAnonymous assign
  obtain ⟨x⟩ := j.objectNonempty
  have empty := hi _ (List.mem_cons_self ..)
  have loop := hi _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact j.nothingExt x (empty x (j.thingExt x) x (loop x))

private def nonSimpleSelf : TBoxRBox where
  tbox := [(.top, .self (.named "r"))]
  assertions := [.transitive (.named "r")]

-- The runtime checks exercise the typed translation, normalization, rank
-- inference and fuel-free search. The semantic theorems above are independent.
#guard cardinalityCollision.decide? == some false
#guard (inverseChain (.inverse "r")).decide? == some false
#guard (inverseChain (.named "r")).decide? == some true
#guard infiniteSuccessors.decide? == some true
#guard localReflexivity.decide? == some true
#guard nonSimpleSelf.decide? == none

#print axioms cardinalityCollision_unsat
#print axioms inverseChain_unsat
#print axioms infiniteSuccessors_sat
#print axioms infiniteSuccessors_no_finite_model
#print axioms localReflexivity_sat
#print axioms owlGlobalReflexivity_unsat

end Sabrina.OWL2.SROIQD.TextbookSRIQ
