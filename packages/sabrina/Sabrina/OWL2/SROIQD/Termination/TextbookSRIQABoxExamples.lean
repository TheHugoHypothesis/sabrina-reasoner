import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQABox

/-! Semantic proofs and live fuel-free regressions for textbook SRIQ ABox
coverage: absence of a unique-name assumption (UNA), negated role assertions
over both simple and composite/inverse roles, RBox + ABox interaction (including
local reflexivity vs OWL global reflexivity), infinite-model ABoxes, and
rejection of non-simple / non-regular inputs. -/

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

/-! ### 1. Absence of a unique-name assumption (UNA) -/

/-- `a : ≤ 1 r.⊤`, `r(a, b)`, `r(a, c)` is satisfiable without UNA because `b`
and `c` may denote the same object. -/
def noUnaMergeSat : KnowledgeBase where
  abox :=
    [.concept (.max 1 (.named "r") .top) "a",
     .role (.named "r") "a" "b",
     .role (.named "r") "a" "c"]

theorem noUnaMergeSat_sat : noUnaMergeSat.Sat := by
  let m : ABoxModel :=
    { toModel := ⟨Unit, ⟨()⟩, fun _ _ => False, fun name _ _ => name = "r"⟩
      individuals := fun _ => () }
  refine ⟨m, ⟨by simp [noUnaMergeSat], by simp [noUnaMergeSat], by simp [noUnaMergeSat]⟩, ?_⟩
  intro ax hax
  simp only [noUnaMergeSat, List.mem_cons, List.not_mem_nil, or_false] at hax
  rcases hax with rfl | rfl | rfl
  · rintro ⟨f, hinj, _⟩
    have h01 : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := hinj _ _ (Subsingleton.elim _ _)
    cases h01
  · exact rfl
  · exact rfl

/-- Adding `b ≠ c` makes the same KB unsatisfiable. -/
def noUnaDiffUnsat : KnowledgeBase where
  abox :=
    [.concept (.max 1 (.named "r") .top) "a",
     .role (.named "r") "a" "b",
     .role (.named "r") "a" "c",
     .different "b" "c"]

theorem noUnaDiffUnsat_unsat : ¬ noUnaDiffUnsat.Sat := by
  rintro ⟨m, _, habox⟩
  have hmax := habox (.concept (.max 1 (.named "r") .top) "a") (by simp [noUnaDiffUnsat])
  have hr1 := habox (.role (.named "r") "a" "b") (by simp [noUnaDiffUnsat])
  have hr2 := habox (.role (.named "r") "a" "c") (by simp [noUnaDiffUnsat])
  have hne := habox (.different "b" "c") (by simp [noUnaDiffUnsat])
  apply hmax
  refine ⟨fun i => if i.val = 0 then m.individuals "b" else m.individuals "c", ?_, ?_⟩
  · intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl
  · intro i
    rcases i with ⟨i, hi⟩
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact ⟨hr1, trivial⟩
    · exact ⟨hr2, trivial⟩

/-- Explicit equality `a = b` forces merging `a : A` and `b : ¬A` into a clash. -/
def sameIndsClash : KnowledgeBase where
  abox :=
    [.concept (.atom "A") "a",
     .concept (.neg (.atom "A")) "b",
     .same "a" "b"]

def noSameIndsSat : KnowledgeBase where
  abox :=
    [.concept (.atom "A") "a",
     .concept (.neg (.atom "A")) "b"]

#guard noUnaMergeSat.decide? == some true
#guard noUnaDiffUnsat.decide? == some false
#guard sameIndsClash.decide? == some false
#guard noSameIndsSat.decide? == some true

/-! ### 2. Negated role assertions (simple, inverse, and composite chain-head roles) -/

def negSimpleInverseUnsat : KnowledgeBase where
  abox :=
    [.role (.named "r") "a" "b",
     .negRole (.inverse "r") "b" "a"]

/-- Composite chain head `t` (`r ∘ s ⊑ t`) in a negated role assertion `¬t(a, c)`
is admitted and proven unsatisfiable when `r(a, b)` and `s(b, c)` hold. -/
def negCompositeChainUnsat : KnowledgeBase where
  tboxRBox := { hierarchy := [⟨.named "r", [.named "s"], "t"⟩] }
  abox :=
    [.role (.named "r") "a" "b",
     .role (.named "s") "b" "c",
     .negRole (.named "t") "a" "c"]

theorem negCompositeChainUnsat_unsat : ¬ negCompositeChainUnsat.Sat := by
  rintro ⟨m, htr, habox⟩
  have hr := habox (.role (.named "r") "a" "b") (by simp [negCompositeChainUnsat])
  have hs := habox (.role (.named "s") "b" "c") (by simp [negCompositeChainUnsat])
  have hnt := habox (.negRole (.named "t") "a" "c") (by simp [negCompositeChainUnsat])
  have hpath : m.toModel.path [.named "r", .named "s"] (m.individuals "a") (m.individuals "c") :=
    .cons hr (.cons hs (.nil _))
  exact hnt (htr.2.1 ⟨.named "r", [.named "s"], "t"⟩ (by simp [negCompositeChainUnsat]) _ _ hpath)

def negCompositeInverseUnsat : KnowledgeBase where
  tboxRBox := { hierarchy := [⟨.named "r", [.named "s"], "t"⟩] }
  abox :=
    [.role (.named "r") "a" "b",
     .role (.named "s") "b" "c",
     .negRole (.inverse "t") "c" "a"]

def negCompositeChainSat : KnowledgeBase where
  tboxRBox := { hierarchy := [⟨.named "r", [.named "s"], "t"⟩] }
  abox :=
    [.role (.named "r") "a" "b",
     .role (.named "s") "b" "c",
     .negRole (.named "t") "c" "a"]

#guard negSimpleInverseUnsat.decide? == some false
#guard negCompositeChainUnsat.decide? == some false
#guard negCompositeInverseUnsat.decide? == some false
#guard negCompositeChainSat.decide? == some true

/-! ### 3. ABox + RBox interaction (local reflexivity, disjointness) -/

def aboxLocalReflUnsat : KnowledgeBase where
  tboxRBox := { assertions := [.localReflexive (.named "r")] }
  abox :=
    [.role (.named "r") "a" "b",
     .concept (.neg (.self (.named "r"))) "a"]

def aboxLocalReflSat : KnowledgeBase where
  tboxRBox := { assertions := [.localReflexive (.named "r")] }
  abox :=
    [.concept (.all (.named "r") .bottom) "a",
     .concept (.neg (.self (.named "r"))) "a"]

def aboxDisjointInverseUnsat : KnowledgeBase where
  tboxRBox := { assertions := [.disjoint (.named "r") (.named "s")] }
  abox :=
    [.role (.named "r") "a" "b",
     .role (.inverse "s") "b" "a"]

#guard aboxLocalReflUnsat.decide? == some false
#guard aboxLocalReflSat.decide? == some true
#guard aboxDisjointInverseUnsat.decide? == some false

/-! ### 4. Cyclic ABox with only infinite models -/

/-- Individual `root` has no `next`-predecessor while every object has a `next`-successor
and at most one `next`-predecessor. Satisfiable, with no finite model. -/
def infiniteChainABox : KnowledgeBase where
  tboxRBox :=
    { tbox :=
        [(.top, .some (.named "next") .top),
         (.top, .max 1 (.inverse "next") .top)] }
  abox :=
    [.concept (.max 0 (.inverse "next") .top) "root"]

theorem infiniteChainABox_sat : infiniteChainABox.Sat := by
  let m : ABoxModel :=
    { toModel := ⟨Nat, ⟨0⟩, fun _ _ => False, fun name x y => name = "next" ∧ y = x + 1⟩
      individuals := fun _ => 0 }
  refine ⟨m, ⟨?_, by simp [infiniteChainABox], by simp [infiniteChainABox]⟩, ?_⟩
  · intro gci hg x _
    change Nat at x
    simp only [infiniteChainABox, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨x + 1, ⟨rfl, rfl⟩, trivial⟩
    · apply mt cardinalityAtLeast_iff.mpr
      apply (atMostOne_iff _).mpr
      intro a b ha hb
      change Nat at a b
      have ha' : x = a + 1 := by simpa [Model.edge, m] using ha.1
      have hb' : x = b + 1 := by simpa [Model.edge, m] using hb.1
      exact Nat.add_right_cancel (ha'.symm.trans hb')
  · intro ax hax
    simp only [infiniteChainABox, List.mem_cons, List.not_mem_nil, or_false] at hax
    subst hax
    rintro ⟨f, _, hf⟩
    change Fin 1 → Nat at f
    have hf' : 0 = f 0 + 1 := by simpa [Model.edge, m] using (hf (0 : Fin 1)).1
    omega

#guard infiniteChainABox.decide? == some true

/-! ### 5. Rejection outside admission boundary (`none`) -/

private def nonSimpleABoxCardinality : KnowledgeBase where
  tboxRBox := { assertions := [.transitive (.named "r")] }
  abox := [.concept (.min 2 (.named "r") .top) "a"]

private def nonRegularABoxHierarchy : KnowledgeBase where
  tboxRBox :=
    { hierarchy :=
        [⟨.named "r", [.named "r"], "s"⟩,
         ⟨.named "s", [.named "s"], "r"⟩] }
  abox := [.role (.named "r") "a" "b"]

#guard nonSimpleABoxCardinality.decide? == none
#guard nonRegularABoxHierarchy.decideRanked? == none
#guard nonRegularABoxHierarchy.decide? == some true

#print axioms noUnaMergeSat_sat
#print axioms noUnaDiffUnsat_unsat
#print axioms negCompositeChainUnsat_unsat
#print axioms infiniteChainABox_sat

end Sabrina.OWL2.SROIQD.TextbookSRIQ
