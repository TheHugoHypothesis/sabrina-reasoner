import Sabrina.OWL2.DecisionProcedure

/-! The finite terminal predicate of the current decision interface cannot
cover every ordinary cyclic input. A total successor relation with at most
one predecessor per object and a predecessor-free root forces infinity. -/
namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.OWL2.DecisionProcedure (TerminatingRuleSet terminatingRuleSet_derivation)
open Sabrina.RoleChains (checkRegular)

private def roleName : IRI := "urn:sabrina:termination:successor"
private def forward : OrientedRole := (roleName,false)
private def backward : OrientedRole := (roleName,true)

private def totalSuccessor : Inclusion := ⟨.top,.some forward .top⟩
private def uniquePredecessor : Inclusion := ⟨.top,.max 1 backward .top⟩
private def startAssertion : Individual × Concept :=
  (.named "urn:sabrina:termination:start",.max 0 backward .top)

def infiniteChain : Problem :=
  { tbox := [totalSuccessor, uniquePredecessor]
    classAssertions := [startAssertion] }

def infiniteChainOntology : Ontology := infiniteChain.toOntology.reverse

theorem infiniteChain_normalizes :
    Normalize.normalizeWithDefs infiniteChainOntology = some ([], infiniteChain) := rfl

theorem infiniteChain_checks : infiniteChain.isOrdinary = true ∧
    infiniteChain.checkSimple = true ∧
    checkRegular (fun _ => 0) infiniteChain.rules infiniteChain.chains = true := by decide

private def orbit {α : Type} (f : α → α) (root : α) : Nat → α
  | 0 => root
  | n + 1 => f (orbit f root n)

private theorem orbit_injective {α : Type} (f : α → α) (root : α)
    (hi : ∀ a b, f a = f b → a = b) (hr : ∀ x, f x ≠ root) :
    ∀ m n, orbit f root m = orbit f root n → m = n := by
  intro m
  induction m with
  | zero =>
    rintro (_ | n) h
    · rfl
    · exact (hr _ h.symm).elim
  | succ m ih =>
    rintro (_ | n) h
    · exact (hr _ h).elim
    · exact congrArg Nat.succ (ih n (hi _ _ h))

private theorem mapped_nodup {α β : Type} {f : α → β} {xs : List α}
    (h : xs.Nodup) (hi : ∀ a b, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have h := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    refine ⟨?_,ih h.2⟩
    intro hm
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    exact h.1 (hi b a he ▸ hb)

private theorem no_enum_of_successors {α : Type} (R : α → α → Prop) (root : α)
    (ht : ∀ x, ∃ y, R x y) (hu : ∀ y a b, R a y → R b y → a = b)
    (hr : ∀ x, ¬ R x root) (xs : List α) :
    ¬ ∀ x, x ∈ xs := by
  classical
  let f := fun x => Classical.choose (ht x)
  have hf (x : α) : R x (f x) := Classical.choose_spec (ht x)
  have hi (a b : α) (he : f a = f b) : a = b := hu _ _ _ (hf a) (he ▸ hf b)
  have hn (x : α) : f x ≠ root := fun e => hr x (e ▸ hf x)
  let seen := (List.range (xs.length + 1)).map (orbit f root)
  have hseen : seen.Nodup := mapped_nodup List.nodup_range (orbit_injective f root hi hn)
  intro hall
  have hle : seen.length ≤ xs.length := hseen.length_le_of_subset (fun {a} _ => hall a)
  simp [seen] at hle
  omega

private theorem no_predecessor {i : Interpretation datatypeMap} {root : i.Object}
    (h : holds i root startAssertion.2) : ∀ x, ¬ holdsOriented i forward x root := by
  intro x hx
  apply h
  refine ⟨[x],rfl,by simp,?_⟩
  intro y hy
  obtain rfl := List.mem_singleton.mp hy
  exact ⟨hx,trivial⟩

theorem infiniteChain_no_finite_interpretation (i : Interpretation datatypeMap)
    (hi : infiniteChain.Models i) :
    ¬ ∃ xs : List i.Object, ∀ x, x ∈ xs := by
  rintro ⟨xs,hxs⟩
  have hr := hi.classAssertions startAssertion (by simp [infiniteChain])
  apply no_enum_of_successors (holdsOriented i forward) _ _ _ (no_predecessor hr) xs hxs
  · intro x
    obtain ⟨y,hy,_⟩ := hi.tbox totalSuccessor (by simp [infiniteChain]) x trivial
    exact ⟨y,hy⟩
  · intro y a b ha hb
    have hn := hi.tbox uniquePredecessor (by simp [infiniteChain]) y trivial
    exact (atMostOne_iff (fun x => holdsOriented i backward y x ∧ True)).mp hn a b
      ⟨ha,trivial⟩ ⟨hb,trivial⟩

private noncomputable def successorInterpretation : Interpretation datatypeMap :=
  let base := GradedBridge.extend datatypeMap
    ⟨Nat,⟨0⟩,fun _ _ => False,fun _ _ _ => False⟩ (fun _ => 0)
  { base with
    objectProperties := fun r x y => r = topObjectProperty ∨ (r = roleName ∧ y = Nat.succ x)
    topObjectExt := fun _ _ => .inl rfl
    bottomObjectExt := by
      intro _ _
      rintro (h | ⟨h,_⟩)
      · exact (by decide : bottomObjectProperty ≠ topObjectProperty) h
      · exact (by decide : bottomObjectProperty ≠ roleName) h }

private theorem successor_role (x y : Nat) :
    holdsOriented successorInterpretation forward x y ↔ y = x + 1 := by
  change (roleName = topObjectProperty ∨ (roleName = roleName ∧ y = x + 1)) ↔ _
  simp [show roleName ≠ topObjectProperty by decide]

theorem infiniteChain_sat : infiniteChain.Sat := by
  refine ⟨successorInterpretation, ?_, (0 : Nat), trivial⟩
  constructor
  case tbox =>
    intro q hq x _
    simp only [infiniteChain, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨Nat.succ x,(successor_role x _).mpr rfl,trivial⟩
    · apply (atMostOne_iff _).mpr
      intro a b ha hb
      have h₁ := (successor_role a x).mp ha.1
      have h₂ := (successor_role b x).mp hb.1
      exact Nat.add_right_cancel (h₁.symm.trans h₂)
  case classAssertions =>
    intro ax hax
    obtain rfl : ax = startAssertion := List.mem_singleton.mp hax
    change holds successorInterpretation (0 : Nat) startAssertion.2
    rintro ⟨xs,hxs,_,hall⟩
    cases xs with
    | nil => simp at hxs
    | cons x rest =>
      have hx := (hall x (List.mem_cons_self ..)).1
      have he := (successor_role x 0).mp hx
      omega
  all_goals simp [infiniteChain]

theorem infiniteChainOntology_sat : Satisfiable datatypeMap infiniteChainOntology :=
  (Normalize.normalizeWithDefs_sat_iff infiniteChain_normalizes).mpr
    ((satisfiable_iff_sat infiniteChain rfl).mpr infiniteChain_sat)

theorem infiniteChain_no_saturated_leaf (s : Branch) (hcf : s.CoreClashFree) :
    ¬ s.SROIQDSaturated infiniteChain := by
  intro hs
  let h0 : 0 ∈ s.support := Branch.label_support hs.root
  let i := s.toSROIQDInterpretation h0
  let root : i.Object := s.indNode h0 startAssertion.1
  have witness (q : Inclusion) (hq : q ∈ infiniteChain.tbox) (htop : q.sub = .top)
      (ho : q.sup.isOrdinary = true) (x : i.Object) : holds i x q.sup := by
    have hl := hs.tbox q hq x.val x.property
    rw [htop] at hl
    exact sroiqd_saturated_holds hcf hs x ho (hl.resolve_left (hcf.noBottom x.val))
  have hroot := sroiqd_saturated_holds hcf hs root
    (by decide : startAssertion.2.isOrdinary = true)
    (hs.classAssertions startAssertion (by simp [infiniteChain]))
  have htotal (x : i.Object) : ∃ y, holdsOriented i forward x y := by
    obtain ⟨y,hy,_⟩ := witness totalSuccessor (by simp [infiniteChain]) rfl (by decide) x
    exact ⟨y,hy⟩
  have hunique (y a b : i.Object) (ha : holdsOriented i forward a y)
      (hb : holdsOriented i forward b y) : a = b :=
    (atMostOne_iff (fun x => holdsOriented i backward y x ∧ True)).mp
      (witness uniquePredecessor (by simp [infiniteChain]) rfl (by decide) y) a b
      ⟨ha,trivial⟩ ⟨hb,trivial⟩
  exact no_enum_of_successors (holdsOriented i forward) root htotal hunique
    (no_predecessor hroot) s.support.attach (List.mem_attach s.support)

private theorem infiniteChain_derivation_closes {s : Branch} (hd : SROIQDDerivation infiniteChain s) :
    CoreRefutation infiniteChain s := by
  induction hd with
  | step t _ ih => exact .step t ih
  | saturated hcf hsat => exact (infiniteChain_no_saturated_leaf _ hcf hsat).elim

theorem infiniteChain_no_derivation {s : Branch} (hs : initial infiniteChain = some s) :
    ¬ SROIQDDerivation infiniteChain s := by
  intro hd
  exact coreRefutation_sound (infiniteChain_derivation_closes hd)
    (initial_sat hs infiniteChain_sat)

theorem infiniteChain_no_terminatingRuleSet : ¬ Nonempty (TerminatingRuleSet infiniteChain) := by
  rintro ⟨rs⟩
  obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp
    (by decide : (initial infiniteChain).isSome = true)
  exact infiniteChain_no_derivation hs (terminatingRuleSet_derivation rs s)

def topShortcutProblem : Problem := { root := .conj .top .top }

def topShortcutBranch : Branch := { labels := [(0, topShortcutProblem.root)] }

/-- The legacy selector treats top as implicit, whereas the current
finite-leaf predicate demands both conjunct labels explicitly. This
discrepancy already arises on a depth-zero acyclic input. -/
theorem next_none_without_saturation (limit : Nat) :
    initial topShortcutProblem = some topShortcutBranch ∧
      next topShortcutProblem topShortcutBranch limit = none ∧
      ¬ topShortcutBranch.SROIQDSaturated topShortcutProblem := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have hp := h.conj 0 .top .top (by simp [topShortcutBranch, topShortcutProblem])
  simp [topShortcutBranch, topShortcutProblem] at hp

#print axioms infiniteChain_normalizes
#print axioms infiniteChain_checks
#print axioms infiniteChain_no_finite_interpretation
#print axioms infiniteChain_sat
#print axioms infiniteChainOntology_sat
#print axioms infiniteChain_no_saturated_leaf
#print axioms infiniteChain_no_derivation
#print axioms infiniteChain_no_terminatingRuleSet
#print axioms next_none_without_saturation

end Sabrina.OWL2.SROIQD.Termination
