import Sabrina.OWL2.SROIQD.Termination.Automata
import Sabrina.OWL2.SROIQD.CoreCompleteness

namespace Sabrina.OWL2.SROIQD

open Sabrina.RoleChains (Rank checkRegular)

def Concept.isSRIQ : Concept → Bool
  | .top | .bottom => true
  | .lit a _ => isCoreClassIRI a
  | .self r _ => isCoreObjPropIRI r.1
  | .conj a b | .disj a b => a.isSRIQ && b.isSRIQ
  | .some r c | .all r c | .min _ r c | .max _ r c => isCoreObjPropIRI r.1 && c.isSRIQ
  | _ => false

/-- The root is the sole designated object. All ABox and concrete data fields
are empty, and no concept contains an individual name. -/
def Problem.isSRIQ (p : Problem) (rank : Rank) : Bool :=
  p.root.isSRIQ && p.tbox.all (fun q => q.sub.isSRIQ && q.sup.isSRIQ) &&
  p.rules.all (fun (r,s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.chains.all (fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI) &&
  p.chars.reflexive.all isCoreObjPropIRI && p.chars.irreflexive.all isCoreObjPropIRI &&
  p.chars.asymmetric.all isCoreObjPropIRI &&
  p.chars.disjoint.all (fun (r,s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.subData.isEmpty && p.disjointData.isEmpty && p.funcData.isEmpty && p.dataRanges.isEmpty &&
  p.keys.isEmpty && p.classAssertions.isEmpty && p.objAssertions.isEmpty &&
  p.negObjAssertions.isEmpty && p.sameInds.isEmpty && p.diffInds.isEmpty &&
  p.dataAssertions.isEmpty && p.negDataAssertions.isEmpty &&
  p.checkSimple && checkRegular rank p.rules p.chains

theorem Concept.sriq_no_individuals {c : Concept} (hc : c.isSRIQ = true) :
    c.individuals = [] := by
  induction c <;> simp_all [Concept.isSRIQ, Concept.individuals]

structure Problem.SRIQInput (rank : Rank) (p : Problem) : Prop where
  root : p.root.isSRIQ = true
  tbox : ∀ q ∈ p.tbox, q.sub.isSRIQ = true ∧ q.sup.isSRIQ = true
  rules : ∀ q ∈ p.rules, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  chains : ∀ c ∈ p.chains, isCoreObjPropIRI c.head = true ∧ ∀ r ∈ c.bodyNames, isCoreObjPropIRI r = true
  reflexive : ∀ r ∈ p.chars.reflexive, isCoreObjPropIRI r = true
  irreflexive : ∀ r ∈ p.chars.irreflexive, isCoreObjPropIRI r = true
  asymmetric : ∀ r ∈ p.chars.asymmetric, isCoreObjPropIRI r = true
  disjoint : ∀ q ∈ p.chars.disjoint, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  subData : p.subData = []
  disjointData : p.disjointData = []
  funcData : p.funcData = []
  dataRanges : p.dataRanges = []
  keys : p.keys = []
  classAssertions : p.classAssertions = []
  objAssertions : p.objAssertions = []
  negObjAssertions : p.negObjAssertions = []
  sameInds : p.sameInds = []
  diffInds : p.diffInds = []
  dataAssertions : p.dataAssertions = []
  negDataAssertions : p.negDataAssertions = []
  simple : p.checkSimple = true
  regular : checkRegular rank p.rules p.chains = true

theorem Problem.sriqInput {p : Problem} {rank : Rank} (h : p.isSRIQ rank = true) :
    p.SRIQInput rank := by
  simp only [Problem.isSRIQ, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  grind [Problem.SRIQInput.mk]

theorem Problem.SRIQInput.no_individuals {p : Problem} {rank : Rank} (h : p.SRIQInput rank) :
    p.nominals = [] ∧ p.anons = [] := by
  have ht : p.tbox.flatMap (fun q => q.sub.individuals ++ q.sup.individuals) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    have hs := h.tbox q hq
    simp [Concept.sriq_no_individuals hs.1, Concept.sriq_no_individuals hs.2]
  simp [Problem.nominals, Problem.anons, Problem.allIndividuals, ht,
    Concept.sriq_no_individuals h.root, h.keys, h.classAssertions, h.objAssertions,
    h.negObjAssertions, h.sameInds, h.diffInds, h.dataAssertions, h.negDataAssertions]

namespace Termination
open Sabrina.ALC (OrientedRole converse)
open Sabrina.RoleChains.TransitivePaths (converse_converse)

/-- A finite rooted tree in parent-before-child order. Edge labels are stored
on the child, with separate sets for each direction. -/
structure BlockedBranch where
  size : Nat
  parent : Fin (size + 1) → Fin (size + 1)
  parent_lt : ∀ x, x ≠ 0 → (parent x).val < x.val
  labels : Fin (size + 1) → List Concept
  guardLabels : Fin (size + 1) → List Guard
  down : Fin (size + 1) → List IRI
  up : Fin (size + 1) → List IRI
  loops : Fin (size + 1) → List IRI
  unequal : List (Fin (size + 1) × Fin (size + 1))
  unequal_siblings : ∀ x y, (x,y) ∈ unequal →
    x ≠ 0 ∧ y ≠ 0 ∧ parent x = parent y
  blockedBy : Fin (size + 1) → Option (Fin (size + 1))

namespace BlockedBranch

abbrev Node (b : BlockedBranch) := Fin (b.size + 1)

def Child (b : BlockedBranch) (x y : b.Node) : Prop := y ≠ 0 ∧ b.parent y = x

theorem child_lt {b : BlockedBranch} {x y : b.Node} (h : b.Child x y) : x.val < y.val :=
  h.2 ▸ b.parent_lt y h.1

inductive Anc (b : BlockedBranch) : b.Node → b.Node → Prop where
  | parent {x y} : b.Child x y → Anc b x y
  | step {a x y} : Anc b a x → b.Child x y → Anc b a y

theorem Anc.lt {b : BlockedBranch} {x y : b.Node} (h : b.Anc x y) : x.val < y.val := by
  induction h with
  | parent h => exact child_lt h
  | step _ h ih => exact Nat.lt_trans ih (child_lt h)

theorem Anc.child_iff {b : BlockedBranch} {a x y : b.Node} (h : b.Child x y) :
    b.Anc a y ↔ a = x ∨ b.Anc a x := by
  constructor
  · intro ha
    cases ha with
    | parent hv => exact .inl (hv.2.symm.trans h.2)
    | step hu hv => exact .inr (hv.2.symm.trans h.2 ▸ hu)
  · rintro (rfl | ha)
    · exact .parent h
    · exact .step ha h

theorem Anc.trans {b : BlockedBranch} {x y z : b.Node} (h : b.Anc x y)
    (h' : b.Anc y z) : b.Anc x z := by
  induction h' with
  | parent hc => exact .step h hc
  | step _ hc ih => exact .step ih hc

theorem root_ancestor {b : BlockedBranch} (x : b.Node) (hx : x ≠ 0) :
    b.Anc 0 x := by
  have h : b.Child (b.parent x) x := ⟨hx,rfl⟩
  by_cases hp : b.parent x = 0
  · exact hp ▸ Anc.parent h
  · exact .step (root_ancestor (b.parent x) hp) h
termination_by x.val
decreasing_by exact b.parent_lt x hx

def DirectlyBlocked (b : BlockedBranch) (x : b.Node) : Prop := (b.blockedBy x).isSome

def IndirectlyBlocked (b : BlockedBranch) (x : b.Node) : Prop :=
  ∃ a, b.Anc a x ∧ b.DirectlyBlocked a

def Unblocked (b : BlockedBranch) (x : b.Node) : Prop :=
  b.blockedBy x = none ∧ ¬ b.IndirectlyBlocked x

def target (b : BlockedBranch) (x : b.Node) : b.Node := (b.blockedBy x).getD x

def Down (b : BlockedBranch) (r : OrientedRole) (y : b.Node) : Prop :=
  r.1 ∈ if r.2 then b.up y else b.down y

def Edge (b : BlockedBranch) (r : OrientedRole) (x y : b.Node) : Prop :=
  (x = y ∧ r.1 ∈ b.loops x) ∨
    (b.Child x y ∧ b.Down r y) ∨ (b.Child y x ∧ b.Down (converse r) x)

theorem edge_converse (b : BlockedBranch) (r : OrientedRole) (x y : b.Node) :
    b.Edge (converse r) y x ↔ b.Edge r x y := by
  simp only [Edge, converse_converse]
  constructor <;> rintro (⟨rfl,h⟩ | h | h)
  · exact .inl ⟨rfl,h⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)
  · exact .inl ⟨rfl,h⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)

theorem edge_child_iff {b : BlockedBranch} {r : OrientedRole} {x y : b.Node}
    (h : b.Child x y) : b.Edge r x y ↔ b.Down r y := by
  have hlt := child_lt h
  constructor
  · rintro (⟨rfl,_⟩ | ⟨_,he⟩ | ⟨hrev,_⟩)
    · exact (Nat.lt_irrefl _ hlt).elim
    · exact he
    · exact (Nat.lt_asymm hlt (child_lt hrev)).elim
  · exact fun he => .inr (.inl ⟨h,he⟩)

theorem edge_loop_iff (b : BlockedBranch) (r : OrientedRole) (x : b.Node) :
    b.Edge r x x ↔ r.1 ∈ b.loops x := by
  constructor
  · rintro (⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩)
    · exact h
    · exact (Nat.lt_irrefl _ (child_lt h)).elim
    · exact (Nat.lt_irrefl _ (child_lt h)).elim
  · exact fun h => .inl ⟨rfl,h⟩

/-- Pairwise blocking compares both endpoints and both directions of the
incoming tree edge. Membership equality makes label order immaterial. -/
structure PairMatch (b : BlockedBranch) (x y : b.Node) : Prop where
  parentLabels : ∀ c, c ∈ b.labels (b.parent x) ↔ c ∈ b.labels (b.parent y)
  labels : ∀ c, c ∈ b.labels x ↔ c ∈ b.labels y
  parentGuards : ∀ g, g ∈ b.guardLabels (b.parent x) ↔ g ∈ b.guardLabels (b.parent y)
  guards : ∀ g, g ∈ b.guardLabels x ↔ g ∈ b.guardLabels y
  roles : ∀ r, b.Down r x ↔ b.Down r y

structure BlockingValid (b : BlockedBranch) : Prop where
  blocker : ∀ x y, b.blockedBy x = some y →
    b.Anc y x ∧ y ≠ 0 ∧ b.Unblocked y ∧ ¬ b.IndirectlyBlocked x ∧ b.PairMatch x y

theorem direct_blocker {b : BlockedBranch} (hw : b.BlockingValid) {x : b.Node}
    (h : b.DirectlyBlocked x) :
    b.Anc (b.target x) x ∧ b.target x ≠ 0 ∧ b.Unblocked (b.target x) ∧
      ¬ b.IndirectlyBlocked x ∧ b.PairMatch x (b.target x) := by
  cases e : b.blockedBy x with
  | none => simp [DirectlyBlocked,e] at h
  | some y => simpa [target,e] using hw.blocker x y e

theorem target_of_unblocked {b : BlockedBranch} {x : b.Node} (h : b.Unblocked x) :
    b.target x = x := by simp [target,h.1]

theorem target_match {b : BlockedBranch} {x : b.Node} (hw : b.BlockingValid) :
    b.PairMatch x (b.target x) := by
  cases e : b.blockedBy x with
  | none => simp only [target,e,Option.getD_none]; exact ⟨fun _ => Iff.rfl,fun _ => Iff.rfl,
      fun _ => Iff.rfl,fun _ => Iff.rfl,fun _ => Iff.rfl⟩
  | some y => simpa [target,e] using (hw.blocker x y e).2.2.2.2

theorem root_unblocked {b : BlockedBranch} (hw : b.BlockingValid) :
    b.Unblocked 0 := by
  constructor
  · cases e : b.blockedBy 0 with
    | none => rfl
    | some y =>
      have hlt := (hw.blocker 0 y e).1.lt
      exact (Nat.not_lt_zero _ hlt).elim
  · rintro ⟨a,ha,_⟩
    exact Nat.not_lt_zero _ ha.lt

theorem target_nonroot {b : BlockedBranch} (hw : b.BlockingValid) {x : b.Node}
    (hx : x ≠ 0) : b.target x ≠ 0 := by
  cases e : b.blockedBy x with
  | none => simpa [target,e] using hx
  | some y => simpa [target,e] using (hw.blocker x y e).2.1

theorem child_target_unblocked {b : BlockedBranch} (hw : b.BlockingValid) {x y : b.Node}
    (hx : b.Unblocked x) (hy : b.Child x y) : b.Unblocked (b.target y) := by
  cases e : b.blockedBy y with
  | some z => simpa [target,e] using (hw.blocker y z e).2.2.1
  | none =>
    rw [show b.target y = y by simp [target,e]]
    refine ⟨e,?_⟩
    rintro ⟨a,ha,hb⟩
    rcases (Anc.child_iff hy).mp ha with rfl | h
    · simp [DirectlyBlocked,hx.1] at hb
    · exact hx.2 ⟨a,h,hb⟩

structure BlockedClashFree (b : BlockedBranch) (p : Problem) : Prop where
  bottom : ∀ x, .bottom ∉ b.labels x
  literal : ∀ x a, .lit a true ∈ b.labels x → .lit a false ∉ b.labels x
  unequal : ∀ x, (x,x) ∉ b.unequal
  irreflexive : ∀ r ∈ p.chars.irreflexive, ∀ x, ¬ b.Edge (r,false) x x
  asymmetric : ∀ r ∈ p.chars.asymmetric, ∀ x y, b.Edge (r,false) x y → ¬ b.Edge (r,false) y x
  disjoint : ∀ q ∈ p.chars.disjoint, ∀ x y, ¬ (b.Edge q.1 x y ∧ b.Edge q.2 x y)
  selfNeg : ∀ x r, .self r false ∈ b.labels x → ¬ b.Edge r x x

structure BlockedSaturated (b : BlockedBranch) (rank : Rank) (p : Problem) : Prop where
  blocking : b.BlockingValid
  root : p.root ∈ b.labels 0
  conj : ∀ x, b.Unblocked x → ∀ a c, .conj a c ∈ b.labels x →
    a ∈ b.labels x ∧ c ∈ b.labels x
  disj : ∀ x, b.Unblocked x → ∀ a c, .disj a c ∈ b.labels x →
    a ∈ b.labels x ∨ c ∈ b.labels x
  some : ∀ x, b.Unblocked x → ∀ r c, .some r c ∈ b.labels x →
    ∃ y, b.Edge r x y ∧ c ∈ b.labels y
  min : ∀ x, b.Unblocked x → ∀ n r c, .min n r c ∈ b.labels x →
    AtLeast n (fun y => b.Edge r x y ∧ c ∈ b.labels y)
  maxQual : ∀ x, b.Unblocked x → ∀ n r c, .max n r c ∈ b.labels x → ∀ y, b.Edge r x y →
    c ∈ b.labels y ∨ c.dual ∈ b.labels y
  maxBound : ∀ x, b.Unblocked x → ∀ n r c, .max n r c ∈ b.labels x →
    ¬ AtLeast (n+1) (fun y => b.Edge r x y ∧ c ∈ b.labels y)
  selfPos : ∀ x, b.Unblocked x → ∀ r, .self r true ∈ b.labels x → b.Edge r x x
  tbox : ∀ q ∈ p.tbox, ∀ x, b.Unblocked x → q.sub.dual ∈ b.labels x ∨ q.sup ∈ b.labels x
  rules : ∀ q ∈ p.rules, ∀ x y, b.Edge q.1 x y → b.Edge q.2 x y
  reflexive : ∀ r ∈ p.chars.reflexive, ∀ x, b.Edge (r,false) x x
  guardStart : ∀ x, b.Unblocked x → ∀ r c, .all r c ∈ b.labels x →
    (⟨roleLanguage rank p r,c⟩ : Guard) ∈ b.guardLabels x
  guardStep : ∀ x y r, b.Edge r x y → ∀ g ∈ b.guardLabels x, ∀ k ∈ g.advance r,
    k ∈ b.guardLabels y
  guardAccept : ∀ x, ∀ g ∈ b.guardLabels x, g.state.nullable = true → g.filler ∈ b.labels x

/-- The usual local universal rule follows from one guard transition.
Longer words are handled by the walk proof in `Unraveling`. -/
theorem BlockedSaturated.all_local {b : BlockedBranch} {rank : Rank} {p : Problem}
    (h : b.BlockedSaturated rank p) (hr : checkRegular rank p.rules p.chains = true)
    {x y : b.Node} (hx : b.Unblocked x) {r : OrientedRole} {c : Concept}
    (hl : .all r c ∈ b.labels x) (he : b.Edge r x y) : c ∈ b.labels y := by
  let g : Guard := ⟨roleLanguage rank p r,c⟩
  have hw := (roleLanguage_accepts hr r [r]).mpr
    ((Sabrina.RoleChains.RankedPaths.generated_closed _ _).letter r)
  have hm := (g.state.accepts_iff [r]).mp hw
  obtain ⟨state,hres,ha⟩ := (Sabrina.RoleChains.PathRegex.matches_derivative _ _ _).mp hm
  let next : Guard := ⟨state,c⟩
  have hnext : next ∈ g.advance r := List.mem_map.mpr ⟨state,hres,rfl⟩
  exact h.guardAccept y next (h.guardStep x y r he g (h.guardStart x hx r c hl) next hnext)
    (state.nullable_iff.mpr ha)

#print axioms direct_blocker

end BlockedBranch
end Termination
end Sabrina.OWL2.SROIQD
