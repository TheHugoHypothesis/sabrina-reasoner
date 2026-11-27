import Sabrina.OWL2.SROIQD.Termination.Unraveling

/-! Search semantics and finite blocking bounds for the object-only fragment. -/
namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank)
open Sabrina.RoleChains.TransitivePaths (converse_converse)

namespace BlockedBranch

variable {b : BlockedBranch}

/-- A realizing assignment may identify nodes, subject to the explicit
inequalities imposed when it creates a set of number-restriction witnesses.
Blocking links impose no equality on the realizing assignment. -/
structure Realizes (b : BlockedBranch) (i : Interpretation datatypeMap)
    (env : b.Node → i.Object) : Prop where
  labels : ∀ x c, c ∈ b.labels x → holds i (env x) c
  edges : ∀ r x y, b.Edge r x y → holdsOriented i r (env x) (env y)
  guards : ∀ x g, g ∈ b.guardLabels x → g.Holds i (env x)
  unequal : ∀ x y, (x,y) ∈ b.unequal → env x ≠ env y

def Sat (b : BlockedBranch) (p : Problem) : Prop :=
  ∃ i : Interpretation datatypeMap, p.Models i ∧ ∃ env, b.Realizes i env

def LabelsWithin (b : BlockedBranch) (p : Problem) : Prop :=
  ∀ x, b.labels x ⊆ clos p

def GuardsWithin (b : BlockedBranch) (rank : Rank) (p : Problem) : Prop :=
  ∀ x, b.guardLabels x ⊆ guards rank p

private def conceptRoles : Concept → List IRI
  | .some r _ | .all r _ | .min _ r _ | .max _ r _ | .self r _ => [r.1]
  | _ => []

def roleNames (p : Problem) : List IRI :=
  ((clos p).flatMap conceptRoles ++ p.rules.flatMap (fun (r,s) => [r.1,s.1]) ++
    p.chains.flatMap (fun c => c.head :: c.bodyNames) ++ p.chars.reflexive ++
    p.chars.irreflexive ++ p.chars.asymmetric ++
    p.chars.disjoint.flatMap (fun (r,s) => [r.1,s.1])).eraseDups

def RolesWithin (b : BlockedBranch) (p : Problem) : Prop :=
  ∀ x, b.down x ⊆ roleNames p ∧ b.up x ⊆ roleNames p ∧ b.loops x ⊆ roleNames p

structure Within (b : BlockedBranch) (rank : Rank) (p : Problem) : Prop where
  labels : b.LabelsWithin p
  guards : b.GuardsWithin rank p
  roles : b.RolesWithin p

def initial (p : Problem) : BlockedBranch where
  size := 0
  parent _ := 0
  parent_lt := by intro x h; have hx := x.isLt; exact (h (Fin.ext (by omega))).elim
  labels _ := [p.root]
  guardLabels _ := []
  down _ := []
  up _ := []
  loops _ := []
  unequal := []
  unequal_siblings := by simp
  blockedBy _ := none

theorem initial_within (rank : Rank) (p : Problem) : (initial p).Within rank p := by
  refine ⟨?_,fun _ => List.nil_subset _,fun _ => ⟨List.nil_subset _,List.nil_subset _,List.nil_subset _⟩⟩
  intro x c h
  obtain rfl := List.mem_singleton.mp h
  exact seed_mem_clos (by simp [seeds])

theorem initial_sat_iff (p : Problem) : (initial p).Sat p ↔ p.Sat := by
  constructor
  · rintro ⟨i,hi,e,he⟩
    exact ⟨i,hi,e 0,he.labels 0 p.root (by simp [initial])⟩
  · rintro ⟨i,hi,x,hx⟩
    refine ⟨i,hi,fun _ => x,?_⟩
    constructor
    · intro y c h
      obtain rfl := List.mem_singleton.mp h
      exact hx
    · intro r y z he
      simp [Edge,Down,initial] at he
    · intro y g hg
      exact (List.not_mem_nil hg).elim
    · intro y z h
      exact (List.not_mem_nil h).elim

private theorem orientation_flip (i : Interpretation datatypeMap) (r : OrientedRole)
    (x y : i.Object) : holdsOriented i (converse r) y x ↔ holdsOriented i r x y := by
  rcases r with ⟨r,_ | _⟩ <;> rfl

theorem realizes_clashFree {p : Problem} {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hm : p.Models i) (he : b.Realizes i env) : b.BlockedClashFree p := by
  constructor
  · intro x h
    exact he.labels x .bottom h
  · intro x a hp hn
    exact he.labels x (.lit a false) hn (he.labels x (.lit a true) hp)
  · intro x h
    exact he.unequal x x h rfl
  · intro r hr x h
    exact hm.irreflexive r hr (env x) (he.edges (r,false) x x h)
  · intro r hr x y h h'
    exact hm.asymmetric r hr (env x) (env y)
      (he.edges (r,false) x y h) (he.edges (r,false) y x h')
  · intro q hq x y h
    exact hm.disjoint q hq (env x) (env y) ⟨he.edges q.1 x y h.1,he.edges q.2 x y h.2⟩
  · intro x r hl h
    exact he.labels x (.self r false) hl (he.edges r x x h)

theorem clash_refutes {p : Problem} (h : ¬ b.BlockedClashFree p) : ¬ b.Sat p := by
  rintro ⟨i,hm,env,he⟩
  exact h (realizes_clashFree hm he)

/-- The strict ancestors, starting at the parent and ending with the root. -/
def ancestors (b : BlockedBranch) (x : b.Node) : List b.Node :=
  if _h : x = 0 then [] else b.parent x :: b.ancestors (b.parent x)
termination_by x.val
decreasing_by exact b.parent_lt x _h

theorem mem_ancestors {x a : b.Node} : a ∈ b.ancestors x ↔ b.Anc a x := by
  rw [ancestors]
  split
  · rename_i hx
    subst x
    exact ⟨fun h => (List.not_mem_nil h).elim,fun h => (Nat.not_lt_zero _ h.lt).elim⟩
  · rename_i hx
    exact List.mem_cons.trans
      ((or_congr Iff.rfl (mem_ancestors (x := b.parent x))).trans
        (Anc.child_iff ⟨hx,rfl⟩).symm)
termination_by x.val
decreasing_by apply b.parent_lt; assumption

def depth (b : BlockedBranch) (x : b.Node) : Nat := (b.ancestors x).length

/-- The compact index set after pruning a subtree. Index order is inherited
from the source, so parent-before-child order survives compaction. -/
def retained (b : BlockedBranch) (drop : b.Node) : List b.Node :=
  (List.finRange (b.size+1)).filter (fun x => x != drop && !(b.ancestors x).contains drop)

theorem mem_retained {drop x : b.Node} :
    x ∈ b.retained drop ↔ x ≠ drop ∧ ¬ b.Anc drop x := by
  simp [retained,mem_ancestors]

/-- Extra inequalities belong to the search state. They record identifications
across levels without changing the sibling-only invariant of the unfolded
tree interface. -/
structure ConstrainedTree where
  tree : BlockedBranch
  extraUnequal : List (tree.Node × tree.Node)

def ConstrainedTree.Realizes (s : ConstrainedTree) (i : Interpretation datatypeMap)
    (env : s.tree.Node → i.Object) : Prop :=
  s.tree.Realizes i env ∧ ∀ x y, (x,y) ∈ s.extraUnequal → env x ≠ env y

def ConstrainedTree.Sat (s : ConstrainedTree) (p : Problem) : Prop :=
  ∃ i : Interpretation datatypeMap, p.Models i ∧ ∃ env, s.Realizes i env

def ConstrainedTree.RecordedDistinct (s : ConstrainedTree) (x y : s.tree.Node) : Prop :=
  ((x,y) ∈ s.tree.unequal ∨ (x,y) ∈ s.extraUnequal) ∨
    ((y,x) ∈ s.tree.unequal ∨ (y,x) ∈ s.extraUnequal)

theorem ConstrainedTree.RecordedDistinct.symm {s : ConstrainedTree} {x y : s.tree.Node}
    (h : s.RecordedDistinct x y) : s.RecordedDistinct y x :=
  h.elim Or.inr Or.inl

/-- A lower-bound witness group whose distinctness is explicitly recorded.
Existing neighbors can satisfy a lower bound without supplying this stronger
invariant. A fresh group allocated by the generating rule supplies it. -/
def ConstrainedTree.ProtectedWitnesses (s : ConstrainedTree) (x : s.tree.Node)
    (r : OrientedRole) (c : Concept) (n : Nat) : Prop :=
  ∃ ys : List s.tree.Node, ys.length = n ∧ ys.Nodup ∧ ys.Pairwise s.RecordedDistinct ∧
    ∀ y ∈ ys, s.tree.Edge r x y ∧ c ∈ s.tree.labels y

abbrev KeepsVertex (b : BlockedBranch) (drop : Option b.Node) (x : b.Node) : Prop :=
  match drop with
  | none => True
  | some d => x ∈ b.retained d

/-- A transition preserves the incident witnesses of every surviving center
and preserves explicit inequalities between their images. -/
structure WitnessMap (s t : ConstrainedTree) (drop : Option s.tree.Node) where
  redirect : s.tree.Node → Option t.tree.Node
  root : redirect 0 = some 0
  center : ∀ x, KeepsVertex s.tree drop x → ∃ x', redirect x = some x'
  injectiveOnSurvivors : ∀ {x y : s.tree.Node} {z : t.tree.Node},
    KeepsVertex s.tree drop x → KeepsVertex s.tree drop y →
    redirect x = some z → redirect y = some z → x = y
  parent : ∀ {x y : s.tree.Node}, s.tree.Child x y → KeepsVertex s.tree drop y →
    KeepsVertex s.tree drop x ∧ ∀ {x' y' : t.tree.Node},
      redirect x = some x' → redirect y = some y' → t.tree.Child x' y'
  edge : ∀ {x : s.tree.Node} {x' : t.tree.Node}, KeepsVertex s.tree drop x →
    redirect x = some x' → ∀ r y, s.tree.Edge r x y →
      ∃ y', redirect y = some y' ∧ t.tree.Edge r x' y'
  label : ∀ {y : s.tree.Node} {y' : t.tree.Node}, redirect y = some y' →
    ∀ c ∈ s.tree.labels y, c ∈ t.tree.labels y'
  distinct : ∀ {y z : s.tree.Node} {y' z' : t.tree.Node},
    redirect y = some y' → redirect z = some z' → y ≠ z → s.RecordedDistinct y z →
      y' ≠ z' ∧ t.RecordedDistinct y' z'


abbrev MergeWitnessMap (s t : ConstrainedTree) (drop : s.tree.Node) :=
  WitnessMap s t (some drop)

private def extensionWitnessMap {s t : ConstrainedTree} (f : s.tree.Node → t.tree.Node)
    (injective : ∀ {x y}, f x = f y → x = y)
    (root : f 0 = 0)
    (parents : ∀ {x y}, s.tree.Child x y → t.tree.Child (f x) (f y))
    (edges : ∀ {x y r}, s.tree.Edge r x y → t.tree.Edge r (f x) (f y))
    (labels : ∀ {x c}, c ∈ s.tree.labels x → c ∈ t.tree.labels (f x))
    (distinct : ∀ {x y}, s.RecordedDistinct x y → t.RecordedDistinct (f x) (f y)) :
    WitnessMap s t none where
  redirect x := some (f x)
  root := congrArg some root
  center x _ := ⟨f x,rfl⟩
  injectiveOnSurvivors _ _ hx hy := injective (Option.some.inj (hx.trans hy.symm))
  parent hc _ := ⟨trivial,fun hx hy => by cases hx; cases hy; exact parents hc⟩
  edge _ h r y he := by
    cases h
    exact ⟨f y,rfl,edges he⟩
  label h c hc := by
    cases h
    exact labels hc
  distinct hx hy ne h := by
    cases hx
    cases hy
    exact ⟨fun eq => ne (injective eq),distinct h⟩

structure ConstrainedTransition (rank : Rank) (p : Problem) (s : ConstrainedTree) where
  branches : List ConstrainedTree
  preserves : s.Sat p → ∃ t ∈ branches, t.Sat p
  within : s.tree.Within rank p → ∀ t ∈ branches, t.tree.Within rank p
  root : p.root ∈ s.tree.labels 0 → ∀ t ∈ branches, p.root ∈ t.tree.labels 0
  protects : ∀ t ∈ branches, ∃ drop, Nonempty (WitnessMap s t drop)

end BlockedBranch

/-- Branching preserves at least one realization and keeps every alternative
inside the finite alphabet whenever the source uses that alphabet. -/
structure BlockedTransition (rank : Rank) (p : Problem) (b : BlockedBranch) where
  branches : List BlockedBranch
  preserves : b.Sat p → ∃ next ∈ branches, next.Sat p
  within : b.Within rank p → ∀ next ∈ branches, next.Within rank p
  root : p.root ∈ b.labels 0 → ∀ next ∈ branches, p.root ∈ next.labels 0
  lift : ∀ xs : List (b.Node × b.Node), BlockedBranch.ConstrainedTransition rank p ⟨b,xs⟩

inductive BlockedRefutation (rank : Rank) (p : Problem) : BlockedBranch → Prop where
  | step {b} (t : BlockedTransition rank p b) :
      (∀ next ∈ t.branches, BlockedRefutation rank p next) → BlockedRefutation rank p b

theorem blockedRefutation_sound {rank : Rank} {p : Problem} {b : BlockedBranch}
    (h : BlockedRefutation rank p b) : ¬ b.Sat p := by
  induction h with
  | step t _ ih =>
    intro hb
    obtain ⟨next,hn,hs⟩ := t.preserves hb
    exact ih next hn hs

def BlockedTransition.close {rank : Rank} {p : Problem} {b : BlockedBranch}
    (h : ¬ b.BlockedClashFree p) : BlockedTransition rank p b where
  branches := []
  preserves := fun hb => (BlockedBranch.clash_refutes h hb).elim
  within := by simp
  root := by simp
  lift _ := ⟨[],fun ⟨i,hm,e,he⟩ => (BlockedBranch.clash_refutes h ⟨i,hm,e,he.1⟩).elim,
    by simp,by simp,by simp⟩

namespace BlockedBranch

variable {b : BlockedBranch}

private def addOnce {α : Type} [DecidableEq α] (a : α) (xs : List α) : List α :=
  if a ∈ xs then xs else a :: xs

private theorem mem_addOnce {α : Type} [DecidableEq α] {a c : α} {xs : List α} :
    c ∈ addOnce a xs ↔ c = a ∨ c ∈ xs := by
  unfold addOnce
  split
  · rename_i ha
    exact ⟨Or.inr, fun h => h.elim (· ▸ ha) id⟩
  · exact List.mem_cons

/-- Expanding a label or guard invalidates the cached blocking choices. -/
def addLabel (b : BlockedBranch) (x : b.Node) (c : Concept) : BlockedBranch :=
  { b with labels := fun y => if y = x then addOnce c (b.labels y) else b.labels y
           blockedBy := fun _ => none }

def addGuard (b : BlockedBranch) (x : b.Node) (g : Guard) : BlockedBranch :=
  { b with guardLabels := fun y => if y = x then addOnce g (b.guardLabels y) else b.guardLabels y
           blockedBy := fun _ => none }

private theorem addLabel_mem {x y : b.Node} {c d : Concept} :
    d ∈ (b.addLabel x c).labels y ↔ (y = x ∧ d = c) ∨ d ∈ b.labels y := by
  by_cases hy : y = x <;> simp [addLabel,hy,mem_addOnce]

private theorem addGuard_mem {x y : b.Node} {g k : Guard} :
    k ∈ (b.addGuard x g).guardLabels y ↔ (y = x ∧ k = g) ∨ k ∈ b.guardLabels y := by
  by_cases hy : y = x <;> simp [addGuard,hy,mem_addOnce]

theorem addLabel_within {p : Problem} {rank : Rank} {x : b.Node} {c : Concept}
    (hw : b.Within rank p) (hc : c ∈ clos p) : (b.addLabel x c).Within rank p := by
  refine ⟨?_,hw.guards,hw.roles⟩
  intro y d hd
  rcases addLabel_mem.mp hd with ⟨_,rfl⟩ | hd
  · exact hc
  · exact hw.labels y hd

theorem addGuard_within {p : Problem} {rank : Rank} {x : b.Node} {g : Guard}
    (hw : b.Within rank p) (hg : g ∈ guards rank p) : (b.addGuard x g).Within rank p := by
  refine ⟨hw.labels,?_,hw.roles⟩
  intro y k hk
  rcases addGuard_mem.mp hk with ⟨_,rfl⟩ | hk
  · exact hg
  · exact hw.guards y hk

theorem Realizes.addLabel_realizes {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (h : b.Realizes i env) {x : b.Node} {c : Concept} (hc : holds i (env x) c) :
    (b.addLabel x c).Realizes i env := by
  refine ⟨?_,h.edges,h.guards,h.unequal⟩
  intro y d hd
  rcases addLabel_mem.mp hd with ⟨ey,ed⟩ | hd
  · subst y; subst d; exact hc
  · exact h.labels y d hd

theorem Realizes.addGuard_realizes {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (h : b.Realizes i env) {x : b.Node} {g : Guard} (hg : g.Holds i (env x)) :
    (b.addGuard x g).Realizes i env := by
  refine ⟨h.labels,h.edges,?_,h.unequal⟩
  intro y k hk
  rcases addGuard_mem.mp hk with ⟨ey,ek⟩ | hk
  · subst y; subst k; exact hg
  · exact h.guards y k hk

/-- A deterministic rule adds a consequent valid in every realization. -/
def labelStep {p : Problem} {rank : Rank} (x : b.Node) (c : Concept) (hc : b.Within rank p → c ∈ clos p)
    (derive : ∀ (i : Interpretation datatypeMap) (env : b.Node → i.Object),
      p.Models i → b.Realizes i env → holds i (env x) c) : BlockedTransition rank p b where
  branches := [b.addLabel x c]
  preserves := by
    rintro ⟨i,hm,env,he⟩
    exact ⟨_,List.mem_singleton_self _,i,hm,env,he.addLabel_realizes (derive i env hm he)⟩
  within := by
    intro hw next hn
    obtain rfl := List.mem_singleton.mp hn
    exact addLabel_within hw (hc hw)
  root := by
    intro hr next hn
    obtain rfl := List.mem_singleton.mp hn
    exact addLabel_mem.mpr (.inr hr)
  lift xs := {
    branches := [⟨b.addLabel x c,xs⟩]
    preserves := by
      rintro ⟨i,hm,e,he,hn⟩
      exact ⟨_,List.mem_singleton_self _,i,hm,e,he.addLabel_realizes (derive i e hm he),hn⟩
    within := by
      intro hw next hn
      obtain rfl := List.mem_singleton.mp hn
      exact addLabel_within hw (hc hw)
    root := by
      intro hr next hn
      obtain rfl := List.mem_singleton.mp hn
      exact addLabel_mem.mpr (.inr hr)
    protects := by
      intro next hn
      obtain rfl := List.mem_singleton.mp hn
      exact ⟨none,⟨extensionWitnessMap id (fun h => h) rfl (fun h => h) (fun h => h)
        (fun h => addLabel_mem.mpr (.inr h)) (fun h => h)⟩⟩ }

def guardStep {p : Problem} {rank : Rank} (x : b.Node) (g : Guard)
    (hg : b.Within rank p → g ∈ guards rank p)
    (derive : ∀ (i : Interpretation datatypeMap) (env : b.Node → i.Object),
      p.Models i → b.Realizes i env → g.Holds i (env x)) : BlockedTransition rank p b where
  branches := [b.addGuard x g]
  preserves := by
    rintro ⟨i,hm,env,he⟩
    exact ⟨_,List.mem_singleton_self _,i,hm,env,he.addGuard_realizes (derive i env hm he)⟩
  within := by
    intro hw next hn
    obtain rfl := List.mem_singleton.mp hn
    exact addGuard_within hw (hg hw)
  root := by
    intro hr next hn
    obtain rfl := List.mem_singleton.mp hn
    exact hr
  lift xs := {
    branches := [⟨b.addGuard x g,xs⟩]
    preserves := by
      rintro ⟨i,hm,e,he,hn⟩
      exact ⟨_,List.mem_singleton_self _,i,hm,e,he.addGuard_realizes (derive i e hm he),hn⟩
    within := by
      intro hw next hn
      obtain rfl := List.mem_singleton.mp hn
      exact addGuard_within hw (hg hw)
    root := by
      intro hr next hn
      obtain rfl := List.mem_singleton.mp hn
      exact hr
    protects := by
      intro next hn
      obtain rfl := List.mem_singleton.mp hn
      exact ⟨none,⟨extensionWitnessMap id (fun h => h) rfl (fun h => h)
        (fun h => h) (fun h => h) (fun h => h)⟩⟩ }

/-- The two alternatives require only a semantic disjunction. -/
def splitStep {p : Problem} {rank : Rank} (x : b.Node) (c d : Concept)
    (hc : b.Within rank p → c ∈ clos p) (hd : b.Within rank p → d ∈ clos p)
    (derive : ∀ (i : Interpretation datatypeMap) (env : b.Node → i.Object),
      p.Models i → b.Realizes i env → holds i (env x) c ∨ holds i (env x) d) :
    BlockedTransition rank p b where
  branches := [b.addLabel x c,b.addLabel x d]
  preserves := by
    rintro ⟨i,hm,env,he⟩
    rcases derive i env hm he with h | h
    · exact ⟨b.addLabel x c,by simp,i,hm,env,he.addLabel_realizes h⟩
    · exact ⟨b.addLabel x d,by simp,i,hm,env,he.addLabel_realizes h⟩
  within := by
    intro hw next hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact addLabel_within hw (hc hw)
    · exact addLabel_within hw (hd hw)
  root := by
    intro hr next hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> exact addLabel_mem.mpr (.inr hr)
  lift xs := {
    branches := [⟨b.addLabel x c,xs⟩,⟨b.addLabel x d,xs⟩]
    preserves := by
      rintro ⟨i,hm,e,he,hn⟩
      rcases derive i e hm he with h | h
      · exact ⟨⟨b.addLabel x c,xs⟩,by simp,i,hm,e,he.addLabel_realizes h,hn⟩
      · exact ⟨⟨b.addLabel x d,xs⟩,by simp,i,hm,e,he.addLabel_realizes h,hn⟩
    within := by
      intro hw next hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact addLabel_within hw (hc hw)
      · obtain rfl := List.mem_singleton.mp hn
        exact addLabel_within hw (hd hw)
    root := by
      intro hr next hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> exact addLabel_mem.mpr (.inr hr)
    protects := by
      intro next hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> exact ⟨none,⟨extensionWitnessMap id (fun h => h) rfl
        (fun h => h) (fun h => h)
        (fun h => addLabel_mem.mpr (.inr h)) (fun h => h)⟩⟩ }

def expandConj {p : Problem} {rank : Rank} {x : b.Node} {c d : Concept}
    (hl : .conj c d ∈ b.labels x) (keepLeft : Bool) :
    BlockedTransition rank p b := by
  cases keepLeft
  · exact labelStep x d (hc := by
      intro hw; exact clos_operands (hw.labels x hl) (by simp [operands]))
      (fun _ _ _ he => (he.labels x (.conj c d) hl).2)
  · exact labelStep x c (hc := by
      intro hw; exact clos_operands (hw.labels x hl) (by simp [operands]))
      (fun _ _ _ he => (he.labels x (.conj c d) hl).1)


def expandDisj {p : Problem} {rank : Rank} {x : b.Node} {c d : Concept}
    (hl : .disj c d ∈ b.labels x) : BlockedTransition rank p b :=
  splitStep x c d (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun _ _ _ he => he.labels x _ hl)

def expandTBox {p : Problem} {rank : Rank} (x : b.Node) {q : Inclusion}
    (hq : q ∈ p.tbox) : BlockedTransition rank p b := by
  have hs : q.sub ∈ seeds p := by
    have hm : q.sub ∈ p.tbox.flatMap (fun a => [a.sub,a.sup]) :=
      List.mem_flatMap.mpr ⟨q,hq,by simp⟩
    simp [seeds,hm]
  have ht : q.sup ∈ seeds p := by
    have hm : q.sup ∈ p.tbox.flatMap (fun a => [a.sub,a.sup]) :=
      List.mem_flatMap.mpr ⟨q,hq,by simp⟩
    simp [seeds,hm]
  apply splitStep x q.sub.dual q.sup (fun _ => seed_dual_mem_clos hs)
    (fun _ => seed_mem_clos ht)
  intro i env hm _
  by_cases h : holds i (env x) q.sub
  · exact .inr (hm.tbox q hq (env x) h)
  · exact .inl ((holds_dual i (env x) q.sub).mpr h)

def expandMaxQual {p : Problem} {rank : Rank} {x : b.Node} (y : b.Node) {n : Nat}
    {r : OrientedRole} {c : Concept} (hl : .max n r c ∈ b.labels x) :
    BlockedTransition rank p b := by
  apply splitStep y c c.dual
    (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
  intro i env _ _
  by_cases h : holds i (env y) c
  · exact .inl h
  · exact .inr ((holds_dual i (env y) c).mpr h)

def expandAll {p : Problem} {rank : Rank} {x y : b.Node} {r : OrientedRole} {c : Concept}
    (hl : .all r c ∈ b.labels x) (hedge : b.Edge r x y) : BlockedTransition rank p b :=
  labelStep y c (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun _ _ _ hr => hr.labels _ _ hl _ (hr.edges _ _ _ hedge))

def startGuard {p : Problem} {rank : Rank} (hi : p.SRIQInput rank) {x : b.Node}
    {r : OrientedRole} {c : Concept} (hl : .all r c ∈ b.labels x) : BlockedTransition rank p b :=
  guardStep x ⟨roleLanguage rank p r,c⟩ (fun hw => initial_guard_mem (hw.labels x hl))
    (fun _ _ hm he => initial_guard_sound hi.regular hm (he.labels _ _ hl))

def advanceGuard {p : Problem} {rank : Rank} {x y : b.Node} {r : OrientedRole}
    {g k : Guard} (hg : g ∈ b.guardLabels x) (he : b.Edge r x y) (hk : k ∈ g.advance r) :
    BlockedTransition rank p b :=
  guardStep y k (fun hw => guards_closed (hw.guards x hg) r hk)
    (fun _ _ _ hr => guard_step_sound (hr.guards _ _ hg) (hr.edges _ _ _ he) hk)

def acceptGuard {p : Problem} {rank : Rank} {x : b.Node} {g : Guard}
    (hg : g ∈ b.guardLabels x) (ha : g.state.nullable = true) : BlockedTransition rank p b :=
  labelStep x g.filler (fun hw => guard_filler_mem (hw.guards x hg))
    (fun _ _ _ hr => guard_accept_sound (hr.guards _ _ hg) ha)


private def sameMembers {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private theorem sameMembers_iff {α : Type} [DecidableEq α] {xs ys : List α} :
    sameMembers xs ys = true ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  simp only [sameMembers,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem]
  exact ⟨fun ⟨a,b⟩ x => ⟨a x,b x⟩,fun h => ⟨fun x => (h x).mp,fun x => (h x).mpr⟩⟩

def comparePair (b : BlockedBranch) (x y : b.Node) : Bool :=
  sameMembers (b.labels (b.parent x)) (b.labels (b.parent y)) &&
    sameMembers (b.labels x) (b.labels y) &&
    sameMembers (b.guardLabels (b.parent x)) (b.guardLabels (b.parent y)) &&
    sameMembers (b.guardLabels x) (b.guardLabels y) &&
    sameMembers (b.down x) (b.down y) && sameMembers (b.up x) (b.up y)

theorem comparePair_iff {x y : b.Node} : b.comparePair x y = true ↔ b.PairMatch x y := by
  simp only [comparePair,Bool.and_eq_true,sameMembers_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨a,c⟩,d⟩,e⟩,f⟩,g⟩
    refine ⟨a,c,d,e,?_⟩
    rintro ⟨r,_ | _⟩
    · exact f r
    · exact g r
  · intro h
    exact ⟨⟨⟨⟨⟨h.parentLabels,h.labels⟩,h.parentGuards⟩,h.guards⟩,
      fun r => h.roles (r,false)⟩,fun r => h.roles (r,true)⟩

private def candidate (b : BlockedBranch) (x : b.Node) : Option b.Node :=
  (b.ancestors x).find? (fun a => a != 0 && b.comparePair x a)

private theorem candidate_some {x a : b.Node} (h : b.candidate x = some a) :
    b.Anc a x ∧ a ≠ 0 ∧ b.PairMatch x a := by
  have hc : (a != 0 && b.comparePair x a) = true := List.find?_some (p := fun n => n != 0 && b.comparePair x n) h
  simp only [Bool.and_eq_true,bne_iff_ne,comparePair_iff] at hc
  exact ⟨mem_ancestors.mp (List.mem_of_find?_eq_some h),hc⟩

private theorem candidate_none {x a : b.Node} (h : b.candidate x = none) (ha : b.Anc a x)
    (hn : a ≠ 0) : ¬ b.PairMatch x a := by
  have ht := List.find?_eq_none.mp h a (mem_ancestors.mpr ha)
  intro hm
  simp [hn,comparePair_iff.mpr hm] at ht

private def hasCandidate (b : BlockedBranch) (x : b.Node) : Bool :=
  (b.candidate x).isSome

private def hasEarlier (b : BlockedBranch) (x : b.Node) : Bool :=
  (b.ancestors x).any b.hasCandidate

private theorem earlier_iff {x : b.Node} :
    b.hasEarlier x = true ↔ ∃ a, b.Anc a x ∧ b.hasCandidate a = true := by
  simp only [hasEarlier,List.any_eq_true,mem_ancestors]

private theorem earlier_false {x : b.Node} (h : b.hasEarlier x = false) {a : b.Node}
    (ha : b.Anc a x) : b.candidate a = none := by
  cases e : b.candidate a with
  | none => rfl
  | some y =>
    have ht := earlier_iff.mpr ⟨a,ha,by simp [hasCandidate,e]⟩
    rw [h] at ht
    contradiction

/-- An actual blocking pointer is installed at the first repetition on a
root path. Nodes beyond it are indirectly blocked. -/
def reblock (b : BlockedBranch) : BlockedBranch :=
  { b with blockedBy := fun x => if b.hasEarlier x then none else b.candidate x }

theorem reblock_sat_iff (p : Problem) : b.reblock.Sat p ↔ b.Sat p :=
  ⟨fun ⟨i,hm,env,he⟩ => ⟨i,hm,env,he.labels,he.edges,he.guards,he.unequal⟩,
   fun ⟨i,hm,env,he⟩ => ⟨i,hm,env,he.labels,he.edges,he.guards,he.unequal⟩⟩

theorem reblock_within {p : Problem} {rank : Rank} (h : b.Within rank p) :
    b.reblock.Within rank p := ⟨h.labels,h.guards,h.roles⟩

private theorem anc_from_reblock {x a : b.Node} (h : b.reblock.Anc a x) : b.Anc a x :=
  match h with
  | .parent hc => .parent hc
  | .step ha hc => .step (anc_from_reblock ha) hc
termination_by structural h

private theorem anc_to_reblock {x a : b.Node} (h : b.Anc a x) : b.reblock.Anc a x :=
  match h with
  | .parent hc => .parent hc
  | .step ha hc => .step (anc_to_reblock ha) hc
termination_by structural h

private theorem same_anc_reblock {x a : b.Node} : b.reblock.Anc a x ↔ b.Anc a x :=
  ⟨anc_from_reblock,anc_to_reblock⟩

theorem reblock_valid (b : BlockedBranch) : b.reblock.BlockingValid := by
  constructor
  intro x y he
  change (if b.hasEarlier x then none else b.candidate x) = some y at he
  cases hb : b.hasEarlier x with
  | true => simp [hb] at he
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at he
    have ⟨ha,hn,hm⟩ := candidate_some he
    have noAt (a : b.Node) (ha : b.Anc a x) : b.reblock.blockedBy a = none := by
      change (if b.hasEarlier a then none else b.candidate a) = none
      simp [earlier_false hb ha]
    have noAnc (a : b.Node) (h : ∀ z, b.Anc z a → b.Anc z x) :
        ¬ b.reblock.IndirectlyBlocked a := by
      rintro ⟨z,hz,hb⟩
      simp [DirectlyBlocked,noAt z (h z (same_anc_reblock.mp hz))] at hb
    refine ⟨same_anc_reblock.mpr ha,hn,⟨noAt y ha,noAnc y (fun _ hz => hz.trans ha)⟩,
      noAnc x (fun _ hz => hz),?_⟩
    exact ⟨hm.parentLabels,hm.labels,hm.parentGuards,hm.guards,hm.roles⟩

private theorem candidate_exists_front {x : b.Node}
    (h : b.hasCandidate x = true) :
    ∃ a, (a = x ∨ b.Anc a x) ∧ b.reblock.DirectlyBlocked a := by
  cases he : b.hasEarlier x with
  | false => exact ⟨x,.inl rfl,by simpa [DirectlyBlocked,reblock,he,hasCandidate] using h⟩
  | true =>
    obtain ⟨a,ha,hh⟩ := earlier_iff.mp he
    obtain ⟨z,hz,hd⟩ := candidate_exists_front hh
    exact ⟨z,.inr (hz.elim (· ▸ ha) (·.trans ha)),hd⟩
termination_by x.val
decreasing_by exact ha.lt

theorem unblocked_avoids_pair {x a : b.Node} (hu : b.reblock.Unblocked x) (ha : b.Anc a x)
    (hn : a ≠ 0) : ¬ b.PairMatch x a := by
  cases h : b.candidate x with
  | none => exact candidate_none h ha hn
  | some z =>
    obtain ⟨y,hy,hd⟩ := candidate_exists_front (x := x) (by simp [hasCandidate,h])
    rcases hy with rfl | hy
    · simp [DirectlyBlocked,hu.1] at hd
    · exact (hu.2 ⟨y,same_anc_reblock.mpr hy,hd⟩).elim

theorem unblocked_ancestor {x a : b.Node} (hx : b.Unblocked x) (ha : b.Anc a x) :
    b.Unblocked a := by
  constructor
  · cases h : b.blockedBy a with
    | none => rfl
    | some y => exact (hx.2 ⟨a,ha,by simp [DirectlyBlocked,h]⟩).elim
  · rintro ⟨z,hz,hb⟩
    exact hx.2 ⟨z,hz.trans ha,hb⟩


private inductive PairToken where
  | parent (label : Concept ⊕ Guard)
  | child (label : Concept ⊕ Guard)
  | down (role : IRI)
  | up (role : IRI)
  deriving DecidableEq

private def pairAlphabet (rank : Rank) (p : Problem) : List PairToken :=
  (alphabet rank p).map .parent ++ (alphabet rank p).map .child ++
    (roleNames p).map .down ++ (roleNames p).map .up

private def observed (b : BlockedBranch) (x : b.Node) : PairToken → Bool
  | .parent (.inl c) => (b.labels (b.parent x)).contains c
  | .parent (.inr g) => (b.guardLabels (b.parent x)).contains g
  | .child (.inl c) => (b.labels x).contains c
  | .child (.inr g) => (b.guardLabels x).contains g
  | .down r => (b.down x).contains r
  | .up r => (b.up x).contains r

private def signature (b : BlockedBranch) (rank : Rank) (p : Problem) (x : b.Node) : List PairToken :=
  (pairAlphabet rank p).filter (b.observed x)

private theorem observed_in_alphabet {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {x : b.Node} {t : PairToken} (h : b.observed x t = true) : t ∈ pairAlphabet rank p := by
  cases t with
  | parent label =>
    apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ?_)))
    cases label with
    | inl c => exact List.mem_append_left _ (List.mem_map_of_mem (hw.labels _ (List.contains_iff_mem.mp h)))
    | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (hw.guards _ (List.contains_iff_mem.mp h)))
  | child label =>
    apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ?_)))
    cases label with
    | inl c => exact List.mem_append_left _ (List.mem_map_of_mem (hw.labels _ (List.contains_iff_mem.mp h)))
    | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (hw.guards _ (List.contains_iff_mem.mp h)))
  | down r =>
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem ((hw.roles x).1 (List.contains_iff_mem.mp h))))
  | up r =>
    exact List.mem_append_right _ (List.mem_map_of_mem ((hw.roles x).2.1 (List.contains_iff_mem.mp h)))

private theorem signature_iff {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {x : b.Node} {t : PairToken} :
    t ∈ b.signature rank p x ↔ b.observed x t = true :=
  ⟨fun h => (List.mem_filter.mp h).2,fun h => List.mem_filter.mpr ⟨observed_in_alphabet hw h,h⟩⟩

private theorem signature_eq_match {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {x y : b.Node} (he : b.signature rank p x = b.signature rank p y) : b.PairMatch x y := by
  have matchAt (t : PairToken) : b.observed x t = true ↔ b.observed y t = true :=
    (signature_iff hw).symm.trans (he ▸ signature_iff hw)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro c; simpa only [observed,List.contains_iff_mem] using matchAt (.parent (.inl c))
  · intro c; simpa only [observed,List.contains_iff_mem] using matchAt (.child (.inl c))
  · intro g; simpa only [observed,List.contains_iff_mem] using matchAt (.parent (.inr g))
  · intro g; simpa only [observed,List.contains_iff_mem] using matchAt (.child (.inr g))
  · rintro ⟨r,_ | _⟩
    · change r ∈ b.down x ↔ r ∈ b.down y
      simpa only [observed,List.contains_iff_mem] using matchAt (.down r)
    · change r ∈ b.up x ↔ r ∈ b.up y
      simpa only [observed,List.contains_iff_mem] using matchAt (.up r)

/-- Root-to-node depth counts incoming edges. Only nonroot nodes have a
pairwise blocking signature, hence the root is omitted from this list. -/
private def nonrootPath (b : BlockedBranch) (x : b.Node) : List b.Node :=
  if _h : x = 0 then [] else x :: b.nonrootPath (b.parent x)
termination_by x.val
decreasing_by exact b.parent_lt x _h

private theorem nonroot_length (x : b.Node) : (b.nonrootPath x).length = b.depth x := by
  rw [nonrootPath,depth,ancestors]
  split
  · simp_all
  · rename_i hx
    simp only [List.length_cons]
    exact congrArg Nat.succ (nonroot_length (b.parent x))
termination_by x.val
decreasing_by apply b.parent_lt; assumption

private theorem mem_nonrootPath {x a : b.Node} (h : a ∈ b.nonrootPath x) :
    a ≠ 0 ∧ (a = x ∨ b.Anc a x) := by
  rw [nonrootPath] at h
  split at h
  · exact (List.not_mem_nil h).elim
  · rename_i hx
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨hx,.inl rfl⟩
    · have ⟨hn,ha⟩ := mem_nonrootPath h
      exact ⟨hn,.inr ((Anc.child_iff ⟨hx,rfl⟩).mpr ha)⟩
termination_by x.val
decreasing_by apply b.parent_lt; assumption

private theorem distinct_signatures {rank : Rank} {p : Problem} (hw : b.Within rank p)
    (x : b.Node) (hu : b.reblock.Unblocked x) :
    ((b.nonrootPath x).map (b.signature rank p)).Nodup := by
  rw [nonrootPath]
  split
  · simp
  · rename_i hx
    simp only [List.map_cons,List.nodup_cons]
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := List.mem_map.mp h
      have ⟨hyn,hyp⟩ := mem_nonrootPath hy
      have hanc : b.Anc y x := (Anc.child_iff ⟨hx,rfl⟩).mpr hyp
      exact unblocked_avoids_pair hu hanc hyn (signature_eq_match hw he.symm)
    · exact distinct_signatures hw (b.parent x)
        (unblocked_ancestor hu (anc_to_reblock (.parent ⟨hx,rfl⟩)))
termination_by x.val
decreasing_by apply b.parent_lt; assumption

/-- Two mixed vertex labels and two directed role sets determine one pairwise
signature. The bound counts all subsets of their tagged alphabet. -/
def maxDepth (rank : Rank) (p : Problem) : Nat :=
  2 ^ (2 * (alphabet rank p).length + 2 * (roleNames p).length)

theorem unblocked_depth_le {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {x : b.Node} (hu : b.reblock.Unblocked x) : b.depth x ≤ maxDepth rank p := by
  have hsubset : (b.nonrootPath x).map (b.signature rank p) ⊆ subsets (pairAlphabet rank p) := by
    intro row hm
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    exact filter_mem_subsets _ _
  have hle := (distinct_signatures hw x hu).length_le_of_subset hsubset
  rw [List.length_map,nonroot_length,subsets_length] at hle
  have sizes : (pairAlphabet rank p).length =
      2 * (alphabet rank p).length + 2 * (roleNames p).length := by
    simp only [pairAlphabet,List.length_append,List.length_map]
    omega
  rwa [sizes] at hle

theorem blocked_of_depth_gt {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {x : b.Node} (h : maxDepth rank p < b.depth x) :
    b.reblock.DirectlyBlocked x ∨ b.reblock.IndirectlyBlocked x := by
  by_cases hi : b.reblock.IndirectlyBlocked x
  · exact .inr hi
  · cases he : b.reblock.blockedBy x with
    | none => exact (Nat.not_lt_of_ge (unblocked_depth_le hw ⟨he,hi⟩) h).elim
    | some y => exact .inl (by simp [DirectlyBlocked,he])


private abbrev Extended (b : BlockedBranch) (n : Nat) := Fin (b.size + n + 1)

private def oldNode (n : Nat) (x : b.Node) : Extended b n := ⟨x.val,by have := x.isLt; omega⟩

private def newNode (b : BlockedBranch) {n : Nat} (x : Fin n) : Extended b n :=
  ⟨b.size + 1 + x.val,by have := x.isLt; omega⟩

private theorem oldNode_inj {n : Nat} {x y : b.Node} (h : oldNode n x = oldNode n y) : x = y :=
  Fin.ext (congrArg (fun z : Extended b n => z.val) h)

private theorem oldNode_eq_zero {n : Nat} {x : b.Node} : oldNode n x = 0 ↔ x = 0 := by
  exact ⟨fun h => Fin.ext (congrArg (fun z : Extended b n => z.val) h),
    fun h => Fin.ext (congrArg (fun z : b.Node => z.val) h)⟩

private theorem newNode_ne_zero {n : Nat} (x : Fin n) : b.newNode x ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change b.size + 1 + x.val = 0 at hv
  omega

private theorem old_ne_new {n : Nat} (x : b.Node) (y : Fin n) : oldNode n x ≠ b.newNode y := by
  intro h
  have hv := congrArg Fin.val h
  change x.val = b.size + 1 + y.val at hv
  have hlt := x.isLt
  omega

private def onExtended {α : Type} {n : Nat} (old : b.Node → α) (new : Fin n → α)
    (x : Extended b n) : α :=
  if h : x.val < b.size + 1 then old ⟨x.val,h⟩
  else new ⟨x.val - (b.size + 1),by have := x.isLt; omega⟩

@[simp] private theorem onExtended_old {α : Type} {n : Nat} (old : b.Node → α)
    (new : Fin n → α) (x : b.Node) : onExtended old new (oldNode n x) = old x := by
  simp [onExtended,oldNode,x.isLt]

@[simp] private theorem onExtended_new {α : Type} {n : Nat} (old : b.Node → α)
    (new : Fin n → α) (x : Fin n) : onExtended old new (b.newNode x) = new x := by
  unfold onExtended
  have hn : ¬ (b.newNode x).val < b.size + 1 := by
    change ¬ b.size + 1 + x.val < b.size + 1
    omega
  rw [dite_eq_right hn]
  congr 1
  apply Fin.ext
  change b.size + 1 + x.val - (b.size + 1) = x.val
  omega

private theorem extended_cases {n : Nat} (x : Extended b n) :
    (∃ y : b.Node, x = oldNode n y) ∨ ∃ y : Fin n, x = b.newNode y := by
  by_cases h : x.val < b.size + 1
  · exact .inl ⟨⟨x.val,h⟩,rfl⟩
  · have hlt := x.isLt
    refine .inr ⟨⟨x.val - (b.size + 1),by omega⟩,Fin.ext ?_⟩
    change x.val = b.size + 1 + (x.val - (b.size + 1))
    omega

private def freshPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun x =>
    ((List.finRange n).filter (· != x)).map fun y => (x,y)

private theorem freshPairs_ne {n : Nat} {x y : Fin n} (h : (x,y) ∈ freshPairs n) : x ≠ y := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp h
  obtain ⟨c,hc,he⟩ := List.mem_map.mp ha
  cases he
  exact Ne.symm (bne_iff_ne.mp (List.mem_filter.mp hc).2)

/-- Allocate a group of children with an explicit inequality for every pair.
Every new node has the same designated parent. Existing node indices and
labels are retained, and blocking pointers are recomputed by the caller. -/
def appendChildren (b : BlockedBranch) (n : Nat) (x : b.Node) (r : OrientedRole)
    (c : Concept) : BlockedBranch where
  size := b.size + n
  parent := onExtended (fun y => oldNode n (b.parent y)) (fun _ => oldNode n x)
  parent_lt := by
    intro y hy
    rcases extended_cases y with ⟨w,rfl⟩ | ⟨w,rfl⟩
    · rw [onExtended_old]
      exact b.parent_lt w (fun h => hy (oldNode_eq_zero.mpr h))
    · rw [onExtended_new]
      change x.val < b.size + 1 + w.val
      have hx := x.isLt
      omega
  labels := onExtended b.labels (fun _ => [c])
  guardLabels := onExtended b.guardLabels (fun _ => [])
  down := onExtended b.down (fun _ => if r.2 then [] else [r.1])
  up := onExtended b.up (fun _ => if r.2 then [r.1] else [])
  loops := onExtended b.loops (fun _ => [])
  unequal := b.unequal.map (fun (u,v) => (oldNode n u,oldNode n v)) ++
    (freshPairs n).map (fun (u,v) => (b.newNode u,b.newNode v))
  unequal_siblings := by
    intro y z h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨⟨u,v⟩,huv,he⟩ := List.mem_map.mp h
      cases he
      have ⟨h₁,h₂,h₃⟩ := b.unequal_siblings u v huv
      exact ⟨(not_congr oldNode_eq_zero).mpr h₁,(not_congr oldNode_eq_zero).mpr h₂,by simp [h₃]⟩
    · obtain ⟨⟨u,v⟩,_,he⟩ := List.mem_map.mp h
      cases he
      exact ⟨newNode_ne_zero u,newNode_ne_zero v,by simp⟩
  blockedBy := fun _ => none

private theorem appendChild_old {n : Nat} {x a z : b.Node} {r : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Child (oldNode n a) (oldNode n z) ↔ b.Child a z := by
  change oldNode n z ≠ 0 ∧
    onExtended (fun y => oldNode n (b.parent y)) (fun _ => oldNode n x) (oldNode n z) =
      oldNode n a ↔ _
  rw [onExtended_old]
  exact and_congr (not_congr oldNode_eq_zero) ⟨oldNode_inj,congrArg (oldNode n)⟩

private theorem appendChild_new {n : Nat} {x a : b.Node} {z : Fin n}
    {r : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Child (oldNode n a) (b.newNode z) ↔ a = x := by
  change b.newNode z ≠ 0 ∧
    onExtended (fun y => oldNode n (b.parent y)) (fun _ => oldNode n x) (b.newNode z) =
      oldNode n a ↔ _
  rw [onExtended_new]
  exact ⟨fun h => (oldNode_inj h.2).symm,fun h => ⟨newNode_ne_zero _,congrArg (oldNode n) h.symm⟩⟩

private theorem fresh_has_no_child {n : Nat} {x : b.Node} {y : Fin n} {z : Extended b n}
    {r : OrientedRole} {c : Concept} : ¬ (b.appendChildren n x r c).Child (b.newNode y) z := by
  intro h
  rcases extended_cases z with ⟨z,rfl⟩ | ⟨z,rfl⟩
  · have hh := h.2
    change onExtended (fun u => oldNode n (b.parent u)) (fun _ => oldNode n x) (oldNode n z)
      = b.newNode y at hh
    rw [onExtended_old] at hh
    exact old_ne_new _ _ hh
  · have hh := h.2
    change onExtended (fun u => oldNode n (b.parent u)) (fun _ => oldNode n x) (b.newNode z)
      = b.newNode y at hh
    rw [onExtended_new] at hh
    exact old_ne_new _ _ hh

private theorem appendEdge_old {n : Nat} {x a z : b.Node} {r s : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Edge s (oldNode n a) (oldNode n z) ↔ b.Edge s a z := by
  unfold Edge
  rw [appendChild_old,appendChild_old]
  simp only [Down,appendChildren,onExtended_old]
  exact or_congr (and_congr ⟨oldNode_inj,congrArg (oldNode n)⟩ Iff.rfl) Iff.rfl

private theorem appendEdge_new {n : Nat} {x a : b.Node} {z : Fin n}
    {r s : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Edge s (oldNode n a) (b.newNode z) ↔ a = x ∧ s = r := by
  unfold Edge
  rw [appendChild_new]
  have hn := fresh_has_no_child (x := x) (y := z) (z := oldNode n a) (r := r) (c := c)
  have hne := old_ne_new (b := b) a z
  rw [or_iff_right (fun h => hne h.1), or_iff_left (fun h => hn h.1)]
  simp only [Down,appendChildren,onExtended_new]
  apply and_congr_right
  intro _
  rcases s with ⟨s,_ | _⟩ <;> rcases r with ⟨r,_ | _⟩ <;> simp

private theorem appendEdge_fresh_fresh {n : Nat} {x : b.Node} {a z : Fin n}
    {r s : OrientedRole} {c : Concept} :
    ¬ (b.appendChildren n x r c).Edge s (b.newNode a) (b.newNode z) := by
  rintro (⟨_,hl⟩ | ⟨he,_⟩ | ⟨he,_⟩)
  · simp [appendChildren,onExtended_new] at hl
  · exact fresh_has_no_child he
  · exact fresh_has_no_child he

private theorem role_in_closure {p : Problem} {goal : Concept} (hm : goal ∈ clos p)
    {r : IRI} (hr : r ∈ conceptRoles goal) : r ∈ roleNames p := by
  have hs : r ∈ (clos p).flatMap conceptRoles := List.mem_flatMap.mpr ⟨goal,hm,hr⟩
  simp [roleNames,hs]

theorem appendChildren_within {p : Problem} {rank : Rank} (hw : b.Within rank p) (n : Nat)
    (x : b.Node) (r : OrientedRole) (c : Concept) (hc : c ∈ clos p) (hr : r.1 ∈ roleNames p) :
    (b.appendChildren n x r c).Within rank p := by
  constructor
  · intro y d hd
    change d ∈ onExtended b.labels (fun _ => [c]) y at hd
    rcases extended_cases y with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · rw [onExtended_old] at hd
      exact hw.labels z hd
    · rw [onExtended_new] at hd
      exact List.mem_singleton.mp hd ▸ hc
  · intro y g hg
    change g ∈ onExtended b.guardLabels (fun _ => []) y at hg
    rcases extended_cases y with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · rw [onExtended_old] at hg
      exact hw.guards z hg
    · rw [onExtended_new] at hg
      exact (List.not_mem_nil hg).elim
  · intro y
    rcases extended_cases y with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · simpa only [appendChildren,onExtended_old] using hw.roles z
    · simp only [appendChildren,onExtended_new]
      have hs : [r.1] ⊆ roleNames p := fun _ ha => List.mem_singleton.mp ha ▸ hr
      cases r.2 <;> simp_all

private theorem Realizes.append_realizes {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (he : b.Realizes i env) {x : b.Node} {r : OrientedRole} {c : Concept} {n : Nat}
    (witness : Fin n → i.Object) (inj : ∀ a d, witness a = witness d → a = d)
    (sat : ∀ a, holdsOriented i r (env x) (witness a) ∧ holds i (witness a) c) :
    (b.appendChildren n x r c).Realizes i (onExtended env witness) := by
  constructor
  case labels =>
    intro y d hd
    rcases extended_cases y with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · simp only [appendChildren,onExtended_old] at hd ⊢
      exact he.labels z d hd
    · simp only [appendChildren,onExtended_new] at hd ⊢
      exact List.mem_singleton.mp hd ▸ (sat z).2
  case guards =>
    intro y g hg
    rcases extended_cases y with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · simp only [appendChildren,onExtended_old] at hg ⊢
      exact he.guards z g hg
    · simp [appendChildren,onExtended_new] at hg
  case unequal =>
    intro y z h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨⟨a,d⟩,had,h⟩ := List.mem_map.mp h
      cases h
      simpa only [onExtended_old] using he.unequal a d had
    · obtain ⟨⟨a,d⟩,had,h⟩ := List.mem_map.mp h
      cases h
      simp only [onExtended_new]
      exact fun h => freshPairs_ne had (inj _ _ h)
  case edges =>
    intro s y z h
    rcases extended_cases y with ⟨y,rfl⟩ | ⟨y,rfl⟩ <;>
      rcases extended_cases z with ⟨z,rfl⟩ | ⟨z,rfl⟩
    · simp only [onExtended_old]
      exact he.edges s y z (appendEdge_old.mp h)
    · obtain ⟨rfl,rfl⟩ := appendEdge_new.mp h
      simpa only [onExtended_old,onExtended_new] using (sat z).1
    · apply (orientation_flip i s _ _).mp
      obtain ⟨hy,hr⟩ := appendEdge_new.mp ((edge_converse _ s _ _).mpr h)
      simp only [onExtended_old,onExtended_new]
      rw [hr,hy]
      exact (sat y).1
    · exact (appendEdge_fresh_fresh h).elim

private theorem realize_count {α : Type} {n : Nat} {q : α → Prop} (h : AtLeast n q) :
    ∃ f : Fin n → α, (∀ i j, f i = f j → i = j) ∧ ∀ i, q (f i) := by
  obtain ⟨xs,hlen,hn,hx⟩ := h
  have idx (i : Fin n) : i.val < xs.length := hlen.symm ▸ i.isLt
  refine ⟨fun i => xs[i.val]'(idx i),?_,fun i => hx _ (List.getElem_mem (idx i))⟩
  intro i j hj
  exact Fin.ext (hn.eq_of_getElem_eq (idx i) (idx j) hj)

def ConstrainedTree.appendFresh (s : ConstrainedTree) (x : s.tree.Node) (r : OrientedRole)
    (c : Concept) (n : Nat) : ConstrainedTree :=
  ⟨s.tree.appendChildren n x r c,s.extraUnequal.map (fun (a,d) => (oldNode n a,oldNode n d))⟩

private def appendFresh_map (s : ConstrainedTree) (x : s.tree.Node) (r : OrientedRole)
    (c : Concept) (n : Nat) : WitnessMap s (s.appendFresh x r c n) none := by
  apply extensionWitnessMap (oldNode n) oldNode_inj (oldNode_eq_zero.mpr rfl)
    (fun h => appendChild_old.mpr h) (fun h => appendEdge_old.mpr h)
  · intro y h hmem
    change h ∈ onExtended s.tree.labels (fun _ => [c]) (oldNode n y)
    rwa [onExtended_old]
  · intro y z h
    have transport {a d : s.tree.Node}
        (h : (a,d) ∈ s.tree.unequal ∨ (a,d) ∈ s.extraUnequal) :
        (oldNode n a,oldNode n d) ∈ (s.appendFresh x r c n).tree.unequal ∨
        (oldNode n a,oldNode n d) ∈ (s.appendFresh x r c n).extraUnequal := by
      rcases h with h | h
      · exact .inl (List.mem_append_left _ (List.mem_map_of_mem h))
      · exact .inr (List.mem_map_of_mem h)
    exact h.elim (fun h => .inl (transport h)) (fun h => .inr (transport h))

/-- Allocation installs a protected group of the requested size, including
the explicit inequality for every pair of distinct fresh children. -/
theorem ConstrainedTree.appendFresh_protected (s : ConstrainedTree) (x : s.tree.Node)
    (r : OrientedRole) (c : Concept) (n : Nat) :
    (s.appendFresh x r c n).ProtectedWitnesses (oldNode n x) r c n := by
  let fresh (k : Fin n) : (s.appendFresh x r c n).tree.Node := s.tree.newNode k
  have inj {a d : Fin n} (h : fresh a = fresh d) : a = d := by
    have eq := congrArg Fin.val h
    change s.tree.size + 1 + a.val = s.tree.size + 1 + d.val at eq
    exact Fin.ext (by omega)
  have apart {a d : Fin n} (h : a ≠ d) : (a,d) ∈ freshPairs n := by
    apply List.mem_flatMap.mpr
    refine ⟨a,List.mem_finRange a,List.mem_map.mpr ⟨d,?_ ,rfl⟩⟩
    exact List.mem_filter.mpr ⟨List.mem_finRange d,bne_iff_ne.mpr (Ne.symm h)⟩
  have nd := List.nodup_finRange n
  refine ⟨(List.finRange n).map fresh,by simp, List.pairwise_map.mpr (nd.imp (fun h e => h (inj e))),
    List.pairwise_map.mpr (nd.imp (fun h => .inl (.inl
      (List.mem_append_right _ (List.mem_map_of_mem (apart h)))))),?_⟩
  intro y hm
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hm
  refine ⟨appendEdge_new.mpr ⟨rfl,rfl⟩,?_⟩
  change c ∈ onExtended s.tree.labels (fun _ => [c]) (s.tree.newNode k)
  rw [onExtended_new]
  exact List.mem_singleton_self c

def generate {p : Problem} {rank : Rank} (x : b.Node) (r : OrientedRole) (c : Concept) (n : Nat)
    (hc : b.Within rank p → c ∈ clos p) (hr : b.Within rank p → r.1 ∈ roleNames p)
    (ensure : ∀ (i : Interpretation datatypeMap) (env : b.Node → i.Object),
      b.Realizes i env → AtLeast n (fun y => holdsOriented i r (env x) y ∧ holds i y c)) :
    BlockedTransition rank p b where
  branches := [b.appendChildren n x r c]
  preserves := by
    rintro ⟨i,hm,env,he⟩
    obtain ⟨w,hDistinct,hw⟩ := realize_count (ensure i env he)
    exact ⟨_,List.mem_singleton_self _,i,hm,_,he.append_realizes w hDistinct hw⟩
  within := by
    intro hw y hy
    obtain rfl := List.mem_singleton.mp hy
    exact appendChildren_within hw n x r c (hc hw) (hr hw)
  root := by
    intro hroot next hn
    obtain rfl := List.mem_singleton.mp hn
    have e : oldNode n (0 : b.Node) = 0 := oldNode_eq_zero.mpr rfl
    change p.root ∈ onExtended b.labels (fun _ => [c]) (0 : Extended b n)
    rw [←e,onExtended_old]
    exact hroot
  lift xs := {
    branches := [ConstrainedTree.appendFresh ⟨b,xs⟩ x r c n]
    preserves := by
      rintro ⟨i,hm,e,he,hn⟩
      obtain ⟨w,hw,hs⟩ := realize_count (ensure i e he)
      refine ⟨_,List.mem_singleton_self _,i,hm,_,he.append_realizes w hw hs,?_⟩
      intro a d h
      obtain ⟨⟨a',d'⟩,hin,hh⟩ := List.mem_map.mp h
      cases hh
      simpa only [onExtended_old] using hn a' d' hin
    within := by
      intro hw next hn
      obtain rfl := List.mem_singleton.mp hn
      exact appendChildren_within hw n x r c (hc hw) (hr hw)
    root := by
      intro hroot next hn
      obtain rfl := List.mem_singleton.mp hn
      have e : oldNode n (0 : b.Node) = 0 := oldNode_eq_zero.mpr rfl
      change p.root ∈ onExtended b.labels (fun _ => [c]) (0 : Extended b n)
      rw [←e,onExtended_old]
      exact hroot
    protects := by
      intro next hn
      obtain rfl := List.mem_singleton.mp hn
      exact ⟨none,⟨appendFresh_map ⟨b,xs⟩ x r c n⟩⟩ }

def generateSome {p : Problem} {rank : Rank} {x : b.Node} {r : OrientedRole} {c : Concept}
    (hl : .some r c ∈ b.labels x) : BlockedTransition rank p b :=
  generate x r c 1 (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun hw => role_in_closure (hw.labels x hl) (by simp [conceptRoles]))
    (by
      intro i env he
      obtain ⟨y,hy⟩ := he.labels x _ hl
      exact ⟨[y],rfl,by simp,by simpa⟩)

def generateMin {p : Problem} {rank : Rank} {x : b.Node} {r : OrientedRole} {c : Concept} {n : Nat}
    (hl : .min n r c ∈ b.labels x) : BlockedTransition rank p b :=
  generate x r c n (fun hw => clos_operands (hw.labels x hl) (by simp [operands]))
    (fun hw => role_in_closure (hw.labels x hl) (by simp [conceptRoles]))
    (fun _ _ he => he.labels x _ hl)


def Local (b : BlockedBranch) (x y : b.Node) : Prop :=
  x = y ∨ b.Child x y ∨ b.Child y x

private instance (x y : b.Node) : Decidable (b.Child x y) :=
  inferInstanceAs (Decidable (y ≠ 0 ∧ b.parent y = x))

theorem Edge.local {r : OrientedRole} {x y : b.Node} (h : b.Edge r x y) : b.Local x y :=
  h.elim (fun a => .inl a.1) (fun a => a.elim (fun c => .inr (.inl c.1)) (fun c => .inr (.inr c.1)))

def addNamedEdge (b : BlockedBranch) (r : IRI) (x y : b.Node) : BlockedBranch :=
  { b with
    loops := fun z => if z = x ∧ z = y then addOnce r (b.loops z) else b.loops z
    down := fun z => if b.Child x z ∧ z = y then addOnce r (b.down z) else b.down z
    up := fun z => if b.Child y z ∧ z = x then addOnce r (b.up z) else b.up z
    blockedBy := fun _ => none }

private theorem mem_addWhere {α : Type} [DecidableEq α] {a d : α} {xs : List α}
    (h : Prop) [Decidable h] :
    d ∈ (if h then addOnce a xs else xs) ↔ (h ∧ d = a) ∨ d ∈ xs := by
  by_cases hh : h <;> simp [hh,mem_addOnce]

private theorem addNamedEdge_iff {r s : IRI} {x y a c : b.Node} :
    (b.addNamedEdge r x y).Edge (s,false) a c ↔
      b.Edge (s,false) a c ∨ (s = r ∧ a = x ∧ c = y ∧ b.Local x y) := by
  change (a = c ∧ s ∈ (if a = x ∧ a = y then addOnce r (b.loops a) else b.loops a) ∨
    (b.Child a c ∧ s ∈ (if b.Child x c ∧ c = y then addOnce r (b.down c) else b.down c)) ∨
    (b.Child c a ∧ s ∈ (if b.Child y a ∧ a = x then addOnce r (b.up a) else b.up a))) ↔
    (a = c ∧ s ∈ b.loops a ∨ (b.Child a c ∧ s ∈ b.down c) ∨
      (b.Child c a ∧ s ∈ b.up a)) ∨ (s = r ∧ a = x ∧ c = y ∧ b.Local x y)
  simp only [mem_addWhere,Local]
  constructor
  · rintro (⟨h,⟨⟨hx,hy⟩,hr⟩ | he⟩ | ⟨h,⟨⟨hp,hy⟩,hr⟩ | he⟩ |
      ⟨h,⟨⟨hp,hx⟩,hr⟩ | he⟩)
    · exact .inr ⟨hr,hx,h.symm.trans hy,hx.symm.trans hy |> Or.inl⟩
    · exact .inl (.inl ⟨h,he⟩)
    · exact .inr ⟨hr,h.2.symm.trans hp.2,hy,.inr (.inl (hy ▸ hp))⟩
    · exact .inl (.inr (.inl ⟨h,he⟩))
    · exact .inr ⟨hr,hx,h.2.symm.trans hp.2,.inr (.inr (hx ▸ hp))⟩
    · exact .inl (.inr (.inr ⟨h,he⟩))
  · rintro ((⟨h,he⟩ | ⟨h,he⟩ | ⟨h,he⟩) | ⟨rfl,rfl,rfl,hl⟩)
    · exact .inl ⟨h,.inr he⟩
    · exact .inr (.inl ⟨h,.inr he⟩)
    · exact .inr (.inr ⟨h,.inr he⟩)
    · rcases hl with h | h | h
      · exact .inl ⟨h,.inl ⟨⟨rfl,h⟩,rfl⟩⟩
      · exact .inr (.inl ⟨h,.inl ⟨⟨h,rfl⟩,rfl⟩⟩)
      · exact .inr (.inr ⟨h,.inl ⟨⟨h,rfl⟩,rfl⟩⟩)

def addEdge (b : BlockedBranch) (r : OrientedRole) (x y : b.Node) : BlockedBranch :=
  b.addNamedEdge r.1 (if r.2 then y else x) (if r.2 then x else y)

private theorem addEdge_retains {r s : OrientedRole} {x y a c : b.Node}
    (he : b.Edge s a c) : (b.addEdge r x y).Edge s a c := by
  rcases s with ⟨s,_ | _⟩
  · exact addNamedEdge_iff.mpr (.inl he)
  · apply ((b.addEdge r x y).edge_converse (s,false) c a).mpr
    exact addNamedEdge_iff.mpr (.inl ((b.edge_converse (s,false) c a).mp he))

private theorem Realizes.addNamedEdge {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hre : b.Realizes i env) {r : IRI} {x y : b.Node} (he : i.objectProperties r (env x) (env y)) :
    (b.addNamedEdge r x y).Realizes i env := by
  refine ⟨hre.labels,?_,hre.guards,hre.unequal⟩
  have forward : ∀ s a c, (b.addNamedEdge r x y).Edge (s,false) a c →
      holdsOriented i (s,false) (env a) (env c) := by
    intro s a c hs
    rcases addNamedEdge_iff.mp hs with hs | ⟨er,ea,ec,_⟩
    · exact hre.edges _ _ _ hs
    · rw [er,ea,ec]; exact he
  rintro ⟨s,_ | _⟩ a c hs
  · exact forward s a c hs
  · exact forward s c a (((b.addNamedEdge r x y).edge_converse (s,false) c a).mp hs)

private theorem Realizes.addEdge {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hre : b.Realizes i env) {r : OrientedRole} {x y : b.Node}
    (he : holdsOriented i r (env x) (env y)) : (b.addEdge r x y).Realizes i env := by
  rcases r with ⟨r,_ | _⟩ <;> exact hre.addNamedEdge he

private theorem addNamedEdge_within {rank : Rank} {p : Problem} {r : IRI}
    (hw : b.Within rank p) (x y : b.Node) (hr : r ∈ roleNames p) :
    (b.addNamedEdge r x y).Within rank p := by
  refine ⟨hw.labels,hw.guards,?_⟩
  intro a
  change b.Node at a
  refine ⟨?_,?_,?_⟩
  · intro z h
    change z ∈ (if b.Child x a ∧ a = y then addOnce r (b.down a) else b.down a) at h
    rcases (mem_addWhere (b.Child x a ∧ a = y)).mp h with ⟨_,rfl⟩ | h
    · exact hr
    · exact (hw.roles a).1 h
  · intro z h
    change z ∈ (if b.Child y a ∧ a = x then addOnce r (b.up a) else b.up a) at h
    rcases (mem_addWhere (b.Child y a ∧ a = x)).mp h with ⟨_,rfl⟩ | h
    · exact hr
    · exact (hw.roles a).2.1 h
  · intro z h
    change z ∈ (if a = x ∧ a = y then addOnce r (b.loops a) else b.loops a) at h
    rcases (mem_addWhere (a = x ∧ a = y)).mp h with ⟨_,rfl⟩ | h
    · exact hr
    · exact (hw.roles a).2.2 h

def edgeStep {p : Problem} {rank : Rank} (r : OrientedRole) (x y : b.Node)
    (hr : b.Within rank p → r.1 ∈ roleNames p)
    (entails : ∀ (i : Interpretation datatypeMap) (env : b.Node → i.Object),
      p.Models i → b.Realizes i env → holdsOriented i r (env x) (env y)) :
    BlockedTransition rank p b where
  branches := [b.addEdge r x y]
  preserves := by
    rintro ⟨i,hm,env,he⟩
    exact ⟨_,List.mem_singleton_self _,i,hm,env,he.addEdge (entails i env hm he)⟩
  within := by
    intro hw next hn
    obtain rfl := List.mem_singleton.mp hn
    have h := hr hw
    rcases r with ⟨r,_ | _⟩ <;> exact addNamedEdge_within hw _ _ h
  root := by
    intro hroot next hn
    obtain rfl := List.mem_singleton.mp hn
    exact hroot
  lift xs := {
    branches := [⟨b.addEdge r x y,xs⟩]
    preserves := by
      rintro ⟨i,hm,e,he,hn⟩
      exact ⟨_,List.mem_singleton_self _,i,hm,e,he.addEdge (entails i e hm he),hn⟩
    within := by
      intro hw next hn
      obtain rfl := List.mem_singleton.mp hn
      have h := hr hw
      rcases r with ⟨r,_ | _⟩ <;> exact addNamedEdge_within hw _ _ h
    root := by
      intro hroot next hn
      obtain rfl := List.mem_singleton.mp hn
      exact hroot
    protects := by
      intro next hn
      obtain rfl := List.mem_singleton.mp hn
      exact ⟨none,⟨extensionWitnessMap id (fun e => e) rfl (fun h => h)
        addEdge_retains (fun h => h) (fun h => h)⟩⟩ }

def expandRoleRule {p : Problem} {rank : Rank} {q : OrientedRole × OrientedRole}
    (hq : q ∈ p.rules) {x y : b.Node} (he : b.Edge q.1 x y) : BlockedTransition rank p b :=
  edgeStep q.2 x y
    (fun _ => by
      have h : q.2.1 ∈ p.rules.flatMap (fun (r,s) => [r.1,s.1]) :=
        List.mem_flatMap.mpr ⟨q,hq,by simp⟩
      simp [roleNames,h])
    (fun _ env hm hre => hm.rules q hq (env x) (env y) (hre.edges _ _ _ he))

def expandReflexive {p : Problem} {rank : Rank} {r : IRI} (hr : r ∈ p.chars.reflexive)
    (x : b.Node) : BlockedTransition rank p b :=
  edgeStep (r,false) x x (fun _ => by simp [roleNames,hr])
    (fun _ env hm _ => hm.reflexive r hr (env x))

def expandSelf {p : Problem} {rank : Rank} {r : OrientedRole} {x : b.Node}
    (hl : .self r true ∈ b.labels x) : BlockedTransition rank p b :=
  edgeStep r x x
    (fun hw => role_in_closure (hw.labels x hl) (by simp [conceptRoles]))
    (fun _ _ _ he => he.labels _ _ hl)


/-- A nodewise collision is the semantic premise for an upper-bound merge. -/
theorem maximum_collision {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (he : b.Realizes i env) {x : b.Node} {r : OrientedRole} {c : Concept} {n : Nat}
    (maximum : .max n r c ∈ b.labels x) {neighbors : List b.Node}
    (len : neighbors.length = n + 1)
    (distinct : neighbors.Nodup)
    (qualified : ∀ y ∈ neighbors, b.Edge r x y ∧ c ∈ b.labels y) :
    ∃ y ∈ neighbors, ∃ z ∈ neighbors, y ≠ z ∧ env y = env z := by
  classical
  apply Classical.byContradiction
  intro none
  apply he.labels x (.max n r c) maximum
  refine ⟨neighbors.map env,by simp [len],?_,?_⟩
  · apply List.pairwise_map.mpr
    apply distinct.imp_of_mem
    intro a z am zm neq eq
    exact none ⟨a,am,z,zm,neq,eq⟩
  · intro y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
    exact ⟨he.edges r x a (qualified a ha).1,he.labels a c (qualified a ha).2⟩

/-- If a child merges into its parent's predecessor, any inequality with
another child of the same parent changes from a sibling constraint into an
ancestor/descendant constraint. The existing sibling-only storage cannot
carry that pair on the unchanged portion of the tree. -/
theorem ancestor_inequality_requires_other_storage {keep center other : b.Node}
    (hc : b.Child keep center) (ho : b.Child center other) :
    (keep,other) ∉ b.unequal := by
  intro h
  obtain ⟨hn,_,hp⟩ := b.unequal_siblings keep other h
  have h₁ := b.parent_lt keep hn
  have h₂ := child_lt hc
  have h₃ : b.parent other = center := ho.2
  rw [hp,h₃] at h₁
  exact Nat.lt_asymm h₁ h₂

private instance {r : OrientedRole} {x y : b.Node} : Decidable (b.Edge r x y) := by
  unfold Edge Down
  infer_instance

private theorem finite_all_nodes {P : b.Node → Prop} : (∀ x ∈ List.finRange (b.size+1), P x) ↔ ∀ x, P x :=
  ⟨fun h x => h x (List.mem_finRange x),fun h x _ => h x⟩

private theorem finite_count {P : b.Node → Prop} [∀ x, Decidable (P x)] {n : Nat} :
    n ≤ ((List.finRange (b.size + 1)).filter (fun x => decide (P x))).length ↔ AtLeast n P := by
  let eligible := (List.finRange (b.size + 1)).filter (fun x => decide (P x))
  have hm (x : b.Node) : x ∈ eligible ↔ P x := by simp [eligible]
  have hn : eligible.Nodup := (List.nodup_finRange _).filter _
  constructor
  · intro h
    change n ≤ eligible.length at h
    refine ⟨eligible.take n,by simp [Nat.min_eq_left h],hn.sublist (List.take_sublist ..),?_⟩
    intro x hx
    exact (hm x).mp ((List.take_sublist ..).subset hx)
  · rintro ⟨xs,hlen,hnd,hall⟩
    rw [← hlen]
    exact hnd.length_le_of_subset fun a hx => (hm a).mpr (hall a hx)

/-- The exact number of distinct template nodes that already qualify for
one restriction. This counts nodes, not occurrences of role labels. -/
def qualifiedCount (b : BlockedBranch) (x : b.Node) (r : OrientedRole) (c : Concept) : Nat :=
  ((List.finRange (b.size + 1)).filter
    (fun y => decide (b.Edge r x y ∧ c ∈ b.labels y))).length

theorem qualifiedCount_spec {x : b.Node} {r : OrientedRole} {c : Concept} {n : Nat} :
    n ≤ b.qualifiedCount x r c ↔ AtLeast n (fun y => b.Edge r x y ∧ c ∈ b.labels y) :=
  finite_count

private def hasPositiveLiteral (b : BlockedBranch) (x : b.Node) : Concept → Bool
  | .lit a false => (b.labels x).contains (.lit a true)
  | _ => false

private def hasNegativeLoop (b : BlockedBranch) (x : b.Node) : Concept → Bool
  | .self r false => decide (b.Edge r x x)
  | _ => false

/-- Decidable test covering all seven kinds of clashes in the blocked model
interface. It ranges only over stored facts and finite node indices. -/
def clashFreeCheck (b : BlockedBranch) (p : Problem) : Bool :=
  let ns := List.finRange (b.size+1)
  ns.all (fun x => !(b.labels x).contains .bottom &&
    !(b.labels x).any (b.hasPositiveLiteral x) &&
    !b.unequal.contains (x,x) &&
    !(b.labels x).any (b.hasNegativeLoop x)) &&
  p.chars.irreflexive.all (fun r => ns.all (fun x => !decide (b.Edge (r,false) x x))) &&
  p.chars.asymmetric.all (fun r => ns.all (fun x => ns.all (fun y =>
    !decide (b.Edge (r,false) x y ∧ b.Edge (r,false) y x)))) &&
  p.chars.disjoint.all (fun q => ns.all (fun x => ns.all (fun y =>
    !decide (b.Edge q.1 x y ∧ b.Edge q.2 x y))))

private theorem no_dual_literals {x : b.Node} :
    ((b.labels x).any (b.hasPositiveLiteral x)) = false ↔
      ∀ a, .lit a true ∈ b.labels x → .lit a false ∉ b.labels x := by
  rw [← Bool.not_eq_true,List.any_eq_true]
  constructor
  · intro h a hp hn
    exact h ⟨.lit a false,hn,List.contains_iff_mem.mpr hp⟩
  · rintro h ⟨c,hc,ht⟩
    cases c <;> try contradiction
    case lit a sign =>
      cases sign <;> try contradiction
      exact h a (List.contains_iff_mem.mp ht) hc

private theorem no_negative_loop {x : b.Node} :
    ((b.labels x).any (b.hasNegativeLoop x)) = false ↔
      ∀ r, .self r false ∈ b.labels x → ¬ b.Edge r x x := by
  rw [← Bool.not_eq_true,List.any_eq_true]
  constructor
  · intro h r hl he
    exact h ⟨.self r false,hl,decide_eq_true he⟩
  · rintro h ⟨c,hc,ht⟩
    cases c <;> try contradiction
    case self r sign =>
      cases sign <;> try contradiction
      exact h r hc (of_decide_eq_true ht)

private theorem contains_false {α : Type} [DecidableEq α] {xs : List α} {a : α} :
    xs.contains a = false ↔ a ∉ xs := by
  rw [← Bool.not_eq_true,List.contains_iff_mem]

theorem clashFreeCheck_iff {p : Problem} : b.clashFreeCheck p = true ↔ b.BlockedClashFree p := by
  simp only [clashFreeCheck,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true',
    contains_false,finite_all_nodes,no_dual_literals,no_negative_loop,decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨locals,irr⟩,asym⟩,disj⟩
    exact ⟨fun x => (locals x).1.1.1,fun x => (locals x).1.1.2,
      fun x => (locals x).1.2,irr,fun r hr x y h h' => asym r hr x y ⟨h,h'⟩,
      disj,fun x => (locals x).2⟩
  · intro h
    exact ⟨⟨⟨fun x => ⟨⟨⟨h.bottom x,h.literal x⟩,h.unequal x⟩,h.selfNeg x⟩,
      h.irreflexive⟩,fun r hr x y hh => h.asymmetric r hr x y hh.1 hh.2⟩,h.disjoint⟩


def active (b : BlockedBranch) (x : b.Node) : Bool :=
  (b.blockedBy x).isNone && !(b.ancestors x).any (fun z => (b.blockedBy z).isSome)

theorem active_iff {x : b.Node} : b.active x = true ↔ b.Unblocked x := by
  simp only [active,Bool.and_eq_true,Option.isNone_iff_eq_none,Bool.not_eq_true',
    ← Bool.not_eq_true,List.any_eq_true,mem_ancestors,Unblocked,IndirectlyBlocked,
    DirectlyBlocked]

private instance (x : b.Node) : Decidable (b.Unblocked x) :=
  decidable_of_iff (b.active x = true) active_iff

theorem edge_name_within {p : Problem} (hw : b.RolesWithin p)
    {x y : b.Node} {r : OrientedRole} (he : b.Edge r x y) : r.1 ∈ roleNames p := by
  rcases he with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
  · exact (hw x).2.2 h
  · rcases r with ⟨r,_ | _⟩
    · exact (hw y).1 h
    · exact (hw y).2.1 h
  · rcases r with ⟨r,_ | _⟩
    · exact (hw x).2.1 h
    · exact (hw x).1 h

def orientedNames (p : Problem) : List OrientedRole :=
  (roleNames p).flatMap (fun r => [(r,false),(r,true)])

private theorem oriented_mem {p : Problem} {r : OrientedRole} (h : r.1 ∈ roleNames p) :
    r ∈ orientedNames p := by
  rcases r with ⟨r,_ | _⟩ <;> exact List.mem_flatMap.mpr ⟨r,h,by simp⟩

/-- Upper-bound actions are isolated from the ordinary saturation rules.
The obligation records the exact restriction, active node and verified
excess of syntactically distinct template neighbors. -/
structure MergeRequired (b : BlockedBranch) where
  node : b.Node
  role : OrientedRole
  filler : Concept
  limit : Nat
  active : b.Unblocked node
  label : .max limit role filler ∈ b.labels node
  over : limit + 1 ≤ b.qualifiedCount node role filler

private inductive Inspection (rank : Rank) (p : Problem) (b : BlockedBranch) (done : Prop) where
  | satisfied (proof : done)
  | step (transition : BlockedTransition rank p b)
  | merge (obligation : b.MergeRequired)

namespace Inspection

variable {rank : Rank} {p : Problem}

def map {P Q : Prop} (f : P → Q) :
    Inspection rank p b P → Inspection rank p b Q
  | .satisfied h => .satisfied (f h)
  | .step t => .step t
  | .merge m => .merge m

def thenCheck {P Q : Prop} (first : Inspection rank p b P)
    (rest : P → Inspection rank p b Q) : Inspection rank p b (P ∧ Q) :=
  match first with
  | .satisfied h => (rest h).map (And.intro h)
  | .step t => .step t
  | .merge m => .merge m

def forAll {α : Type} {P : α → Prop} (xs : List α)
    (f : ∀ a ∈ xs, Inspection rank p b (P a)) :
    Inspection rank p b (∀ a ∈ xs, P a) :=
  match xs with
  | [] => .satisfied (by simp)
  | a :: tail =>
    ((f a (List.mem_cons_self ..)).thenCheck fun _ =>
      forAll tail (fun z hz => f z (List.mem_cons_of_mem _ hz))).map (by
      intro h x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact h.2 x hx)

def forNodes {P : b.Node → Prop} (f : ∀ x, Inspection rank p b (P x)) :
    Inspection rank p b (∀ x, P x) :=
  (forAll (List.finRange (b.size+1)) (fun x _ => f x)).map finite_all_nodes.mp

def assuming {P Q : Prop} [Decidable P]
    (f : P → Inspection rank p b Q) : Inspection rank p b (P → Q) :=
  if h : P then (f h).map (fun hq _ => hq) else .satisfied (fun hp => (h hp).elim)

def check (goal : Prop) [Decidable goal]
    (expand : ¬ goal → BlockedTransition rank p b) : Inspection rank p b goal :=
  if h : goal then .satisfied h else .step (expand h)

end Inspection

private def LabelLocal (rank : Rank) (p : Problem) (b : BlockedBranch) (x : b.Node) :
    Concept → Prop
  | .conj a c => a ∈ b.labels x ∧ c ∈ b.labels x
  | .disj a c => a ∈ b.labels x ∨ c ∈ b.labels x
  | .all r c => (⟨roleLanguage rank p r,c⟩ : Guard) ∈ b.guardLabels x
  | .self r true => b.Edge r x x
  | .max _ r c => ∀ y, b.Edge r x y → c ∈ b.labels y ∨ c.dual ∈ b.labels y
  | _ => True

private def inspectLabel {rank : Rank} {p : Problem} (hi : p.SRIQInput rank) (x : b.Node)
    (c : Concept) (hc : c ∈ b.labels x) : Inspection rank p b (LabelLocal rank p b x c) :=
  match c with
  | .conj a d =>
    (Inspection.check (a ∈ b.labels x) (fun _ => expandConj hc true)).thenCheck
      (fun _ => Inspection.check (d ∈ b.labels x) (fun _ => expandConj hc false))
  | .disj a d => Inspection.check (a ∈ b.labels x ∨ d ∈ b.labels x) (fun _ => expandDisj hc)
  | .all r d =>
    Inspection.check ((⟨roleLanguage rank p r,d⟩ : Guard) ∈ b.guardLabels x)
      (fun _ => startGuard hi hc)
  | .self r true => Inspection.check (b.Edge r x x) (fun _ => expandSelf hc)
  | .max _ r d => Inspection.forNodes fun y =>
    Inspection.assuming (P := b.Edge r x y) fun _ =>
      Inspection.check (d ∈ b.labels y ∨ d.dual ∈ b.labels y) (fun _ => expandMaxQual y hc)
  | .top | .bottom | .lit .. | .nom .. | .self _ false | .some .. | .min ..
  | .dataSome .. | .dataAll .. | .dataValue .. | .dataMin .. | .dataMax .. => .satisfied trivial

private def AllLabels (rank : Rank) (p : Problem) (b : BlockedBranch) : Prop :=
  ∀ x, b.Unblocked x → ∀ c ∈ b.labels x, LabelLocal rank p b x c

private def inspectLabels {rank : Rank} {p : Problem} (hi : p.SRIQInput rank) :
    Inspection rank p b (AllLabels rank p b) :=
  Inspection.forNodes fun x => Inspection.assuming fun _ =>
    Inspection.forAll (b.labels x) (inspectLabel hi x)

private def inspectTBox {rank : Rank} {p : Problem} :
    Inspection rank p b (∀ q ∈ p.tbox, ∀ x, b.Unblocked x →
      q.sub.dual ∈ b.labels x ∨ q.sup ∈ b.labels x) :=
  Inspection.forAll p.tbox fun q hq => Inspection.forNodes fun x => Inspection.assuming fun _ =>
    Inspection.check (q.sub.dual ∈ b.labels x ∨ q.sup ∈ b.labels x) (fun _ => expandTBox x hq)

private def inspectRules {rank : Rank} {p : Problem} :
    Inspection rank p b (∀ q ∈ p.rules, ∀ x y, b.Edge q.1 x y → b.Edge q.2 x y) :=
  Inspection.forAll p.rules fun q hq => Inspection.forNodes fun x => Inspection.forNodes fun y =>
    Inspection.assuming fun he => Inspection.check (b.Edge q.2 x y) (fun _ => expandRoleRule hq he)

private def inspectReflexive {rank : Rank} {p : Problem} :
    Inspection rank p b (∀ r ∈ p.chars.reflexive, ∀ x, b.Edge (r,false) x x) :=
  Inspection.forAll p.chars.reflexive fun r hr => Inspection.forNodes fun x =>
    Inspection.check (b.Edge (r,false) x x) (fun _ => expandReflexive hr x)

private def inspectGuardAccept {rank : Rank} {p : Problem} :
    Inspection rank p b (∀ x, ∀ g ∈ b.guardLabels x, g.state.nullable = true → g.filler ∈ b.labels x) :=
  Inspection.forNodes fun x => Inspection.forAll (b.guardLabels x) fun g hg =>
    Inspection.assuming fun ha => Inspection.check (g.filler ∈ b.labels x) (fun _ => acceptGuard hg ha)

private def inspectGuardSteps {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    Inspection rank p b (∀ x y r, b.Edge r x y → ∀ g ∈ b.guardLabels x, ∀ k ∈ g.advance r,
      k ∈ b.guardLabels y) :=
  (Inspection.forAll (orientedNames p) fun r _ =>
    Inspection.forNodes fun x => Inspection.forNodes fun y =>
      Inspection.assuming (P := b.Edge r x y) fun he =>
        Inspection.forAll (b.guardLabels x) fun g hg =>
          Inspection.forAll (g.advance r) fun k hk =>
            Inspection.check (k ∈ b.guardLabels y) (fun _ => advanceGuard hg he hk)).map
    (fun h x y r he => h r (oriented_mem (edge_name_within hw.roles he)) x y he)

private def Witnessed (b : BlockedBranch) (x : b.Node) : Concept → Prop
  | .some r c => ∃ y, b.Edge r x y ∧ c ∈ b.labels y
  | .min n r c => AtLeast n (fun y => b.Edge r x y ∧ c ∈ b.labels y)
  | _ => True

private theorem exists_iff_one {α : Type} {P : α → Prop} :
    (∃ x, P x) ↔ AtLeast 1 P := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨[x],rfl,by simp,by simpa⟩
  · rintro ⟨xs,hlen,_,hp⟩
    cases xs with
    | nil => contradiction
    | cons x xs => exact ⟨x,hp x (List.mem_cons_self ..)⟩

private def inspectWitness {rank : Rank} {p : Problem} (x : b.Node) (c : Concept)
    (hc : c ∈ b.labels x) : Inspection rank p b (Witnessed b x c) :=
  match c with
  | .some r d =>
    (Inspection.check (1 ≤ b.qualifiedCount x r d) (fun _ => generateSome hc)).map
      (fun h => exists_iff_one.mpr (qualifiedCount_spec.mp h))
  | .min n r d =>
    (Inspection.check (n ≤ b.qualifiedCount x r d) (fun _ => generateMin hc)).map
      qualifiedCount_spec.mp
  | .top | .bottom | .lit .. | .nom .. | .self .. | .conj .. | .disj .. | .all .. | .max ..
  | .dataSome .. | .dataAll .. | .dataValue .. | .dataMin .. | .dataMax .. => .satisfied trivial

private def AllWitnessed (b : BlockedBranch) : Prop :=
  ∀ x, b.Unblocked x → ∀ c ∈ b.labels x, Witnessed b x c

private def inspectWitnesses {rank : Rank} {p : Problem} :
    Inspection rank p b (AllWitnessed b) :=
  Inspection.forNodes fun x => Inspection.assuming fun _ =>
    Inspection.forAll (b.labels x) (inspectWitness x)

private def UpperBounded (b : BlockedBranch) (x : b.Node) : Concept → Prop
  | .max n r c => ¬ AtLeast (n+1) (fun y => b.Edge r x y ∧ c ∈ b.labels y)
  | _ => True

private def inspectUpper {rank : Rank} {p : Problem} (x : b.Node) (hx : b.Unblocked x) (c : Concept)
    (hc : c ∈ b.labels x) : Inspection rank p b (UpperBounded b x c) :=
  match c with
  | .max n r d =>
    if h : n+1 ≤ b.qualifiedCount x r d then .merge ⟨x,r,d,n,hx,hc,h⟩
    else .satisfied (fun he => h (qualifiedCount_spec.mpr he))
  | .top | .bottom | .lit .. | .nom .. | .self .. | .conj .. | .disj .. | .all .. | .some .. | .min ..
  | .dataSome .. | .dataAll .. | .dataValue .. | .dataMin .. | .dataMax .. => .satisfied trivial

private def AllUpperBounded (b : BlockedBranch) : Prop :=
  ∀ x, b.Unblocked x → ∀ c ∈ b.labels x, UpperBounded b x c

private def inspectUpperBounds {rank : Rank} {p : Problem} :
    Inspection rank p b (AllUpperBounded b) :=
  Inspection.forNodes fun x => Inspection.assuming fun hx =>
    Inspection.forAll (b.labels x) (inspectUpper x hx)

/-- The rule sweep reports a merge obligation separately from saturation.
Every ordinary step already carries a realization-preservation proof. -/
inductive Sweep (rank : Rank) (p : Problem) (b : BlockedBranch) where
  | step (transition : BlockedTransition rank p b)
  | saturated (clashFree : b.BlockedClashFree p) (complete : b.BlockedSaturated rank p)
  | merge (obligation : b.MergeRequired)

def sweep {rank : Rank} {p : Problem} (hi : p.SRIQInput rank) (b : BlockedBranch)
    (hw : b.Within rank p) (root : p.root ∈ b.labels 0) : Sweep rank p b.reblock :=
  if hc : b.reblock.clashFreeCheck p = true then
    let completed := inspectLabels (b := b.reblock) hi
    let result := completed.thenCheck fun _ => inspectTBox.thenCheck fun _ =>
      inspectRules.thenCheck fun _ => inspectReflexive.thenCheck fun _ =>
        (inspectGuardSteps (reblock_within hw)).thenCheck fun _ => inspectGuardAccept.thenCheck fun _ =>
          inspectUpperBounds.thenCheck fun _ => inspectWitnesses
    match result with
    | .step t => .step t
    | .merge m => .merge m
    | .satisfied ⟨labels, tbox, rules, refl, guards, accepts, upper, witnesses⟩ =>
      .saturated (clashFreeCheck_iff.mp hc) {
        blocking := reblock_valid b
        root := root
        conj := fun x hx a c h => labels x hx (.conj a c) h
        disj := fun x hx a c h => labels x hx (.disj a c) h
        some := fun x hx r c h => witnesses x hx (.some r c) h
        min := fun x hx n r c h => witnesses x hx (.min n r c) h
        maxQual := fun x hx n r c h => labels x hx (.max n r c) h
        maxBound := fun x hx n r c h => upper x hx (.max n r c) h
        selfPos := fun x hx r h => labels x hx (.self r true) h
        tbox := tbox
        rules := rules
        reflexive := refl
        guardStart := fun x hx r c h => labels x hx (.all r c) h
        guardStep := guards
        guardAccept := accepts }
  else .step (BlockedTransition.close (fun h => hc (clashFreeCheck_iff.mpr h)))


private theorem retained_parent {drop x : b.Node} (hx : x ∈ b.retained drop) (hn : x ≠ 0) :
    b.parent x ∈ b.retained drop := by
  have ha : b.Anc (b.parent x) x := .parent ⟨hn,rfl⟩
  have h := (mem_retained.mp hx).2
  exact mem_retained.mpr ⟨fun e => h (e ▸ ha),fun h' => h (h'.trans ha)⟩

private theorem retained_root {drop : b.Node} (hd : drop ≠ 0) : 0 ∈ b.retained drop :=
  mem_retained.mpr ⟨Ne.symm hd,fun h => Nat.not_lt_zero _ h.lt⟩

private theorem retained_nodup (drop : b.Node) : (b.retained drop).Nodup :=
  (List.nodup_finRange _).filter _

private theorem retained_sorted (drop : b.Node) :
    (b.retained drop).Pairwise (fun a c => a.val < c.val) := by
  apply List.Pairwise.filter
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hlt
  simpa only [List.getElem_finRange,Fin.val_cast] using hlt

private def pruneSize (b : BlockedBranch) (drop : b.Node) : Nat := (b.retained drop).length - 1

private theorem pruneLength {drop : b.Node} (hd : drop ≠ 0) :
    b.pruneSize drop + 1 = (b.retained drop).length := by
  have hn := List.length_pos_of_mem (retained_root hd)
  dsimp [pruneSize]
  omega

private abbrev Pruned (b : BlockedBranch) (drop : b.Node) := Fin (b.pruneSize drop+1)

private def source {drop : b.Node} (hd : drop ≠ 0) (x : b.Pruned drop) : b.Node :=
  (b.retained drop)[x.val]'(pruneLength hd ▸ x.isLt)

private theorem source_mem {drop : b.Node} (hd : drop ≠ 0) (x : b.Pruned drop) :
    source hd x ∈ b.retained drop :=
  List.getElem_mem _

private def compact {drop x : b.Node} (hd : drop ≠ 0) (hx : x ∈ b.retained drop) :
    b.Pruned drop :=
  ⟨(b.retained drop).idxOf x,(pruneLength hd).symm ▸ List.idxOf_lt_length_of_mem hx⟩

@[simp] private theorem source_compact {drop x : b.Node} (hd : drop ≠ 0)
    (hx : x ∈ b.retained drop) : source hd (compact hd hx) = x := by
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)

private theorem source_inj {drop : b.Node} (hd : drop ≠ 0) {x y : b.Pruned drop}
    (he : source hd x = source hd y) : x = y :=
  Fin.ext ((retained_nodup drop).eq_of_getElem_eq _ _ he)

private theorem source_lt {drop : b.Node} (hd : drop ≠ 0) {x y : b.Pruned drop}
    (h : x.val < y.val) : (source hd x).val < (source hd y).val :=
  (retained_sorted drop).rel_getElem_of_lt _ _ h

private theorem compact_lt {drop : b.Node} (hd : drop ≠ 0) {x y : b.Pruned drop}
    (h : (source hd x).val < (source hd y).val) : x.val < y.val := by
  by_cases hlt : x.val < y.val
  · exact hlt
  · have hle : y.val ≤ x.val := by omega
    rcases Nat.lt_or_eq_of_le hle with hr | hr
    · exact (Nat.lt_asymm h (source_lt hd hr)).elim
    · have e : x = y := Fin.ext hr.symm
      exact (Nat.lt_irrefl _ (e ▸ h)).elim

private theorem source_root {drop : b.Node} (hd : drop ≠ 0) :
    source hd 0 = 0 := by
  let root := compact hd (retained_root hd)
  have he : source hd root = 0 := source_compact hd _
  by_cases hzero : root = 0
  · exact hzero ▸ he
  · have hn : root.val ≠ 0 := fun e => hzero (Fin.ext e)
    have hlt := source_lt hd (x := 0) (y := root) (by change 0 < root.val; omega)
    rw [he] at hlt
    exact (Nat.not_lt_zero _ hlt).elim

private theorem source_nonroot {drop : b.Node} (hd : drop ≠ 0) {x : b.Pruned drop}
    (hx : x ≠ 0) : source hd x ≠ 0 :=
  fun e => hx (source_inj hd (e.trans (source_root hd).symm))

private def compactParent {drop : b.Node} (hd : drop ≠ 0) (x : b.Pruned drop) :
    b.Pruned drop :=
  if hx : x = 0 then 0
  else compact hd (retained_parent (source_mem hd x) (source_nonroot hd hx))

private theorem compactParent_source {drop : b.Node} (hd : drop ≠ 0) {x : b.Pruned drop}
    (hx : x ≠ 0) : source hd (compactParent hd x) = b.parent (source hd x) := by
  simp [compactParent,hx]

/-- A merge reindexes surviving nodes. The discarded node itself maps to
the survivor so its explicit inequalities can be transported. -/
private def siblingIndex {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (x : b.Node) : Option (b.Pruned drop) :=
  if x = drop then some (compact hd hk)
  else if hx : x ∈ b.retained drop then some (compact hd hx) else none

private theorem siblingIndex_src {keep drop : b.Node} (hd : drop ≠ 0) (hk : keep ∈ b.retained drop)
    {x : b.Node} {y : b.Pruned drop} (hy : siblingIndex hd hk x = some y) :
    source hd y = if x = drop then keep else x := by
  unfold siblingIndex at hy
  by_cases he : x = drop
  · simp only [he,↓reduceIte,Option.some.injEq] at hy ⊢
    rw [←hy,source_compact]
  · simp only [he,↓reduceIte] at hy ⊢
    split at hy
    · cases hy
      exact source_compact _ _
    · contradiction

private def siblingPairs {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) : List (b.Pruned drop × b.Pruned drop) :=
  b.unequal.filterMap fun (x,y) =>
    (siblingIndex hd hk x).bind fun a => (siblingIndex hd hk y).map (a, ·)

private theorem siblingPairs_src {keep drop : b.Node} (hd : drop ≠ 0) (hk : keep ∈ b.retained drop)
    {x y : b.Pruned drop} (h : (x,y) ∈ siblingPairs hd hk) :
    ∃ a c, (a,c) ∈ b.unequal ∧
      source hd x = (if a = drop then keep else a) ∧
      source hd y = (if c = drop then keep else c) := by
  obtain ⟨⟨a,c⟩,hm,he⟩ := List.mem_filterMap.mp h
  obtain ⟨j,hj,hend⟩ := Option.bind_eq_some_iff.mp he
  obtain ⟨k,hk',hpair⟩ := Option.map_eq_some_iff.mp hend
  cases hpair
  exact ⟨a,c,hm,siblingIndex_src hd hk hj,siblingIndex_src hd hk hk'⟩

private def copySiblings {α : Type} {drop : b.Node} (hd : drop ≠ 0)
    (keep : b.Node) (labels : b.Node → List α) (x : b.Pruned drop) : List α :=
  labels (source hd x) ++ if source hd x = keep then labels drop else []

/-- Merge equal siblings. The dropped subtree is pruned, its incoming
role labels and local labels are carried to the surviving sibling, and the
surviving and redirected inequalities remain sibling pairs. -/
def mergeSiblings (b : BlockedBranch) (keep drop : b.Node)
    (hd : drop ≠ 0) (hk0 : keep ≠ 0) (hkp : b.parent keep = b.parent drop)
    (hk : keep ∈ b.retained drop) : BlockedBranch where
  size := b.pruneSize drop
  parent := compactParent hd
  parent_lt := by
    intro x hx
    apply compact_lt hd
    rw [compactParent_source hd hx]
    exact b.parent_lt _ (source_nonroot hd hx)
  labels := copySiblings hd keep b.labels
  guardLabels := copySiblings hd keep b.guardLabels
  down := copySiblings hd keep b.down
  up := copySiblings hd keep b.up
  loops := copySiblings hd keep b.loops
  unequal := siblingPairs hd hk
  unequal_siblings := by
    intro x y h
    obtain ⟨a,c,hu,ha,hc⟩ := siblingPairs_src hd hk h
    obtain ⟨ha0,hc0,he⟩ := b.unequal_siblings a c hu
    have eq (x : b.Pruned drop) (a : b.Node) (ha0 : a ≠ 0)
        (ha : source hd x = if a = drop then keep else a) :
        x ≠ 0 ∧ source hd (compactParent hd x) = b.parent a := by
      by_cases he : a = drop
      · have hs : source hd x = keep := by simpa only [he,↓reduceIte] using ha
        have hx : x ≠ 0 := fun en => hk0 (hs.symm.trans (en ▸ source_root hd))
        exact ⟨hx,(compactParent_source hd hx).trans (by rw [hs,hkp,he])⟩
      · have hs : source hd x = a := by simpa only [he,↓reduceIte] using ha
        have hx : x ≠ 0 := fun en => ha0 (hs.symm.trans (en ▸ source_root hd))
        exact ⟨hx,(compactParent_source hd hx).trans (congrArg b.parent hs)⟩
    obtain ⟨hx,hxe⟩ := eq x a ha0 ha
    obtain ⟨hy,hye⟩ := eq y c hc0 hc
    exact ⟨hx,hy,source_inj hd (hxe.trans (he.trans hye.symm))⟩
  blockedBy := fun _ => none

private theorem copySiblings_mem {α : Type} {L : b.Node → List α} {keep drop : b.Node}
    (hd : drop ≠ 0) {x : b.Pruned drop} {a : α} :
    a ∈ copySiblings hd keep L x ↔ a ∈ L (source hd x) ∨
      (source hd x = keep ∧ a ∈ L drop) := by
  by_cases he : source hd x = keep <;> simp [copySiblings,he]

theorem mergeSiblings_within {rank : Rank} {p : Problem} (hw : b.Within rank p)
    {keep drop : b.Node} (hd : drop ≠ 0) (hk0 : keep ≠ 0) (hkp : b.parent keep = b.parent drop)
    (hk : keep ∈ b.retained drop) : (b.mergeSiblings keep drop hd hk0 hkp hk).Within rank p := by
  have copied {α : Type} {L : b.Node → List α} {limit : List α}
      (h : ∀ x, L x ⊆ limit) (x : b.Pruned drop) :
      copySiblings hd keep L x ⊆ limit := by
    intro a ha
    rcases (copySiblings_mem hd).mp ha with he | he
    · exact h _ he
    · exact h drop he.2
  exact ⟨copied hw.labels,copied hw.guards,fun x =>
    ⟨copied (fun a => (hw.roles a).1) x,copied (fun a => (hw.roles a).2.1) x,
     copied (fun a => (hw.roles a).2.2) x⟩⟩


private theorem source_child {keep drop : b.Node} {hd : drop ≠ 0} {hk0 : keep ≠ 0}
    {hkp : b.parent keep = b.parent drop} {hk : keep ∈ b.retained drop} {x y : b.Pruned drop}
    (h : (b.mergeSiblings keep drop hd hk0 hkp hk).Child x y) :
    b.Child (source hd x) (source hd y) := by
  exact ⟨source_nonroot hd h.1,
    (compactParent_source hd h.1).symm.trans (congrArg (source hd) h.2)⟩

private theorem copySiblings_down {keep drop : b.Node} {hd : drop ≠ 0} {hk0 : keep ≠ 0}
    {hkp : b.parent keep = b.parent drop} {hk : keep ∈ b.retained drop} {y : b.Pruned drop}
    {r : OrientedRole} (h : (b.mergeSiblings keep drop hd hk0 hkp hk).Down r y) :
    b.Down r (source hd y) ∨ (source hd y = keep ∧ b.Down r drop) := by
  rcases r with ⟨r,_ | _⟩
  · exact (copySiblings_mem hd).mp h
  · exact (copySiblings_mem hd).mp h

theorem Realizes.mergeSiblings {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hr : b.Realizes i env) {keep drop : b.Node} (hd : drop ≠ 0)
    (hk0 : keep ≠ 0) (hkp : b.parent keep = b.parent drop) (hk : keep ∈ b.retained drop)
    (heq : env keep = env drop) :
    (b.mergeSiblings keep drop hd hk0 hkp hk).Realizes i (fun x => env (source hd x)) := by
  constructor
  case labels =>
    intro x c hl
    rcases (copySiblings_mem hd).mp hl with hl | ⟨hx,hl⟩
    · exact hr.labels _ _ hl
    · simpa only [hx,heq] using hr.labels drop c hl
  case guards =>
    intro x g hg
    rcases (copySiblings_mem hd).mp hg with hg | ⟨hx,hg⟩
    · exact hr.guards _ _ hg
    · simpa only [hx,heq] using hr.guards drop g hg
  case unequal =>
    intro x y h
    obtain ⟨a,c,hu,ha,hc⟩ := siblingPairs_src hd hk h
    have env_same (x : b.Pruned drop) (a : b.Node)
        (ha : source hd x = if a = drop then keep else a) : env (source hd x) = env a := by
      by_cases h : a = drop <;> simp [ha,h,heq]
    simpa only [env_same x a ha,env_same y c hc] using hr.unequal a c hu
  case edges =>
    intro r x y h
    have downCase (s : OrientedRole) (a c : b.Pruned drop)
        (hc : (b.mergeSiblings keep drop hd hk0 hkp hk).Child a c)
        (he : (b.mergeSiblings keep drop hd hk0 hkp hk).Down s c) :
        holdsOriented i s (env (source hd a)) (env (source hd c)) := by
      have hsrc := source_child hc
      rcases copySiblings_down he with he | ⟨hkeep,he⟩
      · exact hr.edges s _ _ ((edge_child_iff hsrc).mpr he)
      · have hdrop : b.Child (source hd a) drop := ⟨hd,hkp.symm.trans (hkeep ▸ hsrc.2)⟩
        simpa only [hkeep,heq] using hr.edges s (source hd a) drop ((edge_child_iff hdrop).mpr he)
    rcases h with ⟨h,he⟩ | ⟨hc,he⟩ | ⟨hc,he⟩
    · subst y
      rcases (copySiblings_mem hd).mp he with he | ⟨hx,he⟩
      · exact hr.edges r _ _ ((edge_loop_iff b r _).mpr he)
      · simpa only [hx,heq] using hr.edges r drop drop ((edge_loop_iff b r _).mpr he)
    · exact downCase r x y hc he
    · exact (orientation_flip i r _ _).mp (downCase (converse r) y x hc he)

private theorem retained_sibling {keep drop : b.Node} (hk0 : keep ≠ 0) (hd0 : drop ≠ 0)
    (hneq : keep ≠ drop) (hpar : b.parent keep = b.parent drop) :
    keep ∈ b.retained drop := by
  refine mem_retained.mpr ⟨hneq,?_⟩
  intro h
  rcases (Anc.child_iff ⟨hk0,rfl⟩).mp h with h | h
  · have he : b.parent drop = drop := hpar.symm.trans h.symm
    have hlt := b.parent_lt drop hd0
    rw [he] at hlt
    exact Nat.lt_irrefl _ hlt
  · have hlt := h.lt
    rw [hpar] at hlt
    exact Nat.lt_asymm hlt (b.parent_lt drop hd0)


private def MergeRequired.witnesses (m : b.MergeRequired) : List b.Node :=
  ((List.finRange (b.size+1)).filter (fun y => decide
      (b.Edge m.role m.node y ∧ m.filler ∈ b.labels y))).take (m.limit + 1)

private theorem MergeRequired.witnesses_spec (m : b.MergeRequired) :
    m.witnesses.length = m.limit + 1 ∧ m.witnesses.Nodup ∧
      ∀ y ∈ m.witnesses, b.Edge m.role m.node y ∧ m.filler ∈ b.labels y := by
  refine ⟨?_, ((List.nodup_finRange _).filter _).sublist (List.take_sublist ..),?_⟩
  · rw [MergeRequired.witnesses,List.length_take]
    exact Nat.min_eq_left m.over
  · intro y hy
    have hh := (List.take_sublist ..).subset hy
    exact of_decide_eq_true (List.mem_filter.mp hh).2

private def MergeRequired.pairs (m : b.MergeRequired) : List (b.Node × b.Node) :=
  m.witnesses.flatMap fun x =>
    (m.witnesses.filter fun y => x != y && !b.unequal.contains (x,y) &&
      !b.unequal.contains (y,x)).map (x, ·)

private theorem MergeRequired.pair_mem {m : b.MergeRequired} {x y : b.Node} :
    (x,y) ∈ m.pairs ↔ x ∈ m.witnesses ∧ y ∈ m.witnesses ∧
      x ≠ y ∧ (x,y) ∉ b.unequal ∧ (y,x) ∉ b.unequal := by
  constructor
  · intro hp
    obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨c,hc,he⟩ := List.mem_map.mp hp
    cases he
    have ⟨hc,hh⟩ := List.mem_filter.mp hc
    simp only [Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',contains_false] at hh
    exact ⟨ha,hc,hh.1.1,hh.1.2,hh.2⟩
  · rintro ⟨hx,hy,hn,hxy,hyx⟩
    exact List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,
      List.mem_filter.mpr ⟨hy,by simp [hn,hxy,hyx]⟩,rfl⟩⟩

private theorem MergeRequired.equal_pair {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (m : b.MergeRequired) (he : b.Realizes i env) :
    ∃ q ∈ m.pairs, env q.1 = env q.2 := by
  obtain ⟨hlen,hnodup,hq⟩ := m.witnesses_spec
  obtain ⟨x,hx,y,hy,hne,heq⟩ := maximum_collision he m.label hlen hnodup hq
  exact ⟨(x,y),m.pair_mem.mpr ⟨hx,hy,hne,
    fun hh => he.unequal x y hh heq, fun hh => he.unequal y x hh heq.symm⟩,heq⟩

private abbrev SiblingPair (b : BlockedBranch) (q : b.Node × b.Node) : Prop :=
  q.1 ≠ 0 ∧ q.2 ≠ 0 ∧ b.parent q.1 = b.parent q.2

private instance (q : b.Node × b.Node) : Decidable (b.SiblingPair q) := by
  unfold SiblingPair
  infer_instance

def AncestorMergeShape (b : BlockedBranch) (keep drop : b.Node) : Prop :=
  b.Child keep drop ∨ b.Child keep (b.parent drop)

private theorem ancestor_retained {keep drop : b.Node} (_hd : drop ≠ 0)
    (h : b.Anc keep drop) : keep ∈ b.retained drop := by
  refine mem_retained.mpr ⟨?_,?_⟩
  · intro e
    exact Nat.lt_irrefl _ (e ▸ h.lt)
  · exact fun h' => Nat.lt_asymm h.lt h'.lt

private theorem mergeShape_anc {keep drop : b.Node} (hd : drop ≠ 0)
    (h : b.AncestorMergeShape keep drop) : b.Anc keep drop :=
  h.elim Anc.parent (fun h => .step (.parent h) ⟨hd,rfl⟩)

private def transportedPairs {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (xs : List (b.Node × b.Node)) :
    List (b.Pruned drop × b.Pruned drop) :=
  xs.filterMap fun (x,y) =>
    (siblingIndex hd hk x).bind fun a => (siblingIndex hd hk y).map (a, ·)

private theorem transported_src {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) {xs : List (b.Node × b.Node)} {x y : b.Pruned drop}
    (hm : (x,y) ∈ transportedPairs hd hk xs) :
    ∃ a c, (a,c) ∈ xs ∧ source hd x = (if a = drop then keep else a) ∧
      source hd y = (if c = drop then keep else c) := by
  obtain ⟨⟨a,c⟩,hm,he⟩ := List.mem_filterMap.mp hm
  obtain ⟨q,hq,he⟩ := Option.bind_eq_some_iff.mp he
  obtain ⟨r,hr,he⟩ := Option.map_eq_some_iff.mp he
  cases he
  exact ⟨a,c,hm,siblingIndex_src hd hk hq,siblingIndex_src hd hk hr⟩

private def compactSiblings {drop : b.Node} (hd : drop ≠ 0)
    (x y : b.Pruned drop) : Bool :=
  decide (x ≠ 0 ∧ y ≠ 0 ∧ compactParent hd x = compactParent hd y)

private def ancestorDown {drop : b.Node} (hd : drop ≠ 0) (keep : b.Node)
    (x : b.Pruned drop) : List IRI :=
  b.down (source hd x) ++
    if source hd x = b.parent drop ∧ source hd x ≠ keep then b.up drop else []

private def ancestorUp {drop : b.Node} (hd : drop ≠ 0) (keep : b.Node)
    (x : b.Pruned drop) : List IRI :=
  b.up (source hd x) ++
    if source hd x = b.parent drop ∧ source hd x ≠ keep then b.down drop else []

private def ancestorLoops {drop : b.Node} (hd : drop ≠ 0) (keep : b.Node)
    (x : b.Pruned drop) : List IRI :=
  copySiblings hd keep b.loops x ++
    if source hd x = keep ∧ b.parent drop = keep then b.down drop ++ b.up drop else []

private def ancestorTree (s : ConstrainedTree) (keep drop : s.tree.Node) (hd : drop ≠ 0)
    (hk : keep ∈ s.tree.retained drop) : BlockedBranch :=
  let pairs := transportedPairs hd hk (s.tree.unequal ++ s.extraUnequal)
  { size := s.tree.pruneSize drop
    parent := compactParent hd
    parent_lt := by
      intro x hx
      apply compact_lt hd
      rw [compactParent_source hd hx]
      exact s.tree.parent_lt _ (source_nonroot hd hx)
    labels := copySiblings hd keep s.tree.labels
    guardLabels := copySiblings hd keep s.tree.guardLabels
    down := ancestorDown hd keep
    up := ancestorUp hd keep
    loops := ancestorLoops hd keep
    unequal := pairs.filter fun q => compactSiblings hd q.1 q.2
    unequal_siblings := fun _ _ h => of_decide_eq_true (List.mem_filter.mp h).2
    blockedBy := fun _ => none }

/-- Prune the descendants of the discarded node and move the incident edge.
A parent merge makes that edge a loop. A grandparent merge folds it onto
the edge above the old parent and reverses its orientation. -/
def mergeAncestor (s : ConstrainedTree) (keep drop : s.tree.Node) (hd : drop ≠ 0)
    (shape : s.tree.AncestorMergeShape keep drop) : ConstrainedTree :=
  let hk := ancestor_retained hd (mergeShape_anc hd shape)
  { tree := ancestorTree s keep drop hd hk
    extraUnequal := (transportedPairs hd hk (s.tree.unequal ++ s.extraUnequal)).filter
      (fun q => !compactSiblings hd q.1 q.2) }

private theorem mem_extra_when {α : Type} {a : α} {xs ys : List α}
    (g : Prop) [Decidable g] :
    a ∈ xs ++ (if g then ys else []) ↔ a ∈ xs ∨ (g ∧ a ∈ ys) := by
  by_cases h : g <;> simp [h]

theorem ConstrainedTree.Realizes.mergeAncestor {s : ConstrainedTree} {i : Interpretation datatypeMap}
    {env : s.tree.Node → i.Object} (hr : s.Realizes i env) {keep drop : s.tree.Node}
    (hd : drop ≠ 0) (shape : s.tree.AncestorMergeShape keep drop) (heq : env keep = env drop) :
    (mergeAncestor s keep drop hd shape).Realizes i (fun x => env (source hd x)) := by
  let b := s.tree
  have hk := ancestor_retained hd (mergeShape_anc hd shape)
  have keepUnequal (x y : b.Pruned drop)
      (h : (x,y) ∈ transportedPairs hd hk (b.unequal ++ s.extraUnequal)) :
      env (source hd x) ≠ env (source hd y) := by
    obtain ⟨a,c,h,ha,hc⟩ := transported_src hd hk h
    have mapped (z : b.Pruned drop) (u : b.Node)
        (h : source hd z = if u = drop then keep else u) : env (source hd z) = env u := by
      by_cases hne : u = drop <;> simp [h,hne,heq]
    rw [mapped x a ha,mapped y c hc]
    exact (List.mem_append.mp h).elim (hr.1.unequal a c) (hr.2 a c)
  refine ⟨?_,fun x y h => keepUnequal x y (List.mem_filter.mp h).1⟩
  constructor
  case labels =>
    intro x c hc
    rcases (copySiblings_mem hd).mp hc with h | ⟨hx,h⟩
    · exact hr.1.labels _ _ h
    · simpa only [hx,heq] using hr.1.labels drop c h
  case guards =>
    intro x g hg
    rcases (copySiblings_mem hd).mp hg with h | ⟨hx,h⟩
    · exact hr.1.guards _ _ h
    · simpa only [hx,heq] using hr.1.guards drop g h
  case unequal =>
    intro x y h
    exact keepUnequal x y (List.mem_filter.mp h).1
  case edges =>
    intro r x y h
    have childCase (r : OrientedRole) (a y : b.Pruned drop)
        (hc : (ancestorTree s keep drop hd hk).Child a y)
        (he : (ancestorTree s keep drop hd hk).Down r y) :
        holdsOriented i r (env (source hd a)) (env (source hd y)) := by
      have hc' : b.Child (source hd a) (source hd y) := ⟨source_nonroot hd hc.1,
        (compactParent_source hd hc.1).symm.trans (congrArg (source hd) hc.2)⟩
      have hor : b.Down r (source hd y) ∨
          ((source hd y = b.parent drop ∧ source hd y ≠ keep) ∧ b.Down (converse r) drop) := by
        rcases r with ⟨r,_ | _⟩
        · exact (mem_extra_when _).mp he
        · exact (mem_extra_when _).mp he
      rcases hor with he | ⟨⟨hy,hne⟩,he⟩
      · exact hr.1.edges _ _ _ ((edge_child_iff hc').mpr he)
      · have ha : source hd a = keep := by
          rcases shape with shape | shape
          · exact (hne (hy.trans shape.2)).elim
          · exact hc'.2.symm.trans ((congrArg b.parent hy).trans shape.2)
        have hdrop : b.Child (source hd y) drop := ⟨hd,hy.symm⟩
        rw [ha,heq]
        exact (orientation_flip i r _ _).mp
          (hr.1.edges (converse r) _ _ ((edge_child_iff hdrop).mpr he))
    rcases h with ⟨h,hl⟩ | ⟨hc,he⟩ | ⟨hc,he⟩
    · subst y
      have hlocal : r.1 ∈ copySiblings hd keep b.loops x ∨
          ((source hd x = keep ∧ b.parent drop = keep) ∧ r.1 ∈ b.down drop ++ b.up drop) :=
        (mem_extra_when _).mp hl
      rcases hlocal with he | ⟨⟨hx,hpar⟩,he⟩
      · rcases (copySiblings_mem hd).mp he with he | ⟨hx,he⟩
        · exact hr.1.edges _ _ _ ((edge_loop_iff b r _).mpr he)
        · simpa only [hx,heq] using hr.1.edges r drop drop ((edge_loop_iff b r _).mpr he)
      · have hc : b.Child keep drop := ⟨hd,hpar⟩
        rcases List.mem_append.mp he with he | he
        · have hf := hr.1.edges (r.1,false) keep drop ((edge_child_iff hc).mpr he)
          rw [←heq] at hf
          rw [hx]
          rcases r with ⟨r,_ | _⟩ <;> exact hf
        · have hu := hr.1.edges (r.1,true) keep drop ((edge_child_iff hc).mpr he)
          rw [←heq] at hu
          rw [hx]
          rcases r with ⟨r,_ | _⟩ <;> exact hu
    · exact childCase r x y hc he
    · exact (orientation_flip i r _ _).mp (childCase (converse r) y x hc he)


private theorem mergeAncestor_within {s : ConstrainedTree} {p : Problem} {rank : Rank}
    (hw : s.tree.Within rank p) {keep drop : s.tree.Node} (hd : drop ≠ 0)
    (shape : s.tree.AncestorMergeShape keep drop) :
    (mergeAncestor s keep drop hd shape).tree.Within rank p := by
  constructor
  · intro x c h
    exact ((copySiblings_mem hd).mp h).elim (fun h => hw.labels _ h) (fun h => hw.labels drop h.2)
  · intro x g h
    exact ((copySiblings_mem hd).mp h).elim (fun h => hw.guards _ h) (fun h => hw.guards drop h.2)
  · intro x
    refine ⟨?_,?_,?_⟩
    · intro r h
      exact ((mem_extra_when _).mp h).elim (fun h => (hw.roles _).1 h) (fun h => (hw.roles drop).2.1 h.2)
    · intro r h
      exact ((mem_extra_when _).mp h).elim (fun h => (hw.roles _).2.1 h) (fun h => (hw.roles drop).1 h.2)
    · intro r h
      rcases (mem_extra_when _).mp h with h | ⟨_,h⟩
      · exact ((copySiblings_mem hd).mp h).elim (fun h => (hw.roles _).2.2 h)
          (fun h => (hw.roles drop).2.2 h.2)
      · exact (List.mem_append.mp h).elim (fun h => (hw.roles drop).1 h) (fun h => (hw.roles drop).2.1 h)

private def mergeWithSibling (s : ConstrainedTree) (keep drop : s.tree.Node)
    (shape : s.tree.SiblingPair (keep,drop)) (hn : keep ≠ drop) : ConstrainedTree :=
  let hk := retained_sibling shape.1 shape.2.1 hn shape.2.2
  { tree := s.tree.mergeSiblings keep drop shape.2.1 shape.1 shape.2.2 hk
    extraUnequal := transportedPairs shape.2.1 hk s.extraUnequal }

private theorem mergeWithSibling_realizes {s : ConstrainedTree} {i : Interpretation datatypeMap}
    {env : s.tree.Node → i.Object} (hr : s.Realizes i env) {keep drop : s.tree.Node}
    (shape : s.tree.SiblingPair (keep,drop)) (hn : keep ≠ drop) (he : env keep = env drop) :
    (mergeWithSibling s keep drop shape hn).Realizes i (fun x => env (source shape.2.1 x)) := by
  let hk := retained_sibling shape.1 shape.2.1 hn shape.2.2
  refine ⟨hr.1.mergeSiblings shape.2.1 shape.1 shape.2.2 hk he,?_⟩
  intro a c h
  obtain ⟨x,y,hm,hx,hy⟩ := transported_src shape.2.1 hk h
  change env (source shape.2.1 a) ≠ env (source shape.2.1 c)
  rw [hx,hy]
  have same (z : s.tree.Node) : env (if z = drop then keep else z) = env z := by
    by_cases hz : z = drop <;> simp [hz,he]
  simpa only [same] using hr.2 x y hm

private theorem merge_geometry {x y z : b.Node} (hy : b.Local x y) (hz : b.Local x z)
    (hne : y ≠ z) :
    b.SiblingPair (y,z) ∨ (z ≠ 0 ∧ b.AncestorMergeShape y z) ∨
      (y ≠ 0 ∧ b.AncestorMergeShape z y) := by
  rcases hy with rfl | hy | hy <;> rcases hz with rfl | hz | hz
  · exact (hne rfl).elim
  · exact .inr (.inl ⟨hz.1,.inl hz⟩)
  · exact .inr (.inr ⟨hz.1,.inl hz⟩)
  · exact .inr (.inr ⟨hy.1,.inl hy⟩)
  · exact .inl ⟨hy.1,hz.1,hy.2.trans hz.2.symm⟩
  · exact .inr (.inr ⟨hy.1,.inr (hy.2.symm ▸ hz)⟩)
  · exact .inr (.inl ⟨hy.1,.inl hy⟩)
  · exact .inr (.inl ⟨hz.1,.inr (hz.2.symm ▸ hy)⟩)
  · exact (hne (hy.2.symm.trans hz.2)).elim

private instance (keep drop : b.Node) : Decidable (b.AncestorMergeShape keep drop) := by
  unfold AncestorMergeShape
  infer_instance

private def mergeLocalPair (s : ConstrainedTree) (keep drop : s.tree.Node) (hn : keep ≠ drop)
    (hg : s.tree.SiblingPair (keep,drop) ∨ (drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop) ∨
      (keep ≠ 0 ∧ s.tree.AncestorMergeShape drop keep)) : ConstrainedTree :=
  if hs : s.tree.SiblingPair (keep,drop) then mergeWithSibling s keep drop hs hn
  else if ha : drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop then mergeAncestor s keep drop ha.1 ha.2
  else
    have rev := (hg.resolve_left hs).resolve_left ha
    mergeAncestor s drop keep rev.1 rev.2

private theorem mergeLocalPair_realizes {s : ConstrainedTree} {i : Interpretation datatypeMap}
    {env : s.tree.Node → i.Object} (hr : s.Realizes i env) {keep drop : s.tree.Node} {hn hg}
    (h : env keep = env drop) :
    ∃ env', (mergeLocalPair s keep drop hn hg).Realizes i env' := by
  by_cases hs : s.tree.SiblingPair (keep,drop)
  · rw [mergeLocalPair,dite_eq_left hs]
    exact ⟨_,mergeWithSibling_realizes hr hs hn h⟩
  · rw [mergeLocalPair,dite_eq_right hs]
    by_cases ha : drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop
    · rw [dite_eq_left ha]
      exact ⟨_,hr.mergeAncestor ha.1 ha.2 h⟩
    · rw [dite_eq_right ha]
      exact ⟨_,hr.mergeAncestor _ _ h.symm⟩

private theorem mergeLocalPair_within {s : ConstrainedTree} {p : Problem} {rank : Rank}
    (hw : s.tree.Within rank p) {keep drop : s.tree.Node} {hn hg} :
    (mergeLocalPair s keep drop hn hg).tree.Within rank p := by
  unfold mergeLocalPair
  split
  · rename_i hs
    exact mergeSiblings_within hw hs.2.1 hs.1 hs.2.2 _
  · split <;> exact mergeAncestor_within hw _ _

private theorem mergeLocalPair_root {s : ConstrainedTree} {p : Problem}
    (hw : p.root ∈ s.tree.labels 0) {keep drop : s.tree.Node} {hn hg} :
    p.root ∈ (mergeLocalPair s keep drop hn hg).tree.labels 0 := by
  by_cases hs : s.tree.SiblingPair (keep,drop)
  · rw [mergeLocalPair,dite_eq_left hs]
    exact (copySiblings_mem hs.2.1).mpr (.inl ((source_root hs.2.1).symm ▸ hw))
  · rw [mergeLocalPair,dite_eq_right hs]
    by_cases ha : drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop
    · rw [dite_eq_left ha]
      exact (copySiblings_mem ha.1).mpr (.inl ((source_root ha.1).symm ▸ hw))
    · rw [dite_eq_right ha]
      exact (copySiblings_mem _).mpr (.inl ((source_root _).symm ▸ hw))

private def MergeRequired.constrainedPairs (s : ConstrainedTree) (m : s.tree.MergeRequired) :
    List (s.tree.Node × s.tree.Node) :=
  m.pairs.filter fun q => !s.extraUnequal.contains q && !s.extraUnequal.contains (q.2,q.1)

private theorem MergeRequired.constrainedEqual {s : ConstrainedTree} (m : s.tree.MergeRequired)
    {i : Interpretation datatypeMap} {env : s.tree.Node → i.Object} (h : s.Realizes i env) :
    ∃ q ∈ m.constrainedPairs s, env q.1 = env q.2 := by
  obtain ⟨q,hq,heq⟩ := m.equal_pair h.1
  have hn₁ : q ∉ s.extraUnequal := fun hneq => h.2 _ _ hneq heq
  have hn₂ : (q.2,q.1) ∉ s.extraUnequal := fun hneq => h.2 _ _ hneq heq.symm
  exact ⟨q,List.mem_filter.mpr ⟨hq,by simp [hn₁,hn₂]⟩,heq⟩

private def MergeRequired.alternative (s : ConstrainedTree) (m : s.tree.MergeRequired)
    (q : {x // x ∈ m.constrainedPairs s}) : ConstrainedTree :=
  let spec := m.pair_mem.mp (List.mem_filter.mp q.property).1
  let quals := m.witnesses_spec.2.2
  mergeLocalPair s q.val.1 q.val.2 spec.2.2.1
    (merge_geometry (quals _ spec.1).1.local (quals _ spec.2.1).1.local spec.2.2.1)

/-! ### Persistence of generated witnesses -/

theorem ConstrainedTree.ProtectedWitnesses.count {s : ConstrainedTree} {x : s.tree.Node}
    {r : OrientedRole} {c : Concept} {n : Nat} (h : s.ProtectedWitnesses x r c n) :
    n ≤ s.tree.qualifiedCount x r c := by
  obtain ⟨ys,hlen,hnd,_,hall⟩ := h
  exact qualifiedCount_spec.mpr ⟨ys,hlen,hnd,hall⟩

theorem WitnessMap.protected {s t : ConstrainedTree} {drop : Option s.tree.Node}
    (m : WitnessMap s t drop) {x : s.tree.Node} {x' : t.tree.Node}
    (hx : KeepsVertex s.tree drop x) (hmap : m.redirect x = some x')
    {r : OrientedRole} {c : Concept} {n : Nat} (hw : s.ProtectedWitnesses x r c n) :
    t.ProtectedWitnesses x' r c n := by
  obtain ⟨ys,hlen,hnd,hd,hne⟩ := hw
  let f := fun y => (m.redirect y).getD 0
  have lift (y : s.tree.Node) (hy : y ∈ ys) :
      m.redirect y = some (f y) ∧ t.tree.Edge r x' (f y) ∧ c ∈ t.tree.labels (f y) := by
    obtain ⟨y',h',he⟩ := m.edge hx hmap r y (hne y hy).1
    have eq : f y = y' := by simp [f,h']
    exact ⟨eq.symm ▸ h',eq.symm ▸ he,eq.symm ▸ m.label h' c (hne y hy).2⟩
  have apart : ys.Pairwise (fun y z => f y ≠ f z ∧ t.RecordedDistinct (f y) (f z)) := by
    apply (hnd.and hd).imp_of_mem
    intro y z hy hz h
    exact m.distinct (lift y hy).1 (lift z hz).1 h.1 h.2
  refine ⟨ys.map f,by simp [hlen], List.pairwise_map.mpr (apart.imp (fun h => h.1)),
    List.pairwise_map.mpr (apart.imp (fun h => h.2)),?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
  exact (lift z hz).2

private theorem depth_child {x y : b.Node} (h : b.Child x y) :
    b.depth y = b.depth x + 1 := by
  unfold depth
  rw [ancestors]
  simp [h.1,h.2]

/-- Renumbering preserves the depth of each surviving vertex. Redirecting the
discarded vertex to its merge representative is separate from this claim. -/
theorem WitnessMap.depth_eq {s t : ConstrainedTree} {drop : Option s.tree.Node}
    (m : WitnessMap s t drop) {x : s.tree.Node} {y : t.tree.Node}
    (hx : KeepsVertex s.tree drop x) (hm : m.redirect x = some y) :
    t.tree.depth y = s.tree.depth x := by
  by_cases hz : x = 0
  · subst x
    have hy := Option.some.inj (m.root.symm.trans hm)
    subst y
    simp [depth,ancestors]
  · have child : s.tree.Child (s.tree.parent x) x := ⟨hz,rfl⟩
    obtain ⟨hp,hchild⟩ := m.parent child hx
    obtain ⟨q,hq⟩ := m.center _ hp
    rw [depth_child (hchild hq hm),depth_child child,m.depth_eq hp hq]
termination_by x.val
decreasing_by exact s.tree.parent_lt x hz

private theorem retained_neighbor {drop x y : b.Node} {r : OrientedRole}
    (hx : x ∈ b.retained drop) (he : b.Edge r x y) : y ∈ b.retained drop ∨ y = drop := by
  rcases he.local with hxy | hxy | hyx
  · exact .inl (hxy ▸ hx)
  · by_cases hy : y = drop
    · exact .inr hy
    · refine .inl (mem_retained.mpr ⟨hy,?_⟩)
      intro h
      exact ((Anc.child_iff hxy).mp h).elim (fun h => (mem_retained.mp hx).1 h.symm)
        (mem_retained.mp hx).2
  · exact .inl (hyx.2 ▸ retained_parent hx hyx.1)

private theorem siblingIndex_kept {keep drop y : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hy : y ∈ b.retained drop) :
    siblingIndex hd hk y = some (compact hd hy) := by
  simp [siblingIndex,(mem_retained.mp hy).1,hy]

private theorem siblingIndex_drop {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) :
    siblingIndex hd hk drop = some (compact hd hk) := by
  simp [siblingIndex]

private theorem siblingIndex_separates {s : ConstrainedTree} {keep drop : s.tree.Node}
    (hd : drop ≠ 0) (hk : keep ∈ s.tree.retained drop)
    (allowed : ¬ s.RecordedDistinct keep drop) {y z : s.tree.Node} {y' z' : s.tree.Pruned drop}
    (hy : siblingIndex hd hk y = some y') (hz : siblingIndex hd hk z = some z')
    (hn : y ≠ z) (h : s.RecordedDistinct y z) : y' ≠ z' := by
  intro he
  have hsrc := (siblingIndex_src hd hk hy).symm.trans
    ((congrArg (source hd) he).trans (siblingIndex_src hd hk hz))
  by_cases hy0 : y = drop <;> by_cases hz0 : z = drop
  · exact hn (hy0.trans hz0.symm)
  · have eq : keep = z := by simpa [hy0,hz0] using hsrc
    exact allowed (eq.symm ▸ hy0 ▸ h.symm)
  · have eq : y = keep := by simpa [hy0,hz0] using hsrc
    exact allowed (eq ▸ hz0 ▸ h)
  · exact hn (by simpa [hy0,hz0] using hsrc)

private theorem transportedPair_mem {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) {xs : List (b.Node × b.Node)}
    {y z : b.Node} {y' z' : b.Pruned drop}
    (hy : siblingIndex hd hk y = some y') (hz : siblingIndex hd hk z = some z')
    (h : (y,z) ∈ xs) : (y',z') ∈ transportedPairs hd hk xs :=
  List.mem_filterMap.mpr ⟨(y,z),h,by simp [hy,hz]⟩

private theorem merge_index_label {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) {α : Type} {L : b.Node → List α} {y : b.Node}
    {y' : b.Pruned drop} (hy : siblingIndex hd hk y = some y') {c : α} (hc : c ∈ L y) :
    c ∈ copySiblings hd keep L y' := by
  have hs := siblingIndex_src hd hk hy
  apply (copySiblings_mem hd).mpr
  by_cases h : y = drop
  · exact .inr ⟨by simpa [h] using hs,h ▸ hc⟩
  · exact .inl ((show source hd y' = y by simpa [h] using hs).symm ▸ hc)

private theorem compact_child {drop : b.Node} (hd : drop ≠ 0) {x y : b.Pruned drop}
    (h : b.Child (source hd x) (source hd y)) :
    y ≠ 0 ∧ compactParent hd y = x := by
  have hn : y ≠ 0 := fun e => h.1 (e ▸ source_root hd)
  exact ⟨hn,source_inj hd ((compactParent_source hd hn).trans h.2)⟩

private theorem siblingIndex_root {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) : siblingIndex hd hk 0 = some 0 := by
  have h0 := retained_root hd
  refine (siblingIndex_kept hd hk h0).trans (congrArg some ?_)
  exact source_inj hd ((source_compact hd h0).trans (source_root hd).symm)

private theorem siblingIndex_inj_retained {keep drop x y : b.Node}
    (hd : drop ≠ 0) (hk : keep ∈ b.retained drop)
    {z : b.Pruned drop} (hx : x ∈ b.retained drop) (hy : y ∈ b.retained drop)
    (hxr : siblingIndex hd hk x = some z) (hyr : siblingIndex hd hk y = some z) : x = y := by
  have ex : compact hd hx = z := Option.some.inj ((siblingIndex_kept hd hk hx).symm.trans hxr)
  have ey : compact hd hy = z := Option.some.inj ((siblingIndex_kept hd hk hy).symm.trans hyr)
  exact (source_compact hd hx).symm.trans
    ((congrArg (source hd) (ex.trans ey.symm)).trans (source_compact hd hy))

private theorem siblingIndex_parent {keep drop x y : b.Node}
    (hd : drop ≠ 0) (hk : keep ∈ b.retained drop) (hc : b.Child x y)
    (hy : y ∈ b.retained drop) :
    x ∈ b.retained drop ∧ ∀ {a d : b.Pruned drop},
      siblingIndex hd hk x = some a → siblingIndex hd hk y = some d →
        d ≠ 0 ∧ compactParent hd d = a := by
  have hx : x ∈ b.retained drop := hc.2 ▸ retained_parent hy hc.1
  refine ⟨hx,?_⟩
  intro a d hxa hyd
  have ea : compact hd hx = a := Option.some.inj ((siblingIndex_kept hd hk hx).symm.trans hxa)
  have ed : compact hd hy = d := Option.some.inj ((siblingIndex_kept hd hk hy).symm.trans hyd)
  subst a
  subst d
  apply compact_child hd
  simpa only [source_compact] using hc

private theorem drop_is_child {drop x : b.Node} {r : OrientedRole}
    (hx : x ∈ b.retained drop) (he : b.Edge r x drop) : b.Child x drop := by
  rcases he.local with h | h | h
  · exact ((mem_retained.mp hx).1 h).elim
  · exact h
  · exact ((mem_retained.mp hx).2 (.parent h)).elim

private def siblingWitnessMap (s : ConstrainedTree) (keep drop : s.tree.Node)
    (shape : s.tree.SiblingPair (keep,drop)) (hn : keep ≠ drop)
    (allowed : ¬ s.RecordedDistinct keep drop) :
    MergeWitnessMap s (mergeWithSibling s keep drop shape hn) drop := by
  let hd := shape.2.1
  let hk := retained_sibling shape.1 hd hn shape.2.2
  let t := mergeWithSibling s keep drop shape hn
  have mapDown {y : s.tree.Node} {y' : t.tree.Node} (hm : siblingIndex hd hk y = some y')
      {r : OrientedRole} (h : s.tree.Down r y) : t.tree.Down r y' := by
    rcases r with ⟨r,_ | _⟩
    · exact merge_index_label hd hk hm h
    · exact merge_index_label hd hk hm h
  have mapLoop {y : s.tree.Node} {y' : t.tree.Node} (hm : siblingIndex hd hk y = some y')
      {r : OrientedRole} (h : r.1 ∈ s.tree.loops y) : r.1 ∈ t.tree.loops y' :=
    merge_index_label hd hk hm h
  have keptEdge {x y : s.tree.Node} {r : OrientedRole} (hx : x ∈ s.tree.retained drop)
      (hy : y ∈ s.tree.retained drop) (he : s.tree.Edge r x y) :
      t.tree.Edge r (compact hd hx) (compact hd hy) := by
    have child {a c : s.tree.Node} (ha : a ∈ s.tree.retained drop)
        (hc : c ∈ s.tree.retained drop) (hh : s.tree.Child a c) :
        t.tree.Child (compact hd ha) (compact hd hc) := by
      apply compact_child hd
      simpa only [source_compact] using hh
    rcases he with ⟨rfl,h⟩ | ⟨ha,h⟩ | ⟨ha,h⟩
    · exact .inl ⟨rfl,mapLoop (siblingIndex_kept hd hk hx) h⟩
    · exact .inr (.inl ⟨child hx hy ha,mapDown (siblingIndex_kept hd hk hy) h⟩)
    · exact .inr (.inr ⟨child hy hx ha,mapDown (siblingIndex_kept hd hk hx) h⟩)
  refine {
    redirect := siblingIndex hd hk
    root := siblingIndex_root hd hk
    center := fun x hx => ⟨compact hd hx,siblingIndex_kept hd hk hx⟩
    injectiveOnSurvivors := siblingIndex_inj_retained hd hk
    parent := siblingIndex_parent hd hk
    edge := ?_
    label := fun hy _ hc => merge_index_label hd hk hy hc
    distinct := ?_ }
  · intro x x' hx hm r y he
    have eq : compact hd hx = x' := Option.some.inj ((siblingIndex_kept hd hk hx).symm.trans hm)
    subst x'
    rcases retained_neighbor hx he with hy | rfl
    · exact ⟨compact hd hy,siblingIndex_kept hd hk hy,keptEdge hx hy he⟩
    · have hc := drop_is_child hx he
      have hc' : s.tree.Child x keep := ⟨shape.1,shape.2.2.trans hc.2⟩
      have ht : t.tree.Child (compact hd hx) (compact hd hk) := by
        apply compact_child hd
        simpa only [source_compact] using hc'
      have hdwn := (edge_child_iff hc).mp he
      exact ⟨compact hd hk,siblingIndex_drop hd hk,
        (edge_child_iff ht).mpr (mapDown (siblingIndex_drop hd hk) hdwn)⟩
  · intro y z y' z' hy hz hdif h
    refine ⟨siblingIndex_separates hd hk allowed hy hz hdif h,?_⟩
    rcases h with (h | h) | (h | h)
    · exact .inl (.inl (transportedPair_mem hd hk hy hz h))
    · exact .inl (.inr (transportedPair_mem hd hk hy hz h))
    · exact .inr (.inl (transportedPair_mem hd hk hz hy h))
    · exact .inr (.inr (transportedPair_mem hd hk hz hy h))

private def ancestorWitnessMap (s : ConstrainedTree) (keep drop : s.tree.Node)
    (hd : drop ≠ 0) (shape : s.tree.AncestorMergeShape keep drop)
    (allowed : ¬ s.RecordedDistinct keep drop) :
    MergeWitnessMap s (mergeAncestor s keep drop hd shape) drop := by
  let hk := ancestor_retained hd (mergeShape_anc hd shape)
  let t := mergeAncestor s keep drop hd shape
  have child {a c : s.tree.Node} (ha : a ∈ s.tree.retained drop)
      (hc : c ∈ s.tree.retained drop) (hh : s.tree.Child a c) :
      t.tree.Child (compact hd ha) (compact hd hc) := by
    apply compact_child hd
    simpa only [source_compact] using hh
  have mapDown {y : s.tree.Node} (hy : y ∈ s.tree.retained drop)
      {r : OrientedRole} (h : s.tree.Down r y) : t.tree.Down r (compact hd hy) := by
    rcases r with ⟨r,_ | _⟩
    · apply List.mem_append_left
      change r ∈ s.tree.down y at h
      simpa only [source_compact] using h
    · apply List.mem_append_left
      change r ∈ s.tree.up y at h
      simpa only [source_compact] using h
  have mapLoop {y : s.tree.Node} (hy : y ∈ s.tree.retained drop)
      {r : OrientedRole} (h : r.1 ∈ s.tree.loops y) : r.1 ∈ t.tree.loops (compact hd hy) :=
    List.mem_append_left _ (merge_index_label hd hk (siblingIndex_kept hd hk hy) h)
  have keptEdge {x y : s.tree.Node} {r : OrientedRole} (hx : x ∈ s.tree.retained drop)
      (hy : y ∈ s.tree.retained drop) (he : s.tree.Edge r x y) :
      t.tree.Edge r (compact hd hx) (compact hd hy) := by
    rcases he with ⟨rfl,h⟩ | ⟨ha,h⟩ | ⟨ha,h⟩
    · exact .inl ⟨rfl,mapLoop hx h⟩
    · exact .inr (.inl ⟨child hx hy ha,mapDown hy h⟩)
    · exact .inr (.inr ⟨child hy hx ha,mapDown hx h⟩)
  refine {
    redirect := siblingIndex hd hk
    root := siblingIndex_root hd hk
    center := fun x hx => ⟨compact hd hx,siblingIndex_kept hd hk hx⟩
    injectiveOnSurvivors := siblingIndex_inj_retained hd hk
    parent := siblingIndex_parent hd hk
    edge := ?_
    label := fun hy _ hc => merge_index_label hd hk hy hc
    distinct := ?_ }
  · intro x x' hx hm r y he
    have eq : compact hd hx = x' := Option.some.inj ((siblingIndex_kept hd hk hx).symm.trans hm)
    subst x'
    rcases retained_neighbor hx he with hy | hy
    · exact ⟨compact hd hy,siblingIndex_kept hd hk hy,keptEdge hx hy he⟩
    · subst y
      refine ⟨compact hd hk,siblingIndex_drop hd hk,?_⟩
      have hc := drop_is_child hx he
      have hdwn := (edge_child_iff hc).mp he
      rcases shape with near | far
      · have eq : compact hd hx = compact hd hk := by
          apply source_inj hd
          rw [source_compact,source_compact]
          exact hc.2.symm.trans near.2
        rw [eq]
        apply (edge_loop_iff t.tree r _).mpr
        have hr : r.1 ∈ s.tree.down drop ++ s.tree.up drop := by
          rcases r with ⟨r,_ | _⟩
          · exact List.mem_append_left _ hdwn
          · exact List.mem_append_right _ hdwn
        apply (mem_extra_when _).mpr
        exact .inr ⟨⟨source_compact hd hk,near.2⟩,hr⟩
      · have hc' : s.tree.Child keep x := hc.2 ▸ far
        have hneq : x ≠ keep := fun e => Nat.lt_irrefl _ (e ▸ child_lt hc')
        have label : t.tree.Down (converse r) (compact hd hx) := by
          have gate : source hd (compact hd hx) = s.tree.parent drop ∧
              source hd (compact hd hx) ≠ keep := ⟨(source_compact hd hx).trans hc.2.symm,
                fun e => hneq ((source_compact hd hx).symm.trans e)⟩
          rcases r with ⟨r,_ | _⟩
          · exact (mem_extra_when _).mpr (.inr ⟨gate,hdwn⟩)
          · exact (mem_extra_when _).mpr (.inr ⟨gate,hdwn⟩)
        exact .inr (.inr ⟨child hk hx hc',label⟩)
  · intro y z y' z' hy hz hdif h
    refine ⟨siblingIndex_separates hd hk allowed hy hz hdif h,?_⟩
    have preserves {a c : s.tree.Node} {a' c' : t.tree.Node}
        (ha : siblingIndex hd hk a = some a') (hc : siblingIndex hd hk c = some c')
        (hm : (a,c) ∈ s.tree.unequal ∨ (a,c) ∈ s.extraUnequal) :
        (a',c') ∈ t.tree.unequal ∨ (a',c') ∈ t.extraUnequal := by
      have moved := transportedPair_mem hd hk ha hc (List.mem_append.mpr hm)
      cases h : compactSiblings hd a' c' with
      | true => exact .inl (List.mem_filter.mpr ⟨moved,h⟩)
      | false => exact .inr (List.mem_filter.mpr ⟨moved,by simp [h]⟩)
    exact h.elim (fun h => .inl (preserves hy hz h)) (fun h => .inr (preserves hz hy h))

private theorem mergeLocalPair_witnessMap {s : ConstrainedTree} {keep drop : s.tree.Node}
    (hn : keep ≠ drop)
    (hg : s.tree.SiblingPair (keep,drop) ∨ (drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop) ∨
      (keep ≠ 0 ∧ s.tree.AncestorMergeShape drop keep))
    (allowed : ¬ s.RecordedDistinct keep drop) :
    ∃ d, Nonempty (MergeWitnessMap s (mergeLocalPair s keep drop hn hg) d) := by
  by_cases hs : s.tree.SiblingPair (keep,drop)
  · rw [mergeLocalPair,dite_eq_left hs]
    exact ⟨drop,⟨siblingWitnessMap s keep drop hs hn allowed⟩⟩
  · rw [mergeLocalPair,dite_eq_right hs]
    by_cases ha : drop ≠ 0 ∧ s.tree.AncestorMergeShape keep drop
    · rw [dite_eq_left ha]
      exact ⟨drop,⟨ancestorWitnessMap s keep drop ha.1 ha.2 allowed⟩⟩
    · rw [dite_eq_right ha]
      exact ⟨keep,⟨ancestorWitnessMap s drop keep _ _ (fun h => allowed h.symm)⟩⟩

private theorem MergeRequired.alternative_witnessMap (s : ConstrainedTree)
    (m : s.tree.MergeRequired) (q : {x // x ∈ m.constrainedPairs s}) :
    ∃ drop, Nonempty (MergeWitnessMap s (m.alternative s q) drop) := by
  have filtered := List.mem_filter.mp q.property
  have limits := m.pair_mem.mp filtered.1
  have extra := filtered.2
  simp only [Bool.and_eq_true,Bool.not_eq_true',contains_false] at extra
  unfold MergeRequired.alternative
  apply mergeLocalPair_witnessMap
  rintro ((h | h) | (h | h))
  · exact limits.2.2.2.1 h
  · exact extra.1 h
  · exact limits.2.2.2.2 h
  · exact extra.2 h

/-- Enumerate every admissible collision among the excess qualified
neighbors. Both sibling and ancestor pairs are handled, and each alternative
retains all redirected inequalities whose endpoints survive pruning. -/
def resolveMerge {rank : Rank} {p : Problem} (s : ConstrainedTree) (m : s.tree.MergeRequired) :
    ConstrainedTransition rank p s where
  branches := (m.constrainedPairs s).attach.map (m.alternative s)
  preserves := by
    rintro ⟨i,hm,env,he⟩
    obtain ⟨q,hq,heq⟩ := m.constrainedEqual he
    have hreal : ∃ e, (m.alternative s ⟨q,hq⟩).Realizes i e := by
      unfold MergeRequired.alternative
      apply mergeLocalPair_realizes he heq
    obtain ⟨env',hnext⟩ := hreal
    exact ⟨m.alternative s ⟨q,hq⟩,List.mem_map_of_mem (List.mem_attach ..),i,hm,env',hnext⟩
  within := by
    intro hw t ht
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp ht
    unfold MergeRequired.alternative
    apply mergeLocalPair_within hw
  root := by
    intro hw t ht
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp ht
    unfold MergeRequired.alternative
    apply mergeLocalPair_root hw
  protects := by
    intro t ht
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp ht
    obtain ⟨d,hm⟩ := m.alternative_witnessMap s q
    exact ⟨some d,hm⟩


def ConstrainedTree.reblock (s : ConstrainedTree) : ConstrainedTree :=
  ⟨s.tree.reblock,s.extraUnequal⟩

theorem ConstrainedTree.reblock_sat_iff (s : ConstrainedTree) (p : Problem) :
    s.reblock.Sat p ↔ s.Sat p :=
  ⟨fun ⟨i,hm,e,h,hx⟩ => ⟨i,hm,e,⟨h.labels,h.edges,h.guards,h.unequal⟩,hx⟩,
   fun ⟨i,hm,e,h,hx⟩ => ⟨i,hm,e,⟨h.labels,h.edges,h.guards,h.unequal⟩,hx⟩⟩

private def ConstrainedTransition.beforeReblock {rank : Rank} {p : Problem} {s : ConstrainedTree}
    (t : ConstrainedTransition rank p s.reblock) : ConstrainedTransition rank p s where
  branches := t.branches
  preserves := fun h => t.preserves ((s.reblock_sat_iff p).mpr h)
  within := fun h => t.within (reblock_within h)
  root := t.root
  protects := by
    intro next hnext
    obtain ⟨drop,⟨m⟩⟩ := t.protects next hnext
    have keeps (x : s.tree.Node) : KeepsVertex s.tree drop x ↔ KeepsVertex s.reblock.tree drop x := by
      cases drop with
      | none => exact Iff.rfl
      | some d =>
        exact mem_retained.trans ((and_congr Iff.rfl (not_congr same_anc_reblock.symm)).trans
          (mem_retained (b := s.reblock.tree) (drop := d) (x := x)).symm)
    exact ⟨drop,⟨{
      redirect := m.redirect
      root := m.root
      center := fun x h => m.center x ((keeps x).mp h)
      injectiveOnSurvivors := fun hx hy => m.injectiveOnSurvivors ((keeps _).mp hx) ((keeps _).mp hy)
      parent := fun hc hy =>
        let h := m.parent hc ((keeps _).mp hy)
        ⟨(keeps _).mpr h.1,h.2⟩
      edge := fun h hm => m.edge ((keeps _).mp h) hm
      label := m.label
      distinct := m.distinct }⟩⟩

structure SearchState (rank : Rank) (p : Problem) where
  branch : ConstrainedTree
  within : branch.tree.Within rank p
  root : p.root ∈ branch.tree.labels 0

def SearchState.initial (rank : Rank) (p : Problem) : SearchState rank p :=
  ⟨⟨BlockedBranch.initial p,[]⟩,initial_within rank p,by simp [BlockedBranch.initial]⟩

theorem SearchState.initial_sat_iff (rank : Rank) (p : Problem) :
    (SearchState.initial rank p).branch.Sat p ↔ p.Sat := by
  rw [← BlockedBranch.initial_sat_iff p]
  constructor
  · rintro ⟨i,hm,e,h,_⟩
    exact ⟨i,hm,e,h⟩
  · rintro ⟨i,hm,e,h⟩
    exact ⟨i,hm,e,h,fun _ _ hnil => (List.not_mem_nil hnil).elim⟩

def SearchState.follow {rank : Rank} {p : Problem} (s : SearchState rank p)
    (t : ConstrainedTransition rank p s.branch) (next : ConstrainedTree)
    (hn : next ∈ t.branches) : SearchState rank p :=
  ⟨next,t.within s.within next hn,t.root s.root next hn⟩

private def closeExtra {rank : Rank} {p : Problem} {s : ConstrainedTree}
    (h : ∃ q ∈ s.extraUnequal, q.1 = q.2) : ConstrainedTransition rank p s where
  branches := []
  preserves := by
    rintro ⟨i,hm,e,hr,hx⟩
    obtain ⟨⟨a,c⟩,h,he⟩ := h
    exact (hx a c h (congrArg e he)).elim
  within := by simp
  root := by simp
  protects := by simp

inductive StepResult {rank : Rank} {p : Problem} (s : SearchState rank p) where
  | expand (t : ConstrainedTransition rank p s.branch)
  | terminal (clashFree : s.branch.tree.reblock.BlockedClashFree p)
      (saturated : s.branch.tree.reblock.BlockedSaturated rank p)

def inspectSRIQ {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    (s : SearchState rank p) : StepResult s :=
  if h : ∃ q ∈ s.branch.extraUnequal, q.1 = q.2 then .expand (closeExtra h)
  else
    match sweep (p.sriqInput hs) s.branch.tree s.within s.root with
    | .step t => .expand (t.lift s.branch.extraUnequal).beforeReblock
    | .merge m => .expand (resolveMerge s.branch.reblock m).beforeReblock
    | .saturated hc h => .terminal hc h

/-- Select one full blocked tableau step. The state carries the finite
alphabet and root invariants, plus general inequalities learned by merges. -/
def sriqStep {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    (s : SearchState rank p) : Option (ConstrainedTransition rank p s.branch) :=
  match inspectSRIQ hs s with
  | .expand t => some t
  | .terminal _ _ => none

theorem sriqStep_fair {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {s : SearchState rank p} (h : sriqStep hs s = none) :
    s.branch.tree.reblock.BlockedClashFree p ∧ s.branch.tree.reblock.BlockedSaturated rank p := by
  unfold sriqStep at h
  split at h
  · contradiction
  · exact ⟨‹_›,‹_›⟩

theorem sriqStep_open_sound {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {s : SearchState rank p} (h : sriqStep hs s = none) : p.Sat :=
  let hw := sriqStep_fair h
  sriq_blocked_saturated_sat hs hw.1 hw.2

/-- A closed search tree is a finite proof that every alternative fails. -/
inductive ConstrainedRefutation (rank : Rank) (p : Problem) : ConstrainedTree → Prop where
  | step {s} (t : ConstrainedTransition rank p s) :
      (∀ next ∈ t.branches, ConstrainedRefutation rank p next) → ConstrainedRefutation rank p s

theorem ConstrainedRefutation.sound {rank : Rank} {p : Problem} {s : ConstrainedTree}
    (h : ConstrainedRefutation rank p s) : ¬ s.Sat p := by
  induction h with
  | step t _ ih =>
    intro hs
    obtain ⟨next,hn,h⟩ := t.preserves hs
    exact ih next hn h


/-- Follow a submitted branch-index sequence and validate the terminal leaf.
The sequence is a certificate of a specific derivation. -/
def checkOpenTrace {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    (s : SearchState rank p) : List Nat → Bool
  | [] => (sriqStep hs s).isNone
  | index :: rest =>
    match sriqStep hs s with
    | none => false
    | some t => match t.branches.attach[index]? with
      | none => false
      | some next => checkOpenTrace hs (s.follow t next.val next.property) rest

theorem openTrace_sound {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {s : SearchState rank p} {trace : List Nat} (hc : checkOpenTrace hs s trace = true) :
    p.Sat := by
  induction trace generalizing s with
  | nil => exact sriqStep_open_sound (Option.isNone_iff_eq_none.mp hc)
  | cons index tail ih =>
    simp only [checkOpenTrace] at hc
    split at hc
    · contradiction
    · split at hc
      · contradiction
      · exact ih hc

private def enqueue {rank : Rank} {p : Problem} (state : SearchState rank p)
    (t : ConstrainedTransition rank p state.branch) : List (SearchState rank p) :=
  t.branches.attach.map fun next => state.follow t next.val next.property

/-- Validate a pre-order proof of closure. An entry records the exact
number of children of one expansion. The stack must be empty once the
certificate has been consumed. -/
def checkClosedTrace {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    (pending : List (SearchState rank p)) : List Nat → Bool
  | [] => pending.isEmpty
  | count :: rest => match pending with
    | [] => false
    | state :: queue =>
      match sriqStep hs state with
      | none => false
      | some t => (count == t.branches.length) &&
          checkClosedTrace hs (enqueue state t ++ queue) rest

theorem closedTrace_refutes {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {queue : List (SearchState rank p)} {trace : List Nat}
    (hc : checkClosedTrace hs queue trace = true) :
    ∀ state ∈ queue, ConstrainedRefutation rank p state.branch := by
  induction trace generalizing queue with
  | nil =>
    have e : queue = [] := List.isEmpty_iff.mp hc
    subst queue
    simp
  | cons count tail ih =>
    cases queue with
    | nil => contradiction
    | cons state queue =>
      simp only [checkClosedTrace] at hc
      split at hc
      · contradiction
      · rename_i t _
        have h := ih (Bool.and_eq_true_iff.mp hc).2
        intro x hx
        rcases List.mem_cons.mp hx with he | hx
        · subst x
          apply ConstrainedRefutation.step t
          intro next hn
          have hin : state.follow t next hn ∈ enqueue state t :=
            List.mem_map.mpr ⟨⟨next,hn⟩,List.mem_attach ..,rfl⟩
          exact h _ (List.mem_append_left _ hin)
        · exact h _ (List.mem_append_right _ hx)

def collisionRole : OrientedRole := ("urn:sabrina:termination:cardinality",false)

def collisionRoot : Concept := .conj (.min 2 collisionRole .top) (.max 1 collisionRole .top)

def collisionProblem : Problem := { root := collisionRoot }

theorem collisionFragment : collisionProblem.isSRIQ (fun _ => 0) = true := by decide

theorem infiniteChainFragment : infiniteChainRooted.isSRIQ (fun _ => 0) = true := by decide

theorem infiniteChain_via_search_trace : infiniteChainRooted.Sat := by
  apply openTrace_sound (hs := infiniteChainFragment) (s := SearchState.initial _ _)
    (trace := [1,1,0,1,1,0,0,1,1,0,1,1])
  decide +kernel

theorem collision_via_search_trace : ¬ collisionProblem.Sat := by
  let state := SearchState.initial (fun _ => 0) collisionProblem
  have checked : checkClosedTrace collisionFragment [state] [1,1,1,0] = true := by
    decide +kernel
  have closed := closedTrace_refutes checked state (List.mem_singleton_self _)
  exact fun h => closed.sound ((SearchState.initial_sat_iff _ _).mpr h)

theorem normalized_open_trace_sound {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} {hs : p.isSRIQ rank = true} {trace : List Nat}
    (hnorm : Normalize.normalizeWithDefs o = some (defs,p)) (hroot : p.root = .top)
    (h : checkOpenTrace hs (SearchState.initial rank p) trace = true) :
    Satisfiable datatypeMap o :=
  (Normalize.normalizeWithDefs_sat_iff hnorm).mpr
    ((satisfiable_iff_sat p hroot).mpr (openTrace_sound h))

theorem normalized_closed_trace_sound {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} {hs : p.isSRIQ rank = true} {trace : List Nat}
    (hnorm : Normalize.normalizeWithDefs o = some (defs,p)) (hroot : p.root = .top)
    (h : checkClosedTrace hs [SearchState.initial rank p] trace = true) :
    ¬ Satisfiable datatypeMap o := by
  intro ho
  have hp := (satisfiable_iff_sat p hroot).mp ((Normalize.normalizeWithDefs_sat_iff hnorm).mp ho)
  exact (closedTrace_refutes h _ (List.mem_singleton_self _)).sound
    ((SearchState.initial_sat_iff rank p).mpr hp)


private def collisionSourceProblem : Problem := {tbox := [⟨.top,collisionRoot⟩]}

def collisionSource : Ontology := collisionSourceProblem.toOntology.reverse

private theorem collisionSourceFragment : collisionSourceProblem.isSRIQ (fun _ => 0) = true := by
  decide

theorem collision_source_via_search_trace : ¬ Satisfiable datatypeMap collisionSource := by
  let trace := [2,0,1,1,1,2,0,1,1,2,0,1,1,0]
  have hnorm : Normalize.normalizeWithDefs collisionSource = some ([],collisionSourceProblem) := rfl
  apply normalized_closed_trace_sound (hs := collisionSourceFragment) (trace := trace) hnorm rfl
  decide +kernel

/-- Number of new children needed for a single application of a generator. -/
def generationArity : Concept → Nat
  | .some .. => 1
  | .min n .. => n
  | _ => 0

private def childSlots (p : Problem) : List (Concept × Nat) :=
  (clos p).flatMap fun c => (List.range (generationArity c)).map (c, ·)

def maxDegree (p : Problem) : Nat := ((clos p).map generationArity).sum

private theorem slots_length (p : Problem) : (childSlots p).length = maxDegree p := by
  simp [childSlots,maxDegree,List.length_flatMap]

def children (b : BlockedBranch) (x : b.Node) : List b.Node :=
  (List.finRange (b.size+1)).filter (fun y => decide (b.Child x y))

/-- The degree bound from the allocation slots. The hypothesis is an
injective allocation record assigning every live child one of its parent's
generation slots. This lemma does not derive that invariant from reachability. -/
theorem degree_le_of_slots (p : Problem) (x : b.Node) (slot : b.Node → Concept × Nat)
    (allowed : ∀ y ∈ b.children x, (slot y).1 ∈ clos p ∧ (slot y).2 < generationArity (slot y).1)
    (injective : ∀ y ∈ b.children x, ∀ z ∈ b.children x, slot y = slot z → y = z) :
    (b.children x).length ≤ maxDegree p := by
  have nd : (b.children x).Nodup := (List.nodup_finRange _).filter _
  have hm : ((b.children x).map slot).Nodup := by
    apply List.pairwise_map.mpr
    exact nd.imp_of_mem fun hy hz hneq heq => hneq (injective _ hy _ hz heq)
  have hle := hm.length_le_of_subset (l₂ := childSlots p) (by
    intro a ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    obtain ⟨hc,hn⟩ := allowed y hy
    exact List.mem_flatMap.mpr ⟨(slot y).1,hc,List.mem_map.mpr ⟨_,List.mem_range.mpr hn,rfl⟩⟩)
  simpa only [List.length_map,slots_length] using hle

theorem prune_size_decreases {drop : b.Node} (hd : drop ≠ 0) : b.pruneSize drop < b.size := by
  have sub : (b.retained drop).Sublist (List.finRange (b.size+1)) := List.filter_sublist
  have hlt : (b.retained drop).length < (List.finRange (b.size+1)).length := by
    have hle := sub.length_le
    by_cases he : (b.retained drop).length = (List.finRange (b.size+1)).length
    · have hmem := List.mem_finRange drop
      rw [← sub.eq_of_length he] at hmem
      exact ((mem_retained.mp hmem).1 rfl).elim
    · omega
  rw [List.length_finRange,←pruneLength hd] at hlt
  omega

/-- The relation used by the total recursion once accessibility of a
reachable search state has been established. -/
inductive SearchFollows {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    SearchState rank p → SearchState rank p → Prop where
  | child {s} {t : ConstrainedTransition rank p s.branch} (ht : sriqStep hs s = some t)
      {next : ConstrainedTree} (hn : next ∈ t.branches) :
      SearchFollows hs (s.follow t next hn) s

/-- The actual selector supplies a witness map for every successor it emits.
The map works simultaneously for all protected cardinality groups at each
center that survives the transition. -/
theorem SearchFollows.witnessMap {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {next current : SearchState rank p} (h : SearchFollows hs next current) :
    ∃ drop, Nonempty (WitnessMap current.branch next.branch drop) := by
  cases h with
  | @child _ t _ branch hn => exact t.protects branch hn

/-- Track an original vertex through actual search steps for as long as it
survives. A discarded vertex does not become a new ancestor in its lineage. -/
inductive VertexLineage {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    (s : SearchState rank p) → s.branch.tree.Node →
      (t : SearchState rank p) → t.branch.tree.Node → Prop where
  | start (s : SearchState rank p) (x : s.branch.tree.Node) : VertexLineage hs s x s x
  | follow {origin s t : SearchState rank p} {x : origin.branch.tree.Node}
      {y : s.branch.tree.Node} {z : t.branch.tree.Node} {drop : Option s.branch.tree.Node}
      (lineage : VertexLineage hs origin x s y) (step : SearchFollows hs t s)
      (map : WitnessMap s.branch t.branch drop) (survives : KeepsVertex s.branch.tree drop y)
      (image : map.redirect y = some z) : VertexLineage hs origin x t z

theorem VertexLineage.protected {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {s t : SearchState rank p} {x : s.branch.tree.Node} {y : t.branch.tree.Node}
    (lineage : VertexLineage hs s x t y) {r : OrientedRole} {c : Concept} {n : Nat}
    (h : s.branch.ProtectedWitnesses x r c n) : t.branch.ProtectedWitnesses y r c n := by
  induction lineage with
  | start => exact h
  | follow _ _ map survives image ih => exact map.protected survives image (ih h)

theorem VertexLineage.depth_eq {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {s t : SearchState rank p} {x : s.branch.tree.Node} {y : t.branch.tree.Node}
    (lineage : VertexLineage hs s x t y) : t.branch.tree.depth y = s.branch.tree.depth x := by
  induction lineage with
  | start => rfl
  | follow _ _ map survives image ih => exact (map.depth_eq survives image).trans ih

/-- A traversal certificate accounts for every child of each visited state.
`none` records an open terminal and `some n` records an expansion of arity
`n`, with zero recording a closed leaf. -/
def checkAccessibilityTrace {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    (pending : List (SearchState rank p)) : List (Option Nat) → Bool
  | [] => pending.isEmpty
  | visit :: rest => match pending with
    | [] => false
    | state :: queue =>
      match sriqStep hs state with
      | none => visit.isNone && checkAccessibilityTrace hs queue rest
      | some t => (visit == some t.branches.length) &&
          checkAccessibilityTrace hs (enqueue state t ++ queue) rest

theorem accessibilityTrace_sound {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {queue : List (SearchState rank p)} {trace : List (Option Nat)}
    (h : checkAccessibilityTrace hs queue trace = true) :
    ∀ state ∈ queue, Acc (SearchFollows hs) state := by
  induction trace generalizing queue with
  | nil =>
    have e : queue = [] := List.isEmpty_iff.mp h
    subst queue
    simp
  | cons visit tail ih =>
    cases queue with
    | nil => contradiction
    | cons state queue =>
      simp only [checkAccessibilityTrace] at h
      split at h
      · rename_i hstep
        intro s hmem
        rcases List.mem_cons.mp hmem with he | hmem
        · subst s
          refine ⟨state,?_⟩
          intro next hn
          cases hn with
          | child ho _ => rw [hstep] at ho; contradiction
        · exact ih (Bool.and_eq_true_iff.mp h).2 s hmem
      · rename_i t hstep
        have sub := ih (Bool.and_eq_true_iff.mp h).2
        intro s hmem
        rcases List.mem_cons.mp hmem with he | hmem
        · subst s
          refine ⟨state,?_⟩
          intro next hn
          cases hn with
          | child hother hk =>
            rw [hstep] at hother
            cases hother
            apply sub
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨⟨_,hk⟩,List.mem_attach ..,rfl⟩
        · exact sub s (List.mem_append_right _ hmem)

structure OpenBranch (rank : Rank) (p : Problem) where
  tree : BlockedBranch
  clashFree : tree.BlockedClashFree p
  saturated : tree.BlockedSaturated rank p

inductive SearchVerdict {rank : Rank} {p : Problem} (s : SearchState rank p) where
  | sat (leaf : OpenBranch rank p)
  | unsat (refutation : ConstrainedRefutation rank p s.branch)

private inductive Alternatives {rank : Rank} {p : Problem} (next : List ConstrainedTree) where
  | sat (leaf : OpenBranch rank p)
  | closed (proof : ∀ s ∈ next, ConstrainedRefutation rank p s)

private def checkAlternatives {rank : Rank} {p : Problem} {s : SearchState rank p}
    (t : ConstrainedTransition rank p s.branch)
    (visit : ∀ next (h : next ∈ t.branches), SearchVerdict (s.follow t next h))
    (children : List ConstrainedTree) (known : children ⊆ t.branches) :
    Alternatives (rank := rank) (p := p) children :=
  match children with
  | [] => .closed (by simp)
  | a :: rest =>
    match visit a (known (List.mem_cons_self ..)) with
    | .sat leaf => .sat leaf
    | .unsat ha =>
      match checkAlternatives t visit rest (fun _ h => known (List.mem_cons_of_mem _ h)) with
      | .sat leaf => .sat leaf
      | .closed hr => .closed (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hr x hx)

/-- Fuel-free recursion for accessible search states. Establishing
accessibility for every admitted initial state remains a separate obligation. -/
def decideAccessible {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true)
    {s : SearchState rank p} (acc : Acc (SearchFollows hs) s) : SearchVerdict s := by
  let A := {state : SearchState rank p // Acc (SearchFollows hs) state}
  let less : A → A → Prop := InvImage (SearchFollows hs) Subtype.val
  let wf : WellFounded less := ⟨fun a => InvImage.accessible Subtype.val a.property⟩
  let run (state : A) (visit : ∀ next, less next state → SearchVerdict next.val) :
      SearchVerdict state.val :=
    match h : sriqStep hs state.val with
    | none =>
      let complete := sriqStep_fair h
      .sat ⟨state.val.branch.tree.reblock,complete.1,complete.2⟩
    | some t =>
      match checkAlternatives t
        (fun next hn =>
          let smaller := SearchFollows.child h hn
          visit ⟨state.val.follow t next hn,state.property.inv smaller⟩ smaller)
        t.branches (fun _ h => h) with
      | .sat leaf => .sat leaf
      | .closed proof => .unsat (.step t proof)
  exact wf.fix run ⟨s,acc⟩

theorem decideAccessible_sat_iff {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    (a : Acc (SearchFollows hs) (SearchState.initial rank p)) :
    (∃ leaf, decideAccessible hs a = .sat leaf) ↔ p.Sat := by
  cases h : decideAccessible hs a with
  | sat leaf =>
    exact ⟨fun _ => sriq_blocked_saturated_sat hs leaf.clashFree leaf.saturated,fun _ => ⟨leaf,rfl⟩⟩
  | unsat ref =>
    exact ⟨by rintro ⟨_,h⟩; contradiction,
      fun hp => (ref.sound ((SearchState.initial_sat_iff rank p).mpr hp)).elim⟩

theorem decideAccessible_unsat_iff {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    (a : Acc (SearchFollows hs) (SearchState.initial rank p)) :
    (∃ ref, decideAccessible hs a = .unsat ref) ↔ ¬ p.Sat := by
  cases h : decideAccessible hs a with
  | sat leaf =>
    exact ⟨by rintro ⟨_,h⟩; contradiction,
      fun h => (h (sriq_blocked_saturated_sat hs leaf.clashFree leaf.saturated)).elim⟩
  | unsat ref =>
    exact ⟨fun _ hp => ref.sound ((SearchState.initial_sat_iff rank p).mpr hp),fun _ => ⟨ref,rfl⟩⟩

theorem decideAccessible_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} {hs : p.isSRIQ rank = true} (a : Acc (SearchFollows hs) (SearchState.initial rank p))
    (hnorm : Normalize.normalizeWithDefs o = some (defs,p)) (hroot : p.root = .top) :
    ((∃ leaf, decideAccessible hs a = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideAccessible hs a = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) := by
  have spec := (Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)
  exact ⟨(decideAccessible_sat_iff a).trans spec.symm,
    (decideAccessible_unsat_iff a).trans (not_congr spec.symm)⟩

private theorem infiniteChainAccessible :
    Acc (SearchFollows infiniteChainFragment) (SearchState.initial (fun _ => 0) infiniteChainRooted) := by
  apply accessibilityTrace_sound (hs := infiniteChainFragment)
    (trace := [some 2,some 0,some 2,some 0,some 1,some 2,some 0,some 2,some 0,some 2,some 1,
      some 2,some 0,some 2,some 0,some 1,some 2,some 0,some 2,some 0,none,some 0])
    (queue := [SearchState.initial _ _]) _ _ (List.mem_singleton_self _)
  decide +kernel

private theorem collisionAccessible :
    Acc (SearchFollows collisionFragment) (SearchState.initial (fun _ => 0) collisionProblem) := by
  apply accessibilityTrace_sound (hs := collisionFragment) (trace := [some 1,some 1,some 1,some 0])
    (queue := [SearchState.initial _ _]) _ _ (List.mem_singleton_self _)
  decide +kernel

theorem infiniteChain_accessible_verdict :
    ∃ leaf, decideAccessible infiniteChainFragment infiniteChainAccessible = .sat leaf :=
  (decideAccessible_sat_iff infiniteChainAccessible).mpr infiniteChain_via_search_trace

theorem collision_accessible_verdict :
    ∃ ref, decideAccessible collisionFragment collisionAccessible = .unsat ref :=
  (decideAccessible_unsat_iff collisionAccessible).mpr collision_via_search_trace

#guard (match decideAccessible infiniteChainFragment infiniteChainAccessible with
  | .sat _ => true
  | .unsat _ => false)

#guard (match decideAccessible collisionFragment collisionAccessible with
  | .sat _ => false
  | .unsat _ => true)


private def grandparentFixtureProblem : Problem :=
  { tbox := [⟨.top,.max 2 collisionRole .top⟩] }

private def grandparentFixture : ConstrainedTree :=
  let initial : ConstrainedTree := ⟨BlockedBranch.initial grandparentFixtureProblem,[]⟩
  let center := initial.appendFresh 0 (converse collisionRole) .top 1
  let family := center.appendFresh 1 collisionRole .top 2
  ⟨family.tree.addLabel 1 (.max 2 collisionRole .top), family.extraUnequal⟩

private def grandparentObligation : grandparentFixture.tree.MergeRequired where
  node := 1
  role := collisionRole
  filler := .top
  limit := 2
  active := active_iff.mp (by decide +kernel)
  label := by decide +kernel
  over := by decide +kernel

private def grandparentAlternatives : List ConstrainedTree :=
  (resolveMerge (rank := fun _ => 0) (p := grandparentFixtureProblem)
    grandparentFixture grandparentObligation).branches

/-- Three qualifying neighbors are reduced to two by merging a child with
the original predecessor. The fresh sibling inequality becomes an explicit
inequality between that predecessor and the other child. -/
theorem grandparent_preserves_count_and_inequality :
    (!grandparentAlternatives.isEmpty && grandparentAlternatives.all (fun s =>
      s.tree.qualifiedCount 1 collisionRole .top == 2 && s.extraUnequal.contains (0,2))) = true := by
  decide +kernel

/-! ### Step classification for well-founded termination -/

/-- Whether a generating concept already has a protected witness group at `x`.
Non-generating concepts are vacuously satisfied. -/
def GenProtected (s : ConstrainedTree) (x : s.tree.Node) : Concept → Prop
  | .some r c => s.ProtectedWitnesses x r c 1
  | .min n r c => s.ProtectedWitnesses x r c n
  | _ => True

theorem Anc.depth_lt {a x : b.Node} (h : b.Anc a x) : b.depth a < b.depth x := by
  induction h with
  | parent hc =>
    rw [depth_child hc]
    omega
  | step _ hc ih =>
    rw [depth_child hc]
    omega

/-- Geometric and monotonic progress classification of every branch emitted by
`sriqStep`. Each transition either enriches a surviving node in place, prunes
a non-root subtree by merging, or installs a protected witness group on an
unblocked node of bounded depth. -/
inductive StrictStep (rank : Rank) (p : Problem) (s t : ConstrainedTree) : Prop where
  | enrich (f : s.tree.Node → t.tree.Node)
      (hinj : ∀ a c, f a = f c → a = c)
      (hsurj : ∀ y, ∃ x, f x = y)
      (hdepth : ∀ z, t.tree.depth (f z) = s.tree.depth z)
      (hlabels : ∀ z, s.tree.labels z ⊆ t.tree.labels (f z))
      (hguards : ∀ z, s.tree.guardLabels z ⊆ t.tree.guardLabels (f z))
      (hdown : ∀ z, s.tree.down z ⊆ t.tree.down (f z))
      (hup : ∀ z, s.tree.up z ⊆ t.tree.up (f z))
      (hloops : ∀ z, s.tree.loops z ⊆ t.tree.loops (f z))
      (hprot : ∀ z r c n, s.ProtectedWitnesses z r c n → t.ProtectedWitnesses (f z) r c n)
      (hnew : ∃ z,
        (∃ c ∈ clos p, c ∉ s.tree.labels z ∧ c ∈ t.tree.labels (f z)) ∨
        (∃ g ∈ guards rank p, g ∉ s.tree.guardLabels z ∧ g ∈ t.tree.guardLabels (f z)) ∨
        (∃ r ∈ roleNames p,
          (r ∉ s.tree.down z ∧ r ∈ t.tree.down (f z)) ∨
          (r ∉ s.tree.up z ∧ r ∈ t.tree.up (f z)) ∨
          (r ∉ s.tree.loops z ∧ r ∈ t.tree.loops (f z))))
  | merge (drop : s.tree.Node) (hd : drop ≠ 0) (f : t.tree.Node → s.tree.Node)
      (hinj : ∀ x y, f x = f y → x = y)
      (hmem : ∀ y, f y ∈ s.tree.retained drop)
      (hsurj : ∀ x, x ∈ s.tree.retained drop → ∃ y, f y = x)
      (hdepth : ∀ y, t.tree.depth y = s.tree.depth (f y))
      (hlabels : ∀ y, s.tree.labels (f y) ⊆ t.tree.labels y)
      (hguards : ∀ y, s.tree.guardLabels (f y) ⊆ t.tree.guardLabels y)
      (hdown : ∀ y, s.tree.down (f y) ⊆ t.tree.down y)
      (hup : ∀ y, s.tree.up (f y) ⊆ t.tree.up y)
      (hloops : ∀ y, s.tree.loops (f y) ⊆ t.tree.loops y)
      (hprot : ∀ y r c n, s.ProtectedWitnesses (f y) r c n → t.ProtectedWitnesses y r c n)
  | generate (x : s.tree.Node) (hxDepth : s.tree.depth x ≤ maxDepth rank p)
      (gen : Concept) (hgenClos : gen ∈ clos p)
      (f : s.tree.Node → t.tree.Node)
      (hinj : ∀ a c, f a = f c → a = c)
      (hdepthOld : ∀ z, t.tree.depth (f z) = s.tree.depth z)
      (hdepthNew : ∀ y : t.tree.Node, (∀ z, f z ≠ y) → t.tree.depth y = s.tree.depth x + 1)
      (hlabels : ∀ z, s.tree.labels z ⊆ t.tree.labels (f z))
      (hguards : ∀ z, s.tree.guardLabels z ⊆ t.tree.guardLabels (f z))
      (hdown : ∀ z, s.tree.down z ⊆ t.tree.down (f z))
      (hup : ∀ z, s.tree.up z ⊆ t.tree.up (f z))
      (hloops : ∀ z, s.tree.loops z ⊆ t.tree.loops (f z))
      (hprot : ∀ z r c n, s.ProtectedWitnesses z r c n → t.ProtectedWitnesses (f z) r c n)
      (hnotBefore : ¬ GenProtected s x gen)
      (hprotAfter : GenProtected t (f x) gen)

private theorem ancestors_unfold (b : BlockedBranch) (x : b.Node) :
    b.ancestors x = if x = 0 then [] else b.parent x :: b.ancestors (b.parent x) := by
  rw [ancestors]
  split <;> rfl

private theorem depth_eq_of_same_tree {b₁ b₂ : BlockedBranch}
    (hs : b₁.size = b₂.size)
    (hp : ∀ x : b₁.Node, (b₁.parent x).val = (b₂.parent ⟨x.val, hs ▸ x.isLt⟩).val)
    (x : b₁.Node) : b₁.depth x = b₂.depth ⟨x.val, hs ▸ x.isLt⟩ := by
  unfold depth
  rw [ancestors_unfold b₁, ancestors_unfold b₂]
  by_cases hx : x = 0
  · subst x
    have h0 : (⟨(0 : b₁.Node).val, hs ▸ (0 : b₁.Node).isLt⟩ : b₂.Node) = 0 := Fin.ext rfl
    rw [ite_eq_left rfl, ite_eq_left h0]
    rfl
  · have hx2 : (⟨x.val, hs ▸ x.isLt⟩ : b₂.Node) ≠ 0 := fun h =>
      hx (Fin.ext (by simpa using congrArg Fin.val h))
    rw [ite_eq_right hx, ite_eq_right hx2]
    simp only [List.length_cons]
    have heq : b₂.parent ⟨x.val, hs ▸ x.isLt⟩ =
        ⟨(b₁.parent x).val, hs ▸ (b₁.parent x).isLt⟩ := Fin.ext (hp x).symm
    rw [heq]
    exact congrArg Nat.succ (depth_eq_of_same_tree hs hp (b₁.parent x))
termination_by x.val
decreasing_by exact b₁.parent_lt x hx

private theorem reblock_depth (b : BlockedBranch) (x : b.Node) :
    b.reblock.depth x = b.depth x :=
  depth_eq_of_same_tree (b₁ := b.reblock) (b₂ := b) rfl (fun _ => rfl) x

private theorem retained_reblock_iff {drop x : b.Node} :
    x ∈ b.reblock.retained drop ↔ x ∈ b.retained drop :=
  mem_retained.trans ((and_congr Iff.rfl (not_congr same_anc_reblock)).trans mem_retained.symm)

private theorem StrictStep.ofReblock {rank : Rank} {p : Problem} {s t : ConstrainedTree}
    (h : StrictStep rank p s.reblock t) : StrictStep rank p s t := by
  cases h with
  | enrich f hinj hsurj hdepth hlabels hguards hdown hup hloops hprot hnew =>
    exact .enrich f hinj hsurj (fun z => (hdepth z).trans (reblock_depth s.tree z))
      hlabels hguards hdown hup hloops hprot hnew
  | merge drop hd f hinj hmem hsurj hdepth hlabels hguards hdown hup hloops hprot =>
    exact .merge drop hd f hinj (fun y => retained_reblock_iff.mp (hmem y))
      (fun x hx => hsurj x (retained_reblock_iff.mpr hx))
      (fun y => (hdepth y).trans (reblock_depth s.tree (f y)))
      hlabels hguards hdown hup hloops hprot
  | generate x hxDepth gen hgenClos f hinj hdepthOld hdepthNew hlabels hguards hdown hup hloops
      hprot hnotBefore hprotAfter =>
    exact .generate x (reblock_depth s.tree x ▸ hxDepth) gen hgenClos f hinj
      (fun z => (hdepthOld z).trans (reblock_depth s.tree z))
      (fun y hy => (hdepthNew y hy).trans (congrArg Nat.succ (reblock_depth s.tree x)))
      hlabels hguards hdown hup hloops hprot hnotBefore hprotAfter

private def StrictTransition {rank : Rank} {p : Problem} {b : BlockedBranch}
    (t : BlockedTransition rank p b) : Prop :=
  ∀ (xs : List (b.Node × b.Node)) (next : ConstrainedTree),
    next ∈ (t.lift xs).branches → StrictStep rank p ⟨b, xs⟩ next

private def Inspection.StepProp {rank : Rank} {p : Problem} {b : BlockedBranch} {done : Prop}
    (P : BlockedTransition rank p b → Prop) (i : Inspection rank p b done) : Prop :=
  ∀ t, i = .step t → P t

private theorem Inspection.StepProp.satisfied {rank : Rank} {p : Problem} {b : BlockedBranch}
    {done : Prop} {P : BlockedTransition rank p b → Prop} (h : done) :
    (Inspection.satisfied (rank := rank) (p := p) (b := b) h).StepProp P := by
  intro _ heq; cases heq

private theorem Inspection.StepProp.merge {rank : Rank} {p : Problem} {b : BlockedBranch}
    {done : Prop} {P : BlockedTransition rank p b → Prop} (m : b.MergeRequired) :
    (Inspection.merge (rank := rank) (p := p) (b := b) (done := done) m).StepProp P := by
  intro _ heq; cases heq

private theorem Inspection.StepProp.map {rank : Rank} {p : Problem} {b : BlockedBranch}
    {P Q : Prop} {Pred : BlockedTransition rank p b → Prop} {f : P → Q}
    {i : Inspection rank p b P} (hi : i.StepProp Pred) : (i.map f).StepProp Pred := by
  intro t ht
  cases i with
  | satisfied _ => cases ht
  | merge _ => cases ht
  | step t' =>
    cases ht
    exact hi t rfl

private theorem Inspection.StepProp.thenCheck {rank : Rank} {p : Problem} {b : BlockedBranch}
    {P Q : Prop} {Pred : BlockedTransition rank p b → Prop}
    {first : Inspection rank p b P} {rest : P → Inspection rank p b Q}
    (h1 : first.StepProp Pred) (h2 : ∀ h, (rest h).StepProp Pred) :
    (first.thenCheck rest).StepProp Pred := by
  intro t ht
  cases first with
  | satisfied h => exact Inspection.StepProp.map (h2 h) t ht
  | step t' =>
    cases ht
    exact h1 t rfl
  | merge _ => cases ht

private theorem Inspection.StepProp.forAll {rank : Rank} {p : Problem} {b : BlockedBranch}
    {α : Type} {P : α → Prop} {Pred : BlockedTransition rank p b → Prop}
    {xs : List α} {f : ∀ a ∈ xs, Inspection rank p b (P a)}
    (hf : ∀ a (ha : a ∈ xs), (f a ha).StepProp Pred) :
    (Inspection.forAll xs f).StepProp Pred := by
  induction xs with
  | nil => exact Inspection.StepProp.satisfied _
  | cons a tail ih =>
    apply Inspection.StepProp.map
    apply Inspection.StepProp.thenCheck (hf a (List.mem_cons_self ..))
    intro _
    exact ih (fun z hz => hf z (List.mem_cons_of_mem _ hz))

private theorem Inspection.StepProp.forNodes {rank : Rank} {p : Problem} {b : BlockedBranch}
    {P : b.Node → Prop} {Pred : BlockedTransition rank p b → Prop}
    {f : ∀ x, Inspection rank p b (P x)} (hf : ∀ x, (f x).StepProp Pred) :
    (Inspection.forNodes f).StepProp Pred :=
  Inspection.StepProp.map (Inspection.StepProp.forAll fun x _ => hf x)

private theorem Inspection.StepProp.assuming {rank : Rank} {p : Problem} {b : BlockedBranch}
    {P Q : Prop} [Decidable P] {Pred : BlockedTransition rank p b → Prop}
    {f : P → Inspection rank p b Q} (hf : ∀ h, (f h).StepProp Pred) :
    (Inspection.assuming f).StepProp Pred := by
  unfold Inspection.assuming
  split
  · rename_i h
    exact Inspection.StepProp.map (hf h)
  · exact Inspection.StepProp.satisfied _

private theorem Inspection.StepProp.check {rank : Rank} {p : Problem} {b : BlockedBranch}
    {goal : Prop} [Decidable goal] {Pred : BlockedTransition rank p b → Prop}
    {expand : ¬ goal → BlockedTransition rank p b}
    (hf : ∀ h : ¬ goal, Pred (expand h)) :
    (Inspection.check goal expand).StepProp Pred := by
  unfold Inspection.check
  split
  · exact Inspection.StepProp.satisfied _
  · rename_i h
    intro t ht
    cases ht
    exact hf h

private theorem addLabel_strict {rank : Rank} {p : Problem} {x : b.Node} {c : Concept}
    (hc : c ∈ clos p) (hnot : c ∉ b.labels x) (xs : List (b.Node × b.Node)) :
    StrictStep rank p ⟨b, xs⟩ ⟨b.addLabel x c, xs⟩ := by
  let wm : WitnessMap ⟨b, xs⟩ ⟨b.addLabel x c, xs⟩ none :=
    extensionWitnessMap id (fun h => h) rfl (fun h => h) (fun h => h)
      (fun h => addLabel_mem.mpr (.inr h)) (fun h => h)
  refine .enrich id (fun _ _ h => h) (fun y => ⟨y, rfl⟩)
    (fun z => depth_eq_of_same_tree (b₁ := b.addLabel x c) (b₂ := b) rfl (fun _ => rfl) z)
    (fun z _ hd => addLabel_mem.mpr (.inr hd))
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (fun z r d n hp => wm.protected trivial rfl hp)
    ⟨x, .inl ⟨c, hc, hnot, addLabel_mem.mpr (.inl ⟨rfl, rfl⟩)⟩⟩

private theorem addGuard_strict {rank : Rank} {p : Problem} {x : b.Node} {g : Guard}
    (hg : g ∈ guards rank p) (hnot : g ∉ b.guardLabels x) (xs : List (b.Node × b.Node)) :
    StrictStep rank p ⟨b, xs⟩ ⟨b.addGuard x g, xs⟩ := by
  let wm : WitnessMap ⟨b, xs⟩ ⟨b.addGuard x g, xs⟩ none :=
    extensionWitnessMap id (fun h => h) rfl (fun h => h) (fun h => h) (fun h => h) (fun h => h)
  refine .enrich id (fun _ _ h => h) (fun y => ⟨y, rfl⟩)
    (fun z => depth_eq_of_same_tree (b₁ := b.addGuard x g) (b₂ := b) rfl (fun _ => rfl) z)
    (fun _ _ h => h)
    (fun z _ hk => addGuard_mem.mpr (.inr hk))
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h)
    (fun z r d n hp => wm.protected trivial rfl hp)
    ⟨x, .inr (.inl ⟨g, hg, hnot, addGuard_mem.mpr (.inl ⟨rfl, rfl⟩)⟩)⟩

private theorem addEdge_has_edge {r : OrientedRole} {x y : b.Node} (hloc : b.Local x y) :
    (b.addEdge r x y).Edge r x y := by
  rcases r with ⟨r, _ | _⟩
  · exact addNamedEdge_iff.mpr (.inr ⟨rfl, rfl, rfl, hloc⟩)
  · apply ((b.addEdge (r, true) x y).edge_converse (r, false) y x).mpr
    have hloc' : b.Local y x :=
      hloc.elim (fun h => .inl h.symm) (fun h => h.elim (fun h => .inr (.inr h)) (fun h => .inr (.inl h)))
    exact addNamedEdge_iff.mpr (.inr ⟨rfl, rfl, rfl, hloc'⟩)

private theorem addEdge_strict {rank : Rank} {p : Problem} {r : OrientedRole} {x y : b.Node}
    (hloc : b.Local x y) (hr : r.1 ∈ roleNames p) (hnot : ¬ b.Edge r x y)
    (xs : List (b.Node × b.Node)) :
    StrictStep rank p ⟨b, xs⟩ ⟨b.addEdge r x y, xs⟩ := by
  let wm : WitnessMap ⟨b, xs⟩ ⟨b.addEdge r x y, xs⟩ none :=
    extensionWitnessMap id (fun h => h) rfl (fun h => h) addEdge_retains (fun h => h) (fun h => h)
  have hsubDown : ∀ z, b.down z ⊆ (b.addEdge r x y).down z := by
    intro z s hs
    exact (mem_addWhere _).mpr (.inr hs)
  have hsubUp : ∀ z, b.up z ⊆ (b.addEdge r x y).up z := by
    intro z s hs
    exact (mem_addWhere _).mpr (.inr hs)
  have hsubLoops : ∀ z, b.loops z ⊆ (b.addEdge r x y).loops z := by
    intro z s hs
    exact (mem_addWhere _).mpr (.inr hs)
  have hadded : (b.addEdge r x y).Edge r x y := addEdge_has_edge hloc
  have hnew : ∃ z : b.Node,
      (∃ c ∈ clos p, c ∉ b.labels z ∧ c ∈ (b.addEdge r x y).labels z) ∨
      (∃ g ∈ guards rank p, g ∉ b.guardLabels z ∧ g ∈ (b.addEdge r x y).guardLabels z) ∨
      (∃ s ∈ roleNames p,
        (s ∉ b.down z ∧ s ∈ (b.addEdge r x y).down z) ∨
        (s ∉ b.up z ∧ s ∈ (b.addEdge r x y).up z) ∨
        (s ∉ b.loops z ∧ s ∈ (b.addEdge r x y).loops z)) := by
    rcases hloc with rfl | hxy | hyx
    · have hn : r.1 ∉ b.loops x := fun h => hnot ((edge_loop_iff b r x).mpr h)
      have ha : r.1 ∈ (b.addEdge r x x).loops x := (edge_loop_iff (b.addEdge r x x) r x).mp hadded
      exact ⟨x, .inr (.inr ⟨r.1, hr, .inr (.inr ⟨hn, ha⟩)⟩)⟩
    · have hn : ¬ b.Down r y := fun h => hnot ((edge_child_iff hxy).mpr h)
      have ha : (b.addEdge r x y).Down r y := (edge_child_iff (b := b.addEdge r x y) hxy).mp hadded
      rcases r with ⟨r, _ | _⟩
      · exact ⟨y, .inr (.inr ⟨r, hr, .inl ⟨hn, ha⟩⟩)⟩
      · exact ⟨y, .inr (.inr ⟨r, hr, .inr (.inl ⟨hn, ha⟩)⟩)⟩
    · have hnot' : ¬ b.Edge (converse r) y x := fun h => hnot ((b.edge_converse r x y).mp h)
      have hadded' : (b.addEdge r x y).Edge (converse r) y x :=
        ((b.addEdge r x y).edge_converse r x y).mpr hadded
      have hn : ¬ b.Down (converse r) x := fun h => hnot' ((edge_child_iff hyx).mpr h)
      have ha : (b.addEdge r x y).Down (converse r) x :=
        (edge_child_iff (b := b.addEdge r x y) hyx).mp hadded'
      rcases r with ⟨r, _ | _⟩
      · exact ⟨x, .inr (.inr ⟨r, hr, .inr (.inl ⟨hn, ha⟩)⟩)⟩
      · exact ⟨x, .inr (.inr ⟨r, hr, .inl ⟨hn, ha⟩⟩)⟩
  exact .enrich id (fun _ _ h => h) (fun z => ⟨z, rfl⟩)
    (fun z => depth_eq_of_same_tree (b₁ := b.addEdge r x y) (b₂ := b) rfl (fun _ => rfl) z)
    (fun _ _ h => h) (fun _ _ h => h) hsubDown hsubUp hsubLoops
    (fun z s d n hp => wm.protected trivial rfl hp) hnew

private theorem labelStep_strict {rank : Rank} {p : Problem} {x : b.Node} {c : Concept}
    {hc : b.Within rank p → c ∈ clos p} {derive} (hw : b.Within rank p) (hnot : c ∉ b.labels x) :
    StrictTransition (labelStep x c hc derive) := by
  intro xs next hn
  obtain rfl := List.mem_singleton.mp hn
  exact addLabel_strict (hc hw) hnot xs

private theorem guardStep_strict {rank : Rank} {p : Problem} {x : b.Node} {g : Guard}
    {hg : b.Within rank p → g ∈ guards rank p} {derive} (hw : b.Within rank p)
    (hnot : g ∉ b.guardLabels x) :
    StrictTransition (guardStep x g hg derive) := by
  intro xs next hn
  obtain rfl := List.mem_singleton.mp hn
  exact addGuard_strict (hg hw) hnot xs

private theorem splitStep_strict {rank : Rank} {p : Problem} {x : b.Node} {c d : Concept}
    {hc : b.Within rank p → c ∈ clos p} {hd : b.Within rank p → d ∈ clos p} {derive}
    (hw : b.Within rank p) (hnot : ¬ (c ∈ b.labels x ∨ d ∈ b.labels x)) :
    StrictTransition (splitStep x c d hc hd derive) := by
  intro xs next hn
  simp only [splitStep, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact addLabel_strict (hc hw) (fun h => hnot (.inl h)) xs
  · exact addLabel_strict (hd hw) (fun h => hnot (.inr h)) xs

private theorem edgeStep_strict {rank : Rank} {p : Problem} {r : OrientedRole} {x y : b.Node}
    {hr : b.Within rank p → r.1 ∈ roleNames p} {entails} (hw : b.Within rank p)
    (hloc : b.Local x y) (hnot : ¬ b.Edge r x y) :
    StrictTransition (edgeStep r x y hr entails) := by
  intro xs next hn
  obtain rfl := List.mem_singleton.mp hn
  exact addEdge_strict hloc (hr hw) hnot xs

private theorem generate_strict {rank : Rank} {p : Problem} {x : b.Node}
    {r : OrientedRole} {c gen : Concept} {n : Nat}
    {hc : b.Within rank p → c ∈ clos p} {hr : b.Within rank p → r.1 ∈ roleNames p} {ensure}
    (hxDepth : b.depth x ≤ maxDepth rank p) (hgenClos : gen ∈ clos p)
    (hnotBefore : ∀ xs, ¬ GenProtected ⟨b, xs⟩ x gen)
    (hprotAfter : ∀ xs, GenProtected (ConstrainedTree.appendFresh ⟨b, xs⟩ x r c n) (oldNode n x) gen) :
    StrictTransition (generate x r c n hc hr ensure) := by
  intro xs next hn
  obtain rfl := List.mem_singleton.mp hn
  let wm := appendFresh_map ⟨b, xs⟩ x r c n
  have hdepthOld : ∀ z : b.Node, (b.appendChildren n x r c).depth (oldNode n z) = b.depth z :=
    fun z => wm.depth_eq trivial rfl
  refine .generate x hxDepth gen hgenClos (oldNode n) (fun _ _ h => oldNode_inj h) hdepthOld ?_
    (fun z d hd => by simpa only [ConstrainedTree.appendFresh, appendChildren, onExtended_old] using hd)
    (fun z g hg => by simpa only [ConstrainedTree.appendFresh, appendChildren, onExtended_old] using hg)
    (fun z s hs => by simpa only [ConstrainedTree.appendFresh, appendChildren, onExtended_old] using hs)
    (fun z s hs => by simpa only [ConstrainedTree.appendFresh, appendChildren, onExtended_old] using hs)
    (fun z s hs => by simpa only [ConstrainedTree.appendFresh, appendChildren, onExtended_old] using hs)
    (fun z r' c' n' hp => wm.protected trivial rfl hp)
    (hnotBefore xs) (hprotAfter xs)
  intro y hy
  rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨w, rfl⟩
  · exact (hy z rfl).elim
  · have hch : (b.appendChildren n x r c).Child (oldNode n x) (b.newNode w) :=
      appendChild_new.mpr rfl
    change (b.appendChildren n x r c).depth (b.newNode w) = b.depth x + 1
    rw [depth_child hch, hdepthOld x]

private theorem compact_source {drop : b.Node} (hd : drop ≠ 0) (y : b.Pruned drop) :
    compact hd (source_mem hd y) = y :=
  source_inj hd (source_compact hd (source_mem hd y))

private theorem mergeWithSibling_strict {rank : Rank} {p : Problem} {s : ConstrainedTree}
    {keep drop : s.tree.Node} (shape : s.tree.SiblingPair (keep, drop)) (hn : keep ≠ drop)
    (allowed : ¬ s.RecordedDistinct keep drop) :
    StrictStep rank p s (mergeWithSibling s keep drop shape hn) := by
  let hd := shape.2.1
  let hk := retained_sibling shape.1 hd hn shape.2.2
  let wm := siblingWitnessMap s keep drop shape hn allowed
  have hmap (y : (mergeWithSibling s keep drop shape hn).tree.Node) :
      wm.redirect (source hd y) = some y := by
    change siblingIndex hd hk (source hd y) = some y
    rw [siblingIndex_kept hd hk (source_mem hd y), compact_source hd y]
    rfl
  exact .merge drop hd (source hd) (fun _ _ h => source_inj hd h) (source_mem hd)
    (fun x hx => ⟨compact hd hx, source_compact hd hx⟩)
    (fun y => wm.depth_eq (source_mem hd y) (hmap y))
    (fun y c hc => (copySiblings_mem hd).mpr (.inl hc))
    (fun y g hg => (copySiblings_mem hd).mpr (.inl hg))
    (fun y r hr => (copySiblings_mem hd).mpr (.inl hr))
    (fun y r hr => (copySiblings_mem hd).mpr (.inl hr))
    (fun y r hr => (copySiblings_mem hd).mpr (.inl hr))
    (fun y r c n hp => wm.protected (source_mem hd y) (hmap y) hp)

private theorem mergeAncestor_strict {rank : Rank} {p : Problem} {s : ConstrainedTree}
    {keep drop : s.tree.Node} (hd : drop ≠ 0) (shape : s.tree.AncestorMergeShape keep drop)
    (allowed : ¬ s.RecordedDistinct keep drop) :
    StrictStep rank p s (mergeAncestor s keep drop hd shape) := by
  let hk := ancestor_retained hd (mergeShape_anc hd shape)
  let wm := ancestorWitnessMap s keep drop hd shape allowed
  have hmap (y : (mergeAncestor s keep drop hd shape).tree.Node) :
      wm.redirect (source hd y) = some y := by
    change siblingIndex hd hk (source hd y) = some y
    rw [siblingIndex_kept hd hk (source_mem hd y), compact_source hd y]
    rfl
  exact .merge drop hd (source hd) (fun _ _ h => source_inj hd h) (source_mem hd)
    (fun x hx => ⟨compact hd hx, source_compact hd hx⟩)
    (fun y => wm.depth_eq (source_mem hd y) (hmap y))
    (fun y c hc => (copySiblings_mem hd).mpr (.inl hc))
    (fun y g hg => (copySiblings_mem hd).mpr (.inl hg))
    (fun y r hr => List.mem_append_left _ hr)
    (fun y r hr => List.mem_append_left _ hr)
    (fun y r hr => List.mem_append_left _ ((copySiblings_mem hd).mpr (.inl hr)))
    (fun y r c n hp => wm.protected (source_mem hd y) (hmap y) hp)

private theorem resolveMerge_strict {rank : Rank} {p : Problem} {s : ConstrainedTree}
    (m : s.tree.MergeRequired) {next : ConstrainedTree}
    (hn : next ∈ (resolveMerge (rank := rank) (p := p) s m).branches) :
    StrictStep rank p s next := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hn
  have filtered := List.mem_filter.mp q.property
  have limits := m.pair_mem.mp filtered.1
  have extra := filtered.2
  simp only [Bool.and_eq_true, Bool.not_eq_true', contains_false] at extra
  have allowed : ¬ s.RecordedDistinct q.val.1 q.val.2 := by
    rintro ((h | h) | (h | h))
    · exact limits.2.2.2.1 h
    · exact extra.1 h
    · exact limits.2.2.2.2 h
    · exact extra.2 h
  unfold MergeRequired.alternative mergeLocalPair
  split
  · exact mergeWithSibling_strict _ _ allowed
  · split
    · exact mergeAncestor_strict _ _ allowed
    · exact mergeAncestor_strict _ _ (fun h => allowed h.symm)

private theorem inspectLabels_strict {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (hw : b.Within rank p) :
    (inspectLabels (b := b) hi).StepProp StrictTransition := by
  unfold inspectLabels
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.assuming; intro _
  apply Inspection.StepProp.forAll; intro c hc
  cases c with
  | conj a d =>
    dsimp [inspectLabel]
    apply Inspection.StepProp.thenCheck
    · exact Inspection.StepProp.check (fun hnot => by
        unfold expandConj; exact labelStep_strict hw hnot)
    · intro _
      exact Inspection.StepProp.check (fun hnot => by
        unfold expandConj; exact labelStep_strict hw hnot)
  | disj a d =>
    dsimp [inspectLabel, LabelLocal]
    exact Inspection.StepProp.check (fun hnot => by
      unfold expandDisj; exact splitStep_strict hw hnot)
  | all r d =>
    dsimp [inspectLabel, LabelLocal]
    exact Inspection.StepProp.check (fun hnot => by
      unfold startGuard; exact guardStep_strict hw hnot)
  | self r sign =>
    cases sign with
    | false => dsimp [inspectLabel]; exact Inspection.StepProp.satisfied _
    | true =>
      dsimp [inspectLabel, LabelLocal]
      exact Inspection.StepProp.check (fun hnot => by
        unfold expandSelf; exact edgeStep_strict hw (.inl rfl) hnot)
  | max n r d =>
    dsimp [inspectLabel]
    apply Inspection.StepProp.forNodes; intro y
    apply Inspection.StepProp.assuming; intro _
    exact Inspection.StepProp.check (fun hnot => by
      unfold expandMaxQual; exact splitStep_strict hw hnot)
  | _ => dsimp [inspectLabel]; exact Inspection.StepProp.satisfied _

private theorem inspectTBox_strict {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    (inspectTBox (rank := rank) (p := p) (b := b)).StepProp StrictTransition := by
  unfold inspectTBox
  apply Inspection.StepProp.forAll; intro q hq
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.assuming; intro _
  exact Inspection.StepProp.check (fun hnot => by
    unfold expandTBox; exact splitStep_strict hw hnot)

private theorem inspectRules_strict {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    (inspectRules (rank := rank) (p := p) (b := b)).StepProp StrictTransition := by
  unfold inspectRules
  apply Inspection.StepProp.forAll; intro q hq
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.forNodes; intro y
  apply Inspection.StepProp.assuming; intro he
  exact Inspection.StepProp.check (fun hnot => by
    unfold expandRoleRule; exact edgeStep_strict hw he.local hnot)

private theorem inspectReflexive_strict {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    (inspectReflexive (rank := rank) (p := p) (b := b)).StepProp StrictTransition := by
  unfold inspectReflexive
  apply Inspection.StepProp.forAll; intro r hr
  apply Inspection.StepProp.forNodes; intro x
  exact Inspection.StepProp.check (fun hnot => by
    unfold expandReflexive; exact edgeStep_strict hw (.inl rfl) hnot)

private theorem inspectGuardSteps_strict {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    (inspectGuardSteps (rank := rank) (p := p) (b := b) hw).StepProp StrictTransition :=
  Inspection.StepProp.map <|
    Inspection.StepProp.forAll fun _ _ =>
    Inspection.StepProp.forNodes fun _ =>
    Inspection.StepProp.forNodes fun _ =>
    Inspection.StepProp.assuming fun _ =>
    Inspection.StepProp.forAll fun _ _ =>
    Inspection.StepProp.forAll fun _ _ =>
    Inspection.StepProp.check fun hnot => by
      unfold advanceGuard; exact guardStep_strict hw hnot

private theorem inspectGuardAccept_strict {rank : Rank} {p : Problem} (hw : b.Within rank p) :
    (inspectGuardAccept (rank := rank) (p := p) (b := b)).StepProp StrictTransition := by
  unfold inspectGuardAccept
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.forAll; intro g hg
  apply Inspection.StepProp.assuming; intro _
  exact Inspection.StepProp.check (fun hnot => by
    unfold acceptGuard; exact labelStep_strict hw hnot)

private theorem inspectUpperBounds_strict {rank : Rank} {p : Problem} :
    (inspectUpperBounds (rank := rank) (p := p) (b := b)).StepProp StrictTransition := by
  unfold inspectUpperBounds
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.assuming; intro hx
  apply Inspection.StepProp.forAll; intro c hc
  cases c with
  | max n r d =>
    dsimp [inspectUpper]
    split
    · exact Inspection.StepProp.merge _
    · exact Inspection.StepProp.satisfied _
  | _ => dsimp [inspectUpper]; exact Inspection.StepProp.satisfied _

private theorem inspectWitnesses_strict {rank : Rank} {p : Problem}
    (hw : b.Within rank p) :
    (inspectWitnesses (rank := rank) (p := p) (b := b.reblock)).StepProp StrictTransition := by
  unfold inspectWitnesses
  apply Inspection.StepProp.forNodes; intro x
  apply Inspection.StepProp.assuming; intro hx
  have hdepth : b.reblock.depth x ≤ maxDepth rank p :=
    (reblock_depth b x).symm ▸ unblocked_depth_le hw hx
  apply Inspection.StepProp.forAll; intro c hc
  have hclos : c ∈ clos p := hw.labels x hc
  cases c with
  | some r d =>
    dsimp [inspectWitness]
    apply Inspection.StepProp.map
    exact Inspection.StepProp.check fun hnot => by
      unfold generateSome
      exact generate_strict hdepth hclos
        (fun xs hp => hnot (ConstrainedTree.ProtectedWitnesses.count hp))
        (fun xs => ConstrainedTree.appendFresh_protected ⟨b.reblock, xs⟩ x r d 1)
  | min n r d =>
    dsimp [inspectWitness]
    apply Inspection.StepProp.map
    exact Inspection.StepProp.check fun hnot => by
      unfold generateMin
      exact generate_strict hdepth hclos
        (fun xs hp => hnot (ConstrainedTree.ProtectedWitnesses.count hp))
        (fun xs => ConstrainedTree.appendFresh_protected ⟨b.reblock, xs⟩ x r d n)
  | _ => dsimp [inspectWitness]; exact Inspection.StepProp.satisfied _

private theorem sweep_step_strict {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (b : BlockedBranch) (hw : b.Within rank p) (root : p.root ∈ b.labels 0)
    (bt : BlockedTransition rank p b.reblock)
    (hsw : sweep hi b hw root = .step bt) : StrictTransition bt := by
  unfold sweep at hsw
  by_cases hcf : b.reblock.clashFreeCheck p = true
  · simp only [hcf, ↓reduceDIte] at hsw
    have hwr := reblock_within hw
    have hall : ((inspectLabels (b := b.reblock) hi).thenCheck fun _ =>
      inspectTBox.thenCheck fun _ => inspectRules.thenCheck fun _ =>
        inspectReflexive.thenCheck fun _ => (inspectGuardSteps hwr).thenCheck fun _ =>
          inspectGuardAccept.thenCheck fun _ => inspectUpperBounds.thenCheck fun _ =>
            inspectWitnesses).StepProp StrictTransition :=
      Inspection.StepProp.thenCheck (inspectLabels_strict hi hwr) fun _ =>
      Inspection.StepProp.thenCheck (inspectTBox_strict hwr) fun _ =>
      Inspection.StepProp.thenCheck (inspectRules_strict hwr) fun _ =>
      Inspection.StepProp.thenCheck (inspectReflexive_strict hwr) fun _ =>
      Inspection.StepProp.thenCheck (inspectGuardSteps_strict hwr) fun _ =>
      Inspection.StepProp.thenCheck (inspectGuardAccept_strict hwr) fun _ =>
      Inspection.StepProp.thenCheck inspectUpperBounds_strict fun _ =>
      inspectWitnesses_strict hw
    split at hsw
    · rename_i bt' hres
      cases hsw
      exact hall bt hres
    · cases hsw
    · cases hsw
  · simp only [hcf] at hsw
    cases hsw
    intro xs next hn
    exact (List.not_mem_nil hn).elim

/-- Every successor emitted by `sriqStep` satisfies the strict-progress
classification `StrictStep`. -/
theorem SearchFollows.strictStep {rank : Rank} {p : Problem} {hs : p.isSRIQ rank = true}
    {next current : SearchState rank p} (h : SearchFollows hs next current) :
    StrictStep rank p current.branch next.branch := by
  cases h with
  | @child _ tr ht branch hn =>
    change StrictStep rank p current.branch branch
    unfold sriqStep inspectSRIQ at ht
    by_cases hex : ∃ q ∈ current.branch.extraUnequal, q.1 = q.2
    · simp only [hex, ↓reduceDIte] at ht
      cases ht
      exact (List.not_mem_nil hn).elim
    · simp only [hex, ↓reduceDIte] at ht
      cases hsw : sweep (p.sriqInput hs) current.branch.tree current.within current.root with
      | saturated _ _ =>
        simp [hsw] at ht
      | merge m =>
        simp only [hsw, Option.some.injEq] at ht
        cases ht
        exact StrictStep.ofReblock (resolveMerge_strict (s := current.branch.reblock) m hn)
      | step bt =>
        simp only [hsw, Option.some.injEq] at ht
        cases ht
        exact StrictStep.ofReblock
          (sweep_step_strict (p.sriqInput hs) current.branch.tree current.within current.root bt hsw
            current.branch.extraUnequal branch hn)

#print axioms reblock_valid
#print axioms blocked_of_depth_gt
#print axioms Realizes.mergeSiblings
#print axioms ConstrainedTree.Realizes.mergeAncestor
#print axioms resolveMerge
#print axioms sriqStep_fair
#print axioms ConstrainedTree.appendFresh_protected
#print axioms WitnessMap.protected
#print axioms WitnessMap.depth_eq
#print axioms SearchFollows.witnessMap
#print axioms SearchFollows.strictStep
#print axioms VertexLineage.protected
#print axioms VertexLineage.depth_eq
#print axioms grandparent_preserves_count_and_inequality
#print axioms ConstrainedRefutation.sound
#print axioms infiniteChain_via_search_trace
#print axioms collision_via_search_trace
#print axioms collision_source_via_search_trace
#print axioms decideAccessible_sat_iff
#print axioms decideAccessible_unsat_iff
#print axioms decideAccessible_ontology_iff
#print axioms infiniteChain_accessible_verdict
#print axioms collision_accessible_verdict

end BlockedBranch

#print axioms blockedRefutation_sound

end Sabrina.OWL2.SROIQD.Termination
