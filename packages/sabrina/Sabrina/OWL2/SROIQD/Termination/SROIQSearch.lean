import Sabrina.OWL2.SROIQD.Termination.SROIQOps
import Sabrina.OWL2.DecisionProcedure

/-!
Checked tableau search, fairness, strict step classification, and fuel-free
accessibility-driven decision procedure for full cyclic `SROIQ` (TBox, RBox
with regular role chains, inverse roles, qualified number restrictions,
nominals, ABox assertions, `HasKey` axioms, and the NN-rule).
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank)
open Sabrina.RoleChains.TransitivePaths (converse_converse)

namespace BlockedForest

/-! ### Boolean decidable helpers on `BlockedForest` -/

def edgeBool (b : BlockedForest) (r : OrientedRole) (x y : b.Node) : Bool :=
  (x == y && (b.loops x).contains r.1) ||
  (b.isRoot x && b.isRoot y &&
    (if r.2 then b.rootEdges.contains (r.1, y, x) else b.rootEdges.contains (r.1, x, y))) ||
  (!b.isRoot y && b.parent y == x &&
    (if r.2 then (b.up y).contains r.1 else (b.down y).contains r.1)) ||
  (!b.isRoot x && b.parent x == y &&
    (if r.2 then (b.down x).contains r.1 else (b.up x).contains r.1)) ||
  (b.toRoot x).contains (r, y) ||
  (b.toRoot y).contains (converse r, x)

theorem edgeBool_iff {b : BlockedForest} {r : OrientedRole} {x y : b.Node} :
    b.edgeBool r x y = true ↔ b.Edge r x y := by
  unfold edgeBool Edge Child RootEdge Down
  rcases r with ⟨rn, _ | _⟩ <;>
    simp only [converse, Bool.not_false, Bool.not_true, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem, Bool.false_eq_true, ↓reduceIte] <;>
    grind

def boundToBool (b : BlockedForest) (ind : Individual) (x : b.Node) : Bool :=
  match ind with
  | .named a => b.noms.contains (a, x)
  | .anonymous d l => b.anons.contains ((d, l), x)

theorem boundToBool_iff {b : BlockedForest} {ind : Individual} {x : b.Node} :
    b.boundToBool ind x = true ↔ b.BoundTo ind x := by
  cases ind with
  | named a => simp [boundToBool, BoundTo]
  | anonymous d l => simp [boundToBool, BoundTo]

def recordedDistinctBool (b : BlockedForest) (x y : b.Node) : Bool :=
  b.unequal.contains (x, y) || b.unequal.contains (y, x)

theorem recordedDistinctBool_iff {b : BlockedForest} {x y : b.Node} :
    b.recordedDistinctBool x y = true ↔ b.RecordedDistinct x y := by
  simp [recordedDistinctBool, RecordedDistinct]

def isUnblockedBool (b : BlockedForest) (x : b.Node) : Bool :=
  (b.reblock.blockedBy x).isNone && !(b.ancestors x).any (fun a => (b.reblock.blockedBy a).isSome)

private theorem holds_or_dual (i : Interpretation datatypeMap) (x : i.Object) (c : Concept) :
    holds i x c ∨ holds i x c.dual :=
  (Classical.em (holds i x c)).imp_right (holds_dual i x c).mpr

theorem isUnblockedBool_iff {b : BlockedForest} {x : b.Node} :
    b.isUnblockedBool x = true ↔ b.reblock.Unblocked x := by
  unfold isUnblockedBool Unblocked IndirectlyBlocked DirectlyBlocked
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none, Bool.eq_false_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨a, ha, hb⟩
    exact h2 (List.any_eq_true.mpr ⟨a, mem_ancestors.mpr (same_anc_reblock.mp ha), hb⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hany => ?_⟩
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp hany
    exact h2 ⟨a, same_anc_reblock.mpr (mem_ancestors.mp ha), hb⟩

theorem edge_admissible_of_edge {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (he : b.Edge r x y) : b.EdgeAdmissible x y := by
  rcases he with ⟨rfl, _⟩ | ⟨hx, hy, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
  · exact .inl rfl
  · exact .inr (.inl ⟨hx, hy⟩)
  · exact .inr (.inr (.inl hc))
  · exact .inr (.inr (.inr (.inl hc)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨(b.toRoot_valid x _ htr).1, (b.toRoot_valid x _ htr).2.1⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨(b.toRoot_valid y _ htr).2.1, (b.toRoot_valid y _ htr).1⟩))))

theorem edge_toRoot_left {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (he : b.Edge r x y) (hx : b.isRoot x = false) (hy : b.isRoot y = true)
    (hp : b.parent x ≠ y) : (r, y) ∈ b.toRoot x := by
  rcases he with ⟨rfl, _⟩ | ⟨hxr, _, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
  · rw [hx] at hy; cases hy
  · rw [hx] at hxr; cases hxr
  · have h := hc.1; rw [hy] at h; cases h
  · exact (hp hc.2).elim
  · exact htr
  · have h := (b.toRoot_valid y _ htr).1; rw [hy] at h; cases h

theorem edge_toRoot_right {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (he : b.Edge r x y) (hx : b.isRoot x = true) (hy : b.isRoot y = false)
    (hp : b.parent y ≠ x) : (converse r, x) ∈ b.toRoot y := by
  rcases he with ⟨rfl, _⟩ | ⟨_, hyr, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
  · rw [hx] at hy; cases hy
  · rw [hy] at hyr; cases hyr
  · exact (hp hc.2).elim
  · have h := hc.1; rw [hx] at h; cases h
  · have h := (b.toRoot_valid x _ htr).1; rw [hx] at h; cases h
  · exact htr

theorem isNamedRoot_iff {b : BlockedForest} {x : b.Node} :
    b.isNamedRoot x = true ↔ ∃ a, (a, x) ∈ b.noms := by
  unfold isNamedRoot
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, y⟩, hm, rfl⟩; exact ⟨a, hm⟩
  · rintro ⟨a, hm⟩; exact ⟨(a, x), hm, rfl⟩

theorem isNamedRoot_isRoot {b : BlockedForest} {x : b.Node} (h : b.isNamedRoot x = true) :
    b.isRoot x = true := by
  obtain ⟨a, ha⟩ := isNamedRoot_iff.mp h
  exact b.noms_valid (a, x) ha

def qualifiedPred (b : BlockedForest) (x : b.Node) (r : OrientedRole) (c : Concept)
    (y : b.Node) : Bool :=
  (!b.isRoot x || b.isRoot y || (!b.isRoot y && b.parent y == x)) &&
  b.edgeBool r x y && (b.labels y).contains c

theorem qualifiedPred_iff {b : BlockedForest} {x y : b.Node} {r : OrientedRole} {c : Concept} :
    b.qualifiedPred x r c y = true ↔
      (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge r x y ∧ c ∈ b.labels y := by
  unfold qualifiedPred Child
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    edgeBool_iff, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun hxr => ?_, h2, h3⟩
    rcases h1 with (hf | hyr) | hch
    · rw [hxr] at hf; cases hf
    · exact .inl hyr
    · exact .inr hch
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    cases hxr : b.isRoot x with
    | false => exact .inl (.inl rfl)
    | true =>
      rcases h1 hxr with hyr | hch
      · exact .inl (.inr hyr)
      · exact .inr hch

def qualifiedNeighbors (b : BlockedForest) (x : b.Node) (r : OrientedRole) (c : Concept) :
    List b.Node :=
  (List.finRange (b.size + 1)).filter (b.qualifiedPred x r c)

theorem mem_qualifiedNeighbors {b : BlockedForest} {x y : b.Node} {r : OrientedRole} {c : Concept} :
    y ∈ b.qualifiedNeighbors x r c ↔
      (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge r x y ∧ c ∈ b.labels y := by
  simp [qualifiedNeighbors, qualifiedPred_iff]

theorem qualifiedNeighbors_nodup (b : BlockedForest) (x : b.Node) (r : OrientedRole) (c : Concept) :
    (b.qualifiedNeighbors x r c).Nodup :=
  (List.nodup_finRange (b.size + 1)).filter _

/-! ### Search state, strict steps, and checked transitions -/

structure SROIQState (rank : Rank) (p : Problem) where
  forest : BlockedForest
  within : forest.Within rank p
  bindings : forest.BindingsValid p
  geom : forest.ForestGeom rank p
  abox : forest.ABoxSeeded p
  nomsSound : ∀ q ∈ forest.noms, q.1 ∈ p.nominals

def SROIQState.initial (rank : Rank) (p : Problem) : SROIQState rank p where
  forest := BlockedForest.initial p
  within := initial_within rank p
  bindings := initial_bindings p
  geom := initial_geom rank p
  abox := initial_aboxSeeded p
  nomsSound := by
    intro ⟨a, r⟩ hm
    change (a, r) ∈ _ at hm
    dsimp only [BlockedForest.initial] at hm
    obtain ⟨i, _, heq⟩ := List.mem_map.mp hm
    cases heq
    have hm' : (p.nominals.eraseDups).get i ∈ p.nominals.eraseDups := List.get_mem ..
    exact (List.mem_eraseDups.mp hm')

theorem SROIQState.initial_sat_iff (rank : Rank) (p : Problem) :
    (SROIQState.initial rank p).forest.Sat p ↔ p.Sat :=
  BlockedForest.initial_sat_iff p

/-- Strict one-step classification of every transition emitted by `sroiqStep`.
`rootMerge` and `nnExpand` strictly decrease the root-level lexicographic vector;
`enrich`, `blockableMerge`, and `generate` preserve the root set bijectively and
strictly decrease the tree-depth lexicographic vector. -/
inductive SROIQStrictStep (rank : Rank) (p : Problem) (b b' : BlockedForest) : Prop where
  | rootMerge (keep drop : b.Node) (hd : drop ≠ 0) (hk : keep ∈ b.retained drop)
      (hvalid : b.MergeValid keep drop) (hdrop : b.isRoot drop = true)
      (heq : b' = b.mergeForest keep drop hd hk hvalid)
  | nnExpand (m : Nat) (r : b.Node) (hr : b.isRoot r = true)
      (rel : OrientedRole) (c : Concept) (n : Nat)
      (hmax : .max n rel c ∈ sroiqClos p) (hno : ¬ b.HasNNBound r (.max n rel c))
      (hlvl : b.nomLevel r + 1 ≤ sroiqMaxDepth rank p)
      (heq : b' = b.appendNNRoots m r hr rel c)
  | addLabel (x : b.Node) (c : Concept) (hc : c ∈ sroiqClos p) (hno : c ∉ b.labels x)
      (heq : b' = b.addLabel x c)
  | addGuard (x : b.Node) (g : Guard) (hg : g ∈ sroiqGuards rank p) (hno : g ∉ b.guardLabels x)
      (heq : b' = b.addGuard x g)
  | addEdge (r : OrientedRole) (x y : b.Node) (hr : r.1 ∈ sroiqRoleNames p)
      (hadm : b.EdgeAdmissible x y) (hno : ¬ b.Edge r x y)
      (heq : b' = b.addEdge r x y)
  | addKeyDisjoint (r₁ r₂ : b.Node) (dp : IRI)
      (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true)
      (hdp : dp ∈ sroiqDataProps p) (hno : (r₁, r₂, dp) ∉ b.keyDisjoint)
      (heq : b' = b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂)
  | blockableMerge (keep drop : b.Node) (hd : drop ≠ 0) (hk : keep ∈ b.retained drop)
      (hvalid : b.MergeValid keep drop) (hdrop : b.isRoot drop = false)
      (hallowed : ¬ b.RecordedDistinct keep drop)
      (heq : b' = b.mergeForest keep drop hd hk hvalid)
  | generate (n : Nat) (x : b.Node) (r : OrientedRole) (c : Concept)
      (hdepth : b.depth x ≤ sroiqMaxDepth rank p) (hr : r.1 ∈ sroiqRoleNames p)
      (hc : c ∈ sroiqClos p)
      (hgen : (.some r c ∈ sroiqClos p ∧ n = 1 ∧ ¬ b.GenProtected x (.some r c)) ∨
              (.min n r c ∈ sroiqClos p ∧ ¬ b.GenProtected x (.min n r c)))
      (heq : b' = b.appendChildren n x r c)

structure SROIQCheckedStep (rank : Rank) (p : Problem) (s : SROIQState rank p) where
  branches : List (SROIQState rank p)
  sound : ∀ i : Interpretation datatypeMap, p.Models i → ∀ env,
    s.forest.Realizes i env → ∃ next ∈ branches, ∃ env', next.forest.Realizes i env'
  strict : ∀ next ∈ branches, SROIQStrictStep rank p s.forest next.forest

/-! ### State update constructors -/

private def stateAddLabel {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (x : s.forest.Node) (c : Concept) (hc : c ∈ sroiqClos p) : SROIQState rank p where
  forest := s.forest.addLabel x c
  within := addLabel_within s.within hc
  bindings := ⟨s.bindings.nomComplete, s.bindings.anonComplete, s.bindings.nomFunctional, s.bindings.anonFunctional⟩
  geom := addLabel_geom s.geom x c
  abox := addLabel_aboxSeeded s.abox x c
  nomsSound := s.nomsSound

private def stateAddGuard {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (x : s.forest.Node) (g : Guard) (hg : g ∈ sroiqGuards rank p) : SROIQState rank p where
  forest := s.forest.addGuard x g
  within := addGuard_within s.within hg
  bindings := ⟨s.bindings.nomComplete, s.bindings.anonComplete, s.bindings.nomFunctional, s.bindings.anonFunctional⟩
  geom := addGuard_geom s.geom x g
  abox := ⟨s.abox.root, s.abox.classAssertions, s.abox.objAssertions, s.abox.negObjAssertions,
    s.abox.sameInds, s.abox.diffInds, s.abox.dataAssertions, s.abox.negDataAssertions⟩
  nomsSound := s.nomsSound

private def stateAddKeyDisjoint {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (r₁ r₂ : s.forest.Node) (dp : IRI)
    (hr₁ : s.forest.isRoot r₁ = true) (hr₂ : s.forest.isRoot r₂ = true) :
    SROIQState rank p where
  forest := s.forest.addKeyDisjoint r₁ r₂ dp hr₁ hr₂
  within := addKeyDisjoint_within s.within r₁ r₂ dp hr₁ hr₂
  bindings := ⟨s.bindings.nomComplete, s.bindings.anonComplete, s.bindings.nomFunctional, s.bindings.anonFunctional⟩
  geom := addKeyDisjoint_geom s.geom r₁ r₂ dp hr₁ hr₂
  abox := addKeyDisjoint_aboxSeeded s.abox r₁ r₂ dp hr₁ hr₂
  nomsSound := s.nomsSound

private def stateAddEdge {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (r : OrientedRole) (x y : s.forest.Node) (hr : r.1 ∈ sroiqRoleNames p)
    (hxy : s.forest.isRoot x = false → s.forest.isRoot y = true → s.forest.parent x ≠ y →
      s.forest.depth x + s.forest.nomLevel y ≤ sroiqMaxDepth rank p)
    (hyx : s.forest.isRoot x = true → s.forest.isRoot y = false → s.forest.parent y ≠ x →
      s.forest.depth y + s.forest.nomLevel x ≤ sroiqMaxDepth rank p) :
    SROIQState rank p where
  forest := s.forest.addEdge r x y
  within := addEdge_within s.within hr x y
  bindings := ⟨s.bindings.nomComplete, s.bindings.anonComplete, s.bindings.nomFunctional, s.bindings.anonFunctional⟩
  geom := addEdge_geom s.geom hxy hyx
  abox := addEdge_aboxSeeded s.abox r x y
  nomsSound := s.nomsSound

private def stateAppendChildren {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (n : Nat) (x : s.forest.Node) (r : OrientedRole) (c : Concept)
    (hr : r.1 ∈ sroiqRoleNames p) (hc : c ∈ sroiqClos p)
    (hdepth : s.forest.depth x ≤ sroiqMaxDepth rank p) : SROIQState rank p where
  forest := s.forest.appendChildren n x r c
  within := appendChildren_within s.within hr hc
  bindings := appendChildren_bindings s.bindings n x r c
  geom := appendChildren_geom s.geom hdepth r c
  abox := appendChildren_aboxSeeded s.abox n x r c
  nomsSound := by
    intro ⟨a, y⟩ hm
    obtain ⟨⟨a', u⟩, hu, heq⟩ := List.mem_map.mp hm
    cases heq
    exact s.nomsSound (a, u) hu

private def stateAppendNNRoots {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (m : Nat) (r : s.forest.Node) (hr : s.forest.isRoot r = true)
    (rel : OrientedRole) (c : Concept)
    (hrel : rel.1 ∈ sroiqRoleNames p) (hc : c ∈ sroiqClos p)
    (hlvl : s.forest.nomLevel r + 1 ≤ sroiqMaxDepth rank p) : SROIQState rank p where
  forest := s.forest.appendNNRoots m r hr rel c
  within := appendNNRoots_within s.within hr hrel hc
  bindings := appendNNRoots_bindings s.bindings m r hr rel c
  geom := appendNNRoots_geom s.geom hr hlvl rel c
  abox := appendNNRoots_aboxSeeded s.abox m r hr rel c
  nomsSound := by
    intro ⟨a, y⟩ hm
    obtain ⟨⟨a', u⟩, hu, heq⟩ := List.mem_map.mp hm
    cases heq
    exact s.nomsSound (a, u) hu

private def stateMerge {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (keep drop : s.forest.Node) (hd : drop ≠ 0) (hk : keep ∈ s.forest.retained drop)
    (hvalid : s.forest.MergeValid keep drop)
    (hbr : s.forest.isRoot keep = true → s.forest.isRoot drop = false →
      s.forest.isRoot (s.forest.parent drop) = false → s.forest.parent (s.forest.parent drop) ≠ keep →
      s.forest.depth (s.forest.parent drop) + s.forest.nomLevel keep ≤ sroiqMaxDepth rank p) :
    SROIQState rank p where
  forest := s.forest.mergeForest keep drop hd hk hvalid
  within := mergeForest_within s.within hd hk hvalid
  bindings := mergeForest_bindings s.bindings hd hk hvalid
  geom := mergeForest_geom s.geom hd hk hvalid hbr
  abox := mergeForest_aboxSeeded s.abox hd hk hvalid
  nomsSound := by
    intro ⟨a, y⟩ hm
    obtain ⟨⟨a', u⟩, hu, hres⟩ := List.mem_filterMap.mp hm
    obtain ⟨u', _, heq⟩ := Option.map_eq_some_iff.mp hres
    cases heq
    exact s.nomsSound (a, u) hu

private def closeStep {rank : Rank} {p : Problem} {s : SROIQState rank p}
    (hunsat : ∀ i : Interpretation datatypeMap, p.Models i → ∀ env, ¬ s.forest.Realizes i env) :
    SROIQCheckedStep rank p s where
  branches := []
  sound := fun i hm env hr => (hunsat i hm env hr).elim
  strict := fun _ h => (List.not_mem_nil h).elim

/-! ### Inspection monad for fair rule sweeps -/

private inductive Inspection (rank : Rank) (p : Problem) (s : SROIQState rank p) (done : Prop) where
  | step (t : SROIQCheckedStep rank p s)
  | done (h : done)

private def Inspection.mapDone {rank : Rank} {p : Problem} {s : SROIQState rank p}
    {P Q : Prop} (f : P → Q) : Inspection rank p s P → Inspection rank p s Q
  | .step t => .step t
  | .done h => .done (f h)

private def Inspection.andThen {rank : Rank} {p : Problem} {s : SROIQState rank p}
    {P Q : Prop} (first : Inspection rank p s P) (second : P → Inspection rank p s Q) :
    Inspection rank p s (P ∧ Q) :=
  match first with
  | .step t => .step t
  | .done hp => (second hp).mapDone (fun hq => ⟨hp, hq⟩)

private def inspectList {α : Type} {rank : Rank} {p : Problem} {s : SROIQState rank p}
    {P : α → Prop} : (xs : List α) → (∀ a ∈ xs, Inspection rank p s (P a)) →
    Inspection rank p s (∀ a ∈ xs, P a)
  | [], _ => .done (fun _ h => (List.not_mem_nil h).elim)
  | a :: xs, f =>
    match f a (List.mem_cons_self ..) with
    | .step t => .step t
    | .done ha =>
      (inspectList xs (fun b hb => f b (List.mem_cons_of_mem _ hb))).mapDone fun hxs b hb =>
        (List.mem_cons.mp hb).elim (· ▸ ha) (hxs b)

private def inspectMatch {α β : Type} {rank : Rank} {p : Problem} {s : SROIQState rank p}
    {P : β → Prop} (xs : List α) (ext : α → Option β)
    (f : ∀ a ∈ xs, ∀ b, ext a = some b → Inspection rank p s (P b)) :
    Inspection rank p s (∀ a ∈ xs, ∀ b, ext a = some b → P b) :=
  inspectList (P := fun a => ∀ b, ext a = some b → P b) xs fun a ha =>
    match h : ext a with
    | some b => (f a ha b h).mapDone fun hb b' h' => (Option.some.inj h') ▸ hb
    | none => .done fun _ h' => by cases h'

private def inspectNodes {rank : Rank} {p : Problem} {s : SROIQState rank p}
    {P : s.forest.Node → Prop} (f : ∀ x : s.forest.Node, Inspection rank p s (P x)) :
    Inspection rank p s (∀ x : s.forest.Node, P x) :=
  (inspectList (List.finRange (s.forest.size + 1)) (fun x _ => f x)).mapDone fun h x =>
    h x (List.mem_finRange x)

/-! ### 1. Clash detection -/

private def inspectClash {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p)
    (rootResult : {r // r = solveDataCSP (s.forest.rootDataCSP p)}) :
    Inspection rank p s (s.forest.reblock.BlockedClashFree p) :=
  let b := s.forest
  let hi := p.sroiqdInput hsroiqd
  let c1 : Inspection rank p s (∀ x, .bottom ∉ b.labels x) :=
    inspectNodes fun x =>
      if h : (b.labels x).contains .bottom then
        .step (closeStep fun _ _ _ hr => hr.labels x .bottom (List.contains_iff_mem.mp h))
      else
        .done fun hm => h (List.contains_iff_mem.mpr hm)
  let c2 : Inspection rank p s (∀ x a, .lit a true ∈ b.labels x → .lit a false ∉ b.labels x) :=
    inspectNodes fun x =>
      (inspectMatch (b.labels x) (fun | .lit a true => some a | _ => none) fun c hc a ha =>
        have hc' : .lit a true ∈ b.labels x := by
          cases c with
          | lit a' sign => cases sign <;> cases ha; exact hc
          | _ => cases ha
        if h : (b.labels x).contains (.lit a false) then
          .step (closeStep fun _ _ _ hr =>
            hr.labels x (.lit a false) (List.contains_iff_mem.mp h) (hr.labels x (.lit a true) hc'))
        else
          .done fun hm => h (List.contains_iff_mem.mpr hm)).mapDone fun h a ht hf => h (.lit a true) ht a rfl hf
  let c3 : Inspection rank p s (∀ x, (x, x) ∉ b.unequal) :=
    inspectNodes fun x =>
      if h : b.unequal.contains (x, x) then
        .step (closeStep fun _ _ _ hr => hr.unequal x x (List.contains_iff_mem.mp h) rfl)
      else
        .done fun hm => h (List.contains_iff_mem.mpr hm)
  let c4 : Inspection rank p s (∀ x ind, .nom ind false ∈ b.labels x → ¬ b.BoundTo ind x) :=
    inspectNodes fun x =>
      (inspectMatch (b.labels x) (fun | .nom ind false => some ind | _ => none) fun c hc ind hind =>
        have hc' : .nom ind false ∈ b.labels x := by
          cases c with
          | nom ind' sign => cases sign <;> cases hind; exact hc
          | _ => cases hind
        if h : b.boundToBool ind x then
          .step (closeStep fun i _ env hr => by
            have hneg : env x ≠ i.individuals ind := hr.labels x (.nom ind false) hc'
            have hbd := boundToBool_iff.mp h
            cases ind with
            | named a => exact hneg (hr.noms a x hbd)
            | anonymous d l => exact hneg (hr.anons (d, l) x hbd))
        else
          .done fun hbd => h (boundToBool_iff.mpr hbd)).mapDone fun h ind hnom hbd => h (.nom ind false) hnom ind rfl hbd
  let c5 : Inspection rank p s (∀ r ∈ p.chars.irreflexive, ∀ x, ¬ b.Edge (r, false) x x) :=
    inspectList p.chars.irreflexive fun r hr =>
      inspectNodes fun x =>
        if h : b.edgeBool (r, false) x x then
          .step (closeStep fun i hm env hreal =>
            hm.irreflexive r hr (env x) (hreal.edges (r, false) x x (edgeBool_iff.mp h)))
        else
          .done fun he => h (edgeBool_iff.mpr he)
  let c6 : Inspection rank p s (∀ r ∈ p.chars.asymmetric, ∀ x y, b.Edge (r, false) x y → ¬ b.Edge (r, false) y x) :=
    inspectList p.chars.asymmetric fun r hr =>
      inspectNodes fun x =>
        inspectNodes fun y =>
          if h : b.edgeBool (r, false) x y && b.edgeBool (r, false) y x then
            .step (closeStep fun i hm env hreal => by
              have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
              exact hm.asymmetric r hr (env x) (env y)
                (hreal.edges (r, false) x y (edgeBool_iff.mp h1))
                (hreal.edges (r, false) y x (edgeBool_iff.mp h2)))
          else
            .done fun h1 h2 => h (Bool.and_eq_true_iff.mpr ⟨edgeBool_iff.mpr h1, edgeBool_iff.mpr h2⟩)
  let c7 : Inspection rank p s (∀ q ∈ p.chars.disjoint, ∀ x y, ¬ (b.Edge q.1 x y ∧ b.Edge q.2 x y)) :=
    inspectList p.chars.disjoint fun q hq =>
      inspectNodes fun x =>
        inspectNodes fun y =>
          if h : b.edgeBool q.1 x y && b.edgeBool q.2 x y then
            .step (closeStep fun i hm env hreal => by
              have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
              exact hm.disjoint q hq (env x) (env y)
                ⟨hreal.edges q.1 x y (edgeBool_iff.mp h1),
                 hreal.edges q.2 x y (edgeBool_iff.mp h2)⟩)
          else
            .done fun ⟨h1, h2⟩ => h (Bool.and_eq_true_iff.mpr ⟨edgeBool_iff.mpr h1, edgeBool_iff.mpr h2⟩)
  let c8 : Inspection rank p s (∀ x r, .self r false ∈ b.labels x → ¬ b.Edge r x x) :=
    inspectNodes fun x =>
      (inspectMatch (b.labels x) (fun | .self r false => some r | _ => none) fun c hc r hr =>
        have hc' : .self r false ∈ b.labels x := by
          cases c with
          | self r' sign => cases sign <;> cases hr; exact hc
          | _ => cases hr
        if h : b.edgeBool r x x then
          .step (closeStep fun i _ env hreal =>
            hreal.labels x (.self r false) hc' (hreal.edges r x x (edgeBool_iff.mp h)))
        else
          .done fun he => h (edgeBool_iff.mpr he)).mapDone fun h r hs he => h (.self r false) hs r rfl he
  let c9 : Inspection rank p s ((solveDataCSP (b.rootDataCSP p)).isSome = true) :=
    match hsol : rootResult.val with
    | some _ => .done (by rw [← rootResult.property, hsol]; rfl)
    | none =>
      .step (closeStep fun i hm env hreal =>
        solveDataCSP_none_unsat (b.rootDataCSP_isSROIQD hi s.within.labels)
          (rootResult.property.symm.trans hsol)
          (b.rootDataCSP_realizes hm hreal))
  let c10 : Inspection rank p s (∀ x, b.reblock.Unblocked x → b.isRoot x = false →
      (solveDataCSP (b.nodeDataCSP p x)).isSome = true) :=
    inspectNodes fun x =>
      if hcond : b.isUnblockedBool x = true ∧ b.isRoot x = false then
        match hsol : solveDataCSP (b.nodeDataCSP p x) with
        | some _ => .done (fun _ _ => rfl)
        | none =>
          .step (closeStep fun i hm env hreal =>
            solveDataCSP_none_unsat (b.nodeDataCSP_isSROIQD hi s.within.labels x) hsol
              (b.nodeDataCSP_realizes hm hreal x))
      else
        .done fun hux hnr => (hcond ⟨isUnblockedBool_iff.mpr hux, hnr⟩).elim
  (((c1.andThen fun _ => c2).andThen fun _ =>
    (c3.andThen fun _ => c4)).andThen (fun _ =>
      (c5.andThen fun _ => c6).andThen fun _ => (c7.andThen fun _ => c8))).andThen
    (fun _ => c9.andThen fun _ => c10) |>.mapDone
    fun ⟨⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩, ⟨h9, h10⟩⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ### 2. Root-to-root merge helper -/

private def rootMergeStep {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (r₁ r₂ : s.forest.Node) (hr₁ : s.forest.isRoot r₁ = true) (hr₂ : s.forest.isRoot r₂ = true)
    (hne : r₁ ≠ r₂)
    (heqModel : ∀ i : Interpretation datatypeMap, p.Models i → ∀ env,
      s.forest.Realizes i env → env r₁ = env r₂) :
    SROIQCheckedStep rank p s :=
  if hrec : s.forest.recordedDistinctBool r₁ r₂ then
    closeStep fun i hm env hreal => by
      have heq := heqModel i hm env hreal
      rcases recordedDistinctBool_iff.mp hrec with h | h
      · exact hreal.unequal r₁ r₂ h heq
      · exact hreal.unequal r₂ r₁ h heq.symm
  else
    let spec := orientRootMerge_spec hne s.geom.nomLevel0
    let pair := s.forest.orientRootMerge r₁ r₂
    let keep := pair.1
    let drop := pair.2
    have hcases : (keep = r₁ ∧ drop = r₂) ∨ (keep = r₂ ∧ drop = r₁) := spec.1
    have hkd : keep ≠ drop := spec.2.1
    have hd0 : drop ≠ 0 := spec.2.2.1
    have hlvl : s.forest.nomLevel keep ≤ s.forest.nomLevel drop := spec.2.2.2
    have hkr : s.forest.isRoot keep = true := hcases.elim (fun h => h.1 ▸ hr₁) (fun h => h.1 ▸ hr₂)
    have hdr : s.forest.isRoot drop = true := hcases.elim (fun h => h.2 ▸ hr₂) (fun h => h.2 ▸ hr₁)
    have hk : keep ∈ s.forest.retained drop := retained_of_isRoot hkr hkd
    have hvalid : s.forest.MergeValid keep drop := .inl ⟨hkr, fun _ => hlvl⟩
    let next := stateMerge s keep drop hd0 hk hvalid (fun _ hf => by rw [hdr] at hf; cases hf)
    { branches := [next]
      sound := fun i hm env hreal => by
        have heq := heqModel i hm env hreal
        have heq' : env keep = env drop := hcases.elim
          (fun h => by rw [h.1, h.2]; exact heq)
          (fun h => by rw [h.1, h.2]; exact heq.symm)
        exact ⟨next, List.mem_cons_self .., _, mergeForest_realizes hreal hd0 hk hvalid heq'⟩
      strict := fun b' hb' => by
        obtain rfl := List.mem_singleton.mp hb'
        exact .rootMerge keep drop hd0 hk hvalid hdr rfl }

/-! ### 3. Positive nominal merging (`nomPos`) -/

private def findBoundRoot (b : BlockedForest) : Individual → Option b.Node
  | .named a => (b.noms.find? (fun q => q.1 == a)).map Prod.snd
  | .anonymous d l => (b.anons.find? (fun q => q.1 == (d, l))).map Prod.snd

private theorem findBoundRoot_some {b : BlockedForest} {ind : Individual} {r : b.Node}
    (h : b.findBoundRoot ind = some r) : b.BoundTo ind r := by
  cases ind with
  | named a =>
    obtain ⟨⟨a', r'⟩, hfind, heq⟩ := Option.map_eq_some_iff.mp h
    dsimp at heq; subst heq
    have ha : a' = a := beq_iff_eq.mp (List.find?_some (p := fun q : IRI × b.Node => q.1 == a) hfind)
    exact ha ▸ List.mem_of_find?_eq_some hfind
  | anonymous d l =>
    obtain ⟨⟨k', r'⟩, hfind, heq⟩ := Option.map_eq_some_iff.mp h
    dsimp at heq; subst heq
    have hk : k' = (d, l) := beq_iff_eq.mp (List.find?_some (p := fun q : (String × String) × b.Node => q.1 == (d, l)) hfind)
    have hmem := List.mem_of_find?_eq_some hfind
    rw [hk] at hmem; exact hmem

private theorem findBoundRoot_none {b : BlockedForest} {ind : Individual}
    (h : b.findBoundRoot ind = none) {r : b.Node} : ¬ b.BoundTo ind r := by
  cases ind with
  | named a =>
    intro hm
    cases hf : b.noms.find? (fun q => q.1 == a) with
    | some q => simp [findBoundRoot, hf] at h
    | none =>
      have hbad := List.find?_eq_none.mp hf (a, r) hm
      simp at hbad
  | anonymous d l =>
    intro hm
    cases hf : b.anons.find? (fun q => q.1 == (d, l)) with
    | some q => simp [findBoundRoot, hf] at h
    | none =>
      have hbad := List.find?_eq_none.mp hf ((d, l), r) hm
      simp at hbad

private def inspectNomPos {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ x, s.forest.reblock.Unblocked x →
      ∀ ind r, .nom ind true ∈ s.forest.labels x → s.forest.BoundTo ind r → x = r) :=
  let b := s.forest
  inspectNodes fun x =>
    if hux : b.isUnblockedBool x then
      (inspectMatch (P := fun ind => ∀ r, b.BoundTo ind r → x = r)
        (b.labels x) (fun | .nom ind true => some ind | _ => none) fun c hc ind hind =>
        have hc' : .nom ind true ∈ b.labels x := by
          cases c with
          | nom ind' sign => cases sign <;> cases hind; exact hc
          | _ => cases hind
        match hfind : b.findBoundRoot ind with
        | none => .done fun r hbd => (findBoundRoot_none hfind hbd).elim
        | some r =>
          have hbd : b.BoundTo ind r := findBoundRoot_some hfind
          have heqModel : ∀ i : Interpretation datatypeMap, p.Models i → ∀ env,
              b.Realizes i env → env x = env r := fun i _ env hreal => by
            have hx : env x = i.individuals ind := hreal.labels x (.nom ind true) hc'
            have hr : env r = i.individuals ind := by
              cases ind with
              | named a => exact hreal.noms a r hbd
              | anonymous d l => exact hreal.anons (d, l) r hbd
            exact hx.trans hr.symm
          if hxr : x = r then
            .done fun r' hbd' => hxr.trans (s.bindings.ind_unique hbd hbd')
          else if hrx : b.isRoot x = true then
            .step (rootMergeStep s x r hrx hbd.isRoot hxr heqModel)
          else
            if hrec : b.recordedDistinctBool r x then
              .step (closeStep fun i hm env hreal => by
                have heq := heqModel i hm env hreal
                rcases recordedDistinctBool_iff.mp hrec with h | h
                · exact hreal.unequal r x h heq.symm
                · exact hreal.unequal x r h heq)
            else
              have hxnr : b.isRoot x = false := Bool.eq_false_iff.mpr hrx
              have hx0 : x ≠ 0 := fun h => by rw [h, b.root0] at hxnr; cases hxnr
              have hk : r ∈ b.retained x := retained_of_isRoot hbd.isRoot (Ne.symm hxr)
              have hvalid : b.MergeValid r x := .inl ⟨hbd.isRoot, fun h => by rw [hxnr] at h; cases h⟩
              have hlvl0 : b.nomLevel r = 0 := by
                cases ind with
                | named a => exact s.geom.boundNomZero a r hbd
                | anonymous d l => exact s.geom.boundAnonZero (d, l) r hbd
              have hbr : b.isRoot r = true → b.isRoot x = false →
                  b.isRoot (b.parent x) = false → b.parent (b.parent x) ≠ r →
                  b.depth (b.parent x) + b.nomLevel r ≤ sroiqMaxDepth rank p := fun _ _ _ _ => by
                have hdx : b.depth x ≤ sroiqMaxDepth rank p :=
                  unblocked_depth_le s.within (isUnblockedBool_iff.mp hux)
                have hch : b.Child (b.parent x) x := ⟨hxnr, rfl⟩
                have hdp := depth_child hch
                omega
              let next := stateMerge s r x hx0 hk hvalid hbr
              .step {
                branches := [next]
                sound := fun i hm env hreal =>
                  ⟨next, List.mem_cons_self .., _,
                    mergeForest_realizes hreal hx0 hk hvalid (heqModel i hm env hreal).symm⟩
                strict := fun b' hb' => by
                  obtain rfl := List.mem_singleton.mp hb'
                  exact .blockableMerge r x hx0 hk hvalid hxnr
                    (fun h => hrec (recordedDistinctBool_iff.mpr h)) rfl }).mapDone fun h _ ind r hnom hbd =>
        h (.nom ind true) hnom ind rfl r hbd
    else
      .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim

/-! ### 4. `HasKey` rules (`keyCls`, `keyObjSplit`, `keyMerge`) -/

private def inspectKeyCls {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ k ∈ p.keys, ∀ x, s.forest.isNamedRoot x = true →
      k.cls ∈ s.forest.labels x ∨ k.cls.dual ∈ s.forest.labels x) :=
  let b := s.forest
  inspectList p.keys fun k hk =>
    inspectNodes fun x =>
      if hnr : b.isNamedRoot x = true then
        if h1 : (b.labels x).contains k.cls then
          .done fun _ => .inl (List.contains_iff_mem.mp h1)
        else if h2 : (b.labels x).contains k.cls.dual then
          .done fun _ => .inr (List.contains_iff_mem.mp h2)
        else
          have ⟨hc1, hc2⟩ := key_cls_mem_sroiqClos hk
          let s1 := stateAddLabel s x k.cls hc1
          let s2 := stateAddLabel s x k.cls.dual hc2
          .step {
            branches := [s1, s2]
            sound := fun i _ env hreal => by
              rcases holds_or_dual i (env x) k.cls with h | h
              · exact ⟨s1, List.mem_cons_self .., env, addLabel_realizes hreal h⟩
              · exact ⟨s2, List.mem_cons_of_mem _ (List.mem_cons_self ..), env, addLabel_realizes hreal h⟩
            strict := fun b' hb' => by
              rcases List.mem_cons.mp hb' with rfl | hb'
              · exact .addLabel x k.cls hc1 (fun hm => h1 (List.contains_iff_mem.mpr hm)) rfl
              · obtain rfl := List.mem_singleton.mp hb'
                exact .addLabel x k.cls.dual hc2 (fun hm => h2 (List.contains_iff_mem.mpr hm)) rfl }
      else
        .done fun h => (hnr h).elim

private def inspectKeyObjSplit {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ k ∈ p.keys, ∀ r ∈ k.objProps, ∀ x, s.forest.isNamedRoot x = true →
      ∀ a z, (a, z) ∈ s.forest.noms →
        s.forest.Edge r x z ∨ .all r (.nom (.named a) false) ∈ s.forest.labels x) :=
  let b := s.forest
  inspectList p.keys fun k hk =>
    inspectList k.objProps fun r hr =>
      inspectNodes fun x =>
        if hnr : b.isNamedRoot x = true then
          (inspectList (P := fun q =>
              b.Edge r x q.2 ∨ .all r (.nom (.named q.1) false) ∈ b.labels x)
            b.noms fun q hq =>
            let a := q.1
            let z := q.2
            if he : b.edgeBool r x z then
              .done (.inl (edgeBool_iff.mp he))
            else if ha : (b.labels x).contains (.all r (.nom (.named a) false)) then
              .done (.inr (List.contains_iff_mem.mp ha))
            else
              have hxr : b.isRoot x = true := isNamedRoot_isRoot hnr
              have hzr : b.isRoot z = true := b.noms_valid q hq
              have hrn : r.1 ∈ sroiqRoleNames p := sroiqRoleNames_of_key hk hr
              have hcl : .all r (.nom (.named a) false) ∈ sroiqClos p :=
                key_objSplit_mem_sroiqClos hk hr (s.nomsSound q hq)
              let s1 := stateAddEdge s r x z hrn
                (fun hf => by rw [hxr] at hf; cases hf)
                (fun _ hf => by rw [hzr] at hf; cases hf)
              let s2 := stateAddLabel s x (.all r (.nom (.named a) false)) hcl
              .step {
                branches := [s1, s2]
                sound := fun i _ env hreal => by
                  by_cases hrel : holdsOriented i r (env x) (env z)
                  · exact ⟨s1, List.mem_cons_self .., env, addEdge_realizes hreal hrel⟩
                  · refine ⟨s2, List.mem_cons_of_mem _ (List.mem_cons_self ..), env,
                      addLabel_realizes hreal ?_⟩
                    intro w hw heqw
                    have hz : env z = i.individuals (.named a) := hreal.noms a z hq
                    exact hrel (heqw.trans hz.symm ▸ hw)
                strict := fun b' hb' => by
                  rcases List.mem_cons.mp hb' with rfl | hb'
                  · exact .addEdge r x z hrn (.inr (.inl ⟨hxr, hzr⟩))
                      (fun h => he (edgeBool_iff.mpr h)) rfl
                  · obtain rfl := List.mem_singleton.mp hb'
                    exact .addLabel x _ hcl (fun h => ha (List.contains_iff_mem.mpr h)) rfl }).mapDone
            fun h _ a z haz => h (a, z) haz
        else
          .done fun h => (hnr h).elim

private def keyMatches (b : BlockedForest) (k : KeyAxiom) (x y : b.Node) : Bool :=
  k.objProps.all fun r =>
    (List.finRange (b.size + 1)).any fun z =>
      b.isNamedRoot z && b.edgeBool r x z && b.edgeBool r y z

private theorem keyMatches_iff {b : BlockedForest} {k : KeyAxiom} {x y : b.Node} :
    b.keyMatches k x y = true ↔
      ∀ r ∈ k.objProps, ∃ z, b.isNamedRoot z = true ∧ b.Edge r x z ∧ b.Edge r y z := by
  unfold keyMatches
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, edgeBool_iff,
    List.mem_finRange, true_and]
  constructor
  · intro h r hr; obtain ⟨z, ⟨hz, h1⟩, h2⟩ := h r hr; exact ⟨z, hz, h1, h2⟩
  · intro h r hr; obtain ⟨z, hz, h1, h2⟩ := h r hr; exact ⟨z, ⟨hz, h1⟩, h2⟩

private def keyDataBranches {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (k : KeyAxiom) (hk : k ∈ p.keys) (x y : s.forest.Node)
    (hxr : s.forest.isRoot x = true) (hyr : s.forest.isRoot y = true) :
    (dps : List IRI) → (∀ dp ∈ dps, dp ∈ k.dataProps ∧ (x, y, dp) ∉ s.forest.keyDisjoint) →
    { bs : List (SROIQState rank p) //
      (∀ dp ∈ dps, ∃ next ∈ bs, ∀ i env, s.forest.Realizes i env →
        (∀ z : i.Data, ¬ (i.dataProperties dp (env x) z ∧ i.dataProperties dp (env y) z)) →
        ∃ env', next.forest.Realizes i env') ∧
      (∀ next ∈ bs, SROIQStrictStep rank p s.forest next.forest) }
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | dp :: dps, hsub =>
    let tail := keyDataBranches s k hk x y hxr hyr dps
      (fun d hd => hsub d (List.mem_cons_of_mem _ hd))
    have ⟨hdpMem, hdpNo⟩ := hsub dp (List.mem_cons_self ..)
    have hdpIn : dp ∈ sroiqDataProps p := key_dataProp_mem_sroiqDataProps hk hdpMem
    let head := stateAddKeyDisjoint s x y dp hxr hyr
    ⟨head :: tail.1,
      fun d hd => by
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact ⟨head, List.mem_cons_self .., fun i env hreal hdisj =>
            ⟨env, addKeyDisjoint_realizes hreal hxr hyr hdisj⟩⟩
        · obtain ⟨next, hmem, hmk⟩ := tail.2.1 d hd'
          exact ⟨next, List.mem_cons_of_mem _ hmem, hmk⟩,
      fun b' hb' => by
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact .addKeyDisjoint x y dp hxr hyr hdpIn hdpNo rfl
        · exact tail.2.2 b' hb'⟩

private def inspectKeyMerge {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ k ∈ p.keys, ∀ x y, s.forest.isNamedRoot x = true →
      s.forest.isNamedRoot y = true → k.cls ∈ s.forest.labels x → k.cls ∈ s.forest.labels y →
      (∀ r ∈ k.objProps, ∃ z, s.forest.isNamedRoot z = true ∧
        s.forest.Edge r x z ∧ s.forest.Edge r y z) →
      x = y ∨ ∃ dp ∈ k.dataProps, (x, y, dp) ∈ s.forest.keyDisjoint) :=
  let b := s.forest
  inspectList p.keys fun k hk =>
    inspectNodes fun x =>
      inspectNodes fun y =>
        if hcond : x ≠ y ∧ b.isNamedRoot x = true ∧ b.isNamedRoot y = true ∧
            (b.labels x).contains k.cls = true ∧ (b.labels y).contains k.cls = true ∧
            b.keyMatches k x y = true ∧
            k.dataProps.any (fun dp => b.keyDisjoint.contains (x, y, dp)) = false then
          have hxr : b.isRoot x = true := isNamedRoot_isRoot hcond.2.1
          have hyr : b.isRoot y = true := isNamedRoot_isRoot hcond.2.2.1
          have hnoData : ∀ dp ∈ k.dataProps, dp ∈ k.dataProps ∧ (x, y, dp) ∉ b.keyDisjoint := by
            intro dp hdp
            refine ⟨hdp, fun hmem => ?_⟩
            have hany : k.dataProps.any (fun d => b.keyDisjoint.contains (x, y, d)) = true :=
              List.any_eq_true.mpr ⟨dp, hdp, List.contains_iff_mem.mpr hmem⟩
            rw [hcond.2.2.2.2.2.2] at hany
            cases hany
          let dataBs := keyDataBranches s k hk x y hxr hyr k.dataProps hnoData
          have hmodelOr : ∀ i : Interpretation datatypeMap, p.Models i → ∀ env,
              b.Realizes i env →
              env x = env y ∨
              ∃ dp ∈ k.dataProps, ∀ z : i.Data,
                ¬ (i.dataProperties dp (env x) z ∧ i.dataProperties dp (env y) z) := by
            intro i hm env hreal
            classical
            by_cases hall : ∀ dp ∈ k.dataProps, ∃ z : i.Data,
                i.dataProperties dp (env x) z ∧ i.dataProperties dp (env y) z
            · left
              obtain ⟨ax, hax⟩ := isNamedRoot_iff.mp hcond.2.1
              obtain ⟨ay, hay⟩ := isNamedRoot_iff.mp hcond.2.2.1
              have hnx : i.named (env x) := (hreal.noms ax x hax).symm ▸ i.namedIndividual ax
              have hny : i.named (env y) := (hreal.noms ay y hay).symm ▸ i.namedIndividual ay
              have hcx := hreal.labels x k.cls (List.contains_iff_mem.mp hcond.2.2.2.1)
              have hcy := hreal.labels y k.cls (List.contains_iff_mem.mp hcond.2.2.2.2.1)
              have hobj : ∀ r ∈ k.objProps, ∃ z, i.named z ∧
                  holdsOriented i r (env x) z ∧ holdsOriented i r (env y) z := by
                intro r hr
                obtain ⟨z, hzn, hxz, hyz⟩ := keyMatches_iff.mp hcond.2.2.2.2.2.1 r hr
                obtain ⟨az, haz⟩ := isNamedRoot_iff.mp hzn
                exact ⟨env z, (hreal.noms az z haz).symm ▸ i.namedIndividual az,
                  hreal.edges r x z hxz, hreal.edges r y z hyz⟩
              exact hm.keys k hk (env x) (env y) hcx hcy hnx hny hobj hall
            · right
              obtain ⟨dp, hnotImp⟩ := Classical.not_forall.mp hall
              have hdp : dp ∈ k.dataProps :=
                Classical.byContradiction fun hndp => hnotImp fun h => (hndp h).elim
              have hnoZ : ¬ ∃ z, i.dataProperties dp (env x) z ∧ i.dataProperties dp (env y) z :=
                fun hex => hnotImp fun _ => hex
              exact ⟨dp, hdp, fun z hz => hnoZ ⟨z, hz⟩⟩
          if hrec : b.recordedDistinctBool x y then
            .step {
              branches := dataBs.1
              sound := fun i hm env hreal => by
                rcases hmodelOr i hm env hreal with heq | ⟨dp, hdp, hdisj⟩
                · exfalso
                  rcases recordedDistinctBool_iff.mp hrec with h | h
                  · exact hreal.unequal x y h heq
                  · exact hreal.unequal y x h heq.symm
                · obtain ⟨next, hmem, hmk⟩ := dataBs.2.1 dp hdp
                  exact ⟨next, hmem, hmk i env hreal hdisj⟩
              strict := dataBs.2.2 }
          else
            let spec := orientRootMerge_spec hcond.1 s.geom.nomLevel0
            let pair := b.orientRootMerge x y
            let keep := pair.1
            let drop := pair.2
            have hcases : (keep = x ∧ drop = y) ∨ (keep = y ∧ drop = x) := spec.1
            have hkd : keep ≠ drop := spec.2.1
            have hd0 : drop ≠ 0 := spec.2.2.1
            have hlvl : b.nomLevel keep ≤ b.nomLevel drop := spec.2.2.2
            have hkr : b.isRoot keep = true := hcases.elim (fun h => h.1 ▸ hxr) (fun h => h.1 ▸ hyr)
            have hdr : b.isRoot drop = true := hcases.elim (fun h => h.2 ▸ hyr) (fun h => h.2 ▸ hxr)
            have hk : keep ∈ b.retained drop := retained_of_isRoot hkr hkd
            have hvalid : b.MergeValid keep drop := .inl ⟨hkr, fun _ => hlvl⟩
            let mergeNext := stateMerge s keep drop hd0 hk hvalid (fun _ hf => by rw [hdr] at hf; cases hf)
            .step {
              branches := mergeNext :: dataBs.1
              sound := fun i hm env hreal => by
                rcases hmodelOr i hm env hreal with heq | ⟨dp, hdp, hdisj⟩
                · have heq' : env keep = env drop := hcases.elim
                    (fun h => by rw [h.1, h.2]; exact heq)
                    (fun h => by rw [h.1, h.2]; exact heq.symm)
                  exact ⟨mergeNext, List.mem_cons_self .., _,
                    mergeForest_realizes hreal hd0 hk hvalid heq'⟩
                · obtain ⟨next, hmem, hmk⟩ := dataBs.2.1 dp hdp
                  exact ⟨next, List.mem_cons_of_mem _ hmem, hmk i env hreal hdisj⟩
              strict := fun b' hb' => by
                rcases List.mem_cons.mp hb' with rfl | hb'
                · exact .rootMerge keep drop hd0 hk hvalid hdr rfl
                · exact dataBs.2.2 b' hb' }
        else
          .done fun hx hy hcx hcy hm => by
            by_cases hxy : x = y
            · exact .inl hxy
            · right
              cases hany : k.dataProps.any (fun dp => b.keyDisjoint.contains (x, y, dp)) with
              | true =>
                obtain ⟨dp, hdp, hmem⟩ := List.any_eq_true.mp hany
                exact ⟨dp, hdp, List.contains_iff_mem.mp hmem⟩
              | false =>
                exact (hcond ⟨hxy, hx, hy, List.contains_iff_mem.mpr hcx,
                  List.contains_iff_mem.mpr hcy, keyMatches_iff.mpr hm, hany⟩).elim

/-! ### 5. Local enrichment rules (labels, TBox, rules, reflexivity, guards) -/

private def inspectLabels {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p) :
    Inspection rank p s (
      (∀ x, s.forest.reblock.Unblocked x → ∀ a c, .conj a c ∈ s.forest.labels x →
        a ∈ s.forest.labels x ∧ c ∈ s.forest.labels x) ∧
      (∀ x, s.forest.reblock.Unblocked x → ∀ a c, .disj a c ∈ s.forest.labels x →
        a ∈ s.forest.labels x ∨ c ∈ s.forest.labels x) ∧
      (∀ x, s.forest.reblock.Unblocked x → ∀ r c, .all r c ∈ s.forest.labels x →
        (⟨roleLanguage rank p r, c⟩ : Guard) ∈ s.forest.guardLabels x) ∧
      (∀ x, s.forest.reblock.Unblocked x → ∀ r, .self r true ∈ s.forest.labels x →
        s.forest.Edge r x x) ∧
      (∀ x, s.forest.reblock.Unblocked x → ∀ n r c, .max n r c ∈ s.forest.labels x →
        ∀ y, s.forest.Edge r x y → c ∈ s.forest.labels y ∨ c.dual ∈ s.forest.labels y)) :=
  let b := s.forest
  let pConj : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ a c, .conj a c ∈ b.labels x →
      a ∈ b.labels x ∧ c ∈ b.labels x) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q => q.1 ∈ b.labels x ∧ q.2 ∈ b.labels x)
          (b.labels x) (fun | .conj a c => some (a, c) | _ => none) fun d hd q hq =>
          have hd' : .conj q.1 q.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let a := q.1
          let c := q.2
          if ha : (b.labels x).contains a then
            if hc : (b.labels x).contains c then
              .done ⟨List.contains_iff_mem.mp ha, List.contains_iff_mem.mp hc⟩
            else
              have hcClos : c ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, c])
              let next := stateAddLabel s x c hcClos
              .step {
                branches := [next]
                sound := fun i _ env hreal =>
                  ⟨next, List.mem_cons_self .., env, addLabel_realizes hreal (hreal.labels x (.conj a c) hd').2⟩
                strict := fun b' hb' => by
                  obtain rfl := List.mem_singleton.mp hb'
                  exact .addLabel x c hcClos (fun hm => hc (List.contains_iff_mem.mpr hm)) rfl }
          else
            have haClos : a ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, a])
            let next := stateAddLabel s x a haClos
            .step {
              branches := [next]
              sound := fun i _ env hreal =>
                ⟨next, List.mem_cons_self .., env, addLabel_realizes hreal (hreal.labels x (.conj a c) hd').1⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .addLabel x a haClos (fun hm => ha (List.contains_iff_mem.mpr hm)) rfl }).mapDone
          fun h _ a c hm => h (.conj a c) hm (a, c) rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  let pDisj : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ a c, .disj a c ∈ b.labels x →
      a ∈ b.labels x ∨ c ∈ b.labels x) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q => q.1 ∈ b.labels x ∨ q.2 ∈ b.labels x)
          (b.labels x) (fun | .disj a c => some (a, c) | _ => none) fun d hd q hq =>
          have hd' : .disj q.1 q.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let a := q.1
          let c := q.2
          if ha : (b.labels x).contains a then
            .done (.inl (List.contains_iff_mem.mp ha))
          else if hc : (b.labels x).contains c then
            .done (.inr (List.contains_iff_mem.mp hc))
          else
            have haClos : a ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, a])
            have hcClos : c ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, c])
            let s1 := stateAddLabel s x a haClos
            let s2 := stateAddLabel s x c hcClos
            .step {
              branches := [s1, s2]
              sound := fun i _ env hreal => by
                rcases hreal.labels x (.disj a c) hd' with h1 | h2
                · exact ⟨s1, List.mem_cons_self .., env, addLabel_realizes hreal h1⟩
                · exact ⟨s2, List.mem_cons_of_mem _ (List.mem_cons_self ..), env, addLabel_realizes hreal h2⟩
              strict := fun b' hb' => by
                rcases List.mem_cons.mp hb' with rfl | hb'
                · exact .addLabel x a haClos (fun hm => ha (List.contains_iff_mem.mpr hm)) rfl
                · obtain rfl := List.mem_singleton.mp hb'
                  exact .addLabel x c hcClos (fun hm => hc (List.contains_iff_mem.mpr hm)) rfl }).mapDone
          fun h _ a c hm => h (.disj a c) hm (a, c) rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  let pAll : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ r c, .all r c ∈ b.labels x →
      (⟨roleLanguage rank p r, c⟩ : Guard) ∈ b.guardLabels x) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q => (⟨roleLanguage rank p q.1, q.2⟩ : Guard) ∈ b.guardLabels x)
          (b.labels x) (fun | .all r c => some (r, c) | _ => none) fun d hd q hq =>
          have hd' : .all q.1 q.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let g : Guard := ⟨roleLanguage rank p q.1, q.2⟩
          if hg : (b.guardLabels x).contains g then
            .done (List.contains_iff_mem.mp hg)
          else
            have hgIn : g ∈ sroiqGuards rank p := sroiq_initial_guard_mem (s.within.labels x hd')
            let next := stateAddGuard s x g hgIn
            .step {
              branches := [next]
              sound := fun i hm env hreal =>
                ⟨next, List.mem_cons_self .., env,
                  addGuard_realizes hreal
                    (initial_guard_sound (p.sroiqdInput hsroiqd).regular hm (hreal.labels x (.all q.1 q.2) hd'))⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .addGuard x g hgIn (fun h => hg (List.contains_iff_mem.mpr h)) rfl }).mapDone
          fun h _ r c hm => h (.all r c) hm (r, c) rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  let pSelf : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ r, .self r true ∈ b.labels x →
      b.Edge r x x) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (b.labels x) (fun | .self r true => some r | _ => none) fun d hd r hr =>
          have hd' : .self r true ∈ b.labels x := by
            cases d with
            | self r' sign => cases sign <;> cases hr; exact hd
            | _ => cases hr
          if he : b.edgeBool r x x then
            .done (edgeBool_iff.mp he)
          else
            have hrn : r.1 ∈ sroiqRoleNames p :=
              (sroiqRoleNames_of_concept (s.within.labels x hd')).2.2.2.2 r true rfl
            let next := stateAddEdge s r x x hrn
              (fun h1 h2 => by rw [h1] at h2; cases h2)
              (fun h1 h2 => by rw [h1] at h2; cases h2)
            .step {
              branches := [next]
              sound := fun i _ env hreal =>
                ⟨next, List.mem_cons_self .., env, addEdge_realizes hreal (hreal.labels x (.self r true) hd')⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .addEdge r x x hrn (.inl rfl) (fun h => he (edgeBool_iff.mpr h)) rfl }).mapDone
          fun h _ r hm => h (.self r true) hm r rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  let pMaxQual : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ n r c, .max n r c ∈ b.labels x →
      ∀ y, b.Edge r x y → c ∈ b.labels y ∨ c.dual ∈ b.labels y) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q => ∀ y, b.Edge q.2.1 x y → q.2.2 ∈ b.labels y ∨ q.2.2.dual ∈ b.labels y)
          (b.labels x) (fun | .max n r c => some (n, r, c) | _ => none) fun d hd q hq =>
          have hd' : .max q.1 q.2.1 q.2.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let r := q.2.1
          let c := q.2.2
          inspectNodes (P := fun y => b.Edge r x y → c ∈ b.labels y ∨ c.dual ∈ b.labels y) fun y =>
            if he : b.edgeBool r x y then
              if h1 : (b.labels y).contains c then
                .done fun _ => .inl (List.contains_iff_mem.mp h1)
              else if h2 : (b.labels y).contains c.dual then
                .done fun _ => .inr (List.contains_iff_mem.mp h2)
              else
                have hc1 : c ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, c])
                have hc2 : c.dual ∈ sroiqClos p := sroiqClos_operands (s.within.labels x hd') (by simp [operands, c])
                let s1 := stateAddLabel s y c hc1
                let s2 := stateAddLabel s y c.dual hc2
                .step {
                  branches := [s1, s2]
                  sound := fun i _ env hreal => by
                    rcases holds_or_dual i (env y) c with h | h
                    · exact ⟨s1, List.mem_cons_self .., env, addLabel_realizes hreal h⟩
                    · exact ⟨s2, List.mem_cons_of_mem _ (List.mem_cons_self ..), env, addLabel_realizes hreal h⟩
                  strict := fun b' hb' => by
                    rcases List.mem_cons.mp hb' with rfl | hb'
                    · exact .addLabel y c hc1 (fun hm => h1 (List.contains_iff_mem.mpr hm)) rfl
                    · obtain rfl := List.mem_singleton.mp hb'
                      exact .addLabel y c.dual hc2 (fun hm => h2 (List.contains_iff_mem.mpr hm)) rfl }
            else
              .done fun h => (he (edgeBool_iff.mpr h)).elim).mapDone fun h _ n r c hm y hy =>
          h (.max n r c) hm (n, r, c) rfl y hy
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  (((pConj.andThen fun _ => pDisj).andThen fun _ => pAll).andThen fun _ => pSelf).andThen
    (fun _ => pMaxQual) |>.mapDone fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩

private def inspectTBox {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ q ∈ p.tbox, ∀ x, s.forest.reblock.Unblocked x →
      q.sub.dual ∈ s.forest.labels x ∨ q.sup ∈ s.forest.labels x) :=
  let b := s.forest
  inspectList p.tbox fun q hq =>
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        if h1 : (b.labels x).contains q.sub.dual then
          .done fun _ => .inl (List.contains_iff_mem.mp h1)
        else if h2 : (b.labels x).contains q.sup then
          .done fun _ => .inr (List.contains_iff_mem.mp h2)
        else
          have ⟨hc1, hc2⟩ := tbox_mem_sroiqClos hq
          let s1 := stateAddLabel s x q.sub.dual hc1
          let s2 := stateAddLabel s x q.sup hc2
          .step {
            branches := [s1, s2]
            sound := fun i hm env hreal => by
              rcases holds_or_dual i (env x) q.sub with hsub | hdual
              · exact ⟨s2, List.mem_cons_of_mem _ (List.mem_cons_self ..), env,
                  addLabel_realizes hreal (hm.tbox q hq (env x) hsub)⟩
              · exact ⟨s1, List.mem_cons_self .., env, addLabel_realizes hreal hdual⟩
            strict := fun b' hb' => by
              rcases List.mem_cons.mp hb' with rfl | hb'
              · exact .addLabel x q.sub.dual hc1 (fun h => h1 (List.contains_iff_mem.mpr h)) rfl
              · obtain rfl := List.mem_singleton.mp hb'
                exact .addLabel x q.sup hc2 (fun h => h2 (List.contains_iff_mem.mpr h)) rfl }
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim

private def inspectRules {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ q ∈ p.rules, ∀ x y, s.forest.Edge q.1 x y → s.forest.Edge q.2 x y) :=
  let b := s.forest
  inspectList p.rules fun q hq =>
    inspectNodes fun x =>
      inspectNodes fun y =>
        if h1 : b.edgeBool q.1 x y then
          if h2 : b.edgeBool q.2 x y then
            .done fun _ => edgeBool_iff.mp h2
          else
            have he1 : b.Edge q.1 x y := edgeBool_iff.mp h1
            have hrn : q.2.1 ∈ sroiqRoleNames p := (sroiqRoleNames_of_rule hq).2
            let next := stateAddEdge s q.2 x y hrn
              (fun hxf hyt hp => s.geom.toRootBound x (q.1, y) (edge_toRoot_left he1 hxf hyt hp))
              (fun hxt hyf hp => s.geom.toRootBound y (converse q.1, x) (edge_toRoot_right he1 hxt hyf hp))
            .step {
              branches := [next]
              sound := fun i hm env hreal =>
                ⟨next, List.mem_cons_self .., env,
                  addEdge_realizes hreal (hm.rules q hq (env x) (env y) (hreal.edges q.1 x y he1))⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .addEdge q.2 x y hrn (edge_admissible_of_edge he1)
                  (fun h => h2 (edgeBool_iff.mpr h)) rfl }
        else
          .done fun h => (h1 (edgeBool_iff.mpr h)).elim

private def inspectReflexive {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ r ∈ p.chars.reflexive, ∀ x, s.forest.Edge (r, false) x x) :=
  let b := s.forest
  inspectList p.chars.reflexive fun r hr =>
    inspectNodes fun x =>
      if he : b.edgeBool (r, false) x x then
        .done (edgeBool_iff.mp he)
      else
        have hrn : r ∈ sroiqRoleNames p := sroiqRoleNames_of_refl hr
        let next := stateAddEdge s (r, false) x x hrn
          (fun h1 h2 => by rw [h1] at h2; cases h2)
          (fun h1 h2 => by rw [h1] at h2; cases h2)
        .step {
          branches := [next]
          sound := fun i hm env hreal =>
            ⟨next, List.mem_cons_self .., env, addEdge_realizes hreal (hm.reflexive r hr (env x))⟩
          strict := fun b' hb' => by
            obtain rfl := List.mem_singleton.mp hb'
            exact .addEdge (r, false) x x hrn (.inl rfl) (fun h => he (edgeBool_iff.mpr h)) rfl }

private def inspectGuardSteps {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ x y r, s.forest.Edge r x y →
      ∀ g ∈ s.forest.guardLabels x, ∀ k ∈ g.advance r, k ∈ s.forest.guardLabels y) :=
  let b := s.forest
  (inspectNodes fun x =>
    inspectNodes fun y =>
      inspectList (P := fun r => b.Edge r x y → ∀ g ∈ b.guardLabels x, ∀ k ∈ g.advance r, k ∈ b.guardLabels y)
        (sroiqOrientedRoles p) fun r _ =>
        if he : b.edgeBool r x y then
          (inspectList (b.guardLabels x) fun g hg =>
            inspectList (g.advance r) fun k hk =>
              if hky : (b.guardLabels y).contains k then
                .done (List.contains_iff_mem.mp hky)
              else
                have hkIn : k ∈ sroiqGuards rank p := sroiq_guards_closed (s.within.guards x hg) r hk
                let next := stateAddGuard s y k hkIn
                .step {
                  branches := [next]
                  sound := fun i _ env hreal =>
                    ⟨next, List.mem_cons_self .., env,
                      addGuard_realizes hreal
                        (guard_step_sound (hreal.guards x g hg) (hreal.edges r x y (edgeBool_iff.mp he)) hk)⟩
                  strict := fun b' hb' => by
                    obtain rfl := List.mem_singleton.mp hb'
                    exact .addGuard y k hkIn (fun h => hky (List.contains_iff_mem.mpr h)) rfl }).mapDone
            fun h _ => h
        else
          .done fun h => (he (edgeBool_iff.mpr h)).elim).mapDone fun h x y r hr g hg k hk =>
    h x y r (mem_sroiqOrientedRoles (edge_role_within s.within.roles hr)) hr g hg k hk

private def inspectGuardAccept {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ x, ∀ g ∈ s.forest.guardLabels x,
      g.state.nullable = true → g.filler ∈ s.forest.labels x) :=
  let b := s.forest
  inspectNodes fun x =>
    inspectList (b.guardLabels x) fun g hg =>
      if hnull : g.state.nullable = true then
        if hf : (b.labels x).contains g.filler then
          .done fun _ => List.contains_iff_mem.mp hf
        else
          have hfClos : g.filler ∈ sroiqClos p := sroiq_guard_filler_mem (s.within.guards x hg)
          let next := stateAddLabel s x g.filler hfClos
          .step {
            branches := [next]
            sound := fun i _ env hreal =>
              ⟨next, List.mem_cons_self .., env,
                addLabel_realizes hreal (guard_accept_sound (hreal.guards x g hg) hnull)⟩
            strict := fun b' hb' => by
              obtain rfl := List.mem_singleton.mp hb'
              exact .addLabel x g.filler hfClos (fun h => hf (List.contains_iff_mem.mpr h)) rfl }
      else
        .done fun h => (hnull h).elim

/-! ### 6. The NN-rule (`inspectNN`) -/

private def nnMergeBranches {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (x y : s.forest.Node) (r : OrientedRole) (c : Concept)
    (ts : List s.forest.Node) (hm : (x, r, c, ts) ∈ s.forest.nnBounds)
    (hy_nr : s.forest.isRoot y = false)
    (hdepthSum : s.forest.depth y + s.forest.nomLevel x ≤ sroiqMaxDepth rank p) :
    (xs : List s.forest.Node) → (∀ o ∈ xs, o ∈ ts) →
    { bs : List (SROIQState rank p) //
      (∀ o ∈ xs, ¬ s.forest.RecordedDistinct o y →
        ∃ next ∈ bs, ∀ i env, s.forest.Realizes i env → env o = env y →
          ∃ env', next.forest.Realizes i env') ∧
      (∀ next ∈ bs, SROIQStrictStep rank p s.forest next.forest) }
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | o :: xs, hsub =>
    let tail := nnMergeBranches s x y r c ts hm hy_nr hdepthSum xs (fun z hz => hsub z (List.mem_cons_of_mem _ hz))
    if hrec : s.forest.recordedDistinctBool o y then
      ⟨tail.1,
        fun w hw hnot => by
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact (hnot (recordedDistinctBool_iff.mp hrec)).elim
          · exact tail.2.1 w hw' hnot,
        tail.2.2⟩
    else
      have hoMem : o ∈ ts := hsub o (List.mem_cons_self ..)
      have ⟨hor, holvl⟩ := (s.forest.nnBounds_valid _ hm).2 o hoMem
      have hy0 : y ≠ 0 := fun h => by rw [h, s.forest.root0] at hy_nr; cases hy_nr
      have hoy : o ≠ y := fun h => by rw [h, hy_nr] at hor; cases hor
      have hk : o ∈ s.forest.retained y := retained_of_isRoot hor hoy
      have hvalid : s.forest.MergeValid o y := .inl ⟨hor, fun h => by rw [hy_nr] at h; cases h⟩
      have hbr : s.forest.isRoot o = true → s.forest.isRoot y = false →
          s.forest.isRoot (s.forest.parent y) = false → s.forest.parent (s.forest.parent y) ≠ o →
          s.forest.depth (s.forest.parent y) + s.forest.nomLevel o ≤ sroiqMaxDepth rank p := fun _ _ _ _ => by
        have hch : s.forest.Child (s.forest.parent y) y := ⟨hy_nr, rfl⟩
        have hdp := depth_child hch
        dsimp only at holvl
        omega
      let next := stateMerge s o y hy0 hk hvalid hbr
      ⟨next :: tail.1,
        fun w hw hnot => by
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨next, List.mem_cons_self .., fun i env hreal heq =>
              ⟨_, mergeForest_realizes hreal hy0 hk hvalid heq⟩⟩
          · obtain ⟨b', hb', hsound⟩ := tail.2.1 w hw' hnot
            exact ⟨b', List.mem_cons_of_mem _ hb', hsound⟩,
        fun b' hb' => by
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact .blockableMerge o y hy0 hk hvalid hy_nr
              (fun h => hrec (recordedDistinctBool_iff.mpr h)) rfl
          · exact tail.2.2 b' hb'⟩

private def inspectNN {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ x, s.forest.isRoot x = true →
      ∀ n r c, .max n r c ∈ s.forest.labels x →
      ∀ y, s.forest.reblock.Unblocked y → s.forest.isRoot y = false → s.forest.parent y ≠ x →
      s.forest.Edge r x y → c ∉ s.forest.labels y) :=
  let b := s.forest
  inspectNodes fun x =>
    if hxr : b.isRoot x = true then
      (inspectMatch (P := fun q =>
          ∀ y, b.reblock.Unblocked y → b.isRoot y = false → b.parent y ≠ x →
            b.Edge q.2.1 x y → q.2.2 ∉ b.labels y)
        (b.labels x) (fun | .max n r c => some (n, r, c) | _ => none) fun d hd q hq =>
        have hd' : .max q.1 q.2.1 q.2.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
        let n := q.1
        let r := q.2.1
        let c := q.2.2
        inspectNodes fun y =>
          if hcond : b.isUnblockedBool y = true ∧ b.isRoot y = false ∧ b.parent y ≠ x ∧
              b.edgeBool r x y = true ∧ (b.labels y).contains c = true then
            have hy_nr : b.isRoot y = false := hcond.2.1
            have hpy : b.parent y ≠ x := hcond.2.2.1
            have hed : b.Edge r x y := edgeBool_iff.mp hcond.2.2.2.1
            have hcy : c ∈ b.labels y := List.contains_iff_mem.mp hcond.2.2.2.2
            have htr : (converse r, x) ∈ b.toRoot y := edge_toRoot_right hed hxr hy_nr hpy
            have hdepthSum : b.depth y + b.nomLevel x ≤ sroiqMaxDepth rank p := s.geom.toRootBound y _ htr
            let pred (e : b.Node × OrientedRole × Concept × List b.Node) : Bool :=
              e.1 == x && e.2.1 == r && e.2.2.1 == c
            match hfind : b.nnBounds.find? pred with
            | some e =>
              have hm0 : e ∈ b.nnBounds := List.mem_of_find?_eq_some hfind
              have heq : pred e = true := List.find?_some (p := pred) hfind
              have hm : (x, r, c, e.2.2.2) ∈ b.nnBounds := by
                simp only [pred, Bool.and_eq_true, beq_iff_eq] at heq
                rcases e with ⟨u, s', d', ts⟩
                simp only at heq
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
                exact hm0
              let res := nnMergeBranches s x y r c e.2.2.2 hm hy_nr hdepthSum e.2.2.2 (fun _ h => h)
              .step {
                branches := res.1
                sound := fun i _ env hreal => by
                  obtain ⟨o, ho, heqo⟩ := hreal.nnBounds (x, r, c, e.2.2.2) hm (env y)
                    (hreal.edges r x y hed) (hreal.labels y c hcy)
                  have hnotRec : ¬ b.RecordedDistinct o y := fun hrec => by
                    rcases hrec with h | h
                    · exact hreal.unequal o y h heqo.symm
                    · exact hreal.unequal y o h heqo
                  obtain ⟨next, hmem, hmk⟩ := res.2.1 o ho hnotRec
                  exact ⟨next, hmem, hmk i env hreal heqo.symm⟩
                strict := res.2.2 }
            | none =>
              have hnoNN : ¬ b.HasNNBound x (.max n r c) := by
                rintro ⟨ts, hts⟩
                have hbad := List.find?_eq_none.mp hfind (x, r, c, ts) hts
                simp [pred] at hbad
              if hn0 : n = 0 then
                .step (closeStep fun i _ env hreal => by
                  have hmax := hreal.labels x (.max n r c) hd'
                  rw [hn0] at hmax
                  exact hmax ⟨[env y], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun z hz => by
                    obtain rfl := List.mem_singleton.mp hz
                    exact ⟨hreal.edges r x y hed, hreal.labels y c hcy⟩⟩)
              else
                have hch : b.Child (b.parent y) y := ⟨hy_nr, rfl⟩
                have hdy : b.depth y = b.depth (b.parent y) + 1 := depth_child hch
                have hlvl : b.nomLevel x + 1 ≤ sroiqMaxDepth rank p := by omega
                have hmaxClos : .max n r c ∈ sroiqClos p := s.within.labels x hd'
                have hrn : r.1 ∈ sroiqRoleNames p := edge_role_within s.within.roles hed
                have hcClos : c ∈ sroiqClos p := s.within.labels y hcy
                let ms := (List.range n).map (· + 1)
                let branches := ms.map fun m => stateAppendNNRoots s m x hxr r c hrn hcClos hlvl
                .step {
                  branches := branches
                  sound := fun i _ env hreal => by
                    let P (z : i.Object) : Prop := holdsOriented i r (env x) z ∧ holds i z c
                    have h1 : AtLeast 1 P := ⟨[env y], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun z hz => by
                      obtain rfl := List.mem_singleton.mp hz
                      exact ⟨hreal.edges r x y hed, hreal.labels y c hcy⟩⟩
                    have hmax : ¬ AtLeast (n + 1) P := hreal.labels x (.max n r c) hd'
                    obtain ⟨m, hm1, hm2, ws, hlen, hnd, hsp, hcov⟩ := exists_maximal_witnesses h1 hmax
                    have hmMem : m ∈ ms := List.mem_map.mpr ⟨m - 1, List.mem_range.mpr (by omega), by omega⟩
                    refine ⟨stateAppendNNRoots s m x hxr r c hrn hcClos hlvl,
                      List.mem_map.mpr ⟨m, hmMem, rfl⟩, ?_⟩
                    exact appendNNRoots_realizes hreal hxr hlen hnd hsp
                      (fun z hz1 hz2 => hcov z ⟨hz1, hz2⟩)
                  strict := fun b' hb' => by
                    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb'
                    exact .nnExpand m x hxr r c n hmaxClos hnoNN hlvl rfl }
          else
            .done fun huy hynr hpy hed hcy =>
              hcond ⟨isUnblockedBool_iff.mpr huy, hynr, hpy, edgeBool_iff.mpr hed,
                List.contains_iff_mem.mpr hcy⟩).mapDone fun h _ n r c hm y huy hynr hpy hed hcy =>
        h (.max n r c) hm (n, r, c) rfl y huy hynr hpy hed hcy
    else
      .done fun h => (hxr h).elim

/-! ### 7. Qualified upper-bound merging (`inspectUpperBounds`) -/

private theorem neighbor_of_blockable_cases {b : BlockedForest} {r : OrientedRole}
    {x w : b.Node} (hx : b.isRoot x = false) (he : b.Edge r x w) :
    (b.isRoot w = true ∧ (w = b.parent x ∨ (r, w) ∈ b.toRoot x)) ∨
    (b.isRoot w = false ∧ (w = x ∨ w = b.parent x ∨ b.Child x w)) := by
  rcases he with ⟨rfl, _⟩ | ⟨hxr, _, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
  · exact .inr ⟨hx, .inl rfl⟩
  · rw [hx] at hxr; cases hxr
  · exact .inr ⟨hc.1, .inr (.inr hc)⟩
  · cases hw : b.isRoot w with
    | true => exact .inl ⟨rfl, .inl hc.2.symm⟩
    | false => exact .inr ⟨rfl, .inr (.inl hc.2.symm)⟩
  · exact .inl ⟨(b.toRoot_valid x _ htr).2.1, .inr htr⟩
  · have h := (b.toRoot_valid w _ htr).2.1; rw [hx] at h; cases h

private theorem retained_of_depth_lt {b : BlockedForest} {u v : b.Node}
    (h : b.depth u < b.depth v) : u ∈ b.retained v := by
  refine mem_retained.mpr ⟨fun heq => Nat.lt_irrefl _ (heq ▸ h), fun hanc => ?_⟩
  exact Nat.lt_asymm h hanc.depth_lt

private theorem retained_of_same_depth {b : BlockedForest} {u v : b.Node}
    (hne : u ≠ v) (h : b.depth u = b.depth v) : u ∈ b.retained v := by
  refine mem_retained.mpr ⟨hne, fun hanc => ?_⟩
  have hlt := hanc.depth_lt
  omega

private def orientNeighborMerge {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (x u v : s.forest.Node) (r : OrientedRole) (c : Concept)
    (hu : u ∈ s.forest.qualifiedNeighbors x r c)
    (hv : v ∈ s.forest.qualifiedNeighbors x r c)
    (hne : u ≠ v) (hnotRec : ¬ s.forest.RecordedDistinct u v) :
    { next : SROIQState rank p //
      (∀ i env, s.forest.Realizes i env → env u = env v → ∃ env', next.forest.Realizes i env') ∧
      SROIQStrictStep rank p s.forest next.forest } :=
  let b := s.forest
  have huSpec := mem_qualifiedNeighbors.mp hu
  have hvSpec := mem_qualifiedNeighbors.mp hv
  if hur : b.isRoot u = true then
    if hvr : b.isRoot v = true then
      let spec := orientRootMerge_spec hne s.geom.nomLevel0
      let pair := b.orientRootMerge u v
      let keep := pair.1
      let drop := pair.2
      have hcases : (keep = u ∧ drop = v) ∨ (keep = v ∧ drop = u) := spec.1
      have hkr : b.isRoot keep = true := hcases.elim (fun h => h.1 ▸ hur) (fun h => h.1 ▸ hvr)
      have hdr : b.isRoot drop = true := hcases.elim (fun h => h.2 ▸ hvr) (fun h => h.2 ▸ hur)
      have hk : keep ∈ b.retained drop := retained_of_isRoot hkr spec.2.1
      have hvalid : b.MergeValid keep drop := .inl ⟨hkr, fun _ => spec.2.2.2⟩
      let next := stateMerge s keep drop spec.2.2.1 hk hvalid
        (fun _ hf => by rw [hdr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => by
          have heq' : env keep = env drop :=
            hcases.elim (fun h => by rw [h.1, h.2]; exact heq) (fun h => by rw [h.1, h.2]; exact heq.symm)
          exact ⟨_, mergeForest_realizes hreal spec.2.2.1 hk hvalid heq'⟩,
        .rootMerge keep drop spec.2.2.1 hk hvalid hdr rfl⟩
    else
      have hvnr : b.isRoot v = false := Bool.eq_false_iff.mpr hvr
      have hv0 : v ≠ 0 := fun h => by rw [h, b.root0] at hvnr; cases hvnr
      have hk : u ∈ b.retained v := retained_of_isRoot hur hne
      have hvalid : b.MergeValid u v := .inl ⟨hur, fun h => by rw [hvnr] at h; cases h⟩
      have hbr : b.isRoot u = true → b.isRoot v = false →
          b.isRoot (b.parent v) = false → b.parent (b.parent v) ≠ u →
          b.depth (b.parent v) + b.nomLevel u ≤ sroiqMaxDepth rank p := by
        intro _ _ hpnr hpp
        cases hxr : b.isRoot x with
        | true =>
          rcases hvSpec.1 hxr with hvrt | hch
          · rw [hvrt] at hvnr; cases hvnr
          · rw [hch.2, hxr] at hpnr; cases hpnr
        | false =>
          rcases neighbor_of_blockable_cases hxr huSpec.2.1 with ⟨_, hup | hutr⟩ | ⟨huf, _⟩
          · rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨hvrt, _⟩ | ⟨_, rfl | rfl | hch⟩
            · rw [hvrt] at hvnr; cases hvnr
            · rw [← hup, hur] at hpnr; cases hpnr
            · exact (hne hup).elim
            · exact (hpp (by rw [hch.2, hup])).elim
          · have htb : b.depth x + b.nomLevel u ≤ sroiqMaxDepth rank p := s.geom.toRootBound x (r, u) hutr
            rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨hvrt, _⟩ | ⟨_, rfl | rfl | hch⟩
            · rw [hvrt] at hvnr; cases hvnr
            · have hlt := (Anc.parent (⟨hvnr, rfl⟩ : b.Child (b.parent v) v)).depth_lt
              omega
            · have h1 := (Anc.parent (⟨hvnr, rfl⟩ : b.Child (b.parent (b.parent x)) (b.parent x))).depth_lt
              have h2 := (Anc.parent (⟨hxr, rfl⟩ : b.Child (b.parent x) x)).depth_lt
              omega
            · rw [hch.2]; exact htb
          · rw [hur] at huf; cases huf
      let next := stateMerge s u v hv0 hk hvalid hbr
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hv0 hk hvalid heq⟩,
        .blockableMerge u v hv0 hk hvalid hvnr hnotRec rfl⟩
  else if hvr : b.isRoot v = true then
    have hunr : b.isRoot u = false := Bool.eq_false_iff.mpr hur
    have hu0 : u ≠ 0 := fun h => by rw [h, b.root0] at hunr; cases hunr
    have hk : v ∈ b.retained u := retained_of_isRoot hvr (Ne.symm hne)
    have hvalid : b.MergeValid v u := .inl ⟨hvr, fun h => by rw [hunr] at h; cases h⟩
    have hbr : b.isRoot v = true → b.isRoot u = false →
        b.isRoot (b.parent u) = false → b.parent (b.parent u) ≠ v →
        b.depth (b.parent u) + b.nomLevel v ≤ sroiqMaxDepth rank p := by
      intro _ _ hpnr hpp
      cases hxr : b.isRoot x with
      | true =>
        rcases huSpec.1 hxr with hurt | hch
        · rw [hurt] at hunr; cases hunr
        · rw [hch.2, hxr] at hpnr; cases hpnr
      | false =>
        rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨_, hvp | hvtr⟩ | ⟨hvf, _⟩
        · rcases neighbor_of_blockable_cases hxr huSpec.2.1 with ⟨hurt, _⟩ | ⟨_, rfl | rfl | hch⟩
          · rw [hurt] at hunr; cases hunr
          · rw [← hvp, hvr] at hpnr; cases hpnr
          · exact (hne hvp.symm).elim
          · exact (hpp (by rw [hch.2, hvp])).elim
        · have htb : b.depth x + b.nomLevel v ≤ sroiqMaxDepth rank p := s.geom.toRootBound x (r, v) hvtr
          rcases neighbor_of_blockable_cases hxr huSpec.2.1 with ⟨hurt, _⟩ | ⟨_, rfl | rfl | hch⟩
          · rw [hurt] at hunr; cases hunr
          · have hlt := (Anc.parent (⟨hunr, rfl⟩ : b.Child (b.parent u) u)).depth_lt
            omega
          · have h1 := (Anc.parent (⟨hunr, rfl⟩ : b.Child (b.parent (b.parent x)) (b.parent x))).depth_lt
            have h2 := (Anc.parent (⟨hxr, rfl⟩ : b.Child (b.parent x) x)).depth_lt
            omega
          · rw [hch.2]; exact htb
        · rw [hvr] at hvf; cases hvf
    let next := stateMerge s v u hu0 hk hvalid hbr
    ⟨next,
      fun i env hreal heq => ⟨_, mergeForest_realizes hreal hu0 hk hvalid heq.symm⟩,
      .blockableMerge v u hu0 hk hvalid hunr (fun h => hnotRec h.symm) rfl⟩
  else
    have hunr : b.isRoot u = false := Bool.eq_false_iff.mpr hur
    have hvnr : b.isRoot v = false := Bool.eq_false_iff.mpr hvr
    have hu0 : u ≠ 0 := fun h => by rw [h, b.root0] at hunr; cases hunr
    have hv0 : v ≠ 0 := fun h => by rw [h, b.root0] at hvnr; cases hvnr
    if hpar : b.parent u = b.parent v then
      have hk : u ∈ b.retained v := retained_of_same_depth hne (by
        have h1 : b.Child (b.parent u) u := ⟨hunr, rfl⟩
        have h2 : b.Child (b.parent v) v := ⟨hvnr, rfl⟩
        rw [depth_child h1, depth_child h2, hpar])
      have hvalid : b.MergeValid u v := .inr ⟨hunr, hvnr, .inl hpar⟩
      let next := stateMerge s u v hv0 hk hvalid (fun hf => by rw [hunr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hv0 hk hvalid heq⟩,
        .blockableMerge u v hv0 hk hvalid hvnr hnotRec rfl⟩
    else if hch1 : b.parent v = u then
      have hch : b.Child u v := ⟨hvnr, hch1⟩
      have hk : u ∈ b.retained v := retained_of_depth_lt (Anc.parent hch).depth_lt
      have hvalid : b.MergeValid u v := .inr ⟨hunr, hvnr, .inr (.inl hch)⟩
      let next := stateMerge s u v hv0 hk hvalid (fun hf => by rw [hunr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hv0 hk hvalid heq⟩,
        .blockableMerge u v hv0 hk hvalid hvnr hnotRec rfl⟩
    else if hch2 : b.parent u = v then
      have hch : b.Child v u := ⟨hunr, hch2⟩
      have hk : v ∈ b.retained u := retained_of_depth_lt (Anc.parent hch).depth_lt
      have hvalid : b.MergeValid v u := .inr ⟨hvnr, hunr, .inr (.inl hch)⟩
      let next := stateMerge s v u hu0 hk hvalid (fun hf => by rw [hvnr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hu0 hk hvalid heq.symm⟩,
        .blockableMerge v u hu0 hk hvalid hunr (fun h => hnotRec h.symm) rfl⟩
    else if hgp1 : b.isRoot (b.parent v) = false ∧ b.parent (b.parent v) = u then
      have hgp : b.Child u (b.parent v) := hgp1
      have hanc : b.Anc u v := .step (.parent hgp) ⟨hvnr, rfl⟩
      have hk : u ∈ b.retained v := retained_of_depth_lt hanc.depth_lt
      have hvalid : b.MergeValid u v := .inr ⟨hunr, hvnr, .inr (.inr hgp)⟩
      let next := stateMerge s u v hv0 hk hvalid (fun hf => by rw [hunr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hv0 hk hvalid heq⟩,
        .blockableMerge u v hv0 hk hvalid hvnr hnotRec rfl⟩
    else
      have hgp2 : b.Child v (b.parent u) := by
        cases hxr : b.isRoot x with
        | true =>
          rcases huSpec.1 hxr with hu1 | hcu
          · rw [hu1] at hunr; cases hunr
          · rcases hvSpec.1 hxr with hv1 | hcv
            · rw [hv1] at hvnr; cases hvnr
            · exact (hpar (hcu.2.trans hcv.2.symm)).elim
        | false =>
          rcases neighbor_of_blockable_cases hxr huSpec.2.1 with ⟨hu1, _⟩ | ⟨_, rfl | rfl | hcu⟩
          · rw [hu1] at hunr; cases hunr
          · rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨hv1, _⟩ | ⟨_, rfl | rfl | hcv⟩
            · rw [hv1] at hvnr; cases hvnr
            · exact (hne rfl).elim
            · exact (hch2 rfl).elim
            · exact (hch1 hcv.2).elim
          · rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨hv1, _⟩ | ⟨_, rfl | rfl | hcv⟩
            · rw [hv1] at hvnr; cases hvnr
            · exact (hch1 rfl).elim
            · exact (hne rfl).elim
            · exact (hgp1 ⟨hcv.2.symm ▸ hxr, by rw [hcv.2]⟩).elim
          · rcases neighbor_of_blockable_cases hxr hvSpec.2.1 with ⟨hv1, _⟩ | ⟨_, rfl | rfl | hcv⟩
            · rw [hv1] at hvnr; cases hvnr
            · exact (hch2 hcu.2).elim
            · exact ⟨hcu.2.symm ▸ hxr, by rw [hcu.2]⟩
            · exact (hpar (hcu.2.trans hcv.2.symm)).elim
      have hanc : b.Anc v u := .step (.parent hgp2) ⟨hunr, rfl⟩
      have hk : v ∈ b.retained u := retained_of_depth_lt hanc.depth_lt
      have hvalid : b.MergeValid v u := .inr ⟨hvnr, hunr, .inr (.inr hgp2)⟩
      let next := stateMerge s v u hu0 hk hvalid (fun hf => by rw [hvnr] at hf; cases hf)
      ⟨next,
        fun i env hreal heq => ⟨_, mergeForest_realizes hreal hu0 hk hvalid heq.symm⟩,
        .blockableMerge v u hu0 hk hvalid hunr (fun h => hnotRec h.symm) rfl⟩

private def upperBoundBranches {rank : Rank} {p : Problem} (s : SROIQState rank p)
    (x : s.forest.Node) (r : OrientedRole) (c : Concept) :
    (xs : List s.forest.Node) → (∀ w ∈ xs, w ∈ s.forest.qualifiedNeighbors x r c) →
    { bs : List (SROIQState rank p) //
      (∀ u ∈ xs, ∀ v ∈ xs, u.val < v.val → ¬ s.forest.RecordedDistinct u v →
        ∃ next ∈ bs, ∀ i env, s.forest.Realizes i env → env u = env v →
          ∃ env', next.forest.Realizes i env') ∧
      (∀ next ∈ bs, SROIQStrictStep rank p s.forest next.forest) }
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | u :: xs, hsub =>
    have hu : u ∈ s.forest.qualifiedNeighbors x r c := hsub u (List.mem_cons_self ..)
    let tail := upperBoundBranches s x r c xs (fun w hw => hsub w (List.mem_cons_of_mem _ hw))
    let rec pairWith : (ys : List s.forest.Node) →
        (∀ w ∈ ys, w ∈ s.forest.qualifiedNeighbors x r c) →
        { bs : List (SROIQState rank p) //
          (∀ v ∈ ys, u ≠ v → ¬ s.forest.RecordedDistinct u v →
            ∃ next ∈ bs, ∀ i env, s.forest.Realizes i env → env u = env v →
              ∃ env', next.forest.Realizes i env') ∧
          (∀ next ∈ bs, SROIQStrictStep rank p s.forest next.forest) }
      | [], _ => ⟨[], fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
      | v :: ys, hys =>
        let rest := pairWith ys (fun w hw => hys w (List.mem_cons_of_mem _ hw))
        if hcond : u ≠ v ∧ ¬ s.forest.recordedDistinctBool u v = true then
          let one := orientNeighborMerge s x u v r c hu (hys v (List.mem_cons_self ..))
            hcond.1 (fun h => hcond.2 (recordedDistinctBool_iff.mpr h))
          ⟨one.1 :: rest.1,
            fun w hw hne hnot => by
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact ⟨one.1, List.mem_cons_self .., one.2.1⟩
              · obtain ⟨b', hb', hmk⟩ := rest.2.1 w hw' hne hnot
                exact ⟨b', List.mem_cons_of_mem _ hb', hmk⟩,
            fun b' hb' => by
              rcases List.mem_cons.mp hb' with rfl | hb'
              · exact one.2.2
              · exact rest.2.2 b' hb'⟩
        else
          ⟨rest.1,
            fun w hw hne hnot => by
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact (hcond ⟨hne, fun h => hnot (recordedDistinctBool_iff.mp h)⟩).elim
              · exact rest.2.1 w hw' hne hnot,
            rest.2.2⟩
    let head := pairWith xs (fun w hw => hsub w (List.mem_cons_of_mem _ hw))
    ⟨head.1 ++ tail.1,
      fun a ha b' hb' hlt hnot => by
        rcases List.mem_cons.mp ha with haeq | ha'
        · subst a
          rcases List.mem_cons.mp hb' with hbeq | hb''
          · subst b'; exact (Nat.lt_irrefl _ hlt).elim
          · obtain ⟨next, hmem, hmk⟩ := head.2.1 b' hb'' (fun h => Nat.lt_irrefl _ (h ▸ hlt)) hnot
            exact ⟨next, List.mem_append_left _ hmem, hmk⟩
        · rcases List.mem_cons.mp hb' with hbeq | hb''
          · subst b'
            obtain ⟨next, hmem, hmk⟩ := head.2.1 a ha' (fun h => Nat.lt_irrefl _ (h ▸ hlt)) (fun h => hnot h.symm)
            exact ⟨next, List.mem_append_left _ hmem, fun i env hreal heq => hmk i env hreal heq.symm⟩
          · obtain ⟨next, hmem, hmk⟩ := tail.2.1 a ha' b' hb'' hlt hnot
            exact ⟨next, List.mem_append_right _ hmem, hmk⟩,
      fun next hmem => (List.mem_append.mp hmem).elim (head.2.2 next) (tail.2.2 next)⟩

private theorem not_nodup_map_exists_pair {α β : Type} {xs : List α} {f : α → β}
    (hnd : xs.Nodup) (hnot : ¬ (xs.map f).Nodup) :
    ∃ u ∈ xs, ∃ v ∈ xs, u ≠ v ∧ f u = f v := by
  induction xs with
  | nil => exact (hnot List.nodup_nil).elim
  | cons a xs ih =>
    have ⟨ha, hxs⟩ := List.nodup_cons.mp hnd
    by_cases hmem : f a ∈ xs.map f
    · obtain ⟨v, hv, hfv⟩ := List.mem_map.mp hmem
      exact ⟨a, List.mem_cons_self .., v, List.mem_cons_of_mem _ hv,
        fun h => ha (h ▸ hv), hfv.symm⟩
    · have hnot' : ¬ (xs.map f).Nodup := fun h => hnot (List.nodup_cons.mpr ⟨hmem, h⟩)
      obtain ⟨u, hu, v, hv, hne, heq⟩ := ih hxs hnot'
      exact ⟨u, List.mem_cons_of_mem _ hu, v, List.mem_cons_of_mem _ hv, hne, heq⟩

private def inspectUpperBounds {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (∀ x, s.forest.reblock.Unblocked x →
      ∀ n r c, .max n r c ∈ s.forest.labels x →
      ¬ AtLeast (n + 1) (fun y =>
        (s.forest.isRoot x = true → s.forest.isRoot y = true ∨ s.forest.Child x y) ∧
        s.forest.Edge r x y ∧ c ∈ s.forest.labels y)) :=
  let b := s.forest
  inspectNodes fun x =>
    if hux : b.isUnblockedBool x then
      (inspectMatch (P := fun q =>
          ¬ AtLeast (q.1 + 1) (fun y =>
            (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge q.2.1 x y ∧ q.2.2 ∈ b.labels y))
        (b.labels x) (fun | .max n r c => some (n, r, c) | _ => none) fun d hd q hq =>
        have hd' : .max q.1 q.2.1 q.2.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
        let n := q.1
        let r := q.2.1
        let c := q.2.2
        let ys := b.qualifiedNeighbors x r c
        if hge : n + 1 ≤ ys.length then
          let res := upperBoundBranches s x r c ys (fun _ h => h)
          .step {
            branches := res.1
            sound := fun i _ env hreal => by
              have hmax : ¬ AtLeast (n + 1) (fun z => holdsOriented i r (env x) z ∧ holds i z c) :=
                hreal.labels x (.max n r c) hd'
              have hnotNd : ¬ (ys.map env).Nodup := by
                intro hnd
                apply hmax
                refine ⟨(ys.map env).take (n + 1), by simp [hge], hnd.sublist (List.take_sublist _ _), ?_⟩
                intro z hz
                have hz' := List.mem_of_mem_take hz
                obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz'
                have hySpec := mem_qualifiedNeighbors.mp hy
                exact ⟨hreal.edges r x y hySpec.2.1, hreal.labels y c hySpec.2.2⟩
              obtain ⟨u, hu, v, hv, hne, heq⟩ :=
                not_nodup_map_exists_pair (qualifiedNeighbors_nodup b x r c) hnotNd
              have hord : (u.val < v.val ∧ u ∈ ys ∧ v ∈ ys ∧ env u = env v) ∨
                          (v.val < u.val ∧ v ∈ ys ∧ u ∈ ys ∧ env v = env u) := by
                rcases Nat.lt_trichotomy u.val v.val with h1 | h2 | h3
                · exact .inl ⟨h1, hu, hv, heq⟩
                · exact (hne (Fin.ext h2)).elim
                · exact .inr ⟨h3, hv, hu, heq.symm⟩
              rcases hord with ⟨hlt, hu', hv', heq'⟩ | ⟨hlt, hv', hu', heq'⟩
              · have hnotRec : ¬ b.RecordedDistinct u v := fun hrec =>
                  hrec.elim (fun h => hreal.unequal u v h heq') (fun h => hreal.unequal v u h heq'.symm)
                obtain ⟨next, hmem, hmk⟩ := res.2.1 u hu' v hv' hlt hnotRec
                exact ⟨next, hmem, hmk i env hreal heq'⟩
              · have hnotRec : ¬ b.RecordedDistinct v u := fun hrec =>
                  hrec.elim (fun h => hreal.unequal v u h heq') (fun h => hreal.unequal u v h heq'.symm)
                obtain ⟨next, hmem, hmk⟩ := res.2.1 v hv' u hu' hlt hnotRec
                exact ⟨next, hmem, hmk i env hreal heq'⟩
            strict := res.2.2 }
        else
          .done fun ⟨ws, hlen, hnd, hsp⟩ => by
            have hsub : ws ⊆ ys := fun w hw => mem_qualifiedNeighbors.mpr (hsp w hw)
            have hle := hnd.length_le_of_subset hsub
            omega).mapDone fun h _ n r c hm => h (.max n r c) hm (n, r, c) rfl
    else
      .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim

/-! ### 8. Witness generation (`inspectWitnesses`) -/

private def inspectWitnesses {rank : Rank} {p : Problem} (s : SROIQState rank p) :
    Inspection rank p s (
      (∀ x, s.forest.reblock.Unblocked x → ∀ r c, .some r c ∈ s.forest.labels x →
        ∃ y, (s.forest.isRoot x = true → s.forest.isRoot y = true ∨ s.forest.Child x y) ∧
          s.forest.Edge r x y ∧ c ∈ s.forest.labels y) ∧
      (∀ x, s.forest.reblock.Unblocked x → ∀ n r c, .min n r c ∈ s.forest.labels x →
        AtLeast n (fun y => (s.forest.isRoot x = true → s.forest.isRoot y = true ∨ s.forest.Child x y) ∧
          s.forest.Edge r x y ∧ c ∈ s.forest.labels y))) :=
  let b := s.forest
  let pSome : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ r c, .some r c ∈ b.labels x →
      ∃ y, (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge r x y ∧ c ∈ b.labels y) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q =>
            ∃ y, (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge q.1 x y ∧ q.2 ∈ b.labels y)
          (b.labels x) (fun | .some r c => some (r, c) | _ => none) fun d hd q hq =>
          have hd' : .some q.1 q.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let r := q.1
          let c := q.2
          let ys := b.qualifiedNeighbors x r c
          match hys : ys with
          | y :: _ =>
            .done ⟨y, mem_qualifiedNeighbors.mp (by change y ∈ ys; rw [hys]; exact List.mem_cons_self ..)⟩
          | [] =>
            have hdx : b.depth x ≤ sroiqMaxDepth rank p :=
              unblocked_depth_le s.within (isUnblockedBool_iff.mp hux)
            have hsClos : .some r c ∈ sroiqClos p := s.within.labels x hd'
            have hrn : r.1 ∈ sroiqRoleNames p := (sroiqRoleNames_of_concept hsClos).1 r c rfl
            have hcClos : c ∈ sroiqClos p := sroiqClos_operands hsClos (by simp [operands])
            have hnotProt : ¬ b.GenProtected x (.some r c) := by
              rintro ⟨ws, hlen, _, _, hsp⟩
              cases ws with
              | nil => cases hlen
              | cons w _ =>
                have hm : w ∈ ys := mem_qualifiedNeighbors.mpr (hsp w (List.mem_cons_self ..))
                rw [hys] at hm; cases hm
            let next := stateAppendChildren s 1 x r c hrn hcClos hdx
            .step {
              branches := [next]
              sound := fun i _ env hreal => by
                obtain ⟨w, hw1, hw2⟩ := hreal.labels x (.some r c) hd'
                refine ⟨next, List.mem_cons_self .., ?_⟩
                exact appendChildren_realizes hreal ⟨[w], rfl,
                  List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
                  fun z hz => by obtain rfl := List.mem_singleton.mp hz; exact ⟨hw1, hw2⟩⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .generate 1 x r c hdx hrn hcClos (.inl ⟨hsClos, rfl, hnotProt⟩) rfl }).mapDone
          fun h _ r c hm => h (.some r c) hm (r, c) rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  let pMin : Inspection rank p s (∀ x, b.reblock.Unblocked x → ∀ n r c, .min n r c ∈ b.labels x →
      AtLeast n (fun y => (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge r x y ∧ c ∈ b.labels y)) :=
    inspectNodes fun x =>
      if hux : b.isUnblockedBool x then
        (inspectMatch (P := fun q =>
            AtLeast q.1 (fun y => (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge q.2.1 x y ∧ q.2.2 ∈ b.labels y))
          (b.labels x) (fun | .min n r c => some (n, r, c) | _ => none) fun d hd q hq =>
          have hd' : .min q.1 q.2.1 q.2.2 ∈ b.labels x := by cases d <;> cases hq; exact hd
          let n := q.1
          let r := q.2.1
          let c := q.2.2
          let ys := b.qualifiedNeighbors x r c
          if hge : n ≤ ys.length then
            .done ⟨ys.take n, by simp [n, hge],
              (qualifiedNeighbors_nodup b x r c).sublist (List.take_sublist _ _),
              fun y hy => mem_qualifiedNeighbors.mp (List.mem_of_mem_take hy)⟩
          else
            have hdx : b.depth x ≤ sroiqMaxDepth rank p :=
              unblocked_depth_le s.within (isUnblockedBool_iff.mp hux)
            have hmClos : .min n r c ∈ sroiqClos p := s.within.labels x hd'
            have hrn : r.1 ∈ sroiqRoleNames p := (sroiqRoleNames_of_concept hmClos).2.2.1 n r c rfl
            have hcClos : c ∈ sroiqClos p := sroiqClos_operands hmClos (by simp [operands])
            have hnotProt : ¬ b.GenProtected x (.min n r c) := by
              rintro ⟨ws, hlen, hnd, _, hsp⟩
              have hsub : ws ⊆ ys := fun w hw => mem_qualifiedNeighbors.mpr (hsp w hw)
              have hle := hnd.length_le_of_subset hsub
              omega
            let next := stateAppendChildren s n x r c hrn hcClos hdx
            .step {
              branches := [next]
              sound := fun i _ env hreal =>
                ⟨next, List.mem_cons_self .., appendChildren_realizes hreal (hreal.labels x (.min n r c) hd')⟩
              strict := fun b' hb' => by
                obtain rfl := List.mem_singleton.mp hb'
                exact .generate n x r c hdx hrn hcClos (.inr ⟨hmClos, hnotProt⟩) rfl }).mapDone
          fun h _ n r c hm => h (.min n r c) hm (n, r, c) rfl
      else
        .done fun hu => (hux (isUnblockedBool_iff.mpr hu)).elim
  pSome.andThen fun _ => pMin

/-! ### Full fair `sroiqStep` sweep -/

private def sroiqSweep {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p)
    (rootResult : {r // r = solveDataCSP (s.forest.rootDataCSP p)}) :
    Inspection rank p s (s.forest.reblock.BlockedClashFree p ∧ s.forest.reblock.BlockedSaturated rank p) :=
  let all :=
    (((((((((((inspectClash hsroiqd s rootResult).andThen fun _ => inspectNomPos s).andThen
      fun _ => inspectKeyCls s).andThen
      fun _ => inspectKeyObjSplit s).andThen
      fun _ => inspectKeyMerge s).andThen
      fun _ => inspectLabels hsroiqd s).andThen
      fun _ => inspectTBox s).andThen
      fun _ => inspectRules s).andThen
      fun _ => inspectReflexive s).andThen
      fun _ => inspectGuardSteps s).andThen
      fun _ => inspectGuardAccept s).andThen
      fun _ => (inspectNN s).andThen fun _ =>
        (inspectUpperBounds s).andThen fun _ => inspectWitnesses s
  all.mapDone fun ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcf, hnomPos⟩, hkeyCls⟩, hkeyObj⟩, hkeyMerge⟩,
      ⟨hconj, hdisj, hguardStart, hselfPos, hmaxQual⟩⟩, htbox⟩, hrules⟩, hrefl⟩, hguardStep⟩, hguardAcc⟩,
      ⟨hnn, hmaxBound, hsome, hmin⟩⟩ =>
    have hbv : s.forest.reblock.BlockingValid := reblock_valid s.forest
    have hrootUnb : ∀ x y, s.forest.isRoot x = true →
        (s.forest.isRoot y = true ∨ s.forest.Child x y) → s.forest.reblock.Unblocked y := by
      intro x y hxr h
      rcases h with hyr | hch
      · exact root_unblocked hbv hyr
      · exact child_of_root_unblocked hbv hxr hch
    ⟨hcf, {
      blocking := hbv
      bindings := reblock_bindings s.bindings
      root := s.abox.root
      classAssertions := s.abox.classAssertions
      objAssertions := s.abox.objAssertions
      negObjAssertions := s.abox.negObjAssertions
      sameInds := fun ab hm r₁ r₂ h1 h2 =>
        hnomPos r₁ (root_unblocked hbv h1.isRoot) ab.2 r₂ (s.abox.sameInds ab hm r₁ h1) h2
      diffInds := s.abox.diffInds
      dataAssertions := s.abox.dataAssertions
      negDataAssertions := s.abox.negDataAssertions
      nomPos := hnomPos
      conj := hconj
      disj := hdisj
      some := fun x hux r c hm => by
        obtain ⟨y, hy1, hy2, hy3⟩ := hsome x hux r c hm
        exact ⟨y, fun hxr => hrootUnb x y hxr (hy1 hxr), hy2, hy3⟩
      min := fun x hux n r c hm => by
        obtain ⟨ws, hlen, hnd, hsp⟩ := hmin x hux n r c hm
        exact ⟨ws, hlen, hnd, fun y hy =>
          ⟨fun hxr => hrootUnb x y hxr ((hsp y hy).1 hxr), (hsp y hy).2.1, (hsp y hy).2.2⟩⟩
      maxQual := hmaxQual
      nnEliminated := hnn
      maxBound := hmaxBound
      selfPos := hselfPos
      tbox := htbox
      rules := hrules
      reflexive := hrefl
      guardStart := hguardStart
      guardStep := hguardStep
      guardAccept := hguardAcc
      keyCls := hkeyCls
      keyObjSplit := hkeyObj
      keyMerge := hkeyMerge }⟩

private def sroiqStepWith {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p)
    (rootResult : {r // r = solveDataCSP (s.forest.rootDataCSP p)}) :
    Option (SROIQCheckedStep rank p s) :=
  match sroiqSweep hsroiqd s rootResult with
  | .step t => some t
  | .done _ => none

/-- Single fair search step for full `SROIQ(D)`: returns `none` iff the reblocked
forest is clash-free and fully saturated; otherwise emits a sound, strictly
progressing branching transition. -/
def sroiqStep {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p) : Option (SROIQCheckedStep rank p s) :=
  sroiqStepWith hsroiqd s ⟨solveDataCSP (s.forest.rootDataCSP p), rfl⟩

private theorem sroiqStepWith_eq {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (s : SROIQState rank p) (result : {r // r = solveDataCSP (s.forest.rootDataCSP p)}) :
    sroiqStepWith hsroiqd s result = sroiqStep hsroiqd s :=
  congrArg (sroiqStepWith hsroiqd s) (Subtype.ext result.property)

theorem sroiqStep_fair {rank : Rank} {p : Problem} {hsroiqd : p.isSROIQD rank = true}
    {s : SROIQState rank p} (h : sroiqStep hsroiqd s = none) :
    s.forest.reblock.BlockedClashFree p ∧ s.forest.reblock.BlockedSaturated rank p := by
  unfold sroiqStep sroiqStepWith at h
  cases hs : sroiqSweep hsroiqd s ⟨solveDataCSP (s.forest.rootDataCSP p), rfl⟩ with
  | step t => rw [hs] at h; cases h
  | done hd => exact hd

/-! ### Search relation, refutations, verdicts, and fuel-free `decideSROIQDAccessible` -/

inductive SROIQFollows {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    SROIQState rank p → SROIQState rank p → Prop where
  | child {s next : SROIQState rank p} {t : SROIQCheckedStep rank p s}
      (hstep : sroiqStep hsroiqd s = some t) (hmem : next ∈ t.branches) :
      SROIQFollows hsroiqd next s

theorem SROIQFollows.strictStep {rank : Rank} {p : Problem} {hsroiqd : p.isSROIQD rank = true}
    {next s : SROIQState rank p} (h : SROIQFollows hsroiqd next s) :
    SROIQStrictStep rank p s.forest next.forest := by
  cases h with
  | child _ hmem => exact ‹SROIQCheckedStep rank p s›.strict next hmem

structure SROIQOpenLeaf (rank : Rank) (p : Problem) where
  forest : BlockedForest
  clashFree : forest.BlockedClashFree p
  saturated : forest.BlockedSaturated rank p

inductive SROIQRefutation {rank : Rank} {p : Problem} : SROIQState rank p → Prop where
  | step {s : SROIQState rank p} (t : SROIQCheckedStep rank p s)
      (closed : ∀ next ∈ t.branches, SROIQRefutation next) : SROIQRefutation s

theorem SROIQRefutation.sound {rank : Rank} {p : Problem} {s : SROIQState rank p}
    (ref : SROIQRefutation s) : ¬ s.forest.Sat p := by
  induction ref with
  | step t _ ih =>
    rintro ⟨i, hm, env, hreal⟩
    obtain ⟨next, hmem, env', hnext⟩ := t.sound i hm env hreal
    exact ih next hmem ⟨i, hm, env', hnext⟩

inductive SROIQVerdict {rank : Rank} {p : Problem} (s : SROIQState rank p) where
  | sat (leaf : SROIQOpenLeaf rank p)
  | unsat (ref : SROIQRefutation s)

private structure RootDataMemo where
  problem : DataCSP
  result : Option (List DataEdge)
  correct : result = solveDataCSP problem

private def solveRootData (problem : DataCSP) (memo : Option RootDataMemo) :
    {entry : RootDataMemo // entry.problem = problem} :=
  match memo with
  | none => ⟨⟨problem, solveDataCSP problem, rfl⟩, rfl⟩
  | some previous =>
    if h : previous.problem = problem then ⟨previous, h⟩
    else ⟨⟨problem, solveDataCSP problem, rfl⟩, rfl⟩

private def refreshLookups (forest : BlockedForest) : BlockedForest := forest

private def refreshLookupsIndexed (forest : BlockedForest) : BlockedForest :=
  let labels := Vector.ofFn forest.labels
  let guards := Vector.ofFn forest.guardLabels
  let loops := Vector.ofFn forest.loops
  let down := Vector.ofFn forest.down
  let up := Vector.ofFn forest.up
  { forest with
    labels := fun x => labels[x.val]
    guardLabels := fun x => guards[x.val]
    loops := fun x => loops[x.val]
    down := fun x => down[x.val]
    up := fun x => up[x.val] }

@[csimp] private theorem refreshLookups_eq_indexed : refreshLookups = refreshLookupsIndexed := by
  funext forest
  have lookupEq {α : Type} (get : forest.Node → α) :
      (fun x : forest.Node => (Vector.ofFn get)[x.val]) = get := by
    funext x
    exact Vector.getElem_ofFn x.isLt
  unfold refreshLookups refreshLookupsIndexed
  dsimp only
  rw [lookupEq forest.labels, lookupEq forest.guardLabels, lookupEq forest.loops,
    lookupEq forest.down, lookupEq forest.up]

-- Point updates close over earlier versions of these fields. Take an indexed
-- snapshot periodically along a branch to bound the lookup chain.
private def refreshState {rank : Rank} {p : Problem} (state : SROIQState rank p)
    (depth : Nat) : SROIQState rank p :=
  if depth % 64 = 0 then { state with forest := refreshLookups state.forest } else state

private theorem refreshState_eq {rank : Rank} {p : Problem} (state : SROIQState rank p)
    (depth : Nat) : refreshState state depth = state := by
  unfold refreshState
  split
  · cases state; rfl
  · rfl

private inductive BranchCheck {rank : Rank} {p : Problem} (xs : List (SROIQState rank p)) where
  | sat (leaf : SROIQOpenLeaf rank p)
  | closed (proof : ∀ next ∈ xs, SROIQRefutation next)

private def checkBranches {rank : Rank} {p : Problem} {s : SROIQState rank p}
    (t : SROIQCheckedStep rank p s)
    (visit : ∀ next ∈ t.branches, SROIQVerdict next) :
    (xs : List (SROIQState rank p)) → (∀ next ∈ xs, next ∈ t.branches) → BranchCheck xs
  | [], _ => .closed fun _ h => (List.not_mem_nil h).elim
  | x :: xs, hsub =>
    match visit x (hsub x (List.mem_cons_self ..)) with
    | .sat leaf => .sat leaf
    | .unsat ref =>
      match checkBranches t visit xs (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) with
      | .sat leaf => .sat leaf
      | .closed rest =>
        .closed fun y hy =>
          match List.mem_cons.mp hy with
          | .inl h => h ▸ ref
          | .inr h => rest y h

/-- Fuel-free decision procedure for any accessible `SROIQ(D)` search state. -/
def decideSROIQDAccessible {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    {s : SROIQState rank p} (acc : Acc (SROIQFollows hsroiqd) s) : SROIQVerdict s := by
  let A := { state : SROIQState rank p // Acc (SROIQFollows hsroiqd) state }
  let less : A → A → Prop := InvImage (SROIQFollows hsroiqd) Subtype.val
  let wf : WellFounded less := ⟨fun a => InvImage.accessible Subtype.val a.property⟩
  let run (state : A)
      (visit : ∀ next, less next state → Option RootDataMemo → Nat → SROIQVerdict next.val)
      (memo : Option RootDataMemo) (depth : Nat) : SROIQVerdict state.val :=
    let current := refreshState state.val depth
    have hcurrent : current = state.val := refreshState_eq state.val depth
    let problem := current.forest.rootDataCSP p
    let saved := solveRootData problem memo
    let result : {r // r = solveDataCSP problem} :=
      ⟨saved.val.result, saved.val.correct.trans (congrArg solveDataCSP saved.property)⟩
    match h : sroiqStepWith hsroiqd current result with
    | none =>
      let complete := sroiqStep_fair ((sroiqStepWith_eq hsroiqd current result).symm.trans h)
      .sat ⟨current.forest.reblock, complete.1, complete.2⟩
    | some t =>
      match checkBranches t
        (fun next hn =>
          have smaller : SROIQFollows hsroiqd next state.val :=
            hcurrent ▸ SROIQFollows.child ((sroiqStepWith_eq hsroiqd current result).symm.trans h) hn
          visit ⟨next, state.property.inv smaller⟩ smaller
            (some saved.val) (depth + 1))
        t.branches (fun _ h => h) with
      | .sat leaf => .sat leaf
      | .closed proof => .unsat (hcurrent ▸ .step t proof)
  exact wf.fix run ⟨s, acc⟩ none 1

theorem decideSROIQDAccessible_sat_iff {rank : Rank} {p : Problem} {hsroiqd : p.isSROIQD rank = true}
    (a : Acc (SROIQFollows hsroiqd) (SROIQState.initial rank p)) :
    (∃ leaf, decideSROIQDAccessible hsroiqd a = .sat leaf) ↔ p.Sat := by
  cases h : decideSROIQDAccessible hsroiqd a with
  | sat leaf =>
    exact ⟨fun _ => sroiqd_blocked_saturated_sat hsroiqd leaf.clashFree leaf.saturated, fun _ => ⟨leaf, rfl⟩⟩
  | unsat ref =>
    exact ⟨by rintro ⟨_, h⟩; contradiction,
      fun hp => (ref.sound ((SROIQState.initial_sat_iff rank p).mpr hp)).elim⟩

theorem decideSROIQDAccessible_unsat_iff {rank : Rank} {p : Problem} {hsroiqd : p.isSROIQD rank = true}
    (a : Acc (SROIQFollows hsroiqd) (SROIQState.initial rank p)) :
    (∃ ref, decideSROIQDAccessible hsroiqd a = .unsat ref) ↔ ¬ p.Sat := by
  cases h : decideSROIQDAccessible hsroiqd a with
  | sat leaf =>
    exact ⟨by rintro ⟨_, h⟩; contradiction,
      fun h => (h (sroiqd_blocked_saturated_sat hsroiqd leaf.clashFree leaf.saturated)).elim⟩
  | unsat ref =>
    exact ⟨fun _ hp => ref.sound ((SROIQState.initial_sat_iff rank p).mpr hp), fun _ => ⟨ref, rfl⟩⟩

theorem decideSROIQDAccessible_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} {hsroiqd : p.isSROIQD rank = true}
    (a : Acc (SROIQFollows hsroiqd) (SROIQState.initial rank p))
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    ((∃ leaf, decideSROIQDAccessible hsroiqd a = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideSROIQDAccessible hsroiqd a = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) := by
  have spec := (Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)
  exact ⟨(decideSROIQDAccessible_sat_iff a).trans spec.symm,
    (decideSROIQDAccessible_unsat_iff a).trans (not_congr spec.symm)⟩

def decideSROIQAccessible {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true)
    {s : SROIQState rank p}
    (acc : Acc (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) s) : SROIQVerdict s :=
  decideSROIQDAccessible (p.isSROIQ_implies_isSROIQD hsroiq) acc

theorem decideSROIQAccessible_sat_iff {rank : Rank} {p : Problem} {hsroiq : p.isSROIQ rank = true}
    (a : Acc (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) (SROIQState.initial rank p)) :
    (∃ leaf, decideSROIQAccessible hsroiq a = .sat leaf) ↔ p.Sat :=
  decideSROIQDAccessible_sat_iff a

theorem decideSROIQAccessible_unsat_iff {rank : Rank} {p : Problem} {hsroiq : p.isSROIQ rank = true}
    (a : Acc (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) (SROIQState.initial rank p)) :
    (∃ ref, decideSROIQAccessible hsroiq a = .unsat ref) ↔ ¬ p.Sat :=
  decideSROIQDAccessible_unsat_iff a

theorem decideSROIQAccessible_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} {hsroiq : p.isSROIQ rank = true}
    (a : Acc (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) (SROIQState.initial rank p))
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    ((∃ leaf, decideSROIQAccessible hsroiq a = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideSROIQAccessible hsroiq a = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) :=
  decideSROIQDAccessible_ontology_iff a hnorm hroot

#print axioms sroiqStep_fair
#print axioms SROIQFollows.strictStep
#print axioms decideSROIQDAccessible_sat_iff
#print axioms decideSROIQDAccessible_unsat_iff
#print axioms decideSROIQDAccessible_ontology_iff

end BlockedForest
end Termination
end Sabrina.OWL2.SROIQD
