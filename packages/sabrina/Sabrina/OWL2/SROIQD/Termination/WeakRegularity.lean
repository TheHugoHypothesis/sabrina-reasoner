import Sabrina.OWL2.SROIQD.Termination.OWLHierarchy

namespace Sabrina.OWL2.RoleHierarchy.Stefanoni

open Sabrina.ALC (OrientedRole RoleTheory)
open Sabrina.RoleChains (Chain ChainShape DependencyPath Ranked)

private abbrev topRole : OrientedRole := (topObjectProperty, false)

def inverse (r : OrientedRole) : OrientedRole :=
  (r.1, if r.1 = topObjectProperty ∨ r.1 = bottomObjectProperty then r.2 else !r.2)

@[simp] theorem inverse_name (r : OrientedRole) : (inverse r).1 = r.1 := by
  rfl

/-- Section 12.1 excludes the transitivity form from its definition of
composite roles. This differs from the W3C simplicity predicate. -/
def Composite (box : List PropertyChain) (r : OrientedRole) : Prop :=
  ∃ a ∈ box, 2 ≤ a.body.length ∧ a.body ≠ [a.head, a.head] ∧
    (a.head = r ∨ a.head = inverse r)

/-- Definition 12.3 adds the two orientations of each nonrecursive source,
with the original orientation of the head as target. -/
def graphEdges (box : List PropertyChain) : RoleTheory :=
  box.flatMap fun a =>
    if a.head = topRole then [] else
      a.body.flatMap fun r =>
        if r = a.head ∨ inverse r = a.head then []
        else [(r, a.head), (inverse r, a.head)]

inductive NonemptyPath (edges : RoleTheory) : OrientedRole → OrientedRole → Prop where
  | edge {r s} : (r, s) ∈ edges → NonemptyPath edges r s
  | trans {r s t} : NonemptyPath edges r s → NonemptyPath edges s t →
      NonemptyPath edges r t

/-- The printed side condition compares a body letter with its own inverse.
The second reading compares with the inverse of the head, as the graph does. -/
inductive InverseExclusion where
  | printed
  | head

def allowedLower (reading : InverseExclusion) (head r : OrientedRole) : Prop :=
  r ≠ head ∧
    match reading with
    | .printed => r ≠ inverse r
    | .head => r ≠ inverse head

def NormalForm (reading : InverseExclusion) (a : PropertyChain) : Prop :=
  a.head = topRole ∨ a.body = [inverse a.head] ∨
    ∃ lower, ChainShape a.head a.body lower ∧ ∀ r ∈ lower, allowedLower reading a.head r

def WeaklyRegular (reading : InverseExclusion) (box : List PropertyChain) : Prop :=
  (∀ r, Composite box r → ¬ NonemptyPath (graphEdges box) r r) ∧
  ∀ a ∈ box, NormalForm reading a

def compiledBox (rules : RoleTheory) (chains : List Chain) : List PropertyChain :=
  (rules.map fun (r, s) => ⟨[r], s⟩) ++
    (chains.map fun c => ⟨c.body, (c.head, false)⟩)

/-- The graph comparison below covers the ordinary object-role signature.
Standalone top-headed OWL chains are handled by the separate lowering pass. -/
def Ordinary (box : List PropertyChain) : Prop :=
  ∀ a ∈ box, (a.head.1 ≠ topObjectProperty ∧ a.head.1 ≠ bottomObjectProperty) ∧
    ∀ r ∈ a.body, r.1 ≠ topObjectProperty ∧ r.1 ≠ bottomObjectProperty

private theorem lower_mem_body {head : OrientedRole} {body rest}
    (hs : ChainShape head body rest) {r} (hr : r ∈ rest) : r ∈ body := by
  cases hs with
  | transitive => simp at hr
  | plain => exact hr
  | left => exact List.mem_cons_of_mem _ hr
  | right => exact List.mem_append_left _ hr

private theorem distinct_names {head r : OrientedRole}
    (h : allowedLower .head head r)
    (hnt : head.1 ≠ topObjectProperty) (hnb : head.1 ≠ bottomObjectProperty) :
    r.1 ≠ head.1 := by
  obtain ⟨name, bit⟩ := head
  obtain ⟨name', bit'⟩ := r
  intro he
  change name' = name at he
  subst name'
  cases bit <;> cases bit'
  · exact h.1 rfl
  · exact h.2 (by simp [inverse, hnt, hnb])
  · exact h.2 (by simp [inverse, hnt, hnb])
  · exact h.1 rfl

private theorem compiledRule_mem {rules : RoleTheory} {chains : List Chain}
    {r s : OrientedRole} (h : (r, s) ∈ rules) :
    (⟨[r], s⟩ : PropertyChain) ∈ compiledBox rules chains :=
  List.mem_append_left _ (List.mem_map_of_mem h)

private theorem compiledChain_mem {rules : RoleTheory} {chains : List Chain}
    {c : Chain} (h : c ∈ chains) :
    (⟨c.body, (c.head, false)⟩ : PropertyChain) ∈ compiledBox rules chains :=
  List.mem_append_right _ (List.mem_map_of_mem h)

private theorem graph_edge {box : List PropertyChain} {a : PropertyChain}
    (ha : a ∈ box) (ho : Ordinary box) {r : OrientedRole} (hr : r ∈ a.body)
    (hne : r.1 ≠ a.head.1) {s : OrientedRole} (hs : s.1 = r.1) :
    NonemptyPath (graphEdges box) s a.head := by
  have hn : a.head ≠ topRole := fun h => (ho a ha).1.1 (congrArg Prod.fst h)
  have hrn : ¬ (r = a.head ∨ inverse r = a.head) := by
    rintro (h | h)
    · exact hne (congrArg Prod.fst h)
    · exact hne (by simpa using congrArg Prod.fst h)
  have hrOrd := (ho a ha).2 r hr
  have hs' : s = r ∨ s = inverse r := by
    obtain ⟨name, bit⟩ := r
    obtain ⟨name', bit'⟩ := s
    change name' = name at hs
    subst name'
    cases bit <;> cases bit' <;> simp [inverse, hrOrd.1, hrOrd.2]
  apply NonemptyPath.edge
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  rw [ite_eq_right hn]
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  rw [ite_eq_right hrn]
  rcases hs' with rfl | rfl <;> simp

private theorem ranked_compiler_chain {box : List PropertyChain}
    (hw : WeaklyRegular .head box) (ho : Ordinary box)
    {a : PropertyChain} (ha : a ∈ box) (hlen : 2 ≤ a.body.length) :
    ∃ lower, ChainShape a.head a.body lower ∧ ∀ r ∈ lower, r.1 ≠ a.head.1 := by
  rcases hw.2 a ha with ht | hi | ⟨lower, hs, hlow⟩
  · exact ((ho a ha).1.1 (congrArg Prod.fst ht)).elim
  · simp [hi] at hlen
  · exact ⟨lower, hs, fun r hr => distinct_names (hlow r hr) (ho a ha).1.1 (ho a ha).1.2⟩

private theorem lift_dependency_path {rules : RoleTheory} {chains : List Chain}
    {lower : Chain → List OrientedRole}
    (hshape : ∀ c ∈ chains, ChainShape (c.head, false) c.body (lower c) ∧
      ∀ r ∈ lower c, r.1 ≠ c.head)
    (ho : Ordinary (compiledBox rules chains))
    {i a b} (path : DependencyPath (Sabrina.RoleChains.weakDependencies rules)
      (Sabrina.RoleChains.strictDependencies chains lower) i a b) :
    ∀ s : OrientedRole, s.1 = a → a = b ∨
      ∃ t, t.1 = b ∧ NonemptyPath (graphEdges (compiledBox rules chains)) s t := by
  induction path with
  | refl => exact fun _ _ => .inl rfl
  | weak h =>
    obtain ⟨⟨r, t⟩, hrt, he⟩ := List.mem_map.mp h
    cases he
    intro s hs
    by_cases hne : r.1 = t.1
    · exact .inl hne
    · exact .inr ⟨t, rfl, graph_edge (compiledRule_mem hrt) ho (List.mem_cons_self ..) hne hs⟩
  | strict h =>
    obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    cases he
    intro s hs
    exact .inr ⟨(c.head, false), rfl,
      graph_edge (compiledChain_mem hc) ho (lower_mem_body (hshape c hc).1 hr)
        ((hshape c hc).2 r hr) hs⟩
  | trans _ _ ih₁ ih₂ =>
    intro s hs
    rcases ih₁ s hs with he | ⟨t, ht, hp⟩
    · exact he ▸ ih₂ s (hs.trans he)
    · rcases ih₂ t ht with he | ⟨u, hu, hq⟩
      · exact .inr ⟨t, ht.trans he, hp⟩
      · exact .inr ⟨u, hu, hp.trans hq⟩

private theorem strict_split {weak strict : List (String × String)}
    {i a b} (path : DependencyPath weak strict i a b) (hi : i = true) :
    ∃ x y j k, (x, y) ∈ strict ∧ DependencyPath weak strict j a x ∧
      DependencyPath weak strict k y b := by
  induction path with
  | refl => contradiction
  | weak => contradiction
  | strict h => exact ⟨_, _, false, false, h, .refl _, .refl _⟩
  | @trans i j _ _ _ p q ihp ihq =>
    cases i
    · have hj : j = true := hi
      obtain ⟨x, y, k, l, hx, hp, hq⟩ := ihq hj
      exact ⟨x, y, false || k, l, hx, p.trans hp, hq⟩
    · obtain ⟨x, y, k, l, hx, hp, hq⟩ := ihp rfl
      exact ⟨x, y, k, l || j, hx, hp, hq.trans q⟩

/-- On the normalized ordinary fragment, the head-inverse reading of
Definition 12.3 implies the verified compiler's exact mixed-cycle criterion. -/
theorem weaklyRegular_hasAcyclicDependencies {rules : RoleTheory} {chains : List Chain}
    (ho : Ordinary (compiledBox rules chains))
    (hlen : ∀ c ∈ chains, 2 ≤ c.body.length)
    (hw : WeaklyRegular .head (compiledBox rules chains)) :
    Sabrina.RoleChains.HasAcyclicDependencies rules chains := by
  classical
  have hex (c : Chain) : ∃ lower, c ∈ chains →
      ChainShape (c.head, false) c.body lower ∧ ∀ r ∈ lower, r.1 ≠ c.head := by
    by_cases hc : c ∈ chains
    · obtain ⟨lower, hs⟩ := ranked_compiler_chain hw ho (compiledChain_mem hc) (hlen c hc)
      exact ⟨lower, fun _ => hs⟩
    · exact ⟨[], fun h => (hc h).elim⟩
  let lower c := Classical.choose (hex c)
  have hshape c hc := Classical.choose_spec (hex c) hc
  refine ⟨lower, fun c hc => ⟨hlen c hc, (hshape c hc).1⟩, ?_⟩
  intro x cycle
  obtain ⟨a, b, _, _, hstrict, ha, hb⟩ := strict_split cycle rfl
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp hstrict
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
  cases he
  have hne := (hshape c hc).2 r hr
  have hrbody := lower_mem_body (hshape c hc).1 hr
  have hcomp : Composite (compiledBox rules chains) (c.head, false) := by
    refine ⟨⟨c.body, (c.head, false)⟩, compiledChain_mem hc, hlen c hc, ?_, .inl rfl⟩
    intro htrans
    change c.body = [(c.head, false), (c.head, false)] at htrans
    rw [htrans] at hrbody
    rcases List.mem_cons.mp hrbody with rfl | hm
    · exact hne rfl
    · exact hne (congrArg Prod.fst (List.mem_singleton.mp hm))
  apply hw.1 _ hcomp
  rcases lift_dependency_path hshape ho (hb.trans ha) (c.head, false) rfl with he | ⟨s, hs, hp⟩
  · exact (hne he.symm).elim
  · exact hp.trans (graph_edge (compiledChain_mem hc) ho hrbody hne hs)

theorem weaklyRegular_exists_ranked {rules : RoleTheory} {chains : List Chain}
    (ho : Ordinary (compiledBox rules chains))
    (hlen : ∀ c ∈ chains, 2 ≤ c.body.length)
    (hw : WeaklyRegular .head (compiledBox rules chains)) :
    ∃ rank, Ranked rank rules chains :=
  Sabrina.RoleChains.exists_ranked_iff_acyclicDependencies.mpr
    (weaklyRegular_hasAcyclicDependencies ho hlen hw)

theorem weaklyRegular_findRank_isSome {rules : RoleTheory} {chains : List Chain}
    (ho : Ordinary (compiledBox rules chains))
    (hlen : ∀ c ∈ chains, 2 ≤ c.body.length)
    (hw : WeaklyRegular .head (compiledBox rules chains)) :
    (Sabrina.RoleChains.findRank rules chains).isSome = true :=
  Sabrina.RoleChains.findRank_iff_acyclicDependencies.mpr
    (weaklyRegular_hasAcyclicDependencies ho hlen hw)

#print axioms weaklyRegular_hasAcyclicDependencies
#print axioms weaklyRegular_findRank_isSome

end Sabrina.OWL2.RoleHierarchy.Stefanoni
