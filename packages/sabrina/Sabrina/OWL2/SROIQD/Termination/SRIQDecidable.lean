import Sabrina.OWL2.SROIQD.Termination.SRIQTermination

/-!
Unconditional termination and fuel-free decidability for cyclic `SRIQ`.

Every search step strictly decreases a fixed-length, depth-indexed lexicographic
measure over levels `0 .. maxDepth rank p + 1`. At each depth `k`, the level
score `(levelCount, levelPotential)` tracks:
1. the number of live template nodes at depth `k`, and
2. the sum over depth-`k` nodes of missing local concepts, missing NFA guards,
   missing role labels (`down`/`up`/`loops`), and unallocated generating
   concepts (`some`/`min` lacking `ProtectedWitnesses`).

- Local enrichments preserve all node counts and depths and strictly lower
  `levelPotential` at the enriched node's depth.
- Sibling and ancestor merges preserve all nodes at strictly shallower depths
  with monotone local data and strictly reduce `levelCount` at the pruned
  node's depth.
- Witness generations occur only on unblocked nodes (depth `≤ maxDepth`),
  install `ProtectedWitnesses` for a previously unprotected generator at depth
  `k`, and add fresh children only at depth `k + 1 ≤ maxDepth + 1`.

Because the vector length `maxDepth rank p + 2` is fixed for a given problem,
this lexicographic order is well-founded, supplying `Acc (SearchFollows hs)` for
every admitted initial state and removing the accessibility hypothesis from
`decideAccessible`.
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank)

namespace BlockedBranch

/-! ### Finite missing-item counting -/

private noncomputable def missingCount {α : Type} (U : List α) (P : α → Prop) : Nat :=
  letI := Classical.propDecidable
  (U.filter (fun a => !decide (P a))).length

private theorem missingCount_le {α : Type} (U : List α) {P Q : α → Prop}
    (h : ∀ a ∈ U, P a → Q a) :
    missingCount U Q ≤ missingCount U P := by
  induction U with
  | nil => simp [missingCount]
  | cons a rest ih =>
    have hrest : missingCount rest Q ≤ missingCount rest P :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold missingCount at hrest ⊢
    letI := Classical.propDecidable
    simp only [List.filter_cons]
    by_cases hp : P a
    · have hq : Q a := h a (List.mem_cons_self ..) hp
      simp [hp, hq, hrest]
    · by_cases hq : Q a
      · simp only [hp, hq, decide_false, decide_true, Bool.not_false, Bool.not_true,
          ↓reduceIte, Bool.false_eq_true, List.length_cons]
        exact Nat.le_succ_of_le hrest
      · simp only [hp, hq, decide_false, Bool.not_false, ↓reduceIte, List.length_cons]
        exact Nat.succ_le_succ hrest

private theorem missingCount_lt {α : Type} (U : List α) {P Q : α → Prop}
    (h : ∀ a ∈ U, P a → Q a)
    {a₀ : α} (ha : a₀ ∈ U) (hp : ¬ P a₀) (hq : Q a₀) :
    missingCount U Q < missingCount U P := by
  induction U with
  | nil => cases ha
  | cons a rest ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · have hrest : missingCount rest Q ≤ missingCount rest P :=
        missingCount_le rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      unfold missingCount at hrest ⊢
      letI := Classical.propDecidable
      simp only [List.filter_cons, hp, hq, decide_false, decide_true, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true, List.length_cons]
      exact Nat.lt_succ_of_le hrest
    · have hrest : missingCount rest Q < missingCount rest P :=
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hmem
      unfold missingCount at hrest ⊢
      letI := Classical.propDecidable
      simp only [List.filter_cons]
      by_cases hpa : P a
      · have hqa : Q a := h a (List.mem_cons_self ..) hpa
        simp [hpa, hqa, hrest]
      · by_cases hqa : Q a
        · simp only [hpa, hqa, decide_false, decide_true, Bool.not_false, Bool.not_true,
            ↓reduceIte, Bool.false_eq_true, List.length_cons]
          exact Nat.lt_succ_of_lt hrest
        · simp only [hpa, hqa, decide_false, Bool.not_false, ↓reduceIte, List.length_cons]
          exact Nat.succ_lt_succ hrest

private theorem missingCount_sub {α : Type} (U : List α) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    missingCount U (fun a => a ∈ l₂) ≤ missingCount U (fun a => a ∈ l₁) :=
  missingCount_le U (P := (· ∈ l₁)) (Q := (· ∈ l₂)) (fun _ _ ha => h ha)

private theorem missingCount_sub_lt {α : Type} (U : List α) {l₁ l₂ : List α} (h : l₁ ⊆ l₂)
    {a₀ : α} (ha : a₀ ∈ U) (hnot : a₀ ∉ l₁) (hhas : a₀ ∈ l₂) :
    missingCount U (fun a => a ∈ l₂) < missingCount U (fun a => a ∈ l₁) :=
  missingCount_lt U (P := (· ∈ l₁)) (Q := (· ∈ l₂)) (fun _ _ hx => h hx) ha hnot hhas

/-! ### List injection and sum comparison lemmas -/

private theorem sum_map_le_of_inj {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd : l₁.Nodup) (f : α → β) (g₁ : α → Nat) (g₂ : β → Nat)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    (hle : ∀ a ∈ l₁, g₁ a ≤ g₂ (f a)) :
    (l₁.map g₁).sum ≤ (l₂.map g₂).sum := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a rest ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem (hmem a (List.mem_cons_self ..))
    have hrestMem : ∀ x ∈ rest, f x ∈ pre ++ post := by
      intro x hx
      have hfx : f x ∈ pre ++ f a :: post := hmem x (List.mem_cons_of_mem _ hx)
      rcases List.mem_append.mp hfx with hp | hp
      · exact List.mem_append_left _ hp
      · rcases List.mem_cons.mp hp with heq | hpost
        · exfalso
          exact hna (hinj x (List.mem_cons_of_mem _ hx) a (List.mem_cons_self ..) heq ▸ hx)
        · exact List.mem_append_right _ hpost
    have hrestSum := ih (pre ++ post) hnd'
      (fun x hx y hy hxy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
      hrestMem (fun x hx => hle x (List.mem_cons_of_mem _ hx))
    have hhead : g₁ a ≤ g₂ (f a) := hle a (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hrestSum ⊢
    omega

private theorem sum_map_lt_of_inj {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd : l₁.Nodup) (f : α → β) (g₁ : α → Nat) (g₂ : β → Nat)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    (hle : ∀ a ∈ l₁, g₁ a ≤ g₂ (f a))
    {a₀ : α} (ha₀ : a₀ ∈ l₁) (hlt : g₁ a₀ < g₂ (f a₀)) :
    (l₁.map g₁).sum < (l₂.map g₂).sum := by
  induction l₁ generalizing l₂ with
  | nil => cases ha₀
  | cons a rest ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem (hmem a (List.mem_cons_self ..))
    have hrestMem : ∀ x ∈ rest, f x ∈ pre ++ post := by
      intro x hx
      have hfx : f x ∈ pre ++ f a :: post := hmem x (List.mem_cons_of_mem _ hx)
      rcases List.mem_append.mp hfx with hp | hp
      · exact List.mem_append_left _ hp
      · rcases List.mem_cons.mp hp with heq | hpost
        · exfalso
          exact hna (hinj x (List.mem_cons_of_mem _ hx) a (List.mem_cons_self ..) heq ▸ hx)
        · exact List.mem_append_right _ hpost
    rcases List.mem_cons.mp ha₀ with rfl | hmem₀
    · have hrestSum := sum_map_le_of_inj rest (pre ++ post) hnd' f g₁ g₂
        (fun x hx y hy hxy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
        hrestMem (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hrestSum ⊢
      omega
    · have hrestSum := ih (pre ++ post) hnd'
        (fun x hx y hy hxy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
        hrestMem (fun x hx => hle x (List.mem_cons_of_mem _ hx)) hmem₀
      have hhead : g₁ a ≤ g₂ (f a) := hle a (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hrestSum ⊢
      omega

private theorem length_le_of_inj {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd : l₁.Nodup) (f : α → β)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂) :
    l₁.length ≤ l₂.length := by
  have hm : (l₁.map f).Nodup :=
    List.pairwise_map.mpr (hnd.imp_of_mem fun ha ha' hne heq => hne (hinj _ ha _ ha' heq))
  have hle := hm.length_le_of_subset fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact hmem a ha
  simpa only [List.length_map] using hle

private theorem length_eq_of_bij {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) (f : α → β)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    (hsurj : ∀ b ∈ l₂, ∃ a ∈ l₁, f a = b) :
    l₁.length = l₂.length := by
  have hle₁ : l₁.length ≤ l₂.length := length_le_of_inj l₁ l₂ hnd₁ f hinj hmem
  have hle₂ : l₂.length ≤ l₁.length := by
    have hsub : l₂ ⊆ l₁.map f := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := hsurj b hb
      exact List.mem_map_of_mem ha
    have h := hnd₂.length_le_of_subset hsub
    simpa only [List.length_map] using h
  omega

private theorem length_lt_of_inj_missing {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd : l₁.Nodup) (f : α → β)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    {b₀ : β} (hb₀ : b₀ ∈ l₂) (hmiss : ∀ a ∈ l₁, f a ≠ b₀) :
    l₁.length < l₂.length := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb₀
  have hmem' : ∀ a ∈ l₁, f a ∈ pre ++ post := by
    intro a ha
    rcases List.mem_append.mp (hmem a ha) with hp | hp
    · exact List.mem_append_left _ hp
    · rcases List.mem_cons.mp hp with heq | hpost
      · exact (hmiss a ha heq).elim
      · exact List.mem_append_right _ hpost
  have hle := length_le_of_inj l₁ (pre ++ post) hnd f hinj hmem'
  simp only [List.length_append, List.length_cons] at hle ⊢
  omega

/-! ### Fixed-length lexicographic well-foundedness -/

private def PairLex (a b : Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (· < ·) a b

private theorem wellFounded_pairLex : WellFounded PairLex :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

private def VecLex {N : Nat} {α : Type} (R : α → α → Prop) (v w : Fin N → α) : Prop :=
  ∃ k : Fin N, (∀ j : Fin N, j.val < k.val → v j = w j) ∧ R (v k) (w k)

private theorem wellFounded_vecLex {N : Nat} {α : Type} {R : α → α → Prop}
    (hR : WellFounded R) : WellFounded (VecLex (N := N) R) := by
  induction N with
  | zero =>
    refine ⟨fun v => ⟨v, fun w h => ?_⟩⟩
    obtain ⟨k, _, _⟩ := h
    exact Fin.elim0 k
  | succ m ih =>
    let split : (Fin (m + 1) → α) → α × (Fin m → α) := fun v => (v 0, fun i => v i.succ)
    have hprodWf : WellFounded (Prod.Lex R (VecLex (N := m) R)) :=
      (Prod.lex ⟨R, hR⟩ ⟨VecLex R, ih⟩).wf
    have himgWf : WellFounded (InvImage (Prod.Lex R (VecLex (N := m) R)) split) :=
      InvImage.wf split hprodWf
    refine Subrelation.wf (r := InvImage (Prod.Lex R (VecLex (N := m) R)) split) ?_ himgWf
    intro v w h
    obtain ⟨k, heq, hlt⟩ := h
    cases k using Fin.cases with
    | zero =>
      exact Prod.Lex.left _ _ hlt
    | succ i =>
      have h0 : v 0 = w 0 := heq 0 (Nat.zero_lt_succ i.val)
      have htail : VecLex R (fun j : Fin m => v j.succ) (fun j : Fin m => w j.succ) :=
        ⟨i, fun j hj => heq j.succ (Nat.succ_lt_succ hj), hlt⟩
      change Prod.Lex R (VecLex R) (v 0, fun j => v j.succ) (w 0, fun j => w j.succ)
      rw [h0]
      exact Prod.Lex.right _ htail

private theorem vecLex_of_prefix_le_lt {N : Nat} {α : Type} {R : α → α → Prop}
    {v w : Fin N → α} (k : Fin N)
    (hle : ∀ j : Fin N, j.val < k.val → v j = w j ∨ R (v j) (w j))
    (hlt : R (v k) (w k)) :
    VecLex R v w := by
  have aux : ∀ (m : Nat) (hm : m < N),
      (∀ j : Fin N, j.val < m → v j = w j ∨ R (v j) (w j)) →
      R (v ⟨m, hm⟩) (w ⟨m, hm⟩) →
      VecLex R v w := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm hpre hnow
      by_cases hex : ∃ j : Fin N, j.val < m ∧ R (v j) (w j)
      · obtain ⟨j, hjlt, hRj⟩ := hex
        exact ih j.val hjlt j.isLt (fun i hi => hpre i (Nat.lt_trans hi hjlt)) hRj
      · refine ⟨⟨m, hm⟩, fun j hj => ?_, hnow⟩
        rcases hpre j hj with heq | hlt'
        · exact heq
        · exact (hex ⟨j, hj, hlt'⟩).elim
  exact aux k.val k.isLt hle hlt

/-! ### Depth-indexed measure on `ConstrainedTree` -/

private noncomputable def nodePotential (rank : Rank) (p : Problem) (s : ConstrainedTree)
    (x : s.tree.Node) : Nat :=
  missingCount (clos p) (fun c => c ∈ s.tree.labels x) +
  missingCount (guards rank p) (fun g => g ∈ s.tree.guardLabels x) +
  missingCount (roleNames p) (fun r => r ∈ s.tree.down x) +
  missingCount (roleNames p) (fun r => r ∈ s.tree.up x) +
  missingCount (roleNames p) (fun r => r ∈ s.tree.loops x) +
  missingCount (clos p) (fun c => GenProtected s x c)

private def nodesAtDepth (b : BlockedBranch) (k : Nat) : List b.Node :=
  (List.finRange (b.size + 1)).filter (fun x => b.depth x == k)

private theorem mem_nodesAtDepth {b : BlockedBranch} {k : Nat} {x : b.Node} :
    x ∈ nodesAtDepth b k ↔ b.depth x = k := by
  simp [nodesAtDepth]

private theorem nodup_nodesAtDepth (b : BlockedBranch) (k : Nat) :
    (nodesAtDepth b k).Nodup :=
  (List.nodup_finRange _).filter _

private def levelCount (b : BlockedBranch) (k : Nat) : Nat :=
  (nodesAtDepth b k).length

private noncomputable def levelPotential (rank : Rank) (p : Problem) (s : ConstrainedTree)
    (k : Nat) : Nat :=
  ((nodesAtDepth s.tree k).map (nodePotential rank p s)).sum

private noncomputable def levelScore (rank : Rank) (p : Problem) (s : ConstrainedTree)
    (k : Nat) : Nat × Nat :=
  (levelCount s.tree k, levelPotential rank p s k)

private noncomputable def measureVec (rank : Rank) (p : Problem) (s : ConstrainedTree) :
    Fin (maxDepth rank p + 2) → Nat × Nat :=
  fun k => levelScore rank p s k.val

private theorem pairLex_or_eq_of_eq_le {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ = a₂) (hb : b₁ ≤ b₂) :
    (a₁, b₁) = (a₂, b₂) ∨ PairLex (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_eq_of_le hb with hlt | heq
  · exact .inr (ha ▸ Prod.Lex.right a₁ hlt)
  · exact .inl (Prod.ext ha heq)

private theorem nodePotential_le {rank : Rank} {p : Problem} {s t : ConstrainedTree}
    {x : s.tree.Node} {y : t.tree.Node}
    (hlabels : s.tree.labels x ⊆ t.tree.labels y)
    (hguards : s.tree.guardLabels x ⊆ t.tree.guardLabels y)
    (hdown : s.tree.down x ⊆ t.tree.down y)
    (hup : s.tree.up x ⊆ t.tree.up y)
    (hloops : s.tree.loops x ⊆ t.tree.loops y)
    (hprot : ∀ r c n, s.ProtectedWitnesses x r c n → t.ProtectedWitnesses y r c n) :
    nodePotential rank p t y ≤ nodePotential rank p s x := by
  have h1 := missingCount_sub (clos p) hlabels
  have h2 := missingCount_sub (guards rank p) hguards
  have h3 := missingCount_sub (roleNames p) hdown
  have h4 := missingCount_sub (roleNames p) hup
  have h5 := missingCount_sub (roleNames p) hloops
  have h6 : missingCount (clos p) (fun c => GenProtected t y c) ≤
      missingCount (clos p) (fun c => GenProtected s x c) := by
    apply missingCount_le
    intro c _ hc
    cases c with
    | some r d => exact hprot r d 1 hc
    | min n r d => exact hprot r d n hc
    | _ => trivial
  unfold nodePotential
  omega

/-- Every node in a reachable state lies within the pairwise-blocking depth
horizon `maxDepth rank p + 1`. -/
def DepthBounded (rank : Rank) (p : Problem) (s : SearchState rank p) : Prop :=
  ∀ x : s.branch.tree.Node, s.branch.tree.depth x ≤ maxDepth rank p + 1

private theorem DepthBounded.initial (rank : Rank) (p : Problem) :
    DepthBounded rank p (SearchState.initial rank p) := by
  intro x
  have hx : x = 0 := Fin.ext (by
    have hlt := x.isLt
    change x.val < 0 + 1 at hlt
    change x.val = 0
    omega)
  subst x
  unfold depth
  rw [ancestors]
  simp

private theorem DepthBounded.step {rank : Rank} {p : Problem} {s t : SearchState rank p}
    (hb : DepthBounded rank p s) (hstep : StrictStep rank p s.branch t.branch) :
    DepthBounded rank p t := by
  cases hstep with
  | enrich f _ hsurj hdepth _ _ _ _ _ _ _ =>
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hdepth x]
    exact hb x
  | merge drop _ f _ _ _ hdepth _ _ _ _ _ _ =>
    intro y
    rw [hdepth y]
    exact hb (f y)
  | generate x hxDepth _ _ f _ hdepthOld hdepthNew _ _ _ _ _ _ _ _ =>
    intro y
    by_cases hold : ∃ z, f z = y
    · obtain ⟨z, rfl⟩ := hold
      rw [hdepthOld z]
      exact hb z
    · rw [hdepthNew y (fun z hz => hold ⟨z, hz⟩)]
      omega

private theorem StrictStep.measure_lt {rank : Rank} {p : Problem} {s t : SearchState rank p}
    (hb : DepthBounded rank p s) (hstep : StrictStep rank p s.branch t.branch) :
    VecLex PairLex (measureVec rank p t.branch) (measureVec rank p s.branch) := by
  cases hstep with
  | enrich f hinj hsurj hdepth hlabels hguards hdown hup hloops hprot hnew =>
    obtain ⟨z₀, hz₀⟩ := hnew
    have hpotLe (z : s.branch.tree.Node) :
        nodePotential rank p t.branch (f z) ≤ nodePotential rank p s.branch z :=
      nodePotential_le (hlabels z) (hguards z) (hdown z) (hup z) (hloops z) (hprot z)
    have hpotLt : nodePotential rank p t.branch (f z₀) < nodePotential rank p s.branch z₀ := by
      have h1 := missingCount_sub (clos p) (hlabels z₀)
      have h2 := missingCount_sub (guards rank p) (hguards z₀)
      have h3 := missingCount_sub (roleNames p) (hdown z₀)
      have h4 := missingCount_sub (roleNames p) (hup z₀)
      have h5 := missingCount_sub (roleNames p) (hloops z₀)
      have h6 : missingCount (clos p) (fun c => GenProtected t.branch (f z₀) c) ≤
          missingCount (clos p) (fun c => GenProtected s.branch z₀ c) := by
        apply missingCount_le; intro c _ hc
        cases c <;> first | exact hprot z₀ _ _ _ hc | trivial
      unfold nodePotential
      rcases hz₀ with ⟨c, hc, hnot, hhas⟩ | ⟨g, hg, hnot, hhas⟩ | ⟨r, hr, hrole⟩
      · have hlt := missingCount_sub_lt (clos p) (hlabels z₀) hc hnot hhas
        omega
      · have hlt := missingCount_sub_lt (guards rank p) (hguards z₀) hg hnot hhas
        omega
      · rcases hrole with ⟨hnot, hhas⟩ | ⟨hnot, hhas⟩ | ⟨hnot, hhas⟩
        · have hlt := missingCount_sub_lt (roleNames p) (hdown z₀) hr hnot hhas
          omega
        · have hlt := missingCount_sub_lt (roleNames p) (hup z₀) hr hnot hhas
          omega
        · have hlt := missingCount_sub_lt (roleNames p) (hloops z₀) hr hnot hhas
          omega
    -- Build inverse `g : t.branch.tree.Node → s.branch.tree.Node` classically using `hsurj`.
    classical
    let g : t.branch.tree.Node → s.branch.tree.Node := fun y => Classical.choose (hsurj y)
    have hfg (y : t.branch.tree.Node) : f (g y) = y := Classical.choose_spec (hsurj y)
    have hgf (x : s.branch.tree.Node) : g (f x) = x := hinj _ _ (hfg (f x))
    have hlevelEq (j : Nat) : levelCount t.branch.tree j = levelCount s.branch.tree j := by
      apply length_eq_of_bij (nodesAtDepth t.branch.tree j) (nodesAtDepth s.branch.tree j)
        (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) g
      · intro a _ c _ hac
        rw [← hfg a, ← hfg c, hac]
      · intro y hy
        have hdy : t.branch.tree.depth y = j := mem_nodesAtDepth.mp hy
        rw [mem_nodesAtDepth, ← hdepth (g y), hfg y]
        exact hdy
      · intro x hx
        refine ⟨f x, mem_nodesAtDepth.mpr ((hdepth x).trans (mem_nodesAtDepth.mp hx)), hgf x⟩
    have hlevelLe (j : Nat) :
        levelPotential rank p t.branch j ≤ levelPotential rank p s.branch j := by
      apply sum_map_le_of_inj (nodesAtDepth t.branch.tree j) (nodesAtDepth s.branch.tree j)
        (nodup_nodesAtDepth _ _) g
      · intro a _ c _ hac
        rw [← hfg a, ← hfg c, hac]
      · intro y hy
        rw [mem_nodesAtDepth, ← hdepth (g y), hfg y]
        exact mem_nodesAtDepth.mp hy
      · intro y _
        simpa only [hfg y] using hpotLe (g y)
    have hkLt : s.branch.tree.depth z₀ < maxDepth rank p + 2 := Nat.lt_succ_of_le (hb z₀)
    apply vecLex_of_prefix_le_lt ⟨s.branch.tree.depth z₀, hkLt⟩
    · intro j _
      exact pairLex_or_eq_of_eq_le (hlevelEq j.val) (hlevelLe j.val)
    · have hltSum : levelPotential rank p t.branch (s.branch.tree.depth z₀) <
          levelPotential rank p s.branch (s.branch.tree.depth z₀) := by
        apply sum_map_lt_of_inj (nodesAtDepth t.branch.tree (s.branch.tree.depth z₀))
          (nodesAtDepth s.branch.tree (s.branch.tree.depth z₀))
          (nodup_nodesAtDepth _ _) g _ _
          (fun a _ c _ hac => by rw [← hfg a, ← hfg c, hac])
          (fun y hy => by rw [mem_nodesAtDepth, ← hdepth (g y), hfg y]; exact mem_nodesAtDepth.mp hy)
          (fun y _ => by simpa only [hfg y] using hpotLe (g y))
          (a₀ := f z₀) (mem_nodesAtDepth.mpr (hdepth z₀))
        simpa only [hgf z₀] using hpotLt
      change PairLex (levelCount t.branch.tree (s.branch.tree.depth z₀),
        levelPotential rank p t.branch (s.branch.tree.depth z₀))
        (levelCount s.branch.tree (s.branch.tree.depth z₀),
          levelPotential rank p s.branch (s.branch.tree.depth z₀))
      rw [hlevelEq (s.branch.tree.depth z₀)]
      exact Prod.Lex.right _ hltSum

  | merge drop hd f hinj hmem hsurj hdepth hlabels hguards hdown hup hloops hprot =>
    have hpotLe (y : t.branch.tree.Node) :
        nodePotential rank p t.branch y ≤ nodePotential rank p s.branch (f y) :=
      nodePotential_le (hlabels y) (hguards y) (hdown y) (hup y) (hloops y) (hprot y)
    have hkLt : s.branch.tree.depth drop < maxDepth rank p + 2 := Nat.lt_succ_of_le (hb drop)
    apply vecLex_of_prefix_le_lt ⟨s.branch.tree.depth drop, hkLt⟩
    · intro j hj
      change j.val < s.branch.tree.depth drop at hj
      have hEq : levelCount t.branch.tree j.val = levelCount s.branch.tree j.val := by
        apply length_eq_of_bij (nodesAtDepth t.branch.tree j.val) (nodesAtDepth s.branch.tree j.val)
          (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) f
        · intro a _ c _ hac
          exact hinj a c hac
        · intro y hy
          rw [mem_nodesAtDepth, ← hdepth y]
          exact mem_nodesAtDepth.mp hy
        · intro x hx
          have hdx : s.branch.tree.depth x = j.val := mem_nodesAtDepth.mp hx
          have hret : x ∈ s.branch.tree.retained drop := by
            refine mem_retained.mpr ⟨?_, ?_⟩
            · intro heq
              rw [heq] at hdx
              exact Nat.ne_of_lt hj hdx.symm
            · intro hanc
              have hlt := hanc.depth_lt
              omega
          obtain ⟨y, rfl⟩ := hsurj x hret
          exact ⟨y, mem_nodesAtDepth.mpr ((hdepth y).trans hdx), rfl⟩
      have hLe : levelPotential rank p t.branch j.val ≤ levelPotential rank p s.branch j.val := by
        apply sum_map_le_of_inj (nodesAtDepth t.branch.tree j.val) (nodesAtDepth s.branch.tree j.val)
          (nodup_nodesAtDepth _ _) f
        · intro a _ c _ hac
          exact hinj a c hac
        · intro y hy
          rw [mem_nodesAtDepth, ← hdepth y]
          exact mem_nodesAtDepth.mp hy
        · intro y _
          exact hpotLe y
      exact pairLex_or_eq_of_eq_le hEq hLe
    · have hcntLt : levelCount t.branch.tree (s.branch.tree.depth drop) <
          levelCount s.branch.tree (s.branch.tree.depth drop) := by
        apply length_lt_of_inj_missing
          (nodesAtDepth t.branch.tree (s.branch.tree.depth drop))
          (nodesAtDepth s.branch.tree (s.branch.tree.depth drop))
          (nodup_nodesAtDepth _ _) f
          (fun a _ c _ hac => hinj a c hac)
          (fun y hy => by rw [mem_nodesAtDepth, ← hdepth y]; exact mem_nodesAtDepth.mp hy)
          (b₀ := drop) (mem_nodesAtDepth.mpr rfl)
        intro y _ hfy
        exact (mem_retained.mp (hmem y)).1 hfy
      exact Prod.Lex.left _ _ hcntLt

  | generate x hxDepth gen hgenClos f hinj hdepthOld hdepthNew hlabels hguards hdown hup hloops
      hprot hnotBefore hprotAfter =>
    have hpotLe (z : s.branch.tree.Node) :
        nodePotential rank p t.branch (f z) ≤ nodePotential rank p s.branch z :=
      nodePotential_le (hlabels z) (hguards z) (hdown z) (hup z) (hloops z) (hprot z)
    have hpotLt : nodePotential rank p t.branch (f x) < nodePotential rank p s.branch x := by
      have h1 := missingCount_sub (clos p) (hlabels x)
      have h2 := missingCount_sub (guards rank p) (hguards x)
      have h3 := missingCount_sub (roleNames p) (hdown x)
      have h4 := missingCount_sub (roleNames p) (hup x)
      have h5 := missingCount_sub (roleNames p) (hloops x)
      have h6 : missingCount (clos p) (fun c => GenProtected t.branch (f x) c) <
          missingCount (clos p) (fun c => GenProtected s.branch x c) := by
        apply missingCount_lt (clos p) _ hgenClos hnotBefore hprotAfter
        intro c _ hc
        cases c <;> first | exact hprot x _ _ _ hc | trivial
      unfold nodePotential
      omega
    -- Every node in `t` at depth `j ≤ depth x` must come from an old node `f z`.
    have holdAt (j : Nat) (hj : j ≤ s.branch.tree.depth x) (y : t.branch.tree.Node)
        (hy : t.branch.tree.depth y = j) : ∃ z, f z = y := by
      by_cases hex : ∃ z, f z = y
      · exact hex
      · exfalso
        have hdn := hdepthNew y (fun z hz => hex ⟨z, hz⟩)
        omega
    classical
    let inv (y : t.branch.tree.Node) : s.branch.tree.Node :=
      if h : ∃ z, f z = y then Classical.choose h else 0
    have hfinv {y : t.branch.tree.Node} (h : ∃ z, f z = y) : f (inv y) = y := by
      simp only [inv, h, ↓reduceDIte]
      exact Classical.choose_spec h
    have hinvf (z : s.branch.tree.Node) : inv (f z) = z :=
      hinj _ _ (hfinv ⟨z, rfl⟩)
    have hlevelEq (j : Nat) (hj : j ≤ s.branch.tree.depth x) :
        levelCount t.branch.tree j = levelCount s.branch.tree j := by
      apply length_eq_of_bij (nodesAtDepth t.branch.tree j) (nodesAtDepth s.branch.tree j)
        (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) inv
      · intro a ha c hc hac
        have ha' := holdAt j hj a (mem_nodesAtDepth.mp ha)
        have hc' := holdAt j hj c (mem_nodesAtDepth.mp hc)
        rw [← hfinv ha', ← hfinv hc', hac]
      · intro y hy
        have hdy := mem_nodesAtDepth.mp hy
        have hy' := holdAt j hj y hdy
        rw [mem_nodesAtDepth, ← hdepthOld (inv y), hfinv hy']
        exact hdy
      · intro z hz
        exact ⟨f z, mem_nodesAtDepth.mpr ((hdepthOld z).trans (mem_nodesAtDepth.mp hz)), hinvf z⟩
    have hlevelLe (j : Nat) (hj : j ≤ s.branch.tree.depth x) :
        levelPotential rank p t.branch j ≤ levelPotential rank p s.branch j := by
      apply sum_map_le_of_inj (nodesAtDepth t.branch.tree j) (nodesAtDepth s.branch.tree j)
        (nodup_nodesAtDepth _ _) inv
      · intro a ha c hc hac
        have ha' := holdAt j hj a (mem_nodesAtDepth.mp ha)
        have hc' := holdAt j hj c (mem_nodesAtDepth.mp hc)
        rw [← hfinv ha', ← hfinv hc', hac]
      · intro y hy
        have hdy := mem_nodesAtDepth.mp hy
        have hy' := holdAt j hj y hdy
        rw [mem_nodesAtDepth, ← hdepthOld (inv y), hfinv hy']
        exact hdy
      · intro y hy
        have hy' := holdAt j hj y (mem_nodesAtDepth.mp hy)
        simpa only [hfinv hy'] using hpotLe (inv y)
    have hkLt : s.branch.tree.depth x < maxDepth rank p + 2 := by omega
    apply vecLex_of_prefix_le_lt ⟨s.branch.tree.depth x, hkLt⟩
    · intro j hj
      exact pairLex_or_eq_of_eq_le (hlevelEq j.val (Nat.le_of_lt hj))
        (hlevelLe j.val (Nat.le_of_lt hj))
    · have hltSum : levelPotential rank p t.branch (s.branch.tree.depth x) <
          levelPotential rank p s.branch (s.branch.tree.depth x) := by
        apply sum_map_lt_of_inj (nodesAtDepth t.branch.tree (s.branch.tree.depth x))
          (nodesAtDepth s.branch.tree (s.branch.tree.depth x))
          (nodup_nodesAtDepth _ _) inv _ _
          (fun a ha c hc hac => by
            have ha' := holdAt _ (Nat.le_refl _) a (mem_nodesAtDepth.mp ha)
            have hc' := holdAt _ (Nat.le_refl _) c (mem_nodesAtDepth.mp hc)
            rw [← hfinv ha', ← hfinv hc', hac])
          (fun y hy => by
            have hdy := mem_nodesAtDepth.mp hy
            have hy' := holdAt _ (Nat.le_refl _) y hdy
            rw [mem_nodesAtDepth, ← hdepthOld (inv y), hfinv hy']
            exact hdy)
          (fun y hy => by
            have hy' := holdAt _ (Nat.le_refl _) y (mem_nodesAtDepth.mp hy)
            simpa only [hfinv hy'] using hpotLe (inv y))
          (a₀ := f x) (mem_nodesAtDepth.mpr (hdepthOld x))
        simpa only [hinvf x] using hpotLt
      change PairLex (levelCount t.branch.tree (s.branch.tree.depth x),
        levelPotential rank p t.branch (s.branch.tree.depth x))
        (levelCount s.branch.tree (s.branch.tree.depth x),
          levelPotential rank p s.branch (s.branch.tree.depth x))
      rw [hlevelEq (s.branch.tree.depth x) (Nat.le_refl _)]
      exact Prod.Lex.right _ hltSum

/-! ### Unconditional accessibility and fuel-free decision procedure -/

private theorem accessible_of_depthBounded {rank : Rank} {p : Problem}
    (hs : p.isSRIQ rank = true) :
    ∀ s : SearchState rank p, DepthBounded rank p s → Acc (SearchFollows hs) s := by
  let wfVec : WellFounded (VecLex (N := maxDepth rank p + 2) PairLex) :=
    wellFounded_vecLex wellFounded_pairLex
  let wfState : WellFounded (InvImage (VecLex (N := maxDepth rank p + 2) PairLex)
      (fun s : SearchState rank p => measureVec rank p s.branch)) :=
    InvImage.wf _ wfVec
  intro s
  induction s using wfState.induction with
  | h s ih =>
    intro hb
    refine Acc.intro s ?_
    intro next hfollow
    have hstrict := hfollow.strictStep
    exact ih next (hstrict.measure_lt hb) (hb.step hstrict)

/-- Every admitted `SRIQ` initial search state is unconditionally accessible
under `SearchFollows`. -/
theorem initial_accessible {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    Acc (SearchFollows hs) (SearchState.initial rank p) :=
  accessible_of_depthBounded hs (SearchState.initial rank p) (DepthBounded.initial rank p)

/-- Unconditional, fuel-free decision procedure for cyclic `SRIQ`. -/
def decideSRIQ {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    SearchVerdict (SearchState.initial rank p) :=
  decideAccessible hs (initial_accessible hs)

theorem decideSRIQ_sat_iff {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    (∃ leaf, decideSRIQ hs = .sat leaf) ↔ p.Sat :=
  decideAccessible_sat_iff (initial_accessible hs)

theorem decideSRIQ_unsat_iff {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    (∃ ref, decideSRIQ hs = .unsat ref) ↔ ¬ p.Sat :=
  decideAccessible_unsat_iff (initial_accessible hs)

theorem decideSRIQ_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hs : p.isSRIQ rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    ((∃ leaf, decideSRIQ hs = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideSRIQ hs = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) :=
  decideAccessible_ontology_iff (initial_accessible hs) hnorm hroot

/-- Boolean wrapper for the unconditional, fuel-free `SRIQ` decision procedure. -/
def decideSRIQBool {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) : Bool :=
  match decideSRIQ hs with
  | .sat _ => true
  | .unsat _ => false

theorem decideSRIQBool_true_iff {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    decideSRIQBool hs = true ↔ p.Sat := by
  rw [← decideSRIQ_sat_iff hs]
  unfold decideSRIQBool
  cases decideSRIQ hs with
  | sat leaf => exact ⟨fun _ => ⟨leaf, rfl⟩, fun _ => rfl⟩
  | unsat _ => exact ⟨by intro h; contradiction, by rintro ⟨_, h⟩; contradiction⟩

theorem decideSRIQBool_false_iff {rank : Rank} {p : Problem} (hs : p.isSRIQ rank = true) :
    decideSRIQBool hs = false ↔ ¬ p.Sat := by
  rw [← decideSRIQ_unsat_iff hs]
  unfold decideSRIQBool
  cases decideSRIQ hs with
  | sat _ => exact ⟨by intro h; contradiction, by rintro ⟨_, h⟩; contradiction⟩
  | unsat ref => exact ⟨fun _ => ⟨ref, rfl⟩, fun _ => rfl⟩

theorem decideSRIQBool_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hs : p.isSRIQ rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    decideSRIQBool hs = true ↔ Satisfiable datatypeMap o := by
  have h := (decideSRIQ_ontology_iff hs hnorm hroot).1
  exact (decideSRIQBool_true_iff hs).trans ((decideSRIQ_sat_iff hs).symm.trans h)

/-! ### Live unconditional regressions (zero traces, zero fuel) -/

theorem infiniteChain_decideSRIQ_sat :
    ∃ leaf, decideSRIQ infiniteChainFragment = .sat leaf :=
  (decideSRIQ_sat_iff infiniteChainFragment).mpr infiniteChain_via_search_trace

theorem collision_decideSRIQ_unsat :
    ∃ ref, decideSRIQ collisionFragment = .unsat ref :=
  (decideSRIQ_unsat_iff collisionFragment).mpr collision_via_search_trace

private def collisionSourceProblem' : Problem := { tbox := [⟨.top, collisionRoot⟩] }

private theorem collisionSourceFragment' : collisionSourceProblem'.isSRIQ (fun _ => 0) = true := by
  decide

theorem collisionSource_decideSRIQ_unsat :
    ∃ ref, decideSRIQ collisionSourceFragment' = .unsat ref := by
  have hnorm : Normalize.normalizeWithDefs collisionSource = some ([], collisionSourceProblem') := rfl
  exact (decideSRIQ_ontology_iff collisionSourceFragment' hnorm rfl).2.mpr collision_source_via_search_trace

/-- Transitive role chain with universal restriction across two hops:
`R ∘ R ⊑ R`, root has `∀ R. A ⊓ ∃ R. ∃ R. ¬ A` (unsatisfiable). -/
private def transRoleName : IRI := "urn:sabrina:termination:transR"
private def transRole : ALC.OrientedRole := (transRoleName, false)
private def transAtom : IRI := "urn:sabrina:termination:A"

private def transChainProblem : Problem where
  root := .conj (.all transRole (.lit transAtom true))
    (.some transRole (.some transRole (.lit transAtom false)))
  chains := [Sabrina.RoleChains.Chain.named [transRoleName, transRoleName] transRoleName]

private theorem transChainFragment : transChainProblem.isSRIQ (fun _ => 0) = true := by decide

/-- Grandparent-merge satisfiability regression:
`⊤ ⊑ ≤ 2 R. ⊤`, root has `∃ R⁻. (≥ 2 R. ⊤)` — satisfiable via grandparent merge
preserving `≥ 2` witnesses without clash. -/
private def grandparentMergeProblem : Problem where
  root := .some (ALC.converse collisionRole) (.min 2 collisionRole .top)
  tbox := [⟨.top, .max 2 collisionRole .top⟩]

private theorem grandparentMergeFragment : grandparentMergeProblem.isSRIQ (fun _ => 0) = true := by
  decide

#guard decideSRIQBool infiniteChainFragment == true
#guard decideSRIQBool collisionFragment == false
#guard decideSRIQBool collisionSourceFragment' == false
#guard decideSRIQBool transChainFragment == false
#guard decideSRIQBool grandparentMergeFragment == true

#print axioms initial_accessible
#print axioms decideSRIQ
#print axioms decideSRIQBool
#print axioms decideSRIQ_sat_iff
#print axioms decideSRIQ_unsat_iff
#print axioms decideSRIQ_ontology_iff
#print axioms decideSRIQBool_true_iff
#print axioms decideSRIQBool_false_iff
#print axioms decideSRIQBool_ontology_iff
#print axioms infiniteChain_decideSRIQ_sat
#print axioms collision_decideSRIQ_unsat
#print axioms collisionSource_decideSRIQ_unsat

end BlockedBranch

end Sabrina.OWL2.SROIQD.Termination
