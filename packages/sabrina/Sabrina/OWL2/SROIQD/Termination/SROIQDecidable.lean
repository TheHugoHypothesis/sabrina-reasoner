import Sabrina.OWL2.SROIQD.Termination.SROIQSearch
import Sabrina.OWL2.SROIQD.Termination.BottomProperties
import Sabrina.OWL2.FunctionalSyntax

/-!
Unconditional termination and fuel-free decidability for full cyclic `SROIQ`
(TBox, RBox with regular role chains, inverse roles, qualified number
restrictions, nominals, ABox assertions, `HasKey` axioms, and the NN-rule).

Every search step strictly decreases a two-stage fixed-length lexicographic
measure `(rootMeasureVec, treeMeasureVec)` in
`Prod.Lex (VecLex (N := sroiqMaxDepth rank p + 1) PairLex)
          (VecLex (N := sroiqMaxDepth rank p + 2) PairLex)`:
1. `rootMeasureVec ℓ` tracks `(numRootsAtLevel ℓ, sumUnfiredNNAtLevel ℓ)` over
   nominal levels `0 .. sroiqMaxDepth rank p`.
   - `rootMerge` drops a root at level `ℓ`, preserving all strictly lower
     nominal levels with monotone `HasNNBound` and strictly decreasing
     `numRootsAtLevel ℓ`.
   - `nnExpand` installs `HasNNBound` for a previously unfired `.max` concept
     at level `ℓ` and allocates fresh roots only at `ℓ + 1 ≤ sroiqMaxDepth`.
2. `treeMeasureVec d` tracks `(levelCount d, levelPotential d)` over tree depths
   `0 .. sroiqMaxDepth rank p + 1`, where `nodePotential` counts missing
   concepts, missing NFA guards, missing `down`/`up`/`loops`, missing
   `GenProtected` witnesses, missing `rootEdges`, and missing `toRoot` edges.
   - `addLabel`, `addGuard`, `addEdge`, `blockableMerge`, and `generate` all
     preserve the root set and `HasNNBound` bijectively (`rootMeasureVec` is
     unchanged) and strictly decrease `treeMeasureVec`.

Well-foundedness of this two-stage lexicographic order supplies
`Acc (SROIQFollows hsroiq) (SROIQState.initial rank p)` unconditionally,
yielding the fuel-free decision procedures `decideSROIQ` and `decideSROIQBool`.
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank)

namespace BlockedForest

/-! ### Finite missing-item counting and list comparison helpers -/

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

private theorem sum_map_eq_of_bij {α β : Type} (l₁ : List α) (l₂ : List β)
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) (f : α → β) (g₁ : α → Nat) (g₂ : β → Nat)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, f a = f a' → a = a')
    (hmem : ∀ a ∈ l₁, f a ∈ l₂)
    (hsurj : ∀ b ∈ l₂, ∃ a ∈ l₁, f a = b)
    (heq : ∀ a ∈ l₁, g₁ a = g₂ (f a)) :
    (l₁.map g₁).sum = (l₂.map g₂).sum := by
  classical
  have hle₁ : (l₁.map g₁).sum ≤ (l₂.map g₂).sum :=
    sum_map_le_of_inj l₁ l₂ hnd₁ f g₁ g₂ hinj hmem (fun a ha => Nat.le_of_eq (heq a ha))
  have hle₂ : (l₂.map g₂).sum ≤ (l₁.map g₁).sum := by
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => exact Nat.le_refl 0
      | cons b _ => obtain ⟨a, ha, _⟩ := hsurj b (List.mem_cons_self ..); cases ha
    | cons a₀ rest =>
      let l₁' := a₀ :: rest
      let inv (b : β) : α := if h : b ∈ l₂ then Classical.choose (hsurj b h) else a₀
      have hinvMem (b : β) (hb : b ∈ l₂) : inv b ∈ l₁' := by
        simp only [inv, dite_eq_left hb]; exact (Classical.choose_spec (hsurj b hb)).1
      have hinvEq (b : β) (hb : b ∈ l₂) : f (inv b) = b := by
        simp only [inv, dite_eq_left hb]; exact (Classical.choose_spec (hsurj b hb)).2
      exact sum_map_le_of_inj l₂ l₁' hnd₂ inv g₂ g₁
        (fun b hb b' hb' he => by rw [← hinvEq b hb, ← hinvEq b' hb', he])
        hinvMem
        (fun b hb => by rw [heq (inv b) (hinvMem b hb), hinvEq b hb]; exact Nat.le_refl _)
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

private theorem missingCount_le_of_bij {α β : Type} (U₁ : List α) (U₂ : List β)
    (hnd₂ : U₂.Nodup) (P₁ : α → Prop) (P₂ : β → Prop) (f : α → β)
    (hsurj : ∀ b ∈ U₂, ∃ a ∈ U₁, f a = b)
    (himp : ∀ a ∈ U₁, P₁ a → P₂ (f a)) :
    missingCount U₂ P₂ ≤ missingCount U₁ P₁ := by
  classical
  unfold missingCount
  letI := Classical.propDecidable
  cases U₁ with
  | nil =>
    cases U₂ with
    | nil => simp
    | cons b _ => obtain ⟨a, ha, _⟩ := hsurj b (List.mem_cons_self ..); cases ha
  | cons a₀ rest =>
    let U₁' := a₀ :: rest
    let inv (b : β) : α := if h : b ∈ U₂ then Classical.choose (hsurj b h) else a₀
    have hinvMem (b : β) (hb : b ∈ U₂) : inv b ∈ U₁' := by
      simp only [inv, dite_eq_left hb]; exact (Classical.choose_spec (hsurj b hb)).1
    have hinvEq (b : β) (hb : b ∈ U₂) : f (inv b) = b := by
      simp only [inv, dite_eq_left hb]; exact (Classical.choose_spec (hsurj b hb)).2
    refine length_le_of_inj (U₂.filter (fun b => !decide (P₂ b)))
      (U₁'.filter (fun a => !decide (P₁ a))) (hnd₂.filter _) inv ?_ ?_
    · intro b hb b' hb' heq
      have hb2 := (List.mem_filter.mp hb).1
      have hb2' := (List.mem_filter.mp hb').1
      rw [← hinvEq b hb2, ← hinvEq b' hb2', heq]
    · intro b hb
      obtain ⟨hb2, hnot2⟩ := List.mem_filter.mp hb
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnot2
      refine List.mem_filter.mpr ⟨hinvMem b hb2, ?_⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro hp1
      exact hnot2 (hinvEq b hb2 ▸ himp (inv b) (hinvMem b hb2) hp1)

private def listProduct {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun a => ys.map (a, ·)

private theorem mem_listProduct {α β : Type} {xs : List α} {ys : List β} {q : α × β} :
    q ∈ listProduct xs ys ↔ q.1 ∈ xs ∧ q.2 ∈ ys := by
  simp only [listProduct, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩; exact ⟨q.1, h1, q.2, h2, rfl⟩

private theorem nodup_product {α β : Type} {xs : List α} {ys : List β}
    (hx : xs.Nodup) (hy : ys.Nodup) : (listProduct xs ys).Nodup := by
  induction xs with
  | nil => simp [listProduct]
  | cons a rest ih =>
    have ⟨hna, hrest⟩ := List.nodup_cons.mp hx
    have hmap : (ys.map (a, ·)).Nodup :=
      List.pairwise_map.mpr (hy.imp fun hne heq => hne (congrArg Prod.snd heq))
    have hdisj : ∀ p ∈ ys.map (a, ·), p ∉ listProduct rest ys := by
      intro p hp hpr
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
      exact hna (mem_listProduct.mp hpr).1
    change (ys.map (a, ·) ++ listProduct rest ys).Nodup
    exact List.nodup_append.mpr ⟨hmap, ih hrest, fun p hp q hq heq => hdisj p hp (heq ▸ hq)⟩

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
    | zero => exact Prod.Lex.left _ _ hlt
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

private theorem pairLex_or_eq_of_eq_le {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ = a₂) (hb : b₁ ≤ b₂) :
    (a₁, b₁) = (a₂, b₂) ∨ PairLex (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_eq_of_le hb with hlt | heq
  · exact .inr (ha ▸ Prod.Lex.right a₁ hlt)
  · exact .inl (Prod.ext ha heq)

/-! ### Two-stage measure on `BlockedForest` -/

private def rootsList (b : BlockedForest) : List b.Node :=
  (List.finRange (b.size + 1)).filter b.isRoot

private theorem mem_rootsList {b : BlockedForest} {x : b.Node} :
    x ∈ rootsList b ↔ b.isRoot x = true := by
  simp [rootsList]

private theorem nodup_rootsList (b : BlockedForest) : (rootsList b).Nodup :=
  (List.nodup_finRange _).filter _

private def rootsAtLevel (b : BlockedForest) (ℓ : Nat) : List b.Node :=
  (List.finRange (b.size + 1)).filter (fun x => b.isRoot x && b.nomLevel x == ℓ)

private theorem mem_rootsAtLevel {b : BlockedForest} {ℓ : Nat} {x : b.Node} :
    x ∈ rootsAtLevel b ℓ ↔ b.isRoot x = true ∧ b.nomLevel x = ℓ := by
  simp [rootsAtLevel]

private theorem nodup_rootsAtLevel (b : BlockedForest) (ℓ : Nat) :
    (rootsAtLevel b ℓ).Nodup :=
  (List.nodup_finRange _).filter _

private noncomputable def rootUnfiredNN (p : Problem) (b : BlockedForest) (x : b.Node) : Nat :=
  missingCount (sroiqClos p) (fun c => b.HasNNBound x c)

private noncomputable def rootMeasureVec (rank : Rank) (p : Problem) (b : BlockedForest) :
    Fin (sroiqMaxDepth rank p + 1) → Nat × Nat :=
  fun ℓ => ((rootsAtLevel b ℓ.val).length, ((rootsAtLevel b ℓ.val).map (rootUnfiredNN p b)).sum)

private def nodesAtDepth (b : BlockedForest) (d : Nat) : List b.Node :=
  (List.finRange (b.size + 1)).filter (fun x => b.depth x == d)

private theorem mem_nodesAtDepth {b : BlockedForest} {d : Nat} {x : b.Node} :
    x ∈ nodesAtDepth b d ↔ b.depth x = d := by
  simp [nodesAtDepth]

private theorem nodup_nodesAtDepth (b : BlockedForest) (d : Nat) :
    (nodesAtDepth b d).Nodup :=
  (List.nodup_finRange _).filter _

private noncomputable def nodeKeyPotential (p : Problem) (b : BlockedForest)
    (x : b.Node) : Nat :=
  missingCount (listProduct (sroiqDataProps p) (rootsList b))
    (fun q => (x, q.2, q.1) ∈ b.keyDisjoint)

private noncomputable def nodePotential (rank : Rank) (p : Problem) (b : BlockedForest)
    (x : b.Node) : Nat :=
  missingCount (sroiqClos p) (fun c => c ∈ b.labels x) +
  missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels x) +
  missingCount (sroiqRoleNames p) (fun r => r ∈ b.down x) +
  missingCount (sroiqRoleNames p) (fun r => r ∈ b.up x) +
  missingCount (sroiqRoleNames p) (fun r => r ∈ b.loops x) +
  missingCount (sroiqClos p) (fun c => b.GenProtected x c) +
  missingCount (listProduct (sroiqRoleNames p) (rootsList b))
    (fun q => (q.1, x, q.2) ∈ b.rootEdges) +
  missingCount (listProduct (sroiqOrientedRoles p) (rootsList b))
    (fun q => (q.1, q.2) ∈ b.toRoot x) +
  nodeKeyPotential p b x

private noncomputable def levelPotential (rank : Rank) (p : Problem) (b : BlockedForest)
    (d : Nat) : Nat :=
  ((nodesAtDepth b d).map (nodePotential rank p b)).sum

private noncomputable def treeMeasureVec (rank : Rank) (p : Problem) (b : BlockedForest) :
    Fin (sroiqMaxDepth rank p + 2) → Nat × Nat :=
  fun d => ((nodesAtDepth b d.val).length, levelPotential rank p b d.val)

private noncomputable def sroiqMeasure (rank : Rank) (p : Problem) (b : BlockedForest) :
    (Fin (sroiqMaxDepth rank p + 1) → Nat × Nat) ×
    (Fin (sroiqMaxDepth rank p + 2) → Nat × Nat) :=
  (rootMeasureVec rank p b, treeMeasureVec rank p b)

private def SROIQMeasureLt (rank : Rank) (p : Problem) :=
  Prod.Lex (VecLex (N := sroiqMaxDepth rank p + 1) PairLex)
           (VecLex (N := sroiqMaxDepth rank p + 2) PairLex)

private theorem wellFounded_sroiqMeasureLt (rank : Rank) (p : Problem) :
    WellFounded (SROIQMeasureLt rank p) :=
  (Prod.lex
    ⟨VecLex PairLex, wellFounded_vecLex wellFounded_pairLex⟩
    ⟨VecLex PairLex, wellFounded_vecLex wellFounded_pairLex⟩).wf

/-! ### Helper lemmas for `sroiqRoleNames` / `sroiqOrientedRoles` Nodup -/

private theorem nodup_sroiqRoleNames (p : Problem) : (sroiqRoleNames p).Nodup := by
  unfold sroiqRoleNames
  exact nodup_eraseDups_list _

private theorem nodup_sroiqDataProps (p : Problem) : (sroiqDataProps p).Nodup := by
  unfold sroiqDataProps
  exact nodup_eraseDups_list _

private theorem nodup_sroiqOrientedRoles (p : Problem) : (sroiqOrientedRoles p).Nodup := by
  unfold sroiqOrientedRoles
  have aux : ∀ xs : List IRI, xs.Nodup → (xs.flatMap (fun r => [(r, false), (r, true)])).Nodup := by
    intro xs hnd
    induction xs with
    | nil => simp
    | cons a rest ih =>
      have ⟨hna, hr⟩ := List.nodup_cons.mp hnd
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨?_, ?_, ih hr⟩
      · intro h
        rcases List.mem_cons.mp h with h1 | h2
        · cases h1
        · obtain ⟨r, hr', hm⟩ := List.mem_flatMap.mp h2
          rcases List.mem_cons.mp hm with h1 | h2
          · cases h1; exact hna hr'
          · obtain h3 := List.mem_singleton.mp h2; cases h3
      · intro h
        obtain ⟨r, hr', hm⟩ := List.mem_flatMap.mp h
        rcases List.mem_cons.mp hm with h1 | h2
        · cases h1
        · obtain h3 := List.mem_singleton.mp h2; cases h3; exact hna hr'
  exact aux (sroiqRoleNames p) (nodup_sroiqRoleNames p)

/-! ### Strict measure decrease for every `SROIQStrictStep` -/

private theorem merge_hasNNBound_fwd {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {y : (b.mergeForest keep drop hd hk hvalid).Node} {c : Concept}
    (h : b.HasNNBound (prunedSrc hd y) c) :
    (b.mergeForest keep drop hd hk hvalid).HasNNBound y c := by
  cases c with
  | max n r d =>
    obtain ⟨ts, hts⟩ := h
    have hne : prunedSrc hd y ≠ drop := (mem_retained.mp (source_mem hd _)).1
    have hyi : prunedIdx hd hk (prunedSrc hd y) = some y := by
      unfold prunedIdx prunedSrc
      rw [mergeIndex_kept hd hk (source_mem hd _), compact_source]
      rfl
    refine ⟨ts.filterMap (prunedIdx hd hk), List.mem_filterMap.mpr ⟨(prunedSrc hd y, r, d, ts), hts, ?_⟩⟩
    dsimp only
    rw [ite_eq_right hne, hyi]
    rfl
  | _ => trivial

private theorem merge_hasNNBound_bwd {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {y : (b.mergeForest keep drop hd hk hvalid).Node} {c : Concept}
    (h : (b.mergeForest keep drop hd hk hvalid).HasNNBound y c) :
    b.HasNNBound (prunedSrc hd y) c := by
  cases c with
  | max n r d =>
    obtain ⟨ts', hts'⟩ := h
    obtain ⟨⟨u, s', d', ts⟩, hm, hres⟩ := List.mem_filterMap.mp hts'
    by_cases hud : u = drop
    · simp [hud] at hres
    · simp only [hud, ↓reduceIte] at hres
      obtain ⟨u', hu', heq⟩ := Option.map_eq_some_iff.mp hres
      cases heq
      have hsu : prunedSrc hd y = u := by
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hu'
        rw [prunedSrc_from, mergeIndex_source hd hk hp, ite_eq_right hud]
      exact ⟨ts, hsu.symm ▸ hm⟩
  | _ => trivial

private theorem nodePotential_le_of_parts {rank : Rank} {p : Problem} {b b' : BlockedForest}
    {x : b.Node} {y : b'.Node}
    (h1 : missingCount (sroiqClos p) (fun d => d ∈ b'.labels y) ≤ missingCount (sroiqClos p) (fun d => d ∈ b.labels x))
    (h2 : missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels y) ≤ missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels x))
    (h3 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.down y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.down x))
    (h4 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.up y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.up x))
    (h5 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.loops y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.loops x))
    (h6 : missingCount (sroiqClos p) (fun d => b'.GenProtected y d) ≤ missingCount (sroiqClos p) (fun d => b.GenProtected x d))
    (h7 : missingCount (listProduct (sroiqRoleNames p) (rootsList b')) (fun q => (q.1, y, q.2) ∈ b'.rootEdges) ≤
          missingCount (listProduct (sroiqRoleNames p) (rootsList b)) (fun q => (q.1, x, q.2) ∈ b.rootEdges))
    (h8 : missingCount (listProduct (sroiqOrientedRoles p) (rootsList b')) (fun q => (q.1, q.2) ∈ b'.toRoot y) ≤
          missingCount (listProduct (sroiqOrientedRoles p) (rootsList b)) (fun q => (q.1, q.2) ∈ b.toRoot x))
    (h9 : nodeKeyPotential p b' y ≤ nodeKeyPotential p b x := by exact Nat.le_refl _) :
    nodePotential rank p b' y ≤ nodePotential rank p b x := by
  unfold nodePotential; omega

private theorem nodePotential_lt_of_parts {rank : Rank} {p : Problem} {b b' : BlockedForest}
    {x : b.Node} {y : b'.Node}
    (h1 : missingCount (sroiqClos p) (fun d => d ∈ b'.labels y) ≤ missingCount (sroiqClos p) (fun d => d ∈ b.labels x))
    (h2 : missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels y) ≤ missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels x))
    (h3 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.down y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.down x))
    (h4 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.up y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.up x))
    (h5 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.loops y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.loops x))
    (h6 : missingCount (sroiqClos p) (fun d => b'.GenProtected y d) ≤ missingCount (sroiqClos p) (fun d => b.GenProtected x d))
    (h7 : missingCount (listProduct (sroiqRoleNames p) (rootsList b')) (fun q => (q.1, y, q.2) ∈ b'.rootEdges) ≤
          missingCount (listProduct (sroiqRoleNames p) (rootsList b)) (fun q => (q.1, x, q.2) ∈ b.rootEdges))
    (h8 : missingCount (listProduct (sroiqOrientedRoles p) (rootsList b')) (fun q => (q.1, q.2) ∈ b'.toRoot y) ≤
          missingCount (listProduct (sroiqOrientedRoles p) (rootsList b)) (fun q => (q.1, q.2) ∈ b.toRoot x))
    (hlt :
      missingCount (sroiqClos p) (fun d => d ∈ b'.labels y) < missingCount (sroiqClos p) (fun d => d ∈ b.labels x) ∨
      missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels y) < missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels x) ∨
      missingCount (sroiqRoleNames p) (fun r => r ∈ b'.down y) < missingCount (sroiqRoleNames p) (fun r => r ∈ b.down x) ∨
      missingCount (sroiqRoleNames p) (fun r => r ∈ b'.up y) < missingCount (sroiqRoleNames p) (fun r => r ∈ b.up x) ∨
      missingCount (sroiqRoleNames p) (fun r => r ∈ b'.loops y) < missingCount (sroiqRoleNames p) (fun r => r ∈ b.loops x) ∨
      missingCount (sroiqClos p) (fun d => b'.GenProtected y d) < missingCount (sroiqClos p) (fun d => b.GenProtected x d) ∨
      missingCount (listProduct (sroiqRoleNames p) (rootsList b')) (fun q => (q.1, y, q.2) ∈ b'.rootEdges) <
        missingCount (listProduct (sroiqRoleNames p) (rootsList b)) (fun q => (q.1, x, q.2) ∈ b.rootEdges) ∨
      missingCount (listProduct (sroiqOrientedRoles p) (rootsList b')) (fun q => (q.1, q.2) ∈ b'.toRoot y) <
        missingCount (listProduct (sroiqOrientedRoles p) (rootsList b)) (fun q => (q.1, q.2) ∈ b.toRoot x))
    (h9 : nodeKeyPotential p b' y ≤ nodeKeyPotential p b x := by exact Nat.le_refl _) :
    nodePotential rank p b' y < nodePotential rank p b x := by
  unfold nodePotential; omega

private theorem nodePotential_lt_of_key {rank : Rank} {p : Problem} {b b' : BlockedForest}
    {x : b.Node} {y : b'.Node}
    (h1 : missingCount (sroiqClos p) (fun d => d ∈ b'.labels y) ≤ missingCount (sroiqClos p) (fun d => d ∈ b.labels x))
    (h2 : missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels y) ≤ missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels x))
    (h3 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.down y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.down x))
    (h4 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.up y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.up x))
    (h5 : missingCount (sroiqRoleNames p) (fun r => r ∈ b'.loops y) ≤ missingCount (sroiqRoleNames p) (fun r => r ∈ b.loops x))
    (h6 : missingCount (sroiqClos p) (fun d => b'.GenProtected y d) ≤ missingCount (sroiqClos p) (fun d => b.GenProtected x d))
    (h7 : missingCount (listProduct (sroiqRoleNames p) (rootsList b')) (fun q => (q.1, y, q.2) ∈ b'.rootEdges) ≤
          missingCount (listProduct (sroiqRoleNames p) (rootsList b)) (fun q => (q.1, x, q.2) ∈ b.rootEdges))
    (h8 : missingCount (listProduct (sroiqOrientedRoles p) (rootsList b')) (fun q => (q.1, q.2) ∈ b'.toRoot y) ≤
          missingCount (listProduct (sroiqOrientedRoles p) (rootsList b)) (fun q => (q.1, q.2) ∈ b.toRoot x))
    (h9 : nodeKeyPotential p b' y < nodeKeyPotential p b x) :
    nodePotential rank p b' y < nodePotential rank p b x := by
  unfold nodePotential; omega

private theorem same_node_treeMeasure_lt {rank : Rank} {p : Problem}
    {b b' : BlockedForest} (hg : b.ForestGeom rank p)
    (hsz : b'.size = b.size)
    (hdepth : ∀ z : b.Node, b'.depth (Fin.cast (congrArg (· + 1) hsz.symm) z) = b.depth z)
    (hpotLe : ∀ z : b.Node, nodePotential rank p b' (Fin.cast (congrArg (· + 1) hsz.symm) z) ≤ nodePotential rank p b z)
    {z₀ : b.Node}
    (hpotLt : nodePotential rank p b' (Fin.cast (congrArg (· + 1) hsz.symm) z₀) < nodePotential rank p b z₀) :
    VecLex PairLex (treeMeasureVec rank p b') (treeMeasureVec rank p b) := by
  let cast : b.Node → b'.Node := Fin.cast (congrArg (· + 1) hsz.symm)
  let uncast : b'.Node → b.Node := Fin.cast (congrArg (· + 1) hsz)
  have hcu (y : b'.Node) : Fin.cast (congrArg (· + 1) hsz.symm) (uncast y) = y := Fin.ext rfl
  have huc (z : b.Node) : uncast (cast z) = z := Fin.ext rfl
  have huncastInj (a c : b'.Node) (h : uncast a = uncast c) : a = c :=
    Fin.ext (by simpa [uncast] using congrArg Fin.val h)
  have huncastDepth (j : Nat) (y : b'.Node) (hy : y ∈ nodesAtDepth b' j) : uncast y ∈ nodesAtDepth b j := by
    have hdy : b'.depth y = j := mem_nodesAtDepth.mp hy
    have hd := hdepth (uncast y)
    rw [hcu y] at hd
    exact mem_nodesAtDepth.mpr (hd.symm.trans hdy)
  have hlevelEq (j : Nat) : (nodesAtDepth b' j).length = (nodesAtDepth b j).length :=
    length_eq_of_bij (nodesAtDepth b' j) (nodesAtDepth b j)
      (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) uncast
      (fun a _ c _ h => huncastInj a c h) (huncastDepth j)
      (fun x hx => ⟨cast x, mem_nodesAtDepth.mpr ((hdepth x).trans (mem_nodesAtDepth.mp hx)), huc x⟩)
  have hlevelLe (j : Nat) : levelPotential rank p b' j ≤ levelPotential rank p b j :=
    sum_map_le_of_inj (nodesAtDepth b' j) (nodesAtDepth b j) (nodup_nodesAtDepth _ _) uncast _ _
      (fun a _ c _ h => huncastInj a c h) (huncastDepth j)
      (fun y _ => by have h := hpotLe (uncast y); rwa [hcu y] at h)
  have hkLt : b.depth z₀ < sroiqMaxDepth rank p + 2 := Nat.lt_succ_of_le (hg.depthBound z₀)
  apply vecLex_of_prefix_le_lt ⟨b.depth z₀, hkLt⟩
  · intro j _
    exact pairLex_or_eq_of_eq_le (hlevelEq j.val) (hlevelLe j.val)
  · have hltSum : levelPotential rank p b' (b.depth z₀) < levelPotential rank p b (b.depth z₀) :=
      sum_map_lt_of_inj (nodesAtDepth b' (b.depth z₀)) (nodesAtDepth b (b.depth z₀))
        (nodup_nodesAtDepth _ _) uncast _ _
        (fun a _ c _ h => huncastInj a c h) (huncastDepth (b.depth z₀))
        (fun y _ => by have h := hpotLe (uncast y); rwa [hcu y] at h)
        (a₀ := cast z₀) (mem_nodesAtDepth.mpr (hdepth z₀)) (by rw [huc z₀]; exact hpotLt)
    change PairLex ((nodesAtDepth b' (b.depth z₀)).length, levelPotential rank p b' (b.depth z₀))
      ((nodesAtDepth b (b.depth z₀)).length, levelPotential rank p b (b.depth z₀))
    rw [hlevelEq (b.depth z₀)]
    exact Prod.Lex.right _ hltSum

private theorem measure_lt_rootMerge {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (keep drop : b.Node) (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) (hdrop : b.isRoot drop = true) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.mergeForest keep drop hd hk hvalid))
      (sroiqMeasure rank p b) := by
  let b' := b.mergeForest keep drop hd hk hvalid
  apply Prod.Lex.left
  have hkd : b.nomLevel drop < sroiqMaxDepth rank p + 1 :=
    Nat.lt_succ_of_le (hg.nomLevelBound drop hdrop)
  have hsrcMem (j : Nat) (y : b'.Node) (hy : y ∈ rootsAtLevel b' j) :
      prunedSrc hd y ∈ rootsAtLevel b j := by
    have h : b'.isRoot y = true ∧ b'.nomLevel y = j := mem_rootsAtLevel.mp hy
    exact mem_rootsAtLevel.mpr h
  have hnnLe (y : b'.Node) : rootUnfiredNN p b' y ≤ rootUnfiredNN p b (prunedSrc hd y) :=
    missingCount_le (sroiqClos p) (fun _ _ h => merge_hasNNBound_fwd h)
  apply vecLex_of_prefix_le_lt ⟨b.nomLevel drop, hkd⟩
  · intro j hjlt
    have hlenEq : (rootsAtLevel b' j.val).length = (rootsAtLevel b j.val).length := by
      apply length_eq_of_bij _ _ (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (prunedSrc hd)
      · intro a _ c _ h; exact prunedSrc_inj hd h
      · exact hsrcMem j.val
      · intro u hu
        have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
        have hud : u ≠ drop := fun h => by rw [h] at hul; exact Nat.ne_of_lt hjlt hul.symm
        have hret : u ∈ b.retained drop := retained_of_isRoot hur hud
        refine ⟨prunedFrom hd (compact hd hret), mem_rootsAtLevel.mpr ?_, prunedSrc_compact hd hret⟩
        change b.isRoot (prunedSrc hd _) = true ∧ b.nomLevel (prunedSrc hd _) = j.val
        rw [prunedSrc_compact hd hret]; exact ⟨hur, hul⟩
    have hsumLe : ((rootsAtLevel b' j.val).map (rootUnfiredNN p b')).sum ≤
        ((rootsAtLevel b j.val).map (rootUnfiredNN p b)).sum :=
      sum_map_le_of_inj _ _ (nodup_rootsAtLevel _ _) (prunedSrc hd) _ _
        (fun a _ c _ h => prunedSrc_inj hd h) (hsrcMem j.val) (fun y _ => hnnLe y)
    exact pairLex_or_eq_of_eq_le hlenEq hsumLe
  · apply Prod.Lex.left
    exact length_lt_of_inj_missing _ _ (nodup_rootsAtLevel _ _) (prunedSrc hd)
      (fun a _ c _ h => prunedSrc_inj hd h) (hsrcMem (b.nomLevel drop))
      (b₀ := drop) (mem_rootsAtLevel.mpr ⟨hdrop, rfl⟩)
      (fun y _ h => (mem_retained.mp (source_mem hd _)).1 h)

private theorem measure_lt_nnExpand {rank : Rank} {p : Problem} {b : BlockedForest}
    (m : Nat) (r : b.Node) (hr : b.isRoot r = true) (rel : OrientedRole) (c : Concept) (n : Nat)
    (hmax : .max n rel c ∈ sroiqClos p) (hno : ¬ b.HasNNBound r (.max n rel c))
    (hlvl : b.nomLevel r + 1 ≤ sroiqMaxDepth rank p) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.appendNNRoots m r hr rel c))
      (sroiqMeasure rank p b) := by
  let b' := b.appendNNRoots m r hr rel c
  apply Prod.Lex.left
  have hkr : b.nomLevel r < sroiqMaxDepth rank p + 1 := by omega
  have hnnFwd (u : b.Node) (d : Concept) (h : b.HasNNBound u d) : b'.HasNNBound (oldNode m u) d := by
    cases d with
    | max n' s' c' =>
      obtain ⟨ts, hts⟩ := h
      exact ⟨ts.map (oldNode m), List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(u, s', c', ts), hts, rfl⟩)⟩
    | _ => trivial
  have hnnLe (u : b.Node) : rootUnfiredNN p b' (oldNode m u) ≤ rootUnfiredNN p b u :=
    missingCount_le (sroiqClos p) (fun d _ h => hnnFwd u d h)
  have hnnLt : rootUnfiredNN p b' (oldNode m r) < rootUnfiredNN p b r := by
    refine missingCount_lt (sroiqClos p) (fun d _ h => hnnFwd r d h) hmax hno ?_
    exact ⟨(List.finRange m).map b.newNode, List.mem_cons_self ..⟩
  have hbijLevel (j : Nat) (hj : j ≤ b.nomLevel r) :
      (rootsAtLevel b' j).length = (rootsAtLevel b j).length ∧
      ∀ y ∈ rootsAtLevel b' j, ∃ u ∈ rootsAtLevel b j, y = oldNode m u := by
    have hsurj : ∀ y ∈ rootsAtLevel b' j, ∃ u ∈ rootsAtLevel b j, y = oldNode m u := by
      intro y hy
      have ⟨hyr, hyl⟩ := mem_rootsAtLevel.mp hy
      rcases extended_cases (b := b) y with ⟨u, rfl⟩ | ⟨k, rfl⟩
      · simp only [b', appendNNRoots, onExtended_old] at hyr hyl
        exact ⟨u, mem_rootsAtLevel.mpr ⟨hyr, hyl⟩, rfl⟩
      · simp only [b', appendNNRoots, onExtended_new] at hyl
        omega
    refine ⟨?_, hsurj⟩
    apply (length_eq_of_bij (rootsAtLevel b j) (rootsAtLevel b' j)
      (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (oldNode m)
      (fun a _ c _ h => oldNode_inj h)
      (fun u hu => by
        have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
        exact mem_rootsAtLevel.mpr ⟨by simp [b', appendNNRoots, onExtended_old, hur],
          by simp [b', appendNNRoots, onExtended_old, hul]⟩)
      (fun y hy => by obtain ⟨u, hu, rfl⟩ := hsurj y hy; exact ⟨u, hu, rfl⟩)).symm
  let inv (y : b'.Node) : b.Node := if h : y.val < b.size + 1 then ⟨y.val, h⟩ else 0
  apply vecLex_of_prefix_le_lt ⟨b.nomLevel r, hkr⟩
  · intro j hjlt
    have ⟨hlenEq, hsurj⟩ := hbijLevel j.val (Nat.le_of_lt hjlt)
    have hsumLe : ((rootsAtLevel b' j.val).map (rootUnfiredNN p b')).sum ≤
        ((rootsAtLevel b j.val).map (rootUnfiredNN p b)).sum := by
      refine sum_map_le_of_inj _ _ (nodup_rootsAtLevel _ _) inv _ _ ?_ ?_ ?_
      · intro y hy y' hy' heq
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        obtain ⟨u', _, rfl⟩ := hsurj y' hy'
        have : u = u' := by simpa [inv, oldNode, u.isLt, u'.isLt] using heq
        exact congrArg (oldNode m) this
      · intro y hy
        obtain ⟨u, hu, rfl⟩ := hsurj y hy
        simpa [inv, oldNode, u.isLt] using hu
      · intro y hy
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        have hinv : inv (oldNode m u) = u := by simp [inv, oldNode, u.isLt]
        rw [hinv]; exact hnnLe u
    exact pairLex_or_eq_of_eq_le hlenEq hsumLe
  · have ⟨hlenEq, hsurj⟩ := hbijLevel (b.nomLevel r) (Nat.le_refl _)
    have hsumLt : ((rootsAtLevel b' (b.nomLevel r)).map (rootUnfiredNN p b')).sum <
        ((rootsAtLevel b (b.nomLevel r)).map (rootUnfiredNN p b)).sum := by
      refine sum_map_lt_of_inj _ _ (nodup_rootsAtLevel _ _) inv _ _ ?_ ?_ ?_
        (a₀ := oldNode m r)
        (mem_rootsAtLevel.mpr ⟨by simp [b', appendNNRoots, onExtended_old, hr],
          by simp [b', appendNNRoots, onExtended_old]⟩) ?_
      · intro y hy y' hy' heq
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        obtain ⟨u', _, rfl⟩ := hsurj y' hy'
        have : u = u' := by simpa [inv, oldNode, u.isLt, u'.isLt] using heq
        exact congrArg (oldNode m) this
      · intro y hy
        obtain ⟨u, hu, rfl⟩ := hsurj y hy
        simpa [inv, oldNode, u.isLt] using hu
      · intro y hy
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        have hinv : inv (oldNode m u) = u := by simp [inv, oldNode, u.isLt]
        rw [hinv]; exact hnnLe u
      · have hinv : inv (oldNode m r) = r := by simp [inv, oldNode]
        rw [hinv]; exact hnnLt
    change PairLex (_, _) (_, _)
    rw [hlenEq]
    exact Prod.Lex.right _ hsumLt

private theorem measure_lt_addLabel {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (x : b.Node) (c : Concept) (hc : c ∈ sroiqClos p) (hno : c ∉ b.labels x) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.addLabel x c)) (sroiqMeasure rank p b) := by
  have hrootEq : rootMeasureVec rank p (b.addLabel x c) = rootMeasureVec rank p b := rfl
  change SROIQMeasureLt rank p (rootMeasureVec rank p (b.addLabel x c), _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have hpotLe (z : b.Node) : nodePotential rank p (b.addLabel x c) z ≤ nodePotential rank p b z :=
    nodePotential_le_of_parts
      (missingCount_sub (sroiqClos p) (fun d hd => addLabel_mem.mpr (.inr hd)))
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_le _ fun d _ hd => by cases d <;> first | exact addLabel_protected hd | trivial)
      (Nat.le_refl _) (Nat.le_refl _)
  have hpotLt : nodePotential rank p (b.addLabel x c) x < nodePotential rank p b x := by
    have h1 : missingCount (sroiqClos p) (fun d => d ∈ (b.addLabel x c).labels x) <
        missingCount (sroiqClos p) (fun d => d ∈ b.labels x) :=
      missingCount_sub_lt (sroiqClos p) (fun d hd => addLabel_mem.mpr (.inr hd))
        hc hno (addLabel_mem.mpr (.inl ⟨rfl, rfl⟩))
    exact nodePotential_lt_of_parts (Nat.le_of_lt h1)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_le _ fun d _ hd => by cases d <;> first | exact addLabel_protected hd | trivial)
      (Nat.le_refl _) (Nat.le_refl _) (Or.inl h1)
  exact same_node_treeMeasure_lt hg rfl (fun z => addLabel_depth b x c z) hpotLe hpotLt

private theorem measure_lt_addGuard {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (x : b.Node) (g : Guard) (hgIn : g ∈ sroiqGuards rank p)
    (hno : g ∉ b.guardLabels x) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.addGuard x g)) (sroiqMeasure rank p b) := by
  have hrootEq : rootMeasureVec rank p (b.addGuard x g) = rootMeasureVec rank p b := rfl
  change SROIQMeasureLt rank p (rootMeasureVec rank p (b.addGuard x g), _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have hpotLe (z : b.Node) : nodePotential rank p (b.addGuard x g) z ≤ nodePotential rank p b z :=
    nodePotential_le_of_parts
      (Nat.le_refl _)
      (missingCount_sub (sroiqGuards rank p) (fun k hk => addGuard_mem.mpr (.inr hk)))
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hpotLt : nodePotential rank p (b.addGuard x g) x < nodePotential rank p b x := by
    have h2 : missingCount (sroiqGuards rank p) (fun k => k ∈ (b.addGuard x g).guardLabels x) <
        missingCount (sroiqGuards rank p) (fun k => k ∈ b.guardLabels x) :=
      missingCount_sub_lt (sroiqGuards rank p) (fun k hk => addGuard_mem.mpr (.inr hk))
        hgIn hno (addGuard_mem.mpr (.inl ⟨rfl, rfl⟩))
    exact nodePotential_lt_of_parts (Nat.le_refl _) (Nat.le_of_lt h2)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Or.inr (Or.inl h2))
  exact same_node_treeMeasure_lt hg rfl (fun z => addGuard_depth b x g z) hpotLe hpotLt

private theorem measure_lt_addEdge {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (r : OrientedRole) (x y : b.Node)
    (hr : r.1 ∈ sroiqRoleNames p) (hadm : b.EdgeAdmissible x y) (hno : ¬ b.Edge r x y) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.addEdge r x y)) (sroiqMeasure rank p b) := by
  let b' := b.addEdge r x y
  have hrootEq : rootMeasureVec rank p b' = rootMeasureVec rank p b := rfl
  change SROIQMeasureLt rank p (rootMeasureVec rank p b', _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have ⟨hdownM, hupM, hloopM, hrootM, htoRootM⟩ := addEdge_monotone (b := b) (r := r) (x := x) (y := y)
  have hparts (z : b.Node) :
      missingCount (sroiqClos p) (fun d => d ∈ b'.labels z) = missingCount (sroiqClos p) (fun d => d ∈ b.labels z) ∧
      missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels z) = missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.down z) ≤ missingCount (sroiqRoleNames p) (fun s => s ∈ b.down z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.up z) ≤ missingCount (sroiqRoleNames p) (fun s => s ∈ b.up z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.loops z) ≤ missingCount (sroiqRoleNames p) (fun s => s ∈ b.loops z) ∧
      missingCount (sroiqClos p) (fun d => b'.GenProtected z d) ≤ missingCount (sroiqClos p) (fun d => b.GenProtected z d) ∧
      missingCount (listProduct (sroiqRoleNames p) (rootsList b')) (fun q => (q.1, z, q.2) ∈ b'.rootEdges) ≤
        missingCount (listProduct (sroiqRoleNames p) (rootsList b)) (fun q => (q.1, z, q.2) ∈ b.rootEdges) ∧
      missingCount (listProduct (sroiqOrientedRoles p) (rootsList b')) (fun q => (q.1, q.2) ∈ b'.toRoot z) ≤
        missingCount (listProduct (sroiqOrientedRoles p) (rootsList b)) (fun q => (q.1, q.2) ∈ b.toRoot z) :=
    ⟨rfl, rfl, missingCount_sub _ (hdownM z), missingCount_sub _ (hupM z), missingCount_sub _ (hloopM z),
      missingCount_le _ (fun d _ hd => by cases d <;> first | exact addEdge_protected hd | trivial),
      missingCount_le _ (fun _ _ h => hrootM h), missingCount_le _ (fun _ _ h => htoRootM z h)⟩
  have hpotLe (z : b.Node) : nodePotential rank p b' z ≤ nodePotential rank p b z := by
    have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts z
    exact nodePotential_le_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
  have hexLt : ∃ z₀ : b.Node, nodePotential rank p b' z₀ < nodePotential rank p b z₀ := by
    have hhas : b'.Edge r x y := addEdge_has_edge (b := b) (r := r) hadm
    rcases hhas with ⟨hxy, hl⟩ | ⟨hxr, hyr, hre⟩ | ⟨hc, hdwn⟩ | ⟨hc, hdwn⟩ | htr | htr
    · refine ⟨x, ?_⟩
      have hnot : r.1 ∉ b.loops x := fun h => hno (.inl ⟨hxy, h⟩)
      have hlt := missingCount_sub_lt (sroiqRoleNames p) (hloopM x) hr hnot hl
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts x
      exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlt)))))
    · rcases r with ⟨rn, _ | _⟩
      · refine ⟨x, ?_⟩
        have hnot : (rn, x, y) ∉ b.rootEdges := fun h => hno (.inr (.inl ⟨hxr, hyr, h⟩))
        have hlt : missingCount (listProduct (sroiqRoleNames p) (rootsList b'))
              (fun q => (q.1, x, q.2) ∈ b'.rootEdges) <
            missingCount (listProduct (sroiqRoleNames p) (rootsList b))
              (fun q => (q.1, x, q.2) ∈ b.rootEdges) :=
          missingCount_lt _ (fun _ _ h => hrootM h) (a₀ := (rn, y))
            (mem_listProduct.mpr ⟨hr, mem_rootsList.mpr hyr⟩) hnot hre
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts x
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlt)))))))
      · refine ⟨y, ?_⟩
        have hnot : (rn, y, x) ∉ b.rootEdges := fun h => hno (.inr (.inl ⟨hxr, hyr, h⟩))
        have hlt : missingCount (listProduct (sroiqRoleNames p) (rootsList b'))
              (fun q => (q.1, y, q.2) ∈ b'.rootEdges) <
            missingCount (listProduct (sroiqRoleNames p) (rootsList b))
              (fun q => (q.1, y, q.2) ∈ b.rootEdges) :=
          missingCount_lt _ (fun _ _ h => hrootM h) (a₀ := (rn, x))
            (mem_listProduct.mpr ⟨hr, mem_rootsList.mpr hxr⟩) hnot hre
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts y
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlt)))))))
    · refine ⟨y, ?_⟩
      rcases r with ⟨rn, _ | _⟩
      · have hnot : rn ∉ b.down y := fun h => hno (.inr (.inr (.inl ⟨hc, h⟩)))
        have hlt := missingCount_sub_lt (sroiqRoleNames p) (hdownM y) hr hnot hdwn
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts y
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inl hlt)))
      · have hnot : rn ∉ b.up y := fun h => hno (.inr (.inr (.inl ⟨hc, h⟩)))
        have hlt := missingCount_sub_lt (sroiqRoleNames p) (hupM y) hr hnot hdwn
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts y
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inr (Or.inl hlt))))
    · refine ⟨x, ?_⟩
      rcases r with ⟨rn, _ | _⟩
      · have hnot : rn ∉ b.up x := fun h => hno (.inr (.inr (.inr (.inl ⟨hc, h⟩))))
        have hlt := missingCount_sub_lt (sroiqRoleNames p) (hupM x) hr hnot hdwn
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts x
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inr (Or.inl hlt))))
      · have hnot : rn ∉ b.down x := fun h => hno (.inr (.inr (.inr (.inl ⟨hc, h⟩))))
        have hlt := missingCount_sub_lt (sroiqRoleNames p) (hdownM x) hr hnot hdwn
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts x
        exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
          (Or.inr (Or.inr (Or.inl hlt)))
    · refine ⟨x, ?_⟩
      have hnot : (r, y) ∉ b.toRoot x := fun h => hno (.inr (.inr (.inr (.inr (.inl h)))))
      have hyr : b.isRoot y = true := (b'.toRoot_valid x _ htr).2.1
      have hlt : missingCount (listProduct (sroiqOrientedRoles p) (rootsList b'))
            (fun q => (q.1, q.2) ∈ b'.toRoot x) <
          missingCount (listProduct (sroiqOrientedRoles p) (rootsList b))
            (fun q => (q.1, q.2) ∈ b.toRoot x) :=
        missingCount_lt _ (fun _ _ h => htoRootM x h) (a₀ := (r, y))
          (mem_listProduct.mpr ⟨mem_sroiqOrientedRoles hr, mem_rootsList.mpr hyr⟩) hnot htr
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts x
      exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlt)))))))
    · refine ⟨y, ?_⟩
      have hnot : (converse r, x) ∉ b.toRoot y := fun h => hno (.inr (.inr (.inr (.inr (.inr h)))))
      have hxr : b.isRoot x = true := (b'.toRoot_valid y _ htr).2.1
      have hcr : (converse r).1 ∈ sroiqRoleNames p := by rcases r with ⟨rn, _ | _⟩ <;> exact hr
      have hlt : missingCount (listProduct (sroiqOrientedRoles p) (rootsList b'))
            (fun q => (q.1, q.2) ∈ b'.toRoot y) <
          missingCount (listProduct (sroiqOrientedRoles p) (rootsList b))
            (fun q => (q.1, q.2) ∈ b.toRoot y) :=
        missingCount_lt _ (fun _ _ h => htoRootM y h) (a₀ := (converse r, x))
          (mem_listProduct.mpr ⟨mem_sroiqOrientedRoles hcr, mem_rootsList.mpr hxr⟩) hnot htr
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hparts y
      exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) h3 h4 h5 h6 h7 h8
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlt)))))))
  obtain ⟨z₀, hz₀⟩ := hexLt
  exact same_node_treeMeasure_lt hg rfl (fun z => addEdge_depth b r x y z) hpotLe hz₀

private theorem measure_lt_addKeyDisjoint {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true)
    (hdp : dp ∈ sroiqDataProps p) (hno : (r₁, r₂, dp) ∉ b.keyDisjoint) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂))
      (sroiqMeasure rank p b) := by
  let b' := b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂
  have hrootEq : rootMeasureVec rank p b' = rootMeasureVec rank p b := rfl
  change SROIQMeasureLt rank p (rootMeasureVec rank p b', _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have hpotLe (z : b.Node) : nodePotential rank p b' z ≤ nodePotential rank p b z :=
    nodePotential_le_of_parts (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_le _ fun d _ hd => by cases d <;> first | exact addKeyDisjoint_protected hd | trivial)
      (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_le _ (fun _ _ h => List.mem_cons_of_mem _ h))
  have hpotLt : nodePotential rank p b' r₁ < nodePotential rank p b r₁ :=
    nodePotential_lt_of_key (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_le _ fun d _ hd => by cases d <;> first | exact addKeyDisjoint_protected hd | trivial)
      (Nat.le_refl _) (Nat.le_refl _)
      (missingCount_lt _ (fun _ _ h => List.mem_cons_of_mem _ h)
        (a₀ := (dp, r₂)) (mem_listProduct.mpr ⟨hdp, mem_rootsList.mpr hr₂⟩)
        hno (List.mem_cons_self ..))
  exact same_node_treeMeasure_lt hg rfl (fun z => addKeyDisjoint_depth b r₁ r₂ dp hr₁ hr₂ z) hpotLe hpotLt

private theorem measure_lt_blockableMerge {rank : Rank} {p : Problem} {b : BlockedForest}
    (hg : b.ForestGeom rank p) (keep drop : b.Node) (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop)
    (hdrop : b.isRoot drop = false) (hallowed : ¬ b.RecordedDistinct keep drop) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.mergeForest keep drop hd hk hvalid))
      (sroiqMeasure rank p b) := by
  let b' := b.mergeForest keep drop hd hk hvalid
  have hrootRet (u : b.Node) (hu : b.isRoot u = true) : u ∈ b.retained drop :=
    retained_of_isRoot hu (fun h => by rw [h, hdrop] at hu; cases hu)
  have hsrcRootAt (ℓ : Nat) (y : b'.Node) (hy : y ∈ rootsAtLevel b' ℓ) :
      prunedSrc hd y ∈ rootsAtLevel b ℓ := by
    have h : b'.isRoot y = true ∧ b'.nomLevel y = ℓ := mem_rootsAtLevel.mp hy
    exact mem_rootsAtLevel.mpr h
  have hrootEq : rootMeasureVec rank p b' = rootMeasureVec rank p b := by
    funext ℓ
    have hlenEq : (rootsAtLevel b' ℓ.val).length = (rootsAtLevel b ℓ.val).length := by
      apply length_eq_of_bij _ _ (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (prunedSrc hd)
      · intro a _ c _ h; exact prunedSrc_inj hd h
      · exact hsrcRootAt ℓ.val
      · intro u hu
        have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
        refine ⟨prunedFrom hd (compact hd (hrootRet u hur)), mem_rootsAtLevel.mpr ?_, prunedSrc_compact hd _⟩
        change b.isRoot (prunedSrc hd _) = true ∧ b.nomLevel (prunedSrc hd _) = ℓ.val
        rw [prunedSrc_compact hd]; exact ⟨hur, hul⟩
    have hnnEq (y : b'.Node) : rootUnfiredNN p b' y = rootUnfiredNN p b (prunedSrc hd y) := by
      have h1 : rootUnfiredNN p b' y ≤ rootUnfiredNN p b (prunedSrc hd y) :=
        missingCount_le _ (fun _ _ h => merge_hasNNBound_fwd h)
      have h2 : rootUnfiredNN p b (prunedSrc hd y) ≤ rootUnfiredNN p b' y :=
        missingCount_le _ (fun _ _ h => merge_hasNNBound_bwd h)
      omega
    have hsumEq : ((rootsAtLevel b' ℓ.val).map (rootUnfiredNN p b')).sum =
        ((rootsAtLevel b ℓ.val).map (rootUnfiredNN p b)).sum :=
      sum_map_eq_of_bij _ _ (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (prunedSrc hd) _ _
        (fun a _ c _ h => prunedSrc_inj hd h) (hsrcRootAt ℓ.val)
        (fun u hu => by
          have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
          refine ⟨prunedFrom hd (compact hd (hrootRet u hur)), mem_rootsAtLevel.mpr ?_, prunedSrc_compact hd _⟩
          change b.isRoot (prunedSrc hd _) = true ∧ b.nomLevel (prunedSrc hd _) = ℓ.val
          rw [prunedSrc_compact hd]; exact ⟨hur, hul⟩)
        (fun y _ => hnnEq y)
    exact Prod.ext hlenEq hsumEq
  change SROIQMeasureLt rank p (rootMeasureVec rank p b', _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have hpotLe (y : b'.Node) : nodePotential rank p b' y ≤ nodePotential rank p b (prunedSrc hd y) := by
    have hrootMap (u : b.Node) (hu : b.isRoot u = true) :
        prunedIdx hd hk u = some (prunedFrom hd (compact hd (hrootRet u hu))) := by
      unfold prunedIdx; rw [mergeIndex_kept hd hk (hrootRet u hu)]; rfl
    have hyIdx : prunedIdx hd hk (prunedSrc hd y) = some y := by
      unfold prunedIdx prunedSrc; rw [mergeIndex_kept hd hk (source_mem hd _), compact_source]; rfl
    refine nodePotential_le_of_parts
      (missingCount_sub _ (fun c hc => List.mem_append_left _ hc))
      (missingCount_sub _ (fun g hg => List.mem_append_left _ hg))
      (missingCount_sub _ (fun r hr => List.mem_append_left _ hr))
      (missingCount_sub _ (fun r hr => List.mem_append_left _ hr))
      (missingCount_sub _ (fun r hr => List.mem_append_left _ hr))
      (missingCount_le _ fun c _ hc => by
        cases c with
        | some r d => exact mergeForest_protected hallowed hc
        | min n r d => exact mergeForest_protected hallowed hc
        | _ => trivial) ?_ ?_ ?_
    · let f (q : IRI × b.Node) : IRI × b'.Node :=
        if h : b.isRoot q.2 = true then (q.1, prunedFrom hd (compact hd (hrootRet q.2 h))) else (q.1, 0)
      refine missingCount_le_of_bij (listProduct (sroiqRoleNames p) (rootsList b))
        (listProduct (sroiqRoleNames p) (rootsList b'))
        (nodup_product (nodup_sroiqRoleNames p) (nodup_rootsList b')) _ _ f ?_ ?_
      · intro ⟨rn, w⟩ hw
        obtain ⟨hrn, hwr⟩ := mem_listProduct.mp hw
        have hwr' : b'.isRoot w = true := mem_rootsList.mp hwr
        have hwr0 : b.isRoot (prunedSrc hd w) = true := hwr'
        refine ⟨(rn, prunedSrc hd w), mem_listProduct.mpr ⟨hrn, mem_rootsList.mpr hwr0⟩, ?_⟩
        simp only [f, dite_eq_left hwr0]
        exact Prod.ext rfl (prunedSrc_inj hd (prunedSrc_compact hd _))
      · intro ⟨rn, u⟩ hu hmem
        obtain ⟨_, hur⟩ := mem_listProduct.mp hu
        have hur' : b.isRoot u = true := mem_rootsList.mp hur
        simp only [f, dite_eq_left hur']
        have hne_u : prunedSrc hd y ≠ u := (b.rootEdges_valid _ hmem).2.2
        have hne' : y ≠ prunedFrom hd (compact hd (hrootRet u hur')) := fun heq =>
          hne_u ((congrArg (prunedSrc hd) heq).trans (prunedSrc_compact hd _))
        refine List.mem_append_left _ (List.mem_append_left _
          (List.mem_filterMap.mpr ⟨(rn, prunedSrc hd y, u), hmem, ?_⟩))
        dsimp only
        rw [hyIdx, hrootMap u hur']
        exact ite_eq_left hne'
    · let f (q : OrientedRole × b.Node) : OrientedRole × b'.Node :=
        if h : b.isRoot q.2 = true then (q.1, prunedFrom hd (compact hd (hrootRet q.2 h))) else (q.1, 0)
      refine missingCount_le_of_bij (listProduct (sroiqOrientedRoles p) (rootsList b))
        (listProduct (sroiqOrientedRoles p) (rootsList b'))
        (nodup_product (nodup_sroiqOrientedRoles p) (nodup_rootsList b')) _ _ f ?_ ?_
      · intro ⟨rel, w⟩ hw
        obtain ⟨hrel, hwr⟩ := mem_listProduct.mp hw
        have hwr' : b'.isRoot w = true := mem_rootsList.mp hwr
        have hwr0 : b.isRoot (prunedSrc hd w) = true := hwr'
        refine ⟨(rel, prunedSrc hd w), mem_listProduct.mpr ⟨hrel, mem_rootsList.mpr hwr0⟩, ?_⟩
        simp only [f, dite_eq_left hwr0]
        exact Prod.ext rfl (prunedSrc_inj hd (prunedSrc_compact hd _))
      · intro ⟨rel, u⟩ hu hmem
        obtain ⟨_, hur⟩ := mem_listProduct.mp hu
        have hur' : b.isRoot u = true := mem_rootsList.mp hur
        simp only [f, dite_eq_left hur']
        have ⟨hynr, _, hparNe⟩ := b.toRoot_valid (prunedSrc hd y) (rel, u) hmem
        have hnp : prunedPar hd y ≠ prunedFrom hd (compact hd (hrootRet u hur')) := by
          intro heq
          have h1 := congrArg (prunedSrc hd) heq
          rw [prunedSrc_compact hd] at h1
          have h2 := compactParent_source hd (y := prunedTo hd y) hynr
          exact hparNe (h2.symm.trans h1)
        refine List.mem_append_left _ (List.mem_append_left _
          (List.mem_filterMap.mpr ⟨(rel, u), hmem, ?_⟩))
        dsimp only
        rw [hrootMap u hur']
        exact ite_eq_left hnp
    · let f (q : IRI × b.Node) : IRI × b'.Node :=
        if h : b.isRoot q.2 = true then (q.1, prunedFrom hd (compact hd (hrootRet q.2 h))) else (q.1, 0)
      refine missingCount_le_of_bij (listProduct (sroiqDataProps p) (rootsList b))
        (listProduct (sroiqDataProps p) (rootsList b'))
        (nodup_product (nodup_sroiqDataProps p) (nodup_rootsList b')) _ _ f ?_ ?_
      · intro ⟨dp, w⟩ hw
        obtain ⟨hdp, hwr⟩ := mem_listProduct.mp hw
        have hwr' : b'.isRoot w = true := mem_rootsList.mp hwr
        have hwr0 : b.isRoot (prunedSrc hd w) = true := hwr'
        refine ⟨(dp, prunedSrc hd w), mem_listProduct.mpr ⟨hdp, mem_rootsList.mpr hwr0⟩, ?_⟩
        simp only [f, dite_eq_left hwr0]
        exact Prod.ext rfl (prunedSrc_inj hd (prunedSrc_compact hd _))
      · intro ⟨dp, u⟩ hu hmem
        obtain ⟨_, hur⟩ := mem_listProduct.mp hu
        have hur' : b.isRoot u = true := mem_rootsList.mp hur
        simp only [f, dite_eq_left hur']
        refine List.mem_filterMap.mpr ⟨(prunedSrc hd y, u, dp), hmem, ?_⟩
        dsimp only
        rw [hyIdx, hrootMap u hur']
        rfl
  have hdepthEq (y : b'.Node) : b'.depth y = b.depth (prunedSrc hd y) :=
    mergeForest_depth y
  have hkd : b.depth drop < sroiqMaxDepth rank p + 2 :=
    Nat.lt_succ_of_le (hg.depthBound drop)
  apply vecLex_of_prefix_le_lt ⟨b.depth drop, hkd⟩
  · intro j hjlt
    have hjlt' : j.val < b.depth drop := hjlt
    have hlenEq : (nodesAtDepth b' j.val).length = (nodesAtDepth b j.val).length := by
      apply length_eq_of_bij _ _ (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) (prunedSrc hd)
      · intro a _ c _ h; exact prunedSrc_inj hd h
      · intro y hy; exact mem_nodesAtDepth.mpr ((hdepthEq y).symm.trans (mem_nodesAtDepth.mp hy))
      · intro u hu
        have hdu : b.depth u = j.val := mem_nodesAtDepth.mp hu
        have hret : u ∈ b.retained drop := by
          refine mem_retained.mpr ⟨fun h => by rw [h] at hdu; exact Nat.ne_of_lt hjlt' hdu.symm, fun hanc => ?_⟩
          have hlt := hanc.depth_lt; omega
        let w : b'.Node := prunedFrom hd (compact hd hret)
        refine ⟨w, mem_nodesAtDepth.mpr ?_, prunedSrc_compact hd hret⟩
        rw [hdepthEq w, prunedSrc_compact hd hret]; exact hdu
    have hsumLe : levelPotential rank p b' j.val ≤ levelPotential rank p b j.val := by
      unfold levelPotential
      exact sum_map_le_of_inj (nodesAtDepth b' j.val) (nodesAtDepth b j.val)
        (nodup_nodesAtDepth _ _) (prunedSrc hd) (nodePotential rank p b') (nodePotential rank p b)
        (fun a _ c _ h => prunedSrc_inj hd h)
        (fun y hy => mem_nodesAtDepth.mpr ((hdepthEq y).symm.trans (mem_nodesAtDepth.mp hy)))
        (fun y _ => hpotLe y)
    exact pairLex_or_eq_of_eq_le hlenEq hsumLe
  · apply Prod.Lex.left
    exact length_lt_of_inj_missing (nodesAtDepth b' (b.depth drop)) (nodesAtDepth b (b.depth drop))
      (nodup_nodesAtDepth _ _) (prunedSrc hd)
      (fun a _ c _ h => prunedSrc_inj hd h)
      (fun y hy => mem_nodesAtDepth.mpr ((hdepthEq y).symm.trans (mem_nodesAtDepth.mp hy)))
      (b₀ := drop) (mem_nodesAtDepth.mpr rfl)
      (fun y _ h => (mem_retained.mp (source_mem hd _)).1 h)

private theorem measure_lt_generate {rank : Rank} {p : Problem} {b : BlockedForest}
    (n : Nat) (x : b.Node) (r : OrientedRole) (c : Concept)
    (hdepth : b.depth x ≤ sroiqMaxDepth rank p)
    (hgen : (.some r c ∈ sroiqClos p ∧ n = 1 ∧ ¬ b.GenProtected x (.some r c)) ∨
            (.min n r c ∈ sroiqClos p ∧ ¬ b.GenProtected x (.min n r c))) :
    SROIQMeasureLt rank p (sroiqMeasure rank p (b.appendChildren n x r c))
      (sroiqMeasure rank p b) := by
  let b' := b.appendChildren n x r c
  have hrootOld (y : b'.Node) (hy : b'.isRoot y = true) : ∃ u : b.Node, b.isRoot u = true ∧ y = oldNode n u := by
    rcases extended_cases (b := b) y with ⟨u, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨u, by simpa [b', appendChildren, onExtended_old] using hy, rfl⟩
    · simp [b', appendChildren, onExtended_new] at hy
  have hnnIff (u : b.Node) (d : Concept) : b'.HasNNBound (oldNode n u) d ↔ b.HasNNBound u d := by
    cases d with
    | max m s' c' =>
      constructor
      · rintro ⟨ts', hts'⟩
        obtain ⟨⟨u', s'', c'', ts⟩, hm, heq⟩ := List.mem_map.mp hts'
        obtain ⟨hu', hs', hc', _⟩ : oldNode n u' = oldNode n u ∧ s'' = s' ∧ c'' = c' ∧ ts.map (oldNode n) = ts' :=
          ⟨congrArg Prod.fst heq, congrArg (fun q => q.2.1) heq,
           congrArg (fun q => q.2.2.1) heq, congrArg (fun q => q.2.2.2) heq⟩
        obtain rfl := oldNode_inj hu'; subst hs'; subst hc'
        exact ⟨ts, hm⟩
      · rintro ⟨ts, hts⟩
        exact ⟨ts.map (oldNode n), List.mem_map.mpr ⟨(u, s', c', ts), hts, rfl⟩⟩
    | _ => exact Iff.rfl
  have hrootEq : rootMeasureVec rank p b' = rootMeasureVec rank p b := by
    funext ℓ
    have hlenEq : (rootsAtLevel b' ℓ.val).length = (rootsAtLevel b ℓ.val).length := by
      apply (length_eq_of_bij (rootsAtLevel b ℓ.val) (rootsAtLevel b' ℓ.val)
        (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (oldNode n)
        (fun a _ c _ h => oldNode_inj h)
        (fun u hu => by
          have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
          exact mem_rootsAtLevel.mpr ⟨by simp [b', appendChildren, onExtended_old, hur],
            by simp [b', appendChildren, onExtended_old, hul]⟩)
        (fun y hy => by
          have ⟨hyr, hyl⟩ := mem_rootsAtLevel.mp hy
          obtain ⟨u, hur, rfl⟩ := hrootOld y hyr
          exact ⟨u, mem_rootsAtLevel.mpr ⟨hur, by simpa [b', appendChildren, onExtended_old] using hyl⟩, rfl⟩)).symm
    have hnnEq (u : b.Node) : rootUnfiredNN p b' (oldNode n u) = rootUnfiredNN p b u := by
      have h1 : rootUnfiredNN p b' (oldNode n u) ≤ rootUnfiredNN p b u :=
        missingCount_le _ (fun d _ h => (hnnIff u d).mpr h)
      have h2 : rootUnfiredNN p b u ≤ rootUnfiredNN p b' (oldNode n u) :=
        missingCount_le _ (fun d _ h => (hnnIff u d).mp h)
      omega
    have hsumEq : ((rootsAtLevel b' ℓ.val).map (rootUnfiredNN p b')).sum =
        ((rootsAtLevel b ℓ.val).map (rootUnfiredNN p b)).sum :=
      (sum_map_eq_of_bij (rootsAtLevel b ℓ.val) (rootsAtLevel b' ℓ.val)
        (nodup_rootsAtLevel _ _) (nodup_rootsAtLevel _ _) (oldNode n) _ _
        (fun a _ c _ h => oldNode_inj h)
        (fun u hu => by
          have ⟨hur, hul⟩ := mem_rootsAtLevel.mp hu
          exact mem_rootsAtLevel.mpr ⟨by simp [b', appendChildren, onExtended_old, hur],
            by simp [b', appendChildren, onExtended_old, hul]⟩)
        (fun y hy => by
          have ⟨hyr, hyl⟩ := mem_rootsAtLevel.mp hy
          obtain ⟨u, hur, rfl⟩ := hrootOld y hyr
          exact ⟨u, mem_rootsAtLevel.mpr ⟨hur, by simpa [b', appendChildren, onExtended_old] using hyl⟩, rfl⟩)
        (fun u _ => (hnnEq u).symm)).symm
    exact Prod.ext hlenEq hsumEq
  change SROIQMeasureLt rank p (rootMeasureVec rank p b', _) (rootMeasureVec rank p b, _)
  rw [hrootEq]
  apply Prod.Lex.right
  have hpotParts (z : b.Node) :
      missingCount (sroiqClos p) (fun d => d ∈ b'.labels (oldNode n z)) =
        missingCount (sroiqClos p) (fun d => d ∈ b.labels z) ∧
      missingCount (sroiqGuards rank p) (fun g => g ∈ b'.guardLabels (oldNode n z)) =
        missingCount (sroiqGuards rank p) (fun g => g ∈ b.guardLabels z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.down (oldNode n z)) =
        missingCount (sroiqRoleNames p) (fun s => s ∈ b.down z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.up (oldNode n z)) =
        missingCount (sroiqRoleNames p) (fun s => s ∈ b.up z) ∧
      missingCount (sroiqRoleNames p) (fun s => s ∈ b'.loops (oldNode n z)) =
        missingCount (sroiqRoleNames p) (fun s => s ∈ b.loops z) ∧
      missingCount (sroiqClos p) (fun d => b'.GenProtected (oldNode n z) d) ≤
        missingCount (sroiqClos p) (fun d => b.GenProtected z d) ∧
      missingCount (listProduct (sroiqRoleNames p) (rootsList b'))
        (fun q => (q.1, oldNode n z, q.2) ∈ b'.rootEdges) ≤
        missingCount (listProduct (sroiqRoleNames p) (rootsList b))
          (fun q => (q.1, z, q.2) ∈ b.rootEdges) ∧
      missingCount (listProduct (sroiqOrientedRoles p) (rootsList b'))
        (fun q => (q.1, q.2) ∈ b'.toRoot (oldNode n z)) ≤
        missingCount (listProduct (sroiqOrientedRoles p) (rootsList b))
          (fun q => (q.1, q.2) ∈ b.toRoot z) ∧
      nodeKeyPotential p b' (oldNode n z) ≤ nodeKeyPotential p b z := by
    refine ⟨by simp [b', appendChildren, onExtended_old],
      by simp [b', appendChildren, onExtended_old],
      by simp [b', appendChildren, onExtended_old],
      by simp [b', appendChildren, onExtended_old],
      by simp [b', appendChildren, onExtended_old], ?_, ?_, ?_, ?_⟩
    · apply missingCount_le; intro d _ hd
      cases d <;> first | exact appendChildren_protected_old hd | trivial
    · refine missingCount_le_of_bij (listProduct (sroiqRoleNames p) (rootsList b))
        (listProduct (sroiqRoleNames p) (rootsList b'))
        (nodup_product (nodup_sroiqRoleNames p) (nodup_rootsList b')) _ _
        (fun q => (q.1, oldNode n q.2)) ?_ ?_
      · intro ⟨rn, w⟩ hw
        obtain ⟨hrn, hwr⟩ := mem_listProduct.mp hw
        obtain ⟨u, hur, rfl⟩ := hrootOld w (mem_rootsList.mp hwr)
        exact ⟨(rn, u), mem_listProduct.mpr ⟨hrn, mem_rootsList.mpr hur⟩, rfl⟩
      · intro ⟨rn, u⟩ _ hm
        exact List.mem_map.mpr ⟨(rn, z, u), hm, rfl⟩
    · refine missingCount_le_of_bij (listProduct (sroiqOrientedRoles p) (rootsList b))
        (listProduct (sroiqOrientedRoles p) (rootsList b'))
        (nodup_product (nodup_sroiqOrientedRoles p) (nodup_rootsList b')) _ _
        (fun q => (q.1, oldNode n q.2)) ?_ ?_
      · intro ⟨rel, w⟩ hw
        obtain ⟨hrel, hwr⟩ := mem_listProduct.mp hw
        obtain ⟨u, hur, rfl⟩ := hrootOld w (mem_rootsList.mp hwr)
        exact ⟨(rel, u), mem_listProduct.mpr ⟨hrel, mem_rootsList.mpr hur⟩, rfl⟩
      · intro ⟨rel, u⟩ _ hm
        simp only [b', appendChildren, onExtended_old]
        exact List.mem_map.mpr ⟨(rel, u), hm, rfl⟩
    · refine missingCount_le_of_bij (listProduct (sroiqDataProps p) (rootsList b))
        (listProduct (sroiqDataProps p) (rootsList b'))
        (nodup_product (nodup_sroiqDataProps p) (nodup_rootsList b')) _ _
        (fun q => (q.1, oldNode n q.2)) ?_ ?_
      · intro ⟨dp, w⟩ hw
        obtain ⟨hdp, hwr⟩ := mem_listProduct.mp hw
        obtain ⟨u, hur, rfl⟩ := hrootOld w (mem_rootsList.mp hwr)
        exact ⟨(dp, u), mem_listProduct.mpr ⟨hdp, mem_rootsList.mpr hur⟩, rfl⟩
      · intro ⟨dp, u⟩ _ hm
        exact List.mem_map.mpr ⟨(z, u, dp), hm, rfl⟩
  have hpotLe (z : b.Node) : nodePotential rank p b' (oldNode n z) ≤ nodePotential rank p b z := by
    have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpotParts z
    exact nodePotential_le_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) (Nat.le_of_eq h3)
      (Nat.le_of_eq h4) (Nat.le_of_eq h5) h6 h7 h8 h9
  have hpotLt : nodePotential rank p b' (oldNode n x) < nodePotential rank p b x := by
    have ⟨h1, h2, h3, h4, h5, _, h7, h8, h9⟩ := hpotParts x
    have h6 : missingCount (sroiqClos p) (fun d => b'.GenProtected (oldNode n x) d) <
        missingCount (sroiqClos p) (fun d => b.GenProtected x d) := by
      rcases hgen with ⟨hsClos, rfl, hnoProt⟩ | ⟨hmClos, hnoProt⟩
      · exact missingCount_lt (sroiqClos p)
          (fun d _ hd => by cases d <;> first | exact appendChildren_protected_old hd | trivial)
          hsClos hnoProt (appendChildren_protected_new b 1 x r c)
      · exact missingCount_lt (sroiqClos p)
          (fun d _ hd => by cases d <;> first | exact appendChildren_protected_old hd | trivial)
          hmClos hnoProt (appendChildren_protected_new b n x r c)
    exact nodePotential_lt_of_parts (Nat.le_of_eq h1) (Nat.le_of_eq h2) (Nat.le_of_eq h3)
      (Nat.le_of_eq h4) (Nat.le_of_eq h5) (Nat.le_of_lt h6) h7 h8
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))) h9
  have hbijDepth (j : Nat) (hj : j ≤ b.depth x) :
      (nodesAtDepth b' j).length = (nodesAtDepth b j).length ∧
      ∀ y ∈ nodesAtDepth b' j, ∃ u ∈ nodesAtDepth b j, y = oldNode n u := by
    have hsurj : ∀ y ∈ nodesAtDepth b' j, ∃ u ∈ nodesAtDepth b j, y = oldNode n u := by
      intro y hy
      have hdy : b'.depth y = j := mem_nodesAtDepth.mp hy
      rcases extended_cases (b := b) y with ⟨u, rfl⟩ | ⟨k, rfl⟩
      · rw [appendChildren_depth_old] at hdy
        exact ⟨u, mem_nodesAtDepth.mpr hdy, rfl⟩
      · rw [appendChildren_depth_new] at hdy; omega
    refine ⟨?_, hsurj⟩
    exact (length_eq_of_bij (nodesAtDepth b j) (nodesAtDepth b' j)
      (nodup_nodesAtDepth _ _) (nodup_nodesAtDepth _ _) (oldNode n)
      (fun a _ c _ h => oldNode_inj h)
      (fun u hu => mem_nodesAtDepth.mpr ((appendChildren_depth_old u).trans (mem_nodesAtDepth.mp hu)))
      (fun y hy => by obtain ⟨u, hu, rfl⟩ := hsurj y hy; exact ⟨u, hu, rfl⟩)).symm
  let inv (y : b'.Node) : b.Node := if h : y.val < b.size + 1 then ⟨y.val, h⟩ else 0
  have hkx : b.depth x < sroiqMaxDepth rank p + 2 := by omega
  apply vecLex_of_prefix_le_lt ⟨b.depth x, hkx⟩
  · intro j hjlt
    have ⟨hlenEq, hsurj⟩ := hbijDepth j.val (Nat.le_of_lt hjlt)
    have hsumLe : levelPotential rank p b' j.val ≤ levelPotential rank p b j.val := by
      refine sum_map_le_of_inj _ _ (nodup_nodesAtDepth _ _) inv _ _ ?_ ?_ ?_
      · intro y hy y' hy' heq
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        obtain ⟨u', _, rfl⟩ := hsurj y' hy'
        have : u = u' := by simpa [inv, oldNode, u.isLt, u'.isLt] using heq
        exact congrArg (oldNode n) this
      · intro y hy
        obtain ⟨u, hu, rfl⟩ := hsurj y hy
        simpa [inv, oldNode, u.isLt] using hu
      · intro y hy
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        have hinv : inv (oldNode n u) = u := by simp [inv, oldNode, u.isLt]
        rw [hinv]; exact hpotLe u
    exact pairLex_or_eq_of_eq_le hlenEq hsumLe
  · have ⟨hlenEq, hsurj⟩ := hbijDepth (b.depth x) (Nat.le_refl _)
    have hsumLt : levelPotential rank p b' (b.depth x) < levelPotential rank p b (b.depth x) := by
      refine sum_map_lt_of_inj _ _ (nodup_nodesAtDepth _ _) inv _ _ ?_ ?_ ?_
        (a₀ := oldNode n x) (mem_nodesAtDepth.mpr (appendChildren_depth_old x)) ?_
      · intro y hy y' hy' heq
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        obtain ⟨u', _, rfl⟩ := hsurj y' hy'
        have : u = u' := by simpa [inv, oldNode, u.isLt, u'.isLt] using heq
        exact congrArg (oldNode n) this
      · intro y hy
        obtain ⟨u, hu, rfl⟩ := hsurj y hy
        simpa [inv, oldNode, u.isLt] using hu
      · intro y hy
        obtain ⟨u, _, rfl⟩ := hsurj y hy
        have hinv : inv (oldNode n u) = u := by simp [inv, oldNode, u.isLt]
        rw [hinv]; exact hpotLe u
      · have hinv : inv (oldNode n x) = x := by simp [inv, oldNode]
        rw [hinv]; exact hpotLt
    change PairLex (_, _) (_, _)
    rw [hlenEq]
    exact Prod.Lex.right _ hsumLt

private theorem SROIQStrictStep.measure_lt {rank : Rank} {p : Problem}
    {s t : SROIQState rank p} (hstep : SROIQStrictStep rank p s.forest t.forest) :
    SROIQMeasureLt rank p (sroiqMeasure rank p t.forest) (sroiqMeasure rank p s.forest) := by
  cases hstep with
  | rootMerge keep drop hd hk hvalid hdrop heq =>
    rw [heq]; exact measure_lt_rootMerge s.geom keep drop hd hk hvalid hdrop
  | nnExpand m r hr rel c n hmax hno hlvl heq =>
    rw [heq]; exact measure_lt_nnExpand m r hr rel c n hmax hno hlvl
  | addLabel x c hc hno heq =>
    rw [heq]; exact measure_lt_addLabel s.geom x c hc hno
  | addGuard x g hg hno heq =>
    rw [heq]; exact measure_lt_addGuard s.geom x g hg hno
  | addEdge r x y hr hadm hno heq =>
    rw [heq]; exact measure_lt_addEdge s.geom r x y hr hadm hno
  | addKeyDisjoint r₁ r₂ dp hr₁ hr₂ hdp hno heq =>
    rw [heq]; exact measure_lt_addKeyDisjoint s.geom r₁ r₂ dp hr₁ hr₂ hdp hno
  | blockableMerge keep drop hd hk hvalid hdrop hallowed heq =>
    rw [heq]; exact measure_lt_blockableMerge s.geom keep drop hd hk hvalid hdrop hallowed
  | generate n x r c hdepth _ _ hgen heq =>
    rw [heq]; exact measure_lt_generate n x r c hdepth hgen

/-! ### Unconditional well-foundedness and fuel-free `SROIQ(D)` decision procedure -/

theorem sroiqd_follows_wf {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    WellFounded (SROIQFollows hsroiqd) := by
  let measureFn (s : SROIQState rank p) := sroiqMeasure rank p s.forest
  have hwf : WellFounded (InvImage (SROIQMeasureLt rank p) measureFn) :=
    InvImage.wf measureFn (wellFounded_sroiqMeasureLt rank p)
  refine Subrelation.wf (r := InvImage (SROIQMeasureLt rank p) measureFn) ?_ hwf
  intro next s hfollow
  exact hfollow.strictStep.measure_lt

theorem sroiqd_initial_accessible {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    Acc (SROIQFollows hsroiqd) (SROIQState.initial rank p) :=
  (sroiqd_follows_wf hsroiqd).apply (SROIQState.initial rank p)

/-- Unconditional, fuel-free, kernel-verified decision procedure for full cyclic `SROIQ(D)`. -/
def decideSROIQD {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    SROIQVerdict (SROIQState.initial rank p) :=
  decideSROIQDAccessible hsroiqd (sroiqd_initial_accessible hsroiqd)

def decideSROIQDBool {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) : Bool :=
  match decideSROIQD hsroiqd with
  | .sat _ => true
  | .unsat _ => false

theorem decideSROIQD_sat_iff {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    (∃ leaf, decideSROIQD hsroiqd = .sat leaf) ↔ p.Sat :=
  decideSROIQDAccessible_sat_iff (sroiqd_initial_accessible hsroiqd)

theorem decideSROIQD_unsat_iff {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    (∃ ref, decideSROIQD hsroiqd = .unsat ref) ↔ ¬ p.Sat :=
  decideSROIQDAccessible_unsat_iff (sroiqd_initial_accessible hsroiqd)

theorem decideSROIQDBool_iff {rank : Rank} {p : Problem} (hsroiqd : p.isSROIQD rank = true) :
    decideSROIQDBool hsroiqd = true ↔ p.Sat := by
  unfold decideSROIQDBool
  cases h : decideSROIQD hsroiqd with
  | sat leaf => exact ⟨fun _ => (decideSROIQD_sat_iff hsroiqd).mp ⟨leaf, h⟩, fun _ => rfl⟩
  | unsat ref =>
    exact ⟨fun hc => Bool.noConfusion hc, fun hp => ((decideSROIQD_unsat_iff hsroiqd).mp ⟨ref, h⟩ hp).elim⟩

theorem decideSROIQD_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    ((∃ leaf, decideSROIQD hsroiqd = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideSROIQD hsroiqd = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) :=
  decideSROIQDAccessible_ontology_iff (sroiqd_initial_accessible hsroiqd) hnorm hroot

theorem decideSROIQDBool_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hsroiqd : p.isSROIQD rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    decideSROIQDBool hsroiqd = true ↔ Satisfiable datatypeMap o :=
  (decideSROIQDBool_iff hsroiqd).trans
    ((Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)).symm

/-- Check the source role hierarchy, then eliminate bottom properties before
running the decision procedure. `none` indicates an input outside the admitted fragment. -/
def decideAdmittedOntology? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    (Sabrina.RoleChains.findRank p.rules p.chains).bind fun rank =>
      if p.root = .top ∧ p.checkSimple = true then
        if h : p.lowerBottom.isSROIQD rank = true then some (decideSROIQDBool h) else none
      else none

theorem decideAdmittedOntology_iff {o : Ontology} {b : Bool}
    (h : decideAdmittedOntology? o = some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideAdmittedOntology?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := h
  split at hb
  · next hroot =>
    split at hb
    · next hadmit =>
      cases hb
      exact (decideSROIQDBool_iff hadmit).trans
        (p.lowerBottom_sat_iff.trans
          ((Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot.1)).symm)
    · contradiction
  · contradiction

theorem decideAdmittedOntology_unsat_iff {o : Ontology} {b : Bool}
    (h : decideAdmittedOntology? o = some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideAdmittedOntology_iff h]
  cases b <;> simp

theorem decideAdmittedOntology_isSome_iff {o : Ontology} :
    (decideAdmittedOntology? o).isSome = true ↔
      ∃ defs p rank, Normalize.normalizeWithDefs o = some (defs, p) ∧
        p.root = .top ∧ p.checkSimple = true ∧
        Sabrina.RoleChains.checkRegular rank p.rules p.chains = true ∧
        p.lowerBottom.isSROIQD rank = true := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    simp only [decideAdmittedOntology?, Option.bind_eq_some_iff] at hb
    obtain ⟨⟨defs, p⟩, hnorm, rank, hfound, hb⟩ := hb
    split at hb
    · next hroot =>
      split at hb
      · next hadmit =>
        exact ⟨defs, p, rank, hnorm, hroot.1, hroot.2,
          Sabrina.RoleChains.checkRegular_iff.mpr (Sabrina.RoleChains.findRank_sound hfound), hadmit⟩
      · contradiction
    · contradiction
  · rintro ⟨defs, p, rank, hnorm, hroot, hsimple, hregular, hadmit⟩
    have hrank := Sabrina.RoleChains.checkRegular_sound hregular
    obtain ⟨rank', hfound⟩ := Option.isSome_iff_exists.mp (Sabrina.RoleChains.findRank_complete hrank)
    have hchecked := Sabrina.RoleChains.checkRegular_iff.mpr
      (Sabrina.RoleChains.findRank_sound hfound)
    have hadmit' : p.lowerBottom.isSROIQD rank' = true := by
      simp only [Problem.isSROIQD, Bool.and_eq_true] at hadmit ⊢
      exact ⟨hadmit.1, p.checkRegular_lowerBottom hchecked⟩
    simp [decideAdmittedOntology?, hnorm, hfound, hroot, hsimple, hadmit']

/-! ### Object-only `SROIQ` specializations -/

theorem sroiq_follows_wf {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    WellFounded (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) :=
  sroiqd_follows_wf (p.isSROIQ_implies_isSROIQD hsroiq)

theorem sroiq_initial_accessible {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    Acc (SROIQFollows (p.isSROIQ_implies_isSROIQD hsroiq)) (SROIQState.initial rank p) :=
  sroiqd_initial_accessible (p.isSROIQ_implies_isSROIQD hsroiq)

/-- Unconditional, fuel-free, kernel-verified decision procedure for full cyclic `SROIQ`. -/
def decideSROIQ {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    SROIQVerdict (SROIQState.initial rank p) :=
  decideSROIQD (p.isSROIQ_implies_isSROIQD hsroiq)

def decideSROIQBool {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) : Bool :=
  decideSROIQDBool (p.isSROIQ_implies_isSROIQD hsroiq)

theorem decideSROIQ_sat_iff {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    (∃ leaf, decideSROIQ hsroiq = .sat leaf) ↔ p.Sat :=
  decideSROIQD_sat_iff (p.isSROIQ_implies_isSROIQD hsroiq)

theorem decideSROIQ_unsat_iff {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    (∃ ref, decideSROIQ hsroiq = .unsat ref) ↔ ¬ p.Sat :=
  decideSROIQD_unsat_iff (p.isSROIQ_implies_isSROIQD hsroiq)

theorem decideSROIQBool_iff {rank : Rank} {p : Problem} (hsroiq : p.isSROIQ rank = true) :
    decideSROIQBool hsroiq = true ↔ p.Sat :=
  decideSROIQDBool_iff (p.isSROIQ_implies_isSROIQD hsroiq)

theorem decideSROIQ_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hsroiq : p.isSROIQ rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    ((∃ leaf, decideSROIQ hsroiq = .sat leaf) ↔ Satisfiable datatypeMap o) ∧
    ((∃ ref, decideSROIQ hsroiq = .unsat ref) ↔ ¬ Satisfiable datatypeMap o) :=
  decideSROIQD_ontology_iff (p.isSROIQ_implies_isSROIQD hsroiq) hnorm hroot

theorem decideSROIQBool_ontology_iff {rank : Rank} {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hsroiq : p.isSROIQ rank = true)
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top) :
    decideSROIQBool hsroiq = true ↔ Satisfiable datatypeMap o :=
  decideSROIQDBool_ontology_iff (p.isSROIQ_implies_isSROIQD hsroiq) hnorm hroot

#print axioms sroiqd_follows_wf
#print axioms sroiqd_initial_accessible
#print axioms decideSROIQD_sat_iff
#print axioms decideSROIQD_unsat_iff
#print axioms decideSROIQDBool_iff
#print axioms decideSROIQD_ontology_iff
#print axioms decideSROIQDBool_ontology_iff
#print axioms decideAdmittedOntology_iff
#print axioms decideAdmittedOntology_unsat_iff
#print axioms decideAdmittedOntology_isSome_iff
#print axioms sroiq_follows_wf
#print axioms sroiq_initial_accessible
#print axioms decideSROIQ_sat_iff
#print axioms decideSROIQ_unsat_iff
#print axioms decideSROIQBool_iff
#print axioms decideSROIQ_ontology_iff
#print axioms decideSROIQBool_ontology_iff

/-! ### Live fuel-free `SROIQ` regressions (zero fuel, zero traces) -/

section Regressions

private def sroiqRank : Rank := fun _ => 0

-- 1. Cyclic SRIQ infinite-chain problem (satisfiable with blocking)
private def regRole : IRI := "urn:sroiq:r"
private def regRole2 : IRI := "urn:sroiq:s"
private def regClsA : IRI := "urn:sroiq:A"
private def regClsB : IRI := "urn:sroiq:B"
private def regInd1 : Individual := .named "urn:sroiq:a"
private def regInd2 : Individual := .named "urn:sroiq:b"
private def regInd3 : Individual := .named "urn:sroiq:c"

private def cyclicInfProblem : Problem :=
  { tbox := [⟨.top, .some (regRole, false) .top⟩,
             ⟨.top, .max 1 (regRole, true) .top⟩]
    root := .max 0 (regRole, true) .top }

private theorem cyclicInf_admitted : cyclicInfProblem.isSROIQ sroiqRank = true := by decide

#guard decideSROIQBool cyclicInf_admitted == true

-- 2. Nominal + ABox + role chain + NegativeObjectPropertyAssertion contradiction
private def nomChainUnsat : Problem :=
  { chains := [Sabrina.RoleChains.Chain.named [regRole, regRole] regRole2]
    objAssertions := [(regRole, regInd1, regInd2), (regRole, regInd2, regInd3)]
    negObjAssertions := [(regRole2, regInd1, regInd3)]
    root := .top }

private def chainRank : Rank := fun r => if r == regRole2 then 1 else 0

private theorem nomChainUnsat_admitted : nomChainUnsat.isSROIQ chainRank = true := by decide

#guard decideSROIQBool nomChainUnsat_admitted == false

-- 3. `HasKey` across a composite role chain forcing a nominal merge that clashes with `diffInds`
private def hasKeyChainUnsat : Problem :=
  { chains := [Sabrina.RoleChains.Chain.named [regRole, regRole] regRole2]
    keys := [⟨.lit regClsA true, [(regRole2, false)], []⟩]
    classAssertions := [(regInd1, .lit regClsA true), (regInd2, .lit regClsA true)]
    objAssertions := [(regRole, regInd1, regInd3), (regRole, regInd2, regInd3), (regRole, regInd3, regInd3)]
    diffInds := [(regInd1, regInd2)]
    root := .top }

private theorem hasKeyChainUnsat_admitted : hasKeyChainUnsat.isSROIQ chainRank = true := by decide

#guard decideSROIQBool hasKeyChainUnsat_admitted == false

-- 4. NN-rule regression: nominal `a` has `≤ 1 r⁻.A`, blockable `x` has `A` and `r`-edge to `{a}`,
--    forcing NN-rule expansion of `{a}` + merge of `x` into the NN nominal;
--    with a second distinct `A` pointing to `{a}` and `B` vs `¬B`, yields UNSAT!
private def nnRuleUnsat : Problem :=
  { classAssertions := [(regInd1, .max 1 (regRole, true) (.lit regClsA true))]
    root := .conj (.some (regRole, false) (.conj (.lit regClsA true) (.conj (.lit regClsB true) (.some (regRole, false) (.nom regInd1 true)))))
                  (.some (regRole, false) (.conj (.lit regClsA true) (.conj (.lit regClsB false) (.some (regRole, false) (.nom regInd1 true))))) }

private theorem nnRuleUnsat_admitted : nnRuleUnsat.isSROIQ sroiqRank = true := by decide

#guard decideSROIQBool nnRuleUnsat_admitted == false

-- 5. NN-rule satisfiable regression: nominal `a` has `≤ 1 r⁻.A` and two compatible `A`-predecessors merge cleanly
private def nnRuleSat : Problem :=
  { classAssertions := [(regInd1, .max 1 (regRole, true) (.lit regClsA true))]
    root := .conj (.some (regRole, false) (.conj (.lit regClsA true) (.some (regRole, false) (.nom regInd1 true))))
                  (.some (regRole, false) (.conj (.lit regClsA true) (.some (regRole, false) (.nom regInd1 true)))) }

private theorem nnRuleSat_admitted : nnRuleSat.isSROIQ sroiqRank = true := by decide

#guard decideSROIQBool nnRuleSat_admitted == true

-- 6. End-to-end OWL 2 Direct Semantics source `Ontology` normalized through
--    `Normalize.normalizeWithDefs` (combining role chain, HasKey, ABox, DifferentIndividuals)
private def regOntology : Ontology :=
  [.subObjectPropertyChain [.named regRole, .named regRole] (.named regRole2),
   .hasKey (.named regClsA) [.named regRole2] [],
   .classAssertion (.named regClsA) regInd1,
   .classAssertion (.named regClsA) regInd2,
   .objectAssertion (.named regRole) regInd1 regInd3,
   .objectAssertion (.named regRole) regInd2 regInd3,
   .objectAssertion (.named regRole) regInd3 regInd3,
   .differentIndividuals [regInd1, regInd2]]

private def decideRegOntology? (_ : Unit) : Option Bool :=
  match Sabrina.OWL2.Normalize.normalizeWithDefs regOntology with
  | some (_, p) =>
    if h : p.isSROIQ chainRank = true then some (decideSROIQBool h) else none
  | none => none

#guard decideRegOntology? () == some false

-- 7. Concrete datatype `xsd:integer` order-facet interval difference:
--    `[10, 11] \ {10}` has cardinality 1, so `dataMin 2` is UNSAT whereas `dataMin 1` is SAT!
private def regDataProp : IRI := "urn:sroiq:dp"
private def regDataProp2 : IRI := "urn:sroiq:dp2"

private def intLit (s : String) : Literal := ⟨s, Sabrina.OWL2.Datatypes.xsd "integer"⟩

private def range10to11 : DataRange :=
  .restriction (Sabrina.OWL2.Datatypes.xsd "integer")
    [⟨Sabrina.OWL2.Datatypes.xsd "minInclusive", intLit "10"⟩,
     ⟨Sabrina.OWL2.Datatypes.xsd "maxInclusive", intLit "11"⟩]

private def intIntervalUnsat : Problem :=
  { root := .conj (.dataMin 2 regDataProp range10to11)
                  (.dataValue regDataProp (intLit "10") false) }

private theorem intIntervalUnsat_admitted : intIntervalUnsat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool intIntervalUnsat_admitted == false

private def intIntervalSat : Problem :=
  { root := .conj (.dataMin 1 regDataProp range10to11)
                  (.dataValue regDataProp (intLit "10") false) }

private theorem intIntervalSat_admitted : intIntervalSat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool intIntervalSat_admitted == true

-- 8. Concrete datatype `xsd:boolean` pigeonhole (`dataMin 3` UNSAT, `dataMin 2` SAT)
private def boolRange : DataRange := .datatype (Sabrina.OWL2.Datatypes.xsd "boolean")

private def boolPigeonholeUnsat : Problem :=
  { root := .dataMin 3 regDataProp boolRange }

private theorem boolPigeonholeUnsat_admitted : boolPigeonholeUnsat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool boolPigeonholeUnsat_admitted == false

private def boolPigeonholeSat : Problem :=
  { root := .dataMin 2 regDataProp boolRange }

private theorem boolPigeonholeSat_admitted : boolPigeonholeSat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool boolPigeonholeSat_admitted == true

-- 9. Global data axioms (`subData`, `disjointData`, `funcData`, `dataRanges`) + ABox data assertions
private def dataAxiomsUnsat : Problem :=
  { subData := [(regDataProp, regDataProp2)]
    funcData := [regDataProp2]
    dataRanges := [(regDataProp2, range10to11)]
    dataAssertions := [(regDataProp, regInd1, intLit "10"), (regDataProp2, regInd1, intLit "11")]
    root := .top }

private theorem dataAxiomsUnsat_admitted : dataAxiomsUnsat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool dataAxiomsUnsat_admitted == false

-- 10. Mixed object + data `HasKey` (`k.objProps = [regRole]` and `k.dataProps = [regDataProp]`):
--     Two distinct individuals `a, b ∈ A` sharing object neighbor `c` AND integer literal `"42"`
--     must merge by `HasKey`, clashing with `diffInds`!
private def mixedHasKeyUnsat : Problem :=
  { keys := [⟨.lit regClsA true, [(regRole, false)], [regDataProp]⟩]
    classAssertions := [(regInd1, .lit regClsA true), (regInd2, .lit regClsA true)]
    objAssertions := [(regRole, regInd1, regInd3), (regRole, regInd2, regInd3)]
    dataAssertions := [(regDataProp, regInd1, intLit "42"), (regDataProp, regInd2, intLit "42")]
    diffInds := [(regInd1, regInd2)]
    root := .top }

private theorem mixedHasKeyUnsat_admitted : mixedHasKeyUnsat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool mixedHasKeyUnsat_admitted == false

private def mixedHasKeySat : Problem :=
  { keys := [⟨.lit regClsA true, [(regRole, false)], [regDataProp]⟩]
    classAssertions := [(regInd1, .lit regClsA true), (regInd2, .lit regClsA true)]
    objAssertions := [(regRole, regInd1, regInd3), (regRole, regInd2, regInd3)]
    dataAssertions := [(regDataProp, regInd1, intLit "42"), (regDataProp, regInd2, intLit "43")]
    diffInds := [(regInd1, regInd2)]
    root := .top }

private theorem mixedHasKeySat_admitted : mixedHasKeySat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool mixedHasKeySat_admitted == true

-- 11. Finite-domain datatype pigeonhole `HasKey`:
--     `HasKey(A, (), (dp))` across 3 pairwise distinct individuals `a, b, c ∈ A` where each has
--     `∃dp.xsd:boolean` (without any explicit literal!). By pigeonhole over `{true, false}`, two
--     of `a, b, c` must share a boolean `dp`-value and merge by `HasKey`, clashing with `diffInds`!
private def boolHasKeyPigeonholeUnsat : Problem :=
  { keys := [⟨.lit regClsA true, [], [regDataProp]⟩]
    classAssertions :=
      [(regInd1, .conj (.lit regClsA true) (.dataSome regDataProp boolRange)),
       (regInd2, .conj (.lit regClsA true) (.dataSome regDataProp boolRange)),
       (regInd3, .conj (.lit regClsA true) (.dataSome regDataProp boolRange))]
    diffInds := [(regInd1, regInd2), (regInd1, regInd3), (regInd2, regInd3)]
    root := .top }

private theorem boolHasKeyPigeonholeUnsat_admitted :
    boolHasKeyPigeonholeUnsat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool boolHasKeyPigeonholeUnsat_admitted == false

private def boolHasKeyPigeonholeSat : Problem :=
  { keys := [⟨.lit regClsA true, [], [regDataProp]⟩]
    classAssertions :=
      [(regInd1, .conj (.lit regClsA true) (.dataSome regDataProp boolRange)),
       (regInd2, .conj (.lit regClsA true) (.dataSome regDataProp boolRange))]
    diffInds := [(regInd1, regInd2)]
    root := .top }

private theorem boolHasKeyPigeonholeSat_admitted :
    boolHasKeyPigeonholeSat.isSROIQD sroiqRank = true := by decide

#guard decideSROIQDBool boolHasKeyPigeonholeSat_admitted == true

-- 12. End-to-end OWL 2 Direct Semantics `Ontology` with concrete datatypes and mixed `HasKey`
--     normalized through `Normalize.normalizeWithDefs`
private def regDataOntology : Ontology :=
  [.subObjectPropertyChain [.named regRole, .named regRole] (.named regRole2),
   .hasKey (.named regClsA) [.named regRole2] [regDataProp],
   .classAssertion (.named regClsA) regInd1,
   .classAssertion (.named regClsA) regInd2,
   .objectAssertion (.named regRole) regInd1 regInd3,
   .objectAssertion (.named regRole) regInd2 regInd3,
   .objectAssertion (.named regRole) regInd3 regInd3,
   .dataAssertion regDataProp regInd1 (intLit "42"),
   .dataAssertion regDataProp regInd2 (intLit "42"),
   .differentIndividuals [regInd1, regInd2]]

private def decideRegDataOntology? (_ : Unit) : Option Bool :=
  match Sabrina.OWL2.Normalize.normalizeWithDefs regDataOntology with
  | some (_, p) =>
    if h : p.isSROIQD chainRank = true then some (decideSROIQDBool h) else none
  | none => none

#guard decideRegDataOntology? () == some false

private def decideOFNRegression (text : String) : Except String Bool := do
  let doc ← FunctionalSyntax.parseDocument text
  let some verdict := decideAdmittedOntology? doc.ontology
    | throw "outside the verified fragment"
  return verdict

private def verdictIs (result : Except String Bool) (expected : Bool) : Bool :=
  match result with
  | .ok b => b == expected
  | .error _ => false

private def w3cDateTimeFunctionality : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(ex:birthDate))
  Declaration(NamedIndividual(ex:Peter))
  FunctionalDataProperty(ex:birthDate)
  DataPropertyAssertion(ex:birthDate ex:Peter \"1956-06-25T04:00:00-05:00\"^^xsd:dateTime)
  DataPropertyAssertion(ex:birthDate ex:Peter \"1956-06-25T10:00:00+01:00\"^^xsd:dateTime)
)"

#guard verdictIs (decideOFNRegression w3cDateTimeFunctionality) false

private def floatFunctionality : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(ex:reading))
  Declaration(NamedIndividual(ex:a))
  FunctionalDataProperty(ex:reading)
  DataPropertyAssertion(ex:reading ex:a \"0.1\"^^xsd:float)
  DataPropertyAssertion(ex:reading ex:a \"0.100000001490116119384765625\"^^xsd:float)
)"

#guard verdictIs (decideOFNRegression floatFunctionality) true

private def inverseKeyOntology (first second : String) : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(Class(ex:Person))
  Declaration(ObjectProperty(ex:identifies))
  Declaration(NamedIndividual(ex:a))
  Declaration(NamedIndividual(ex:b))
  Declaration(NamedIndividual(ex:key))
  HasKey(ex:Person (ObjectInverseOf(ex:identifies)) ())
  ClassAssertion(ex:Person ex:a)
  ClassAssertion(ex:Person ex:b)
  DifferentIndividuals(ex:a ex:b)
" ++ first ++ "\n" ++ second ++ "\n)"

#guard verdictIs (decideOFNRegression (inverseKeyOntology
  "ObjectPropertyAssertion(ex:identifies ex:key ex:a)"
  "ObjectPropertyAssertion(ex:identifies ex:key ex:b)")) false

#guard verdictIs (decideOFNRegression (inverseKeyOntology
  "ObjectPropertyAssertion(ex:identifies ex:a ex:key)"
  "ObjectPropertyAssertion(ex:identifies ex:b ex:key)")) true

private def stringLengthZero (count : Nat) : String := s!"
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(ex:label))
  Declaration(NamedIndividual(ex:a))
  ClassAssertion(DataMinCardinality({count} ex:label
    DatatypeRestriction(xsd:string xsd:length \"0\"^^xsd:integer)) ex:a)
)"

#guard verdictIs (decideOFNRegression (stringLengthZero 1)) true
#guard verdictIs (decideOFNRegression (stringLengthZero 2)) false

private def emptyDecimalRange : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(ex:reading))
  Declaration(NamedIndividual(ex:a))
  DataPropertyRange(ex:reading DatatypeRestriction(xsd:decimal
    xsd:minInclusive \"0.25\"^^xsd:decimal xsd:maxExclusive \"0.25\"^^xsd:decimal))
  DataPropertyAssertion(ex:reading ex:a \"0.25\"^^xsd:decimal)
)"

#guard verdictIs (decideOFNRegression emptyDecimalRange) false

private def fractionalIntegerBounds (upper : String) : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(DataProperty(ex:reading))
  Declaration(NamedIndividual(ex:a))
  ClassAssertion(DataSomeValuesFrom(ex:reading DatatypeRestriction(xsd:integer
    xsd:minExclusive \"-1.5\"^^xsd:decimal xsd:maxExclusive \"" ++ upper ++
    "\"^^xsd:decimal)) ex:a)
)"

#guard verdictIs (decideOFNRegression (fractionalIntegerBounds "-0.5")) true
#guard verdictIs (decideOFNRegression (fractionalIntegerBounds "-1.0")) false

private def inverseChainOntology (inputEdge head witness : String) : String := "
Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(ObjectProperty(ex:r))
  Declaration(ObjectProperty(ex:s))
  Declaration(ObjectProperty(ex:t))
  Declaration(NamedIndividual(ex:a))
  Declaration(NamedIndividual(ex:b))
  Declaration(NamedIndividual(ex:c))
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(ex:r) ex:s) " ++ head ++ ")
  " ++ inputEdge ++ "
  ObjectPropertyAssertion(ex:s ex:b ex:c)
  " ++ witness ++ "
)"

#guard verdictIs (decideOFNRegression (inverseChainOntology
  "ObjectPropertyAssertion(ex:r ex:b ex:a)" "ex:t"
  "NegativeObjectPropertyAssertion(ex:t ex:a ex:c)")) false
#guard verdictIs (decideOFNRegression (inverseChainOntology
  "ObjectPropertyAssertion(ex:r ex:a ex:b)" "ex:t"
  "NegativeObjectPropertyAssertion(ex:t ex:a ex:c)")) true
#guard verdictIs (decideOFNRegression (inverseChainOntology
  "ObjectPropertyAssertion(ex:r ex:b ex:a)" "ObjectInverseOf(ex:t)"
  "NegativeObjectPropertyAssertion(ex:t ex:c ex:a)")) false
#guard verdictIs (decideOFNRegression (inverseChainOntology
  "ObjectPropertyAssertion(ex:r ex:b ex:a)" "ObjectInverseOf(ex:t)"
  "NegativeObjectPropertyAssertion(ex:t ex:a ex:c)")) true

private def bottomPropertiesOFN (axioms : String) : String :=
  "Prefix(ex:=<http://example.org/>)
Ontology(
  Declaration(Class(ex:Person))
  Declaration(ObjectProperty(ex:r))
  Declaration(ObjectProperty(ex:s))
  Declaration(DataProperty(ex:value))
  Declaration(NamedIndividual(ex:a))
  Declaration(NamedIndividual(ex:b))
  " ++ axioms ++ "
)"

private def decideBottomProperties (axioms : String) : Except String Bool :=
  decideOFNRegression (bottomPropertiesOFN axioms)

#guard verdictIs (decideBottomProperties "
  ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(owl:bottomObjectProperty) owl:Nothing) ex:a)
  NegativeObjectPropertyAssertion(owl:bottomObjectProperty ex:a ex:b)") true
#guard verdictIs (decideBottomProperties "
  ClassAssertion(ObjectSomeValuesFrom(ObjectInverseOf(owl:bottomObjectProperty) owl:Thing) ex:a)") false
#guard verdictIs (decideBottomProperties "
  ObjectPropertyAssertion(owl:bottomObjectProperty ex:a ex:b)") false
#guard verdictIs (decideBottomProperties "
  ReflexiveObjectProperty(owl:bottomObjectProperty)") false

#guard verdictIs (decideBottomProperties "
  SubObjectPropertyOf(ObjectPropertyChain(owl:bottomObjectProperty ex:s) ex:r)
  ObjectPropertyAssertion(ex:s ex:a ex:b)
  NegativeObjectPropertyAssertion(ex:r ex:a ex:b)") true
#guard verdictIs (decideBottomProperties "
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(ex:r) ex:s) owl:bottomObjectProperty)
  ObjectPropertyAssertion(ex:r ex:b ex:a)
  ObjectPropertyAssertion(ex:s ex:b ex:a)") false
#guard verdictIs (decideBottomProperties "
  SubObjectPropertyOf(ex:r owl:bottomObjectProperty)
  ObjectPropertyAssertion(ex:r ex:a ex:b)") false

#guard verdictIs (decideBottomProperties "
  ClassAssertion(DataExactCardinality(0 owl:bottomDataProperty rdfs:Literal) ex:a)
  NegativeDataPropertyAssertion(owl:bottomDataProperty ex:a \"true\"^^xsd:boolean)") true
#guard verdictIs (decideBottomProperties "
  ClassAssertion(DataMinCardinality(1 owl:bottomDataProperty rdfs:Literal) ex:a)") false
#guard verdictIs (decideBottomProperties "
  SubDataPropertyOf(ex:value owl:bottomDataProperty)
  DataPropertyAssertion(ex:value ex:a \"true\"^^xsd:boolean)") false
#guard verdictIs (decideBottomProperties "
  HasKey(ex:Person (owl:bottomObjectProperty) (owl:bottomDataProperty))
  ClassAssertion(ex:Person ex:a)
  ClassAssertion(ex:Person ex:b)
  DifferentIndividuals(ex:a ex:b)") true

-- The chain is vacuous semantically, but it still makes its head non-simple.
#guard (decideBottomProperties "
  SubObjectPropertyOf(ObjectPropertyChain(owl:bottomObjectProperty ex:s) ex:r)
  FunctionalObjectProperty(ex:r)").isOk == false

-- A semantically vacuous recursive chain still needs a source rank.
#guard (decideBottomProperties "
  SubObjectPropertyOf(ObjectPropertyChain(ex:r ex:r owl:bottomObjectProperty) ex:r)").isOk == false

end Regressions

end BlockedForest
end Termination
end Sabrina.OWL2.SROIQD
