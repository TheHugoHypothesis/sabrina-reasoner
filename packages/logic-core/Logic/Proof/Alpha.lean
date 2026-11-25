import Logic.FOL.Alpha
import Logic.Proof.Derivation

/-! Alpha conversion is admissible in the original calculus. The proof is
syntactic induction on formula depth, using only the existing inference rules. -/
namespace Logic.Proof
open Logic.FOL

private theorem alpha_derives_depth [DecidableEq V] [Fresh V]
    (n : Nat) (a b : Formula R F V) (hn : a.depth ≤ n) (h : a.Alpha b)
    (Γ : List (Formula R F V)) : Derives Γ a ↔ Derives Γ b := by
  induction n generalizing a b Γ with
  | zero => cases a <;> simp [Formula.depth] at hn
  | succ n ih =>
    cases a <;> cases b <;> try (solve | have h0 := h Term.var; cases h0)
    case tr.tr => rfl
    case fls.fls => rfl
    case eql.eql a b c d =>
      have h0 := h Term.var
      simp only [Formula.bindingTree, Term.expand_var, BindingTree.eql.injEq] at h0
      rcases h0 with ⟨rfl, rfl⟩
      rfl
    case rel.rel r ts s us =>
      have h0 := h Term.var
      simp only [Formula.bindingTree, expandTerms_var, BindingTree.rel.injEq] at h0
      rcases h0 with ⟨rfl, rfl⟩
      rfl
    case conj.conj a b c d =>
      have ha : a.Alpha c := fun σ => (BindingTree.conj.inj (h σ)).1
      have hb : b.Alpha d := fun σ => (BindingTree.conj.inj (h σ)).2
      have hn' : max a.depth b.depth ≤ n := Nat.le_of_succ_le_succ hn
      have ia := fun Δ => ih a c (Nat.le_trans (Nat.le_max_left _ _) hn') ha Δ
      have ib := fun Δ => ih b d (Nat.le_trans (Nat.le_max_right _ _) hn') hb Δ
      exact ⟨fun p => .andIntro ((ia Γ).mp (.andLeft p)) ((ib Γ).mp (.andRight p)),
        fun p => .andIntro ((ia Γ).mpr (.andLeft p)) ((ib Γ).mpr (.andRight p))⟩
    case disj.disj a b c d =>
      have ha : a.Alpha c := fun σ => (BindingTree.disj.inj (h σ)).1
      have hb : b.Alpha d := fun σ => (BindingTree.disj.inj (h σ)).2
      have hn' : max a.depth b.depth ≤ n := Nat.le_of_succ_le_succ hn
      have ia := fun Δ => ih a c (Nat.le_trans (Nat.le_max_left _ _) hn') ha Δ
      have ib := fun Δ => ih b d (Nat.le_trans (Nat.le_max_right _ _) hn') hb Δ
      constructor
      · intro p
        exact .orElim p (.orLeft ((ia _).mp (.assumption List.mem_cons_self)))
          (.orRight ((ib _).mp (.assumption List.mem_cons_self)))
      · intro p
        exact .orElim p (.orLeft ((ia _).mpr (.assumption List.mem_cons_self)))
          (.orRight ((ib _).mpr (.assumption List.mem_cons_self)))
    case impl.impl a b c d =>
      have ha : a.Alpha c := fun σ => (BindingTree.impl.inj (h σ)).1
      have hb : b.Alpha d := fun σ => (BindingTree.impl.inj (h σ)).2
      have hn' : max a.depth b.depth ≤ n := Nat.le_of_succ_le_succ hn
      have ia := fun Δ => ih a c (Nat.le_trans (Nat.le_max_left _ _) hn') ha Δ
      have ib := fun Δ => ih b d (Nat.le_trans (Nat.le_max_right _ _) hn') hb Δ
      constructor
      · intro p
        exact .impIntro ((ib _).mp (.impElim (weaken_cons c p)
          ((ia _).mpr (.assumption List.mem_cons_self))))
      · intro p
        exact .impIntro ((ib _).mpr (.impElim (weaken_cons a p)
          ((ia _).mp (.assumption List.mem_cons_self))))
    case iffT.iffT a b c d =>
      have ha : a.Alpha c := fun σ => (BindingTree.iffT.inj (h σ)).1
      have hb : b.Alpha d := fun σ => (BindingTree.iffT.inj (h σ)).2
      have hn' : max a.depth b.depth ≤ n := Nat.le_of_succ_le_succ hn
      have ia := fun Δ => ih a c (Nat.le_trans (Nat.le_max_left _ _) hn') ha Δ
      have ib := fun Δ => ih b d (Nat.le_trans (Nat.le_max_right _ _) hn') hb Δ
      constructor
      · intro p
        exact .iffIntro
          ((ib _).mp (.iffLeft (weaken_cons c p) ((ia _).mpr (.assumption List.mem_cons_self))))
          ((ia _).mp (.iffRight (weaken_cons d p) ((ib _).mpr (.assumption List.mem_cons_self))))
      · intro p
        exact .iffIntro
          ((ib _).mpr (.iffLeft (weaken_cons a p) ((ia _).mp (.assumption List.mem_cons_self))))
          ((ia _).mpr (.iffRight (weaken_cons b p) ((ib _).mp (.assumption List.mem_cons_self))))
    case neg.neg a b =>
      have hab : a.Alpha b := fun σ => BindingTree.neg.inj (h σ)
      have hn' : a.depth ≤ n := Nat.le_of_succ_le_succ hn
      constructor
      · intro p
        exact .negIntro (.negElim (weaken_cons b p)
          ((ih a b hn' hab _).mpr (.assumption List.mem_cons_self)))
      · intro p
        exact .negIntro (.negElim (weaken_cons a p)
          ((ih a b hn' hab _).mp (.assumption List.mem_cons_self)))
    case allv.allv x a y b =>
      have hab (t : Term F V) : (a.subst x t).Alpha (b.subst y t) := by
        intro σ
        simp only [Formula.bindingTree_subst]
        exact congrFun (BindingTree.allv.inj (h σ)) (t.expand σ)
      have hn' (t : Term F V) : (a.subst x t).depth ≤ n := by
        rw [Formula.subst_depth]; exact Nat.le_of_succ_le_succ hn
      constructor
      · intro p
        exact .allIntro fun z _ _ => (ih _ _ (hn' (.var z)) (hab (.var z)) Γ).mp (.allElim (.var z) p)
      · intro p
        exact .allIntro fun z _ _ => (ih _ _ (hn' (.var z)) (hab (.var z)) Γ).mpr (.allElim (.var z) p)
    case exv.exv x a y b =>
      have hab (t : Term F V) : (a.subst x t).Alpha (b.subst y t) := by
        intro σ
        simp only [Formula.bindingTree_subst]
        exact congrFun (BindingTree.exv.inj (h σ)) (t.expand σ)
      have hn' (t : Term F V) : (a.subst x t).depth ≤ n := by
        rw [Formula.subst_depth]; exact Nat.le_of_succ_le_succ hn
      constructor
      · intro p
        exact .existsElim p fun z _ _ _ => .existsIntro (.var z)
          ((ih _ _ (hn' (.var z)) (hab (.var z)) _).mp (.assumption List.mem_cons_self))
      · intro p
        exact .existsElim p fun z _ _ _ => .existsIntro (.var z)
          ((ih _ _ (hn' (.var z)) (hab (.var z)) _).mpr (.assumption List.mem_cons_self))

/-- Alpha-equivalent formulas are interderivable in every context. -/
theorem alpha_derives [DecidableEq V] [Fresh V]
    {a b : Formula R F V} (h : a.Alpha b) (Γ : List (Formula R F V)) :
    Derives Γ a ↔ Derives Γ b := alpha_derives_depth a.depth a b (Nat.le_refl _) h Γ

end Logic.Proof
