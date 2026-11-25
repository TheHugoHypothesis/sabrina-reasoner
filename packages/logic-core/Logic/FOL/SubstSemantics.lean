import Logic.FOL.Models
import Logic.FOL.Subst

/-! Semantic substitution for terms and quantifier-free formulas. The general
formula theorem, including alpha-renaming, is in `Logic.FOL.SubstFull`. -/
namespace Logic.FOL

mutual
/-- Evaluating a substituted term agrees with updating the assignment. -/
theorem Term.eval_subst [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    (x : V) (replacement : Term F V) (t : Term F V) :
    (Term.subst x replacement t).eval s σ =
      t.eval s (fun y => if y = x then replacement.eval s σ else σ y) := by
  cases t with
  | var y =>
    by_cases h : y = x <;> simp [Term.subst, Term.subst', Term.eval, h]
  | app f args =>
    simp only [Term.subst, Term.subst', Term.eval]
    rw [eval_subst_list s σ x replacement args]

/-- List companion used for function arguments. -/
theorem eval_subst_list [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    (x : V) (replacement : Term F V) (ts : List (Term F V)) :
    (subst'List (x, replacement) ts).map (Term.eval s σ) =
      ts.map (Term.eval s (fun y => if y = x then replacement.eval s σ else σ y)) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [subst'List, List.map_cons]
    change Term.eval s σ (Term.subst x replacement t) :: _ = _
    rw [Term.eval_subst s σ x replacement t,
        eval_subst_list s σ x replacement ts]
end

/-- Alpha-renaming does not change the depth used to bound substitution fuel. -/
theorem Formula.rename_depth [DecidableEq V] (y z : V) (φ : Formula R F V) :
    (φ.rename y z).depth = φ.depth := by
  induction φ with
  | tr | fls | eql | rel => rfl
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | impl _ _ ih₁ ih₂ | iffT _ _ ih₁ ih₂ =>
      simp [Formula.rename, Formula.depth, ih₁, ih₂]
  | neg _ ih => simp [Formula.rename, Formula.depth, ih]
  | allv w b ih | exv w b ih =>
      simp only [Formula.rename, Formula.depth]
      split <;> simp_all

/-- Whether a formula contains no quantifiers. -/
def Formula.quantifierFree : Formula R F V → Bool
  | .tr | .fls | .eql .. | .rel .. => true
  | .conj a b | .disj a b | .impl a b | .iffT a b =>
      a.quantifierFree && b.quantifierFree
  | .neg a => a.quantifierFree
  | .allv .. | .exv .. => false

/-- Semantic substitution for quantifier-free formulas. The fuel bound is
explicit so recursive calls can reuse the result for arbitrary subformulas. -/
theorem satisfies_substFuel_quantifierFree [DecidableEq V] [Fresh V]
    (s : Structure R F V) (σ : V → Elem s) (x : V) (replacement : Term F V)
    (φ : Formula R F V) (n : Nat) (hn : φ.depth ≤ n)
    (hq : φ.quantifierFree = true) :
    satisfies s σ (substFuel x replacement n φ) ↔
      satisfies s (fun y => if y = x then replacement.eval s σ else σ y) φ := by
  induction φ generalizing n with
  | tr | fls => cases n <;> simp_all [Formula.depth, substFuel, satisfies]
  | eql a b =>
    cases n with
    | zero => simp [Formula.depth] at hn
    | succ n => simp [substFuel, satisfies, Term.eval_subst]
  | rel r args =>
    cases n with
    | zero => simp [Formula.depth] at hn
    | succ n => simp [substFuel, satisfies, eval_subst_list]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    cases n with
    | zero => simp [Formula.depth] at hn
    | succ n =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      have hna : a.depth ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hnb : b.depth ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
      simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
      simp only [substFuel, satisfies]
      rw [ia n hna hq.1, ib n hnb hq.2]
  | neg a ia =>
    cases n with
    | zero => simp [Formula.depth] at hn
    | succ n =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      simp only [Formula.quantifierFree] at hq
      simp only [substFuel, satisfies]
      rw [ia n hn hq]
  | allv x a ia | exv x a ia => simp [Formula.quantifierFree] at hq

/-- Substitution on a quantifier-free formula has the usual assignment semantics. -/
theorem satisfies_subst_quantifierFree [DecidableEq V] [Fresh V]
    (s : Structure R F V) (σ : V → Elem s) (x : V) (replacement : Term F V)
    (φ : Formula R F V) (hq : φ.quantifierFree = true) :
    satisfies s σ (Formula.subst x replacement φ) ↔
      satisfies s (fun y => if y = x then replacement.eval s σ else σ y) φ :=
  satisfies_substFuel_quantifierFree s σ x replacement φ φ.depth (Nat.le_refl _) hq

end Logic.FOL
