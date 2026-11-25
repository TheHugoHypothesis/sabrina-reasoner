import Logic.FOL.Assignment
import Logic.FOL.SubstSemantics

/-! Semantics of renaming free occurrences. -/
namespace Logic.FOL

mutual
/-- Renaming a term evaluates like updating the renamed variable. -/
theorem Term.eval_rename [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    (y z : V) (t : Term F V) :
    (t.rename y z).eval s σ = t.eval s (fun v => if v = y then σ z else σ v) := by
  cases t with
  | var v => by_cases h : v = y <;> simp [Term.rename, Term.eval, h]
  | app f args =>
    simp only [Term.rename, Term.eval]
    rw [eval_rename_terms s σ y z args]

theorem eval_rename_terms [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    (y z : V) (ts : List (Term F V)) :
    (renameTerms y z ts).map (Term.eval s σ) =
      ts.map (Term.eval s (fun v => if v = y then σ z else σ v)) := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [renameTerms, List.map_cons, Term.eval_rename,
      eval_rename_terms]
end

/-- Renaming `y` to a name absent from all variables in the formula agrees
with interpreting `y` as the value of the fresh name. -/
theorem satisfies_rename [DecidableEq V] (s : Structure R F V)
    (φ : Formula R F V) (y z : V) (hz : z ∉ φ.vars) (σ : V → Elem s) :
    satisfies s σ (φ.rename y z) ↔
      satisfies s (fun v => if v = y then σ z else σ v) φ := by
  induction φ generalizing σ with
  | tr | fls => rfl
  | eql a b => simp [Formula.rename, satisfies, Term.eval_rename]
  | rel r ts => simp [Formula.rename, satisfies, eval_rename_terms]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.vars, List.mem_append, not_or] at hz
    simp only [Formula.rename, satisfies]
    rw [ia hz.1 σ, ib hz.2 σ]
  | neg a ia =>
    simp only [Formula.vars] at hz
    simp only [Formula.rename, satisfies]
    rw [ia hz σ]
  | allv w a ia | exv w a ia =>
    simp only [Formula.vars, List.mem_cons, not_or] at hz
    by_cases hwy : w = y
    · subst w
      simp only [Formula.rename, beq_self_eq_true, decide_true, ite_true, satisfies]
      have eqfun (d : Elem s) :
          (fun v => if v = y then d else (if v = y then σ z else σ v)) =
          (fun v => if v = y then d else σ v) := by
        funext v
        by_cases h : v = y <;> simp [h]
      simp only [eqfun]
    · simp only [Formula.rename, beq_iff_eq, hwy, decide_false, satisfies]
      have eqfun (d : Elem s) :
          (fun v => if v = y then (if z = w then d else σ z)
                    else (if v = w then d else σ v)) =
          (fun v => if v = w then d else (if v = y then σ z else σ v)) := by
        funext v
        have hzw : z ≠ w := hz.1
        by_cases hvy : v = y <;> by_cases hvw : v = w <;> simp_all
      have equiv (d : Elem s) :
          satisfies s (fun v => if v = w then d else σ v) (a.rename y z) ↔
          satisfies s (fun v => if v = w then d else if v = y then σ z else σ v) a := by
        rw [← eqfun d]
        exact ia hz.2 _
      simp only [Bool.false_eq_true, ↓reduceIte, equiv]

/-- Every free variable occurs among the variables of the formula. -/
theorem Formula.freeVars_subset_vars [DecidableEq V] (φ : Formula R F V)
    (v : V) (h : v ∈ φ.freeVars) : v ∈ φ.vars := by
  induction φ with
  | tr | fls => simp [Formula.freeVars] at h
  | eql | rel => simpa [Formula.freeVars, Formula.vars] using h
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.freeVars, List.mem_append] at h
    simp only [Formula.vars, List.mem_append]
    exact h.elim (fun ha => Or.inl (ia ha)) (fun hb => Or.inr (ib hb))
  | neg a ia => exact ia h
  | allv w a ia | exv w a ia =>
    simp only [Formula.freeVars, List.mem_filter] at h
    simp only [Formula.vars, List.mem_cons]
    exact Or.inr (ia h.1)

mutual
/-- The executable occurrence check agrees with term free-variable membership. -/
theorem Term.hasFreeVar_iff [DecidableEq V] (w : V) (t : Term F V) :
    t.hasFreeVar? w = true ↔ w ∈ t.freeVars := by
  cases t with
  | var v =>
    by_cases h : v = w
    · subst v; simp [Term.hasFreeVar?, Term.freeVars]
    · simp [Term.hasFreeVar?, Term.freeVars, h, Ne.symm h]
  | app f ts => exact hasFreeVars_iff w ts

theorem hasFreeVars_iff [DecidableEq V] (w : V) (ts : List (Term F V)) :
    hasFreeVars? w ts = true ↔ w ∈ freeVarsOfTerms ts := by
  cases ts with
  | nil => simp [hasFreeVars?, freeVarsOfTerms]
  | cons t ts => simp [hasFreeVars?, freeVarsOfTerms, Term.hasFreeVar_iff,
      hasFreeVars_iff]
end

end Logic.FOL
