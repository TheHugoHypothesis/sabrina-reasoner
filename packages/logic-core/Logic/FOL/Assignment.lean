import Logic.FOL.Models

/-! Satisfaction depends only on the values of free variables. -/
namespace Logic.FOL

mutual
/-- Terms evaluate equally under assignments that agree on their variables. -/
theorem Term.eval_agree (s : Structure R F V) (σ τ : V → Elem s)
    (t : Term F V) (h : ∀ v ∈ t.freeVars, σ v = τ v) :
    t.eval s σ = t.eval s τ := by
  cases t with
  | var x => simpa [Term.eval, Term.freeVars] using h x (by simp [Term.freeVars])
  | app f ts =>
    simp only [Term.eval]
    congr 1
    exact eval_terms_agree s σ τ ts h

/-- List companion for term evaluation. -/
theorem eval_terms_agree (s : Structure R F V) (σ τ : V → Elem s)
    (ts : List (Term F V)) (h : ∀ v ∈ freeVarsOfTerms ts, σ v = τ v) :
    ts.map (Term.eval s σ) = ts.map (Term.eval s τ) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [freeVarsOfTerms, List.mem_append] at h
    simp only [List.map_cons]
    rw [Term.eval_agree s σ τ t (fun v hv => h v (Or.inl hv)),
        eval_terms_agree s σ τ ts (fun v hv => h v (Or.inr hv))]
end

/-- Satisfaction is invariant when assignments agree on all free variables. -/
theorem satisfies_agree [DecidableEq V] (s : Structure R F V)
    (φ : Formula R F V) (σ τ : V → Elem s)
    (h : ∀ v ∈ φ.freeVars, σ v = τ v) : satisfies s σ φ ↔ satisfies s τ φ := by
  induction φ generalizing σ τ with
  | tr | fls => rfl
  | eql a b =>
    simp only [Formula.freeVars, List.mem_append] at h
    simp only [satisfies]
    rw [Term.eval_agree s σ τ a (fun v hv => h v (Or.inl hv)),
        Term.eval_agree s σ τ b (fun v hv => h v (Or.inr hv))]
  | rel r args =>
    simp only [Formula.freeVars] at h
    simp only [satisfies]
    rw [eval_terms_agree s σ τ args h]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.freeVars, List.mem_append] at h
    have ha := ia σ τ (fun v hv => h v (Or.inl hv))
    have hb := ib σ τ (fun v hv => h v (Or.inr hv))
    simp only [satisfies, ha, hb]
  | neg a ia =>
    simp only [Formula.freeVars] at h
    simp only [satisfies, ia σ τ h]
  | allv x a ia | exv x a ia =>
    simp only [Formula.freeVars, List.mem_filter] at h
    have upd (d : Elem s) : ∀ v ∈ a.freeVars,
        (if v = x then d else σ v) = (if v = x then d else τ v) := by
      intro v hv
      by_cases he : v = x
      · simp [he]
      · simp [he, h v ⟨hv, by simp [he]⟩]
    simp only [satisfies]
    simp only [ia _ _ (upd _)]

/-- A sentence has the same truth value under all assignments. -/
theorem sentence_assignment_independent [DecidableEq V] (s : Structure R F V)
    (φ : Formula R F V) (closed : φ.isSentence = true) (σ τ : V → Elem s) :
    satisfies s σ φ ↔ satisfies s τ φ := by
  apply satisfies_agree
  intro v hv
  have : φ.freeVars = [] := List.isEmpty_iff.mp closed
  simp [this] at hv

end Logic.FOL
