import Logic.FOL.SubstFull

/-! Assignment-invariance lemmas behind the eigenvariable rules `allIntro`
and `existsElim` of the natural-deduction calculus. -/
namespace Logic.Proof
open Logic.FOL

/-- `y` is not free in any formula of the context. -/
def FreshIn [DecidableEq V] (y : V) (Γ : List (Formula R F V)) : Prop :=
  ∀ a ∈ Γ, y ∉ a.freeVars

/-- Assignment update at one variable. -/
def upd [DecidableEq V] {s : Structure R F V} (σ : V → Elem s) (y : V) (d : Elem s) :
    V → Elem s :=
  fun w => if w = y then d else σ w

/-- A context in which `y` is not free is insensitive to updating `y`. -/
theorem context_update [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    {Γ : List (Formula R F V)} {y : V} (hy : FreshIn y Γ) (d : Elem s)
    (hs : ∀ a ∈ Γ, satisfies s σ a) : ∀ a ∈ Γ, satisfies s (upd σ y d) a := by
  intro a ha
  refine (satisfies_agree s a σ (upd σ y d) ?_).1 (hs a ha)
  intro v hv
  have : v ≠ y := fun h => hy a ha (h ▸ hv)
  simp [upd, this]

/-- A formula in which `y` is not free is insensitive to updating `y`. -/
theorem formula_update [DecidableEq V] (s : Structure R F V) (σ : V → Elem s)
    {c : Formula R F V} {y : V} (hy : y ∉ c.freeVars) (d : Elem s) :
    satisfies s (upd σ y d) c ↔ satisfies s σ c := by
  apply satisfies_agree
  intro v hv
  have : v ≠ y := fun h => hy (h ▸ hv)
  simp [upd, this]

/-- Instantiating a bound variable by a fresh eigenvariable `y`, interpreted as
`d`, is the same as updating the binder to `d` (needs `y` not free in `∀x.body`). -/
theorem eigen_instance [DecidableEq V] [Fresh V] (s : Structure R F V)
    (σ : V → Elem s) {x y : V} {body : Formula R F V}
    (hy : y ∉ (Formula.allv x body).freeVars) (d : Elem s) :
    satisfies s (upd σ y d) (body.subst x (.var y)) ↔
      satisfies s (fun w => if w = x then d else σ w) body := by
  rw [satisfies_subst]
  apply satisfies_agree
  intro w hw
  by_cases hwx : w = x
  · simp [hwx, Term.eval, upd]
  · have hwy : w ≠ y := by
      intro h
      apply hy
      simp only [Formula.freeVars, List.mem_filter]
      exact ⟨h ▸ hw, by simpa [h] using hwx⟩
    simp [hwx, hwy, upd]

/-- A variable fresh for a context and for any further finite list exists. -/
theorem exists_fresh [DecidableEq V] [Fresh V] (Γ : List (Formula R F V))
    (used : List V) : ∃ y : V, FreshIn y Γ ∧ y ∉ used := by
  refine ⟨Fresh.fresh (Γ.flatMap Formula.freeVars ++ used), ?_, ?_⟩
  · intro a ha hy
    exact Fresh.fresh_notMem (Γ.flatMap Formula.freeVars ++ used) _
      (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨a, ha, hy⟩))) rfl
  · intro hy
    exact Fresh.fresh_notMem (Γ.flatMap Formula.freeVars ++ used) _
      (List.mem_append.mpr (Or.inr hy)) rfl

end Logic.Proof
