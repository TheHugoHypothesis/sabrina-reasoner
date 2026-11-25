import Logic.Proof.Derivation

/-! A finitary derivation relation with an explicitly chosen eigenvariable.
The relation is not yet a serialized certificate format or a completeness result. -/
namespace Logic.Proof
open Logic.FOL

inductive FiniteDerives [DecidableEq V] [Fresh V] :
    List (Formula R F V) → Formula R F V → Prop where
  | assumption {Γ φ} : φ ∈ Γ → FiniteDerives Γ φ
  | truth {Γ} : FiniteDerives Γ .tr
  | falseElim {Γ φ} : FiniteDerives Γ .fls → FiniteDerives Γ φ
  | andIntro {Γ a b} : FiniteDerives Γ a → FiniteDerives Γ b → FiniteDerives Γ (.conj a b)
  | andLeft {Γ a b} : FiniteDerives Γ (.conj a b) → FiniteDerives Γ a
  | andRight {Γ a b} : FiniteDerives Γ (.conj a b) → FiniteDerives Γ b
  | orLeft {Γ a b} : FiniteDerives Γ a → FiniteDerives Γ (.disj a b)
  | orRight {Γ a b} : FiniteDerives Γ b → FiniteDerives Γ (.disj a b)
  | orElim {Γ a b c} : FiniteDerives Γ (.disj a b) →
      FiniteDerives (a :: Γ) c → FiniteDerives (b :: Γ) c → FiniteDerives Γ c
  | impIntro {Γ a b} : FiniteDerives (a :: Γ) b → FiniteDerives Γ (.impl a b)
  | impElim {Γ a b} : FiniteDerives Γ (.impl a b) → FiniteDerives Γ a → FiniteDerives Γ b
  | negIntro {Γ a} : FiniteDerives (a :: Γ) .fls → FiniteDerives Γ (.neg a)
  | negElim {Γ a} : FiniteDerives Γ (.neg a) → FiniteDerives Γ a → FiniteDerives Γ .fls
  | classical {Γ a} : FiniteDerives (.neg a :: Γ) .fls → FiniteDerives Γ a
  | iffIntro {Γ a b} : FiniteDerives (a :: Γ) b → FiniteDerives (b :: Γ) a →
      FiniteDerives Γ (.iffT a b)
  | iffLeft {Γ a b} : FiniteDerives Γ (.iffT a b) → FiniteDerives Γ a → FiniteDerives Γ b
  | iffRight {Γ a b} : FiniteDerives Γ (.iffT a b) → FiniteDerives Γ b → FiniteDerives Γ a
  | eqRefl {Γ} (t : Term F V) : FiniteDerives Γ (.eql t t)
  | eqSymm {Γ a b} : FiniteDerives Γ (.eql a b) → FiniteDerives Γ (.eql b a)
  | eqTrans {Γ a b c} : FiniteDerives Γ (.eql a b) → FiniteDerives Γ (.eql b c) →
      FiniteDerives Γ (.eql a c)
  | eqSubst {Γ a b} (x : V) (φ : Formula R F V) : FiniteDerives Γ (.eql a b) →
      FiniteDerives Γ (φ.subst x a) → FiniteDerives Γ (φ.subst x b)
  | allElim {Γ x body} (t : Term F V) : FiniteDerives Γ (.allv x body) →
      FiniteDerives Γ (body.subst x t)
  | existsIntro {Γ x body} (t : Term F V) : FiniteDerives Γ (body.subst x t) →
      FiniteDerives Γ (.exv x body)
  | allIntro {Γ x body} (y : V) : FreshIn y Γ →
      y ∉ (Formula.allv x body).freeVars →
      FiniteDerives Γ (body.subst x (.var y)) → FiniteDerives Γ (.allv x body)
  | existsElim {Γ x body} {c : Formula R F V} (y : V) :
      FreshIn y Γ → y ∉ (Formula.exv x body).freeVars → y ∉ c.freeVars →
      FiniteDerives Γ (.exv x body) →
      FiniteDerives (body.subst x (.var y) :: Γ) c → FiniteDerives Γ c

theorem finite_sound [DecidableEq V] [Fresh V]
    {Γ : List (Formula R F V)} {φ} (h : FiniteDerives Γ φ) : Entails Γ φ := by
  induction h with
  | assumption h => intro s σ hs; exact hs _ h
  | truth => intro s σ hs; trivial
  | falseElim _ ih => intro s σ hs; exact False.elim (ih s σ hs)
  | andIntro _ _ ia ib => intro s σ hs; exact ⟨ia s σ hs, ib s σ hs⟩
  | andLeft _ ih => intro s σ hs; exact (ih s σ hs).1
  | andRight _ ih => intro s σ hs; exact (ih s σ hs).2
  | orLeft _ ih => intro s σ hs; exact Or.inl (ih s σ hs)
  | orRight _ ih => intro s σ hs; exact Or.inr (ih s σ hs)
  | orElim _ _ _ ih ia ib =>
    intro s σ hs
    rcases ih s σ hs with ha | hb
    · apply ia s σ
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact ha
      · exact hs φ hφ
    · apply ib s σ
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hb
      · exact hs φ hφ
  | @impIntro Γ a b _ ih =>
    intro s σ hs
    classical
    by_cases ha : satisfies s σ a
    · right
      apply ih s σ
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact ha
      · exact hs φ hφ
    · exact Or.inl ha
  | impElim _ _ ih ia =>
    intro s σ hs
    rcases ih s σ hs with hn | hb
    · exact False.elim (hn (ia s σ hs))
    · exact hb
  | negIntro _ ih =>
    intro s σ hs ha
    apply ih s σ
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact ha
    · exact hs φ hφ
  | negElim _ _ ineg ia => intro s σ hs; exact ineg s σ hs (ia s σ hs)
  | classical _ ih =>
    intro s σ hs
    classical
    apply Classical.byContradiction
    intro hn
    apply ih s σ
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact hn
    · exact hs φ hφ
  | iffIntro _ _ ia ib =>
    intro s σ hs
    constructor
    · intro ha
      apply ia s σ
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact ha
      · exact hs φ hφ
    · intro hb
      apply ib s σ
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hb
      · exact hs φ hφ
  | iffLeft _ _ ih ia => intro s σ hs; exact (ih s σ hs).1 (ia s σ hs)
  | iffRight _ _ ih ib => intro s σ hs; exact (ih s σ hs).2 (ib s σ hs)
  | eqRefl => intro s σ hs; rfl
  | eqSymm _ ih => intro s σ hs; exact (ih s σ hs).symm
  | eqTrans _ _ ia ib => intro s σ hs; exact (ia s σ hs).trans (ib s σ hs)
  | @eqSubst Γ a b x φ _ _ ih ip =>
    intro s σ hs
    have heq : a.eval s σ = b.eval s σ := ih s σ hs
    apply (satisfies_subst s σ x b φ).2
    have h := (satisfies_subst s σ x a φ).1 (ip s σ hs)
    rw [heq] at h
    exact h
  | @allElim Γ x body t _ ih =>
    intro s σ hs
    exact (satisfies_subst s σ x t body).2 (ih s σ hs (t.eval s σ))
  | @existsIntro Γ x body t _ ih =>
    intro s σ hs
    exact ⟨t.eval s σ, (satisfies_subst s σ x t body).1 (ih s σ hs)⟩
  | @allIntro Γ x body y hΓ hy _ ih =>
    intro s σ hs d
    exact (eigen_instance s σ hy d).1 (ih s (upd σ y d) (context_update s σ hΓ d hs))
  | @existsElim Γ x body c y hΓ hy hc _ _ ih ic =>
    intro s σ hs
    obtain ⟨d, hd⟩ := ih s σ hs
    have hyall : y ∉ (Formula.allv x body).freeVars := by
      simpa [Formula.freeVars] using hy
    have hinst := (eigen_instance s σ hyall d).2 hd
    have hctx := context_update s σ hΓ d hs
    have hc' := ic s (upd σ y d) (by
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hinst
      · exact hctx φ hφ)
    exact (formula_update s σ hc d).1 hc'

/-- Every derivation in the original relation has a finite derivation. The
infinitary rules supply a premise for the fresh variable chosen here. -/
theorem derivation_to_finite [DecidableEq V] [Fresh V]
    {Γ : List (Formula R F V)} {φ} (h : Derives Γ φ) : FiniteDerives Γ φ := by
  induction h with
  | assumption h => exact .assumption h
  | truth => exact .truth
  | falseElim _ ih => exact .falseElim ih
  | andIntro _ _ ia ib => exact .andIntro ia ib
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | orElim _ _ _ ic il ir => exact .orElim ic il ir
  | impIntro _ ih => exact .impIntro ih
  | impElim _ _ il ir => exact .impElim il ir
  | negIntro _ ih => exact .negIntro ih
  | negElim _ _ il ir => exact .negElim il ir
  | classical _ ih => exact .classical ih
  | iffIntro _ _ il ir => exact .iffIntro il ir
  | iffLeft _ _ il ir => exact .iffLeft il ir
  | iffRight _ _ il ir => exact .iffRight il ir
  | eqRefl t => exact .eqRefl t
  | eqSymm _ ih => exact .eqSymm ih
  | eqTrans _ _ il ir => exact .eqTrans il ir
  | eqSubst x body _ _ il ir => exact .eqSubst x body il ir
  | allElim t _ ih => exact .allElim t ih
  | existsIntro t _ ih => exact .existsIntro t ih
  | @allIntro Γ x body _ ih =>
    obtain ⟨y, hΓ, hy⟩ := exists_fresh Γ (Formula.allv x body).freeVars
    exact .allIntro y hΓ hy (ih y hΓ hy)
  | @existsElim Γ x body c _ _ iw ib =>
    obtain ⟨y, hΓ, hy⟩ := exists_fresh Γ ((Formula.exv x body).freeVars ++ c.freeVars)
    have hbody : y ∉ (Formula.exv x body).freeVars :=
      fun h => hy (List.mem_append.mpr (Or.inl h))
    have hc : y ∉ c.freeVars := fun h => hy (List.mem_append.mpr (Or.inr h))
    exact .existsElim y hΓ hbody hc iw (ib y hΓ hbody hc)

end Logic.Proof
