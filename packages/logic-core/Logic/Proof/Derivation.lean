import Logic.FOL.SubstFull
import Logic.Proof.Eigen

/-! A sound natural-deduction relation with infinitary eigenvariable premises.
No completeness or finite certificate claim is made. -/
namespace Logic.Proof
open Logic.FOL

inductive Derives [DecidableEq V] [Fresh V] :
    List (Formula R F V) → Formula R F V → Prop where
  | assumption {Γ φ} : φ ∈ Γ → Derives Γ φ
  | truth {Γ} : Derives Γ .tr
  | falseElim {Γ φ} : Derives Γ .fls → Derives Γ φ
  | andIntro {Γ a b} : Derives Γ a → Derives Γ b → Derives Γ (.conj a b)
  | andLeft {Γ a b} : Derives Γ (.conj a b) → Derives Γ a
  | andRight {Γ a b} : Derives Γ (.conj a b) → Derives Γ b
  | orLeft {Γ a b} : Derives Γ a → Derives Γ (.disj a b)
  | orRight {Γ a b} : Derives Γ b → Derives Γ (.disj a b)
  | orElim {Γ a b c} : Derives Γ (.disj a b) →
      Derives (a :: Γ) c → Derives (b :: Γ) c → Derives Γ c
  | impIntro {Γ a b} : Derives (a :: Γ) b → Derives Γ (.impl a b)
  | impElim {Γ a b} : Derives Γ (.impl a b) → Derives Γ a → Derives Γ b
  | negIntro {Γ a} : Derives (a :: Γ) .fls → Derives Γ (.neg a)
  | negElim {Γ a} : Derives Γ (.neg a) → Derives Γ a → Derives Γ .fls
  | classical {Γ a} : Derives (.neg a :: Γ) .fls → Derives Γ a
  | iffIntro {Γ a b} : Derives (a :: Γ) b → Derives (b :: Γ) a →
      Derives Γ (.iffT a b)
  | iffLeft {Γ a b} : Derives Γ (.iffT a b) → Derives Γ a → Derives Γ b
  | iffRight {Γ a b} : Derives Γ (.iffT a b) → Derives Γ b → Derives Γ a
  | eqRefl {Γ} (t : Term F V) : Derives Γ (.eql t t)
  | eqSymm {Γ a b} : Derives Γ (.eql a b) → Derives Γ (.eql b a)
  | eqTrans {Γ a b c} : Derives Γ (.eql a b) → Derives Γ (.eql b c) →
      Derives Γ (.eql a c)
  | allElim {Γ x body} (t : Term F V) : Derives Γ (.allv x body) →
      Derives Γ (body.subst x t)
  | existsIntro {Γ x body} (t : Term F V) : Derives Γ (body.subst x t) →
      Derives Γ (.exv x body)
  /-- Leibniz substitution: from `a = b` and `φ[x:=a]` conclude `φ[x:=b]`. Both
  instances use capture-avoiding substitution, so replacement below binders is safe. -/
  | eqSubst {Γ a b} (x : V) (φ : Formula R F V) : Derives Γ (.eql a b) →
      Derives Γ (φ.subst x a) → Derives Γ (φ.subst x b)
  /-- Universal introduction. The eigenvariable `y` is universally quantified:
  the premise must hold for every `y` that is not free in the context nor in the
  conclusion `∀x.body`. This form is stable under context extension. -/
  | allIntro {Γ x body} :
      (∀ y, FreshIn y Γ → y ∉ (Formula.allv x body).freeVars →
        Derives Γ (body.subst x (.var y))) → Derives Γ (.allv x body)
  /-- Existential elimination. `y` must be fresh for the context, the quantified
  formula and the conclusion `c`. -/
  | existsElim {Γ x body} {c : Formula R F V} : Derives Γ (.exv x body) →
      (∀ y, FreshIn y Γ → y ∉ (Formula.exv x body).freeVars → y ∉ c.freeVars →
        Derives (body.subst x (.var y) :: Γ) c) → Derives Γ c

theorem sound [DecidableEq V] [Fresh V] {Γ : List (Formula R F V)} {φ}
    (h : Derives Γ φ) : Entails Γ φ := by
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
  | @allElim Γ x body t _ ih =>
    intro s σ hs
    apply (satisfies_subst s σ x t body).2
    exact ih s σ hs (t.eval s σ)
  | @existsIntro Γ x body t _ ih =>
    intro s σ hs
    exact ⟨t.eval s σ, (satisfies_subst s σ x t body).1 (ih s σ hs)⟩
  | @eqSubst Γ a b x φ _ _ ih ip =>
    intro s σ hs
    have heq : a.eval s σ = b.eval s σ := ih s σ hs
    apply (satisfies_subst s σ x b φ).2
    have h := (satisfies_subst s σ x a φ).1 (ip s σ hs)
    rw [heq] at h
    exact h
  | @allIntro Γ x body _ ih =>
    intro s σ hs d
    obtain ⟨y, hΓ, hy⟩ := exists_fresh Γ (Formula.allv x body).freeVars
    exact (eigen_instance s σ hy d).1 (ih y hΓ hy s (upd σ y d) (context_update s σ hΓ d hs))
  | @existsElim Γ x body c _ _ ih ic =>
    intro s σ hs
    obtain ⟨y, hΓ, hy⟩ := exists_fresh (Γ) ((Formula.exv x body).freeVars ++ c.freeVars)
    have hy1 : y ∉ (Formula.exv x body).freeVars := fun h => hy (List.mem_append.mpr (Or.inl h))
    have hy2 : y ∉ c.freeVars := fun h => hy (List.mem_append.mpr (Or.inr h))
    obtain ⟨d, hd⟩ := ih s σ hs
    have hyall : y ∉ (Formula.allv x body).freeVars := by
      simpa [Formula.freeVars] using hy1
    have hinst := (eigen_instance s σ hyall d).2 hd
    have hctx := context_update s σ hΓ d hs
    have hc := ic y hΓ hy1 hy2 s (upd σ y d) (by
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hinst
      · exact hctx φ hφ)
    exact (formula_update s σ hy2 d).1 hc

/-- Context inclusion (covers weakening, contraction and exchange). -/
theorem weaken [DecidableEq V] [Fresh V] {Γ Δ : List (Formula R F V)} {φ}
    (h : Derives Γ φ) (sub : ∀ a ∈ Γ, a ∈ Δ) : Derives Δ φ := by
  induction h generalizing Δ with
  | assumption h => exact .assumption (sub _ h)
  | truth => exact .truth
  | falseElim _ ih => exact .falseElim (ih sub)
  | andIntro _ _ ia ib => exact .andIntro (ia sub) (ib sub)
  | andLeft _ ih => exact .andLeft (ih sub)
  | andRight _ ih => exact .andRight (ih sub)
  | orLeft _ ih => exact .orLeft (ih sub)
  | orRight _ ih => exact .orRight (ih sub)
  | orElim _ _ _ ih ia ib =>
    exact .orElim (ih sub) (ia (ext sub)) (ib (ext sub))
  | impIntro _ ih => exact .impIntro (ih (ext sub))
  | impElim _ _ ih ia => exact .impElim (ih sub) (ia sub)
  | negIntro _ ih => exact .negIntro (ih (ext sub))
  | negElim _ _ ih ia => exact .negElim (ih sub) (ia sub)
  | classical _ ih => exact .classical (ih (ext sub))
  | iffIntro _ _ ia ib => exact .iffIntro (ia (ext sub)) (ib (ext sub))
  | iffLeft _ _ ih ia => exact .iffLeft (ih sub) (ia sub)
  | iffRight _ _ ih ia => exact .iffRight (ih sub) (ia sub)
  | allIntro _ ih =>
    exact .allIntro fun y hy hc => ih y (fun a ha => hy a (sub a ha)) hc sub
  | existsElim _ _ ih ic =>
    exact .existsElim (ih sub) fun y hy hq hc =>
      ic y (fun a ha => hy a (sub a ha)) hq hc (ext sub)
  | eqRefl t => exact .eqRefl t
  | eqSymm _ ih => exact .eqSymm (ih sub)
  | eqTrans _ _ ia ib => exact .eqTrans (ia sub) (ib sub)
  | eqSubst x φ _ _ ih ip => exact .eqSubst x φ (ih sub) (ip sub)
  | allElim t _ ih => exact .allElim t (ih sub)
  | existsIntro t _ ih => exact .existsIntro t (ih sub)
where
  ext {Γ Δ : List (Formula R F V)} {a : Formula R F V}
      (sub : ∀ x ∈ Γ, x ∈ Δ) : ∀ x ∈ a :: Γ, x ∈ a :: Δ := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub x hx)

theorem weaken_cons [DecidableEq V] [Fresh V] {Γ : List (Formula R F V)} {φ}
    (a : Formula R F V) (h : Derives Γ φ) : Derives (a :: Γ) φ :=
  weaken h (fun _ hx => List.mem_cons_of_mem _ hx)

theorem exchange [DecidableEq V] [Fresh V] {Γ : List (Formula R F V)} {φ a b}
    (h : Derives (a :: b :: Γ) φ) : Derives (b :: a :: Γ) φ :=
  weaken h (by
    intro x hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with h | h | h <;> simp [h])

/-- Cut: a derived formula may replace an assumption. -/
theorem cut [DecidableEq V] [Fresh V] {Γ : List (Formula R F V)} {a φ}
    (ha : Derives Γ a) (h : Derives (a :: Γ) φ) : Derives Γ φ :=
  .impElim (.impIntro h) ha

end Logic.Proof
