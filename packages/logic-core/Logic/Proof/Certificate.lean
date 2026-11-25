import Logic.Proof.Finite
import Logic.Proof.DecidableSyntax

/-! An executable checker for finite natural-deduction certificate trees.
Accepted certificates yield finite derivations and semantic consequences.
Completeness, a textual format and external certificate import are not proved. -/
namespace Logic.Proof
open Logic.FOL

inductive Certificate (R F V : Type) where
  | assumption
  | truth
  | impIntro : Certificate R F V → Certificate R F V
  | impElim : Formula R F V → Certificate R F V → Certificate R F V → Certificate R F V
  | andIntro : Certificate R F V → Certificate R F V → Certificate R F V
  | falseElim : Certificate R F V → Certificate R F V
  | andLeft : Formula R F V → Certificate R F V → Certificate R F V
  | andRight : Formula R F V → Certificate R F V → Certificate R F V
  | orLeft : Certificate R F V → Certificate R F V
  | orRight : Certificate R F V → Certificate R F V
  | orElim : Formula R F V → Formula R F V → Certificate R F V →
      Certificate R F V → Certificate R F V → Certificate R F V
  | negIntro : Certificate R F V → Certificate R F V
  | negElim : Formula R F V → Certificate R F V → Certificate R F V → Certificate R F V
  | classical : Certificate R F V → Certificate R F V
  | iffIntro : Certificate R F V → Certificate R F V → Certificate R F V
  | iffLeft : Formula R F V → Certificate R F V → Certificate R F V → Certificate R F V
  | iffRight : Formula R F V → Certificate R F V → Certificate R F V → Certificate R F V
  | eqRefl
  | eqSymm : Certificate R F V → Certificate R F V
  | eqTrans : Term F V → Certificate R F V → Certificate R F V → Certificate R F V
  | eqSubst : V → Formula R F V → Term F V → Term F V →
      Certificate R F V → Certificate R F V → Certificate R F V
  | allElim : V → Formula R F V → Term F V → Certificate R F V → Certificate R F V
  | existsIntro : Term F V → Certificate R F V → Certificate R F V
  | allIntro : V → Certificate R F V → Certificate R F V
  | existsElim : V → V → Formula R F V → Certificate R F V →
      Certificate R F V → Certificate R F V
  deriving Repr

def check [DecidableEq V] [Fresh V] [DecidableEq (Term F V)] [DecidableEq (Formula R F V)] :
    List (Formula R F V) → Formula R F V → Certificate R F V → Bool
  | Γ, φ, .assumption => decide (φ ∈ Γ)
  | _, .tr, .truth => true
  | _, _, .truth => false
  | Γ, .impl a b, .impIntro proof => check (a :: Γ) b proof
  | _, _, .impIntro _ => false
  | Γ, φ, .impElim a left right =>
      check Γ (.impl a φ) left && check Γ a right
  | Γ, .conj a b, .andIntro left right =>
      check Γ a left && check Γ b right
  | _, _, .andIntro _ _ => false
  | Γ, _, .falseElim proof => check Γ .fls proof
  | Γ, φ, .andLeft b proof => check Γ (.conj φ b) proof
  | Γ, φ, .andRight a proof => check Γ (.conj a φ) proof
  | Γ, .disj a _, .orLeft proof => check Γ a proof
  | _, _, .orLeft _ => false
  | Γ, .disj _ b, .orRight proof => check Γ b proof
  | _, _, .orRight _ => false
  | Γ, c, .orElim a b choice left right =>
      check Γ (.disj a b) choice && check (a :: Γ) c left && check (b :: Γ) c right
  | Γ, .neg a, .negIntro proof => check (a :: Γ) .fls proof
  | _, _, .negIntro _ => false
  | Γ, .fls, .negElim a left right => check Γ (.neg a) left && check Γ a right
  | _, _, .negElim _ _ _ => false
  | Γ, φ, .classical proof => check (.neg φ :: Γ) .fls proof
  | Γ, .iffT a b, .iffIntro left right => check (a :: Γ) b left && check (b :: Γ) a right
  | _, _, .iffIntro _ _ => false
  | Γ, φ, .iffLeft a left right => check Γ (.iffT a φ) left && check Γ a right
  | Γ, φ, .iffRight b left right => check Γ (.iffT φ b) left && check Γ b right
  | _, .eql a b, .eqRefl => decide (a = b)
  | _, _, .eqRefl => false
  | Γ, .eql a b, .eqSymm proof => check Γ (.eql b a) proof
  | _, _, .eqSymm _ => false
  | Γ, .eql a c, .eqTrans b left right =>
      check Γ (.eql a b) left && check Γ (.eql b c) right
  | _, _, .eqTrans _ _ _ => false
  | Γ, goal, .eqSubst x body a b left right =>
      decide (goal = body.subst x b) &&
        (check Γ (.eql a b) left && check Γ (body.subst x a) right)
  | Γ, φ, .allElim x body t proof =>
      decide (φ = body.subst x t) && check Γ (.allv x body) proof
  | Γ, .exv x body, .existsIntro t proof => check Γ (body.subst x t) proof
  | _, _, .existsIntro _ _ => false
  | Γ, .allv x body, .allIntro y proof =>
      decide (y ∉ Γ.flatMap Formula.freeVars ∧ y ∉ (Formula.allv x body).freeVars) &&
        check Γ (body.subst x (.var y)) proof
  | _, _, .allIntro _ _ => false
  | Γ, conclusion, .existsElim x y body witness branch =>
      decide (y ∉ Γ.flatMap Formula.freeVars ∧ y ∉ (Formula.exv x body).freeVars ∧
        y ∉ conclusion.freeVars) &&
        (check Γ (.exv x body) witness &&
          check (body.subst x (.var y) :: Γ) conclusion branch)

theorem check_derives [DecidableEq V] [Fresh V] [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (cert : Certificate R F V) (Γ : List (Formula R F V)) (φ : Formula R F V)
    (h : check Γ φ cert = true) : FiniteDerives Γ φ := by
  induction cert generalizing Γ φ with
  | assumption =>
    apply FiniteDerives.assumption
    exact of_decide_eq_true h
  | truth =>
    cases φ <;> simp [check] at h
    exact FiniteDerives.truth
  | impIntro proof ih =>
    cases φ <;> simp [check] at h
    exact FiniteDerives.impIntro (ih _ _ h)
  | impElim a left right il ir =>
    simp only [check, Bool.and_eq_true] at h
    exact FiniteDerives.impElim (il _ _ h.1) (ir _ _ h.2)
  | andIntro left right il ir =>
    cases φ <;> simp [check] at h
    exact FiniteDerives.andIntro (il _ _ h.1) (ir _ _ h.2)
  | falseElim proof ih => exact .falseElim (ih _ _ h)
  | andLeft b proof ih => exact .andLeft (ih _ _ h)
  | andRight a proof ih => exact .andRight (ih _ _ h)
  | orLeft proof ih =>
    cases φ <;> simp [check] at h
    exact .orLeft (ih _ _ h)
  | orRight proof ih =>
    cases φ <;> simp [check] at h
    exact .orRight (ih _ _ h)
  | orElim a b choice left right ic il ir =>
    simp only [check, Bool.and_eq_true] at h
    exact .orElim (ic _ _ h.1.1) (il _ _ h.1.2) (ir _ _ h.2)
  | negIntro proof ih =>
    cases φ <;> simp [check] at h
    exact .negIntro (ih _ _ h)
  | negElim a left right il ir =>
    cases φ <;> simp [check] at h
    exact .negElim (il _ _ h.1) (ir _ _ h.2)
  | classical proof ih => exact .classical (ih _ _ h)
  | iffIntro left right il ir =>
    cases φ <;> simp [check] at h
    exact .iffIntro (il _ _ h.1) (ir _ _ h.2)
  | iffLeft a left right il ir =>
    simp only [check, Bool.and_eq_true] at h
    exact .iffLeft (il _ _ h.1) (ir _ _ h.2)
  | iffRight b left right il ir =>
    simp only [check, Bool.and_eq_true] at h
    exact .iffRight (il _ _ h.1) (ir _ _ h.2)
  | eqRefl =>
    cases φ <;> simp [check] at h
    subst h
    exact .eqRefl _
  | eqSymm proof ih =>
    cases φ <;> simp [check] at h
    exact .eqSymm (ih _ _ h)
  | eqTrans b left right il ir =>
    cases φ <;> simp [check] at h
    exact .eqTrans (il _ _ h.1) (ir _ _ h.2)
  | eqSubst x body a b left right il ir =>
    simp only [check, Bool.and_eq_true] at h
    have heq : φ = body.subst x b := of_decide_eq_true h.1
    subst φ
    exact .eqSubst x body (il _ _ h.2.1) (ir _ _ h.2.2)
  | allElim x body t proof ih =>
    simp only [check, Bool.and_eq_true] at h
    have heq : φ = body.subst x t := of_decide_eq_true h.1
    subst φ
    exact FiniteDerives.allElim t (ih _ _ h.2)
  | existsIntro t proof ih =>
    cases φ <;> simp [check] at h
    exact FiniteDerives.existsIntro t (ih _ _ h)
  | allIntro y proof ih =>
    cases φ <;> simp [check] at h
    rename_i x body
    obtain ⟨hyΓ, hy⟩ := h.1
    have fresh : FreshIn y Γ := by
      intro a ha hv
      exact hyΓ a ha hv
    exact FiniteDerives.allIntro y fresh hy (ih _ _ h.2)
  | existsElim x y body witness branch iw ib =>
    simp only [check, Bool.and_eq_true] at h
    have hf := of_decide_eq_true h.1
    have fresh : FreshIn y Γ := by
      intro a ha hv
      exact hf.1 (List.mem_flatMap.mpr ⟨a, ha, hv⟩)
    exact FiniteDerives.existsElim y fresh hf.2.1 hf.2.2
      (iw _ _ h.2.1) (ib _ _ h.2.2)

theorem check_sound [DecidableEq V] [Fresh V] [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (cert : Certificate R F V) (Γ : List (Formula R F V)) (φ : Formula R F V)
    (h : check Γ φ cert = true) : Entails Γ φ :=
  finite_sound (check_derives cert Γ φ h)

/-- Every finitary derivation has an accepted certificate tree. This is
completeness relative to `FiniteDerives`, not semantic FOL completeness. -/
theorem finite_has_certificate [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    {Γ : List (Formula R F V)} {φ} (h : FiniteDerives Γ φ) :
    ∃ cert, check Γ φ cert = true := by
  induction h with
  | assumption h => exact ⟨.assumption, by simp [check, h]⟩
  | truth => exact ⟨.truth, rfl⟩
  | falseElim _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.falseElim p, hp⟩
  | andIntro _ _ ia ib =>
    obtain ⟨a, ha⟩ := ia; obtain ⟨b, hb⟩ := ib
    exact ⟨.andIntro a b, by simp [check, ha, hb]⟩
  | @andLeft Γ a b _ ih =>
    obtain ⟨p, hp⟩ := ih; exact ⟨.andLeft b p, hp⟩
  | @andRight Γ a b _ ih =>
    obtain ⟨p, hp⟩ := ih; exact ⟨.andRight a p, hp⟩
  | orLeft _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.orLeft p, hp⟩
  | orRight _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.orRight p, hp⟩
  | @orElim Γ a b c _ _ _ ic il ir =>
    obtain ⟨p, hp⟩ := ic; obtain ⟨q, hq⟩ := il; obtain ⟨r, hr⟩ := ir
    exact ⟨.orElim a b p q r, by simp [check, hp, hq, hr]⟩
  | impIntro _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.impIntro p, hp⟩
  | @impElim Γ a b _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.impElim a p q, by simp [check, hp, hq]⟩
  | negIntro _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.negIntro p, hp⟩
  | @negElim Γ a _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.negElim a p q, by simp [check, hp, hq]⟩
  | classical _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.classical p, hp⟩
  | iffIntro _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.iffIntro p q, by simp [check, hp, hq]⟩
  | @iffLeft Γ a b _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.iffLeft a p q, by simp [check, hp, hq]⟩
  | @iffRight Γ a b _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.iffRight b p q, by simp [check, hp, hq]⟩
  | eqRefl t => exact ⟨.eqRefl, by simp [check]⟩
  | eqSymm _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨.eqSymm p, hp⟩
  | @eqTrans Γ a b c _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.eqTrans b p q, by simp [check, hp, hq]⟩
  | @eqSubst Γ a b x body _ _ il ir =>
    obtain ⟨p, hp⟩ := il; obtain ⟨q, hq⟩ := ir
    exact ⟨.eqSubst x body a b p q, by simp [check, hp, hq]⟩
  | @allElim Γ x body t _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.allElim x body t p, by simp [check, hp]⟩
  | @existsIntro Γ x body t _ ih =>
    obtain ⟨p, hp⟩ := ih; exact ⟨.existsIntro t p, hp⟩
  | @allIntro Γ x body y hΓ hy _ ih =>
    obtain ⟨p, hp⟩ := ih
    have hf : y ∉ Γ.flatMap Formula.freeVars := by
      intro hmem
      obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hmem
      exact hΓ a ha hv
    exact ⟨.allIntro y p, by simp [check, hf, hy, hp]⟩
  | @existsElim Γ x body c y hΓ hy hc _ _ iw ib =>
    obtain ⟨p, hp⟩ := iw; obtain ⟨q, hq⟩ := ib
    have hf : y ∉ Γ.flatMap Formula.freeVars := by
      intro hmem
      obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hmem
      exact hΓ a ha hv
    exact ⟨.existsElim x y body p q, by simp [check, hf, hy, hc, hp, hq]⟩

theorem finite_iff_certificate [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (Γ : List (Formula R F V)) (φ : Formula R F V) :
    FiniteDerives Γ φ ↔ ∃ cert, check Γ φ cert = true := by
  constructor
  · exact finite_has_certificate
  · rintro ⟨cert, h⟩
    exact check_derives cert Γ φ h

/-- Every original derivation admits a finite accepted certificate. -/
theorem derivation_has_certificate [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    {Γ : List (Formula R F V)} {φ} (h : Derives Γ φ) :
    ∃ cert, check Γ φ cert = true :=
  finite_has_certificate (derivation_to_finite h)

end Logic.Proof
