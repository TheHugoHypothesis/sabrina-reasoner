import Logic.Proof.Certificate

/-! Reverse translation for certificate trees without eigenvariable rules.
The general reverse direction still needs derivation renaming. -/
namespace Logic.Proof
open Logic.FOL

def eigenFree : Certificate R F V → Bool
  | .assumption | .truth | .eqRefl => true
  | .impIntro p | .falseElim p | .andLeft _ p | .andRight _ p
  | .orLeft p | .orRight p | .negIntro p | .classical p | .eqSymm p
  | .allElim _ _ _ p | .existsIntro _ p => eigenFree p
  | .impElim _ p q | .andIntro p q | .negElim _ p q
  | .iffIntro p q | .iffLeft _ p q | .iffRight _ p q
  | .eqTrans _ p q | .eqSubst _ _ _ _ p q =>
      eigenFree p && eigenFree q
  | .orElim _ _ p q r => eigenFree p && eigenFree q && eigenFree r
  | .allIntro _ _ | .existsElim _ _ _ _ _ => false

theorem eigenFree_check_derives [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (cert : Certificate R F V) (Γ : List (Formula R F V)) (φ : Formula R F V)
    (h : check Γ φ cert = true) (hn : eigenFree cert = true) : Derives Γ φ := by
  induction cert generalizing Γ φ with
  | assumption => exact .assumption (of_decide_eq_true h)
  | truth => cases φ <;> simp [check] at h; exact .truth
  | impIntro proof ih =>
    simp only [eigenFree] at hn
    cases φ <;> simp [check] at h
    exact .impIntro (ih _ _ h hn)
  | impElim a left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    simp only [check, Bool.and_eq_true] at h
    exact .impElim (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | andIntro left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    cases φ <;> simp [check] at h
    exact .andIntro (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | falseElim proof ih => exact .falseElim (ih _ _ h hn)
  | andLeft b proof ih => exact .andLeft (ih _ _ h hn)
  | andRight a proof ih => exact .andRight (ih _ _ h hn)
  | orLeft proof ih =>
    cases φ <;> simp [check] at h
    exact .orLeft (ih _ _ h hn)
  | orRight proof ih =>
    cases φ <;> simp [check] at h
    exact .orRight (ih _ _ h hn)
  | orElim a b choice left right ic il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    simp only [check, Bool.and_eq_true] at h
    exact .orElim (ic _ _ h.1.1 hn.1.1) (il _ _ h.1.2 hn.1.2) (ir _ _ h.2 hn.2)
  | negIntro proof ih =>
    cases φ <;> simp [check] at h
    exact .negIntro (ih _ _ h hn)
  | negElim a left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    cases φ <;> simp [check] at h
    exact .negElim (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | classical proof ih => exact .classical (ih _ _ h hn)
  | iffIntro left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    cases φ <;> simp [check] at h
    exact .iffIntro (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | iffLeft a left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    simp only [check, Bool.and_eq_true] at h
    exact .iffLeft (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | iffRight b left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    simp only [check, Bool.and_eq_true] at h
    exact .iffRight (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | eqRefl => cases φ <;> simp [check] at h; subst h; exact .eqRefl _
  | eqSymm proof ih =>
    cases φ <;> simp [check] at h
    exact .eqSymm (ih _ _ h hn)
  | eqTrans b left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    cases φ <;> simp [check] at h
    exact .eqTrans (il _ _ h.1 hn.1) (ir _ _ h.2 hn.2)
  | eqSubst x body a b left right il ir =>
    simp only [eigenFree, Bool.and_eq_true] at hn
    simp only [check, Bool.and_eq_true] at h
    have heq : φ = body.subst x b := of_decide_eq_true h.1
    subst φ
    exact .eqSubst x body (il _ _ h.2.1 hn.1) (ir _ _ h.2.2 hn.2)
  | allElim x body t proof ih =>
    simp only [check, Bool.and_eq_true] at h
    have heq : φ = body.subst x t := of_decide_eq_true h.1
    subst φ
    exact .allElim t (ih _ _ h.2 hn)
  | existsIntro t proof ih =>
    cases φ <;> simp [check] at h
    exact .existsIntro t (ih _ _ h hn)
  | allIntro y proof ih => simp [eigenFree] at hn
  | existsElim x y body witness branch iw ib => simp [eigenFree] at hn

end Logic.Proof
