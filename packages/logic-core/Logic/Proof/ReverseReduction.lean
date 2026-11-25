import Logic.Proof.Finite

/-! Reduction of the unrestricted reverse implication to two explicit
derivation-renaming obligations. They remain explicit hypotheses of this
reduction; `Logic.Proof.Renaming` proves both and obtains the unconditional result. -/
namespace Logic.Proof
open Logic.FOL

def UniversalPremiseRename (R F V : Type) [DecidableEq V] [Fresh V] : Prop :=
  ∀ (Γ : List (Formula R F V)) (x y z : V) (body : Formula R F V),
    FreshIn y Γ → y ∉ (Formula.allv x body).freeVars →
    FreshIn z Γ → z ∉ (Formula.allv x body).freeVars →
    Derives Γ (body.subst x (.var y)) →
    Derives Γ (body.subst x (.var z))

def ExistentialPremiseRename (R F V : Type) [DecidableEq V] [Fresh V] : Prop :=
  ∀ (Γ : List (Formula R F V)) (x y z : V) (body c : Formula R F V),
    FreshIn y Γ → y ∉ (Formula.exv x body).freeVars → y ∉ c.freeVars →
    FreshIn z Γ → z ∉ (Formula.exv x body).freeVars → z ∉ c.freeVars →
    Derives (body.subst x (.var y) :: Γ) c →
    Derives (body.subst x (.var z) :: Γ) c

/-- If both proof-renaming obligations are established, every finitary proof
has a counterpart in the original relation. The obligations remain explicit. -/
theorem reverse_of_renaming [DecidableEq V] [Fresh V]
    (hall : UniversalPremiseRename R F V) (hex : ExistentialPremiseRename R F V)
    {Γ : List (Formula R F V)} {φ} (h : FiniteDerives Γ φ) : Derives Γ φ := by
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
  | @allIntro Γ x body y hΓ hy _ ih =>
    apply Derives.allIntro
    intro z hzΓ hz
    exact hall Γ x y z body hΓ hy hzΓ hz ih
  | @existsElim Γ x body c y hΓ hy hc _ _ iw ib =>
    apply Derives.existsElim iw
    intro z hzΓ hz hzc
    exact hex Γ x y z body c hΓ hy hc hzΓ hz hzc ib

end Logic.Proof
