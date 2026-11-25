import Logic.Proof.Alpha
import Logic.FOL.Permutation
import Logic.Proof.ReverseReduction

/-! Admissible syntactic renaming in the original calculus. Alpha conversion
handles the non-equivariant fresh-name choices made by capture-safe substitution. -/
namespace Logic.Proof
open Logic.FOL

/-- Replace the first assumption by an alpha-equivalent formula. -/
theorem alpha_head [DecidableEq V] [Fresh V]
    {Γ : List (Formula R F V)} {a b c : Formula R F V}
    (hab : a.Alpha b) (d : Derives (a :: Γ) c) : Derives (b :: Γ) c :=
  .impElim (weaken_cons b (.impIntro d))
    ((alpha_derives hab _).mpr (.assumption List.mem_cons_self))

/-- A finite list of assumptions can be replaced by derivations. This uses
implication introduction/elimination, not a freshness-sensitive rule induction. -/
theorem context_consequence [DecidableEq V] [Fresh V]
    {Γ Δ : List (Formula R F V)} {c : Formula R F V}
    (d : Derives Γ c) (h : ∀ a ∈ Γ, Derives Δ a) : Derives Δ c := by
  induction Γ generalizing c with
  | nil => exact weaken d (by simp)
  | cons a Γ ih =>
    exact .impElim (ih (.impIntro d) (fun b hb => h b (List.mem_cons_of_mem a hb)))
      (h a List.mem_cons_self)

/-- Any involutive permutation of variable names transports an entire derivation.
Both bound and free names move; no equivariance of `Fresh.fresh` is assumed. -/
theorem derives_mapNames [DecidableEq V] [Fresh V]
    (ρ : V → V) (hinv : ∀ v, ρ (ρ v) = v)
    {Γ : List (Formula R F V)} {c : Formula R F V} (d : Derives Γ c) :
    Derives (Γ.map (Formula.mapNames ρ)) (c.mapNames ρ) := by
  have hinj : ∀ a b, ρ a = ρ b → a = b := by
    intro a b h
    have := congrArg ρ h
    simpa only [hinv] using this
  have fresh {Γ : List (Formula R F V)} {y : V}
      (h : FreshIn y (Γ.map (Formula.mapNames ρ))) : FreshIn (ρ y) Γ := by
    intro a ha hmem
    apply h (a.mapNames ρ) (List.mem_map.mpr ⟨a, ha, rfl⟩)
    have hm := (Formula.mem_mapNames_freeVars ρ hinv a (ρ y)).mpr hmem
    simpa only [hinv] using hm
  have absent {a : Formula R F V} {y : V}
      (h : y ∉ (a.mapNames ρ).freeVars) : ρ y ∉ a.freeVars := by
    intro hm
    have hh := (Formula.mem_mapNames_freeVars ρ hinv a (ρ y)).mpr hm
    exact h (by simpa only [hinv] using hh)
  induction d with
  | assumption h => exact .assumption (List.mem_map.mpr ⟨_, h, rfl⟩)
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
  | eqRefl t => exact .eqRefl (t.mapNames ρ)
  | eqSymm _ ih => exact .eqSymm ih
  | eqTrans _ _ il ir => exact .eqTrans il ir
  | @eqSubst Γ a b x body _ _ ie ip =>
    have p := (alpha_derives (body.mapNames_subst_alpha ρ hinj x a) _).mp ip
    exact (alpha_derives (body.mapNames_subst_alpha ρ hinj x b) _).mpr
      (.eqSubst (ρ x) (body.mapNames ρ) ie p)
  | @allElim Γ x body t _ ih =>
    exact (alpha_derives (body.mapNames_subst_alpha ρ hinj x t) _).mpr
      (.allElim (t.mapNames ρ) ih)
  | @existsIntro Γ x body t _ ih =>
    exact .existsIntro (t.mapNames ρ)
      ((alpha_derives (body.mapNames_subst_alpha ρ hinj x t) _).mp ih)
  | @allIntro Γ x body _ ih =>
    apply Derives.allIntro
    intro y hΓ hy
    have d := ih (ρ y) (fresh hΓ) (absent hy)
    have p := (alpha_derives (body.mapNames_subst_alpha ρ hinj x (.var (ρ y))) _).mp d
    simpa only [Term.mapNames, hinv] using p
  | @existsElim Γ x body c _ _ iw ib =>
    apply Derives.existsElim iw
    intro y hΓ hy hc
    have d := ib (ρ y) (fresh hΓ) (absent hy) (absent hc)
    have p := alpha_head (body.mapNames_subst_alpha ρ hinj x (.var (ρ y))) d
    simpa only [Term.mapNames, hinv] using p

/-- Swapping two fresh eigenvariables transports a universal introduction premise. -/
theorem universalPremiseRename [DecidableEq V] [Fresh V] :
    UniversalPremiseRename R F V := by
  intro Γ x y z body hyΓ hy hzΓ hz d
  have renamed := derives_mapNames (swapNames y z) (swapNames_involutive y z) d
  have restored : Derives Γ ((body.subst x (.var y)).mapNames (swapNames y z)) := by
    apply context_consequence renamed
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (alpha_derives (b.swapNames_alpha y z (hyΓ b hb) (hzΓ b hb)) Γ).mpr (.assumption hb)
  exact (alpha_derives (body.swapNames_instance_alpha x y z hy hz) Γ).mp restored

/-- Swapping two fresh eigenvariables transports an existential elimination branch. -/
theorem existentialPremiseRename [DecidableEq V] [Fresh V] :
    ExistentialPremiseRename R F V := by
  intro Γ x y z body c hyΓ hy hyc hzΓ hz hzc d
  have renamed := derives_mapNames (swapNames y z) (swapNames_involutive y z) d
  have hbody := body.swapNames_instance_alpha x y z hy hz
  have restored : Derives (body.subst x (.var z) :: Γ) (c.mapNames (swapNames y z)) := by
    apply context_consequence renamed
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (alpha_derives hbody _).mpr (.assumption List.mem_cons_self)
    · exact (alpha_derives (b.swapNames_alpha y z (hyΓ b hb) (hzΓ b hb)) _).mpr
        (.assumption (List.mem_cons_of_mem _ hb))
  exact (alpha_derives (c.swapNames_alpha y z hyc hzc) _).mp restored

/-- Every finite derivation belongs to the original relation, with no extra
renaming hypotheses and no semantic-completeness assumption. -/
theorem finite_to_derivation [DecidableEq V] [Fresh V]
    {Γ : List (Formula R F V)} {c : Formula R F V} (d : FiniteDerives Γ c) :
    Derives Γ c := reverse_of_renaming universalPremiseRename existentialPremiseRename d

/-- The original and finite calculi derive exactly the same sequents. -/
theorem derivation_iff_finite [DecidableEq V] [Fresh V]
    {Γ : List (Formula R F V)} {c : Formula R F V} :
    Derives Γ c ↔ FiniteDerives Γ c := ⟨derivation_to_finite, finite_to_derivation⟩

end Logic.Proof
