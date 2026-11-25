import Init.Data.Rat.Lemmas

namespace Sabrina.OWL2.Datatypes

/-- Values given by a signed coefficient and a power-of-ten denominator.
    A rational with a nonterminating decimal expansion is outside this space. -/
def DecimalValue (q : Rat) : Prop :=
  ∃ coefficient : Int, ∃ places : Nat, q = mkRat coefficient (10 ^ places)

/-- Strip factors shared with ten. Each recursive call strictly reduces the
    denominator, so the starting denominator bounds the number of steps. -/
private def checkDenominator : Nat → Nat → Bool
  | 0, _ => false
  | steps + 1, den =>
    if 1 < den then
      let factor := Nat.gcd den 10
      if 1 < factor then checkDenominator steps (den / factor) else false
    else den == 1

private theorem ten_pow_ne_zero (k : Nat) : (10 : Nat) ^ k ≠ 0 :=
  Nat.ne_of_gt (Nat.pow_pos (by decide))

private theorem checkDenominator_iff (steps den : Nat) (hsteps : den ≤ steps) :
    checkDenominator steps den = true ↔ ∃ k : Nat, den ∣ 10 ^ k := by
  induction steps generalizing den with
  | zero =>
    have hzero : den = 0 := Nat.eq_zero_of_le_zero hsteps
    subst den
    simp [checkDenominator]
  | succ steps ih =>
    rw [checkDenominator]
    split
    · rename_i hden
      dsimp only
      split
      · rename_i hfactor
        have hlt : den / Nat.gcd den 10 < den := Nat.div_lt_self (by omega) hfactor
        rw [ih _ (by omega)]
        have hcancel := Nat.div_mul_cancel (Nat.gcd_dvd_left den 10)
        have hdivide : den / Nat.gcd den 10 ∣ den := ⟨_, hcancel.symm⟩
        constructor
        · rintro ⟨k,hk⟩
          refine ⟨k + 1, ?_⟩
          have h := Nat.mul_dvd_mul hk (Nat.gcd_dvd_right den 10)
          rw [hcancel] at h
          simpa only [Nat.pow_succ] using h
        · rintro ⟨k,hk⟩
          exact ⟨k,Nat.dvd_trans hdivide hk⟩
      · rename_i hfactor
        have hp := Nat.gcd_pos_of_pos_left 10 (by omega : 0 < den)
        have hg : Nat.gcd den 10 = 1 := by omega
        constructor
        · intro h
          cases h
        · rintro ⟨k,hk⟩
          have he := (Nat.gcd_eq_left_iff_dvd.mpr hk).symm.trans
            (Nat.gcd_pow_right_of_gcd_eq_one hg)
          omega
    · rename_i hl
      have h : den = 0 ∨ den = 1 := by omega
      rcases h with rfl | rfl
      · simp
      · exact ⟨fun _ => ⟨0,Nat.one_dvd _⟩,fun _ => rfl⟩

def checkDecimalValue (q : Rat) : Bool := checkDenominator q.den q.den

theorem checkDecimalValue_iff (q : Rat) :
    checkDecimalValue q = true ↔ DecimalValue q := by
  rw [checkDecimalValue, checkDenominator_iff _ _ (Nat.le_refl _)]
  constructor
  · rintro ⟨places, factor, he⟩
    have h : factor ≠ 0 := by
      intro h
      simp [h] at he
    exact ⟨q.num * (factor : Int),places,by rw [he, Rat.mkRat_mul_right h, Rat.mkRat_self]⟩
  · rintro ⟨coefficient,places,rfl⟩
    refine ⟨places,?_⟩
    rw [Rat.den_mkRat, ite_eq_right (ten_pow_ne_zero _)]
    exact ⟨_,(Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩

instance (q : Rat) : Decidable (DecimalValue q) :=
  decidable_of_iff (checkDecimalValue q = true) (checkDecimalValue_iff q)

end Sabrina.OWL2.Datatypes
