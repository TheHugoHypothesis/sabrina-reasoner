import Sabrina.OWL2.Datatypes

/-! Independent W3C XSD 1.1 / IEEE-754 / RFC 4647 lexical-decoder correspondence
    proofs for SABRINA's 33-datatype map (Milestone C.2.1). -/

namespace Sabrina.OWL2.Datatypes.StandardsCorrespondence

open Sabrina.OWL2.Datatypes

/-! ### 1. `xsd:hexBinary` & `xsd:base64Binary` Correspondence -/

/-- Independent declarative specification of a single hexadecimal digit character
and its 4-bit numeric value (`0..15`). -/
def HexDigitVal (c : Char) (v : Nat) : Prop :=
  ('0' ≤ c ∧ c ≤ '9' ∧ v = c.toNat - '0'.toNat) ∨
  ('a' ≤ c ∧ c ≤ 'f' ∧ v = 10 + c.toNat - 'a'.toNat) ∨
  ('A' ≤ c ∧ c ≤ 'F' ∧ v = 10 + c.toNat - 'A'.toNat)

/-- Independent W3C XSD 1.1 §3.3.15 lexical specification for `xsd:hexBinary`. -/
inductive HexBinaryLexical : List Char → List UInt8 → Prop where
  | nil : HexBinaryLexical [] []
  | cons {hi lo : Char} {h l : Nat} {rest : List Char} {tail : List UInt8} :
      HexDigitVal hi h → HexDigitVal lo l →
      HexBinaryLexical rest tail →
      HexBinaryLexical (hi :: lo :: rest) (UInt8.ofNat (h * 16 + l) :: tail)

private def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('A'.toNat + (n - 10))

/-- Canonical uppercase `xsd:hexBinary` encoder. -/
def encodeHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigitChar (b.toNat / 16), hexDigitChar (b.toNat % 16)])

private theorem char_le_toNat {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

private theorem hexNibble_iff (c : Char) (v : Nat) :
    (if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
     else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
     else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
     else none) = some v ↔ HexDigitVal c v := by
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hf : 'f'.toNat = 102 := rfl
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  unfold HexDigitVal
  simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_toNat, h0, h9, ha, hf, hA, hF]
  by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · simp only [h1, and_self, ↓reduceIte, Option.some.injEq]
    constructor
    · intro hv; exact Or.inl ⟨trivial, trivial, hv.symm⟩
    · rintro (⟨_, _, hv⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩) <;> omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 97 ≤ c.toNat ∧ c.toNat ≤ 102
    · simp only [h2, and_self, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hv; exact Or.inr (Or.inl ⟨trivial, trivial, hv.symm⟩)
      · rintro (⟨h1a, h1b, _⟩ | ⟨_, _, hv⟩ | ⟨h3a, h3b, _⟩) <;> omega
    · simp only [h2, ↓reduceIte]
      by_cases h3 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
      · simp only [h3, and_self, ↓reduceIte, Option.some.injEq]
        constructor
        · intro hv; exact Or.inr (Or.inr ⟨trivial, trivial, hv.symm⟩)
        · rintro (⟨h1a, h1b, _⟩ | ⟨h2a, h2b, _⟩ | ⟨_, _, hv⟩) <;> omega
      · simp only [h3, ↓reduceIte, reduceCtorEq, false_iff]
        rintro (⟨h1a, h1b, _⟩ | ⟨h2a, h2b, _⟩ | ⟨h3a, h3b, _⟩)
        · exact h1 ⟨h1a, h1b⟩
        · exact h2 ⟨h2a, h2b⟩
        · exact h3 ⟨h3a, h3b⟩

private theorem parseHexBinary_go_iff (cs : List Char) (bs : List UInt8) :
    parseHexBinary.go cs = some bs ↔ HexBinaryLexical cs bs := by
  induction cs using parseHexBinary.go.induct generalizing bs with
  | case1 =>
    simp only [parseHexBinary.go, Option.some.injEq]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | case2 c =>
    simp only [parseHexBinary.go, reduceCtorEq, false_iff]
    intro h; cases h
  | case3 hi lo rest ih =>
    unfold parseHexBinary.go
    change (Option.bind (if '0' ≤ hi && hi ≤ '9' then some (hi.toNat - '0'.toNat)
      else if 'a' ≤ hi && hi ≤ 'f' then some (10 + hi.toNat - 'a'.toNat)
      else if 'A' ≤ hi && hi ≤ 'F' then some (10 + hi.toNat - 'A'.toNat)
      else none) fun h =>
      Option.bind (if '0' ≤ lo && lo ≤ '9' then some (lo.toNat - '0'.toNat)
      else if 'a' ≤ lo && lo ≤ 'f' then some (10 + lo.toNat - 'a'.toNat)
      else if 'A' ≤ lo && lo ≤ 'F' then some (10 + lo.toNat - 'A'.toNat)
      else none) fun l =>
      Option.bind (parseHexBinary.go rest) fun tail =>
      some (UInt8.ofNat (h * 16 + l) :: tail)) = some bs ↔ _
    constructor
    · intro h
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨hv, hhv, lv, hlv, tail, htail, rfl⟩ := h
      exact .cons ((hexNibble_iff hi hv).mp hhv) ((hexNibble_iff lo lv).mp hlv) ((ih tail).mp htail)
    · intro h
      cases h with
      | cons hhv hlv htail =>
        simp only [Option.bind_eq_some_iff, Option.some.injEq]
        exact ⟨_, (hexNibble_iff _ _).mpr hhv, _, (hexNibble_iff _ _).mpr hlv, _, (ih _).mpr htail, rfl⟩

/-- Exact correspondence between SABRINA's `parseHexBinary` and W3C XSD 1.1 `HexBinaryLexical`. -/
theorem parseHexBinary_iff (raw : String) (bs : List UInt8) :
    parseHexBinary raw = some bs ↔ HexBinaryLexical raw.toList bs :=
  parseHexBinary_go_iff raw.toList bs

private theorem hexDigitChar_spec {n : Nat} (hn : n < 16) :
    HexDigitVal (hexDigitChar n) n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
         n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold HexDigitVal hexDigitChar <;> decide

/-- Canonical `encodeHex` round-trips identically through `parseHexBinary`. -/
theorem parseHexBinary_encodeHex (bs : List UInt8) :
    parseHexBinary (encodeHex bs) = some bs := by
  rw [parseHexBinary_iff, encodeHex, String.toList_ofList]
  induction bs with
  | nil => exact .nil
  | cons b tail ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    have hlt : b.toNat < 256 := b.toBitVec.isLt
    have hEq : UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b := by
      have hdiv : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
      rw [hdiv, UInt8.ofNat_toNat]
    have hcon := HexBinaryLexical.cons
      (hexDigitChar_spec (by omega : b.toNat / 16 < 16))
      (hexDigitChar_spec (by omega : b.toNat % 16 < 16))
      ih
    rwa [hEq] at hcon

private def b64Alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def b64Char (n : Nat) : Char :=
  b64Alphabet.getD n 'A'

private def encodeBase64Chars : List UInt8 → List Char
  | [] => []
  | [b1] =>
    let n1 := b1.toNat
    [b64Char (n1 / 4), b64Char ((n1 % 4) * 16), '=', '=']
  | [b1, b2] =>
    let n1 := b1.toNat; let n2 := b2.toNat
    [b64Char (n1 / 4), b64Char ((n1 % 4) * 16 + n2 / 16), b64Char ((n2 % 16) * 4), '=']
  | b1 :: b2 :: b3 :: rest =>
    let n1 := b1.toNat; let n2 := b2.toNat; let n3 := b3.toNat
    b64Char (n1 / 4) :: b64Char ((n1 % 4) * 16 + n2 / 16) ::
      b64Char ((n2 % 16) * 4 + n3 / 64) :: b64Char (n3 % 64) :: encodeBase64Chars rest

/-- Canonical RFC 4648 / XSD 1.1 `xsd:base64Binary` encoder. -/
def encodeBase64 (bs : List UInt8) : String :=
  String.ofList (encodeBase64Chars bs)

/-- Concrete round-trip and non-canonical padding rejection checks for `xsd:base64Binary`. -/
theorem base64_normative_checks :
    parseBase64Binary (encodeBase64 []) = some [] ∧
    parseBase64Binary (encodeBase64 [0x4D]) = some [0x4D] ∧
    parseBase64Binary (encodeBase64 [0x4D, 0x61]) = some [0x4D, 0x61] ∧
    parseBase64Binary (encodeBase64 [0x4D, 0x61, 0x6E]) = some [0x4D, 0x61, 0x6E] ∧
    parseBase64Binary (encodeBase64 [0x00, 0xFF, 0x80, 0x7F]) = some [0x00, 0xFF, 0x80, 0x7F] ∧
    parseBase64Binary "AB==" = none ∧
    parseBase64Binary "AAB=" = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### 2. IEEE-754 Round-to-Nearest-Ties-to-Even Correspondence -/

/-- Independent IEEE-754 §4.3.1 declarative specification of round-to-nearest-ties-to-even
for a nonnegative rational `num / den` (`den > 0`):
- `q` minimizes `|num / den - q|` over `Nat` (`2 * |num - q * den| ≤ den`), and
- on an exact half-way tie, `q` is even (`q % 2 = 0`). -/
def RoundTiesEvenSpec (num den q : Nat) : Prop :=
  0 < den ∧
  (2 * num ≤ (2 * q + 1) * den) ∧
  ((2 * q) * den ≤ 2 * num + den) ∧
  (2 * num = (2 * q + 1) * den ∨ 2 * num + den = 2 * q * den → q % 2 = 0)

/-- Exact equivalence between SABRINA's `roundTiesEven` and IEEE-754 `RoundTiesEvenSpec`. -/
theorem roundTiesEven_iff {num den : Nat} (hden : 0 < den) (q : Nat) :
    roundTiesEven num den = q ↔ RoundTiesEvenSpec num den q := by
  unfold roundTiesEven RoundTiesEvenSpec
  have hdiv : num = den * (num / den) + num % den := (Nat.div_add_mod num den).symm
  have hmod : num % den < den := Nat.mod_lt num hden
  have hmul0 : 2 * (num / den) * den = 2 * (den * (num / den)) := by
    rw [Nat.mul_assoc, Nat.mul_comm (num / den) den]
  have hmul1 : (2 * (num / den) + 1) * den = 2 * (den * (num / den)) + den := by
    rw [Nat.add_mul, Nat.one_mul, hmul0]
  have hmul2 : 2 * (num / den + 1) * den = 2 * (den * (num / den)) + 2 * den := by
    rw [Nat.mul_add, Nat.add_mul, hmul0]
  have hmul3 : (2 * (num / den + 1) + 1) * den = 2 * (den * (num / den)) + 3 * den := by
    have : 2 * (num / den + 1) + 1 = 2 * (num / den) + 3 := by omega
    rw [this, Nat.add_mul, hmul0]
  have hmul4 : 2 * (num / den + 2) * den = 2 * (den * (num / den)) + 4 * den := by
    have : 2 * (num / den + 2) = 2 * (num / den) + 4 := by omega
    rw [this, Nat.add_mul, hmul0]
  by_cases hup : den < 2 * (num % den) ∨ (den = 2 * (num % den) ∧ (num / den) % 2 = 1)
  · have hcond : (decide (den < 2 * (num % den)) || (den == 2 * (num % den) && (num / den) % 2 == 1)) = true := by
      rcases hup with h1 | ⟨h2, h3⟩
      · simp only [decide_eq_true h1, Bool.true_or]
      · simp only [beq_iff_eq.mpr h2, beq_iff_eq.mpr h3, Bool.and_self, Bool.or_true]
    simp only [hcond, ↓reduceIte]
    constructor
    · rintro rfl
      refine ⟨hden, ?_, ?_, ?_⟩
      · omega
      · rcases hup with h1 | ⟨h2, _⟩ <;> omega
      · intro htie
        rcases hup with h1 | ⟨h2, h3⟩ <;> omega
    · rintro ⟨_, h1, h2, htie⟩
      have hhi : q ≤ num / den + 1 := by
        cases Nat.lt_or_ge (num / den + 1) q with
        | inl hlt =>
          have hm : 2 * (num / den + 2) * den ≤ 2 * q * den :=
            Nat.mul_le_mul_right den (by omega)
          omega
        | inr hle => exact hle
      cases Nat.lt_or_ge q (num / den) with
      | inl hlt =>
        have hpos : 1 ≤ 2 * (num / den) := by omega
        have hm : (2 * q + 1) * den ≤ (2 * (num / den) - 1) * den :=
          Nat.mul_le_mul_right den (by omega)
        have hsub : (2 * (num / den) - 1) * den + den = 2 * (den * (num / den)) := by
          have h1d : (2 * (num / den) - 1) * den + 1 * den = (2 * (num / den) - 1 + 1) * den :=
            (Nat.add_mul (2 * (num / den) - 1) 1 den).symm
          rw [Nat.one_mul, Nat.sub_add_cancel hpos, hmul0] at h1d
          exact h1d
        omega
      | inr hge =>
        by_cases hq : q = num / den
        · subst hq
          rcases hup with hlt | ⟨heq, hodd⟩
          · omega
          · have heven := htie (Or.inl (by omega))
            omega
        · omega
  · have hcond : (decide (den < 2 * (num % den)) || (den == 2 * (num % den) && (num / den) % 2 == 1)) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact hup h
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hlehalf : 2 * (num % den) ≤ den :=
      match Nat.lt_or_ge den (2 * (num % den)) with
      | .inl hlt => (hup (Or.inl hlt)).elim
      | .inr hle => hle
    constructor
    · rintro rfl
      refine ⟨hden, by omega, by omega, ?_⟩
      intro htie
      rcases htie with ht | ht
      · have heq : den = 2 * (num % den) := by omega
        have hnotodd : (num / den) % 2 ≠ 1 := fun ho => hup (Or.inr ⟨heq, ho⟩)
        omega
      · omega
    · rintro ⟨_, h1, h2, htie⟩
      have hlo : num / den ≤ q := by
        cases Nat.lt_or_ge q (num / den) with
        | inl hlt =>
          have hpos : 1 ≤ 2 * (num / den) := by omega
          have hm : (2 * q + 1) * den ≤ (2 * (num / den) - 1) * den :=
            Nat.mul_le_mul_right den (by omega)
          have hsub : (2 * (num / den) - 1) * den + den = 2 * (den * (num / den)) := by
            have h1d : (2 * (num / den) - 1) * den + 1 * den = (2 * (num / den) - 1 + 1) * den :=
              (Nat.add_mul (2 * (num / den) - 1) 1 den).symm
            rw [Nat.one_mul, Nat.sub_add_cancel hpos, hmul0] at h1d
            exact h1d
          omega
        | inr hge => exact hge
      have hhi : q ≤ num / den + 1 := by
        cases Nat.lt_or_ge (num / den + 1) q with
        | inl hlt =>
          have hm : 2 * (num / den + 2) * den ≤ 2 * q * den :=
            Nat.mul_le_mul_right den (by omega)
          omega
        | inr hle => exact hle
      by_cases hq : q = num / den
      · exact hq.symm
      · have hq1 : q = num / den + 1 := by omega
        subst hq1
        have heq : den = 2 * (num % den) := by omega
        have hnotodd : (num / den) % 2 ≠ 1 := fun ho => hup (Or.inr ⟨heq, ho⟩)
        have heven : (num / den + 1) % 2 = 0 := htie (Or.inr (by omega))
        omega

/-- IEEE-754 signed-zero & NaN algebraic properties (kernel-verified). -/
theorem ieee754_special_values_spec :
    FloatVal.negZero ≠ FloatVal.posZero ∧
    FloatVal.le .negZero .posZero = true ∧
    FloatVal.le .posZero .negZero = true ∧
    FloatVal.lt .negZero .posZero = false ∧
    FloatVal.lt .posZero .negZero = false ∧
    (∀ x, FloatVal.le .nan x = false) ∧
    (∀ x, FloatVal.le x .nan = false) ∧
    (∀ x, FloatVal.lt .nan x = false) ∧
    (∀ x, FloatVal.lt x .nan = false) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    fun x => by cases x <;> rfl, fun x => by cases x <;> rfl,
    fun x => by cases x <;> rfl, fun x => by cases x <;> rfl⟩

/-! ### 3. W3C XSD 1.1 `xsd:dateTime` & `xsd:dateTimeStamp` Correspondence -/

private theorem option_bind_eq_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- Every timezone offset accepted by `parseTzSuffix` is a whole-minute offset
within the W3C XSD 1.1 inclusive `[-14:00, +14:00]` range. -/
theorem parseTzSuffix_valid {cs : List Char} {offset : Option Int}
    (h : parseTzSuffix cs = some offset) : validTimezoneOffset offset := by
  unfold parseTzSuffix at h
  split at h
  · injection h with h0; subst h0; trivial
  · injection h with h0; subst h0; simp [validTimezoneOffset]
  · rename_i sign h1 h2 m1 m2
    change (if (sign != '+' && sign != '-') = true then none else _) = some offset at h
    split at h
    · cases h
    · obtain ⟨hr, _, h1⟩ := option_bind_eq_some h
      obtain ⟨mn, _, hbound⟩ := option_bind_eq_some h1
      split at hbound
      · cases hbound
      · rename_i hok
        injection hbound with h0
        subst h0
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          not_or, not_and, Nat.not_lt, Nat.not_le] at hok
        have hsec : hr * 3600 + mn * 60 ≤ 50400 := by omega
        split <;> simp only [validTimezoneOffset, Int.ofNat_eq_natCast] <;> omega
  · cases h

private theorem ite_none_eq_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then none else x) = some y) : ¬ c ∧ x = some y := by
  by_cases hc : c
  · simp [hc] at h
  · simp [hc] at h; exact ⟨hc, h⟩

private theorem parseDateTime_frac_den {fracAndTz : List Char} {fn : Int} {fd : Nat} {tz : List Char}
    (h : (match fracAndTz with
      | '.' :: r =>
        let (fDigits, tz) := r.span (fun c => '0' ≤ c && c ≤ '9')
        match parseNatDigits fDigits with
        | none => none
        | some fVal => some ((fVal : Int), 10 ^ fDigits.length, tz)
      | tz => some ((0 : Int), 1, tz)) = some (fn, fd, tz)) :
    ∃ k : Nat, fd = 10 ^ k := by
  split at h
  · dsimp only at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨_, h.2.1.symm⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, h.2.1.symm⟩

/-- Every timestamp accepted by `parseDateTime` satisfies `DateTimeVal.valid`
(decimal epoch seconds and whole-minute offset in `[-14h, +14h]`). -/
theorem parseDateTime_valid {req : Bool} {raw : String} {dt : DateTimeVal}
    (h : parseDateTime req raw = some dt) : dt.valid := by
  unfold parseDateTime at h
  split at h; · cases h
  rename_i chars _
  try dsimp only at h
  generalize (match chars with | '-' :: r => (true, r) | _ => (false, chars)) = pair at h
  rcases pair with ⟨negYear, rest⟩
  try dsimp only at h
  split at h
  · rename_i yearChars afterYear _
    have ⟨_, h⟩ := ite_none_eq_some h
    cases hy : parseNatDigits yearChars with
    | none => rw [hy] at h; cases h
    | some yNat =>
      rw [hy] at h
      try dsimp only at h
      have ⟨_, h⟩ := ite_none_eq_some h
      try dsimp only at h
      split at h
      · split at h
        · have ⟨_, h⟩ := ite_none_eq_some h
          split at h
          · cases h
          · obtain ⟨k, hk⟩ := parseDateTime_frac_den ‹_›
            have ⟨_, h⟩ := ite_none_eq_some h
            split at h
            · cases h
            · have ⟨_, h⟩ := ite_none_eq_some h
              injection h with hdt
              subst hdt
              refine ⟨?_, parseTzSuffix_valid ‹_›⟩
              dsimp only
              split
              · exact ⟨_, 0, (Rat.mkRat_one _).symm⟩
              · rw [hk]
                exact ⟨_, k, rfl⟩
        · cases h
      · cases h
  · cases h

/-! ### 4. RFC 4647 §3.3.1 `rdf:langRange` Basic Filtering Correspondence -/

/-- Independent declarative specification of RFC 4647 §3.3.1 basic language-range
matching (case-insensitive ASCII). -/
def BasicLangRangeMatch (pat lang : String) : Prop :=
  let pl := pat.toList.map toLowerAscii
  let ll := lang.toList.map toLowerAscii
  (pl = ['*'] ∧ ll ≠ []) ∨
  (pl ≠ ['*'] ∧ pl ≠ [] ∧ (ll = pl ∨ ∃ rest, ll = pl ++ '-' :: rest))

private theorem listStartsWith_iff {α : Type} [DecidableEq α] (p s : List α) :
    listStartsWith p s = true ↔ ∃ rest, s = p ++ rest := by
  induction p generalizing s with
  | nil => simp [listStartsWith]
  | cons a ps ih =>
    cases s with
    | nil => simp [listStartsWith]
    | cons b ss =>
      simp only [listStartsWith, Bool.and_eq_true, beq_iff_eq, ih, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, rest, rfl⟩; exact ⟨rest, rfl, rfl⟩
      · rintro ⟨rest, rfl, rfl⟩; exact ⟨rfl, rest, rfl⟩

/-- Exact equivalence between SABRINA's `matchesLangRange` and RFC 4647 `BasicLangRangeMatch`. -/
theorem matchesLangRange_iff (pat lang : String) :
    matchesLangRange pat lang = true ↔ BasicLangRangeMatch pat lang := by
  unfold matchesLangRange BasicLangRangeMatch
  dsimp only
  generalize hpl : pat.toList.map toLowerAscii = pl
  generalize hll : lang.toList.map toLowerAscii = ll
  by_cases hstar : pl = ['*']
  · simp [hstar, List.isEmpty_eq_false_iff]
  · have hstarB : (pl == ['*']) = false := beq_false_of_ne hstar
    by_cases hempty : pl = []
    · simp [hempty]
    · have hemptyB : pl.isEmpty = false := List.isEmpty_eq_false_iff.mpr hempty
      simp only [hstarB, hemptyB, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
        beq_iff_eq, listStartsWith_iff, hstar, hempty, false_and, false_or, ne_eq,
        not_false_eq_true, true_and, List.append_assoc, List.singleton_append]

#print axioms parseHexBinary_iff
#print axioms parseHexBinary_encodeHex
#print axioms base64_normative_checks
#print axioms roundTiesEven_iff
#print axioms ieee754_special_values_spec
#print axioms parseTzSuffix_valid
#print axioms parseDateTime_valid
#print axioms matchesLangRange_iff

end Sabrina.OWL2.Datatypes.StandardsCorrespondence
