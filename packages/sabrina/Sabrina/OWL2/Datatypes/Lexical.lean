import Init.Data.Int.Lemmas
import Init.Data.Rat.Lemmas
import Init.Data.List.Lemmas
import Init.Data.String.Lemmas

/-! Lexical forms from XSD 1.1 sections 3.3.2 and 3.4.13. These decoders
take the lexical form of an OWL literal, as in OWL 2 section 5.7. -/

namespace Sabrina.OWL2.Datatypes

def BooleanLexical (s : String) (b : Bool) : Prop :=
  if b then s = "true" ∨ s = "1" else s = "false" ∨ s = "0"

def parseBoolean (s : String) : Option Bool :=
  if s = "true" ∨ s = "1" then some true
  else if s = "false" ∨ s = "0" then some false
  else none

theorem parseBoolean_iff (s : String) (b : Bool) :
    parseBoolean s = some b ↔ BooleanLexical s b := by
  have separated : (s = "true" ∨ s = "1") → ¬ (s = "false" ∨ s = "0") := by
    rintro (rfl | rfl) <;> decide
  cases b
  · by_cases ht : s = "true" ∨ s = "1"
    · simp [parseBoolean, BooleanLexical, ht, separated ht]
    · by_cases hf : s = "false" ∨ s = "0" <;> simp [parseBoolean, BooleanLexical, ht, hf]
  · by_cases ht : s = "true" ∨ s = "1"
    · simp [parseBoolean, BooleanLexical, ht]
    · by_cases hf : s = "false" ∨ s = "0" <;> simp [parseBoolean, BooleanLexical, ht, hf]

def AsciiDigit (c : Char) : Prop :=
  '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat

instance (c : Char) : Decidable (AsciiDigit c) :=
  inferInstanceAs (Decidable ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat))

private def digitValue (c : Char) : Nat := c.toNat - '0'.toNat

/-- Decimal place value, given independently of the accumulator parser. -/
def decimalValue : List Char → Nat
  | [] => 0
  | c :: tail => digitValue c * 10 ^ tail.length + decimalValue tail

def MagnitudeLexical (digits : List Char) (n : Nat) : Prop :=
  digits ≠ [] ∧ (∀ c ∈ digits, AsciiDigit c) ∧ n = decimalValue digits

inductive SignedIntegerLexical : List Char → Int → Prop
  | unsigned {digits n} : MagnitudeLexical digits n → SignedIntegerLexical digits n
  | plus {digits n} : MagnitudeLexical digits n → SignedIntegerLexical ('+' :: digits) n
  | minus {digits n} : MagnitudeLexical digits n → SignedIntegerLexical ('-' :: digits) (-(n : Int))

def IntegerLexical (s : String) (n : Int) : Prop := SignedIntegerLexical s.toList n

private def readDigits (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: tail =>
    if AsciiDigit c then readDigits (acc * 10 + digitValue c) tail else none

private theorem readDigits_iff (acc : Nat) (digits : List Char) (n : Nat) :
    readDigits acc digits = some n ↔
      (∀ c ∈ digits, AsciiDigit c) ∧ n = acc * 10 ^ digits.length + decimalValue digits := by
  induction digits generalizing acc with
  | nil => simp [readDigits, decimalValue, eq_comm]
  | cons c tail ih =>
    by_cases hc : AsciiDigit c
    · rw [readDigits, ite_eq_left hc, ih]
      simp only [List.mem_cons, forall_eq_or_imp, hc, true_and, List.length_cons,
        decimalValue, Nat.add_mul, Nat.pow_succ', Nat.mul_assoc, Nat.add_assoc]
    · rw [readDigits, ite_eq_right hc]
      simp [hc]

private def parseMagnitude (digits : List Char) : Option Nat :=
  if digits = [] then none else readDigits 0 digits

private theorem parseMagnitude_iff (digits : List Char) (n : Nat) :
    parseMagnitude digits = some n ↔ MagnitudeLexical digits n := by
  by_cases h : digits = []
  · simp [parseMagnitude, MagnitudeLexical, h]
  · simp [parseMagnitude, MagnitudeLexical, h, readDigits_iff]

private def parseSigned : List Char → Option Int
  | '+' :: digits => (parseMagnitude digits).map Int.ofNat
  | '-' :: digits => (parseMagnitude digits).map fun n : Nat => -(n : Int)
  | digits => (parseMagnitude digits).map Int.ofNat

def parseInteger (s : String) : Option Int := parseSigned s.toList

private theorem parseSigned_unsigned (c : Char) (tail : List Char)
    (hp : c ≠ '+') (hn : c ≠ '-') :
    parseSigned (c :: tail) = (parseMagnitude (c :: tail)).map Int.ofNat := by
  unfold parseSigned
  split <;> simp_all

private theorem parseSigned_iff (digits : List Char) (z : Int) :
    parseSigned digits = some z ↔ SignedIntegerLexical digits z := by
  constructor
  · intro h
    cases digits with
    | nil => cases h
    | cons c tail =>
      by_cases hp : c = '+'
      · subst c
        change (parseMagnitude tail).map Int.ofNat = some z at h
        obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp h
        rw [← he]
        exact .plus ((parseMagnitude_iff _ _).mp hn)
      by_cases hm : c = '-'
      · subst c
        change (parseMagnitude tail).map (fun n : Nat => -(n : Int)) = some z at h
        obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp h
        rw [← he]
        exact .minus ((parseMagnitude_iff _ _).mp hn)
      rw [parseSigned_unsigned c tail hp hm] at h
      obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp h
      rw [← he]
      exact .unsigned ((parseMagnitude_iff _ _).mp hn)
  · intro h
    cases h with
    | @plus raw n hm =>
      change (parseMagnitude raw).map Int.ofNat = some (n : Int)
      rw [(parseMagnitude_iff _ _).mpr hm]
      rfl
    | @minus raw n hm =>
      change (parseMagnitude raw).map (fun n : Nat => -(n : Int)) = some (-(n : Int))
      rw [(parseMagnitude_iff _ _).mpr hm]
      rfl
    | unsigned hm =>
      cases digits with
      | nil => exact (hm.1 rfl).elim
      | cons c tail =>
        have hd := hm.2.1 c (List.mem_cons_self ..)
        have hp : c ≠ '+' := fun he => (by decide : ¬ AsciiDigit '+') (he ▸ hd)
        have hn : c ≠ '-' := fun he => (by decide : ¬ AsciiDigit '-') (he ▸ hd)
        rw [parseSigned_unsigned c tail hp hn, (parseMagnitude_iff _ _).mpr hm]
        rfl

theorem parseInteger_iff (s : String) (z : Int) :
    parseInteger s = some z ↔ IntegerLexical s z :=
  parseSigned_iff s.toList z


private def splitFirst (mark : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: tail =>
    if c = mark then some ([],tail)
    else (splitFirst mark tail).map fun (before,after) => (c :: before,after)

private theorem splitFirst_some {mark : Char} {raw before after : List Char} :
    splitFirst mark raw = some (before,after) ↔
      raw = before ++ mark :: after ∧ mark ∉ before := by
  induction raw generalizing before after with
  | nil => cases before <;> simp [splitFirst]
  | cons c tail ih =>
    by_cases he : c = mark
    · subst c
      cases before with
      | nil => simp [splitFirst]
      | cons a before =>
        constructor
        · intro h
          simp [splitFirst] at h
        · rintro ⟨h,hn⟩
          have h' := List.cons.inj h
          exact (hn (List.mem_cons.mpr (Or.inl h'.1))).elim
    · rw [splitFirst, ite_eq_right he]
      constructor
      · intro h
        obtain ⟨⟨xs,ys⟩, hsplit, hpair⟩ := Option.map_eq_some_iff.mp h
        cases hpair
        obtain ⟨rfl,hn⟩ := ih.mp hsplit
        exact ⟨rfl, by simp [Ne.symm he,hn]⟩
      · rintro ⟨h,hn⟩
        cases before with
        | nil => exact (he (List.cons.inj h).1).elim
        | cons a before =>
          have htail := (List.cons.inj h).2
          have hhead := (List.cons.inj h).1
          subst a
          exact Option.map_eq_some_iff.mpr
            ⟨(before,after),ih.mpr ⟨htail,fun hm => hn (List.mem_cons_of_mem _ hm)⟩,rfl⟩

private theorem splitFirst_none {mark : Char} {raw : List Char} :
    splitFirst mark raw = none ↔ mark ∉ raw := by
  induction raw with
  | nil => simp [splitFirst]
  | cons c tail ih =>
    by_cases he : c = mark
    · subst c
      simp [splitFirst]
    · rw [splitFirst, ite_eq_right he, Option.map_eq_none_iff, ih]
      simp [Ne.symm he]

private theorem SignedIntegerLexical.not_mem_mark {raw : List Char} {z : Int}
    (h : SignedIntegerLexical raw z) {c : Char} (hp : c ≠ '+') (hn : c ≠ '-')
    (hd : ¬ AsciiDigit c) : c ∉ raw := by
  cases h with
  | unsigned hm => exact fun hc => hd (hm.2.1 c hc)
  | plus hm =>
    exact fun hc => (List.mem_cons.mp hc).elim hp (fun hc => hd (hm.2.1 c hc))
  | minus hm =>
    exact fun hc => (List.mem_cons.mp hc).elim hn (fun hc => hd (hm.2.1 c hc))

private theorem integer_no_dot {raw : List Char} {z : Int}
    (h : SignedIntegerLexical raw z) : '.' ∉ raw :=
  h.not_mem_mark (by decide) (by decide) (by decide)

private theorem integer_no_slash {raw : List Char} {z : Int}
    (h : SignedIntegerLexical raw z) : '/' ∉ raw :=
  h.not_mem_mark (by decide) (by decide) (by decide)

/-- The integer before scaling is obtained by removing the decimal point.
    Requiring digits after the point to be unsigned keeps the sign at the
    start of the complete spelling. Either side of the point may be empty. -/
def DecimalLexical (s : String) (q : Rat) : Prop :=
  (∃ z, IntegerLexical s z ∧ q = Rat.ofInt z) ∨
  (∃ whole fraction z, s.toList = whole ++ '.' :: fraction ∧
    (∀ c ∈ fraction, AsciiDigit c) ∧ SignedIntegerLexical (whole ++ fraction) z ∧
    q = mkRat z (10 ^ fraction.length))

def parseDecimal (s : String) : Option Rat :=
  match splitFirst '.' s.toList with
  | none => (parseInteger s).map Rat.ofInt
  | some (whole,fraction) =>
    if fraction.all (fun c => decide (AsciiDigit c)) then
      (parseSigned (whole ++ fraction)).map fun z => mkRat z (10 ^ fraction.length)
    else none

theorem parseDecimal_iff (s : String) (q : Rat) :
    parseDecimal s = some q ↔ DecimalLexical s q := by
  constructor
  · intro he
    unfold parseDecimal at he
    cases hs : splitFirst '.' s.toList with
    | none =>
      rw [hs] at he
      obtain ⟨z,hz,hq⟩ := Option.map_eq_some_iff.mp he
      exact Or.inl ⟨z,(parseInteger_iff _ _).mp hz,hq.symm⟩
    | some parts =>
      obtain ⟨whole,fraction⟩ := parts
      rw [hs] at he
      dsimp only at he
      split at he
      · rename_i hf
        obtain ⟨z,hz,hq⟩ := Option.map_eq_some_iff.mp he
        exact Or.inr ⟨whole,fraction,z,(splitFirst_some.mp hs).1,
          fun c hc => of_decide_eq_true (List.all_eq_true.mp hf c hc),
          (parseSigned_iff _ _).mp hz,hq.symm⟩
      · cases he
  · rintro (⟨z,hz,rfl⟩ | ⟨whole,fraction,z,hs,hf,hz,rfl⟩)
    · rw [parseDecimal, splitFirst_none.mpr (integer_no_dot hz), (parseInteger_iff _ _).mpr hz]
      rfl
    · have hsplit : splitFirst '.' s.toList = some (whole,fraction) :=
        splitFirst_some.mpr ⟨hs,fun h => integer_no_dot hz (List.mem_append_left _ h)⟩
      have hall : fraction.all (fun c => decide (AsciiDigit c)) = true :=
        List.all_eq_true.mpr fun c hc => decide_eq_true (hf c hc)
      rw [parseDecimal, hsplit]
      simp [hall, (parseSigned_iff _ _).mpr hz]

def RationalLexical (s : String) (q : Rat) : Prop :=
  ∃ numerator denominator z n, s.toList = numerator ++ '/' :: denominator ∧
    SignedIntegerLexical numerator z ∧ MagnitudeLexical denominator n ∧ 0 < n ∧ q = mkRat z n

def parseRational (s : String) : Option Rat := do
  let (numerator,denominator) ← splitFirst '/' s.toList
  let z ← parseSigned numerator
  let n ← parseMagnitude denominator
  if n = 0 then none else some (mkRat z n)

theorem parseRational_iff (s : String) (q : Rat) :
    parseRational s = some q ↔ RationalLexical s q := by
  constructor
  · intro h
    unfold parseRational at h
    obtain ⟨⟨num,den⟩,hs,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨z,hz,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n,hn,h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hp : n = 0
    · simp [hp] at h
    · have he : mkRat z n = q := by simpa [hp] using h
      exact ⟨num,den,z,n,(splitFirst_some.mp hs).1,
        (parseSigned_iff _ _).mp hz,(parseMagnitude_iff _ _).mp hn, Nat.pos_of_ne_zero hp,he.symm⟩
  · rintro ⟨num,den,z,n,hs,hz,hn,hpos,rfl⟩
    have hr : splitFirst '/' s.toList = some (num,den) :=
      splitFirst_some.mpr ⟨hs,integer_no_slash hz⟩
    simp [parseRational, hr, (parseSigned_iff _ _).mpr hz, (parseMagnitude_iff _ _).mpr hn,
      Nat.ne_of_gt hpos]

end Sabrina.OWL2.Datatypes
