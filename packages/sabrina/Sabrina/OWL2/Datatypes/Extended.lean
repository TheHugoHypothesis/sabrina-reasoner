import Sabrina.OWL2.Datatypes.Lexical
import Sabrina.OWL2.Datatypes.DecimalSpace
import Sabrina.OWL2.Datatypes.XMLNames

/-! Value representations, lexical decoders, and facet relations for the
remaining standard OWL 2 DL datatype families: floating-point (`xsd:float`,
`xsd:double`), string subtypes & `rdf:PlainLiteral`, binary (`xsd:hexBinary`,
`xsd:base64Binary`), date/time (`xsd:dateTime`, `xsd:dateTimeStamp`),
`xsd:anyURI`, and `rdf:XMLLiteral`. -/

namespace Sabrina.OWL2.Datatypes

/-- Exact algebraic value space for IEEE-754 floating-point datatypes
(`xsd:float` and `xsd:double` have disjoint copies in `Value`).
`-0.0` and `+0.0` are distinct values per W3C OWL 2 Direct Semantics §4.2,
while `NaN` is incomparable under all order facets. -/
inductive FloatVal where
  | negInf
  | finite (value : Rat) -- nonzero finite value
  | negZero
  | posZero
  | posInf
  | nan
  deriving DecidableEq, Repr

private def pow10Nat (n : Nat) : Nat := 10 ^ n

private def scalePow10 (q : Rat) (exp : Int) : Rat :=
  if exp ≥ 0 then
    mkRat (q.num * (pow10Nat exp.toNat : Int)) q.den
  else
    mkRat q.num (q.den * pow10Nat (-exp).toNat)

/-- The IEEE binary formats used by the OWL 2 datatype map. -/
inductive FloatFormat where
  | binary32
  | binary64

private def FloatFormat.precision : FloatFormat → Nat
  | .binary32 => 24
  | .binary64 => 53

private def FloatFormat.minExponent : FloatFormat → Int
  | .binary32 => -126
  | .binary64 => -1022

private def FloatFormat.maxExponent : FloatFormat → Int
  | .binary32 => 127
  | .binary64 => 1023

private def scalePow2 (q : Rat) (exp : Int) : Rat :=
  if exp ≥ 0 then
    mkRat (q.num * (2 ^ exp.toNat : Nat)) q.den
  else
    mkRat q.num (q.den * 2 ^ (-exp).toNat)

private def roundTiesEven (numerator denominator : Nat) : Nat :=
  let whole := numerator / denominator
  let twiceRemainder := 2 * (numerator % denominator)
  if denominator < twiceRemainder || (denominator == twiceRemainder && whole % 2 == 1)
  then whole + 1
  else whole

/-- Round exact rationals to the format's significand grid, including
subnormals and overflow. Lexical zeros preserve the sign independently. -/
def FloatFormat.round (format : FloatFormat) (value : Rat) : FloatVal :=
  let negative := value.num < 0
  if value.num == 0 then .posZero
  else
    let absValue := mkRat (Int.ofNat value.num.natAbs) value.den
    let estimate := (Int.ofNat value.num.natAbs.log2) - Int.ofNat value.den.log2
    let exponent := if scalePow2 absValue (-estimate) < 1 then estimate - 1 else estimate
    if format.maxExponent < exponent then
      if negative then .negInf else .posInf
    else
      let unitExponent := max exponent format.minExponent - Int.ofNat (format.precision - 1)
      let scaled := scalePow2 absValue (-unitExponent)
      let significand := roundTiesEven scaled.num.natAbs scaled.den
      if significand == 0 then
        if negative then .negZero else .posZero
      else if exponent == format.maxExponent && 2 ^ format.precision ≤ significand then
        if negative then .negInf else .posInf
      else
        let signed := if negative then -Int.ofNat significand else Int.ofNat significand
        .finite (scalePow2 (Rat.ofInt signed) unitExponent)

private def decodeScaledFloat (format : FloatFormat) (negative : Bool) (base : Rat)
    (decimalExponent : Int) : FloatVal :=
  if base.num == 0 then
    if negative then .negZero else .posZero
  else
    -- Opposite extreme exponents can cancel a long mantissa. Estimate the
    -- magnitude from both parts before constructing the power of ten.
    let magnitude := decimalExponent + Int.ofNat (toString base.num.natAbs).length -
      Int.ofNat (toString base.den).length
    if magnitude > 310 then
      if negative then .negInf else .posInf
    else if magnitude < -330 then
      if negative then .negZero else .posZero
    else format.round (scalePow10 base decimalExponent)

/-- Parse XSD float/double lexical space: `INF`, `+INF`, `-INF`, `NaN`, or
decimal/scientific notation rounded to the requested IEEE format. -/
def parseFloatVal (raw : String) (format : FloatFormat := .binary32) : Option FloatVal :=
  if raw == "INF" || raw == "+INF" then some .posInf
  else if raw == "-INF" then some .negInf
  else if raw == "NaN" then some .nan
  else
    let chars := raw.toList
    let (mantissaChars, expChars?) :=
      match chars.span (fun c => c != 'e' && c != 'E') with
      | (m, []) => (m, none)
      | (m, _ :: e) => (m, some e)
    let mantissaStr := String.ofList mantissaChars
    let negativeSign := mantissaChars.head? == some '-'
    match parseDecimal mantissaStr with
    | none => none
    | some base =>
      match expChars? with
      | none => some (decodeScaledFloat format negativeSign base 0)
      | some eChars => (parseInteger (String.ofList eChars)).map
          (decodeScaledFloat format negativeSign base)

/-- One signed IEEE significand interval at a fixed binary scale. -/
structure FloatBand where
  exponent : Int
  lo : Int
  hi : Int

def FloatBand.unit (b : FloatBand) : Rat := (2 : Rat) ^ b.exponent

theorem FloatBand.unit_pos (b : FloatBand) : 0 < b.unit :=
  Rat.zpow_pos (by decide : (0 : Rat) < 2)

def FloatBand.value (b : FloatBand) (z : Int) : Rat := (z : Rat) * b.unit

theorem FloatBand.value_injective (b : FloatBand) {x y : Int}
    (h : b.value x = b.value y) : x = y := by
  have hn : b.unit ≠ 0 := fun he => (Rat.not_lt.mpr (show b.unit ≤ 0 by rw [he]; exact Rat.le_refl)) b.unit_pos
  have he := congrArg (· / b.unit) h
  have he' : (x : Rat) = (y : Rat) := by simpa only [FloatBand.value, Rat.mul_div_cancel hn] using he
  exact Rat.intCast_inj.mp he'

/-- The first exponent band includes the subnormal grid. All other bands
use the normalized significand interval. Negative values use its reflection. -/
private def FloatFormat.bandCount (f : FloatFormat) : Nat :=
  (f.maxExponent - f.minExponent + 1).toNat

private def FloatFormat.bandAt (f : FloatFormat) (i : Nat) (negative : Bool) : FloatBand :=
  let e := f.minExponent + (i : Int) - ((f.precision - 1 : Nat) : Int)
  let lo : Int := if i == 0 then 1 else Int.ofNat (2 ^ (f.precision - 1))
  let hi : Int := Int.ofNat (2 ^ f.precision - 1)
  if negative then ⟨e, -hi, -lo⟩ else ⟨e, lo, hi⟩

def FloatFormat.bands (format : FloatFormat) : List FloatBand :=
  (List.range format.bandCount).flatMap fun i => [format.bandAt i false, format.bandAt i true]

private theorem FloatFormat.bandAt_mem (f : FloatFormat) (i : Nat) (neg : Bool)
    (hi : i < f.bandCount) : f.bandAt i neg ∈ f.bands :=
  List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by cases neg <;> simp⟩

private def FloatFormat.guessBandIndex (f : FloatFormat) (q : Rat) : Nat :=
  let magnitude := mkRat (Int.ofNat q.num.natAbs) q.den
  let estimate := (Int.ofNat q.num.natAbs.log2) - Int.ofNat q.den.log2
  let exponent := if scalePow2 magnitude (-estimate) < 1 then estimate - 1 else estimate
  (max exponent f.minExponent - f.minExponent).toNat

private def FloatFormat.guessBand (f : FloatFormat) (q : Rat) : Option FloatBand :=
  let i := f.guessBandIndex q
  if i < f.bandCount then some (f.bandAt i (q.num < 0)) else none

private theorem FloatFormat.guessBand_mem (f : FloatFormat) (q : Rat) {b : FloatBand}
    (h : f.guessBand q = some b) : b ∈ f.bands := by
  by_cases hi : f.guessBandIndex q < f.bandCount
  · simp only [FloatFormat.guessBand, hi, ↓reduceIte, Option.some.injEq] at h
    exact h ▸ f.bandAt_mem _ _ hi
  · simp [FloatFormat.guessBand, hi] at h

def FloatBand.contains (b : FloatBand) (q : Rat) : Prop :=
  let coord := q / b.unit
  coord.den = 1 ∧ b.lo ≤ coord.num ∧ coord.num ≤ b.hi

instance (b : FloatBand) (q : Rat) : Decidable (b.contains q) :=
  inferInstanceAs (Decidable ((_ : Rat).den = 1 ∧ _ ≤ _ ∧ _ ≤ _))

theorem FloatBand.contains_iff (b : FloatBand) (q : Rat) :
    b.contains q ↔ ∃ z : Int, b.lo ≤ z ∧ z ≤ b.hi ∧ b.value z = q := by
  have hn : b.unit ≠ 0 := fun h => (Rat.not_lt.mpr (show b.unit ≤ 0 by rw [h]; exact Rat.le_refl)) b.unit_pos
  constructor
  · rintro ⟨hd, hl, hu⟩
    refine ⟨(q / b.unit).num, hl, hu, ?_⟩
    have hc : Rat.ofInt (q / b.unit).num = q / b.unit := by
      exact Rat.ext rfl hd.symm
    exact (congrArg (· * b.unit) hc).trans (Rat.div_mul_cancel hn)
  · rintro ⟨z, hl, hu, rfl⟩
    change (b.value z / b.unit).den = 1 ∧
      b.lo ≤ (b.value z / b.unit).num ∧ (b.value z / b.unit).num ≤ b.hi
    rw [FloatBand.value, Rat.mul_div_cancel hn]
    exact ⟨rfl, hl, hu⟩

def FloatFormat.contains (format : FloatFormat) : FloatVal → Prop
  | .finite value =>
    ((format.guessBand value).any (fun b => decide (b.contains value)) ||
      format.bands.any (fun b => decide (b.contains value))) = true
  | _ => True

instance (format : FloatFormat) (value : FloatVal) : Decidable (format.contains value) := by
  cases value <;> unfold FloatFormat.contains <;> infer_instance

theorem FloatFormat.contains_finite_iff (f : FloatFormat) (q : Rat) :
    f.contains (.finite q) ↔ ∃ b ∈ f.bands, ∃ z : Int,
      b.lo ≤ z ∧ z ≤ b.hi ∧ b.value z = q := by
  have h (b : FloatBand) : decide (b.contains q) = true ↔
      ∃ z : Int, b.lo ≤ z ∧ z ≤ b.hi ∧ b.value z = q :=
    by simpa only [decide_eq_true_eq] using b.contains_iff q
  constructor
  · intro hv
    rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · cases he : f.guessBand q with
      | none => simp [he] at hv
      | some b => exact ⟨b, f.guessBand_mem q he, (h b).mp (by simpa [he] using hv)⟩
    · obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp hv
      exact ⟨b, hb, (h b).mp hc⟩
  · rintro ⟨b, hb, hc⟩
    exact Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨b, hb, (h b).mpr hc⟩))

/-- XSD numeric value for order comparisons on non-NaN floats (`-0.0 = +0.0` in order). -/
def FloatVal.le (a b : FloatVal) : Bool :=
  match a, b with
  | .nan, _ | _, .nan => false
  | .negInf, _ => true
  | _, .negInf => false
  | _, .posInf => true
  | .posInf, _ => false
  | .negZero, .negZero | .negZero, .posZero | .posZero, .negZero | .posZero, .posZero => true
  | .negZero, .finite q | .posZero, .finite q => decide ((0 : Rat) ≤ q)
  | .finite q, .negZero | .finite q, .posZero => decide (q ≤ (0 : Rat))
  | .finite p, .finite q => decide (p ≤ q)

def FloatVal.lt (a b : FloatVal) : Bool :=
  match a, b with
  | .nan, _ | _, .nan => false
  | .negInf, .negInf => false
  | .negInf, _ => true
  | _, .negInf => false
  | .posInf, _ => false
  | _, .posInf => true
  | .negZero, .negZero | .negZero, .posZero | .posZero, .negZero | .posZero, .posZero => false
  | .negZero, .finite q | .posZero, .finite q => decide ((0 : Rat) < q)
  | .finite q, .negZero | .finite q, .posZero => decide (q < (0 : Rat))
  | .finite p, .finite q => decide (p < q)

/-! String subtypes and `rdf:PlainLiteral`. -/

def isNormalizedString (s : String) : Bool :=
  s.toList.all fun c => c != '\r' && c != '\n' && c != '\t'

def isToken (s : String) : Bool :=
  isNormalizedString s &&
  match s.toList with
  | [] => true
  | c :: rest =>
    c != ' ' && (rest.getLastD c) != ' ' &&
    !(hasDoubleSpace (c :: rest))
where
  hasDoubleSpace : List Char → Bool
    | ' ' :: ' ' :: _ => true
    | _ :: tail => hasDoubleSpace tail
    | [] => false

private def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def isAsciiAlnum (c : Char) : Bool :=
  isAsciiAlpha c || ('0' ≤ c && c ≤ '9')

private def splitOnChar (sep : Char) (cs : List Char) : List (List Char) :=
  let rec go : List Char → List Char → List (List Char)
    | [], cur => [cur.reverse]
    | c :: rest, cur =>
      if c == sep then cur.reverse :: go rest []
      else go rest (c :: cur)
  go cs []

def isLanguageTag (s : String) : Bool :=
  let parts := splitOnChar '-' s.toList
  match parts with
  | [] => false
  | first :: rest =>
    1 ≤ first.length && first.length ≤ 8 && first.all isAsciiAlpha &&
    rest.all fun p => 1 ≤ p.length && p.length ≤ 8 && p.all isAsciiAlnum

def isNameStartChar (c : Char) : Bool :=
  isAsciiAlpha c || c == '_' || c == ':' || XMLNames.inRanges XMLNames.highStarts c.toNat

def isNameChar (c : Char) : Bool :=
  isNameStartChar c || ('0' ≤ c && c ≤ '9') || c == '-' || c == '.' ||
    XMLNames.inRanges XMLNames.highExtras c.toNat

def isNMTOKEN (s : String) : Bool :=
  !s.isEmpty && s.toList.all isNameChar

def isName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isNameStartChar c && rest.all isNameChar

def isNCName (s : String) : Bool :=
  isName s && !(s.toList.contains ':')

theorem isNameStartChar_iff (c : Char) : isNameStartChar c = true ↔ XMLNames.NameStartChar c := by
  simp [isNameStartChar, isAsciiAlpha, Bool.or_eq_true, Bool.and_eq_true, Char.le_def,
    UInt32.le_iff_toNat_le, ← Char.toNat_inj, XMLNames.inRanges, XMLNames.highStarts,
    XMLNames.NameStartChar] <;> omega

theorem isNameChar_iff (c : Char) : isNameChar c = true ↔ XMLNames.NameChar c := by
  by_cases h : XMLNames.NameStartChar c <;>
    simp [isNameChar, isNameStartChar_iff, Bool.or_eq_true, Bool.and_eq_true, Char.le_def,
      UInt32.le_iff_toNat_le, ← Char.toNat_inj, XMLNames.inRanges, XMLNames.highExtras,
      XMLNames.NameChar, h] <;> omega

theorem isName_iff (s : String) : isName s = true ↔ XMLNames.Name s.toList := by
  cases h : s.toList with
  | nil => simp [isName, XMLNames.Name, h]
  | cons head tail =>
    simp only [isName, h, Bool.and_eq_true, isNameStartChar_iff, List.all_eq_true,
      isNameChar_iff, XMLNames.Name]
    exact ⟨fun hp => ⟨head, tail, rfl, hp⟩, fun ⟨_, _, he, hp⟩ => by cases he; exact hp⟩

theorem isNCName_iff (s : String) : isNCName s = true ↔ XMLNames.NCName s.toList := by
  simp [isNCName, XMLNames.NCName, isName_iff]

theorem isNMTOKEN_iff (s : String) : isNMTOKEN s = true ↔ XMLNames.Nmtoken s.toList := by
  simp [isNMTOKEN, XMLNames.Nmtoken, List.all_eq_true, isNameChar_iff]

theorem isNameChar_of_isNameStartChar {c : Char} (h : isNameStartChar c = true) :
    isNameChar c = true := by
  simp [isNameChar, h]

theorem isNMTOKEN_of_isName {s : String} (h : isName s = true) : isNMTOKEN s = true := by
  unfold isName at h
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c rest =>
    rw [hs] at h
    obtain ⟨hc, hrest⟩ := Bool.and_eq_true_iff.mp h
    have hne : s.isEmpty = false := by
      cases he : s.isEmpty
      · rfl
      · have := congrArg String.toList (String.isEmpty_iff.mp he)
        rw [hs] at this; cases this
    simp [isNMTOKEN, hne, hs, isNameChar_of_isNameStartChar hc, hrest]

private theorem splitOnChar_go_spec (sep : Char) (cs : List Char) :
    ∀ (cur : List Char),
      (∃ pref rem, splitOnChar.go sep cs cur = (cur.reverse ++ pref) :: rem ∧
        (∀ c ∈ pref, c ≠ sep) ∧ (cs = pref ∨ ∃ suf, cs = pref ++ sep :: suf)) ∧
      (∀ x ∈ cs, x = sep ∨ ∃ p ∈ splitOnChar.go sep cs cur, x ∈ p) := by
  induction cs with
  | nil =>
    intro cur
    refine ⟨⟨[], [], by simp [splitOnChar.go], by simp, .inl rfl⟩, by simp⟩
  | cons c rest ih =>
    intro cur
    by_cases hsep : c = sep
    · subst hsep
      simp only [splitOnChar.go, beq_self_eq_true, ↓reduceIte]
      refine ⟨⟨[], splitOnChar.go c rest [], by simp, by simp, .inr ⟨rest, rfl⟩⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hrest
      · exact .inl rfl
      · rcases (ih []).2 x hrest with rfl | ⟨p, hp, hxp⟩
        · exact .inl rfl
        · exact .inr ⟨p, List.mem_cons_of_mem _ hp, hxp⟩
    · have hbeq : (c == sep) = false := beq_false_of_ne hsep
      simp only [splitOnChar.go, hbeq, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨⟨pref, rem, hgo, hno, hsplit⟩, hmem⟩ := ih (c :: cur)
      refine ⟨⟨c :: pref, rem, by simpa [List.reverse_cons, List.append_assoc] using hgo, ?_, ?_⟩, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hp
        · exact hsep
        · exact hno y hp
      · rcases hsplit with rfl | ⟨suf, rfl⟩
        · exact .inl rfl
        · exact .inr ⟨suf, rfl⟩
      · intro x hx
        rcases List.mem_cons.mp hx with hxc | hrest
        · subst hxc
          refine .inr ⟨(x :: cur).reverse ++ pref, hgo ▸ List.mem_cons_self .., ?_⟩
          simp
        · exact hmem x hrest

theorem isNCName_of_isLanguageTag {s : String} (h : isLanguageTag s = true) :
    isNCName s = true := by
  unfold isLanguageTag splitOnChar at h
  have ⟨⟨pref, rem, hgo, _, hsplit⟩, hmem⟩ := splitOnChar_go_spec '-' s.toList []
  simp only [List.reverse_nil, List.nil_append] at hgo
  rw [hgo] at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen1, _⟩, hprefAlpha⟩, hremAll⟩ := h
  cases hpref : pref with
  | nil => subst hpref; simp at hlen1
  | cons c prefTail =>
    have hcAlpha : isAsciiAlpha c = true := hprefAlpha c (hpref ▸ List.mem_cons_self ..)
    have hcStart : isNameStartChar c = true := by simp [isNameStartChar, hcAlpha]
    have hcs : ∃ tail, s.toList = c :: tail := by
      rcases hsplit with h1 | ⟨suf, h2⟩
      · exact ⟨prefTail, by rw [h1, hpref]⟩
      · exact ⟨prefTail ++ '-' :: suf, by rw [h2, hpref, List.cons_append]⟩
    obtain ⟨tail, htailEq⟩ := hcs
    have hallChar : ∀ x ∈ s.toList, isNameChar x = true ∧ x ≠ ':' := by
      intro x hx
      rcases hmem x hx with rfl | ⟨p, hpMem, hxp⟩
      · exact ⟨by decide, by decide⟩
      · rw [hgo] at hpMem
        rcases List.mem_cons.mp hpMem with rfl | hpRem
        · have hxA := hprefAlpha x hxp
          have hxS : isNameStartChar x = true := by simp [isNameStartChar, hxA]
          refine ⟨isNameChar_of_isNameStartChar hxS, ?_⟩
          intro rfl; cases hxA
        · have hxAN := (hremAll p hpRem).2 x hxp
          simp only [isAsciiAlnum, Bool.or_eq_true] at hxAN
          rcases hxAN with hxA | hxD
          · have hxS : isNameStartChar x = true := by simp [isNameStartChar, hxA]
            refine ⟨isNameChar_of_isNameStartChar hxS, ?_⟩
            intro rfl; cases hxA
          · refine ⟨by simp [isNameChar, hxD], ?_⟩
            intro rfl; cases hxD
    have hname : isName s = true := by
      unfold isName
      rw [htailEq]
      simp only [Bool.and_eq_true, List.all_eq_true]
      exact ⟨hcStart, fun x hx => (hallChar x (htailEq ▸ List.mem_cons_of_mem _ hx)).1⟩
    simp [isNCName, hname]
    exact fun h => (hallChar ':' h).2 rfl

theorem isLanguageTag_false_of_head {c : Char} {tail : List Char}
    (hc : isAsciiAlpha c = false) : isLanguageTag (String.ofList (c :: tail)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold isLanguageTag splitOnChar at h
  rw [String.toList_ofList] at h
  obtain ⟨⟨pref, rem, hp, _, hs⟩, _⟩ := splitOnChar_go_spec '-' (c :: tail) []
  simp only [List.reverse_nil, List.nil_append] at hp
  rw [hp] at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have hpos := h.1.1.1
  have hall := h.1.2
  cases pref with
  | nil => simp at hpos
  | cons lead rest =>
    have he : c = lead := by
      rcases hs with hs | ⟨suffix, hs⟩
      · exact (List.cons.inj hs).1
      · exact (List.cons.inj hs).1
    subst lead
    have ha := hall c (List.mem_cons_self ..)
    rw [hc] at ha
    cases ha

private theorem hasDoubleSpace_iff (cs : List Char) :
    isToken.hasDoubleSpace cs = true ↔ ∃ u v, cs = u ++ ' ' :: ' ' :: v := by
  induction cs with
  | nil => simp [isToken.hasDoubleSpace]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [isToken.hasDoubleSpace, Bool.false_eq_true, false_iff, not_exists]
      intro u v h
      have hl := congrArg List.length h
      simp at hl
      omega
    | cons b tail =>
      by_cases hab : a = ' ' ∧ b = ' '
      · rcases hab with ⟨rfl, rfl⟩
        simp only [isToken.hasDoubleSpace, true_iff]
        exact ⟨[], tail, rfl⟩
      · have hstep : isToken.hasDoubleSpace (a :: b :: tail) = isToken.hasDoubleSpace (b :: tail) := by
          rw [isToken.hasDoubleSpace.eq_def]
          split
          · rename_i _ heq
            obtain ⟨h1, h2⟩ := List.cons.inj heq
            exact (hab ⟨h1, (List.cons.inj h2).1⟩).elim
          · rename_i _ _ _ heq
            rw [(List.cons.inj heq).2]
          · rename_i heq; cases heq
        rw [hstep, ih]
        constructor
        · rintro ⟨u, v, heq⟩
          exact ⟨a :: u, v, by simpa using congrArg (a :: ·) heq⟩
        · rintro ⟨u, v, heq⟩
          cases u with
          | nil =>
            obtain ⟨ha, hrest⟩ := List.cons.inj heq
            obtain ⟨hb, _⟩ := List.cons.inj hrest
            exact (hab ⟨ha, hb⟩).elim
          | cons x u' =>
            obtain ⟨_, hrest⟩ := List.cons.inj heq
            exact ⟨u', v, hrest⟩

private theorem getLastD_eq_iff {α : Type} (c : α) (rest : List α) (x : α) :
    rest.getLastD c = x ↔ ∃ u, c :: rest = u ++ [x] := by
  induction rest generalizing c with
  | nil =>
    simp only [List.getLastD_nil]
    constructor
    · rintro rfl; exact ⟨[], rfl⟩
    · rintro ⟨u, hu⟩
      cases u with
      | nil => exact (List.cons.inj hu).1
      | cons a u' =>
        have hl := congrArg List.length hu
        simp at hl
  | cons b tail ih =>
    simp only [List.getLastD_cons]
    rw [ih b]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨c :: u, by simpa using congrArg (c :: ·) hu⟩
    · rintro ⟨u, hu⟩
      cases u with
      | nil =>
        have hl := congrArg List.length hu
        simp at hl
      | cons a u' =>
        exact ⟨u', (List.cons.inj hu).2⟩

theorem isToken_iff (s : String) :
    isToken s = true ↔
      isNormalizedString s = true ∧
      (∀ t, s.toList ≠ ' ' :: t) ∧
      (∀ u, s.toList ≠ u ++ [' ']) ∧
      (∀ u v, s.toList ≠ u ++ ' ' :: ' ' :: v) := by
  unfold isToken
  simp only [Bool.and_eq_true]
  refine and_congr Iff.rfl ?_
  cases h : s.toList with
  | nil =>
    simp only [true_iff]
    refine ⟨(fun t ht => by cases ht), fun u hu => ?_, fun u v huv => ?_⟩
    · have hl := congrArg List.length hu; simp at hl
    · have hl := congrArg List.length huv; simp at hl
  | cons c rest =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      Bool.eq_false_iff, hasDoubleSpace_iff, not_exists, getLastD_eq_iff]
    constructor
    · rintro ⟨⟨hc, hlast⟩, hds⟩
      exact ⟨fun t ht => hc (List.cons.inj ht).1, hlast, hds⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun he => h1 rest (he ▸ rfl), h2⟩, h3⟩

def isAsciiAlphaChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isAsciiAlnumChar (c : Char) : Bool :=
  isAsciiAlphaChar c || ('0' ≤ c && c ≤ '9')

private theorem splitOnChar_go_reconstruct (cs cur : List Char) :
    ∃ p ps, splitOnChar.go '-' cs cur = p :: ps ∧
      cur.reverse ++ cs = p ++ ps.flatMap ('-' :: ·) := by
  induction cs generalizing cur with
  | nil =>
    exact ⟨cur.reverse, [], by simp [splitOnChar.go]⟩
  | cons c rest ih =>
    by_cases hc : c = '-'
    · subst hc
      obtain ⟨q, qs, hgo, hrec⟩ := ih []
      simp only [List.reverse_nil, List.nil_append] at hrec
      refine ⟨cur.reverse, q :: qs, by simp [splitOnChar.go, hgo], ?_⟩
      simp [List.flatMap_cons, ← hrec]
    · have hbeq : (c == '-') = false := beq_false_of_ne hc
      obtain ⟨p, ps, hgo, hrec⟩ := ih (c :: cur)
      refine ⟨p, ps, by simp [splitOnChar.go, hbeq, hgo], ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using hrec

private theorem splitOnChar_go_no_sep (u v cur : List Char) (hno : ∀ c ∈ u, c ≠ '-') :
    splitOnChar.go '-' (u ++ v) cur = splitOnChar.go '-' v (u.reverse ++ cur) := by
  induction u generalizing cur with
  | nil => simp
  | cons c rest ih =>
    have hc : (c == '-') = false := beq_false_of_ne (hno c (List.mem_cons_self ..))
    simp only [List.cons_append, splitOnChar.go, hc, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: cur) (fun x hx => hno x (List.mem_cons_of_mem _ hx))]
    simp [List.reverse_cons, List.append_assoc]

private theorem splitOnChar_go_of_parts (first : List Char) (rest : List (List Char))
    (cur : List Char)
    (hf : ∀ c ∈ first, c ≠ '-')
    (hr : ∀ p ∈ rest, ∀ c ∈ p, c ≠ '-') :
    splitOnChar.go '-' (first ++ rest.flatMap ('-' :: ·)) cur =
      (cur.reverse ++ first) :: rest := by
  induction rest generalizing first cur with
  | nil =>
    simp only [List.flatMap_nil]
    rw [splitOnChar_go_no_sep first [] cur hf]
    simp [splitOnChar.go]
  | cons q qs ih =>
    simp only [List.flatMap_cons]
    rw [splitOnChar_go_no_sep first _ cur hf]
    simp only [List.cons_append, splitOnChar.go, beq_self_eq_true, ↓reduceIte,
      List.reverse_append, List.reverse_reverse]
    have hq := hr q (List.mem_cons_self ..)
    have hqs : ∀ p ∈ qs, ∀ c ∈ p, c ≠ '-' := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    simpa using ih q [] hq hqs

theorem isLanguageTag_iff (s : String) :
    isLanguageTag s = true ↔
      ∃ (first : List Char) (rest : List (List Char)),
        s.toList = first ++ rest.flatMap ('-' :: ·) ∧
        (1 ≤ first.length ∧ first.length ≤ 8 ∧ ∀ c ∈ first, isAsciiAlphaChar c = true) ∧
        (∀ p ∈ rest, 1 ≤ p.length ∧ p.length ≤ 8 ∧ ∀ c ∈ p, isAsciiAlnumChar c = true) := by
  unfold isLanguageTag splitOnChar
  constructor
  · intro h
    obtain ⟨p, ps, hgo, hrec⟩ := splitOnChar_go_reconstruct s.toList []
    rw [hgo] at h
    simp only [List.reverse_nil, List.nil_append] at hrec
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, ha⟩, hrest⟩ := h
    refine ⟨p, ps, hrec, ⟨h1, h2, ha⟩, fun q hq => ?_⟩
    obtain ⟨⟨q1, q2⟩, qa⟩ := hrest q hq
    exact ⟨q1, q2, qa⟩
  · rintro ⟨first, rest, hs, ⟨h1, h2, ha⟩, hrest⟩
    have hnf : ∀ c ∈ first, c ≠ '-' := fun c hc he => by
      subst he; have := ha '-' hc; cases this
    have hnr : ∀ p ∈ rest, ∀ c ∈ p, c ≠ '-' := fun p hp c hc he => by
      subst he; have := (hrest p hp).2.2 '-' hc; cases this
    rw [hs, splitOnChar_go_of_parts first rest [] hnf hnr]
    simp only [List.reverse_nil, List.nil_append, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, ha⟩,
      fun q hq => ⟨⟨decide_eq_true (hrest q hq).1, decide_eq_true (hrest q hq).2.1⟩, (hrest q hq).2.2⟩⟩

private def languageWitnessChars : Nat → List Char
  | 0 => ['a']
  | n + 1 => 'a' :: '-' :: languageWitnessChars n

def languageWitness (n : Nat) : String := String.ofList (languageWitnessChars n)

theorem languageWitness_length (n : Nat) : (languageWitness n).length = 2 * n + 1 := by
  simp only [languageWitness, String.length, String.toList_ofList]
  induction n with
  | zero => rfl
  | succ n ih => simp only [languageWitnessChars, List.length_cons, ih]; omega

theorem isLanguageTag_languageWitness (n : Nat) : isLanguageTag (languageWitness n) = true := by
  have hparts : splitOnChar '-' (languageWitnessChars n) = List.replicate (n + 1) ['a'] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change ['a'] :: splitOnChar '-' (languageWitnessChars n) = _
      rw [ih]
      rfl
  unfold isLanguageTag languageWitness
  rw [String.toList_ofList, hparts, List.replicate_succ]
  simp only [List.length_cons, List.length_nil, List.all_cons, List.all_nil, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by decide, ?_⟩
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  decide

/-! ### Character profiles for string datatype counting -/

private def isStringControl (c : Char) : Bool := c == '\r' || c == '\n' || c == '\t'

/-- Characters with the same representative have the same contribution to
the string subtype tests. The whitespace controls form one class. -/
def stringCharacterProfile (c : Char) : Char :=
  if isAsciiAlpha c then 'a'
  else if '0' ≤ c ∧ c ≤ '9' then '0'
  else if c = '_' then '_'
  else if c = ':' then ':'
  else if c = '-' then '-'
  else if c = '.' then '.'
  else if c = ' ' then ' '
  else if isStringControl c then '\t'
  else if XMLNames.inRanges XMLNames.highStarts c.toNat then 'À'
  else if XMLNames.inRanges XMLNames.highExtras c.toNat then '·'
  else '!'

def stringCharacterProfiles : List Char := ['a', '0', '_', ':', '-', '.', ' ', '\t', 'À', '·', '!']

theorem stringCharacterProfile_mem (c : Char) : stringCharacterProfile c ∈ stringCharacterProfiles := by
  unfold stringCharacterProfile
  repeat first | split | decide

private theorem charFacts (c : Char) :
    let p := stringCharacterProfile c
    (isAsciiAlpha p = isAsciiAlpha c) ∧
    (isAsciiAlnum p = isAsciiAlnum c) ∧
    (isNameStartChar p = isNameStartChar c) ∧
    (isNameChar p = isNameChar c) ∧
    ((p == ':') = (c == ':')) ∧
    ((p == '-') = (c == '-')) ∧
    ((p == ' ') = (c == ' ')) ∧
    ((p != '\r' && p != '\n' && p != '\t') = (c != '\r' && c != '\n' && c != '\t')) := by
  dsimp only
  generalize hp : stringCharacterProfile c = p
  unfold stringCharacterProfile at hp
  repeat' split at hp
  all_goals
    subst p
    simp_all [isAsciiAlpha, isAsciiAlnum, isNameStartChar, isNameChar, isStringControl,
      Char.le_def, UInt32.le_iff_toNat_le, ← Char.toNat_inj] <;>
    (try have hlow : c.toNat < 128 := by omega) <;>
    (try simp_all [XMLNames.highStarts_low, XMLNames.highExtras_low, ← Char.toNat_inj,
      show XMLNames.inRanges XMLNames.highStarts 183 = false by decide,
      show XMLNames.inRanges XMLNames.highExtras 183 = true by decide]) <;>
    first | decide | omega

theorem stringCharacterProfile_high (c : Char) (h : 128 ≤ c.toNat) :
    stringCharacterProfile c =
      if XMLNames.inRanges XMLNames.highStarts c.toNat then 'À'
      else if XMLNames.inRanges XMLNames.highExtras c.toNat then '·' else '!' := by
  simp [stringCharacterProfile, isAsciiAlpha, isStringControl, Char.le_def, UInt32.le_iff_toNat_le]
  have ne (a : Char) (ha : a.toNat < 128) : c ≠ a := fun e => by
    have := congrArg Char.toNat e
    omega
  simp [show ¬ c.toNat ≤ 122 by omega, show ¬ c.toNat ≤ 90 by omega, show ¬ c.toNat ≤ 57 by omega,
    ne '_' (by decide), ne ':' (by decide), ne '-' (by decide), ne '.' (by decide),
    ne ' ' (by decide), ne '\r' (by decide), ne '\n' (by decide), ne '\t' (by decide)]

structure StringSubtypeFlags where
  normalized : Bool
  token : Bool
  nameToken : Bool
  name : Bool
  ncname : Bool
  language : Bool

def stringSubtypeFlags (s : String) : StringSubtypeFlags :=
  ⟨isNormalizedString s, isToken s, isNMTOKEN s, isName s, isNCName s, isLanguageTag s⟩

private theorem all_profile (p : Char → Bool)
    (hp : ∀ c, p (stringCharacterProfile c) = p c) (xs : List Char) :
    (xs.map stringCharacterProfile).all p = xs.all p := by
  induction xs <;> simp [*]

private theorem doubleSpace_profile (cs : List Char) :
    isToken.hasDoubleSpace (cs.map stringCharacterProfile) = isToken.hasDoubleSpace cs := by
  have space (c : Char) : stringCharacterProfile c = ' ' ↔ c = ' ' := by
    simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp (charFacts c).2.2.2.2.2.2.1
  induction cs with
  | nil => rfl
  | cons c tail ih =>
    cases tail with
    | nil => simp [isToken.hasDoubleSpace]
    | cons d ds =>
      have step (x y : Char) (ys : List Char) :
          isToken.hasDoubleSpace (x :: y :: ys) =
            if x = ' ' ∧ y = ' ' then true else isToken.hasDoubleSpace (y :: ys) := by
        by_cases hx : x = ' ' <;> by_cases hy : y = ' ' <;>
          simp [isToken.hasDoubleSpace, hx, hy]
      exact (by
        simp only [List.map_cons, step, space]
        split <;> simp_all)

private theorem splitOnChar_profile (xs cur : List Char) :
    splitOnChar.go '-' (xs.map stringCharacterProfile) (cur.map stringCharacterProfile) =
      (splitOnChar.go '-' xs cur).map (List.map stringCharacterProfile) := by
  induction xs generalizing cur with
  | nil => simp [splitOnChar.go, List.map_reverse]
  | cons c xs ih =>
    simp only [List.map_cons, splitOnChar.go, (charFacts c).2.2.2.2.2.1]
    split
    · simp only [List.map_reverse, List.map_cons, List.cons.injEq, true_and]
      exact ih []
    · exact ih (c :: cur)

private theorem languageTag_profile (xs : List Char) :
    isLanguageTag (String.ofList (xs.map stringCharacterProfile)) =
      isLanguageTag (String.ofList xs) := by
  simp only [isLanguageTag, String.toList_ofList, splitOnChar]
  rw [show splitOnChar.go '-' (List.map stringCharacterProfile xs) [] = _ from splitOnChar_profile xs []]
  cases splitOnChar.go '-' xs [] with
  | nil => rfl
  | cons x xs =>
    simp only [List.map_cons, List.length_map]
    rw [all_profile isAsciiAlpha (fun c => (charFacts c).1)]
    congr 1
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, List.all_cons, List.length_map,
        all_profile isAsciiAlnum (fun c => (charFacts c).2.1), ih]

theorem stringSubtypeFlags_profile (xs : List Char) :
    stringSubtypeFlags (String.ofList (xs.map stringCharacterProfile)) =
      stringSubtypeFlags (String.ofList xs) := by
  have nameChars := all_profile isNameChar (fun c => (charFacts c).2.2.2.1)
  have normal : isNormalizedString (String.ofList (xs.map stringCharacterProfile)) =
      isNormalizedString (String.ofList xs) := by
    simp only [isNormalizedString, String.toList_ofList]
    exact all_profile _ (fun c => (charFacts c).2.2.2.2.2.2.2) xs
  have name : isName (String.ofList (xs.map stringCharacterProfile)) =
      isName (String.ofList xs) := by
    cases xs with
    | nil => rfl
    | cons c tail =>
      simp only [isName, String.toList_ofList, List.map_cons, (charFacts c).2.2.1, nameChars]
  have colon : (xs.map stringCharacterProfile).contains ':' = xs.contains ':' := by
    have fact (c : Char) : (':' == stringCharacterProfile c) = (':' == c) := by
      have h := Bool.eq_iff_iff.mp (charFacts c).2.2.2.2.1
      simpa only [beq_iff_eq, eq_comm (a := ':')] using Bool.eq_iff_iff.mpr
        (show (':' == stringCharacterProfile c) = true ↔ (':' == c) = true by
          simpa only [beq_iff_eq, eq_comm (a := ':')] using h)
    clear name normal nameChars
    simp only [List.contains_eq_any_beq]
    induction xs with
    | nil => rfl
    | cons c tail ih => simp only [List.map_cons, List.any_cons, fact, ih]
  have ncname : isNCName (String.ofList (xs.map stringCharacterProfile)) =
      isNCName (String.ofList xs) := by
    simp only [isNCName, name, String.toList_ofList, colon]
  have nmtok : isNMTOKEN (String.ofList (xs.map stringCharacterProfile)) =
      isNMTOKEN (String.ofList xs) := by
    have eq : (String.ofList (xs.map stringCharacterProfile)).isEmpty = (String.ofList xs).isEmpty := by
      rw [Bool.eq_iff_iff, String.isEmpty_iff, String.isEmpty_iff]
      constructor <;> intro h <;> have hh := congrArg String.toList h <;>
        simp_all [← String.toList_inj]
    simp only [isNMTOKEN, String.toList_ofList, nameChars, eq]
  have tok : isToken (String.ofList (xs.map stringCharacterProfile)) =
      isToken (String.ofList xs) := by
    simp only [isToken, normal, String.toList_ofList]
    cases xs with
    | nil => rfl
    | cons c tail =>
      simp only [List.map_cons, List.getLastD_map, bne, (charFacts c).2.2.2.2.2.2.1,
        (charFacts (tail.getLastD c)).2.2.2.2.2.2.1,
        show isToken.hasDoubleSpace (stringCharacterProfile c :: tail.map stringCharacterProfile) =
          isToken.hasDoubleSpace (c :: tail) from doubleSpace_profile (c :: tail)]
  simp only [stringSubtypeFlags, normal, tok, nmtok, name, ncname, languageTag_profile]

theorem stringSubtypeFlags_eq_of_profile {xs ys : List Char}
    (h : xs.map stringCharacterProfile = ys.map stringCharacterProfile) :
    stringSubtypeFlags (String.ofList xs) = stringSubtypeFlags (String.ofList ys) := by
  rw [← stringSubtypeFlags_profile xs, ← stringSubtypeFlags_profile ys, h]

/-- Parse `rdf:PlainLiteral` lexical form `text@langTag`. Per W3C rdf:PlainLiteral,
the language tag is lowercased; an empty tag denotes the same value as `xsd:string`. -/
def parsePlainLiteral (raw : String) : Option (String × String) :=
  let rev := raw.toList.reverse
  match rev.span (· != '@') with
  | (_, []) => none
  | (revLang, _ :: revText) =>
    let text := String.ofList revText.reverse
    let lang := String.ofList (revLang.reverse.map Char.toLower)
    if lang.isEmpty || isLanguageTag lang then some (text, lang) else none

/-! Binary datatypes: `xsd:hexBinary` and `xsd:base64Binary`. -/

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def parseHexBinary (raw : String) : Option (List UInt8) :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
      let h ← hexNibble hi
      let l ← hexNibble lo
      let tail ← go rest
      return UInt8.ofNat (h * 16 + l) :: tail
  go raw.toList

private def base64Val (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (26 + c.toNat - 'a'.toNat)
  else if '0' ≤ c && c ≤ '9' then some (52 + c.toNat - '0'.toNat)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

def parseBase64Binary (raw : String) : Option (List UInt8) :=
  let chars := raw.toList.filter fun c => c != ' ' && c != '\n' && c != '\r' && c != '\t'
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | [c1, c2, '=', '='] => do
      let v1 ← base64Val c1
      let v2 ← base64Val c2
      if v2 % 16 != 0 then none
      else some [UInt8.ofNat (v1 * 4 + v2 / 16)]
    | [c1, c2, c3, '='] => do
      let v1 ← base64Val c1
      let v2 ← base64Val c2
      let v3 ← base64Val c3
      if v3 % 4 != 0 then none
      else some [
        UInt8.ofNat (v1 * 4 + v2 / 16),
        UInt8.ofNat ((v2 % 16) * 16 + v3 / 4)
      ]
    | c1 :: c2 :: c3 :: c4 :: rest => do
      let v1 ← base64Val c1
      let v2 ← base64Val c2
      let v3 ← base64Val c3
      let v4 ← base64Val c4
      let tail ← go rest
      return UInt8.ofNat (v1 * 4 + v2 / 16) ::
        UInt8.ofNat ((v2 % 16) * 16 + v3 / 4) ::
        UInt8.ofNat ((v3 % 4) * 64 + v4) :: tail
    | _ => none
  go chars

/-! Date/time datatypes: `xsd:dateTime` and `xsd:dateTimeStamp`. -/

/-- UTC seconds for a zoned value, local seconds otherwise. The signed offset
is retained in seconds because XSD value identity includes the timezone. -/
structure DateTimeVal where
  epochSeconds : Rat
  timezoneOffset : Option Int
  deriving DecidableEq, Repr

def DateTimeVal.hasTimezone (dt : DateTimeVal) : Bool := dt.timezoneOffset.isSome

/-- Offsets are whole minutes in the inclusive ±14 hour interval. -/
def validTimezoneOffset (offset : Option Int) : Prop :=
  match offset with
  | none => True
  | some o => -50400 ≤ o ∧ o ≤ 50400 ∧ o % 60 = 0

instance (offset : Option Int) : Decidable (validTimezoneOffset offset) := by
  cases offset <;> unfold validTimezoneOffset <;> infer_instance

def DateTimeVal.valid (dt : DateTimeVal) : Prop :=
  DecimalValue dt.epochSeconds ∧ validTimezoneOffset dt.timezoneOffset

instance (dt : DateTimeVal) : Decidable dt.valid := by
  unfold DateTimeVal.valid
  infer_instance

def dateTimeOffsets : List (Option Int) :=
  none :: (List.range 1681).map fun n : Nat => some (((n : Int) - 840) * 60)

theorem mem_dateTimeOffsets_iff (offset : Option Int) :
    offset ∈ dateTimeOffsets ↔ validTimezoneOffset offset := by
  cases offset with
  | none => simp [dateTimeOffsets, validTimezoneOffset]
  | some o =>
    simp only [dateTimeOffsets, List.mem_cons, List.mem_map, List.mem_range,
      Option.some_ne_none, false_or, Option.some.injEq, validTimezoneOffset]
    constructor
    · rintro ⟨n, hn, rfl⟩
      omega
    · rintro ⟨hl, hh, hm⟩
      refine ⟨(o / 60 + 840).toNat, ?_, ?_⟩ <;> omega

private def isLeapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0)

private def daysInMonth (y : Int) (m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

/-- Howard Hinnant's exact civil-from-days formula (days since 1970-01-01). -/
private def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y' : Int := if m ≤ 2 then y - 1 else y
  let era : Int := Int.ediv y' 400
  let yoe : Int := y' - era * 400
  let m' : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy : Int := (153 * m' + 2) / 5 + (d : Int) - 1
  let doe : Int := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

private def parseNatDigits (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all (fun c => '0' ≤ c && c ≤ '9') then none
  else some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)

private def digitVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none

private def parseTwoChars (a b : Char) : Option Nat := do
  let d1 ← digitVal a
  let d2 ← digitVal b
  some (d1 * 10 + d2)

private def parseTzSuffix : List Char → Option (Option Int)
  | [] => some none
  | ['Z'] => some (some 0)
  | [sign, h1, h2, ':', m1, m2] => do
    if sign != '+' && sign != '-' then none
    let h ← parseTwoChars h1 h2
    let m ← parseTwoChars m1 m2
    if h > 14 || m ≥ 60 || (h == 14 && m > 0) then none
    else
      let seconds : Int := Int.ofNat (h * 3600 + m * 60)
      some (some (if sign == '-' then -seconds else seconds))
  | _ => none

/-- Fast kernel-friendly ASCII decoding: a UTF-8 string is pure ASCII iff every
byte is `< 128`, in which case its characters are `Char.ofNat b.toNat`. -/
private def asciiChars? (raw : String) : Option (List Char) :=
  let bytes := raw.toByteArray.data.toList
  if bytes.all (·.toNat < 128) then some (bytes.map fun b => Char.ofNat b.toNat)
  else none

/-- Parse ISO-8601 `xsd:dateTime` / `xsd:dateTimeStamp` lexical forms:
`(-)?YYYY-MM-DDThh:mm:ss(.fff)?(Z|(+|-)hh:mm)?`. -/
def parseDateTime (requireTz : Bool) (raw : String) : Option DateTimeVal := do
  let chars ← asciiChars? raw
  let (negYear, rest) := match chars with
    | '-' :: r => (true, r)
    | _ => (false, chars)
  let (yearChars, afterYear) ← match rest.span (· != '-') with
    | (y, '-' :: r) => some (y, r)
    | _ => none
  if yearChars.length < 4 then none
  if yearChars.length > 4 && yearChars.head? == some '0' then none
  let yNat ← parseNatDigits yearChars
  let year : Int := if negYear then -(yNat : Int) else (yNat : Int)
  let (month, day, hour, minute, sec, fracAndTz) ← match afterYear with
    | mo1 :: mo2 :: '-' :: d1 :: d2 :: 'T' :: h1 :: h2 :: ':' :: m1 :: m2 :: ':' :: s1 :: s2 :: tail => do
      let mo ← parseTwoChars mo1 mo2
      let dy ← parseTwoChars d1 d2
      let hr ← parseTwoChars h1 h2
      let mn ← parseTwoChars m1 m2
      let sc ← parseTwoChars s1 s2
      some (mo, dy, hr, mn, sc, tail)
    | _ => none
  if month < 1 || month > 12 || day < 1 || day > daysInMonth year month then none
  if hour > 24 || minute ≥ 60 || sec ≥ 60 then none
  let (fracNum, fracDen, tzChars) ← match fracAndTz with
    | '.' :: r =>
      let (fDigits, tz) := r.span (fun c => '0' ≤ c && c ≤ '9')
      match parseNatDigits fDigits with
      | none => none
      | some fVal => some ((fVal : Int), 10 ^ fDigits.length, tz)
    | tz => some ((0 : Int), 1, tz)
  if hour == 24 && (minute != 0 || sec != 0 || fracNum != 0) then none
  let offset ← parseTzSuffix tzChars
  if requireTz && offset.isNone then none
  let days := daysFromCivil year month day
  let daySec : Nat := hour * 3600 + minute * 60 + sec
  let totalSec : Int := days * 86400 + Int.ofNat daySec - offset.getD 0
  let epoch : Rat := if fracDen == 1 then Rat.ofInt totalSec
    else mkRat (totalSec * (fracDen : Int) + fracNum) fracDen
  some ⟨epoch, offset⟩

/-- For mixed zoned and local values, strict order must hold under every
permitted offset for the local value. The extreme offsets are ±14 hours. -/
def DateTimeVal.lt (a b : DateTimeVal) : Bool :=
  match a.timezoneOffset, b.timezoneOffset with
  | some _, none => decide (a.epochSeconds < b.epochSeconds - 50400)
  | none, some _ => decide (a.epochSeconds + 50400 < b.epochSeconds)
  | _, _ => decide (a.epochSeconds < b.epochSeconds)

def DateTimeVal.le (a b : DateTimeVal) : Bool :=
  if a.hasTimezone == b.hasTimezone then decide (a.epochSeconds ≤ b.epochSeconds)
  else a.lt b

/-! ## `rdf:langRange` (RFC 4647 Basic Filtering) and `xsd:pattern` (Brzozowski Regex) -/

def toLowerAscii (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def listStartsWith {α : Type} [BEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, s :: ss => p == s && listStartsWith ps ss

/-- RFC 4647 basic language-range matching for `rdf:langRange` on `rdf:PlainLiteral`. -/
def matchesLangRange (pat lang : String) : Bool :=
  let pl := pat.toList.map toLowerAscii
  let ll := lang.toList.map toLowerAscii
  if pl == ['*'] then !ll.isEmpty
  else if pl.isEmpty then false
  else ll == pl || listStartsWith (pl ++ ['-']) ll

/-- Character tests are data so automata can identify residual states by
structural equality. -/
inductive PatternClass where
  | empty
  | interval (lo hi : Char)
  | nameStart | nameChar | space | word
  | union (a b : PatternClass)
  | neg (a : PatternClass)
  | lowerASCII (a : PatternClass)
  deriving DecidableEq

def PatternClass.accepts (p : PatternClass) (c : Char) : Bool :=
  match p with
  | .empty => false
  | .interval lo hi => lo ≤ c && c ≤ hi
  | .nameStart => isNameStartChar c
  | .nameChar => isNameChar c
  | .space => c == ' ' || c == '\t' || c == '\n' || c == '\r'
  | .word => c.isAlphanum || c == '_'
  | .union a b => a.accepts c || b.accepts c
  | .neg a => !a.accepts c
  | .lowerASCII a => a.accepts (toLowerAscii c)

inductive Regex where
  | empty
  | eps
  | any
  | pred (p : PatternClass)
  | seq (a b : Regex)
  | alt (a b : Regex)
  | star (r : Regex)
  deriving DecidableEq

def Regex.nullable : Regex → Bool
  | .empty => false
  | .eps => true
  | .any => false
  | .pred _ => false
  | .seq a b => a.nullable && b.nullable
  | .alt a b => a.nullable || b.nullable
  | .star _ => true

def Regex.mkSeq : Regex → Regex → Regex
  | .empty, _ | _, .empty => .empty
  | .eps, b => b
  | a, .eps => a
  | a, b => .seq a b

def Regex.mkAlt : Regex → Regex → Regex
  | .empty, b => b
  | a, .empty => a
  | a, b => .alt a b

def Regex.deriv (c : Char) : Regex → Regex
  | .empty | .eps => .empty
  | .any => if c == '\n' || c == '\r' then .empty else .eps
  | .pred p => if p.accepts c then .eps else .empty
  | .seq a b =>
    let d1 := Regex.mkSeq (a.deriv c) b
    if a.nullable then Regex.mkAlt d1 (b.deriv c) else d1
  | .alt a b => Regex.mkAlt (a.deriv c) (b.deriv c)
  | .star r => Regex.mkSeq (r.deriv c) (.star r)

private def parseEscape (c : Char) : PatternClass :=
  match c with
  | 'i' => .nameStart
  | 'I' => .neg .nameStart
  | 'c' => .nameChar
  | 'C' => .neg .nameChar
  | 'd' => .interval '0' '9'
  | 'D' => .neg (.interval '0' '9')
  | 'w' => .word
  | 'W' => .neg .word
  | 's' => .space
  | 'S' => .neg .space
  | 'n' => .interval '\n' '\n'
  | 'r' => .interval '\r' '\r'
  | 't' => .interval '\t' '\t'
  | ch => .interval ch ch

private def parseCharClass (cs : List Char) : Option (PatternClass × List Char) :=
  let (neg, rest) := match cs with | '^' :: t => (true, t) | t => (false, t)
  let rec go (acc : PatternClass) : List Char → Option (PatternClass × List Char)
    | [] => none
    | ']' :: t => some (if neg then .neg acc else acc, t)
    | '\\' :: c :: t => go (.union acc (parseEscape c)) t
    | c1 :: '-' :: c2 :: t =>
      if c2 == ']' then
        let acc' := .union (.union acc (.interval c1 c1)) (.interval '-' '-')
        some (if neg then .neg acc' else acc', t)
      else go (.union acc (.interval c1 c2)) t
    | c :: t => go (.union acc (.interval c c)) t
  go .empty rest

private def repeatRegex (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => Regex.mkSeq r (repeatRegex r n)

private def repeatUpTo (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => Regex.mkAlt .eps (Regex.mkSeq r (repeatUpTo r n))

private def parseQuantDigits (cs : List Char) : Option (Nat × List Char) :=
  let (ds, rest) := cs.span (fun c => '0' ≤ c && c ≤ '9')
  match parseNatDigits ds with
  | some n => some (n, rest)
  | none => none

private def parseRegexFuel : Nat → List Char → Option (Regex × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    let rec parseSeq : Nat → List Char → Option (Regex × List Char)
      | 0, _ => none
      | sf + 1, s =>
        match s with
        | [] | ')' :: _ | '|' :: _ => some (.eps, s)
        | _ =>
          let step0 : Option (Regex × List Char) := match s with
            | '(' :: t =>
              match parseRegexFuel fuel t with
              | some (inner, ')' :: t2) => some (inner, t2)
              | _ => none
            | '[' :: t =>
              match parseCharClass t with
              | some (p, rem) => some (.pred p, rem)
              | none => none
            | '\\' :: c :: t => some (.pred (parseEscape c), t)
            | '.' :: t => some (.any, t)
            | c :: t => some (.pred (.interval c c), t)
            | [] => none
          match step0 with
          | none => none
          | some (base, rest0) =>
            let step1 : Option (Regex × List Char) := match rest0 with
              | '*' :: t => some (.star base, t)
              | '+' :: t => some (Regex.mkSeq base (.star base), t)
              | '?' :: t => some (Regex.mkAlt .eps base, t)
              | '{' :: t =>
                match parseQuantDigits t with
                | some (n, '}' :: t2) => some (repeatRegex base n, t2)
                | some (n, ',' :: '}' :: t2) => some (Regex.mkSeq (repeatRegex base n) (.star base), t2)
                | some (n, ',' :: t2) =>
                  match parseQuantDigits t2 with
                  | some (m, '}' :: t3) =>
                    if n ≤ m then some (Regex.mkSeq (repeatRegex base n) (repeatUpTo base (m - n)), t3)
                    else none
                  | _ => none
                | _ => none
              | _ => some (base, rest0)
            match step1 with
            | none => none
            | some (atom, rest) =>
              match parseSeq sf rest with
              | some (tail, rem) => some (Regex.mkSeq atom tail, rem)
              | none => none
    match parseSeq (fuel + 1) cs with
    | none => none
    | some (first, rest) =>
      match rest with
      | '|' :: t =>
        match parseRegexFuel fuel t with
        | some (rhs, rem) => some (Regex.mkAlt first rhs, rem)
        | none => none
      | _ => some (first, rest)

/-- The XSD name expressions that lower directly to datatype ranges. -/
inductive NamePattern where
  | startChar
  | nameChar
  | name
  | nmtoken

def NamePattern.source : NamePattern → String
  | .startChar => "\\i"
  | .nameChar => "\\c"
  | .name => "\\i\\c*"
  | .nmtoken => "\\c+"

def parseNamePattern (s : String) : Option { p : NamePattern // s = p.source } :=
  if h : s = NamePattern.startChar.source then some ⟨.startChar, h⟩
  else if h : s = NamePattern.nameChar.source then some ⟨.nameChar, h⟩
  else if h : s = NamePattern.name.source then some ⟨.name, h⟩
  else if h : s = NamePattern.nmtoken.source then some ⟨.nmtoken, h⟩
  else none

private def NamePattern.regex : NamePattern → Regex
  | .startChar => .pred .nameStart
  | .nameChar => .pred .nameChar
  | .name => .seq (.pred .nameStart) (.star (.pred .nameChar))
  | .nmtoken => .seq (.pred .nameChar) (.star (.pred .nameChar))

def parseCompleteRegex (pat : String) : Option Regex :=
  match parseNamePattern pat with
  | some p => some p.1.regex
  | none =>
    let cs := pat.toList
    match parseRegexFuel (cs.length * 4 + 16) cs with
    | some (re, []) => some re
    | _ => none

/-- Anchored matching for the implemented regex syntax, via Brzozowski derivatives. -/
def matchesPattern (pat s : String) : Bool :=
  match parseCompleteRegex pat with
  | some re => (s.toList.foldl (fun r c => r.deriv c) re).nullable
  | none => false

private theorem parseCompleteRegex_namePattern (p : NamePattern) :
    parseCompleteRegex p.source = some p.regex := by
  cases p <;> rfl

def NamePattern.holds : NamePattern → String → Prop
  | .startChar, s => s.length = 1 ∧ XMLNames.Name s.toList
  | .nameChar, s => s.length = 1 ∧ XMLNames.Nmtoken s.toList
  | .name, s => XMLNames.Name s.toList
  | .nmtoken, s => XMLNames.Nmtoken s.toList

private theorem Regex.matches_empty (cs : List Char) :
    (cs.foldl (fun r c => r.deriv c) Regex.empty).nullable = false := by
  induction cs <;> simp_all [Regex.deriv, Regex.nullable]

private theorem Regex.matches_pred (p : PatternClass) (cs : List Char) :
    (cs.foldl (fun r c => r.deriv c) (Regex.pred p)).nullable =
      (match cs with | [c] => p.accepts c | _ => false) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    cases cs <;> cases h : p.accepts c <;>
      simp [Regex.deriv, Regex.nullable, h, Regex.matches_empty]

private theorem Regex.matches_star_pred (p : PatternClass) (cs : List Char) :
    (cs.foldl (fun r c => r.deriv c) (Regex.star (.pred p))).nullable = cs.all p.accepts := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases h : p.accepts c <;>
      simp [Regex.deriv, Regex.mkSeq, h, Regex.matches_empty, ih]

private theorem Regex.matches_pred_seq_star (p q : PatternClass) (cs : List Char) :
    (cs.foldl (fun r c => r.deriv c) (Regex.seq (.pred p) (.star (.pred q)))).nullable =
      (match cs with | [] => false | c :: tail => p.accepts c && tail.all q.accepts) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    cases h : p.accepts c <;>
      simp [Regex.deriv, Regex.mkSeq, Regex.nullable, h, Regex.matches_empty, Regex.matches_star_pred]

theorem namePattern_matches_iff (p : NamePattern) (s : String) :
    matchesPattern p.source s = true ↔ p.holds s := by
  unfold matchesPattern
  simp only [parseCompleteRegex_namePattern]
  cases p with
  | startChar =>
    rw [NamePattern.regex, Regex.matches_pred, NamePattern.holds, ← isName_iff]
    change _ ↔ s.toList.length = 1 ∧ isName s = true
    cases h : s.toList with
    | nil => simp
    | cons c tail => cases tail <;> simp [isName, h, PatternClass.accepts]
  | nameChar =>
    rw [NamePattern.regex, Regex.matches_pred, NamePattern.holds]
    change _ ↔ s.toList.length = 1 ∧ XMLNames.Nmtoken s.toList
    cases h : s.toList with
    | nil => simp
    | cons c tail => cases tail <;> simp [XMLNames.Nmtoken, PatternClass.accepts, ← isNameChar_iff]
  | name =>
    rw [NamePattern.regex, Regex.matches_pred_seq_star, NamePattern.holds, ← isName_iff]
    rfl
  | nmtoken =>
    rw [NamePattern.regex, Regex.matches_pred_seq_star, NamePattern.holds]
    cases h : s.toList <;> simp [XMLNames.Nmtoken, PatternClass.accepts, ← isNameChar_iff, List.all_eq_true]

private def sampleRegex : Regex → Option (List Char)
  | .empty => none
  | .eps | .star _ => some []
  | .any => some ['a']
  | .pred p =>
    (List.range 128).findSome? fun n =>
      let c := Char.ofNat n
      if p.accepts c then some [c] else none
  | .seq a b =>
    match sampleRegex a, sampleRegex b with
    | some sa, some sb => some (sa ++ sb)
    | _, _ => none
  | .alt a b =>
    match sampleRegex a with
    | some sa => some sa
    | none => sampleRegex b

/-- Synthesize a sample ASCII string matching `pat` when one exists. -/
def samplePattern (pat : String) : Option String :=
  match parseCompleteRegex pat with
  | some re => (sampleRegex re).map String.ofList
  | _ => none

private def samplePredChars (limit : Nat) (p : Char → Bool) : List (List Char) :=
  ((List.range 128).filterMap fun n =>
    let c := Char.ofNat n
    if p c then some [c] else none).take limit

private def combineSeqSamples (limit : Nat) (xs ys : List (List Char)) : List (List Char) :=
  (xs.flatMap fun x => ys.map fun y => x ++ y).take limit

private def sampleRegexMany (limit : Nat) : Regex → List (List Char)
  | .empty => []
  | .eps => [[]]
  | .any =>
    (['a', 'b', 'c', '0', '1', '_'].map fun c => [c]).take (max 1 limit)
  | .pred p => samplePredChars (max 1 limit) p.accepts
  | .seq a b =>
    combineSeqSamples (max 1 limit) (sampleRegexMany limit a) (sampleRegexMany limit b)
  | .alt a b =>
    ((sampleRegexMany limit a) ++ (sampleRegexMany limit b)).take (max 1 limit)
  | .star r =>
    let unit := (sampleRegexMany 4 r).filter (· != [])
    match unit with
    | [] => [[]]
    | u :: rest =>
      let rep1 := (List.range (max 1 limit)).map fun k => (List.replicate k u).flatten
      let rep2 := match rest with
        | u2 :: _ => (List.range (max 1 limit)).map fun k => (List.replicate (k + 1) u2).flatten
        | [] => []
      (rep1 ++ rep2).take (max 1 limit)

/-- Synthesize up to `limit` distinct candidate strings matching `pat`. -/
def samplePatternMany (limit : Nat) (pat : String) : List String :=
  match parseCompleteRegex pat with
  | some re =>
    (((sampleRegexMany (limit + 4) re).map String.ofList).eraseDups).filter (matchesPattern pat)
  | _ => []

/-! ## Normative `rdf:XMLLiteral`: XML 1.0 + Namespaces in XML 1.0 + Exclusive XML Canonicalization (Exc-C14N) -/

/-- W3C XML 1.0 Fifth Edition Production [2] `Char`. -/
def isXML10Char (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xD ||
  (0x20 ≤ n && n ≤ 0xD7FF) ||
  (0xE000 ≤ n && n ≤ 0xFFFD) ||
  (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- W3C XML 1.0 Production [3] `S` (whitespace). -/
def isXMLSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- W3C XML 1.0 Fifth Edition Production [4] `NameStartChar`. -/
def isXMLNameStartChar (c : Char) : Bool := isNameStartChar c

/-- W3C XML 1.0 Fifth Edition Production [4a] `NameChar`. -/
def isXMLNameChar (c : Char) : Bool := isNameChar c

def isXMLNCNameStartChar (c : Char) : Bool :=
  isXMLNameStartChar c && c != ':'

def isXMLNCNameChar (c : Char) : Bool :=
  isXMLNameChar c && c != ':'

def isXMLNCName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isXMLNCNameStartChar c && rest.all isXMLNCNameChar

/-- Namespaces in XML 1.0 Production [7] `QName := PrefixedName | UnprefixedName`. -/
def splitXMLQName (s : String) : Option (Option String × String) :=
  let cs := s.toList
  if !cs.contains ':' then
    if isXMLNCName s then some (none, s) else none
  else
    let (pfxCs, rest) := cs.span (· != ':')
    match rest with
    | ':' :: locCs =>
      let pfx := String.ofList pfxCs
      let loc := String.ofList locCs
      if isXMLNCName pfx && isXMLNCName loc then some (some pfx, loc) else none
    | _ => none

def isXML10Codepoint (n : Nat) : Bool :=
  n == 0x9 || n == 0xA || n == 0xD ||
  (0x20 ≤ n && n ≤ 0xD7FF) ||
  (0xE000 ≤ n && n ≤ 0xFFFD) ||
  (0x10000 ≤ n && n ≤ 0x10FFFF)

private def skipXMLSpaces : List Char → List Char
  | c :: rest => if isXMLSpace c then skipXMLSpaces rest else c :: rest
  | [] => []

private def takeXMLNameChars : List Char → List Char × List Char
  | c :: rest =>
    if isXMLNameChar c then
      let (ns, rem) := takeXMLNameChars rest
      (c :: ns, rem)
    else ([], c :: rest)
  | [] => ([], [])

private def readXMLName : List Char → Option (String × List Char)
  | c :: rest =>
    if isXMLNameStartChar c then
      let (more, rem) := takeXMLNameChars rest
      some (String.ofList (c :: more), rem)
    else none
  | [] => none

private def parseXMLDecNat (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    if '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat then
      parseXMLDecNat (acc * 10 + (c.toNat - '0'.toNat)) rest
    else none

private def xmlHexDigitVal (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then some (10 + c.toNat - 'a'.toNat)
  else if 'A'.toNat ≤ c.toNat && c.toNat ≤ 'F'.toNat then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseXMLHexNat (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    match xmlHexDigitVal c with
    | some d => parseXMLHexNat (acc * 16 + d) rest
    | none => none

private def takeUntilSemi : List Char → Option (List Char × List Char)
  | [] => none
  | ';' :: rest => some ([], rest)
  | c :: rest =>
    (takeUntilSemi rest).map fun (body, rem) => (c :: body, rem)

private def decodeXMLRef (cs : List Char) : Option (Char × List Char) :=
  match takeUntilSemi cs with
  | none => none
  | some (body, rem) =>
    match body with
    | '#' :: 'x' :: hex =>
      if hex.isEmpty then none
      else match parseXMLHexNat 0 hex with
      | some cp =>
        if isXML10Codepoint cp && cp.isValidChar then some (Char.ofNat cp, rem) else none
      | none => none
    | '#' :: dec =>
      if dec.isEmpty then none
      else match parseXMLDecNat 0 dec with
      | some cp =>
        if isXML10Codepoint cp && cp.isValidChar then some (Char.ofNat cp, rem) else none
      | none => none
    | _ =>
      let s := String.ofList body
      if s == "amp" then some ('&', rem)
      else if s == "lt" then some ('<', rem)
      else if s == "gt" then some ('>', rem)
      else if s == "quot" then some ('"', rem)
      else if s == "apos" then some ('\'', rem)
      else none

private def parseXMLAttrValLoop (q : Char) :
    Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, acc, c :: rest =>
    if c == q then some (String.ofList acc.reverse, rest)
    else if c == '<' || !isXML10Char c then none
    else if c == '&' then
      match decodeXMLRef rest with
      | some (ch, rem) => parseXMLAttrValLoop q fuel (ch :: acc) rem
      | none => none
    else if c == '\r' then
      let rest' := match rest with | '\n' :: r => r | r => r
      parseXMLAttrValLoop q fuel (' ' :: acc) rest'
    else if c == '\n' || c == '\t' then
      parseXMLAttrValLoop q fuel (' ' :: acc) rest
    else parseXMLAttrValLoop q fuel (c :: acc) rest

private def parseXMLRawAttrsLoop :
    Nat → List (String × String) → List Char → Option (List (String × String) × Bool × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, acc, '>' :: rest => some (acc.reverse, false, rest)
  | _ + 1, acc, '/' :: '>' :: rest => some (acc.reverse, true, rest)
  | fuel + 1, acc, c :: rest =>
    if !isXMLSpace c then none
    else
      let rem0 := skipXMLSpaces rest
      match rem0 with
      | '>' :: rem1 => some (acc.reverse, false, rem1)
      | '/' :: '>' :: rem1 => some (acc.reverse, true, rem1)
      | _ =>
        match readXMLName rem0 with
        | none => none
        | some (aname, rem1) =>
          if acc.any (fun (k, _) => k == aname) then none
          else
            let rem2 := skipXMLSpaces rem1
            match rem2 with
            | '=' :: rem3 =>
              let rem4 := skipXMLSpaces rem3
              match rem4 with
              | q :: rem5 =>
                if q == '"' || q == '\'' then
                  match parseXMLAttrValLoop q (rem5.length + 1) [] rem5 with
                  | none => none
                  | some (aval, rem6) =>
                    parseXMLRawAttrsLoop fuel ((aname, aval) :: acc) rem6
                else none
              | [] => none
            | _ => none

private def escapeCanonTextChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '\r' => ['&', '#', 'x', 'D', ';']
  | c => [c]

private def escapeCanonAttrChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | '\t' => ['&', '#', 'x', '9', ';']
  | '\n' => ['&', '#', 'x', 'A', ';']
  | '\r' => ['&', '#', 'x', 'D', ';']
  | c => [c]

private def escapeCanonAttrChars (s : String) : List Char :=
  s.toList.flatMap escapeCanonAttrChar

private def xmlNamespaceURI : String := "http://www.w3.org/XML/1998/namespace"
private def xmlnsNamespaceURI : String := "http://www.w3.org/2000/xmlns/"

-- Canonical XML rejects relative namespace references.
private def hasNamespaceScheme (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
    c.isAlpha && c.toNat < 128 &&
      ((rest.dropWhile fun x =>
        x.toNat < 128 && (x.isAlphanum || x == '+' || x == '-' || x == '.')).head? == some ':')
  | [] => false

private structure ResolvedXMLAttr where
  qname : String
  pfx? : Option String
  uri : String
  localName : String
  val : String

private def partitionXMLAttrs (rawAttrs : List (String × String)) :
    Option (List (String × String) × List (String × Option String × String × String)) :=
  let rec go : List (String × String) →
      Option (List (String × String) × List (String × Option String × String × String))
    | [] => some ([], [])
    | (aname, aval) :: rest => do
      let (nsTail, regTail) ← go rest
      if aname == "xmlns" then
        if aval == xmlNamespaceURI || aval == xmlnsNamespaceURI ||
          (!aval.isEmpty && !hasNamespaceScheme aval) then none
        else some (("", aval) :: nsTail, regTail)
      else
        match splitXMLQName aname with
        | none => none
        | some (some "xmlns", pfx) =>
          if !hasNamespaceScheme aval || pfx == "xmlns" || aval == xmlnsNamespaceURI then none
          else if (pfx == "xml") != (aval == xmlNamespaceURI) then none
          else some ((pfx, aval) :: nsTail, regTail)
        | some (apfx?, aloc) =>
          some (nsTail, (aname, apfx?, aloc, aval) :: regTail)
  go rawAttrs

private def resolveXMLRegAttrs (nsEnv : List (String × String)) :
    List (String × Option String × String × String) → Option (List ResolvedXMLAttr)
  | [] => some []
  | (aname, apfx?, aloc, aval) :: rest => do
    let uri ← match apfx? with
      | none => some ""
      | some p =>
        match nsEnv.lookup p with
        | some u => if u.isEmpty then none else some u
        | none => none
    let tail ← resolveXMLRegAttrs nsEnv rest
    if uri != "" && tail.any (fun a => a.uri == uri && a.localName == aloc) then none
    else some (⟨aname, apfx?, uri, aloc, aval⟩ :: tail)

private def charListLe : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c₁ :: r₁, c₂ :: r₂ =>
    if c₁.toNat < c₂.toNat then true
    else if c₂.toNat < c₁.toNat then false
    else charListLe r₁ r₂

private def strLe (a b : String) : Bool :=
  charListLe a.toList b.toList

private def dedupStrings (acc : List String) : List String → List String
  | [] => acc.reverse
  | x :: xs =>
    if acc.contains x then dedupStrings acc xs else dedupStrings (x :: acc) xs

private def insertSortedNsDecl (x : String × String) : List (String × String) → List (String × String)
  | [] => [x]
  | y :: ys =>
    let xKey : List Char := if x.1.isEmpty then [] else ':' :: x.1.toList
    let yKey : List Char := if y.1.isEmpty then [] else ':' :: y.1.toList
    if charListLe xKey yKey then x :: y :: ys else y :: insertSortedNsDecl x ys

private def sortNsDecls : List (String × String) → List (String × String)
  | [] => []
  | x :: xs => insertSortedNsDecl x (sortNsDecls xs)

private def attrLessEq (a b : ResolvedXMLAttr) : Bool :=
  match a.uri.isEmpty, b.uri.isEmpty with
  | true, false => true
  | false, true => false
  | true, true => strLe a.localName b.localName
  | false, false =>
    if a.uri == b.uri then strLe a.localName b.localName
    else strLe a.uri b.uri

private def insertSortedAttr (x : ResolvedXMLAttr) : List ResolvedXMLAttr → List ResolvedXMLAttr
  | [] => [x]
  | y :: ys => if attrLessEq x y then x :: y :: ys else y :: insertSortedAttr x ys

private def sortResolvedAttrs : List ResolvedXMLAttr → List ResolvedXMLAttr
  | [] => []
  | x :: xs => insertSortedAttr x (sortResolvedAttrs xs)

private structure XMLFrame where
  qname : String
  nsEnv : List (String × String)
  renderedEnv : List (String × String)

private def processStartTag (curNsEnv curRenderedEnv : List (String × String))
    (qname : String) (rawAttrs : List (String × String)) :
    Option (List Char × List (String × String) × List (String × String)) := do
  let (elemPfx?, _) ← splitXMLQName qname
  if elemPfx? == some "xmlns" then none
  let (nsDecls, regRaw) ← partitionXMLAttrs rawAttrs
  let nsEnv' := nsDecls ++ curNsEnv
  let elemPfx := elemPfx?.getD ""
  let elemURI ← nsEnv'.lookup elemPfx
  if !elemPfx.isEmpty && elemURI.isEmpty then none
  let resolvedAttrs ← resolveXMLRegAttrs nsEnv' regRaw
  let visPrefixes := (dedupStrings [] (elemPfx :: resolvedAttrs.filterMap (·.pfx?))).filter (· != "xml")
  let toRender := visPrefixes.filterMap fun p =>
    let uri := (nsEnv'.lookup p).getD ""
    let prev := (curRenderedEnv.lookup p).getD ""
    if p.isEmpty then
      if uri != prev then some ("", uri) else none
    else
      if curRenderedEnv.lookup p != some uri then some (p, uri) else none
  let sortedNs := sortNsDecls toRender
  let renderedEnv' := sortedNs ++ curRenderedEnv
  let sortedAttrs := sortResolvedAttrs resolvedAttrs
  let nsChars : List Char := sortedNs.flatMap fun (p, u) =>
    let attrNameChars : List Char :=
      if p.isEmpty then ['x', 'm', 'l', 'n', 's']
      else 'x' :: 'm' :: 'l' :: 'n' :: 's' :: ':' :: p.toList
    (' ' :: attrNameChars) ++ ('=' :: '"' :: escapeCanonAttrChars u) ++ ['"']
  let attrChars : List Char := sortedAttrs.flatMap fun a =>
    (' ' :: a.qname.toList) ++ ('=' :: '"' :: escapeCanonAttrChars a.val) ++ ['"']
  let openTagChars : List Char := ('<' :: qname.toList) ++ nsChars ++ attrChars ++ ['>']
  some (openTagChars, nsEnv', renderedEnv')

private def readXMLCommentBody (acc : List Char) : List Char → Option (List Char × List Char)
  | '-' :: '-' :: '>' :: rest => some (acc.reverse, rest)
  | '-' :: '-' :: _ => none
  | '\r' :: '\n' :: rest => readXMLCommentBody ('\n' :: acc) rest
  | '\r' :: rest => readXMLCommentBody ('\n' :: acc) rest
  | c :: rest => if isXML10Char c then readXMLCommentBody (c :: acc) rest else none
  | [] => none

private def readXMLCDATABody (acc : List Char) : List Char → Option (List Char × List Char)
  | ']' :: ']' :: '>' :: rest => some (acc.reverse, rest)
  | '\r' :: '\n' :: rest => readXMLCDATABody ('\n' :: acc) rest
  | '\r' :: rest => readXMLCDATABody ('\n' :: acc) rest
  | c :: rest => if isXML10Char c then readXMLCDATABody (c :: acc) rest else none
  | [] => none

private def readXMLPIBody (acc : List Char) : List Char → Option (String × List Char)
  | '?' :: '>' :: rest => some (String.ofList acc.reverse, rest)
  | '\r' :: '\n' :: rest => readXMLPIBody ('\n' :: acc) rest
  | '\r' :: rest => readXMLPIBody ('\n' :: acc) rest
  | c :: rest => if isXML10Char c then readXMLPIBody (c :: acc) rest else none
  | [] => none

private def canonXMLLoop :
    Nat → List XMLFrame → List (String × String) → List (String × String) →
    List Char → List Char → Option String
  | 0, _, _, _, _, _ => none
  | _ + 1, stack, _, _, outRev, [] =>
    if stack.isEmpty then some (String.ofList outRev.reverse) else none
  | fuel + 1, stack, _curNs, _curRend, outRev, '<' :: '/' :: rest =>
    match readXMLName rest with
    | none => none
    | some (ename, rem1) =>
      match stack with
      | top :: tail =>
        if top.qname != ename then none
        else
          match skipXMLSpaces rem1 with
          | '>' :: rem2 =>
            let closeChars := ('<' :: '/' :: ename.toList) ++ ['>']
            canonXMLLoop fuel tail top.nsEnv top.renderedEnv (closeChars.reverse ++ outRev) rem2
          | _ => none
      | [] => none
  | fuel + 1, stack, curNs, curRend, outRev, '<' :: '!' :: '-' :: '-' :: rest =>
    match readXMLCommentBody [] rest with
    | none => none
    | some (body, rem) =>
      let chars := ['<', '!', '-', '-'] ++ body ++ ['-', '-', '>']
      canonXMLLoop fuel stack curNs curRend (chars.reverse ++ outRev) rem
  | fuel + 1, stack, curNs, curRend, outRev, '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: rest =>
    match readXMLCDATABody [] rest with
    | none => none
    | some (cdataChars, rem) =>
      let esc := cdataChars.flatMap escapeCanonTextChar
      canonXMLLoop fuel stack curNs curRend (esc.reverse ++ outRev) rem
  | fuel + 1, stack, curNs, curRend, outRev, '<' :: '?' :: rest =>
    match readXMLName rest with
    | none => none
    | some (target, rem1) =>
      if target.toLower == "xml" || !isXMLNCName target then none
      else
        match rem1 with
        | '?' :: '>' :: rem2 =>
          let piChars := ('<' :: '?' :: target.toList) ++ ['?', '>']
          canonXMLLoop fuel stack curNs curRend (piChars.reverse ++ outRev) rem2
        | c :: rem2 =>
          if isXMLSpace c then
            match readXMLPIBody [] (skipXMLSpaces rem2) with
            | none => none
            | some (body, rem3) =>
              let piChars :=
                if body.isEmpty then ('<' :: '?' :: target.toList) ++ ['?', '>']
                else ('<' :: '?' :: target.toList) ++ (' ' :: body.toList) ++ ['?', '>']
              canonXMLLoop fuel stack curNs curRend (piChars.reverse ++ outRev) rem3
          else none
        | [] => none
  | fuel + 1, stack, curNs, curRend, outRev, '<' :: rest =>
    match readXMLName rest with
    | none => none
    | some (tname, rem1) =>
      match parseXMLRawAttrsLoop (rem1.length + 1) [] rem1 with
      | none => none
      | some (rawAttrs, selfClose, rem2) =>
        match processStartTag curNs curRend tname rawAttrs with
        | none => none
        | some (openTagChars, nsEnv', renderedEnv') =>
          if selfClose then
            let fullChars := openTagChars ++ ('<' :: '/' :: tname.toList) ++ ['>']
            canonXMLLoop fuel stack curNs curRend (fullChars.reverse ++ outRev) rem2
          else
            let frame : XMLFrame := ⟨tname, curNs, curRend⟩
            canonXMLLoop fuel (frame :: stack) nsEnv' renderedEnv' (openTagChars.reverse ++ outRev) rem2
  | fuel + 1, stack, curNs, curRend, outRev, '&' :: rest =>
    match decodeXMLRef rest with
    | none => none
    | some (ch, rem) =>
      let esc := escapeCanonTextChar ch
      canonXMLLoop fuel stack curNs curRend (esc.reverse ++ outRev) rem
  | _ + 1, _, _, _, _, ']' :: ']' :: '>' :: _ => none
  | fuel + 1, stack, curNs, curRend, outRev, '\r' :: '\n' :: rest =>
    canonXMLLoop fuel stack curNs curRend ('\n' :: outRev) rest
  | fuel + 1, stack, curNs, curRend, outRev, '\r' :: rest =>
    canonXMLLoop fuel stack curNs curRend ('\n' :: outRev) rest
  | fuel + 1, stack, curNs, curRend, outRev, c :: rest =>
    if !isXML10Char c then none
    else
      let esc := escapeCanonTextChar c
      canonXMLLoop fuel stack curNs curRend (esc.reverse ++ outRev) rest

def isSimpleCanonTextChar (c : Char) : Bool :=
  isXML10Char c && c != '<' && c != '>' && c != '&' && c != '\r' && c != ']'

private def initXMLNsEnv : List (String × String) :=
  [("", ""), ("xml", xmlNamespaceURI)]

def canonicalizeXMLPass (raw : String) : Option String :=
  let cs := raw.toList
  if cs.all isSimpleCanonTextChar then some raw
  else canonXMLLoop (cs.length + 1) [] initXMLNsEnv initXMLNsEnv [] cs

/-- Canonicalize supported balanced XML content with namespace resolution and
comments retained. The second pass checks that the result is a fixed point. -/
def canonicalizeXMLLiteral (raw : String) : Option String :=
  match canonicalizeXMLPass raw with
  | some canon =>
    if canonicalizeXMLPass canon == some canon then some canon else none
  | none => none

/-- Test whether the canonicalizer accepts balanced XML content. -/
def checkWellFormedXMLLiteral (s : String) : Bool :=
  (canonicalizeXMLLiteral s).isSome

/-- Test whether the input is a fixed point of the canonicalization pass. -/
def checkCanonicalXMLLiteral (s : String) : Bool :=
  canonicalizeXMLPass s == some s

theorem canonicalizeXMLLiteral_idempotent {raw canon : String}
    (h : canonicalizeXMLLiteral raw = some canon) :
    canonicalizeXMLLiteral canon = some canon := by
  unfold canonicalizeXMLLiteral at h ⊢
  cases hp : canonicalizeXMLPass raw with
  | none => simp [hp] at h
  | some c =>
    simp only [hp] at h
    by_cases hfix : (canonicalizeXMLPass c == some c) = true
    · simp only [hfix, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hfc : canonicalizeXMLPass c = some c := beq_iff_eq.mp hfix
      simp [hfc]
    · simp [hfix] at h

theorem checkCanonicalXMLLiteral_of_canonicalize {raw canon : String}
    (h : canonicalizeXMLLiteral raw = some canon) :
    checkCanonicalXMLLiteral canon = true := by
  unfold canonicalizeXMLLiteral at h
  cases hp : canonicalizeXMLPass raw with
  | none => simp [hp] at h
  | some c =>
    simp only [hp] at h
    by_cases hfix : (canonicalizeXMLPass c == some c) = true
    · simp only [hfix, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hfix
    · simp [hfix] at h

theorem checkCanonicalXMLLiteral_iff (s : String) :
    checkCanonicalXMLLiteral s = true ↔ canonicalizeXMLLiteral s = some s := by
  constructor
  · intro h
    have hp : canonicalizeXMLPass s = some s := beq_iff_eq.mp h
    simp [canonicalizeXMLLiteral, hp]
  · exact checkCanonicalXMLLiteral_of_canonicalize

theorem canonicalXMLLiteral_implies_wellFormed {s : String}
    (h : checkCanonicalXMLLiteral s = true) : checkWellFormedXMLLiteral s = true := by
  unfold checkWellFormedXMLLiteral
  rw [(checkCanonicalXMLLiteral_iff s).mp h]
  rfl

theorem checkCanonicalXMLLiteral_replicate_a (k : Nat) :
    checkCanonicalXMLLiteral (String.ofList (List.replicate k 'a')) = true := by
  apply (checkCanonicalXMLLiteral_iff _).mpr
  have hall : (List.replicate k 'a').all isSimpleCanonTextChar = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [List.eq_of_mem_replicate hc]
    decide
  have hpass : canonicalizeXMLPass (String.ofList (List.replicate k 'a')) =
      some (String.ofList (List.replicate k 'a')) := by
    simp [canonicalizeXMLPass, String.toList_ofList, hall]
  simp [canonicalizeXMLLiteral, hpass]

end Sabrina.OWL2.Datatypes
