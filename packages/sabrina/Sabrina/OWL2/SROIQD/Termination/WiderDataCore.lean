import Sabrina.OWL2.SROIQD.Termination.DataRangeExact
import Sabrina.OWL2.SROIQD.Termination.StringLengthCells

/-!
Exact Boolean-closed wider `DataRange` algebra and bounded witness sampler
extending `DataRangeExact` to:
- All 16 exact numeric datatypes (`owl:real`, `owl:rational`, `xsd:decimal`,
  `xsd:integer`, and its 12 named subtypes) with arbitrary order facets
  (`minInclusive`, `maxInclusive`, `minExclusive`, `maxExclusive`) across
  integer, proper-decimal, and non-decimal rational strata;
- String and `rdf:PlainLiteral` hierarchy (`rdf:PlainLiteral`, `xsd:string`,
  `xsd:normalizedString`, `xsd:token`, `xsd:NMTOKEN`, `xsd:Name`, `xsd:NCName`)
  combined with length facets on `xsd:string` and `rdf:PlainLiteral`;
- `xsd:anyURI`, `xsd:hexBinary`, and `xsd:base64Binary` with length facets;
- `xsd:boolean`, `rdf:XMLLiteral`, `xsd:dateTime`, and `xsd:dateTimeStamp`;
- Arbitrary `DataOneOf` literal enumerations and nested Boolean combinations.
-/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.DataRanges
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination

/-! ### 1. Elementary `Rat` order helpers & exact rational interval algebra -/

private theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [Rat.lt_iff] at h1 h2 ⊢
  have ha : (0 : Int) < (a.den : Int) := by have := a.den_pos; omega
  have hb : (0 : Int) < (b.den : Int) := by have := b.den_pos; omega
  have hc : (0 : Int) < (c.den : Int) := by have := c.den_pos; omega
  have h1' : a.num * (b.den : Int) * (c.den : Int) < b.num * (a.den : Int) * (c.den : Int) :=
    Int.mul_lt_mul_of_pos_right h1 hc
  have h2' : b.num * (c.den : Int) * (a.den : Int) < c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_lt_mul_of_pos_right h2 ha
  have hmid : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (a.den : Int) (c.den : Int), ← Int.mul_assoc]
  have hcomb : a.num * (c.den : Int) * (b.den : Int) < c.num * (a.den : Int) * (b.den : Int) := by
    have hl : a.num * (c.den : Int) * (b.den : Int) = a.num * (b.den : Int) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (c.den : Int) (b.den : Int), ← Int.mul_assoc]
    have hr : c.num * (a.den : Int) * (b.den : Int) = c.num * (b.den : Int) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (a.den : Int) (b.den : Int), ← Int.mul_assoc]
    rw [hl, hr]; omega
  exact Int.lt_of_mul_lt_mul_right hcomb (Int.le_of_lt hb)

private theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  by_cases h : c ≤ a
  · exact (Rat.not_lt.mpr (Rat.le_trans h h1) h2).elim
  · exact Rat.not_le.mp h

private theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  by_cases h : c ≤ a
  · exact (Rat.not_lt.mpr (Rat.le_trans h2 h) h1).elim
  · exact Rat.not_le.mp h

private theorem rat_trichotomy (a b : Rat) : a < b ∨ b < a ∨ a = b := by
  by_cases h1 : a < b
  · exact .inl h1
  · by_cases h2 : b < a
    · exact .inr (.inl h2)
    · exact .inr (.inr (Rat.le_antisymm (Rat.not_lt.mp h2) (Rat.not_lt.mp h1)))

structure RatEndpoint where
  val : Rat
  inclusive : Bool
  deriving DecidableEq, Repr

def RatEndpoint.holdsLower (e : RatEndpoint) (q : Rat) : Prop :=
  if e.inclusive then e.val ≤ q else e.val < q

def RatEndpoint.holdsUpper (e : RatEndpoint) (q : Rat) : Prop :=
  if e.inclusive then q ≤ e.val else q < e.val

instance (e : RatEndpoint) (q : Rat) : Decidable (e.holdsLower q) := by
  unfold RatEndpoint.holdsLower; split <;> infer_instance

instance (e : RatEndpoint) (q : Rat) : Decidable (e.holdsUpper q) := by
  unfold RatEndpoint.holdsUpper; split <;> infer_instance

def RatEndpoint.maxLower (a b : RatEndpoint) : RatEndpoint :=
  if a.val < b.val then b
  else if b.val < a.val then a
  else ⟨a.val, a.inclusive && b.inclusive⟩

def RatEndpoint.minUpper (a b : RatEndpoint) : RatEndpoint :=
  if a.val < b.val then a
  else if b.val < a.val then b
  else ⟨a.val, a.inclusive && b.inclusive⟩

theorem RatEndpoint.holdsLower_maxLower (a b : RatEndpoint) (q : Rat) :
    (a.maxLower b).holdsLower q ↔ a.holdsLower q ∧ b.holdsLower q := by
  rcases a with ⟨av, ai⟩
  rcases b with ⟨bv, bi⟩
  unfold maxLower holdsLower
  rcases rat_trichotomy av bv with hlt | hgt | heq
  · simp only [hlt, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨rat_lt_trans hlt h, h⟩, And.right⟩
    · exact ⟨fun h => ⟨rat_lt_of_lt_of_le hlt h, h⟩, And.right⟩
    · exact ⟨fun h => ⟨Rat.le_of_lt (rat_lt_trans hlt h), h⟩, And.right⟩
    · exact ⟨fun h => ⟨Rat.le_trans (Rat.le_of_lt hlt) h, h⟩, And.right⟩
  · have hnot : ¬ av < bv := fun h => Rat.lt_irrefl (rat_lt_trans hgt h)
    simp only [hnot, hgt, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨h, rat_lt_trans hgt h⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_of_lt (rat_lt_trans hgt h)⟩, And.left⟩
    · exact ⟨fun h => ⟨h, rat_lt_of_lt_of_le hgt h⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_trans (Rat.le_of_lt hgt) h⟩, And.left⟩
  · subst heq
    have hnot : ¬ av < av := Rat.lt_irrefl
    simp only [hnot, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [Bool.and_false, Bool.and_true, ↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨h, h⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_of_lt h⟩, And.left⟩
    · exact ⟨fun h => ⟨Rat.le_of_lt h, h⟩, And.right⟩
    · exact ⟨fun h => ⟨h, h⟩, And.left⟩

theorem RatEndpoint.holdsUpper_minUpper (a b : RatEndpoint) (q : Rat) :
    (a.minUpper b).holdsUpper q ↔ a.holdsUpper q ∧ b.holdsUpper q := by
  rcases a with ⟨av, ai⟩
  rcases b with ⟨bv, bi⟩
  unfold minUpper holdsUpper
  rcases rat_trichotomy av bv with hlt | hgt | heq
  · simp only [hlt, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨h, rat_lt_trans h hlt⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_of_lt (rat_lt_trans h hlt)⟩, And.left⟩
    · exact ⟨fun h => ⟨h, rat_lt_of_le_of_lt h hlt⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_trans h (Rat.le_of_lt hlt)⟩, And.left⟩
  · have hnot : ¬ av < bv := fun h => Rat.lt_irrefl (rat_lt_trans hgt h)
    simp only [hnot, hgt, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨rat_lt_trans h hgt, h⟩, And.right⟩
    · exact ⟨fun h => ⟨rat_lt_of_le_of_lt h hgt, h⟩, And.right⟩
    · exact ⟨fun h => ⟨Rat.le_of_lt (rat_lt_trans h hgt), h⟩, And.right⟩
    · exact ⟨fun h => ⟨Rat.le_trans h (Rat.le_of_lt hgt), h⟩, And.right⟩
  · subst heq
    have hnot : ¬ av < av := Rat.lt_irrefl
    simp only [hnot, ↓reduceIte]
    cases ai <;> cases bi <;> simp only [Bool.and_false, Bool.and_true, ↓reduceIte, Bool.false_eq_true]
    · exact ⟨fun h => ⟨h, h⟩, And.left⟩
    · exact ⟨fun h => ⟨h, Rat.le_of_lt h⟩, And.left⟩
    · exact ⟨fun h => ⟨Rat.le_of_lt h, h⟩, And.right⟩
    · exact ⟨fun h => ⟨h, h⟩, And.left⟩

structure RatBounds where
  lower : Option RatEndpoint := none
  upper : Option RatEndpoint := none
  deriving DecidableEq, Repr

def RatBounds.contains (b : RatBounds) (q : Rat) : Prop :=
  (b.lower.elim True (·.holdsLower q)) ∧ (b.upper.elim True (·.holdsUpper q))

instance (b : RatBounds) (q : Rat) : Decidable (b.contains q) := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> unfold RatBounds.contains <;> dsimp <;> infer_instance

def RatBounds.intersect (a b : RatBounds) : RatBounds :=
  { lower := match a.lower, b.lower with
      | none, y => y
      | x, none => x
      | some x, some y => some (x.maxLower y),
    upper := match a.upper, b.upper with
      | none, y => y
      | x, none => x
      | some x, some y => some (x.minUpper y) }

theorem RatBounds.contains_intersect (a b : RatBounds) (q : Rat) :
    (a.intersect b).contains q ↔ a.contains q ∧ b.contains q := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  have hl : (match al, bl with
      | none, y => y
      | x, none => x
      | some x, some y => some (x.maxLower y)).elim True (·.holdsLower q) ↔
      al.elim True (·.holdsLower q) ∧ bl.elim True (·.holdsLower q) := by
    cases al <;> cases bl <;> simp [RatEndpoint.holdsLower_maxLower]
  have hu : (match au, bu with
      | none, y => y
      | x, none => x
      | some x, some y => some (x.minUpper y)).elim True (·.holdsUpper q) ↔
      au.elim True (·.holdsUpper q) ∧ bu.elim True (·.holdsUpper q) := by
    cases au <;> cases bu <;> simp [RatEndpoint.holdsUpper_minUpper]
  simp only [RatBounds.intersect, RatBounds.contains, hl, hu]
  exact ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩,
         fun ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩

def isNonEmptyRatBounds (b : RatBounds) : Bool :=
  match b.lower, b.upper with
  | some lo, some hi =>
    if lo.val < hi.val then true
    else lo.val == hi.val && lo.inclusive && hi.inclusive
  | _, _ => true

private theorem isNonEmptyRatBounds_of_contains {b : RatBounds} {q : Rat}
    (h : b.contains q) : isNonEmptyRatBounds b = true := by
  rcases b with ⟨lo, hi⟩
  cases lo with
  | none => rfl
  | some lo =>
    rcases lo with ⟨lov, loi⟩
    cases hi with
    | none => rfl
    | some hi =>
      rcases hi with ⟨hiv, hii⟩
      obtain ⟨h1, h2⟩ := h
      simp only [Option.elim_some, RatEndpoint.holdsLower, RatEndpoint.holdsUpper] at h1 h2
      simp only [isNonEmptyRatBounds]
      split
      · rfl
      · rename_i hnot
        have hle1 : lov ≤ q := by cases loi <;> simp at h1; exact Rat.le_of_lt h1; exact h1
        have hle2 : q ≤ hiv := by cases hii <;> simp at h2; exact Rat.le_of_lt h2; exact h2
        have hle : lov ≤ hiv := Rat.le_trans hle1 hle2
        have heq : lov = hiv := by
          rcases rat_trichotomy lov hiv with hlt | hgt | heq
          · exact (hnot hlt).elim
          · exact (Rat.not_lt.mpr hle hgt).elim
          · exact heq
        subst heq
        have hq : q = lov := Rat.le_antisymm hle2 hle1
        subst hq
        have hli : loi = true := by
          cases loi
          · simp at h1
          · rfl
        have hhi : hii = true := by
          cases hii
          · simp at h2
          · rfl
        simp [hli, hhi]

def subtractRatBoundsOne (cur neg : RatBounds) : List RatBounds :=
  let left : List RatBounds :=
    match neg.lower with
    | none => []
    | some nlo =>
      let cap : RatEndpoint := ⟨nlo.val, !nlo.inclusive⟩
      [{ lower := cur.lower,
         upper := match cur.upper with
           | none => some cap
           | some chi => some (chi.minUpper cap) }]
  let right : List RatBounds :=
    match neg.upper with
    | none => []
    | some nhi =>
      let flr : RatEndpoint := ⟨nhi.val, !nhi.inclusive⟩
      [{ lower := match cur.lower with
           | none => some flr
           | some clo => some (clo.maxLower flr),
         upper := cur.upper }]
  (left ++ right).filter isNonEmptyRatBounds

private theorem not_holdsLower_iff (e : RatEndpoint) (q : Rat) :
    ¬ e.holdsLower q ↔ (⟨e.val, !e.inclusive⟩ : RatEndpoint).holdsUpper q := by
  rcases e with ⟨v, _ | _⟩ <;> simp [RatEndpoint.holdsLower, RatEndpoint.holdsUpper, Rat.not_le, Rat.not_lt]

private theorem not_holdsUpper_iff (e : RatEndpoint) (q : Rat) :
    ¬ e.holdsUpper q ↔ (⟨e.val, !e.inclusive⟩ : RatEndpoint).holdsLower q := by
  rcases e with ⟨v, _ | _⟩ <;> simp [RatEndpoint.holdsLower, RatEndpoint.holdsUpper, Rat.not_le, Rat.not_lt]

theorem mem_subtractRatBoundsOne_iff (cur neg : RatBounds) (q : Rat) :
    (∃ b ∈ subtractRatBoundsOne cur neg, b.contains q) ↔ (cur.contains q ∧ ¬ neg.contains q) := by
  classical
  rcases cur with ⟨clo, chi⟩
  rcases neg with ⟨nlo, nhi⟩
  let leftL : List RatBounds :=
    match nlo with
    | none => []
    | some e => [⟨clo, match chi with
        | none => some ⟨e.val, !e.inclusive⟩
        | some c => some (c.minUpper ⟨e.val, !e.inclusive⟩)⟩]
  let rightL : List RatBounds :=
    match nhi with
    | none => []
    | some e => [⟨match clo with
        | none => some ⟨e.val, !e.inclusive⟩
        | some c => some (c.maxLower ⟨e.val, !e.inclusive⟩), chi⟩]
  have hleft : (∃ b ∈ leftL, b.contains q) ↔
      (clo.elim True (·.holdsLower q) ∧ chi.elim True (·.holdsUpper q) ∧ ¬ nlo.elim True (·.holdsLower q)) := by
    dsimp only [leftL]
    cases nlo with
    | none => simp
    | some e =>
      cases chi with
      | none => simp [RatBounds.contains, not_holdsLower_iff]
      | some c =>
        simp only [List.mem_singleton, exists_eq_left, RatBounds.contains, Option.elim_some,
          RatEndpoint.holdsUpper_minUpper, not_holdsLower_iff]
  have hright : (∃ b ∈ rightL, b.contains q) ↔
      (clo.elim True (·.holdsLower q) ∧ chi.elim True (·.holdsUpper q) ∧ ¬ nhi.elim True (·.holdsUpper q)) := by
    dsimp only [rightL]
    cases nhi with
    | none => simp
    | some e =>
      cases clo with
      | none =>
        simp only [List.mem_singleton, exists_eq_left, RatBounds.contains, Option.elim_none,
          Option.elim_some, true_and, not_holdsUpper_iff]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, h2⟩⟩
      | some c =>
        simp only [List.mem_singleton, exists_eq_left, RatBounds.contains, Option.elim_some,
          RatEndpoint.holdsLower_maxLower, not_holdsUpper_iff]
        exact ⟨fun ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h3⟩, h2⟩⟩
  have hfilt : (∃ b ∈ (leftL ++ rightL).filter isNonEmptyRatBounds, b.contains q) ↔
      (∃ b ∈ leftL ++ rightL, b.contains q) :=
    ⟨fun ⟨b, hb, hq⟩ => ⟨b, (List.mem_filter.mp hb).1, hq⟩,
     fun ⟨b, hb, hq⟩ => ⟨b, List.mem_filter.mpr ⟨hb, isNonEmptyRatBounds_of_contains hq⟩, hq⟩⟩
  change (∃ b ∈ (leftL ++ rightL).filter isNonEmptyRatBounds, b.contains q) ↔ _
  rw [hfilt]
  simp only [List.mem_append, RatBounds.contains]
  constructor
  · rintro ⟨b, h1 | h2, hb⟩
    · obtain ⟨hlo, hhi, hnl⟩ := hleft.mp ⟨b, h1, hb⟩
      exact ⟨⟨hlo, hhi⟩, fun h => hnl h.1⟩
    · obtain ⟨hlo, hhi, hnh⟩ := hright.mp ⟨b, h2, hb⟩
      exact ⟨⟨hlo, hhi⟩, fun h => hnh h.2⟩
  · rintro ⟨⟨hlo, hhi⟩, hnot⟩
    by_cases hl : nlo.elim True (·.holdsLower q)
    · have hh : ¬ nhi.elim True (·.holdsUpper q) := fun hh => hnot ⟨hl, hh⟩
      obtain ⟨b, hm, hb⟩ := hright.mpr ⟨hlo, hhi, hh⟩
      exact ⟨b, .inr hm, hb⟩
    · obtain ⟨b, hm, hb⟩ := hleft.mpr ⟨hlo, hhi, hl⟩
      exact ⟨b, .inl hm, hb⟩

def foldSubtractRatBounds : List RatBounds → List RatBounds → List RatBounds
  | bs, [] => bs
  | bs, neg :: rest => foldSubtractRatBounds (bs.flatMap (subtractRatBoundsOne · neg)) rest

theorem mem_foldSubtractRatBounds_iff (bs negs : List RatBounds) (q : Rat) :
    (∃ b ∈ foldSubtractRatBounds bs negs, b.contains q) ↔
      ((∃ b ∈ bs, b.contains q) ∧ ∀ n ∈ negs, ¬ n.contains q) := by
  induction negs generalizing bs with
  | nil => simp [foldSubtractRatBounds]
  | cons neg rest ih =>
    simp only [foldSubtractRatBounds, ih, List.mem_flatMap, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨b, ⟨b₀, hb₀, hb⟩, hq⟩, hrest⟩
      have ⟨h1, h2⟩ := (mem_subtractRatBoundsOne_iff b₀ neg q).mp ⟨b, hb, hq⟩
      exact ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
    · rintro ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
      obtain ⟨b, hb, hq⟩ := (mem_subtractRatBoundsOne_iff b₀ neg q).mpr ⟨h1, h2⟩
      exact ⟨⟨b, ⟨b₀, hb₀, hb⟩, hq⟩, hrest⟩

def RatBounds.toIntBounds (b : RatBounds) : IntegerBounds :=
  { lower := b.lower.map fun e => if e.inclusive then e.val.ceil else e.val.floor + 1,
    upper := b.upper.map fun e => if e.inclusive then e.val.floor else e.val.ceil - 1 }

theorem RatBounds.toIntBounds_iff (b : RatBounds) (z : Int) :
    b.toIntBounds.contains z ↔ b.contains (Rat.ofInt z) := by
  rcases b with ⟨lo, hi⟩
  have hlo : (lo.map fun e => if e.inclusive then e.val.ceil else e.val.floor + 1).elim True (· ≤ z) ↔
      lo.elim True (·.holdsLower (Rat.ofInt z)) := by
    cases lo with
    | none => simp
    | some e =>
      rcases e with ⟨v, _ | _⟩
      · simp only [Option.map_some, Option.elim_some, Bool.false_eq_true, ↓reduceIte, RatEndpoint.holdsLower]
        change v.floor + 1 ≤ z ↔ v < (z : Rat)
        rw [← Rat.floor_lt_iff]; omega
      · simp only [Option.map_some, Option.elim_some, ↓reduceIte, RatEndpoint.holdsLower]
        exact Rat.ceil_le_iff
  have hhi : (hi.map fun e => if e.inclusive then e.val.floor else e.val.ceil - 1).elim True (z ≤ ·) ↔
      hi.elim True (·.holdsUpper (Rat.ofInt z)) := by
    cases hi with
    | none => simp
    | some e =>
      rcases e with ⟨v, _ | _⟩
      · simp only [Option.map_some, Option.elim_some, Bool.false_eq_true, ↓reduceIte, RatEndpoint.holdsUpper]
        change z ≤ v.ceil - 1 ↔ (z : Rat) < v
        rw [← Rat.lt_ceil_iff]; omega
      · simp only [Option.map_some, Option.elim_some, ↓reduceIte, RatEndpoint.holdsUpper]
        exact Rat.le_floor_iff
  exact and_congr hlo hhi

def intBoundsToRatBounds (b : IntegerBounds) : RatBounds :=
  { lower := b.lower.map fun lo => ⟨Rat.ofInt lo, true⟩,
    upper := b.upper.map fun hi => ⟨Rat.ofInt hi, true⟩ }

theorem intBoundsToRatBounds_iff (b : IntegerBounds) (z : Int) :
    (intBoundsToRatBounds b).contains (Rat.ofInt z) ↔ b.contains z := by
  rcases b with ⟨lo, hi⟩
  have hlo : (lo.map fun l => RatEndpoint.mk (Rat.ofInt l) true).elim True (·.holdsLower (Rat.ofInt z)) ↔
      lo.elim True (· ≤ z) := by
    cases lo with
    | none => simp
    | some l => simp [RatEndpoint.holdsLower, Rat.le_iff]
  have hhi : (hi.map fun u => RatEndpoint.mk (Rat.ofInt u) true).elim True (·.holdsUpper (Rat.ofInt z)) ↔
      hi.elim True (z ≤ ·) := by
    cases hi with
    | none => simp
    | some u => simp [RatEndpoint.holdsUpper, Rat.le_iff]
  exact and_congr hlo hhi

/-! ### 2. Constructive dense witnesses for proper decimals & non-decimal rationals -/

private theorem ten_pow_pos (p : Nat) : 0 < (10 : Nat) ^ p :=
  Nat.pow_pos (by decide)

private theorem three_pow_pos (p : Nat) : 0 < (3 : Nat) ^ p :=
  Nat.pow_pos (by decide)

private def pow10Above (n : Nat) : Nat :=
  let rec go : Nat → Nat → Nat → Nat
    | 0, p, _ => p
    | fuel + 1, p, cur =>
      if n < cur then p
      else go fuel (p + 1) (cur * 10)
  go (n + 1) 1 10

private theorem pow10Above_gt (n : Nat) : n < 10 ^ (pow10Above n) := by
  unfold pow10Above
  suffices ∀ fuel p cur, cur = 10 ^ p → n < cur + fuel → n < 10 ^ (pow10Above.go n fuel p cur) by
    exact this (n + 1) 1 10 rfl (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro p cur hcur hlt
    simpa [pow10Above.go, hcur] using hlt
  | succ f ih =>
    intro p cur hcur hlt
    unfold pow10Above.go
    split
    · rename_i hlt'
      simpa [hcur] using hlt'
    · rename_i hge
      have hcurPos : 1 ≤ cur := by rw [hcur]; exact ten_pow_pos p
      have hnext : cur * 10 = 10 ^ (p + 1) := by rw [hcur, Nat.pow_succ]
      exact ih (p + 1) (cur * 10) hnext (by omega)

private theorem nat_dvd_natAbs_to_int {d : Nat} {z : Int} (h : d ∣ z.natAbs) :
    (d : Int) ∣ z := by
  obtain ⟨k, hk⟩ := h
  cases z with
  | ofNat m =>
    have hm : m = d * k := hk
    refine ⟨(k : Int), ?_⟩
    change ((m : Nat) : Int) = (d : Int) * (k : Int)
    exact_mod_cast hm
  | negSucc m =>
    have hm : m + 1 = d * k := hk
    refine ⟨-(k : Int), ?_⟩
    have : ((m + 1 : Nat) : Int) = (d : Int) * (k : Int) := by exact_mod_cast hm
    rw [Int.mul_neg]
    omega

private theorem mkRat_lt_iff {n₁ n₂ : Int} {d₁ d₂ : Nat} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    mkRat n₁ d₁ < mkRat n₂ d₂ ↔ n₁ * (d₂ : Int) < n₂ * (d₁ : Int) := by
  have hd1z : d₁ ≠ 0 := Nat.ne_of_gt hd₁
  have hd2z : d₂ ≠ 0 := Nat.ne_of_gt hd₂
  have hg1 : 0 < d₁.gcd n₁.natAbs := Nat.gcd_pos_of_pos_left _ hd₁
  have hg2 : 0 < d₂.gcd n₂.natAbs := Nat.gcd_pos_of_pos_left _ hd₂
  have hcancel1 : (d₁ / d₁.gcd n₁.natAbs) * d₁.gcd n₁.natAbs = d₁ :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left d₁ n₁.natAbs)
  have hcancel2 : (d₂ / d₂.gcd n₂.natAbs) * d₂.gcd n₂.natAbs = d₂ :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left d₂ n₂.natAbs)
  have hnd1 : (n₁ / (d₁.gcd n₁.natAbs : Int)) * (d₁.gcd n₁.natAbs : Int) = n₁ :=
    Int.ediv_mul_cancel (nat_dvd_natAbs_to_int (Nat.gcd_dvd_right d₁ n₁.natAbs))
  have hnd2 : (n₂ / (d₂.gcd n₂.natAbs : Int)) * (d₂.gcd n₂.natAbs : Int) = n₂ :=
    Int.ediv_mul_cancel (nat_dvd_natAbs_to_int (Nat.gcd_dvd_right d₂ n₂.natAbs))
  rw [Rat.lt_iff, Rat.num_mkRat, Rat.den_mkRat, Rat.num_mkRat, Rat.den_mkRat,
    ite_eq_right hd1z, ite_eq_right hd2z, ite_eq_right hd2z, ite_eq_right hd1z]
  have hg1pos : (0 : Int) < (d₁.gcd n₁.natAbs : Int) := by omega
  have hg2pos : (0 : Int) < (d₂.gcd n₂.natAbs : Int) := by omega
  have hprodPos : (0 : Int) < (d₁.gcd n₁.natAbs : Int) * (d₂.gcd n₂.natAbs : Int) :=
    Int.mul_pos hg1pos hg2pos
  have hc1 : ((d₁ / d₁.gcd n₁.natAbs : Nat) : Int) * (d₁.gcd n₁.natAbs : Int) = (d₁ : Int) := by
    exact_mod_cast hcancel1
  have hc2 : ((d₂ / d₂.gcd n₂.natAbs : Nat) : Int) * (d₂.gcd n₂.natAbs : Int) = (d₂ : Int) := by
    exact_mod_cast hcancel2
  have hlhs : ((n₁ / (d₁.gcd n₁.natAbs : Int)) * ((d₂ / d₂.gcd n₂.natAbs : Nat) : Int)) *
      ((d₁.gcd n₁.natAbs : Int) * (d₂.gcd n₂.natAbs : Int)) = n₁ * (d₂ : Int) := by
    calc ((n₁ / (d₁.gcd n₁.natAbs : Int)) * ((d₂ / d₂.gcd n₂.natAbs : Nat) : Int)) *
          ((d₁.gcd n₁.natAbs : Int) * (d₂.gcd n₂.natAbs : Int))
        = ((n₁ / (d₁.gcd n₁.natAbs : Int)) * (d₁.gcd n₁.natAbs : Int)) *
          (((d₂ / d₂.gcd n₂.natAbs : Nat) : Int) * (d₂.gcd n₂.natAbs : Int)) := by
          rw [Int.mul_assoc, Int.mul_left_comm ((d₂ / d₂.gcd n₂.natAbs : Nat) : Int), ← Int.mul_assoc]
      _ = n₁ * (d₂ : Int) := by rw [hnd1, hc2]
  have hrhs : ((n₂ / (d₂.gcd n₂.natAbs : Int)) * ((d₁ / d₁.gcd n₁.natAbs : Nat) : Int)) *
      ((d₁.gcd n₁.natAbs : Int) * (d₂.gcd n₂.natAbs : Int)) = n₂ * (d₁ : Int) := by
    calc ((n₂ / (d₂.gcd n₂.natAbs : Int)) * ((d₁ / d₁.gcd n₁.natAbs : Nat) : Int)) *
          ((d₁.gcd n₁.natAbs : Int) * (d₂.gcd n₂.natAbs : Int))
        = ((n₂ / (d₂.gcd n₂.natAbs : Int)) * (d₂.gcd n₂.natAbs : Int)) *
          (((d₁ / d₁.gcd n₁.natAbs : Nat) : Int) * (d₁.gcd n₁.natAbs : Int)) := by
          rw [Int.mul_comm (d₁.gcd n₁.natAbs : Int) (d₂.gcd n₂.natAbs : Int),
            Int.mul_assoc, Int.mul_left_comm ((d₁ / d₁.gcd n₁.natAbs : Nat) : Int), ← Int.mul_assoc]
      _ = n₂ * (d₁ : Int) := by rw [hnd2, hc1]
  constructor
  · intro h
    have := Int.mul_lt_mul_of_pos_right h hprodPos
    rwa [hlhs, hrhs] at this
  · intro h
    rw [← hlhs, ← hrhs] at h
    exact Int.lt_of_mul_lt_mul_right h (Int.le_of_lt hprodPos)

private theorem mkRat_lt_rat_iff {n : Int} {d : Nat} (hd : 0 < d) (q : Rat) :
    mkRat n d < q ↔ n * (q.den : Int) < q.num * (d : Int) := by
  have h := mkRat_lt_iff (n₁ := n) (n₂ := q.num) (d₁ := d) (d₂ := q.den) hd q.den_pos
  simpa [Rat.mkRat_self] using h

private theorem gcd_ten_pow_add_one (m : Int) (p k : Nat) :
    (10 ^ (p + k + 1)).gcd (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs = 1 := by
  have h10 : (10 : Nat).Coprime (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs := by
    have hmod : (m * ((10 ^ (k + 1) : Nat) : Int) + 1) % 10 = 1 := by
      have hpow : ((10 ^ (k + 1) : Nat) : Int) = ((10 ^ k : Nat) : Int) * 10 := by
        exact_mod_cast Nat.pow_succ 10 k
      rw [hpow, ← Int.mul_assoc, Int.add_emod, Int.mul_emod_left]
      decide
    have h2 : ¬ (2 ∣ (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs) := by
      intro hd
      obtain ⟨t, ht⟩ := nat_dvd_natAbs_to_int hd
      omega
    have h5 : ¬ (5 ∣ (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs) := by
      intro hd
      obtain ⟨t, ht⟩ := nat_dvd_natAbs_to_int hd
      omega
    let g := (10 : Nat).gcd (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs
    have hdvd10 : g ∣ 10 := Nat.gcd_dvd_left ..
    have hdvdN : g ∣ (m * ((10 ^ (k + 1) : Nat) : Int) + 1).natAbs := Nat.gcd_dvd_right ..
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by decide)
    show g = 1
    have hgle : g ≤ 10 := Nat.le_of_dvd (by decide) hdvd10
    have hmod10 : 10 % g = 0 := Nat.mod_eq_zero_of_dvd hdvd10
    have h10mod : ∀ n < 11, 0 < n → 10 % n = 0 → n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10 := by decide
    have hcases : g = 1 ∨ g = 2 ∨ g = 5 ∨ g = 10 := h10mod g (by omega) hgpos hmod10
    rcases hcases with h1 | h2e | h5e | h10e
    · exact h1
    · exact (h2 (h2e ▸ hdvdN)).elim
    · exact (h5 (h5e ▸ hdvdN)).elim
    · exact (h2 (Nat.dvd_trans (by decide : 2 ∣ 10) (h10e ▸ hdvdN))).elim
  exact (Nat.Coprime.pow_left (p + k + 1) h10).gcd_eq_one

private def properDecStep (m : Int) (p k : Nat) : Rat :=
  mkRat (m * ((10 ^ (k + 1) : Nat) : Int) + 1) (10 ^ (p + k + 1))

private theorem properDecStep_den (m : Int) (p k : Nat) :
    (properDecStep m p k).den = 10 ^ (p + k + 1) := by
  unfold properDecStep
  rw [Rat.den_mkRat, ite_eq_right (Nat.ne_of_gt (ten_pow_pos _)),
    gcd_ten_pow_add_one, Nat.div_one]

private theorem properDecStep_isProperDec (m : Int) (p k : Nat) :
    DecimalValue (properDecStep m p k) ∧ (properDecStep m p k).den ≠ 1 := by
  refine ⟨⟨m * ((10 ^ (k + 1) : Nat) : Int) + 1, p + k + 1, rfl⟩, ?_⟩
  rw [properDecStep_den]
  have h10 : 10 ≤ 10 ^ (p + k + 1) := by
    calc 10 = 10 ^ 1 := by decide
      _ ≤ 10 ^ (p + k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem properDecStep_inj (m : Int) (p : Nat) {k₁ k₂ : Nat}
    (h : properDecStep m p k₁ = properDecStep m p k₂) : k₁ = k₂ := by
  have hd := congrArg Rat.den h
  rw [properDecStep_den, properDecStep_den] at hd
  have hpow : p + k₁ + 1 = p + k₂ + 1 :=
    (Nat.pow_right_inj (by decide : 1 < 10)).mp hd
  omega

private theorem properDecStep_between (m : Int) (p k : Nat) :
    mkRat m (10 ^ p) < properDecStep m p k ∧ properDecStep m p k < mkRat (m + 1) (10 ^ p) := by
  unfold properDecStep
  have hp : 0 < (10 : Nat) ^ p := ten_pow_pos p
  have hpk : 0 < (10 : Nat) ^ (p + k + 1) := ten_pow_pos (p + k + 1)
  have hmul : (10 : Nat) ^ (p + k + 1) = 10 ^ p * 10 ^ (k + 1) := by
    rw [Nat.add_assoc, Nat.pow_add]
  have hkpos : (1 : Int) < ((10 ^ (k + 1) : Nat) : Int) := by
    have : 10 ≤ 10 ^ (k + 1) := by
      calc 10 = 10 ^ 1 := by decide
        _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpz : (0 : Int) < ((10 ^ p : Nat) : Int) := by omega
  have hm : ((10 ^ (p + k + 1) : Nat) : Int) = ((10 ^ p : Nat) : Int) * ((10 ^ (k + 1) : Nat) : Int) := by
    exact_mod_cast hmul
  constructor
  · rw [mkRat_lt_iff hp hpk, hm]
    calc m * (((10 ^ p : Nat) : Int) * ((10 ^ (k + 1) : Nat) : Int))
        = (m * ((10 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) := by
          rw [Int.mul_left_comm, Int.mul_comm ((10 ^ p : Nat) : Int)]
      _ < (m * ((10 ^ (k + 1) : Nat) : Int) + 1) * ((10 ^ p : Nat) : Int) :=
          Int.mul_lt_mul_of_pos_right (by omega) hpz
  · rw [mkRat_lt_iff hpk hp, hm]
    calc (m * ((10 ^ (k + 1) : Nat) : Int) + 1) * ((10 ^ p : Nat) : Int)
        < (m * ((10 ^ (k + 1) : Nat) : Int) + ((10 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) :=
          Int.mul_lt_mul_of_pos_right (by omega) hpz
      _ = ((m + 1) * ((10 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) := by
          rw [Int.add_mul m 1, Int.one_mul]
      _ = (m + 1) * (((10 ^ p : Nat) : Int) * ((10 ^ (k + 1) : Nat) : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm ((10 ^ (k + 1) : Nat) : Int)]

private def nonDecRatStep (m : Int) (p k : Nat) : Rat :=
  mkRat (m * ((3 ^ (k + 1) : Nat) : Int) + 1) (10 ^ p * 3 ^ (k + 1))

private theorem dvd_of_three_dvd_mul {a b : Nat} (h : 3 ∣ a * b) (hb : ¬ 3 ∣ b) : 3 ∣ a := by
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hbm : b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hmod : (a * b) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod] at hmod
  rcases ha with h0 | h1 | h2
  · exact Nat.dvd_of_mod_eq_zero h0
  · rcases hbm with hb1 | hb2
    · rw [h1, hb1] at hmod; cases hmod
    · rw [h1, hb2] at hmod; cases hmod
  · rcases hbm with hb1 | hb2
    · rw [h2, hb1] at hmod; cases hmod
    · rw [h2, hb2] at hmod; cases hmod

private theorem nonDecRatStep_not_decimal (m : Int) (p k : Nat) :
    ¬ DecimalValue (nonDecRatStep m p k) := by
  intro hdec
  rcases hdec with ⟨c, j, heq⟩
  have hj : (nonDecRatStep m p k).den ∣ 10 ^ j := by
    rw [heq, Rat.den_mkRat, ite_eq_right (Nat.ne_of_gt (ten_pow_pos j))]
    exact ⟨_, (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩
  have h3not : ¬ (3 ∣ (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs) := by
    intro hd
    have h3i := nat_dvd_natAbs_to_int hd
    have hpow : ((3 ^ (k + 1) : Nat) : Int) = ((3 ^ k : Nat) : Int) * 3 := by
      exact_mod_cast Nat.pow_succ 3 k
    rw [hpow, ← Int.mul_assoc] at h3i
    obtain ⟨t, ht⟩ := h3i
    omega
  have hcop3g : ¬ (3 ∣ (10 ^ p * 3 ^ (k + 1)).gcd (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs) :=
    fun hd => h3not (Nat.dvd_trans hd (Nat.gcd_dvd_right ..))
  have h3inD : 3 ∣ 10 ^ p * 3 ^ (k + 1) := by
    refine ⟨10 ^ p * 3 ^ k, ?_⟩
    rw [Nat.pow_succ, Nat.mul_comm 3, Nat.mul_assoc]
  have hdenEq : (nonDecRatStep m p k).den =
      (10 ^ p * 3 ^ (k + 1)) / (10 ^ p * 3 ^ (k + 1)).gcd (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs := by
    unfold nonDecRatStep
    rw [Rat.den_mkRat, ite_eq_right (Nat.ne_of_gt (Nat.mul_pos (ten_pow_pos p) (three_pow_pos (k + 1))))]
  have h3den : 3 ∣ (nonDecRatStep m p k).den := by
    rw [hdenEq]
    have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left (10 ^ p * 3 ^ (k + 1))
      (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs)
    have h3prod : 3 ∣ ((10 ^ p * 3 ^ (k + 1)) /
        (10 ^ p * 3 ^ (k + 1)).gcd (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs) *
        (10 ^ p * 3 ^ (k + 1)).gcd (m * ((3 ^ (k + 1) : Nat) : Int) + 1).natAbs := by
      rwa [hmul]
    exact dvd_of_three_dvd_mul h3prod hcop3g
  have h3pow10 : 3 ∣ 10 ^ j := Nat.dvd_trans h3den hj
  have hcop : Nat.Coprime 3 (10 ^ j) := Nat.Coprime.pow_right j (by decide)
  have h1 : 3 ∣ 1 := by
    have hg := Nat.dvd_gcd (Nat.dvd_refl 3) h3pow10
    rwa [hcop.gcd_eq_one] at hg
  omega

private theorem nonDecRatStep_strictAnti (m : Int) (p : Nat) {k₁ k₂ : Nat} (hlt : k₁ < k₂) :
    nonDecRatStep m p k₂ < nonDecRatStep m p k₁ := by
  unfold nonDecRatStep
  have hd₁ : 0 < 10 ^ p * 3 ^ (k₁ + 1) := Nat.mul_pos (ten_pow_pos p) (three_pow_pos _)
  have hd₂ : 0 < 10 ^ p * 3 ^ (k₂ + 1) := Nat.mul_pos (ten_pow_pos p) (three_pow_pos _)
  rw [mkRat_lt_iff hd₂ hd₁]
  have hpow : (3 : Nat) ^ (k₁ + 1) < 3 ^ (k₂ + 1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega)
  have hpowI : ((3 ^ (k₁ + 1) : Nat) : Int) < ((3 ^ (k₂ + 1) : Nat) : Int) := by omega
  have hpz : (0 : Int) < ((10 ^ p : Nat) : Int) := by have := ten_pow_pos p; omega
  have hprod1 : ((10 ^ p * 3 ^ (k₁ + 1) : Nat) : Int) = ((10 ^ p : Nat) : Int) * ((3 ^ (k₁ + 1) : Nat) : Int) := by
    exact_mod_cast rfl
  have hprod2 : ((10 ^ p * 3 ^ (k₂ + 1) : Nat) : Int) = ((10 ^ p : Nat) : Int) * ((3 ^ (k₂ + 1) : Nat) : Int) := by
    exact_mod_cast rfl
  rw [hprod1, hprod2]
  have hA : (m * ((3 ^ (k₂ + 1) : Nat) : Int)) * (((10 ^ p : Nat) : Int) * ((3 ^ (k₁ + 1) : Nat) : Int)) =
      (m * ((3 ^ (k₁ + 1) : Nat) : Int)) * (((10 ^ p : Nat) : Int) * ((3 ^ (k₂ + 1) : Nat) : Int)) := by
    have h1 : ((3 ^ (k₂ + 1) : Nat) : Int) * (((10 ^ p : Nat) : Int) * ((3 ^ (k₁ + 1) : Nat) : Int)) =
        ((3 ^ (k₁ + 1) : Nat) : Int) * (((10 ^ p : Nat) : Int) * ((3 ^ (k₂ + 1) : Nat) : Int)) := by
      rw [Int.mul_left_comm ((3 ^ (k₂ + 1) : Nat) : Int),
        Int.mul_comm ((3 ^ (k₂ + 1) : Nat) : Int) ((3 ^ (k₁ + 1) : Nat) : Int),
        ← Int.mul_left_comm]
    rw [Int.mul_assoc m, h1, ← Int.mul_assoc m]
  have hB : ((10 ^ p : Nat) : Int) * ((3 ^ (k₁ + 1) : Nat) : Int) <
      ((10 ^ p : Nat) : Int) * ((3 ^ (k₂ + 1) : Nat) : Int) :=
    Int.mul_lt_mul_of_pos_left hpowI hpz
  rw [Int.add_mul, Int.add_mul, Int.one_mul, Int.one_mul, hA]
  omega

private theorem nonDecRatStep_inj (m : Int) (p : Nat) {k₁ k₂ : Nat}
    (h : nonDecRatStep m p k₁ = nonDecRatStep m p k₂) : k₁ = k₂ := by
  rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact (Rat.lt_irrefl (h ▸ nonDecRatStep_strictAnti m p hlt)).elim
  · exact heq
  · exact (Rat.lt_irrefl (h ▸ nonDecRatStep_strictAnti m p hgt)).elim

private theorem nonDecRatStep_between (m : Int) (p k : Nat) :
    mkRat m (10 ^ p) < nonDecRatStep m p k ∧ nonDecRatStep m p k < mkRat (m + 1) (10 ^ p) := by
  unfold nonDecRatStep
  have hp : 0 < (10 : Nat) ^ p := ten_pow_pos p
  have hpk : 0 < 10 ^ p * 3 ^ (k + 1) := Nat.mul_pos hp (three_pow_pos _)
  have hkpos : (1 : Int) < ((3 ^ (k + 1) : Nat) : Int) := by
    have : 3 ≤ 3 ^ (k + 1) := by
      calc 3 = 3 ^ 1 := by decide
        _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpz : (0 : Int) < ((10 ^ p : Nat) : Int) := by omega
  have hm : ((10 ^ p * 3 ^ (k + 1) : Nat) : Int) = ((10 ^ p : Nat) : Int) * ((3 ^ (k + 1) : Nat) : Int) := by
    exact_mod_cast rfl
  constructor
  · rw [mkRat_lt_iff hp hpk, hm]
    calc m * (((10 ^ p : Nat) : Int) * ((3 ^ (k + 1) : Nat) : Int))
        = (m * ((3 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) := by
          rw [Int.mul_left_comm, Int.mul_comm ((10 ^ p : Nat) : Int)]
      _ < (m * ((3 ^ (k + 1) : Nat) : Int) + 1) * ((10 ^ p : Nat) : Int) :=
          Int.mul_lt_mul_of_pos_right (by omega) hpz
  · rw [mkRat_lt_iff hpk hp, hm]
    calc (m * ((3 ^ (k + 1) : Nat) : Int) + 1) * ((10 ^ p : Nat) : Int)
        < (m * ((3 ^ (k + 1) : Nat) : Int) + ((3 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) :=
          Int.mul_lt_mul_of_pos_right (by omega) hpz
      _ = ((m + 1) * ((3 ^ (k + 1) : Nat) : Int)) * ((10 ^ p : Nat) : Int) := by
          rw [Int.add_mul m 1, Int.one_mul]
      _ = (m + 1) * (((10 ^ p : Nat) : Int) * ((3 ^ (k + 1) : Nat) : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm ((3 ^ (k + 1) : Nat) : Int)]

private def openBracket (lo hi : Rat) : Int × Nat :=
  let d := hi - lo
  let p := pow10Above (2 * d.den)
  let m := (lo * Rat.ofInt (10 ^ p : Nat)).floor + 1
  (m, p)

private theorem openBracket_spec {lo hi : Rat} (hlt : lo < hi) :
    let (m, p) := openBracket lo hi
    lo < mkRat m (10 ^ p) ∧ mkRat (m + 1) (10 ^ p) < hi := by
  dsimp only [openBracket]
  let d := hi - lo
  let p := pow10Above (2 * d.den)
  let m := (lo * Rat.ofInt (10 ^ p : Nat)).floor + 1
  have hp : 0 < (10 : Nat) ^ p := ten_pow_pos p
  have hpz : (0 : Int) < ((10 ^ p : Nat) : Int) := by omega
  have hpR : (0 : Rat) < Rat.ofInt ((10 ^ p : Nat) : Int) := by
    rw [Rat.lt_iff]
    simpa [Rat.ofInt] using hpz
  have h1 : lo < mkRat m (10 ^ p) := by
    have hfl : lo * Rat.ofInt ((10 ^ p : Nat) : Int) < Rat.ofInt m := Rat.lt_floor_add_one _
    have hdiv := Rat.mul_lt_mul_of_pos_right hfl (Rat.inv_pos.mpr hpR)
    have hcancel : lo * Rat.ofInt ((10 ^ p : Nat) : Int) * (Rat.ofInt ((10 ^ p : Nat) : Int))⁻¹ = lo := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hpR), Rat.mul_one]
    rw [hcancel] at hdiv
    have hmk : mkRat m (10 ^ p) = Rat.ofInt m * (Rat.ofInt ((10 ^ p : Nat) : Int))⁻¹ := by
      rw [Rat.mkRat_eq_div, Rat.div_def]; rfl
    rw [hmk]; exact hdiv
  have h2 : mkRat (m + 1) (10 ^ p) < hi := by
    have hfl : Rat.ofInt (lo * Rat.ofInt ((10 ^ p : Nat) : Int)).floor ≤ lo * Rat.ofInt ((10 ^ p : Nat) : Int) :=
      Rat.floor_le _
    have hle1 : mkRat (m + 1) (10 ^ p) ≤ lo + mkRat 2 (10 ^ p) := by
      have hnum : Rat.ofInt (m + 1) ≤ lo * Rat.ofInt ((10 ^ p : Nat) : Int) + Rat.ofInt 2 := by
        have hm : Rat.ofInt (m + 1) = Rat.ofInt (lo * Rat.ofInt ((10 ^ p : Nat) : Int)).floor + Rat.ofInt 2 := by
          have : m + 1 = (lo * Rat.ofInt ((10 ^ p : Nat) : Int)).floor + 2 := by omega
          rw [this]
          apply Rat.ext <;> simp [Rat.ofInt, Rat.add_def]
        rw [hm]
        exact Rat.add_le_add_right.mpr hfl
      have hdiv := Rat.mul_le_mul_of_nonneg_right hnum (Rat.le_of_lt (Rat.inv_pos.mpr hpR))
      rw [Rat.add_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hpR), Rat.mul_one] at hdiv
      have hmk1 : mkRat (m + 1) (10 ^ p) = Rat.ofInt (m + 1) * (Rat.ofInt ((10 ^ p : Nat) : Int))⁻¹ := by
        rw [Rat.mkRat_eq_div, Rat.div_def]; rfl
      have hmk2 : mkRat 2 (10 ^ p) = Rat.ofInt 2 * (Rat.ofInt ((10 ^ p : Nat) : Int))⁻¹ := by
        rw [Rat.mkRat_eq_div, Rat.div_def]; rfl
      rw [hmk1, hmk2]; exact hdiv
    have hdpos : (0 : Rat) < d := by
      have hadd : lo + 0 < lo + d := by
        have hsum : lo + d = hi := by
          dsimp [d]; rw [Rat.sub_eq_add_neg, Rat.add_comm hi, ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
        rw [Rat.add_zero, hsum]; exact hlt
      exact (Rat.add_lt_add_left).mp hadd
    have hdnum : 1 ≤ d.num := by
      rw [Rat.lt_iff] at hdpos
      simp at hdpos
      omega
    have hgt : 2 * d.den < 10 ^ p := pow10Above_gt (2 * d.den)
    have hgap : mkRat 2 (10 ^ p) < d := by
      rw [mkRat_lt_rat_iff hp d]
      have h1' : (2 : Int) * (d.den : Int) < ((10 ^ p : Nat) : Int) := by exact_mod_cast hgt
      have h2' : ((10 ^ p : Nat) : Int) ≤ d.num * ((10 ^ p : Nat) : Int) := by
        calc ((10 ^ p : Nat) : Int) = 1 * ((10 ^ p : Nat) : Int) := (Int.one_mul _).symm
          _ ≤ d.num * ((10 ^ p : Nat) : Int) := Int.mul_le_mul_of_nonneg_right hdnum (Int.le_of_lt hpz)
      omega
    have hsum : lo + mkRat 2 (10 ^ p) < hi := by
      have h1' := (Rat.add_lt_add_left (c := lo)).mpr hgap
      have heq : lo + d = hi := by
        dsimp [d]; rw [Rat.sub_eq_add_neg, Rat.add_comm hi, ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
      rwa [heq] at h1'
    exact rat_lt_of_le_of_lt hle1 hsum
  exact ⟨h1, h2⟩

def sampleProperDecBounds (K : Nat) (b : RatBounds) : List Rat :=
  match b.lower, b.upper with
  | none, none => (List.range K).map fun k => properDecStep 0 0 k
  | some ⟨lo, _⟩, none => (List.range K).map fun k => properDecStep (lo.floor + 1) 0 k
  | none, some ⟨hi, _⟩ => (List.range K).map fun k => properDecStep (hi.ceil - 2) 0 k
  | some ⟨lo, loInc⟩, some ⟨hi, hiInc⟩ =>
    if lo < hi then
      let (m, p) := openBracket lo hi
      (List.range K).map fun k => properDecStep m p k
    else if lo == hi && loInc && hiInc && checkDecimalValue lo && lo.den != 1 then
      [lo]
    else []

theorem sampleProperDecBounds_nodup (K : Nat) (b : RatBounds) :
    (sampleProperDecBounds K b).Nodup := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleProperDecBounds]
  · exact nodup_map_inj (properDecStep_inj 0 0) List.nodup_range
  · rename_i hi; exact nodup_map_inj (properDecStep_inj (hi.val.ceil - 2) 0) List.nodup_range
  · rename_i lo; exact nodup_map_inj (properDecStep_inj (lo.val.floor + 1) 0) List.nodup_range
  · rename_i lo hi
    split
    · exact nodup_map_inj (properDecStep_inj _ _) List.nodup_range
    · split
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      · exact List.nodup_nil

theorem sampleProperDecBounds_sound (K : Nat) (b : RatBounds) {q : Rat}
    (hq : q ∈ sampleProperDecBounds K b) :
    b.contains q ∧ DecimalValue q ∧ q.den ≠ 1 := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleProperDecBounds] at hq
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨⟨trivial, trivial⟩, properDecStep_isProperDec 0 0 k⟩
  · rename_i hi
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    have hlt := (properDecStep_between (hi.val.ceil - 2) 0 k).2
    have htop : mkRat (hi.val.ceil - 2 + 1) (10 ^ 0) < hi.val := by
      have : mkRat (hi.val.ceil - 2 + 1) (10 ^ 0) = Rat.ofInt (hi.val.ceil - 1) := by
        apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat]; omega
      rw [this]
      exact Rat.lt_ceil_iff.mp (by omega)
    have hqlt : properDecStep (hi.val.ceil - 2) 0 k < hi.val := rat_lt_trans hlt htop
    refine ⟨⟨trivial, ?_⟩, properDecStep_isProperDec _ 0 k⟩
    cases hi.inclusive <;> simp [RatEndpoint.holdsUpper, hqlt, Rat.le_of_lt hqlt]
  · rename_i lo
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    have hgt := (properDecStep_between (lo.val.floor + 1) 0 k).1
    have hbot : lo.val < mkRat (lo.val.floor + 1) (10 ^ 0) := by
      have : mkRat (lo.val.floor + 1) (10 ^ 0) = Rat.ofInt (lo.val.floor + 1) := by
        apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat]
      rw [this]
      exact Rat.lt_floor_add_one lo.val
    have hqgt : lo.val < properDecStep (lo.val.floor + 1) 0 k := rat_lt_trans hbot hgt
    refine ⟨⟨?_, trivial⟩, properDecStep_isProperDec _ 0 k⟩
    cases lo.inclusive <;> simp [RatEndpoint.holdsLower, hqgt, Rat.le_of_lt hqgt]
  · rename_i lo hi
    split at hq
    · rename_i hlt
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
      have hbr := openBracket_spec hlt
      have hbt := properDecStep_between (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k
      have hlo : lo.val < properDecStep (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k :=
        rat_lt_trans hbr.1 hbt.1
      have hhi : properDecStep (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k < hi.val :=
        rat_lt_trans hbt.2 hbr.2
      refine ⟨⟨?_, ?_⟩, properDecStep_isProperDec _ _ k⟩
      · cases lo.inclusive <;> simp [RatEndpoint.holdsLower, hlo, Rat.le_of_lt hlo]
      · cases hi.inclusive <;> simp [RatEndpoint.holdsUpper, hhi, Rat.le_of_lt hhi]
    · split at hq
      · rename_i hcond
        obtain rfl := List.mem_singleton.mp hq
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcond
        obtain ⟨⟨⟨⟨heq, hli⟩, hhi⟩, hdec⟩, hden⟩ := hcond
        refine ⟨⟨?_, ?_⟩, (checkDecimalValue_iff _).mp hdec, hden⟩
        · simp [RatEndpoint.holdsLower, hli]
        · simp [RatEndpoint.holdsUpper, hhi, heq]
      · cases hq

theorem properDecimalWitnesses_between (K : Nat) {lo hi : Rat} (h : lo < hi) :
    ∃ xs : List Rat, xs.length = K ∧ xs.Nodup ∧
      ∀ q ∈ xs, lo < q ∧ q < hi ∧ DecimalValue q ∧ q.den ≠ 1 := by
  let b : RatBounds := ⟨some ⟨lo, false⟩, some ⟨hi, false⟩⟩
  refine ⟨sampleProperDecBounds K b, by simp [sampleProperDecBounds, b, h],
    sampleProperDecBounds_nodup K b, ?_⟩
  intro q hq
  obtain ⟨⟨hl, hu⟩, hd, hn⟩ := sampleProperDecBounds_sound K b hq
  exact ⟨hl, hu, hd, hn⟩

theorem sampleProperDecBounds_complete_of_lt (K : Nat) (b : RatBounds)
    (hlt : (sampleProperDecBounds K b).length < K) {q : Rat}
    (hq : b.contains q) (hdec : DecimalValue q) (hden : q.den ≠ 1) :
    q ∈ sampleProperDecBounds K b := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleProperDecBounds] at hlt ⊢
  · simp at hlt
  · simp at hlt
  · simp at hlt
  · rename_i lo hi
    rcases lo with ⟨lov, loi⟩
    rcases hi with ⟨hiv, hii⟩
    obtain ⟨h1, h2⟩ := hq
    simp only [Option.elim_some, RatEndpoint.holdsLower, RatEndpoint.holdsUpper] at h1 h2
    by_cases hlt' : lov < hiv
    · simp [hlt'] at hlt
    · simp only [hlt', ↓reduceIte] at hlt ⊢
      have hle : lov ≤ q := by cases loi <;> simp at h1; exact Rat.le_of_lt h1; exact h1
      have hle2 : q ≤ hiv := by cases hii <;> simp at h2; exact Rat.le_of_lt h2; exact h2
      have hlov_le_hiv : lov ≤ hiv := Rat.le_trans hle hle2
      have heq : lov = hiv := by
        rcases rat_trichotomy lov hiv with h | h | h
        · exact (hlt' h).elim
        · exact (Rat.not_lt.mpr hlov_le_hiv h).elim
        · exact h
      subst heq
      have hqeq : q = lov := Rat.le_antisymm hle2 hle
      subst hqeq
      have hloi : loi = true := by
        cases loi
        · simp at h1
        · rfl
      have hhii : hii = true := by
        cases hii
        · simp at h2
        · rfl
      have hchk : checkDecimalValue q = true := (checkDecimalValue_iff q).mpr hdec
      simp [hloi, hhii, hchk, hden]

def sampleNonDecRatBounds (K : Nat) (b : RatBounds) : List Rat :=
  match b.lower, b.upper with
  | none, none => (List.range K).map fun k => nonDecRatStep 0 0 k
  | some ⟨lo, _⟩, none => (List.range K).map fun k => nonDecRatStep (lo.floor + 1) 0 k
  | none, some ⟨hi, _⟩ => (List.range K).map fun k => nonDecRatStep (hi.ceil - 2) 0 k
  | some ⟨lo, loInc⟩, some ⟨hi, hiInc⟩ =>
    if lo < hi then
      let (m, p) := openBracket lo hi
      (List.range K).map fun k => nonDecRatStep m p k
    else if lo == hi && loInc && hiInc && !checkDecimalValue lo then
      [lo]
    else []

theorem sampleNonDecRatBounds_nodup (K : Nat) (b : RatBounds) :
    (sampleNonDecRatBounds K b).Nodup := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleNonDecRatBounds]
  · exact nodup_map_inj (nonDecRatStep_inj 0 0) List.nodup_range
  · rename_i hi; exact nodup_map_inj (nonDecRatStep_inj (hi.val.ceil - 2) 0) List.nodup_range
  · rename_i lo; exact nodup_map_inj (nonDecRatStep_inj (lo.val.floor + 1) 0) List.nodup_range
  · rename_i lo hi
    split
    · exact nodup_map_inj (nonDecRatStep_inj _ _) List.nodup_range
    · split
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      · exact List.nodup_nil

theorem sampleNonDecRatBounds_sound (K : Nat) (b : RatBounds) {q : Rat}
    (hq : q ∈ sampleNonDecRatBounds K b) :
    b.contains q ∧ ¬ DecimalValue q := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleNonDecRatBounds] at hq
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨⟨trivial, trivial⟩, nonDecRatStep_not_decimal 0 0 k⟩
  · rename_i hi
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    have hlt := (nonDecRatStep_between (hi.val.ceil - 2) 0 k).2
    have htop : mkRat (hi.val.ceil - 2 + 1) (10 ^ 0) < hi.val := by
      have : mkRat (hi.val.ceil - 2 + 1) (10 ^ 0) = Rat.ofInt (hi.val.ceil - 1) := by
        apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat]; omega
      rw [this]
      exact Rat.lt_ceil_iff.mp (by omega)
    have hqlt : nonDecRatStep (hi.val.ceil - 2) 0 k < hi.val := rat_lt_trans hlt htop
    refine ⟨⟨trivial, ?_⟩, nonDecRatStep_not_decimal _ 0 k⟩
    cases hi.inclusive <;> simp [RatEndpoint.holdsUpper, hqlt, Rat.le_of_lt hqlt]
  · rename_i lo
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    have hgt := (nonDecRatStep_between (lo.val.floor + 1) 0 k).1
    have hbot : lo.val < mkRat (lo.val.floor + 1) (10 ^ 0) := by
      have : mkRat (lo.val.floor + 1) (10 ^ 0) = Rat.ofInt (lo.val.floor + 1) := by
        apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat]
      rw [this]
      exact Rat.lt_floor_add_one lo.val
    have hqgt : lo.val < nonDecRatStep (lo.val.floor + 1) 0 k := rat_lt_trans hbot hgt
    refine ⟨⟨?_, trivial⟩, nonDecRatStep_not_decimal _ 0 k⟩
    cases lo.inclusive <;> simp [RatEndpoint.holdsLower, hqgt, Rat.le_of_lt hqgt]
  · rename_i lo hi
    split at hq
    · rename_i hlt
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
      have hbr := openBracket_spec hlt
      have hbt := nonDecRatStep_between (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k
      have hlo : lo.val < nonDecRatStep (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k :=
        rat_lt_trans hbr.1 hbt.1
      have hhi : nonDecRatStep (openBracket lo.val hi.val).1 (openBracket lo.val hi.val).2 k < hi.val :=
        rat_lt_trans hbt.2 hbr.2
      refine ⟨⟨?_, ?_⟩, nonDecRatStep_not_decimal _ _ k⟩
      · cases lo.inclusive <;> simp [RatEndpoint.holdsLower, hlo, Rat.le_of_lt hlo]
      · cases hi.inclusive <;> simp [RatEndpoint.holdsUpper, hhi, Rat.le_of_lt hhi]
    · split at hq
      · rename_i hcond
        obtain rfl := List.mem_singleton.mp hq
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
        obtain ⟨⟨⟨heq, hli⟩, hhi⟩, hndec⟩ := hcond
        refine ⟨⟨?_, ?_⟩, fun hd => by rw [(checkDecimalValue_iff _).mpr hd] at hndec; cases hndec⟩
        · simp [RatEndpoint.holdsLower, hli]
        · simp [RatEndpoint.holdsUpper, hhi, heq]
      · cases hq

theorem sampleNonDecRatBounds_complete_of_lt (K : Nat) (b : RatBounds)
    (hlt : (sampleNonDecRatBounds K b).length < K) {q : Rat}
    (hq : b.contains q) (hndec : ¬ DecimalValue q) :
    q ∈ sampleNonDecRatBounds K b := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleNonDecRatBounds] at hlt ⊢
  · simp at hlt
  · simp at hlt
  · simp at hlt
  · rename_i lo hi
    rcases lo with ⟨lov, loi⟩
    rcases hi with ⟨hiv, hii⟩
    obtain ⟨h1, h2⟩ := hq
    simp only [Option.elim_some, RatEndpoint.holdsLower, RatEndpoint.holdsUpper] at h1 h2
    by_cases hlt' : lov < hiv
    · simp [hlt'] at hlt
    · simp only [hlt', ↓reduceIte] at hlt ⊢
      have hle : lov ≤ q := by cases loi <;> simp at h1; exact Rat.le_of_lt h1; exact h1
      have hle2 : q ≤ hiv := by cases hii <;> simp at h2; exact Rat.le_of_lt h2; exact h2
      have hlov_le_hiv : lov ≤ hiv := Rat.le_trans hle hle2
      have heq : lov = hiv := by
        rcases rat_trichotomy lov hiv with h | h | h
        · exact (hlt' h).elim
        · exact (Rat.not_lt.mpr hlov_le_hiv h).elim
        · exact h
      subst heq
      have hqeq : q = lov := Rat.le_antisymm hle2 hle
      subst hqeq
      have hloi : loi = true := by
        cases loi
        · simp at h1
        · rfl
      have hhii : hii = true := by
        cases hii
        · simp at h2
        · rfl
      have hchk : checkDecimalValue q = false := by
        cases h : checkDecimalValue q
        · rfl
        · exact (hndec ((checkDecimalValue_iff q).mp h)).elim
      simp [hloi, hhii, hchk]

def sampleProperDecSet (K : Nat) (bs : List RatBounds) : List Rat :=
  (bs.flatMap (sampleProperDecBounds K)).eraseDups

theorem sampleProperDecSet_nodup (K : Nat) (bs : List RatBounds) :
    (sampleProperDecSet K bs).Nodup := nodup_eraseDups_list _

theorem sampleProperDecSet_sound (K : Nat) (bs : List RatBounds) {q : Rat}
    (hq : q ∈ sampleProperDecSet K bs) :
    (∃ b ∈ bs, b.contains q) ∧ DecimalValue q ∧ q.den ≠ 1 := by
  obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hq)
  obtain ⟨hc, hd, hn⟩ := sampleProperDecBounds_sound K b hqb
  exact ⟨⟨b, hb, hc⟩, hd, hn⟩

theorem sampleProperDecSet_complete_of_lt (K : Nat) (bs : List RatBounds)
    (hlt : (sampleProperDecSet K bs).length < K) {q : Rat}
    (hq : ∃ b ∈ bs, b.contains q) (hdec : DecimalValue q) (hden : q.den ≠ 1) :
    q ∈ sampleProperDecSet K bs := by
  obtain ⟨b, hb, hqb⟩ := hq
  have hsub : ∀ x ∈ sampleProperDecBounds K b, x ∈ sampleProperDecSet K bs := fun x hx =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hx⟩)
  have hle := (sampleProperDecBounds_nodup K b).length_le_of_subset hsub
  exact hsub q (sampleProperDecBounds_complete_of_lt K b (Nat.lt_of_le_of_lt hle hlt) hqb hdec hden)

def sampleNonDecRatSet (K : Nat) (bs : List RatBounds) : List Rat :=
  (bs.flatMap (sampleNonDecRatBounds K)).eraseDups

theorem sampleNonDecRatSet_nodup (K : Nat) (bs : List RatBounds) :
    (sampleNonDecRatSet K bs).Nodup := nodup_eraseDups_list _

theorem sampleNonDecRatSet_sound (K : Nat) (bs : List RatBounds) {q : Rat}
    (hq : q ∈ sampleNonDecRatSet K bs) :
    (∃ b ∈ bs, b.contains q) ∧ ¬ DecimalValue q := by
  obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hq)
  obtain ⟨hc, hnd⟩ := sampleNonDecRatBounds_sound K b hqb
  exact ⟨⟨b, hb, hc⟩, hnd⟩

theorem sampleNonDecRatSet_complete_of_lt (K : Nat) (bs : List RatBounds)
    (hlt : (sampleNonDecRatSet K bs).length < K) {q : Rat}
    (hq : ∃ b ∈ bs, b.contains q) (hndec : ¬ DecimalValue q) :
    q ∈ sampleNonDecRatSet K bs := by
  obtain ⟨b, hb, hqb⟩ := hq
  have hsub : ∀ x ∈ sampleNonDecRatBounds K b, x ∈ sampleNonDecRatSet K bs := fun x hx =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hx⟩)
  have hle := (sampleNonDecRatBounds_nodup K b).length_le_of_subset hsub
  exact hsub q (sampleNonDecRatBounds_complete_of_lt K b (Nat.lt_of_le_of_lt hle hlt) hqb hndec)

/-! ### 3. Numeric atomic classification (`NumericKind`, `extractNumAtom`) -/

inductive NumericKind where
  | int
  | dec
  | rat
  deriving DecidableEq, Repr

def numericBase (t : IRI) : Option (NumericKind × RatBounds) :=
  if t == xsd "decimal" then some (.dec, {})
  else if t == owlRational || t == owlReal then some (.rat, {})
  else (integerBounds t).map fun b => (.int, intBoundsToRatBounds b)

def ratFacetBounds (f : Facet) : Option RatBounds :=
  match orderFacet f.name, decodeLiteral f.bound with
  | some .minInclusive, some (.number b) => some { lower := some ⟨b, true⟩ }
  | some .maxInclusive, some (.number b) => some { upper := some ⟨b, true⟩ }
  | some .minExclusive, some (.number b) => some { lower := some ⟨b, false⟩ }
  | some .maxExclusive, some (.number b) => some { upper := some ⟨b, false⟩ }
  | _, _ => none

def foldRatFacetBounds (acc : RatBounds) : List Facet → Option RatBounds
  | [] => some acc
  | f :: fs => do
    let fb ← ratFacetBounds f
    foldRatFacetBounds (acc.intersect fb) fs

def extractNumAtom : DataRange → Option (NumericKind × RatBounds)
  | .datatype t => numericBase t
  | .restriction t fs => do
    let (kind, base) ← numericBase t
    let bounds ← foldRatFacetBounds base fs
    some (kind, bounds)
  | _ => none

private def aboveFacetBounds (f : Facet) : Option RatBounds :=
  (ratFacetBounds f).map fun b =>
    ⟨b.lower.map (fun e => ⟨e.val, true⟩), b.upper.map (fun e => ⟨e.val, false⟩)⟩

private def foldAboveFacetBounds (acc : RatBounds) : List Facet → Option RatBounds
  | [] => some acc
  | f :: fs => (aboveFacetBounds f).bind fun fb => foldAboveFacetBounds (acc.intersect fb) fs

def extractIrrationalBounds : DataRange → Option RatBounds
  | .datatype t => if t = owlReal then some {} else none
  | .restriction t fs => if t = owlReal then foldAboveFacetBounds {} fs else none
  | _ => none

def NumericKind.holds : NumericKind → Rat → Prop
  | .int, q => q.den = 1
  | .dec, q => DecimalValue q
  | .rat, _ => True

instance (k : NumericKind) (q : Rat) : Decidable (k.holds q) := by
  cases k <;> unfold NumericKind.holds <;> infer_instance

theorem numericBase_supported {t : IRI} {kind : NumericKind} {base : RatBounds}
    (h : numericBase t = some (kind, base)) : supportedDatatype t = true := by
  unfold numericBase at h
  split at h
  · rename_i hd; rw [beq_iff_eq.mp hd]; decide
  · split at h
    · rename_i hr
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · rw [beq_iff_eq.mp h1]; decide
      · rw [beq_iff_eq.mp h2]; decide
    · obtain ⟨b, hb, _⟩ := Option.map_eq_some_iff.mp h
      exact integerBounds_supported hb

theorem valueSpace_numericBase_iff {t : IRI} {kind : NumericKind} {base : RatBounds}
    (h : numericBase t = some (kind, base)) (v : Value)
    (hnot : ∀ q, v ≠ .irrational q) :
    valueSpace t v ↔ ∃ q : Rat, kind.holds q ∧ base.contains q ∧ v = .number q := by
  unfold numericBase at h
  split at h
  · rename_i hd
    have ht := beq_iff_eq.mp hd; subst ht
    cases h
    rw [valueSpace_decimal_iff]
    exact exists_congr fun q => by simp [NumericKind.holds, RatBounds.contains]
  · split at h
    · rename_i hr
      cases h
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · have ht := beq_iff_eq.mp h1; subst ht
        rw [valueSpace_rational_iff]
        exact exists_congr fun q => by simp [NumericKind.holds, RatBounds.contains]
      · have ht := beq_iff_eq.mp h2; subst ht
        rw [valueSpace_real_iff]
        simp [NumericKind.holds, RatBounds.contains, hnot]
    · obtain ⟨ib, hib, hpair⟩ := Option.map_eq_some_iff.mp h
      cases hpair
      rw [valueSpace_integerSubtype_iff hib]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Rat.ofInt z, rfl, (intBoundsToRatBounds_iff ib z).mpr hz, rfl⟩
      · rintro ⟨q, hden, hcon, rfl⟩
        have hden' : q.den = 1 := hden
        have hq : q = Rat.ofInt q.num := by apply Rat.ext <;> simp [hden']
        rw [hq] at hcon ⊢
        exact ⟨q.num, (intBoundsToRatBounds_iff ib q.num).mp hcon, rfl⟩

private theorem ratFacetBounds_iff {t : IRI} {f : Facet} {fb : RatBounds}
    (hfb : ratFacetBounds f = some fb) (i : Interpretation datatypeMap) (q : Rat)
    (hvs : valueSpace t (.number q)) :
    facetHolds i t f (i.embedValue (.number q)) ↔ fb.contains q := by
  unfold ratFacetBounds at hfb
  cases ho : orderFacet f.name with
  | none => simp [ho] at hfb
  | some ord =>
    cases hb : decodeLiteral f.bound with
    | none => simp [ho, hb] at hfb
    | some v =>
      cases v <;> simp only [ho, hb] at hfb
      case number b =>
        rw [facetHolds_iff_check i t f (.number b) (.number q) hb,
            checkFacet_iff t f.name (.number b) (.number q)]
        simp only [facetSpace, hvs, true_and, ho, Option.some.injEq, exists_eq_left']
        cases ord <;> simp only [Option.some.injEq] at hfb <;> subst hfb <;>
          simp [OrderFacet.holds, RatBounds.contains, RatEndpoint.holdsLower, RatEndpoint.holdsUpper]
      all_goals cases ord <;> contradiction

private theorem foldRatFacetBounds_iff {t : IRI} {fs : List Facet} {acc res : RatBounds}
    (hfold : foldRatFacetBounds acc fs = some res) (i : Interpretation datatypeMap) (q : Rat)
    (hvs : valueSpace t (.number q)) :
    (acc.contains q ∧ ∀ f ∈ fs, facetHolds i t f (i.embedValue (.number q))) ↔ res.contains q := by
  induction fs generalizing acc with
  | nil => cases hfold; simp
  | cons f tail ih =>
    simp only [foldRatFacetBounds] at hfold
    obtain ⟨fb, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    rw [← ih htail, RatBounds.contains_intersect, List.forall_mem_cons,
      ratFacetBounds_iff hfb i q hvs]
    exact ⟨fun ⟨ha, hf, hr⟩ => ⟨⟨ha, hf⟩, hr⟩, fun ⟨⟨ha, hf⟩, hr⟩ => ⟨ha, hf, hr⟩⟩

theorem extractNumAtom_iff {a : DataRange} {kind : NumericKind} {bounds : RatBounds}
    (h : extractNumAtom a = some (kind, bounds)) (i : Interpretation datatypeMap)
    (v : Value) (hn : ∀ q, v ≠ .irrational q) :
    dataHolds i (i.embedValue v) a ↔ ∃ q : Rat, v = .number q ∧ kind.holds q ∧ bounds.contains q := by
  have embedded (t : IRI) (h : supportedDatatype t = true) :
      i.datatypes t (i.embedValue v) ↔ valueSpace t v := by
    rw [i.datatypeAgreement t h]
    exact ⟨fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
  cases a with
  | datatype t =>
    simp only [extractNumAtom] at h
    rw [dataHolds, embedded t (numericBase_supported h), valueSpace_numericBase_iff h v hn]
    exact exists_congr fun _ => ⟨fun ⟨hk, hb, hv⟩ => ⟨hv, hk, hb⟩,
      fun ⟨hv, hk, hb⟩ => ⟨hk, hb, hv⟩⟩
  | restriction t fs =>
    simp only [extractNumAtom] at h
    obtain ⟨⟨k, base⟩, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hfold, hpair⟩ := Option.bind_eq_some_iff.mp hrest
    cases hpair
    rw [dataHolds, embedded t (numericBase_supported ht)]
    constructor
    · rintro ⟨hv, hfs⟩
      obtain ⟨q, hk, hb, rfl⟩ := (valueSpace_numericBase_iff ht v hn).mp hv
      exact ⟨q, rfl, hk, (foldRatFacetBounds_iff hfold i q hv).mp ⟨hb, hfs⟩⟩
    · rintro ⟨q, rfl, hk, hcon⟩
      have hsub : ∀ (l : List Facet) (acc : RatBounds),
          foldRatFacetBounds acc l = some bounds → bounds.contains q → acc.contains q := by
        intro l
        induction l with
        | nil =>
          intro acc hf hr
          cases hf
          exact hr
        | cons f tail ih =>
          intro acc hf hr
          obtain ⟨fb, _, htail⟩ := Option.bind_eq_some_iff.mp hf
          exact ((RatBounds.contains_intersect _ _ _).mp (ih _ htail hr)).1
      have hv := (valueSpace_numericBase_iff ht (.number q) hn).mpr
        ⟨q, hk, hsub fs base hfold hcon, rfl⟩
      exact ⟨hv, ((foldRatFacetBounds_iff hfold i q hv).mpr hcon).2⟩
  | _ => cases h

/-! ### 4. Natural length intervals (`NatBounds`) for string / URI / binary length facets -/

structure NatBounds where
  lower : Nat := 0
  upper : Option Nat := none
  deriving DecidableEq, Repr

def NatBounds.contains (b : NatBounds) (n : Nat) : Prop :=
  b.lower ≤ n ∧ b.upper.elim True (n ≤ ·)

instance (b : NatBounds) (n : Nat) : Decidable (b.contains n) := by
  rcases b with ⟨lo, hi⟩
  cases hi <;> unfold NatBounds.contains <;> dsimp <;> infer_instance

def NatBounds.intersect (a b : NatBounds) : NatBounds :=
  { lower := max a.lower b.lower,
    upper := match a.upper, b.upper with
      | none, y => y
      | x, none => x
      | some x, some y => some (min x y) }

theorem NatBounds.contains_intersect (a b : NatBounds) (n : Nat) :
    (a.intersect b).contains n ↔ a.contains n ∧ b.contains n := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp [NatBounds.intersect, NatBounds.contains] <;> omega

def isNonEmptyNatBounds (b : NatBounds) : Bool :=
  match b.upper with
  | none => true
  | some hi => decide (b.lower ≤ hi)

private theorem isNonEmptyNatBounds_of_contains {b : NatBounds} {n : Nat}
    (h : b.contains n) : isNonEmptyNatBounds b = true := by
  rcases b with ⟨lo, hi⟩
  cases hi <;> simp [isNonEmptyNatBounds, NatBounds.contains] at h ⊢ <;> omega

def subtractNatBoundsOne (cur neg : NatBounds) : List NatBounds :=
  let left : List NatBounds :=
    if neg.lower = 0 then []
    else
      let cap := neg.lower - 1
      [{ lower := cur.lower,
         upper := match cur.upper with
           | none => some cap
           | some chi => some (min chi cap) }]
  let right : List NatBounds :=
    match neg.upper with
    | none => []
    | some nhi => [{ lower := max cur.lower (nhi + 1), upper := cur.upper }]
  (left ++ right).filter isNonEmptyNatBounds

theorem mem_subtractNatBoundsOne_iff (cur neg : NatBounds) (n : Nat) :
    (∃ b ∈ subtractNatBoundsOne cur neg, b.contains n) ↔ (cur.contains n ∧ ¬ neg.contains n) := by
  have hfilt : ∀ xs : List NatBounds,
      (∃ b ∈ xs.filter isNonEmptyNatBounds, b.contains n) ↔ (∃ b ∈ xs, b.contains n) := fun xs =>
    ⟨fun ⟨b, hb, hn⟩ => ⟨b, (List.mem_filter.mp hb).1, hn⟩,
     fun ⟨b, hb, hn⟩ => ⟨b, List.mem_filter.mpr ⟨hb, isNonEmptyNatBounds_of_contains hn⟩, hn⟩⟩
  unfold subtractNatBoundsOne
  rw [hfilt]
  rcases cur with ⟨clo, chi⟩
  rcases neg with ⟨nlo, nhi⟩
  by_cases hz : nlo = 0
  · subst hz
    cases chi <;> cases nhi <;> simp [NatBounds.contains] <;> omega
  · cases chi <;> cases nhi <;> simp [hz, NatBounds.contains] <;> omega

def foldSubtractNatBounds : List NatBounds → List NatBounds → List NatBounds
  | bs, [] => bs
  | bs, neg :: rest => foldSubtractNatBounds (bs.flatMap (subtractNatBoundsOne · neg)) rest

theorem mem_foldSubtractNatBounds_iff (bs negs : List NatBounds) (n : Nat) :
    (∃ b ∈ foldSubtractNatBounds bs negs, b.contains n) ↔
      ((∃ b ∈ bs, b.contains n) ∧ ∀ neg ∈ negs, ¬ neg.contains n) := by
  induction negs generalizing bs with
  | nil => simp [foldSubtractNatBounds]
  | cons neg rest ih =>
    simp only [foldSubtractNatBounds, ih, List.mem_flatMap, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨b, ⟨b₀, hb₀, hb⟩, hn⟩, hrest⟩
      have ⟨h1, h2⟩ := (mem_subtractNatBoundsOne_iff b₀ neg n).mp ⟨b, hb, hn⟩
      exact ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
    · rintro ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
      obtain ⟨b, hb, hn⟩ := (mem_subtractNatBoundsOne_iff b₀ neg n).mpr ⟨h1, h2⟩
      exact ⟨⟨b, ⟨b₀, hb₀, hb⟩, hn⟩, hrest⟩

def lenFacetBounds (f : Facet) : Option NatBounds :=
  match lengthFacet f.name, decodeLiteral f.bound with
  | some .length, some (.number q) =>
    if q.den = 1 ∧ 0 ≤ q.num then some ⟨q.num.toNat, some q.num.toNat⟩ else none
  | some .minLength, some (.number q) =>
    if q.den = 1 ∧ 0 ≤ q.num then some ⟨q.num.toNat, none⟩ else none
  | some .maxLength, some (.number q) =>
    if q.den = 1 ∧ 0 ≤ q.num then some ⟨0, some q.num.toNat⟩ else none
  | _, _ => none

def foldLenFacetBounds (acc : NatBounds) : List Facet → Option NatBounds
  | [] => some acc
  | f :: fs => do
    let fb ← lenFacetBounds f
    foldLenFacetBounds (acc.intersect fb) fs

private theorem lenFacetBounds_holdsNat_iff {f : Facet} {fb : NatBounds}
    (hfb : lenFacetBounds f = some fb) {n : Nat} :
    (∃ q : Rat, decodeLiteral f.bound = some (.number q) ∧ q.den = 1 ∧ 0 ≤ q.num ∧
      ∃ lf, lengthFacet f.name = some lf ∧ lf.holdsNat q.num.toNat n) ↔ fb.contains n := by
  unfold lenFacetBounds at hfb
  cases hl : lengthFacet f.name with
  | none => simp [hl] at hfb
  | some lf =>
    cases hb : decodeLiteral f.bound with
    | none => simp [hl, hb] at hfb
    | some v =>
      cases v <;> simp only [hl, hb] at hfb
      case number q =>
        cases lf <;> simp only at hfb <;> split at hfb <;> try contradiction
        all_goals
          rename_i hq
          cases hfb
          constructor
          · rintro ⟨q', hq', _, _, lf', hlf', hh⟩
            cases hq'; cases hlf'
            simp only [LengthFacet.holdsNat, NatBounds.contains, Option.elim_some, Option.elim_none] at hh ⊢
            exact ⟨by omega, by first | trivial | omega⟩
          · intro hcon
            refine ⟨q, rfl, hq.1, hq.2, _, rfl, ?_⟩
            simp only [LengthFacet.holdsNat, NatBounds.contains, Option.elim_some, Option.elim_none] at hcon ⊢
            omega
      all_goals cases lf <;> contradiction

/-! Length-bounded witness generators for `String` and `List UInt8` -/

private def charOfNatSafe (k : Nat) : Char :=
  Char.ofNat (if k < 0xD800 then k else 0)

private theorem charOfNatSafe_inj {k₁ k₂ : Nat} (h1 : k₁ < 0xD800) (h2 : k₂ < 0xD800)
    (heq : charOfNatSafe k₁ = charOfNatSafe k₂) : k₁ = k₂ := by
  simp only [charOfNatSafe, h1, h2, ↓reduceIte] at heq
  have hv := congrArg Char.toNat heq
  have hvalid1 : k₁.isValidChar := by simp [Nat.isValidChar]; omega
  have hvalid2 : k₂.isValidChar := by simp [Nat.isValidChar]; omega
  have hs : UInt32.size = 4294967296 := rfl
  have hl1 : k₁ < UInt32.size := by omega
  have hl2 : k₂ < UInt32.size := by omega
  have he1 : (Char.ofNat k₁).toNat = k₁ := by
    simp only [Char.ofNat, hvalid1, ↓reduceDIte, Char.toNat, Char.ofNatAux]
    rfl
  have he2 : (Char.ofNat k₂).toNat = k₂ := by
    simp only [Char.ofNat, hvalid2, ↓reduceDIte, Char.toNat, Char.ofNatAux]
    rfl
  rw [he1, he2] at hv
  exact hv

/-- Fixed-length `m ≥ 1` distinct strings (`k < 55296`), or `""` for `m = 0`. -/
def fixedLenStr (m k : Nat) : String :=
  match m with
  | 0 => ""
  | m' + 1 => String.ofList (charOfNatSafe k :: List.replicate m' 'a')

theorem fixedLenStr_length (m k : Nat) : (fixedLenStr m k).length = m := by
  cases m <;> simp [fixedLenStr, String.length]

theorem fixedLenStr_inj {m k₁ k₂ : Nat} (hm : 0 < m) (h1 : k₁ < 0xD800) (h2 : k₂ < 0xD800)
    (h : fixedLenStr m k₁ = fixedLenStr m k₂) : k₁ = k₂ := by
  cases m with
  | zero => omega
  | succ m' =>
    have hl := congrArg String.toList h
    simp only [fixedLenStr, String.toList_ofList, List.cons.injEq] at hl
    exact charOfNatSafe_inj h1 h2 hl.1

/-- Fixed-length byte lists: for `m = 0` singleton `[]`, for `m = 1` all 256 bytes,
for `m ≥ 2` up to 65536 distinct byte lists. -/
def fixedLenBytes (m k : Nat) : List UInt8 :=
  match m with
  | 0 => []
  | 1 => [UInt8.ofNat k]
  | m' + 2 => UInt8.ofNat (k / 256) :: UInt8.ofNat (k % 256) :: List.replicate m' 0

theorem fixedLenBytes_length (m k : Nat) : (fixedLenBytes m k).length = m := by
  match m with
  | 0 => rfl
  | 1 => rfl
  | m' + 2 => simp [fixedLenBytes]

theorem fixedLenBytes_inj1 {k₁ k₂ : Nat} (h1 : k₁ < 256) (h2 : k₂ < 256)
    (h : fixedLenBytes 1 k₁ = fixedLenBytes 1 k₂) : k₁ = k₂ := by
  simp only [fixedLenBytes, List.cons.injEq, and_true] at h
  have hv := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at hv
  omega

theorem fixedLenBytes_inj2 {m k₁ k₂ : Nat} (hm : 2 ≤ m) (h1 : k₁ < 65536) (h2 : k₂ < 65536)
    (h : fixedLenBytes m k₁ = fixedLenBytes m k₂) : k₁ = k₂ := by
  match m with
  | 0 | 1 => omega
  | m' + 2 =>
    simp only [fixedLenBytes, List.cons.injEq] at h
    have hv1 := congrArg UInt8.toNat h.1
    have hv2 := congrArg UInt8.toNat h.2.1
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at hv1 hv2
    omega

/-! ### 5. String subtype hierarchy and its witnesses -/

inductive StrTier where
  | language
  | ncname
  | name
  | nmtoken
  | token
  | normalizedString
  | string
  | plainLiteral
  deriving DecidableEq, Repr

def strTierOfIRI (t : IRI) : Option StrTier :=
  if t == xsd "language" then some .language
  else if t == xsd "NCName" then some .ncname
  else if t == xsd "Name" then some .name
  else if t == xsd "NMTOKEN" then some .nmtoken
  else if t == xsd "token" then some .token
  else if t == xsd "normalizedString" then some .normalizedString
  else if t == xsd "string" then some .string
  else if t == rdf "PlainLiteral" then some .plainLiteral
  else none

def StrTier.holds : StrTier → String → String → Bool
  | .language, s, l => l.isEmpty && isLanguageTag s
  | .ncname, s, l => l.isEmpty && isNCName s
  | .name, s, l => l.isEmpty && isName s
  | .nmtoken, s, l => l.isEmpty && isNMTOKEN s
  | .token, s, l => l.isEmpty && isToken s
  | .normalizedString, s, l => l.isEmpty && isNormalizedString s
  | .string, _, l => l.isEmpty
  | .plainLiteral, _, _ => true

theorem strTierOfIRI_supported {t : IRI} {tier : StrTier} (h : strTierOfIRI t = some tier) :
    supportedDatatype t = true := by
  unfold strTierOfIRI at h
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  split at h; · rename_i he; rw [beq_iff_eq.mp he]; decide
  cases h

theorem valueSpace_strTier_iff {t : IRI} {tier : StrTier} (h : strTierOfIRI t = some tier) (v : Value) :
    valueSpace t v ↔ ∃ s lang, tier.holds s lang = true ∧ v = .plainLiteral s lang := by
  rw [← checkValue_iff]
  unfold strTierOfIRI at h
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isLanguageTag s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isNCName s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isName s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isNMTOKEN s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isToken s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty && isNormalizedString s = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (l.isEmpty = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  split at h
  · rename_i he; have ht := beq_iff_eq.mp he; subst ht; cases h
    cases v with
    | plainLiteral s l =>
      change (decide (true = true)) = true ↔ _
      simp [StrTier.holds]
    | _ => simp [StrTier.holds]; rfl
  cases h

private theorem hasDoubleSpace_of_no_space : ∀ cs : List Char, (∀ c ∈ cs, c ≠ ' ') →
    isToken.hasDoubleSpace cs = false
  | [], _ => rfl
  | [a], hns => by
    have ha : a ≠ ' ' := hns a (List.mem_cons_self ..)
    unfold isToken.hasDoubleSpace
    split <;> simp_all [isToken.hasDoubleSpace]
  | a :: b :: rest, hns => by
    have ha : a ≠ ' ' := hns a (List.mem_cons_self ..)
    have hrest := hasDoubleSpace_of_no_space (b :: rest) fun c hc => hns c (List.mem_cons_of_mem _ hc)
    unfold isToken.hasDoubleSpace
    split <;> simp_all

private theorem getLast?_getD_mem {α : Type} (c : α) (rest : List α) :
    rest.getLast?.getD c ∈ c :: rest := by
  cases h : rest.getLast? with
  | none => simp
  | some z => exact List.mem_cons_of_mem _ (List.mem_of_getLast? h)

private theorem isToken_of_no_ws {s : String} (hne : s.toList ≠ [])
    (hchar : ∀ c ∈ s.toList, c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\t' ∧ c ≠ ' ') :
    isToken s = true := by
  have hnorm : isNormalizedString s = true := by
    simp only [isNormalizedString, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    intro c hc
    have ⟨h1, h2, h3, _⟩ := hchar c hc
    exact ⟨⟨h1, h2⟩, h3⟩
  simp only [isToken, hnorm, Bool.true_and]
  cases hs : s.toList with
  | nil => exact (hne hs).elim
  | cons c rest =>
    have hc : c ≠ ' ' := (hchar c (hs ▸ List.mem_cons_self ..)).2.2.2
    have hlast : rest.getLast?.getD c ≠ ' ' := (hchar _ (hs ▸ getLast?_getD_mem c rest)).2.2.2
    have hds : isToken.hasDoubleSpace (c :: rest) = false :=
      hasDoubleSpace_of_no_space (c :: rest) fun x hx => (hchar x (hs ▸ hx)).2.2.2
    simp [hc, hlast, hds]

theorem isToken_of_isNMTOKEN {s : String} (h : isNMTOKEN s = true) : isToken s = true := by
  simp only [isNMTOKEN, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hall := List.all_eq_true.mp h.2
  have hne : s.toList ≠ [] := by
    intro hnil
    have h0 : s = "" := by
      have := congrArg String.ofList hnil
      simpa using this
    subst h0; cases h.1
  exact isToken_of_no_ws hne fun c hc => by
    have hnm := hall c hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro rfl; cases hnm)

theorem isToken_of_isName {s : String} (h : isName s = true) : isToken s = true := by
  unfold isName at h
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c rest =>
    rw [hs] at h
    obtain ⟨hc, hr⟩ := Bool.and_eq_true_iff.mp h
    have hall := List.all_eq_true.mp hr
    exact isToken_of_no_ws (by rw [hs]; exact List.cons_ne_nil c rest) fun x hx => by
      rw [hs] at hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro rfl; cases hc)
      · have hx' := hall x hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro rfl; cases hx')

theorem isName_of_isNCName {s : String} (h : isNCName s = true) : isName s = true := by
  simp only [isNCName, Bool.and_eq_true] at h; exact h.1

theorem isNormalizedString_of_isToken {s : String} (h : isToken s = true) :
    isNormalizedString s = true := by
  simp only [isToken, Bool.and_eq_true] at h; exact h.1

/-- Witness string for exact string stratum `r ∈ 1..6` of length `k + 1`:
- `1`: `NCName` (`"_a...a"`)
- `2`: `Name \ NCName` (`":a...a"`)
- `3`: `NMTOKEN \ Name` (`"0a...a"`)
- `4`: `token \ NMTOKEN` (`"!a...a"`)
- `5`: `normalizedString \ token` (`" a...a"`)
- `6`: `string \ normalizedString` (`"\ta...a"`) -/
def stratumStr (c : Char) (k : Nat) : String :=
  String.ofList (c :: List.replicate k 'a')

theorem stratumStr_length (c : Char) (k : Nat) : (stratumStr c k).length = k + 1 := by
  simp [stratumStr, String.length]

theorem stratumStr_inj (c : Char) {k₁ k₂ : Nat} (h : stratumStr c k₁ = stratumStr c k₂) :
    k₁ = k₂ := by
  have hl := congrArg String.length h
  rw [stratumStr_length, stratumStr_length] at hl
  omega

private theorem stratumStr_isNormalizedString (c : Char) (k : Nat)
    (h1 : c ≠ '\r') (h2 : c ≠ '\n') (h3 : c ≠ '\t') :
    isNormalizedString (stratumStr c k) = true := by
  simp only [isNormalizedString, stratumStr, String.toList_ofList, List.all_cons, List.all_replicate,
    Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  cases k with
  | zero => rfl
  | succ _ => simp

private theorem stratumStr_isToken (c : Char) (k : Nat)
    (h1 : c ≠ '\r') (h2 : c ≠ '\n') (h3 : c ≠ '\t') (h4 : c ≠ ' ') :
    isToken (stratumStr c k) = true :=
  isToken_of_no_ws (by simp [stratumStr]) fun x hx => by
    simp only [stratumStr, String.toList_ofList, List.mem_cons] at hx
    rcases hx with rfl | hrep
    · exact ⟨h1, h2, h3, h4⟩
    · rw [List.eq_of_mem_replicate hrep]; decide

private theorem stratumStr_isNMTOKEN_true (c : Char) (k : Nat)
    (hc : isNMTOKEN (String.ofList [c]) = true) :
    isNMTOKEN (stratumStr c k) = true := by
  simp only [isNMTOKEN, String.toList_ofList, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hc
  simp only [isNMTOKEN, stratumStr, String.toList_ofList, List.all_cons,
    List.all_replicate, Bool.and_eq_true, Bool.not_eq_true']
  have hne : (String.ofList (c :: List.replicate k 'a')).isEmpty = false := by
    cases h : (String.ofList (c :: List.replicate k 'a')).isEmpty
    · rfl
    · have := congrArg String.toList (String.isEmpty_iff.mp h)
      simp at this
  refine ⟨hne, hc.2, ?_⟩
  cases k with
  | zero => rfl
  | succ _ => simp; decide

private theorem stratumStr_isName_true (c : Char) (k : Nat)
    (hc : isName (String.ofList [c]) = true) :
    isName (stratumStr c k) = true := by
  simp only [isName, String.toList_ofList, List.all_nil, Bool.and_true] at hc
  simp only [isName, stratumStr, String.toList_ofList, List.all_replicate, Bool.and_eq_true]
  refine ⟨hc, ?_⟩
  cases k with
  | zero => rfl
  | succ _ => simp; decide

private theorem stratumStr_isNCName_true (c : Char) (k : Nat)
    (hc : isNCName (String.ofList [c]) = true) :
    isNCName (stratumStr c k) = true := by
  have hn : isName (String.ofList [c]) = true := isName_of_isNCName hc
  have hnc : c ≠ ':' := by intro rfl; cases hc
  have hnotmem : ':' ∉ (c :: List.replicate k 'a') := by
    intro hm
    rcases List.mem_cons.mp hm with heq | hrep
    · exact hnc heq.symm
    · have := List.eq_of_mem_replicate hrep; cases this
  have hcont : (c :: List.replicate k 'a').contains ':' = false := by
    cases h : (c :: List.replicate k 'a').contains ':'
    · rfl
    · exact (hnotmem (List.contains_iff_mem.mp h)).elim
  rw [isNCName, stratumStr_isName_true c k hn, Bool.true_and, stratumStr, String.toList_ofList, hcont]
  rfl

private theorem stratumStr_flags_underscore (k : Nat) :
    isNormalizedString (stratumStr '_' k) = true ∧
    isToken (stratumStr '_' k) = true ∧
    isNMTOKEN (stratumStr '_' k) = true ∧
    isName (stratumStr '_' k) = true ∧
    isNCName (stratumStr '_' k) = true :=
  ⟨stratumStr_isNormalizedString '_' k (by decide) (by decide) (by decide),
   stratumStr_isToken '_' k (by decide) (by decide) (by decide) (by decide),
   stratumStr_isNMTOKEN_true '_' k (by decide),
   stratumStr_isName_true '_' k (by decide),
   stratumStr_isNCName_true '_' k (by decide)⟩

private theorem stratumStr_flags_colon (k : Nat) :
    isNormalizedString (stratumStr ':' k) = true ∧
    isToken (stratumStr ':' k) = true ∧
    isNMTOKEN (stratumStr ':' k) = true ∧
    isName (stratumStr ':' k) = true ∧
    isNCName (stratumStr ':' k) = false :=
  ⟨stratumStr_isNormalizedString ':' k (by decide) (by decide) (by decide),
   stratumStr_isToken ':' k (by decide) (by decide) (by decide) (by decide),
   stratumStr_isNMTOKEN_true ':' k (by decide),
   stratumStr_isName_true ':' k (by decide),
   by simp [isNCName, stratumStr]⟩

private theorem stratumStr_flags_zero (k : Nat) :
    isNormalizedString (stratumStr '0' k) = true ∧
    isToken (stratumStr '0' k) = true ∧
    isNMTOKEN (stratumStr '0' k) = true ∧
    isName (stratumStr '0' k) = false ∧
    isNCName (stratumStr '0' k) = false := by
  have hn : isName (stratumStr '0' k) = false := by
    simp only [isName, stratumStr, String.toList_ofList, Bool.and_eq_false_iff]
    exact .inl (by decide)
  exact ⟨stratumStr_isNormalizedString '0' k (by decide) (by decide) (by decide),
    stratumStr_isToken '0' k (by decide) (by decide) (by decide) (by decide),
    stratumStr_isNMTOKEN_true '0' k (by decide),
    hn, by simp [isNCName, hn]⟩

private theorem stratumStr_flags_bang (k : Nat) :
    isNormalizedString (stratumStr '!' k) = true ∧
    isToken (stratumStr '!' k) = true ∧
    isNMTOKEN (stratumStr '!' k) = false ∧
    isName (stratumStr '!' k) = false ∧
    isNCName (stratumStr '!' k) = false := by
  have hnm : isNMTOKEN (stratumStr '!' k) = false := by
    simp only [isNMTOKEN, stratumStr, String.toList_ofList, List.all_cons, Bool.and_eq_false_iff]
    exact .inr (.inl (by decide))
  have hn : isName (stratumStr '!' k) = false := by
    simp only [isName, stratumStr, String.toList_ofList, Bool.and_eq_false_iff]
    exact .inl (by decide)
  exact ⟨stratumStr_isNormalizedString '!' k (by decide) (by decide) (by decide),
    stratumStr_isToken '!' k (by decide) (by decide) (by decide) (by decide),
    hnm, hn, by simp [isNCName, hn]⟩

private theorem stratumStr_flags_space (k : Nat) :
    isNormalizedString (stratumStr ' ' k) = true ∧
    isToken (stratumStr ' ' k) = false ∧
    isNMTOKEN (stratumStr ' ' k) = false ∧
    isName (stratumStr ' ' k) = false ∧
    isNCName (stratumStr ' ' k) = false := by
  have ht : isToken (stratumStr ' ' k) = false := by simp [isToken, stratumStr]
  have hnm : isNMTOKEN (stratumStr ' ' k) = false := by
    cases h : isNMTOKEN (stratumStr ' ' k)
    · rfl
    · have := isToken_of_isNMTOKEN h; rw [ht] at this; cases this
  have hn : isName (stratumStr ' ' k) = false := by
    cases h : isName (stratumStr ' ' k)
    · rfl
    · have := isToken_of_isName h; rw [ht] at this; cases this
  exact ⟨stratumStr_isNormalizedString ' ' k (by decide) (by decide) (by decide),
    ht, hnm, hn, by simp [isNCName, hn]⟩

private theorem stratumStr_flags_tab (k : Nat) :
    isNormalizedString (stratumStr '\t' k) = false ∧
    isToken (stratumStr '\t' k) = false ∧
    isNMTOKEN (stratumStr '\t' k) = false ∧
    isName (stratumStr '\t' k) = false ∧
    isNCName (stratumStr '\t' k) = false := by
  have hns : isNormalizedString (stratumStr '\t' k) = false := by simp [isNormalizedString, stratumStr]
  have ht : isToken (stratumStr '\t' k) = false := by simp [isToken, hns]
  have hnm : isNMTOKEN (stratumStr '\t' k) = false := by
    cases h : isNMTOKEN (stratumStr '\t' k)
    · rfl
    · have := isToken_of_isNMTOKEN h; rw [ht] at this; cases this
  have hn : isName (stratumStr '\t' k) = false := by
    cases h : isName (stratumStr '\t' k)
    · rfl
    · have := isToken_of_isName h; rw [ht] at this; cases this
  exact ⟨hns, ht, hnm, hn, by simp [isNCName, hn]⟩

private def stratumWitness (c : Char) (k : Nat) : String :=
  if c = 'a' then languageWitness k else stratumStr c k

private theorem stratumWitness_inj (c : Char) {j k : Nat}
    (h : stratumWitness c j = stratumWitness c k) : j = k := by
  unfold stratumWitness at h
  split at h
  · have hl := congrArg String.length h
    simp only [languageWitness_length] at hl
    omega
  · exact stratumStr_inj c h

/-! ### 6. Unified wider exact `DataRange` fragment, evaluator, and bounded sampler -/

private def isLenFacet (f : Facet) : Bool :=
  (lenFacetBounds f).isSome

private def isOrderFacet (f : Facet) : Bool :=
  (ratFacetBounds f).isSome

/-- Exact atomic data ranges supported by the wider algebra. -/
def legacy_isWiderExactAtom : DataRange → Bool
  | .datatype t =>
    t == literalDatatype ||
    t == xsd "boolean" ||
    (numericBase t).isSome ||
    (strTierOfIRI t).isSome ||
    t == xsd "anyURI" ||
    t == rdf "XMLLiteral" ||
    t == xsd "hexBinary" ||
    t == xsd "base64Binary" ||
    t == xsd "dateTime" ||
    t == xsd "dateTimeStamp"
  | .restriction t fs =>
    ((numericBase t).isSome && fs.all isOrderFacet) ||
    ((t == xsd "string" || t == rdf "PlainLiteral" || t == xsd "anyURI" ||
      t == xsd "hexBinary" || t == xsd "base64Binary") &&
      fs.all isLenFacet)
  | .oneOf ls =>
    ls.all fun l => (decodeLiteral l).isSome
  | _ => false

private def atomUsesStrSubtype : DataRange → Bool
  | .datatype t =>
    t == xsd "language" || t == xsd "NCName" || t == xsd "Name" || t == xsd "NMTOKEN" ||
    t == xsd "token" || t == xsd "normalizedString"
  | _ => false

/-- Each input atom must be in the wider exact datatype algebra. -/
def legacy_widerAtomsAdmissible (atoms : List DataRange) : Bool :=
  atoms.all legacy_isWiderExactAtom

/-- Total atomic evaluator for all wider exact atoms. -/
def evalWiderAtom : DataRange → Value → Bool
  | .datatype t, v =>
    if t == literalDatatype then true else checkValue t v
  | .restriction t fs, v =>
    checkValue t v &&
    fs.all fun f =>
      match decodeLiteral f.bound with
      | some b => checkFacet t f.name b v
      | none => false
  | .oneOf ls, v =>
    match decodeLiteralsList ls with
    | some vs => vs.contains v
    | none => false
  | _, _ => false

def evalWiderDataRange : DataRange → Value → Bool
  | .complement r, v => !evalWiderDataRange r v
  | .intersection a b, v => evalWiderDataRange a v && evalWiderDataRange b v
  | .union a b, v => evalWiderDataRange a v || evalWiderDataRange b v
  | a, v => evalWiderAtom a v

def evalWiderPartition (pos neg : List DataRange) (v : Value) : Bool :=
  pos.all (evalWiderAtom · v) && neg.all (fun a => !evalWiderAtom a v)

theorem legacy_widerDatatype_supported {t : IRI} (h : legacy_isWiderExactAtom (.datatype t) = true)
    (hne : t ≠ literalDatatype) : supportedDatatype t = true := by
  simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · exact (hne rfl).elim
  · decide
  · obtain ⟨⟨k, b⟩, hb⟩ := Option.isSome_iff_exists.mp hnum; exact numericBase_supported hb
  · obtain ⟨tier, ht⟩ := Option.isSome_iff_exists.mp hstr; exact strTierOfIRI_supported ht
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem legacy_widerRestriction_supported {t : IRI} {fs : List Facet}
    (h : legacy_isWiderExactAtom (.restriction t fs) = true) :
    supportedDatatype t = true ∧ ∀ f ∈ fs, (decodeLiteral f.bound).isSome = true := by
  simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  rcases h with ⟨hnum, hfs⟩ | ⟨ht, hfs⟩
  · obtain ⟨⟨k, b⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
    refine ⟨numericBase_supported hb, fun f hf => ?_⟩
    have hof := hfs f hf
    unfold isOrderFacet ratFacetBounds at hof
    cases orderFacet f.name <;> cases hdec : decodeLiteral f.bound <;> simp [hdec] at hof ⊢
  · refine ⟨?_, fun f hf => ?_⟩
    · rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
    · have hlf := hfs f hf
      unfold isLenFacet lenFacetBounds at hlf
      cases lengthFacet f.name <;> cases hdec : decodeLiteral f.bound <;> simp [hdec] at hlf ⊢

theorem legacy_evalWiderAtom_iff {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalWiderAtom a v = true ↔ dataHolds i (i.embedValue v) a := by
  cases a with
  | datatype t =>
    simp only [evalWiderAtom]
    by_cases hlit : t = literalDatatype
    · subst hlit; simp [dataHolds, i.literalDatatypeExt]
    · have hsup : datatypeMap.builtin t := legacy_widerDatatype_supported ha hlit
      rw [beq_false_of_ne hlit]
      change checkValue t v = true ↔ i.datatypes t (i.embedValue v)
      rw [checkValue_iff, i.datatypeAgreement t hsup (i.embedValue v)]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
  | restriction t fs =>
    have ⟨hsup, hbounds⟩ := legacy_widerRestriction_supported ha
    simp only [evalWiderAtom, Bool.and_eq_true, List.all_eq_true, dataHolds]
    refine and_congr ?_ ?_
    · rw [checkValue_iff, i.datatypeAgreement t hsup (i.embedValue v)]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
    · refine forall_congr' fun f => imp_congr_right fun hf => ?_
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hbounds f hf)
      simp only [hb]
      exact (facetHolds_iff_check i t f b v hb).symm
  | oneOf ls =>
    simp only [legacy_isWiderExactAtom] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    rw [decodeLiteralsList_iff hvs i (i.embedValue v)]
    simp only [evalWiderAtom, hvs, List.contains_iff_mem]
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
  | complement _ | intersection _ _ | union _ _ => cases ha

theorem evalWiderDataRange_of_atoms {dm : DatatypeMap} (i : Interpretation dm)
    (y : i.Data) (v : Value) (d : DataRange)
    (h : ∀ a ∈ atomsOfDataRange d, evalWiderAtom a v = true ↔ dataHolds i y a) :
    evalWiderDataRange d v = true ↔ dataHolds i y d := by
  induction d with
  | complement r ih =>
    simpa only [evalWiderDataRange, Bool.not_eq_true', Bool.eq_false_iff, dataHolds] using
      not_congr (ih h)
  | intersection a b iha ihb =>
    exact (Bool.and_eq_true_iff).trans (and_congr
      (iha fun r hr => h r (List.mem_eraseDups.mpr (List.mem_append_left _ hr)))
      (ihb fun r hr => h r (List.mem_eraseDups.mpr (List.mem_append_right _ hr))))
  | union a b iha ihb =>
    exact (Bool.or_eq_true_iff).trans (or_congr
      (iha fun r hr => h r (List.mem_eraseDups.mpr (List.mem_append_left _ hr)))
      (ihb fun r hr => h r (List.mem_eraseDups.mpr (List.mem_append_right _ hr))))
  | datatype _ | restriction _ _ | oneOf _ =>
    exact h _ (List.mem_singleton_self _)

/-! ### 7. Candidate generation for the original wider strata -/

private def negRatBoundsForStratum (stratum : NumericKind) : DataRange → List RatBounds
  | .oneOf ls =>
    ((decodeLiteralsList ls).getD []).filterMap fun
      | .number q => some { lower := some ⟨q, true⟩, upper := some ⟨q, true⟩ }
      | _ => none
  | a =>
    match extractNumAtom a with
    | some (k, b) =>
      match stratum, k with
      | .int, _ => [b]
      | .dec, .dec => [b]
      | .dec, .rat => [b]
      | .rat, .rat => [b]
      | _, _ => []
    | none => []

private def vennNumRatBounds (stratum : NumericKind) (pos neg : List DataRange) : List RatBounds :=
  let posBounds := pos.filterMap fun a => (extractNumAtom a).map Prod.snd
  let base : RatBounds := posBounds.foldr RatBounds.intersect {}
  let negBounds := neg.flatMap (negRatBoundsForStratum stratum)
  foldSubtractRatBounds [base] negBounds

def vennIrrationalBounds (pos neg : List DataRange) : List RatBounds :=
  let lower := (pos.filterMap extractIrrationalBounds).foldr RatBounds.intersect {}
  foldSubtractRatBounds [lower] (neg.filterMap extractIrrationalBounds)

private def vennNumIntBounds (pos neg : List DataRange) : List IntegerBounds :=
  let posBounds := pos.filterMap fun a => (extractNumAtom a).map fun (_, b) => b.toIntBounds
  let base : IntegerBounds := posBounds.foldr IntegerBounds.intersect {}
  let negBounds := neg.flatMap fun
    | .oneOf ls =>
      ((decodeLiteralsList ls).getD []).filterMap fun
        | .number q => if q.den == 1 then some { lower := some q.num, upper := some q.num } else none
        | _ => none
    | a =>
      match extractNumAtom a with
      | some (_, b) => [b.toIntBounds]
      | none => []
  foldSubtractBounds [base] negBounds

private def extractLenOf (sort : IRI) : DataRange → Option NatBounds
  | .datatype t => if t == sort then some {} else none
  | .restriction t fs => if t == sort then foldLenFacetBounds {} fs else none
  | _ => none

private def extractStrOrPlainLen : DataRange → Option NatBounds
  | .datatype t =>
    if t == xsd "string" || t == rdf "PlainLiteral" then some {} else none
  | .restriction t fs =>
    if t == xsd "string" || t == rdf "PlainLiteral" then foldLenFacetBounds {} fs else none
  | _ => none

private def vennLenBounds (ext : DataRange → Option NatBounds) (pos neg : List DataRange) :
    List NatBounds :=
  let posB := pos.filterMap ext
  let base : NatBounds := posB.foldr NatBounds.intersect {}
  let negB := neg.filterMap ext
  foldSubtractNatBounds [base] negB

private def sampleWordBounds {α} (alphabet : BoundedWords.Alphabet α) (filler : α)
    (count : Nat) (bs : List NatBounds) : List (List α) :=
  bs.flatMap fun b =>
    match b.upper with
    | none => (List.range count).map fun k => List.replicate (b.lower + k) filler
    | some hi =>
      if hi < b.lower then [] else alphabet.sample count b.lower hi

private def sampleLenStringsForBounds (count : Nat) (bs : List NatBounds) : List String :=
  (sampleWordBounds BoundedWords.scalars 'a' count bs).map String.ofList

private def sampleLenBytesForBounds (count : Nat) (bs : List NatBounds) : List (List UInt8) :=
  sampleWordBounds BoundedWords.bytes 0 count bs

private def matchesSubtypes (pos neg : List DataRange) (s : String) : Bool :=
  ((pos.filter atomUsesStrSubtype).all fun a => evalWiderAtom a (Value.string s)) &&
    ((neg.filter atomUsesStrSubtype).all fun a => !evalWiderAtom a (Value.string s))

private def sampleSubtypeLengths (count : Nat) (bounds : List NatBounds)
    (accept : String → Bool) : List String :=
  bounds.flatMap fun b =>
    match b.upper with
    | none => stringCharacterProfiles.flatMap fun c =>
        (List.range count).map fun k => stratumWitness c (b.lower + k)
    | some hi => (List.range' b.lower (hi + 1 - b.lower)).flatMap (fun n => StringLengthCells.sample count n accept)

private def quickSubtypeCandidates (K : Nat) (pos neg : List DataRange) (bounds : List NatBounds) :
    List Value :=
  let accept := matchesSubtypes pos neg
  let count := K + (allOneOfValues neg).length
  let samples := bounds.flatMap fun b =>
    ([b.lower, max 2 b.lower, max 3 b.lower].filter fun n =>
      b.upper.isNone || n ≤ b.upper.getD n).flatMap fun n =>
      StringLengthCells.sampleShortlist count n accept
  ((samples.map Value.string).filter (evalWiderPartition pos neg)).eraseDups

def legacy_widerCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  let M := K + (allOneOfValues neg).length
  let bools := [Value.boolean false, Value.boolean true]
  let oneOfs := allOneOfValues pos ++ allOneOfValues neg
  let ints := (sampleIntSet K (vennNumIntBounds pos neg)).map Value.integer
  let decs := (sampleProperDecSet K (vennNumRatBounds .dec pos neg)).map Value.number
  let rats := (sampleNonDecRatSet K (vennNumRatBounds .rat pos neg)).map Value.number
  let strLenBs := vennLenBounds extractStrOrPlainLen pos neg
  let strLens := (sampleLenStringsForBounds M strLenBs).map Value.string
  let strTiers :=
    let accept := matchesSubtypes pos neg
    if (pos ++ neg).any atomUsesStrSubtype &&
        stringCharacterProfiles.any (fun c => accept (stratumWitness c 0)) then
      let quick := quickSubtypeCandidates K pos neg strLenBs
      if K ≤ quick.length then quick
      else (sampleSubtypeLengths M strLenBs accept).map Value.string
    else []
  let plainLenBs := vennLenBounds (extractLenOf (rdf "PlainLiteral")) pos neg
  let plainLangs := plainLenBs.flatMap fun b =>
    (List.range M).map fun k =>
      Value.plainLiteral (String.ofList (List.replicate b.lower 'a'))
        (String.ofList (List.replicate (k + 1) 'e'))
  let uriLenBs := vennLenBounds (extractLenOf (xsd "anyURI")) pos neg
  let uris := (sampleLenStringsForBounds M uriLenBs).map Value.anyURI
  let xmls := (List.range M).map fun k => Value.xmlLiteral (String.ofList (List.replicate k 'a'))
  let hexLenBs := vennLenBounds (extractLenOf (xsd "hexBinary")) pos neg
  let hexs := (sampleLenBytesForBounds M hexLenBs).map Value.hexBinary
  let b64LenBs := vennLenBounds (extractLenOf (xsd "base64Binary")) pos neg
  let b64s := (sampleLenBytesForBounds M b64LenBs).map Value.base64Binary
  let dtsZ := (List.range M).map fun k => Value.dateTime ⟨Rat.ofInt (Int.ofNat k), some 0⟩
  let dtsL := (List.range M).map fun k => Value.dateTime ⟨Rat.ofInt (Int.ofNat k), none⟩
  let irrationals := (sampleProperDecSet K (vennIrrationalBounds pos neg)).map Value.irrational
  irrationals ++ (bools ++ oneOfs ++ ints ++ decs ++ rats ++ strLens ++ strTiers ++ plainLangs ++
    uris ++ xmls ++ hexs ++ b64s ++ dtsZ ++ dtsL)

/-! ### 8. Coverage of the original candidate families -/

private theorem w_mem_allOneOfValues_of_mem {xs : List DataRange} {a : DataRange} {v : Value}
    (ha : a ∈ xs) (hv : v ∈ oneOfValuesOfAtom a) : v ∈ allOneOfValues xs :=
  List.mem_flatMap.mpr ⟨a, ha, hv⟩

private theorem w_nodup_map_range {α : Type} (n : Nat) (f : Nat → α)
    (hinj : ∀ {k₁ k₂}, k₁ < n → k₂ < n → f k₁ = f k₂ → k₁ = k₂) :
    ((List.range n).map f).Nodup := by
  have aux : ∀ (l : List Nat), l.Nodup → (∀ k ∈ l, k < n) → (l.map f).Nodup := by
    intro l hnd hlt
    induction l with
    | nil => exact List.nodup_nil
    | cons a as ih =>
      obtain ⟨hna, hnda⟩ := List.nodup_cons.mp hnd
      refine List.nodup_cons.mpr ⟨?_, ih hnda fun k hk => hlt k (List.mem_cons_of_mem _ hk)⟩
      intro hm
      obtain ⟨b, hb, hfab⟩ := List.mem_map.mp hm
      have heq := hinj (hlt b (List.mem_cons_of_mem _ hb)) (hlt a (List.mem_cons_self ..)) hfab
      exact hna (heq ▸ hb)
  exact aux (List.range n) List.nodup_range fun k hk => List.mem_range.mp hk

theorem w_nodup_map_inj {α β : Type} {f : α → β} (hinj : ∀ {x y}, f x = f y → x = y)
    {l : List α} (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    obtain ⟨hna, hnda⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih hnda⟩
    intro hm
    obtain ⟨b, hb, hfab⟩ := List.mem_map.mp hm
    exact hna (hinj hfab ▸ hb)

theorem w_filter_length_le_of_sub_eraseDups {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) (p : α → Bool) (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    (xs.filter p).length ≤ (ys.eraseDups.filter p).length := by
  classical
  exact StringLengthCells.length_le_of_nodup_subset (List.filter_sublist.nodup hnd) fun x hx => by
    obtain ⟨hxm, hxp⟩ := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (hsub x hxm), hxp⟩

private theorem w_filter_pred_length_ge_of_avoid {α : Type} [DecidableEq α]
    (xs bad : List α) (p : α → Bool) (hnd : xs.Nodup)
    (hp : ∀ x ∈ xs, x ∉ bad → p x = true) :
    xs.length ≤ (xs.filter p).length + bad.length := by
  have hbad : (xs.filter fun x => !p x).length ≤ bad.length :=
    StringLengthCells.length_le_of_nodup_subset (List.filter_sublist.nodup hnd) fun x hx => by
      obtain ⟨hxm, hnp⟩ := List.mem_filter.mp hx
      by_cases hb : x ∈ bad
      · exact hb
      · rw [hp x hxm hb] at hnp; cases hnp
  have hsum : ∀ l : List α, (l.filter p).length + (l.filter fun x => !p x).length = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
      cases hpa : p a <;> simp [hpa] <;> omega
  have := hsum xs
  omega

private theorem w_bounded_family_ge_K {pos neg : List DataRange} (K : Nat)
    (mkVal : Nat → Value)
    (hinj : ∀ {k₁ k₂}, k₁ < K + (allOneOfValues neg).length →
      k₂ < K + (allOneOfValues neg).length → mkVal k₁ = mkVal k₂ → k₁ = k₂)
    (hsub : ∀ x ∈ (List.range (K + (allOneOfValues neg).length)).map mkVal,
      x ∈ legacy_widerCandidates K pos neg)
    (heval : ∀ k < K + (allOneOfValues neg).length,
      mkVal k ∉ allOneOfValues neg → evalWiderPartition pos neg (mkVal k) = true) :
    K ≤ ((legacy_widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).length := by
  let M := K + (allOneOfValues neg).length
  let xs := (List.range M).map mkVal
  have hnd : xs.Nodup := w_nodup_map_range M mkVal hinj
  have h1 := w_filter_pred_length_ge_of_avoid xs (allOneOfValues neg) (evalWiderPartition pos neg)
    hnd fun x hx hnb => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact heval k (List.mem_range.mp hk) hnb
  have h2 := w_filter_length_le_of_sub_eraseDups xs (legacy_widerCandidates K pos neg)
    (evalWiderPartition pos neg) hnd hsub
  have hlen : xs.length = M := by simp [xs]
  omega

theorem evalWiderAtom_oneOf_mem {ls : List Literal} {v : Value}
    (h : evalWiderAtom (.oneOf ls) v = true) : v ∈ oneOfValuesOfAtom (.oneOf ls) := by
  simp only [evalWiderAtom, oneOfValuesOfAtom] at h ⊢
  cases hd : decodeLiteralsList ls with
  | none => simp [hd] at h
  | some vs =>
    simp only [hd, List.contains_iff_mem] at h
    simpa [hd] using h

private theorem evalWiderAtom_oneOf_not_mem {ls : List Literal} {v : Value}
    (h : v ∉ oneOfValuesOfAtom (.oneOf ls)) : evalWiderAtom (.oneOf ls) v = false := by
  cases he : evalWiderAtom (.oneOf ls) v
  · rfl
  · exact (h (evalWiderAtom_oneOf_mem he)).elim

private theorem allOneOfValues_append (a b : List DataRange) :
    allOneOfValues (a ++ b) = allOneOfValues a ++ allOneOfValues b := by
  simp [allOneOfValues, List.flatMap_append]

private theorem checkValue_numericBase_false {t : IRI} {k : NumericKind} {b : RatBounds}
    (hb : numericBase t = some (k, b)) {v : Value} (h : ∀ q, v ≠ .number q)
    (hnot : ∀ q, v ≠ .irrational q := by intro q he; cases he) :
    checkValue t v = false := by
  cases hc : checkValue t v
  · rfl
  · obtain ⟨q, _, _, hq⟩ := (valueSpace_numericBase_iff hb v hnot).mp ((checkValue_iff _ _).mp hc)
    exact (h q hq).elim

private theorem checkValue_strTier_false {t : IRI} {tier : StrTier}
    (ht : strTierOfIRI t = some tier) {v : Value} (h : ∀ s l, v ≠ .plainLiteral s l) :
    checkValue t v = false := by
  cases hc : checkValue t v
  · rfl
  · obtain ⟨s, l, _, hq⟩ := (valueSpace_strTier_iff ht v).mp ((checkValue_iff _ _).mp hc)
    exact (h s l hq).elim

private theorem evalWiderAtom_extractNumAtom_iff {a : DataRange} {k : NumericKind} {b : RatBounds}
    (ha : legacy_isWiderExactAtom a = true) (hex : extractNumAtom a = some (k, b))
    (i : Interpretation datatypeMap) (v : Value)
    (hnot : ∀ q, v ≠ .irrational q := by intro q h; cases h) :
    evalWiderAtom a v = true ↔ ∃ q, v = .number q ∧ k.holds q ∧ b.contains q := by
  rw [legacy_evalWiderAtom_iff ha i v]
  exact extractNumAtom_iff hex i v hnot

private theorem evalWiderAtom_nonNum_number_false {a : DataRange}
    (ha : legacy_isWiderExactAtom a = true) (hnoLit : a ≠ .datatype literalDatatype)
    (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (hnoNum : extractNumAtom a = none)
    (q : Rat) : evalWiderAtom a (.number q) = false := by
  cases a with
  | datatype t =>
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [evalWiderAtom, beq_false_of_ne hne]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · rfl
    · obtain ⟨⟨k, b⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      simp [extractNumAtom, hb] at hnoNum
    · obtain ⟨tier, ht⟩ := Option.isSome_iff_exists.mp hstr
      exact checkValue_strTier_false ht (fun _ _ h => by cases h)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  | restriction t fs =>
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, hfs⟩ | ⟨ht, _⟩
    · obtain ⟨⟨k, b⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hfold : (foldRatFacetBounds b fs).isSome = true := by
        have aux : ∀ (acc : RatBounds) (l : List Facet),
            (∀ f ∈ l, isOrderFacet f = true) → (foldRatFacetBounds acc l).isSome = true := by
          intro acc l hl
          induction l generalizing acc with
          | nil => rfl
          | cons f rest ih =>
            obtain ⟨fb, hfb⟩ := Option.isSome_iff_exists.mp (hl f (List.mem_cons_self ..))
            simp only [foldRatFacetBounds, hfb]
            exact ih _ fun f' hf' => hl f' (List.mem_cons_of_mem _ hf')
        exact aux b fs hfs
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hfold
      simp [extractNumAtom, hb, hb'] at hnoNum
    · simp only [evalWiderAtom, Bool.and_eq_false_iff]
      left
      rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

theorem evalWiderAtom_float_or_double_false {a : DataRange}
    (ha : legacy_isWiderExactAtom a = true) (hnoLit : a ≠ .datatype literalDatatype)
    (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (v : Value)
    (hfd : (∃ f, v = .float f) ∨ (∃ d, v = .double d)) :
    evalWiderAtom a v = false := by
  have hnotNum : ∀ q, v ≠ .number q := fun q h => by rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases h
  have hnotPL : ∀ s l, v ≠ .plainLiteral s l := fun s l h => by rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases h
  cases a with
  | datatype t =>
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [evalWiderAtom, beq_false_of_ne hne]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      exact checkValue_numericBase_false hb hnotNum (fun _ hi => by
        rw [hi] at hfd
        rcases hfd with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h)
    · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
      exact checkValue_strTier_false ht hnotPL
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  | restriction t fs =>
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, Bool.and_eq_false_iff]; left
    rcases ha with ⟨hnum, _⟩ | ⟨ht, _⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      exact checkValue_numericBase_false hb hnotNum (fun _ hi => by
        rw [hi] at hfd
        rcases hfd with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h)
    · rcases hfd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem foldr_intersect_int_iff (bs : List IntegerBounds) (z : Int) :
    (bs.foldr IntegerBounds.intersect {}).contains z ↔ ∀ b ∈ bs, b.contains z := by
  induction bs with
  | nil => simp [IntegerBounds.contains]
  | cons b rest ih =>
    simp only [List.foldr_cons, IntegerBounds.contains_intersect, ih, List.forall_mem_cons]

private theorem foldr_intersect_rat_iff (bs : List RatBounds) (q : Rat) :
    (bs.foldr RatBounds.intersect {}).contains q ↔ ∀ b ∈ bs, b.contains q := by
  induction bs with
  | nil => simp [RatBounds.contains]
  | cons b rest ih =>
    simp only [List.foldr_cons, RatBounds.contains_intersect, ih, List.forall_mem_cons]

private theorem foldr_intersect_nat_iff (bs : List NatBounds) (n : Nat) :
    (bs.foldr NatBounds.intersect {}).contains n ↔ ∀ b ∈ bs, b.contains n := by
  induction bs with
  | nil => simp [NatBounds.contains]
  | cons b rest ih =>
    simp only [List.foldr_cons, NatBounds.contains_intersect, ih, List.forall_mem_cons]

theorem decimalValue_ofInt (z : Int) : DecimalValue (Rat.ofInt z) :=
  ⟨z, 0, by apply Rat.ext <;> simp [Rat.ofInt, Rat.num_mkRat, Rat.den_mkRat]⟩

private theorem evalWiderAtom_neg_int_iff {a : DataRange}
    (ha : legacy_isWiderExactAtom a = true) (hnoLit : a ≠ .datatype literalDatatype)
    (i : Interpretation datatypeMap) (z : Int) :
    evalWiderAtom a (.integer z) = false ↔
      ∀ b ∈ (match a with
        | .oneOf ls =>
          ((decodeLiteralsList ls).getD []).filterMap fun
            | Value.number q =>
              if q.den == 1 then some ({ lower := some q.num, upper := some q.num } : IntegerBounds)
              else none
            | _ => none
        | a => match extractNumAtom a with | some (_, b) => [b.toIntBounds] | none => []),
        ¬ b.contains z := by
  cases a with
  | oneOf ls =>
    simp only [legacy_isWiderExactAtom] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    simp only [evalWiderAtom, hvs, Option.getD_some, Bool.eq_false_iff, ne_eq,
      List.contains_iff_mem, List.mem_filterMap]
    constructor
    · intro hnot b ⟨v, hv, hvb⟩
      cases v with
      | number q =>
        dsimp only at hvb
        split at hvb
        · rename_i hden
          cases hvb
          intro hcon
          have hze : q.num = z := by
            simp only [IntegerBounds.contains, Option.elim_some] at hcon; omega
          have hqe : q = Rat.ofInt z := by
            apply Rat.ext
            · simp [hze]
            · simp [beq_iff_eq.mp hden]
          have hveq : Value.number q = Value.integer z := by
            simp [Value.integer, hqe]
          exact hnot (hveq ▸ hv)
        · cases hvb
      | _ => cases hvb
    · intro hall hmem
      have hb : ({ lower := some z, upper := some z } : IntegerBounds).contains z := by
        simp [IntegerBounds.contains]
      exact hall _ ⟨.integer z, hmem, by simp⟩ hb
  | datatype t =>
    dsimp only
    cases hex : extractNumAtom (.datatype t) with
    | none =>
      simp [evalWiderAtom_nonNum_number_false ha hnoLit (fun _ h => by cases h) hex (Rat.ofInt z)]
    | some kb =>
      rcases kb with ⟨k, b⟩
      simp only [List.mem_singleton, forall_eq, Bool.eq_false_iff, ne_eq]
      rw [evalWiderAtom_extractNumAtom_iff ha hex i (.integer z), b.toIntBounds_iff z]
      have hk : k.holds (Rat.ofInt z) := by
        cases k <;> simp [NumericKind.holds]
        exact decimalValue_ofInt z
      constructor
      · intro h hcon; exact h ⟨Rat.ofInt z, rfl, hk, hcon⟩
      · rintro h ⟨q, hq, _, hcon⟩
        have hqe := Value.number.inj hq
        rw [← hqe] at hcon; exact h hcon
  | restriction t fs =>
    dsimp only
    cases hex : extractNumAtom (.restriction t fs) with
    | none =>
      simp [evalWiderAtom_nonNum_number_false ha hnoLit (fun _ h => by cases h) hex (Rat.ofInt z)]
    | some kb =>
      rcases kb with ⟨k, b⟩
      simp only [List.mem_singleton, forall_eq, Bool.eq_false_iff, ne_eq]
      rw [evalWiderAtom_extractNumAtom_iff ha hex i (.integer z), b.toIntBounds_iff z]
      have hk : k.holds (Rat.ofInt z) := by
        cases k <;> simp [NumericKind.holds]
        exact decimalValue_ofInt z
      constructor
      · intro h hcon; exact h ⟨Rat.ofInt z, rfl, hk, hcon⟩
      · rintro h ⟨q, hq, _, hcon⟩
        have hqe := Value.number.inj hq
        rw [← hqe] at hcon; exact h hcon
  | _ => cases ha

private theorem evalWiderAtom_neg_rat_iff {a : DataRange} {stratum : NumericKind}
    (ha : legacy_isWiderExactAtom a = true) (hnoLit : a ≠ .datatype literalDatatype)
    (i : Interpretation datatypeMap) {q : Rat}
    (hstratum : (stratum = .dec ∧ DecimalValue q ∧ q.den ≠ 1) ∨
      (stratum = .rat ∧ ¬ DecimalValue q)) :
    evalWiderAtom a (.number q) = false ↔
      ∀ b ∈ negRatBoundsForStratum stratum a, ¬ b.contains q := by
  have hnonOneOf (hno : ∀ ls, a ≠ .oneOf ls) :
      evalWiderAtom a (.number q) = false ↔
        ∀ b ∈ (match extractNumAtom a with
          | some (k, b) =>
            match stratum, k with
            | .int, _ => [b]
            | .dec, .dec => [b]
            | .dec, .rat => [b]
            | .rat, .rat => [b]
            | _, _ => []
          | none => []), ¬ b.contains q := by
    cases hex : extractNumAtom a with
    | none =>
      simp [evalWiderAtom_nonNum_number_false ha hnoLit hno hex q]
    | some kb =>
      rcases kb with ⟨k, b⟩
      rw [Bool.eq_false_iff]
      change ¬ evalWiderAtom a (.number q) = true ↔ _
      rw [evalWiderAtom_extractNumAtom_iff ha hex i (.number q)]
      rcases hstratum with ⟨rfl, hdec, hden⟩ | ⟨rfl, hndec⟩
      · cases k
        · simp [NumericKind.holds, hden]
        · simp [NumericKind.holds, hdec]
        · simp [NumericKind.holds]
      · cases k
        · have hden : q.den ≠ 1 := fun h1 => hndec ⟨q.num, 0, by
            apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat, h1]⟩
          simp [NumericKind.holds, hden]
        · simp [NumericKind.holds, hndec]
        · simp [NumericKind.holds]
  cases a with
  | oneOf ls =>
    simp only [legacy_isWiderExactAtom] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    simp only [evalWiderAtom, hvs, negRatBoundsForStratum, Option.getD_some,
      Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_filterMap]
    constructor
    · intro hnot b ⟨v, hv, hvb⟩
      cases v with
      | number q' =>
        cases hvb
        intro hcon
        simp only [RatBounds.contains, Option.elim_some, RatEndpoint.holdsLower,
          RatEndpoint.holdsUpper, ↓reduceIte] at hcon
        have hqe : q' = q := Rat.le_antisymm hcon.1 hcon.2
        exact hnot (hqe ▸ hv)
      | _ => cases hvb
    · intro hall hmem
      have hb : ({ lower := some ⟨q, true⟩, upper := some ⟨q, true⟩ } : RatBounds).contains q := by
        simp [RatBounds.contains, RatEndpoint.holdsLower, RatEndpoint.holdsUpper]
      exact hall _ ⟨.number q, hmem, rfl⟩ hb
  | datatype t => exact hnonOneOf (fun _ h => by cases h)
  | restriction t fs => exact hnonOneOf (fun _ h => by cases h)
  | _ => cases ha

/-! Length-facet evaluation & completeness helpers -/

private theorem foldLenFacetBounds_holds_iff {fs : List Facet} {acc b : NatBounds}
    (hfold : foldLenFacetBounds acc fs = some b) {n : Nat} :
    (acc.contains n ∧ ∀ f ∈ fs,
      ∃ q : Rat, decodeLiteral f.bound = some (.number q) ∧ q.den = 1 ∧ 0 ≤ q.num ∧
        ∃ lf, lengthFacet f.name = some lf ∧ lf.holdsNat q.num.toNat n) ↔ b.contains n := by
  induction fs generalizing acc with
  | nil =>
    cases hfold; simp
  | cons f rest ih =>
    simp only [foldLenFacetBounds] at hfold
    cases hfb : lenFacetBounds f with
    | none => simp [hfb] at hfold
    | some fb =>
      simp only [hfb] at hfold
      rw [← ih hfold, NatBounds.contains_intersect, List.forall_mem_cons,
        lenFacetBounds_holdsNat_iff hfb]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

private theorem lenFacetBounds_isSome_spec {f : Facet} (h : isLenFacet f = true) :
    ∃ q : Rat, decodeLiteral f.bound = some (.number q) ∧ q.den = 1 ∧ 0 ≤ q.num ∧
      (lengthFacet f.name).isSome = true := by
  unfold isLenFacet lenFacetBounds at h
  cases hl : lengthFacet f.name with
  | none => simp [hl] at h
  | some lf =>
    cases hb : decodeLiteral f.bound with
    | none => simp [hl, hb] at h
    | some v =>
      cases v <;> simp only [hl, hb] at h
      case number q =>
        cases lf <;> simp only at h <;> split at h <;> try contradiction
        all_goals
          rename_i hq
          exact ⟨q, rfl, hq.1, hq.2, rfl⟩
      all_goals cases lf <;> contradiction

private theorem evalWiderAtom_lenRestriction_iff {t : IRI} {fs : List Facet} {b : NatBounds}
    (ha : legacy_isWiderExactAtom (.restriction t fs) = true)
    (hfsAll : ∀ f ∈ fs, isLenFacet f = true)
    (hfold : foldLenFacetBounds {} fs = some b)
    (i : Interpretation datatypeMap) (v : Value) (n : Nat)
    (hvalLen : valueSpace t v →
      ∀ f ∈ fs, ∀ q : Rat, q.den = 1 → 0 ≤ q.num →
        (facetSpace t f.name (.number q) v ↔
          ∃ lf, lengthFacet f.name = some lf ∧ lf.holdsNat q.num.toNat n)) :
    evalWiderAtom (.restriction t fs) v = true ↔ valueSpace t v ∧ b.contains n := by
  have ⟨hsup, _⟩ := legacy_widerRestriction_supported ha
  rw [legacy_evalWiderAtom_iff ha i v]
  simp only [dataHolds, i.datatypeAgreement t hsup (i.embedValue v)]
  constructor
  · rintro ⟨⟨w, hw, he⟩, hfs⟩
    have hwe : w = v := i.embedValue_injective he
    subst hwe
    refine ⟨hw, (foldLenFacetBounds_holds_iff hfold).mp ⟨⟨Nat.zero_le _, trivial⟩, fun f hf => ?_⟩⟩
    obtain ⟨q, hbd, hq1, hq2, _⟩ := lenFacetBounds_isSome_spec (hfsAll f hf)
    have hfh := (facetHolds_iff_check i t f (.number q) w hbd).mp (hfs f hf)
    have hfs' := (checkFacet_iff t f.name (.number q) w).mp hfh
    obtain ⟨lf, hlf, hh⟩ := (hvalLen hw f hf q hq1 hq2).mp hfs'
    exact ⟨q, hbd, hq1, hq2, lf, hlf, hh⟩
  · rintro ⟨hv, hcon⟩
    have hrest := ((foldLenFacetBounds_holds_iff hfold).mpr hcon).2
    refine ⟨⟨v, hv, rfl⟩, fun f hf => ?_⟩
    obtain ⟨q, hqdec, hq1, hq2, lf, hlf, hh⟩ := hrest f hf
    have hfs' := (hvalLen hv f hf q hq1 hq2).mpr ⟨lf, hlf, hh⟩
    exact (facetHolds_iff_check i t f (.number q) v hqdec).mpr ((checkFacet_iff t f.name (.number q) v).mpr hfs')

private theorem foldLenFacetBounds_isSome_of_all {fs : List Facet}
    (h : ∀ f ∈ fs, isLenFacet f = true) : (foldLenFacetBounds {} fs).isSome = true := by
  have aux : ∀ (acc : NatBounds) (l : List Facet),
      (∀ f ∈ l, isLenFacet f = true) → (foldLenFacetBounds acc l).isSome = true := by
    intro acc l hl
    induction l generalizing acc with
    | nil => rfl
    | cons f rest ih =>
      obtain ⟨fb, hfb⟩ := Option.isSome_iff_exists.mp (hl f (List.mem_cons_self ..))
      simp only [foldLenFacetBounds, hfb]
      exact ih _ fun f' hf' => hl f' (List.mem_cons_of_mem _ hf')
  exact aux {} fs h

private theorem sampleWordBounds_cover {α} (alphabet : BoundedWords.Alphabet α) (filler : α)
    {K : Nat} {pos neg : List DataRange} {bounds : List NatBounds}
    (wrap : List α → Value) (hwrapInj : ∀ {xs ys}, wrap xs = wrap ys → xs = ys)
    (hsub : ∀ xs ∈ sampleWordBounds alphabet filler (K + (allOneOfValues neg).length) bounds,
      wrap xs ∈ legacy_widerCandidates K pos neg)
    (heval : ∀ xs, wrap xs ∉ allOneOfValues neg →
      (∃ b ∈ bounds, b.contains xs.length) → evalWiderPartition pos neg (wrap xs) = true)
    {xs : List α} (hxs : ∃ b ∈ bounds, b.contains xs.length) :
    K ≤ ((legacy_widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).length ∨
      wrap xs ∈ legacy_widerCandidates K pos neg := by
  let count := K + (allOneOfValues neg).length
  obtain ⟨b, hb, hcontains⟩ := hxs
  cases upper : b.upper with
  | none =>
    refine .inl (w_bounded_family_ge_K K
      (fun k => wrap (List.replicate (b.lower + k) filler)) (fun _ _ heq => ?_) ?_ ?_)
    · have eq := congrArg List.length (hwrapInj heq)
      simpa using eq
    · intro v hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      apply hsub
      exact List.mem_flatMap.mpr ⟨b, hb, by rw [upper]; exact List.mem_map_of_mem hk⟩
    · intro k _ hnot
      exact heval _ hnot ⟨b, hb, by simp [NatBounds.contains, upper]⟩
  | some hi =>
    have hlo : b.lower ≤ xs.length := hcontains.1
    have hhi : xs.length ≤ hi := by simpa [upper] using hcontains.2
    have valid : b.lower ≤ hi := Nat.le_trans hlo hhi
    let n := BoundedWords.sampleLength count b.lower hi
    by_cases enough : count ≤ alphabet.size ^ n
    · have boundsN := BoundedWords.sampleLength_bounds (k := count) valid
      refine .inl (w_bounded_family_ge_K K (fun k => wrap (alphabet.word n k))
        (fun _ _ heq => alphabet.word_injective (by omega) (by omega) (hwrapInj heq)) ?_ ?_)
      · intro v hv
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
        apply hsub
        refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
        simp only [upper, Nat.not_lt.mpr valid, ite_false]
        exact alphabet.large_mem enough (List.mem_range.mp hk)
      · intro k _ hnot
        exact heval _ hnot ⟨b, hb, by simpa [NatBounds.contains, upper, alphabet.word_length] using boundsN⟩
    · refine .inr (hsub xs (List.mem_flatMap.mpr ⟨b, hb, ?_⟩))
      simp only [upper, Nat.not_lt.mpr valid, ite_false]
      exact alphabet.small_mem enough hlo hhi

private theorem sampleLenStrings_cover {K : Nat} {pos neg : List DataRange} {bounds : List NatBounds}
    (wrap : String → Value) (hwrapInj : ∀ {s₁ s₂}, wrap s₁ = wrap s₂ → s₁ = s₂)
    (hsub : ∀ s ∈ sampleLenStringsForBounds (K + (allOneOfValues neg).length) bounds,
      wrap s ∈ legacy_widerCandidates K pos neg)
    (heval : ∀ s, wrap s ∉ allOneOfValues neg →
      (∃ b ∈ bounds, b.contains s.length) → evalWiderPartition pos neg (wrap s) = true)
    {s : String} (hs : ∃ b ∈ bounds, b.contains s.length) :
    K ≤ ((legacy_widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).length ∨
      wrap s ∈ legacy_widerCandidates K pos neg := by
  have h := sampleWordBounds_cover (K := K) (pos := pos) (neg := neg) (bounds := bounds)
    BoundedWords.scalars 'a' (fun xs => wrap (String.ofList xs))
    (fun {xs ys} eq => by
      have e := congrArg String.toList (hwrapInj eq)
      simpa using e)
    (fun xs h => hsub _ (List.mem_map_of_mem h))
    (fun xs h hb => heval _ h (by simpa [String.length] using hb))
    (xs := s.toList) hs
  simpa using h

private theorem lengthFacet_holds_iff_holdsNat (lf : LengthFacet) (n : Nat) (s : String) :
    lf.holds n s ↔ lf.holdsNat n s.length := by
  cases lf <;> rfl

/-! Standalone per-sort atom evaluators (keeps `legacy_cover_of_evalWiderPartition` fast) -/

private theorem evalWiderAtom_plainLiteral_lang_iff (i : Interpretation datatypeMap)
    {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (hnoLit : a ≠ .datatype literalDatatype) (hnoOneOf : ∀ ls, a ≠ .oneOf ls)
    (s' l' : String) (hlne : l' ≠ "") :
    evalWiderAtom a (.plainLiteral s' l') = true ↔
      ∃ b, extractLenOf (rdf "PlainLiteral") a = some b ∧ b.contains s'.length := by
  have hlEmpty : l'.isEmpty = false := by
    cases h : l'.isEmpty
    · rfl
    · exact (hlne (String.isEmpty_iff.mp h)).elim
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, beq_false_of_ne hne, extractLenOf]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneP : t ≠ rdf "PlainLiteral" := by intro rfl; cases hb
      simp only [beq_false_of_ne hneP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; decide
    · obtain ⟨tier, ht⟩ := Option.isSome_iff_exists.mp hstr
      cases tier with
      | plainLiteral =>
        have htP : t = rdf "PlainLiteral" := by
          unfold strTierOfIRI at ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht; · cases ht
          split at ht
          · rename_i he; exact beq_iff_eq.mp he
          · cases ht
        subst htP
        simp [NatBounds.contains]; rfl
      | _ =>
        have hneP : t ≠ rdf "PlainLiteral" := by intro rfl; cases ht
        simp only [beq_false_of_ne hneP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
          exists_false, iff_false]
        intro hcv
        obtain ⟨_, _, hholds, heq⟩ := (valueSpace_strTier_iff ht _).mp ((checkValue_iff _ _).mp hcv)
        have ⟨_, hle⟩ := Value.plainLiteral.inj heq; subst hle
        simp [StrTier.holds, hlEmpty] at hholds
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
  | restriction t fs =>
    have ha' := ha
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, _⟩ | ⟨ht, hfs⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneP : t ≠ rdf "PlainLiteral" := by intro rfl; cases hb
      simp only [extractLenOf, beq_false_of_ne hneP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_and, exists_false, iff_false]
      simp only [evalWiderAtom]; rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; simp
    · by_cases htP : t = rdf "PlainLiteral"
      · subst htP
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (foldLenFacetBounds_isSome_of_all hfs)
        simp only [extractLenOf, beq_self_eq_true, ↓reduceIte, hb, Option.some.injEq, exists_eq_left']
        rw [evalWiderAtom_lenRestriction_iff ha' hfs hb i (.plainLiteral s' l') s'.length]
        · have hvs : valueSpace (rdf "PlainLiteral") (.plainLiteral s' l') := (checkValue_iff _ _).mp rfl
          simp [hvs]
        · intro hv _ _ q hq1 hq2
          simp [facetSpace, lengthFacet_holds_iff_holdsNat, hq1, hq2, hv]
      · simp only [extractLenOf, beq_false_of_ne htP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
          false_and, exists_false, iff_false]
        intro hev
        have hcv := (Bool.and_eq_true_iff.mp hev).1
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl
        · have hvs := (valueSpace_strTier_iff (t := xsd "string") (tier := .string) rfl _).mp
            ((checkValue_iff _ _).mp hcv)
          obtain ⟨_, _, hh, heq⟩ := hvs
          have ⟨_, hle⟩ := Value.plainLiteral.inj heq; subst hle
          simp [StrTier.holds, hlEmpty] at hh
        · exact (htP rfl).elim
        · cases hcv
        · cases hcv
        · cases hcv
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem evalWiderAtom_string_noSub_iff (i : Interpretation datatypeMap)
    {a : DataRange} (ha : legacy_isWiderExactAtom a = true) (hns : atomUsesStrSubtype a = false)
    (hnoLit : a ≠ .datatype literalDatatype) (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (s' : String) :
    evalWiderAtom a (Value.string s') = true ↔
      ∃ b, extractStrOrPlainLen a = some b ∧ b.contains s'.length := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, beq_false_of_ne hne, extractStrOrPlainLen]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneSP : (t == xsd "string" || t == rdf "PlainLiteral") = false := by
        cases h1 : (t == xsd "string" || t == rdf "PlainLiteral")
        · rfl
        · simp only [Bool.or_eq_true, beq_iff_eq] at h1; rcases h1 with rfl | rfl <;> cases hb
      simp only [hneSP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and, exists_false, iff_false]
      rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; decide
    · obtain ⟨tier, ht⟩ := Option.isSome_iff_exists.mp hstr
      unfold strTierOfIRI at ht
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht; · (rename_i he; rw [beq_iff_eq.mp he] at hns; cases hns)
      split at ht
      · rename_i he; rw [beq_iff_eq.mp he]; simp [NatBounds.contains]; rfl
      split at ht
      · rename_i he; rw [beq_iff_eq.mp he]; simp [NatBounds.contains]; rfl
      cases ht
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
  | restriction t fs =>
    have ha' := ha
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, _⟩ | ⟨ht, hfs⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneSP : (t == xsd "string" || t == rdf "PlainLiteral") = false := by
        cases h1 : (t == xsd "string" || t == rdf "PlainLiteral")
        · rfl
        · simp only [Bool.or_eq_true, beq_iff_eq] at h1; rcases h1 with rfl | rfl <;> cases hb
      simp only [extractStrOrPlainLen, hneSP, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_and, exists_false, iff_false]
      simp only [evalWiderAtom]; rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; simp
    · by_cases htSP : t = xsd "string" ∨ t = rdf "PlainLiteral"
      · have hbool : (t == xsd "string" || t == rdf "PlainLiteral") = true := by
          rcases htSP with rfl | rfl <;> decide
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (foldLenFacetBounds_isSome_of_all hfs)
        simp only [extractStrOrPlainLen, hbool, ↓reduceIte, hb, Option.some.injEq, exists_eq_left']
        rw [evalWiderAtom_lenRestriction_iff ha' hfs hb i (Value.string s') s'.length]
        · have hvs : valueSpace t (Value.string s') := by
            rcases htSP with rfl | rfl <;> exact (checkValue_iff _ _).mp rfl
          simp [hvs]
        · intro hv _ _ q hq1 hq2
          simp [facetSpace, lengthFacet_holds_iff_holdsNat, hq1, hq2, hv]
      · have hbool : (t == xsd "string" || t == rdf "PlainLiteral") = false := by
          cases h1 : (t == xsd "string" || t == rdf "PlainLiteral")
          · rfl
          · simp only [Bool.or_eq_true, beq_iff_eq] at h1; exact (htSP h1).elim
        simp only [extractStrOrPlainLen, hbool, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
          false_and, exists_false, iff_false]
        intro hev
        have hcv := (Bool.and_eq_true_iff.mp hev).1
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl
        · exact (htSP (.inl rfl)).elim
        · exact (htSP (.inr rfl)).elim
        · cases hcv
        · cases hcv
        · cases hcv
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem lenAtom_noSubtype {a : DataRange} {b : NatBounds}
    (h : extractStrOrPlainLen a = some b) :
    atomUsesStrSubtype a = false := by
  cases a with
  | datatype t =>
    simp only [extractStrOrPlainLen] at h
    split at h
    · rename_i ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with rfl | rfl <;> decide
    · cases h
  | restriction => rfl
  | _ => cases h

private theorem evalWiderAtom_subtype_eq {a : DataRange} (h : atomUsesStrSubtype a = true)
    {s t : String} (agree : stringSubtypeFlags t = stringSubtypeFlags s) :
    evalWiderAtom a (Value.string t) = evalWiderAtom a (Value.string s) := by
  cases a with
  | datatype iri =>
    simp only [atomUsesStrSubtype, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
    · change isLanguageTag t = isLanguageTag s
      exact congrArg StringSubtypeFlags.language agree
    · change isNCName t = isNCName s
      exact congrArg StringSubtypeFlags.ncname agree
    · change isName t = isName s
      exact congrArg StringSubtypeFlags.name agree
    · change isNMTOKEN t = isNMTOKEN s
      exact congrArg StringSubtypeFlags.nameToken agree
    · change isToken t = isToken s
      exact congrArg StringSubtypeFlags.token agree
    · change isNormalizedString t = isNormalizedString s
      exact congrArg StringSubtypeFlags.normalized agree
  | _ => cases h

private theorem evalWiderAtom_anyURI_iff (i : Interpretation datatypeMap)
    {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (hnoLit : a ≠ .datatype literalDatatype) (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (s' : String) :
    evalWiderAtom a (.anyURI s') = true ↔
      ∃ b, extractLenOf (xsd "anyURI") a = some b ∧ b.contains s'.length := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, beq_false_of_ne hne, extractLenOf]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneU : t ≠ xsd "anyURI" := by intro rfl; cases hb
      simp only [beq_false_of_ne hneU, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; decide
    · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
      have hneU : t ≠ xsd "anyURI" := by intro rfl; cases ht
      simp only [beq_false_of_ne hneU, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_strTier_false ht (fun _ _ h => by cases h)]; decide
    · simp [NatBounds.contains]; rfl
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
  | restriction t fs =>
    have ha' := ha
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, _⟩ | ⟨ht, hfs⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneU : t ≠ xsd "anyURI" := by intro rfl; cases hb
      simp only [extractLenOf, beq_false_of_ne hneU, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_and, exists_false, iff_false]
      simp only [evalWiderAtom]; rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; simp
    · by_cases htU : t = xsd "anyURI"
      · subst htU
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (foldLenFacetBounds_isSome_of_all hfs)
        simp only [extractLenOf, beq_self_eq_true, ↓reduceIte, hb, Option.some.injEq, exists_eq_left']
        rw [evalWiderAtom_lenRestriction_iff ha' hfs hb i (.anyURI s') s'.length]
        · have hvs : valueSpace (xsd "anyURI") (.anyURI s') := (checkValue_iff _ _).mp rfl
          simp [hvs]
        · intro hv _ _ q hq1 hq2
          simp [facetSpace, lengthFacet_holds_iff_holdsNat, hq1, hq2, hv]
      · simp only [extractLenOf, beq_false_of_ne htU, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
          false_and, exists_false, iff_false]
        intro hev
        have hcv := (Bool.and_eq_true_iff.mp hev).1
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl
        · cases hcv
        · cases hcv
        · exact (htU rfl).elim
        · cases hcv
        · cases hcv
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem evalWiderAtom_hexBinary_iff (i : Interpretation datatypeMap)
    {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (hnoLit : a ≠ .datatype literalDatatype) (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (bs' : List UInt8) :
    evalWiderAtom a (.hexBinary bs') = true ↔
      ∃ b, extractLenOf (xsd "hexBinary") a = some b ∧ b.contains bs'.length := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, beq_false_of_ne hne, extractLenOf]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneH : t ≠ xsd "hexBinary" := by intro rfl; cases hb
      simp only [beq_false_of_ne hneH, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; decide
    · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
      have hneH : t ≠ xsd "hexBinary" := by intro rfl; cases ht
      simp only [beq_false_of_ne hneH, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_strTier_false ht (fun _ _ h => by cases h)]; decide
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · simp [NatBounds.contains]; rfl
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
  | restriction t fs =>
    have ha' := ha
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, _⟩ | ⟨ht, hfs⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneH : t ≠ xsd "hexBinary" := by intro rfl; cases hb
      simp only [extractLenOf, beq_false_of_ne hneH, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_and, exists_false, iff_false]
      simp only [evalWiderAtom]; rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; simp
    · by_cases htH : t = xsd "hexBinary"
      · subst htH
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (foldLenFacetBounds_isSome_of_all hfs)
        simp only [extractLenOf, beq_self_eq_true, ↓reduceIte, hb, Option.some.injEq, exists_eq_left']
        rw [evalWiderAtom_lenRestriction_iff ha' hfs hb i (.hexBinary bs') bs'.length]
        · have hvs : valueSpace (xsd "hexBinary") (.hexBinary bs') := (checkValue_iff _ _).mp rfl
          simp [hvs]
        · intro hv _ _ q hq1 hq2
          simp [facetSpace, LengthFacet.holdsNat, hq1, hq2, hv]
      · simp only [extractLenOf, beq_false_of_ne htH, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
          false_and, exists_false, iff_false]
        intro hev
        have hcv := (Bool.and_eq_true_iff.mp hev).1
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl
        · cases hcv
        · cases hcv
        · cases hcv
        · exact (htH rfl).elim
        · cases hcv
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem evalWiderAtom_base64Binary_iff (i : Interpretation datatypeMap)
    {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (hnoLit : a ≠ .datatype literalDatatype) (hnoOneOf : ∀ ls, a ≠ .oneOf ls) (bs' : List UInt8) :
    evalWiderAtom a (.base64Binary bs') = true ↔
      ∃ b, extractLenOf (xsd "base64Binary") a = some b ∧ b.contains bs'.length := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hnoLit (congrArg DataRange.datatype h)
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalWiderAtom, beq_false_of_ne hne, extractLenOf]
    rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne rfl).elim
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneB : t ≠ xsd "base64Binary" := by intro rfl; cases hb
      simp only [beq_false_of_ne hneB, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; decide
    · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
      have hneB : t ≠ xsd "base64Binary" := by intro rfl; cases ht
      simp only [beq_false_of_ne hneB, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and,
        exists_false, iff_false]
      rw [checkValue_strTier_false ht (fun _ _ h => by cases h)]; decide
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · simp [NatBounds.contains]; rfl
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
    · exact ⟨(fun h => by cases h), (fun ⟨_, h, _⟩ => by split at h <;> first | (rename_i he; exact absurd he (by decide)) | cases h)⟩
  | restriction t fs =>
    have ha' := ha
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ha
    rcases ha with ⟨hnum, _⟩ | ⟨ht, hfs⟩
    · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
      have hneB : t ≠ xsd "base64Binary" := by intro rfl; cases hb
      simp only [extractLenOf, beq_false_of_ne hneB, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_and, exists_false, iff_false]
      simp only [evalWiderAtom]; rw [checkValue_numericBase_false hb (fun _ h => by cases h)]; simp
    · by_cases htB : t = xsd "base64Binary"
      · subst htB
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (foldLenFacetBounds_isSome_of_all hfs)
        simp only [extractLenOf, beq_self_eq_true, ↓reduceIte, hb, Option.some.injEq, exists_eq_left']
        rw [evalWiderAtom_lenRestriction_iff ha' hfs hb i (.base64Binary bs') bs'.length]
        · have hvs : valueSpace (xsd "base64Binary") (.base64Binary bs') := (checkValue_iff _ _).mp rfl
          simp [hvs]
        · intro hv _ _ q hq1 hq2
          simp [facetSpace, LengthFacet.holdsNat, hq1, hq2, hv]
      · simp only [extractLenOf, beq_false_of_ne htB, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
          false_and, exists_false, iff_false]
        intro hev
        have hcv := (Bool.and_eq_true_iff.mp hev).1
        rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl
        · cases hcv
        · cases hcv
        · cases hcv
        · cases hcv
        · exact (htB rfl).elim
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem evalWiderAtom_xmlLiteral_eq {a : DataRange} (ha : legacy_isWiderExactAtom a = true)
    (hno1 : ∀ ls, a ≠ .oneOf ls) {s₁ s₂ : String}
    (hs₁ : checkCanonicalXMLLiteral s₁ = true) (hs₂ : checkCanonicalXMLLiteral s₂ = true) :
    evalWiderAtom a (.xmlLiteral s₁) = evalWiderAtom a (.xmlLiteral s₂) := by
  cases a with
  | datatype t =>
    by_cases hlit : t = literalDatatype
    · subst hlit; simp [evalWiderAtom]
    · simp only [evalWiderAtom, beq_false_of_ne hlit]
      simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at ha
      rcases ha with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
      · exact (hlit rfl).elim
      · rfl
      · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
        rw [checkValue_numericBase_false hb (fun _ h => by cases h),
            checkValue_numericBase_false hb (fun _ h => by cases h)]
      · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
        rw [checkValue_strTier_false ht (fun _ _ h => by cases h),
            checkValue_strTier_false ht (fun _ _ h => by cases h)]
      · rfl
      · have h1 : checkValue (rdf "XMLLiteral") (.xmlLiteral s₁) = true :=
          (checkValue_iff _ _).mpr ((valueSpace_xmlLiteral_iff _).mpr ⟨s₁, hs₁, rfl⟩)
        have h2 : checkValue (rdf "XMLLiteral") (.xmlLiteral s₂) = true :=
          (checkValue_iff _ _).mpr ((valueSpace_xmlLiteral_iff _).mpr ⟨s₂, hs₂, rfl⟩)
        exact h1.trans h2.symm
      · rfl
      · rfl
      · rfl
      · rfl
  | restriction t fs =>
    simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
    have hf (u : String) : checkValue t (.xmlLiteral u) = false := by
      rcases ha with ⟨hnum, _⟩ | ⟨ht, _⟩
      · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
        exact checkValue_numericBase_false hb (fun _ h => by cases h)
      · rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl
    simp [evalWiderAtom, hf]
  | oneOf ls => exact (hno1 ls rfl).elim
  | _ => cases ha

private theorem checkValue_irrational_iff (t : IRI) (q : Rat) :
    checkValue t (.irrational q) = true ↔ t = owlReal ∧ DecimalValue q ∧ q.den ≠ 1 := by
  rw [checkValue_iff, valueSpace_irrational_iff]

private theorem checkAboveFacet_iff (f : Facet) (q : Rat)
    (hvalid : DecimalValue q ∧ q.den ≠ 1) :
    (match decodeLiteral f.bound with
      | some b => checkFacet owlReal f.name b (.irrational q)
      | none => false) = true ↔
      ∃ b, aboveFacetBounds f = some b ∧ b.contains q := by
  have hval := (checkValue_irrational_iff owlReal q).mpr ⟨rfl, hvalid⟩
  cases ho : orderFacet f.name
  · cases hd : decodeLiteral f.bound with
    | none => simp [aboveFacetBounds, ratFacetBounds, ho, hd]
    | some v =>
      cases v <;> simp [checkFacet, aboveFacetBounds, ratFacetBounds, ho, hd]
  · rename_i ord
    cases hd : decodeLiteral f.bound with
    | none => simp [aboveFacetBounds, ratFacetBounds, ho, hd]
    | some v =>
      cases v <;> try simp [checkFacet, aboveFacetBounds, ratFacetBounds, ho, hd]
      case number b =>
        cases ord <;> simp [hval, OrderFacet.holdsAbove, RatBounds.contains,
          RatEndpoint.holdsLower, RatEndpoint.holdsUpper]

private theorem checkAboveFacets_iff (fs : List Facet) (acc : RatBounds) (q : Rat)
    (hvalid : DecimalValue q ∧ q.den ≠ 1) :
    (acc.contains q ∧ ∀ f ∈ fs, (match decodeLiteral f.bound with
      | some b => checkFacet owlReal f.name b (.irrational q)
      | none => false) = true) ↔
      ∃ b, foldAboveFacetBounds acc fs = some b ∧ b.contains q := by
  induction fs generalizing acc with
  | nil => simp [foldAboveFacetBounds]
  | cons f rest ih =>
    simp only [List.forall_mem_cons, checkAboveFacet_iff f q hvalid, foldAboveFacetBounds,
      Option.bind_eq_some_iff]
    constructor
    · rintro ⟨ha, ⟨b, hf, hb⟩, hrest⟩
      obtain ⟨out, he, hc⟩ := (ih (acc.intersect b)).mp
        ⟨(RatBounds.contains_intersect _ _ _).mpr ⟨ha, hb⟩, hrest⟩
      exact ⟨out, ⟨b, hf, he⟩, hc⟩
    · rintro ⟨out, ⟨b, hf, he⟩, hc⟩
      obtain ⟨hab, hrest⟩ := (ih (acc.intersect b)).mpr ⟨out, he, hc⟩
      obtain ⟨ha, hb⟩ := (RatBounds.contains_intersect _ _ _).mp hab
      exact ⟨ha, ⟨b, hf, hb⟩, hrest⟩

private theorem evalWiderAtom_oneOf_irrational (ls : List Literal) (q : Rat) :
    evalWiderAtom (.oneOf ls) (.irrational q) = false := by
  apply evalWiderAtom_oneOf_not_mem
  intro hmem
  simp only [oneOfValuesOfAtom] at hmem
  cases hd : decodeLiteralsList ls with
  | none => simp [hd] at hmem
  | some vs =>
    simp only [hd, Option.getD_some] at hmem
    induction ls generalizing vs with
    | nil => cases hd; cases hmem
    | cons l ls ih =>
      simp only [decodeLiteralsList] at hd
      obtain ⟨v, hv, ht⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨ws, hws, he⟩ := Option.map_eq_some_iff.mp ht
      subst vs
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact decodeLiteral_ne_irrational l q hv
      · exact ih ws hws hm

private theorem evalWiderAtom_irrational_iff (a : DataRange) (q : Rat) :
    evalWiderAtom a (.irrational q) = true ↔ a = .datatype literalDatatype ∨
      (DecimalValue q ∧ q.den ≠ 1) ∧ ∃ b, extractIrrationalBounds a = some b ∧ b.contains q := by
  cases a with
  | datatype t =>
    by_cases h : t = literalDatatype
    · subst t; simp [evalWiderAtom]
    · by_cases hr : t = owlReal
      · subst t
        simp [evalWiderAtom, beq_false_of_ne h, checkValue_irrational_iff,
          extractIrrationalBounds, RatBounds.contains, h]
      · simp [evalWiderAtom, beq_false_of_ne h, checkValue_irrational_iff,
          extractIrrationalBounds, h, hr]
  | restriction t fs =>
    by_cases ht : t = owlReal
    · subst t
      simp only [evalWiderAtom, Bool.and_eq_true, checkValue_irrational_iff, true_and,
        List.all_eq_true, reduceCtorEq, false_or, extractIrrationalBounds, ↓reduceIte]
      constructor
      · rintro ⟨hv, hf⟩
        exact ⟨hv, (checkAboveFacets_iff fs {} q hv).mp ⟨⟨trivial, trivial⟩, hf⟩⟩
      · rintro ⟨hv, hb⟩
        exact ⟨hv, ((checkAboveFacets_iff fs {} q hv).mpr hb).2⟩
    · simp [evalWiderAtom, checkValue_irrational_iff, extractIrrationalBounds, ht]
  | oneOf ls => simp [evalWiderAtom_oneOf_irrational, extractIrrationalBounds]
  | _ => simp [evalWiderAtom, extractIrrationalBounds]

private theorem evalWiderPartition_irrational_iff {pos neg : List DataRange} {q : Rat}
    (hvalid : DecimalValue q ∧ q.den ≠ 1)
    (hneg : .datatype literalDatatype ∉ neg)
    (hpos : ∀ a ∈ pos, a = .datatype literalDatatype ∨ (extractIrrationalBounds a).isSome) :
    evalWiderPartition pos neg (.irrational q) = true ↔
      ∃ b ∈ vennIrrationalBounds pos neg, b.contains q := by
  have heval (a : DataRange) : evalWiderAtom a (.irrational q) = true ↔
      a = .datatype literalDatatype ∨ ∃ b, extractIrrationalBounds a = some b ∧ b.contains q := by
    rw [evalWiderAtom_irrational_iff]
    exact or_congr Iff.rfl ⟨And.right, And.intro hvalid⟩
  have hfalse (a : DataRange) : (!evalWiderAtom a (.irrational q)) = true ↔
      ¬ (a = .datatype literalDatatype ∨ ∃ b, extractIrrationalBounds a = some b ∧ b.contains q) := by
    simpa only [Bool.not_eq_true', Bool.eq_false_iff] using not_congr (heval a)
  simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, heval, hfalse, vennIrrationalBounds,
    mem_foldSubtractRatBounds_iff, List.mem_singleton, exists_eq_left,
    foldr_intersect_rat_iff, List.mem_filterMap]
  refine and_congr ?_ ?_
  · constructor
    · intro h b
      rintro ⟨a, ha, hab⟩
      rcases h a ha with rfl | ⟨b', he, hc⟩
      · simp [extractIrrationalBounds, show literalDatatype ≠ owlReal by decide] at hab
      · rw [hab] at he
        cases he
        exact hc
    · intro h a ha
      rcases hpos a ha with hl | he
      · exact .inl hl
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
        exact .inr ⟨b, hb, h b ⟨a, ha, hb⟩⟩
  · constructor
    · rintro h b ⟨a, ha, hb⟩ hc
      exact h a ha (.inr ⟨b, hb, hc⟩)
    · intro h a ha
      rintro (rfl | ⟨b, hb, hc⟩)
      · exact hneg ha
      · exact h b ⟨a, ha, hb⟩ hc

theorem legacy_cover_of_evalWiderPartition {K : Nat} {pos neg : List DataRange}
    (hadm : legacy_widerAtomsAdmissible (pos ++ neg) = true)
    (i : Interpretation datatypeMap)
    {v₀ : Value} (hv₀ : evalWiderPartition pos neg v₀ = true)
    (ha₀ : ∃ a₀ ∈ pos, a₀ ≠ .datatype literalDatatype)
    (hdate : ∀ dt, v₀ ≠ .dateTime dt) :
    K ≤ ((legacy_widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).length ∨
      v₀ ∈ legacy_widerCandidates K pos neg := by
  simp only [legacy_widerAtomsAdmissible, List.all_eq_true, List.mem_append] at hadm
  have hallAtom := hadm
  have hpos : ∀ a ∈ pos, legacy_isWiderExactAtom a = true := fun a ha => hallAtom a (.inl ha)
  have hneg : ∀ a ∈ neg, legacy_isWiderExactAtom a = true := fun a ha => hallAtom a (.inr ha)
  obtain ⟨hposAll, hnegAll⟩ := Bool.and_eq_true_iff.mp hv₀
  have hposEv (a : DataRange) (ha : a ∈ pos) : evalWiderAtom a v₀ = true :=
    List.all_eq_true.mp hposAll a ha
  have hnegEv (a : DataRange) (ha : a ∈ neg) : evalWiderAtom a v₀ = false := by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp hnegAll a ha
  have hnolit (a : DataRange) (ha : a ∈ neg) : a ≠ .datatype literalDatatype := by
    intro rfl; have := hnegEv (.datatype literalDatatype) ha; simp [evalWiderAtom] at this
  by_cases honePos : ∃ ls, DataRange.oneOf ls ∈ pos
  · obtain ⟨ls, hls⟩ := honePos
    have hmem : v₀ ∈ allOneOfValues pos :=
      w_mem_allOneOfValues_of_mem hls (evalWiderAtom_oneOf_mem (hposEv (.oneOf ls) hls))
    refine .inr ?_
    simp only [legacy_widerCandidates, List.mem_append]
    right
    left; left; left; left; left; left; left; left; left; left; left; left; right; left
    exact hmem
  · have hnoOneOfPos (a : DataRange) (ha : a ∈ pos) (ls : List Literal) : a ≠ .oneOf ls :=
      fun h => honePos ⟨ls, h ▸ ha⟩
    obtain ⟨a₀, ha₀Mem, ha₀Ne⟩ := ha₀
    have ha₀Ev := hposEv a₀ ha₀Mem
    cases v₀ with
    | boolean b =>
      refine .inr ?_
      simp only [legacy_widerCandidates, List.mem_append]
      right
      left; left; left; left; left; left; left; left; left; left; left; left; left
      cases b <;> simp
    | float f =>
      have := evalWiderAtom_float_or_double_false (hpos a₀ ha₀Mem) ha₀Ne (hnoOneOfPos a₀ ha₀Mem)
        (.float f) (.inl ⟨f, rfl⟩)
      rw [ha₀Ev] at this; cases this
    | double d =>
      have := evalWiderAtom_float_or_double_false (hpos a₀ ha₀Mem) ha₀Ne (hnoOneOfPos a₀ ha₀Mem)
        (.double d) (.inr ⟨d, rfl⟩)
      rw [ha₀Ev] at this; cases this
    | number q =>
      have hposOnlyNum (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ ∃ k b, extractNumAtom a = some (k, b) ∧ k.holds q ∧ b.contains q := by
        by_cases hlit : a = .datatype literalDatatype
        · exact .inl hlit
        · cases hex : extractNumAtom a with
          | none =>
            have hf := evalWiderAtom_nonNum_number_false (hpos a ha) hlit (hnoOneOfPos a ha) hex q
            rw [hposEv a ha] at hf; cases hf
          | some kb =>
            rcases kb with ⟨k, b⟩
            obtain ⟨q', hq', hkq, hbq⟩ :=
              (evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.number q)).mp (hposEv a ha)
            have := Value.number.inj hq'; subst this
            exact .inr ⟨k, b, rfl, hkq, hbq⟩
      by_cases hden1 : q.den = 1
      · have hqEq : Value.number q = Value.integer q.num := by
          simp only [Value.integer]; congr 1; apply Rat.ext <;> simp [hden1]
        have hevalInt (z : Int) :
            evalWiderPartition pos neg (.integer z) = true ↔
              ∃ b ∈ vennNumIntBounds pos neg, b.contains z := by
          simp only [vennNumIntBounds, mem_foldSubtractBounds_iff, List.mem_singleton,
            exists_eq_left, foldr_intersect_int_iff, List.mem_filterMap, List.mem_flatMap,
            evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
          refine and_congr ?_ ?_
          · constructor
            · intro h b ⟨a, ha, hmap⟩
              cases hex : extractNumAtom a with
              | none => simp [hex] at hmap
              | some kb =>
                rcases kb with ⟨k, rb⟩
                simp only [hex, Option.map_some, Option.some.injEq] at hmap
                subst hmap
                obtain ⟨q', hq', _, hcon⟩ :=
                  (evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.integer z)).mp (h a ha)
                have hqe := Value.number.inj hq'
                rw [← hqe] at hcon
                exact (rb.toIntBounds_iff z).mpr hcon
            · intro h a ha
              rcases hposOnlyNum a ha with rfl | ⟨k, rb, hex, _, _⟩
              · rfl
              · rw [evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.integer z)]
                have hk : k.holds (Rat.ofInt z) := by
                  cases k <;> simp [NumericKind.holds]
                  exact decimalValue_ofInt z
                have hcon : rb.toIntBounds.contains z :=
                  h rb.toIntBounds ⟨a, ha, by simp [hex]⟩
                exact ⟨Rat.ofInt z, rfl, hk, (rb.toIntBounds_iff z).mp hcon⟩
          · constructor
            · intro h b ⟨a, ha, hb⟩
              exact (evalWiderAtom_neg_int_iff (hneg a ha) (hnolit a ha) i z).mp (h a ha) b hb
            · intro h a ha
              exact (evalWiderAtom_neg_int_iff (hneg a ha) (hnolit a ha) i z).mpr fun b hb =>
                h b ⟨a, ha, hb⟩
        let sInts := sampleIntSet K (vennNumIntBounds pos neg)
        by_cases hlt : sInts.length < K
        · have hqIn := (hevalInt q.num).mp (hqEq ▸ hv₀)
          have hmem : q.num ∈ sInts := sampleIntSet_complete_of_lt K _ hlt hqIn
          refine .inr ?_
          rw [hqEq]
          simp only [legacy_widerCandidates, List.mem_append]
          right
          left; left; left; left; left; left; left; left; left; left; left; right
          exact List.mem_map_of_mem hmem
        · refine .inl ?_
          let xs := sInts.map Value.integer
          have hnd : xs.Nodup := w_nodup_map_inj
            (fun h => congrArg Rat.num (Value.number.inj h)) (sampleIntSet_nodup K _)
          have hsub : ∀ x ∈ xs, x ∈ legacy_widerCandidates K pos neg := fun x hx => by
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; left; left; left; left; left; right
            exact hx
          have hall : (xs.filter (evalWiderPartition pos neg)).length = xs.length := by
            have hfeq : xs.filter (evalWiderPartition pos neg) = xs :=
              List.filter_eq_self.mpr fun x hx => by
                obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
                exact (hevalInt z).mpr (sampleIntSet_sound K _ hz)
            rw [hfeq]
          have hle := w_filter_length_le_of_sub_eraseDups xs (legacy_widerCandidates K pos neg)
            (evalWiderPartition pos neg) hnd hsub
          have hlen : xs.length = sInts.length := List.length_map Value.integer
          omega
      · by_cases hdec : DecimalValue q
        · have hevalDec (q' : Rat) (hdec' : DecimalValue q') (hden' : q'.den ≠ 1) :
              evalWiderPartition pos neg (.number q') = true ↔
                ∃ b ∈ vennNumRatBounds .dec pos neg, b.contains q' := by
            simp only [vennNumRatBounds, mem_foldSubtractRatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_rat_iff, List.mem_filterMap, List.mem_flatMap,
              evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
            refine and_congr ?_ ?_
            · constructor
              · intro h b ⟨a, ha, hmap⟩
                cases hex : extractNumAtom a with
                | none => simp [hex] at hmap
                | some kb =>
                  rcases kb with ⟨k, rb⟩
                  simp only [hex, Option.map_some, Option.some.injEq] at hmap
                  subst hmap
                  obtain ⟨q'', hq'', _, hcon⟩ :=
                    (evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.number q')).mp (h a ha)
                  have := Value.number.inj hq''; subst this; exact hcon
              · intro h a ha
                rcases hposOnlyNum a ha with rfl | ⟨k, rb, hex, hkq, _⟩
                · rfl
                · rw [evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.number q')]
                  have hk' : k.holds q' := by
                    cases k
                    · exact (hden1 hkq).elim
                    · exact hdec'
                    · trivial
                  exact ⟨q', rfl, hk', h rb ⟨a, ha, by simp [hex]⟩⟩
            · constructor
              · intro h b ⟨a, ha, hb⟩
                exact (evalWiderAtom_neg_rat_iff (hneg a ha) (hnolit a ha) i (.inl ⟨rfl, hdec', hden'⟩)).mp
                  (h a ha) b hb
              · intro h a ha
                exact (evalWiderAtom_neg_rat_iff (hneg a ha) (hnolit a ha) i (.inl ⟨rfl, hdec', hden'⟩)).mpr
                  fun b hb => h b ⟨a, ha, hb⟩
          let sDecs := sampleProperDecSet K (vennNumRatBounds .dec pos neg)
          by_cases hlt : sDecs.length < K
          · have hqIn := (hevalDec q hdec hden1).mp hv₀
            have hmem : q ∈ sDecs := sampleProperDecSet_complete_of_lt K _ hlt hqIn hdec hden1
            refine .inr ?_
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; left; left; left; left; right
            exact List.mem_map_of_mem hmem
          · refine .inl ?_
            let xs := sDecs.map Value.number
            have hnd : xs.Nodup := w_nodup_map_inj (fun h => Value.number.inj h) (sampleProperDecSet_nodup K _)
            have hsub : ∀ x ∈ xs, x ∈ legacy_widerCandidates K pos neg := fun x hx => by
              simp only [legacy_widerCandidates, List.mem_append]
              right
              left; left; left; left; left; left; left; left; left; left; right
              exact hx
            have hall : (xs.filter (evalWiderPartition pos neg)).length = xs.length := by
              have hfeq : xs.filter (evalWiderPartition pos neg) = xs :=
                List.filter_eq_self.mpr fun x hx => by
                  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
                  obtain ⟨hcon, hdec', hden'⟩ := sampleProperDecSet_sound K _ hq'
                  exact (hevalDec q' hdec' hden').mpr hcon
              rw [hfeq]
            have hle := w_filter_length_le_of_sub_eraseDups xs (legacy_widerCandidates K pos neg)
              (evalWiderPartition pos neg) hnd hsub
            have hlen : xs.length = sDecs.length := List.length_map Value.number
            omega
        · have hevalRat (q' : Rat) (hndec' : ¬ DecimalValue q') :
              evalWiderPartition pos neg (.number q') = true ↔
                ∃ b ∈ vennNumRatBounds .rat pos neg, b.contains q' := by
            simp only [vennNumRatBounds, mem_foldSubtractRatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_rat_iff, List.mem_filterMap, List.mem_flatMap,
              evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
            refine and_congr ?_ ?_
            · constructor
              · intro h b ⟨a, ha, hmap⟩
                cases hex : extractNumAtom a with
                | none => simp [hex] at hmap
                | some kb =>
                  rcases kb with ⟨k, rb⟩
                  simp only [hex, Option.map_some, Option.some.injEq] at hmap
                  subst hmap
                  obtain ⟨q'', hq'', _, hcon⟩ :=
                    (evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.number q')).mp (h a ha)
                  have := Value.number.inj hq''; subst this; exact hcon
              · intro h a ha
                rcases hposOnlyNum a ha with rfl | ⟨k, rb, hex, hkq, _⟩
                · rfl
                · rw [evalWiderAtom_extractNumAtom_iff (hpos a ha) hex i (.number q')]
                  have hk' : k.holds q' := by
                    cases k
                    · exact (hden1 hkq).elim
                    · exact (hdec hkq).elim
                    · trivial
                  exact ⟨q', rfl, hk', h rb ⟨a, ha, by simp [hex]⟩⟩
            · constructor
              · intro h b ⟨a, ha, hb⟩
                exact (evalWiderAtom_neg_rat_iff (hneg a ha) (hnolit a ha) i (.inr ⟨rfl, hndec'⟩)).mp
                  (h a ha) b hb
              · intro h a ha
                exact (evalWiderAtom_neg_rat_iff (hneg a ha) (hnolit a ha) i (.inr ⟨rfl, hndec'⟩)).mpr
                  fun b hb => h b ⟨a, ha, hb⟩
          let sRats := sampleNonDecRatSet K (vennNumRatBounds .rat pos neg)
          by_cases hlt : sRats.length < K
          · have hqIn := (hevalRat q hdec).mp hv₀
            have hmem : q ∈ sRats := sampleNonDecRatSet_complete_of_lt K _ hlt hqIn hdec
            refine .inr ?_
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; left; left; left; right
            exact List.mem_map_of_mem hmem
          · refine .inl ?_
            let xs := sRats.map Value.number
            have hnd : xs.Nodup := w_nodup_map_inj (fun h => Value.number.inj h) (sampleNonDecRatSet_nodup K _)
            have hsub : ∀ x ∈ xs, x ∈ legacy_widerCandidates K pos neg := fun x hx => by
              simp only [legacy_widerCandidates, List.mem_append]
              right
              left; left; left; left; left; left; left; left; left; right
              exact hx
            have hall : (xs.filter (evalWiderPartition pos neg)).length = xs.length := by
              have hfeq : xs.filter (evalWiderPartition pos neg) = xs :=
                List.filter_eq_self.mpr fun x hx => by
                  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
                  obtain ⟨hcon, hndec'⟩ := sampleNonDecRatSet_sound K _ hq'
                  exact (hevalRat q' hndec').mpr hcon
              rw [hfeq]
            have hle := w_filter_length_le_of_sub_eraseDups xs (legacy_widerCandidates K pos neg)
              (evalWiderPartition pos neg) hnd hsub
            have hlen : xs.length = sRats.length := List.length_map Value.number
            omega
    | plainLiteral s lang =>
      by_cases hlang : lang = ""
      · subst hlang
        by_cases hsub : (pos ++ neg).any atomUsesStrSubtype = true
        · let bounds := vennLenBounds extractStrOrPlainLen pos neg
          have hallLen (a : DataRange) (b : NatBounds) (hexact : legacy_isWiderExactAtom a = true)
              (hb : extractStrOrPlainLen a = some b) (s' : String) :
              evalWiderAtom a (Value.string s') = true ↔ b.contains s'.length := by
            have hnolit : a ≠ .datatype literalDatatype := by intro rfl; cases hb
            have hnoone : ∀ ls, a ≠ .oneOf ls := by intro ls rfl; cases hb
            simpa [hb] using evalWiderAtom_string_noSub_iff i hexact (lenAtom_noSubtype hb)
              hnolit hnoone s'
          have hsBounds : ∃ b ∈ bounds, b.contains s.length := by
            simp only [bounds, vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
            refine ⟨fun b ⟨a, ha, hb⟩ => (hallLen a b (hpos a ha) hb s).mp (hposEv a ha), ?_⟩
            intro b ⟨a, ha, hb⟩ hlen
            have he := (hallLen a b (hneg a ha) hb s).mpr hlen
            rw [hnegEv a ha] at he
            cases he
          have heval (s' : String) (hflag : stringSubtypeFlags s' = stringSubtypeFlags s)
              (havoid : Value.string s' ∉ allOneOfValues neg)
              (hmem : ∃ b ∈ bounds, b.contains s'.length) :
              evalWiderPartition pos neg (Value.string s') = true := by
            simp only [bounds, vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hmem
            simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
            constructor
            · intro a ha
              cases hflagA : atomUsesStrSubtype a
              · by_cases hlit : a = .datatype literalDatatype
                · subst a
                  rfl
                · have hlen := evalWiderAtom_string_noSub_iff i (hpos a ha) hflagA hlit
                    (hnoOneOfPos a ha) s
                  obtain ⟨b, hb, _⟩ := hlen.mp (hposEv a ha)
                  exact (hallLen a b (hpos a ha) hb s').mpr (hmem.1 b ⟨a, ha, hb⟩)
              · rw [evalWiderAtom_subtype_eq hflagA hflag]
                exact hposEv a ha
            · intro a ha
              by_cases hone : ∃ ls, a = .oneOf ls
              · obtain ⟨ls, rfl⟩ := hone
                exact evalWiderAtom_oneOf_not_mem fun hm => havoid (w_mem_allOneOfValues_of_mem ha hm)
              cases hflagA : atomUsesStrSubtype a
              · apply Bool.eq_false_iff.mpr
                intro ht
                obtain ⟨b, hb, hlen⟩ := (evalWiderAtom_string_noSub_iff i (hneg a ha) hflagA
                  (hnolit a ha) (fun ls eq => hone ⟨ls, eq⟩) s').mp ht
                exact hmem.2 b ⟨a, ha, hb⟩ hlen
              · rw [evalWiderAtom_subtype_eq hflagA hflag]
                exact hnegEv a ha
          let count := K + (allOneOfValues neg).length
          have hchoose : ∃ c ∈ stringCharacterProfiles, ∀ k,
              stringSubtypeFlags (stratumWitness c k) = stringSubtypeFlags s := by
            have hstrEq (c : Char) (k : Nat)
                (hnorm : isNormalizedString (stratumWitness c k) = isNormalizedString s)
                (htok : isToken (stratumWitness c k) = isToken s)
                (hnm : isNMTOKEN (stratumWitness c k) = isNMTOKEN s)
                (hname : isName (stratumWitness c k) = isName s)
                (hnc : isNCName (stratumWitness c k) = isNCName s)
                (hlang : isLanguageTag (stratumWitness c k) = isLanguageTag s) :
                stringSubtypeFlags (stratumWitness c k) = stringSubtypeFlags s := by
              simp only [stringSubtypeFlags, hnorm, htok, hnm, hname, hnc, hlang]
            by_cases hlang : isLanguageTag s = true
            · refine ⟨'a', by simp [stringCharacterProfiles], fun k => ?_⟩
              have lang : isLanguageTag (stratumWitness 'a' k) = true := by
                simpa [stratumWitness] using isLanguageTag_languageWitness k
              have nc := isNCName_of_isLanguageTag lang
              have name := isName_of_isNCName nc
              have nm := isNMTOKEN_of_isName name
              have tok := isToken_of_isNMTOKEN nm
              have ncS := isNCName_of_isLanguageTag hlang
              have nameS := isName_of_isNCName ncS
              have nmS := isNMTOKEN_of_isName nameS
              have tokS := isToken_of_isNMTOKEN nmS
              exact hstrEq 'a' k ((isNormalizedString_of_isToken tok).trans
                (isNormalizedString_of_isToken tokS).symm) (tok.trans tokS.symm)
                (nm.trans nmS.symm) (name.trans nameS.symm) (nc.trans ncS.symm) (lang.trans hlang.symm)
            · have hlang := Bool.eq_false_iff.mpr hlang
              by_cases hnc : isNCName s = true
              · have hn := isName_of_isNCName hnc
                have hnm := isNMTOKEN_of_isName hn
                have ht := isToken_of_isNMTOKEN hnm
                have hnorm := isNormalizedString_of_isToken ht
                refine ⟨'_', by simp [stringCharacterProfiles], fun k => ?_⟩
                obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_underscore k
                apply hstrEq '_' k
                all_goals simp only [stratumWitness, show '_' ≠ 'a' by decide, ite_false]
                · exact a.trans hnorm.symm
                · exact b.trans ht.symm
                · exact c.trans hnm.symm
                · exact d.trans hn.symm
                · exact e.trans hnc.symm
                · exact (isLanguageTag_false_of_head (c := '_') (by decide)).trans hlang.symm
              · have hnc := Bool.eq_false_iff.mpr hnc
                by_cases hn : isName s = true
                · have hnm := isNMTOKEN_of_isName hn
                  have ht := isToken_of_isNMTOKEN hnm
                  have hnorm := isNormalizedString_of_isToken ht
                  refine ⟨':', by simp [stringCharacterProfiles], fun k => ?_⟩
                  obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_colon k
                  apply hstrEq ':' k
                  all_goals simp only [stratumWitness, show ':' ≠ 'a' by decide, ite_false]
                  · exact a.trans hnorm.symm
                  · exact b.trans ht.symm
                  · exact c.trans hnm.symm
                  · exact d.trans hn.symm
                  · exact e.trans hnc.symm
                  · exact (isLanguageTag_false_of_head (c := ':') (by decide)).trans hlang.symm
                · have hn := Bool.eq_false_iff.mpr hn
                  by_cases hnm : isNMTOKEN s = true
                  · have ht := isToken_of_isNMTOKEN hnm
                    have hnorm := isNormalizedString_of_isToken ht
                    refine ⟨'0', by simp [stringCharacterProfiles], fun k => ?_⟩
                    obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_zero k
                    apply hstrEq '0' k
                    all_goals simp only [stratumWitness, show '0' ≠ 'a' by decide, ite_false]
                    · exact a.trans hnorm.symm
                    · exact b.trans ht.symm
                    · exact c.trans hnm.symm
                    · exact d.trans hn.symm
                    · exact e.trans hnc.symm
                    · exact (isLanguageTag_false_of_head (c := '0') (by decide)).trans hlang.symm
                  · have hnm := Bool.eq_false_iff.mpr hnm
                    by_cases ht : isToken s = true
                    · have hnorm := isNormalizedString_of_isToken ht
                      refine ⟨'!', by simp [stringCharacterProfiles], fun k => ?_⟩
                      obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_bang k
                      apply hstrEq '!' k
                      all_goals simp only [stratumWitness, show '!' ≠ 'a' by decide, ite_false]
                      · exact a.trans hnorm.symm
                      · exact b.trans ht.symm
                      · exact c.trans hnm.symm
                      · exact d.trans hn.symm
                      · exact e.trans hnc.symm
                      · exact (isLanguageTag_false_of_head (c := '!') (by decide)).trans hlang.symm
                    · have ht := Bool.eq_false_iff.mpr ht
                      by_cases hnorm : isNormalizedString s = true
                      · refine ⟨' ', by simp [stringCharacterProfiles], fun k => ?_⟩
                        obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_space k
                        apply hstrEq ' ' k
                        all_goals simp only [stratumWitness, show ' ' ≠ 'a' by decide, ite_false]
                        · exact a.trans hnorm.symm
                        · exact b.trans ht.symm
                        · exact c.trans hnm.symm
                        · exact d.trans hn.symm
                        · exact e.trans hnc.symm
                        · exact (isLanguageTag_false_of_head (c := ' ') (by decide)).trans hlang.symm
                      · have hnorm := Bool.eq_false_iff.mpr hnorm
                        refine ⟨'\t', by simp [stringCharacterProfiles], fun k => ?_⟩
                        obtain ⟨a, b, c, d, e⟩ := stratumStr_flags_tab k
                        apply hstrEq '\t' k
                        all_goals simp only [stratumWitness, show '\t' ≠ 'a' by decide, ite_false]
                        · exact a.trans hnorm.symm
                        · exact b.trans ht.symm
                        · exact c.trans hnm.symm
                        · exact d.trans hn.symm
                        · exact e.trans hnc.symm
                        · exact (isLanguageTag_false_of_head (c := '\t') (by decide)).trans hlang.symm
          let accept := matchesSubtypes pos neg
          have hacceptFlags (t : String) (hflags : stringSubtypeFlags t = stringSubtypeFlags s) :
              accept t = true := by
            simp only [accept, matchesSubtypes, Bool.and_eq_true, List.all_eq_true, List.mem_filter,
              Bool.not_eq_true']
            exact ⟨fun a ha => (evalWiderAtom_subtype_eq ha.2 hflags).trans (hposEv a ha.1),
              fun a ha => (evalWiderAtom_subtype_eq ha.2 hflags).trans (hnegEv a ha.1)⟩
          obtain ⟨c, hc, hflags⟩ := hchoose
          have hcan : stringCharacterProfiles.any (fun c => accept (stratumWitness c 0)) = true :=
            List.any_eq_true.mpr ⟨c, hc, hacceptFlags _ (hflags 0)⟩
          have htier : ((pos ++ neg).any atomUsesStrSubtype &&
              stringCharacterProfiles.any (fun c => accept (stratumWitness c 0))) = true :=
            Bool.and_eq_true_iff.mpr ⟨hsub, hcan⟩
          by_cases hquick : K ≤ (quickSubtypeCandidates K pos neg bounds).length
          · apply Or.inl
            apply Nat.le_trans hquick
            apply StringLengthCells.length_le_of_nodup_subset (nodup_eraseDups_list _)
            intro v hv
            have hholds := (List.mem_filter.mp (List.mem_eraseDups.mp hv)).2
            refine List.mem_filter.mpr ⟨List.mem_eraseDups.mpr ?_, hholds⟩
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; left; right
            rw [ite_eq_left htier, ite_eq_left hquick]
            exact hv
          let count := K + (allOneOfValues neg).length
          have hCandidate (s' : String) (hs' : s' ∈ sampleSubtypeLengths count bounds accept) :
              Value.string s' ∈ legacy_widerCandidates K pos neg := by
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; left; right
            rw [ite_eq_left htier, ite_eq_right hquick]
            exact List.mem_map_of_mem hs'
          obtain ⟨b, hb, hsLength⟩ := hsBounds
          cases upper : b.upper with
          | none =>
            refine .inl (w_bounded_family_ge_K K
              (fun k => Value.string (stratumWitness c (b.lower + k))) (fun _ _ eq => ?_) ?_ ?_)
            · have hEq := stratumWitness_inj c (Value.plainLiteral.inj eq).1
              omega
            · intro v hv
              obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
              apply hCandidate
              rw [sampleSubtypeLengths, List.mem_flatMap]
              refine ⟨b, hb, ?_⟩
              rw [upper, List.mem_flatMap]
              exact ⟨c, hc, List.mem_map_of_mem hk⟩
            · intro k _ havoid
              refine heval _ (hflags _) havoid ⟨b, hb, ?_⟩
              simp only [NatBounds.contains, upper, Option.elim_none, and_true, stratumWitness]
              split
              · rw [languageWitness_length]
                omega
              · rw [stratumStr_length]
                omega
          | some hi =>
            have hlo : b.lower ≤ s.length := hsLength.1
            have hhi : s.length ≤ hi := by simpa [upper] using hsLength.2
            have haccept : accept (String.ofList (s.toList.map stringCharacterProfile)) = true :=
              hacceptFlags _ (by simpa using stringSubtypeFlags_profile s.toList)
            have hm (t : String) (ht : t ∈ StringLengthCells.sample count s.length accept) :
                Value.string t ∈ legacy_widerCandidates K pos neg := by
              apply hCandidate
              rw [sampleSubtypeLengths, List.mem_flatMap]
              refine ⟨b, hb, ?_⟩
              rw [upper, List.mem_flatMap]
              exact ⟨s.length, List.mem_range'.mpr ⟨s.length - b.lower, by omega, by omega⟩, ht⟩
            have hc : s ∈ StringLengthCells.sample count s.length accept ∨
                ∃ ws : List String, ws.Nodup ∧ count ≤ ws.length ∧
                  ∀ t ∈ ws, t ∈ StringLengthCells.sample count s.length accept ∧
                    t.length = s.length ∧ stringSubtypeFlags t = stringSubtypeFlags s := by
              simpa [String.length] using StringLengthCells.sample_cover count s.toList haccept
            rcases hc with hc | ⟨ws, hnd, hcount, hw⟩
            · exact .inr (hm s hc)
            · let vs := ws.map Value.string
              have hvnd : vs.Nodup := hnd.map Value.string (fun _ _ hn eq =>
                hn (Value.plainLiteral.inj eq).1)
              have hge := w_filter_pred_length_ge_of_avoid vs (allOneOfValues neg)
                (evalWiderPartition pos neg) hvnd fun x hx havoid => by
                  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                  obtain ⟨_, hl, hf⟩ := hw t ht
                  exact heval t hf havoid ⟨b, hb, hl.symm ▸ hsLength⟩
              have hle := w_filter_length_le_of_sub_eraseDups vs (legacy_widerCandidates K pos neg)
                (evalWiderPartition pos neg) hvnd fun x hx => by
                  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                  exact hm t (hw t ht).1
              have hvl : vs.length = ws.length := List.length_map ..
              exact .inl (by dsimp [count] at hcount; omega)
        · have hnoSub : ∀ a ∈ pos ++ neg, atomUsesStrSubtype a = false := fun a ha => by
            cases h : atomUsesStrSubtype a
            · rfl
            · exact (hsub (List.any_eq_true.mpr ⟨a, ha, h⟩)).elim
          have hposOnlySP (a : DataRange) (ha : a ∈ pos) :
              a = .datatype literalDatatype ∨ ∃ b, extractStrOrPlainLen a = some b := by
            by_cases hlit : a = .datatype literalDatatype
            · exact .inl hlit
            · obtain ⟨b, hb, _⟩ :=
                (evalWiderAtom_string_noSub_iff i (hpos a ha) (hnoSub a (List.mem_append_left _ ha))
                  hlit (hnoOneOfPos a ha) s).mp (hposEv a ha)
              exact .inr ⟨b, hb⟩
          have hevalStr (s' : String) (hnb : Value.string s' ∉ allOneOfValues neg)
              (hb' : ∃ b ∈ vennLenBounds extractStrOrPlainLen pos neg, b.contains s'.length) :
              evalWiderPartition pos neg (Value.string s') = true := by
            simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hb'
            simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
            refine ⟨fun a ha => ?_, fun a ha => ?_⟩
            · rcases hposOnlySP a ha with rfl | ⟨b, hb⟩
              · rfl
              · exact (evalWiderAtom_string_noSub_iff i (hpos a ha) (hnoSub a (List.mem_append_left _ ha))
                  (by intro rfl; cases hb) (hnoOneOfPos a ha) s').mpr ⟨b, hb, hb'.1 b ⟨a, ha, hb⟩⟩
            · by_cases h1 : ∃ ls, a = .oneOf ls
              · obtain ⟨ls, rfl⟩ := h1
                exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
              · cases he : evalWiderAtom a (Value.string s')
                · rfl
                · obtain ⟨b, hb, hcon⟩ :=
                    (evalWiderAtom_string_noSub_iff i (hneg a ha) (hnoSub a (List.mem_append_right _ ha))
                      (hnolit a ha) (fun ls h => h1 ⟨ls, h⟩) s').mp he
                  exact (hb'.2 b ⟨a, ha, hb⟩ hcon).elim
          have hs₀In : ∃ b ∈ vennLenBounds extractStrOrPlainLen pos neg, b.contains s.length := by
            simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
            refine ⟨fun b ⟨a, ha, hb⟩ => ?_, fun b ⟨a, ha, hb⟩ hcon => ?_⟩
            · obtain ⟨b', hb', hcon⟩ :=
                (evalWiderAtom_string_noSub_iff i (hpos a ha) (hnoSub a (List.mem_append_left _ ha))
                  (by intro rfl; cases hb) (hnoOneOfPos a ha) s).mp (hposEv a ha)
              rw [hb] at hb'; cases hb'; exact hcon
            · have he := (evalWiderAtom_string_noSub_iff i (hneg a ha) (hnoSub a (List.mem_append_right _ ha))
                (hnolit a ha) (by intro ls rfl; cases hb) s).mpr ⟨b, hb, hcon⟩
              rw [hnegEv a ha] at he; cases he
          exact sampleLenStrings_cover
            Value.string (fun h => (Value.plainLiteral.inj h).1)
            (fun s' hs' => by
              simp only [legacy_widerCandidates, List.mem_append]
              right
              left; left; left; left; left; left; left; left; right
              exact List.mem_map_of_mem hs')
            hevalStr hs₀In
      · have hposOnlyPL (a : DataRange) (ha : a ∈ pos) :
            a = .datatype literalDatatype ∨ ∃ b, extractLenOf (rdf "PlainLiteral") a = some b := by
          by_cases hlit : a = .datatype literalDatatype
          · exact .inl hlit
          · obtain ⟨b, hb, _⟩ :=
              (evalWiderAtom_plainLiteral_lang_iff i (hpos a ha) hlit (hnoOneOfPos a ha) s lang hlang).mp
                (hposEv a ha)
            exact .inr ⟨b, hb⟩
        have hs₀In : ∃ b ∈ vennLenBounds (extractLenOf (rdf "PlainLiteral")) pos neg, b.contains s.length := by
          simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
            exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
          refine ⟨fun b ⟨a, ha, hb⟩ => ?_, fun b ⟨a, ha, hb⟩ hcon => ?_⟩
          · obtain ⟨b', hb', hcon⟩ :=
              (evalWiderAtom_plainLiteral_lang_iff i (hpos a ha) (by intro rfl; cases hb)
                (hnoOneOfPos a ha) s lang hlang).mp (hposEv a ha)
            rw [hb] at hb'; cases hb'; exact hcon
          · have he := (evalWiderAtom_plainLiteral_lang_iff i (hneg a ha) (hnolit a ha)
              (by intro ls rfl; cases hb) s lang hlang).mpr ⟨b, hb, hcon⟩
            rw [hnegEv a ha] at he; cases he
        obtain ⟨b, hbMem, hbCon⟩ := hs₀In
        have hbloCon : b.contains b.lower := by
          refine ⟨Nat.le_refl _, ?_⟩
          cases hup : b.upper with
          | none => trivial
          | some hi =>
            have h1 := hbCon.1
            have h2 : s.length ≤ hi := by simpa [hup] using hbCon.2
            simp only [Option.elim_some]; omega
        refine .inl (w_bounded_family_ge_K K
          (fun k => Value.plainLiteral (String.ofList (List.replicate b.lower 'a'))
            (String.ofList (List.replicate (k + 1) 'e')))
          (fun _ _ h => by
            have hl := congrArg String.length (Value.plainLiteral.inj h).2
            simp [String.length] at hl; omega)
          (fun x hx => by
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
            simp only [legacy_widerCandidates, List.mem_append]
            right
            left; left; left; left; left; left; right
            rw [List.mem_flatMap]
            exact ⟨b, hbMem, List.mem_map_of_mem hk⟩)
          (fun k _ hnb => by
            have hlne : String.ofList (List.replicate (k + 1) 'e') ≠ "" := by
              intro h; have := congrArg String.length h; simp [String.length] at this
            have hb' : ∃ b' ∈ vennLenBounds (extractLenOf (rdf "PlainLiteral")) pos neg,
                b'.contains (String.ofList (List.replicate b.lower 'a')).length :=
              ⟨b, hbMem, by simpa [String.length] using hbloCon⟩
            simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
              exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hb'
            simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
            refine ⟨fun a ha => ?_, fun a ha => ?_⟩
            · rcases hposOnlyPL a ha with rfl | ⟨b', hb'eq⟩
              · rfl
              · exact (evalWiderAtom_plainLiteral_lang_iff i (hpos a ha) (by intro rfl; cases hb'eq)
                  (hnoOneOfPos a ha) _ _ hlne).mpr ⟨b', hb'eq, hb'.1 b' ⟨a, ha, hb'eq⟩⟩
            · by_cases h1 : ∃ ls, a = .oneOf ls
              · obtain ⟨ls, rfl⟩ := h1
                exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
              · cases he : evalWiderAtom a _
                · rfl
                · obtain ⟨b', hb'eq, hcon⟩ :=
                    (evalWiderAtom_plainLiteral_lang_iff i (hneg a ha) (hnolit a ha)
                      (fun ls h => h1 ⟨ls, h⟩) _ _ hlne).mp he
                  exact (hb'.2 b' ⟨a, ha, hb'eq⟩ hcon).elim))
    | anyURI s =>
      have hposOnlyU (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ ∃ b, extractLenOf (xsd "anyURI") a = some b := by
        by_cases hlit : a = .datatype literalDatatype
        · exact .inl hlit
        · obtain ⟨b, hb, _⟩ := (evalWiderAtom_anyURI_iff i (hpos a ha) hlit (hnoOneOfPos a ha) s).mp (hposEv a ha)
          exact .inr ⟨b, hb⟩
      have hevalU (s' : String) (hnb : Value.anyURI s' ∉ allOneOfValues neg)
          (hb' : ∃ b ∈ vennLenBounds (extractLenOf (xsd "anyURI")) pos neg, b.contains s'.length) :
          evalWiderPartition pos neg (.anyURI s') = true := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hb'
        simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
        refine ⟨fun a ha => ?_, fun a ha => ?_⟩
        · rcases hposOnlyU a ha with rfl | ⟨b, hb⟩
          · rfl
          · exact (evalWiderAtom_anyURI_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) s').mpr
              ⟨b, hb, hb'.1 b ⟨a, ha, hb⟩⟩
        · by_cases h1 : ∃ ls, a = .oneOf ls
          · obtain ⟨ls, rfl⟩ := h1
            exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
          · cases he : evalWiderAtom a (.anyURI s')
            · rfl
            · obtain ⟨b, hb, hcon⟩ :=
                (evalWiderAtom_anyURI_iff i (hneg a ha) (hnolit a ha) (fun ls h => h1 ⟨ls, h⟩) s').mp he
              exact (hb'.2 b ⟨a, ha, hb⟩ hcon).elim
      have hs₀In : ∃ b ∈ vennLenBounds (extractLenOf (xsd "anyURI")) pos neg, b.contains s.length := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
        refine ⟨fun b ⟨a, ha, hb⟩ => ?_, fun b ⟨a, ha, hb⟩ hcon => ?_⟩
        · obtain ⟨b', hb', hcon⟩ :=
            (evalWiderAtom_anyURI_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) s).mp (hposEv a ha)
          rw [hb] at hb'; cases hb'; exact hcon
        · have he := (evalWiderAtom_anyURI_iff i (hneg a ha) (hnolit a ha) (by intro ls rfl; cases hb) s).mpr ⟨b, hb, hcon⟩
          rw [hnegEv a ha] at he; cases he
      exact sampleLenStrings_cover
        Value.anyURI (fun h => Value.anyURI.inj h)
        (fun s' hs' => by
          simp only [legacy_widerCandidates, List.mem_append]
          right
          left; left; left; left; left; right
          exact List.mem_map_of_mem hs')
        hevalU hs₀In
    | xmlLiteral s =>
      have hs : checkCanonicalXMLLiteral s = true := by
        have hwa := hpos a₀ ha₀Mem
        cases a₀ with
        | datatype t =>
          have hne : t ≠ literalDatatype := fun h => ha₀Ne (congrArg DataRange.datatype h)
          simp only [evalWiderAtom, beq_false_of_ne hne] at ha₀Ev
          simp only [legacy_isWiderExactAtom, Bool.or_eq_true, beq_iff_eq] at hwa
          rcases hwa with (((((((((rfl | rfl) | hnum) | hstr) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
          · exact (hne rfl).elim
          · cases ha₀Ev
          · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
            rw [checkValue_numericBase_false hb (fun _ h => by cases h)] at ha₀Ev; cases ha₀Ev
          · obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp hstr
            rw [checkValue_strTier_false ht (fun _ _ h => by cases h)] at ha₀Ev; cases ha₀Ev
          · cases ha₀Ev
          · obtain ⟨s', hs', heq⟩ := (valueSpace_xmlLiteral_iff _).mp ((checkValue_iff _ _).mp ha₀Ev)
            cases heq; exact hs'
          · cases ha₀Ev
          · cases ha₀Ev
          · cases ha₀Ev
          · cases ha₀Ev
        | restriction t fs =>
          simp only [legacy_isWiderExactAtom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hwa
          have hf : checkValue t (.xmlLiteral s) = false := by
            rcases hwa with ⟨hnum, _⟩ | ⟨ht, _⟩
            · obtain ⟨⟨_, _⟩, hb⟩ := Option.isSome_iff_exists.mp hnum
              exact checkValue_numericBase_false hb (fun _ h => by cases h)
            · rcases ht with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl
          simp [evalWiderAtom, hf] at ha₀Ev
        | oneOf ls => exact (hnoOneOfPos _ ha₀Mem ls rfl).elim
        | _ => cases hwa
      refine .inl (w_bounded_family_ge_K K
        (fun k => Value.xmlLiteral (String.ofList (List.replicate k 'a')))
        (fun _ _ h => by
          have hl := congrArg String.length (Value.xmlLiteral.inj h)
          simp [String.length] at hl; exact hl)
        (fun x hx => by
          simp only [legacy_widerCandidates, List.mem_append]
          right
          left; left; left; left; right; exact hx)
        (fun k _ hnb => by
          simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
          refine ⟨fun a ha => ?_, fun a ha => ?_⟩
          · rw [evalWiderAtom_xmlLiteral_eq (hpos a ha) (hnoOneOfPos a ha)
              (checkCanonicalXMLLiteral_replicate_a k) hs]; exact hposEv a ha
          · by_cases h1 : ∃ ls, a = .oneOf ls
            · obtain ⟨ls, rfl⟩ := h1
              exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
            · rw [evalWiderAtom_xmlLiteral_eq (hneg a ha) (fun ls h => h1 ⟨ls, h⟩)
                (checkCanonicalXMLLiteral_replicate_a k) hs]; exact hnegEv a ha))
    | hexBinary bs =>
      have hposOnlyH (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ ∃ b, extractLenOf (xsd "hexBinary") a = some b := by
        by_cases hlit : a = .datatype literalDatatype
        · exact .inl hlit
        · obtain ⟨b, hb, _⟩ := (evalWiderAtom_hexBinary_iff i (hpos a ha) hlit (hnoOneOfPos a ha) bs).mp (hposEv a ha)
          exact .inr ⟨b, hb⟩
      have hevalH (bs' : List UInt8) (hnb : Value.hexBinary bs' ∉ allOneOfValues neg)
          (hb' : ∃ b ∈ vennLenBounds (extractLenOf (xsd "hexBinary")) pos neg, b.contains bs'.length) :
          evalWiderPartition pos neg (.hexBinary bs') = true := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hb'
        simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
        refine ⟨fun a ha => ?_, fun a ha => ?_⟩
        · rcases hposOnlyH a ha with rfl | ⟨b, hb⟩
          · rfl
          · exact (evalWiderAtom_hexBinary_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) bs').mpr
              ⟨b, hb, hb'.1 b ⟨a, ha, hb⟩⟩
        · by_cases h1 : ∃ ls, a = .oneOf ls
          · obtain ⟨ls, rfl⟩ := h1
            exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
          · cases he : evalWiderAtom a (.hexBinary bs')
            · rfl
            · obtain ⟨b, hb, hcon⟩ :=
                (evalWiderAtom_hexBinary_iff i (hneg a ha) (hnolit a ha) (fun ls h => h1 ⟨ls, h⟩) bs').mp he
              exact (hb'.2 b ⟨a, ha, hb⟩ hcon).elim
      have hbs₀In : ∃ b ∈ vennLenBounds (extractLenOf (xsd "hexBinary")) pos neg, b.contains bs.length := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
        refine ⟨fun b ⟨a, ha, hb⟩ => ?_, fun b ⟨a, ha, hb⟩ hcon => ?_⟩
        · obtain ⟨b', hb', hcon⟩ :=
            (evalWiderAtom_hexBinary_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) bs).mp (hposEv a ha)
          rw [hb] at hb'; cases hb'; exact hcon
        · have he := (evalWiderAtom_hexBinary_iff i (hneg a ha) (hnolit a ha) (by intro ls rfl; cases hb) bs).mpr ⟨b, hb, hcon⟩
          rw [hnegEv a ha] at he; cases he
      exact sampleWordBounds_cover BoundedWords.bytes 0
        Value.hexBinary (fun h => Value.hexBinary.inj h)
        (fun bs' hbs' => by
          simp only [legacy_widerCandidates, List.mem_append]
          right
          left; left; left; right
          exact List.mem_map_of_mem hbs')
        hevalH hbs₀In
    | base64Binary bs =>
      have hposOnlyB (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ ∃ b, extractLenOf (xsd "base64Binary") a = some b := by
        by_cases hlit : a = .datatype literalDatatype
        · exact .inl hlit
        · obtain ⟨b, hb, _⟩ := (evalWiderAtom_base64Binary_iff i (hpos a ha) hlit (hnoOneOfPos a ha) bs).mp (hposEv a ha)
          exact .inr ⟨b, hb⟩
      have hevalB (bs' : List UInt8) (hnb : Value.base64Binary bs' ∉ allOneOfValues neg)
          (hb' : ∃ b ∈ vennLenBounds (extractLenOf (xsd "base64Binary")) pos neg, b.contains bs'.length) :
          evalWiderPartition pos neg (.base64Binary bs') = true := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap] at hb'
        simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
        refine ⟨fun a ha => ?_, fun a ha => ?_⟩
        · rcases hposOnlyB a ha with rfl | ⟨b, hb⟩
          · rfl
          · exact (evalWiderAtom_base64Binary_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) bs').mpr
              ⟨b, hb, hb'.1 b ⟨a, ha, hb⟩⟩
        · by_cases h1 : ∃ ls, a = .oneOf ls
          · obtain ⟨ls, rfl⟩ := h1
            exact evalWiderAtom_oneOf_not_mem fun hm => hnb (w_mem_allOneOfValues_of_mem ha hm)
          · cases he : evalWiderAtom a (.base64Binary bs')
            · rfl
            · obtain ⟨b, hb, hcon⟩ :=
                (evalWiderAtom_base64Binary_iff i (hneg a ha) (hnolit a ha) (fun ls h => h1 ⟨ls, h⟩) bs').mp he
              exact (hb'.2 b ⟨a, ha, hb⟩ hcon).elim
      have hbs₀In : ∃ b ∈ vennLenBounds (extractLenOf (xsd "base64Binary")) pos neg, b.contains bs.length := by
        simp only [vennLenBounds, mem_foldSubtractNatBounds_iff, List.mem_singleton,
          exists_eq_left, foldr_intersect_nat_iff, List.mem_filterMap]
        refine ⟨fun b ⟨a, ha, hb⟩ => ?_, fun b ⟨a, ha, hb⟩ hcon => ?_⟩
        · obtain ⟨b', hb', hcon⟩ :=
            (evalWiderAtom_base64Binary_iff i (hpos a ha) (by intro rfl; cases hb) (hnoOneOfPos a ha) bs).mp (hposEv a ha)
          rw [hb] at hb'; cases hb'; exact hcon
        · have he := (evalWiderAtom_base64Binary_iff i (hneg a ha) (hnolit a ha) (by intro ls rfl; cases hb) bs).mpr ⟨b, hb, hcon⟩
          rw [hnegEv a ha] at he; cases he
      exact sampleWordBounds_cover BoundedWords.bytes 0
        Value.base64Binary (fun h => Value.base64Binary.inj h)
        (fun bs' hbs' => by
          simp only [legacy_widerCandidates, List.mem_append]
          right
          left; left; right
          exact List.mem_map_of_mem hbs')
        hevalB hbs₀In
    | dateTime dt => exact (hdate dt rfl).elim
    | irrational q =>
      have hvalid : DecimalValue q ∧ q.den ≠ 1 := by
        rcases (evalWiderAtom_irrational_iff a₀ q).mp ha₀Ev with hl | h
        · exact (ha₀Ne hl).elim
        · exact h.1
      have hp (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ (extractIrrationalBounds a).isSome := by
        rcases (evalWiderAtom_irrational_iff a q).mp (hposEv a ha) with hl | ⟨_, b, hb, _⟩
        · exact .inl hl
        · exact .inr (Option.isSome_iff_exists.mpr ⟨b, hb⟩)
      have hn : .datatype literalDatatype ∉ neg := fun he => hnolit _ he rfl
      let bs := vennIrrationalBounds pos neg
      let samples := sampleProperDecSet K bs
      by_cases hlt : samples.length < K
      · have hq := (evalWiderPartition_irrational_iff hvalid hn hp).mp hv₀
        have hm := sampleProperDecSet_complete_of_lt K bs hlt hq hvalid.1 hvalid.2
        exact .inr (List.mem_append_left _ (List.mem_map_of_mem hm))
      · let xs := samples.map Value.irrational
        have hnd : xs.Nodup := w_nodup_map_inj Value.irrational.inj (sampleProperDecSet_nodup K bs)
        have hsub : ∀ x ∈ xs, x ∈ legacy_widerCandidates K pos neg := fun x hx => List.mem_append_left _ hx
        have hfilter : xs.filter (evalWiderPartition pos neg) = xs := List.filter_eq_self.mpr fun x hx => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hb, hd, hi⟩ := sampleProperDecSet_sound K bs hr
          exact (evalWiderPartition_irrational_iff ⟨hd, hi⟩ hn hp).mpr hb
        have hle := w_filter_length_le_of_sub_eraseDups xs (legacy_widerCandidates K pos neg)
          (evalWiderPartition pos neg) hnd hsub
        rw [hfilter] at hle
        have hlen : xs.length = samples.length := List.length_map ..
        exact .inl (by omega)

def observationInterpretation : Interpretation datatypeMap where
  Object := Unit
  objectNonempty := inferInstance
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes t _ := t = thing
  objectProperties t _ _ := t = topObjectProperty
  dataProperties t _ _ := t = topDataProperty
  individuals _ := ()
  datatypes t y := t = literalDatatype ∨ ∃ v, valueSpace t v ∧ some v = y
  literalValue := decodeLiteral
  lexicalAgreement _ _ h := h
  named _ := True
  namedIndividual _ := trivial
  thingExt _ := rfl
  nothingExt _ := by decide
  topObjectExt _ _ := rfl
  bottomObjectExt _ _ := by decide
  topDataExt _ _ := rfl
  bottomDataExt _ _ := by decide
  literalDatatypeExt _ := Or.inl rfl
  datatypeAgreement t ht _ := by
    have hn : t ≠ literalDatatype := fun h => datatypeMap.literal_not_builtin (h ▸ ht)
    simp [hn]; exact Iff.rfl

end Sabrina.OWL2.SROIQD.Termination.WiderData
