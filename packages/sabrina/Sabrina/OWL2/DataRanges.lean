import Sabrina.OWL2.Datatypes

/-! Compile closed data ranges to membership tests on decoded values. -/

namespace Sabrina.OWL2.DataRanges

open Datatypes

private structure ValueTest (p : Interpretation datatypeMap → Value → Prop) where
  test : Value → Bool
  correct : ∀ i v, test v = true ↔ p i v

abbrev Compiled (r : DataRange) :=
  ValueTest fun i v => dataHolds i (i.embedValue v) r

private def compileDatatype (t : IRI) :
    Option (ValueTest fun i v => i.datatypes t (i.embedValue v)) :=
  if h : t = literalDatatype then
    some ⟨fun _ => true, by
      intro i v
      exact ⟨fun _ => h.symm ▸ i.literalDatatypeExt _, fun _ => rfl⟩⟩
  else if h : supportedDatatype t = true then
    some ⟨checkValue t, by
      intro i v
      rw [checkValue_iff, i.datatypeAgreement t h]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩⟩
  else none

private def compileEnumeration : (ls : List Literal) →
    Option (ValueTest fun i v => ∃ l ∈ ls, i.literalValue l = i.embedValue v)
  | [] => some ⟨fun _ => false, by simp⟩
  | l :: ls => do
    let tail ← compileEnumeration ls
    match h : decodeLiteral l with
    | none => none
    | some w =>
      return ⟨fun v => decide (w = v) || tail.test v, by
        intro i v
        simp only [Bool.or_eq_true, decide_eq_true_eq,
          List.mem_cons, exists_eq_or_imp, i.lexicalAgreement l w h]
        exact or_congr ⟨congrArg i.embedValue, i.embedValue_injective⟩ (tail.correct i v)⟩

private def compileFacets (t : IRI) : (fs : List Facet) →
    Option (ValueTest fun i v => ∀ f ∈ fs, facetHolds i t f (i.embedValue v))
  | [] => some ⟨fun _ => true, by simp⟩
  | f :: fs => do
    let tail ← compileFacets t fs
    match h : decodeLiteral f.bound with
    | none => none
    | some bound =>
      if checkApplicableFacet t f.name bound then
        return ⟨fun v => checkFacet t f.name bound v && tail.test v, by
          intro i v
          simp only [Bool.and_eq_true, tail.correct i v, List.forall_mem_cons,
            facetHolds_iff_check i t f bound v h]⟩
      else none

def compile : (r : DataRange) → Option (Compiled r)
  | .datatype t => compileDatatype t
  | .complement r => do
    let body ← compile r
    return ⟨fun v => !body.test v, by
      intro i v
      simp [dataHolds, ← body.correct i v]⟩
  | .intersection r s => do
    let left ← compile r
    let right ← compile s
    return ⟨fun v => left.test v && right.test v, by
      intro i v
      rw [Bool.and_eq_true]
      exact and_congr (left.correct i v) (right.correct i v)⟩
  | .union r s => do
    let left ← compile r
    let right ← compile s
    return ⟨fun v => left.test v || right.test v, by
      intro i v
      rw [Bool.or_eq_true]
      exact or_congr (left.correct i v) (right.correct i v)⟩
  | .oneOf ls => compileEnumeration ls
  | .restriction t fs => do
    let base ← compileDatatype t
    let facets ← compileFacets t fs
    if supportedDatatype t then
      return ⟨fun v => base.test v && facets.test v, by
        intro i v
        rw [Bool.and_eq_true]
        exact and_congr (base.correct i v) (facets.correct i v)⟩
    else none

def Compiled.holds (c : Compiled r) (v : Value) : Bool := c.test v

theorem Compiled.holds_iff (c : Compiled r) (i : Interpretation datatypeMap) (v : Value) :
    c.holds v = true ↔ dataHolds i (i.embedValue v) r :=
  c.correct i v

/-- A closed integer interval `xsd:integer[minInclusive lower, maxInclusive upper]`
    with decoded integer bounds. -/
structure ClosedIntInterval (r : DataRange) where
  lower : Int
  upper : Int
  compiled : Compiled r
  member_bounds : ∀ (i : Interpretation datatypeMap) (y : i.Data),
    dataHolds i y r → ∃ z : Int, lower ≤ z ∧ z ≤ upper ∧ i.embedValue (.integer z) = y

private def decodeIntBound (l : Literal) : Option Int :=
  match decodeLiteral l with
  | some (.number q) => if q.den = 1 then some q.num else none
  | _ => none

private theorem decodeIntBound_eq {l : Literal} {n : Int}
    (h : decodeIntBound l = some n) : decodeLiteral l = some (.integer n) := by
  unfold decodeIntBound at h
  cases hd : decodeLiteral l with
  | none => simp [hd] at h
  | some v =>
    cases v with
    | number q =>
      simp only [hd] at h
      split at h
      · rename_i hden
        cases h
        have hq : Rat.ofInt q.num = q := by
          apply Rat.ext <;> simp [hden]
        simp only [Value.integer]
        congr 2
        exact hq.symm
      · cases h
    | _ => simp [hd] at h

private theorem ofInt_le_ofInt {a b : Int} (h : Rat.ofInt a ≤ Rat.ofInt b) : a ≤ b := by
  simpa [Rat.le_iff] using h

private theorem ofInt_lt_ofInt {a b : Int} (h : Rat.ofInt a < Rat.ofInt b) : a < b := by
  simpa [Rat.lt_iff] using h

/-- An integer-valued data range with sound lower/upper bounds across every
    data domain extending `datatypeMap`. -/
structure IntInterval (r : DataRange) where
  bounds : IntegerBounds
  compiled : Compiled r
  member_bounds : ∀ (i : Interpretation datatypeMap) (y : i.Data),
    dataHolds i y r → ∃ z : Int, bounds.contains z ∧ i.embedValue (.integer z) = y

private def facetBounds (f : Facet) : Option IntegerBounds :=
  match orderFacet f.name, decodeIntBound f.bound with
  | some .minInclusive, some b => some { lower := some b }
  | some .maxInclusive, some b => some { upper := some b }
  | some .minExclusive, some b => some { lower := some (b + 1) }
  | some .maxExclusive, some b => some { upper := some (b - 1) }
  | _, _ => none

private theorem facetBounds_sound {t : IRI} {f : Facet} {fb : IntegerBounds}
    (hfb : facetBounds f = some fb) {i : Interpretation datatypeMap} {z : Int}
    (hf : facetHolds i t f (i.embedValue (.integer z))) : fb.contains z := by
  unfold facetBounds at hfb
  cases ho : orderFacet f.name with
  | none => simp [ho] at hfb
  | some ord =>
    cases hb : decodeIntBound f.bound with
    | none => simp [ho, hb] at hfb
    | some b =>
      have hl : decodeLiteral f.bound = some (.integer b) := decodeIntBound_eq hb
      have hcheck := (facetHolds_iff_check i t f (.integer b) (.integer z) hl).mp hf
      have hspace := (checkFacet_iff t f.name (.integer b) (.integer z)).mp hcheck
      obtain ⟨_, ord', hord', hholds⟩ := hspace
      have heq : ord' = ord := Option.some.inj (hord'.symm.trans ho)
      subst heq
      cases ord' <;> simp only [ho, hb, Option.some.injEq] at hfb <;> subst hfb
      · exact ⟨ofInt_le_ofInt hholds, trivial⟩
      · exact ⟨trivial, ofInt_le_ofInt hholds⟩
      · have hlt := ofInt_lt_ofInt hholds; exact ⟨show b + 1 ≤ z by omega, trivial⟩
      · have hlt := ofInt_lt_ofInt hholds; exact ⟨trivial, show z ≤ b - 1 by omega⟩

private def foldFacetBounds (acc : IntegerBounds) : List Facet → Option IntegerBounds
  | [] => some acc
  | f :: fs => do
    let fb ← facetBounds f
    foldFacetBounds (acc.intersect fb) fs

private theorem foldFacetBounds_sound {t : IRI} {fs : List Facet} {acc res : IntegerBounds}
    (hfold : foldFacetBounds acc fs = some res) {i : Interpretation datatypeMap} {z : Int}
    (hacc : acc.contains z) (hfs : ∀ f ∈ fs, facetHolds i t f (i.embedValue (.integer z))) :
    res.contains z := by
  induction fs generalizing acc with
  | nil =>
    cases hfold
    exact hacc
  | cons f tail ih =>
    simp only [foldFacetBounds] at hfold
    obtain ⟨fb, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    have hcur : (acc.intersect fb).contains z :=
      (IntegerBounds.contains_intersect acc fb z).mpr
        ⟨hacc, facetBounds_sound hfb (hfs f (List.mem_cons_self ..))⟩
    exact ih htail hcur (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

private theorem integerSubtype_member_embedded {t : IRI} {bounds : IntegerBounds}
    (ht : integerBounds t = some bounds) {i : Interpretation datatypeMap} {y : i.Data}
    (hy : i.datatypes t y) : ∃ z : Int, bounds.contains z ∧ i.embedValue (.integer z) = y := by
  have hsup : datatypeMap.builtin t := integerBounds_supported ht
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy
  obtain ⟨z, hz, rfl⟩ := (valueSpace_integerSubtype_iff ht v).mp hv
  exact ⟨z, hz, rfl⟩

/-- Compile any integer datatype, order-facet restriction over an integer subtype,
    or intersection thereof into a sound `IntInterval`. -/
def compileIntInterval : (r : DataRange) → Option (IntInterval r)
  | .datatype t =>
    match ht : integerBounds t, compile (.datatype t) with
    | some base, some compiled =>
      some ⟨base, compiled, fun i y hy => integerSubtype_member_embedded ht hy⟩
    | _, _ => none
  | .restriction t fs =>
    match ht : integerBounds t, compile (.restriction t fs) with
    | some base, some compiled =>
      match hfold : foldFacetBounds base fs with
      | some bounds =>
        some ⟨bounds, compiled, by
          intro i y hy
          obtain ⟨z, hz, rfl⟩ := integerSubtype_member_embedded ht hy.1
          exact ⟨z, foldFacetBounds_sound hfold hz hy.2, rfl⟩⟩
      | none => none
    | _, _ => none
  | .intersection a b =>
    match compileIntInterval a, compileIntInterval b, compile (.intersection a b) with
    | some ia, some ib, some compiled =>
      some ⟨ia.bounds.intersect ib.bounds, compiled, by
        intro i y hy
        obtain ⟨za, hza, hya⟩ := ia.member_bounds i y hy.1
        obtain ⟨zb, hzb, hyb⟩ := ib.member_bounds i y hy.2
        have heq : Value.integer za = Value.integer zb := i.embedValue_injective (hya.trans hyb.symm)
        have hzeq : za = zb := by
          have hrat : Rat.ofInt za = Rat.ofInt zb := Value.number.inj heq
          exact congrArg Rat.num hrat
        subst hzeq
        exact ⟨za, (IntegerBounds.contains_intersect _ _ _).mpr ⟨hza, hzb⟩, hya⟩⟩
    | _, _, _ => none
  | _ => none

theorem IntInterval.empty_sound {r : DataRange} (interval : IntInterval r)
    {lo hi : Int} (hlo : interval.bounds.lower = some lo) (hhi : interval.bounds.upper = some hi)
    (hlt : hi < lo) (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ dataHolds i y r := by
  intro hy
  obtain ⟨z, hz, _⟩ := interval.member_bounds i y hy
  simp only [IntegerBounds.contains, hlo, hhi, Option.elim] at hz
  omega

theorem IntInterval.disjoint_sound {r1 r2 : DataRange}
    (i1 : IntInterval r1) (i2 : IntInterval r2) {lo hi : Int}
    (hlo : (i1.bounds.intersect i2.bounds).lower = some lo)
    (hhi : (i1.bounds.intersect i2.bounds).upper = some hi)
    (hlt : hi < lo) (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ (dataHolds i y r1 ∧ dataHolds i y r2) := by
  rintro ⟨h1, h2⟩
  obtain ⟨z1, hz1, hy1⟩ := i1.member_bounds i y h1
  obtain ⟨z2, hz2, hy2⟩ := i2.member_bounds i y h2
  have hzeq : z1 = z2 := by
    have heq : Value.integer z1 = Value.integer z2 := i.embedValue_injective (hy1.trans hy2.symm)
    exact congrArg Rat.num (Value.number.inj heq)
  subst hzeq
  have hinter := (IntegerBounds.contains_intersect i1.bounds i2.bounds z1).mpr ⟨hz1, hz2⟩
  simp only [IntegerBounds.contains, hlo, hhi, Option.elim] at hinter
  omega

/-- A rational/decimal order bound, either inclusive or exclusive. -/
structure RatBound where
  value : Rat
  inclusive : Bool
  deriving DecidableEq, Repr

structure RatBounds where
  lower : Option RatBound := none
  upper : Option RatBound := none
  deriving DecidableEq, Repr

def RatBounds.contains (b : RatBounds) (q : Rat) : Prop :=
  (match b.lower with
   | none => True
   | some lb => if lb.inclusive then lb.value ≤ q else lb.value < q) ∧
  (match b.upper with
   | none => True
   | some ub => if ub.inclusive then q ≤ ub.value else q < ub.value)

private def maxLowerBound (a b : RatBound) : RatBound :=
  if a.value < b.value then b
  else if b.value < a.value then a
  else ⟨a.value, a.inclusive && b.inclusive⟩

private def minUpperBound (a b : RatBound) : RatBound :=
  if a.value < b.value then a
  else if b.value < a.value then b
  else ⟨a.value, a.inclusive && b.inclusive⟩

def RatBounds.intersect (a b : RatBounds) : RatBounds :=
  { lower := match a.lower, b.lower with
      | none, y => y
      | x, none => x
      | some x, some y => some (maxLowerBound x y),
    upper := match a.upper, b.upper with
      | none, y => y
      | x, none => x
      | some x, some y => some (minUpperBound x y) }

private theorem rat_eq_of_not_lt {a b : Rat} (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  Rat.le_antisymm (Rat.not_lt.mp h2) (Rat.not_lt.mp h1)

theorem RatBounds.contains_intersect_of {a b : RatBounds} {q : Rat}
    (ha : a.contains q) (hb : b.contains q) : (a.intersect b).contains q := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  rcases ha with ⟨hal, hau⟩
  rcases hb with ⟨hbl, hbu⟩
  constructor
  · cases al with
    | none => exact hbl
    | some x =>
      cases bl with
      | none => exact hal
      | some y =>
        simp only [RatBounds.intersect, maxLowerBound]
        split
        · exact hbl
        · split
          · exact hal
          · rename_i h1 h2
            have heq : x.value = y.value := rat_eq_of_not_lt h1 h2
            cases hx : x.inclusive <;> cases hy : y.inclusive <;>
              simp [hx, hy] at hal hbl ⊢
            · exact hal
            · exact hal
            · exact heq.symm ▸ hbl
            · exact hal
  · cases au with
    | none => exact hbu
    | some x =>
      cases bu with
      | none => exact hau
      | some y =>
        simp only [RatBounds.intersect, minUpperBound]
        split
        · exact hau
        · split
          · exact hbu
          · rename_i h1 h2
            have heq : x.value = y.value := rat_eq_of_not_lt h1 h2
            cases hx : x.inclusive <;> cases hy : y.inclusive <;>
              simp [hx, hy] at hau hbu ⊢
            · exact hau
            · exact hau
            · exact heq.symm ▸ hbu
            · exact hau

def RatBounds.isEmpty (b : RatBounds) (decimalOnly : Bool) : Bool :=
  match b.lower, b.upper with
  | some lb, some ub =>
    if ub.value < lb.value then true
    else if lb.value == ub.value then
      !(lb.inclusive && ub.inclusive) || (decimalOnly && !checkDecimalValue lb.value)
    else false
  | _, _ => false

theorem RatBounds.isEmpty_sound {b : RatBounds} {decimalOnly : Bool}
    (he : b.isEmpty decimalOnly = true) {q : Rat}
    (hdec : decimalOnly = true → DecimalValue q) (hc : b.contains q) : False := by
  unfold RatBounds.isEmpty at he
  cases hl : b.lower with
  | none => simp [hl] at he
  | some lb =>
    cases hu : b.upper with
    | none => simp [hl, hu] at he
    | some ub =>
      simp only [hl, hu] at he
      rcases hc with ⟨hcl, hcu⟩
      simp only [hl, hu] at hcl hcu
      have hlo : lb.value ≤ q := by
        cases hli : lb.inclusive <;> simp [hli] at hcl
        · exact Rat.le_of_lt hcl
        · exact hcl
      have hhi : q ≤ ub.value := by
        cases hui : ub.inclusive <;> simp [hui] at hcu
        · exact Rat.le_of_lt hcu
        · exact hcu
      split at he
      · rename_i hlt
        exact Rat.not_lt.mpr (Rat.le_trans hlo hhi) hlt
      · split at he
        · rename_i _ hbeq
          have hveq : lb.value = ub.value := beq_iff_eq.mp hbeq
          have hqeq : q = lb.value := Rat.le_antisymm (hveq ▸ hhi) hlo
          rw [← hveq] at hcu
          rw [hqeq] at hcl hcu hdec
          simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
            Bool.and_eq_true] at he
          rcases he with (hli | hui) | ⟨hd, hnd⟩
          · simp [hli] at hcl
          · simp [hui] at hcu
          · have hcheck := (checkDecimalValue_iff lb.value).mpr (hdec hd)
            rw [hcheck] at hnd
            contradiction
        · contradiction

/-- A rational/decimal data range with sound order bounds across every data domain. -/
structure RatInterval (r : DataRange) where
  decimalOnly : Bool
  bounds : RatBounds
  compiled : Compiled r
  member_bounds : ∀ (i : Interpretation datatypeMap) (y : i.Data),
    dataHolds i y r → ∃ q : Rat, (decimalOnly = true → DecimalValue q) ∧
      bounds.contains q ∧ i.embedValue (.number q) = y

private def ratFacetBounds (f : Facet) : Option RatBounds :=
  match orderFacet f.name, decodeLiteral f.bound with
  | some .minInclusive, some (.number b) => some { lower := some ⟨b, true⟩ }
  | some .maxInclusive, some (.number b) => some { upper := some ⟨b, true⟩ }
  | some .minExclusive, some (.number b) => some { lower := some ⟨b, false⟩ }
  | some .maxExclusive, some (.number b) => some { upper := some ⟨b, false⟩ }
  | _, _ => none

private theorem ratFacetBounds_sound {t : IRI} {f : Facet} {fb : RatBounds}
    (hfb : ratFacetBounds f = some fb) {i : Interpretation datatypeMap} {q : Rat}
    (hf : facetHolds i t f (i.embedValue (.number q))) : fb.contains q := by
  unfold ratFacetBounds at hfb
  cases ho : orderFacet f.name with
  | none => simp [ho] at hfb
  | some ord =>
    cases hb : decodeLiteral f.bound with
    | none => simp [ho, hb] at hfb
    | some bv =>
      cases bv with
      | number b =>
        have hcheck := (facetHolds_iff_check i t f (.number b) (.number q) hb).mp hf
        have hspace := (checkFacet_iff t f.name (.number b) (.number q)).mp hcheck
        obtain ⟨_, ord', hord', hholds⟩ := hspace
        have heq : ord' = ord := Option.some.inj (hord'.symm.trans ho)
        subst heq
        cases ord' <;> simp only [ho, hb, Option.some.injEq] at hfb <;> subst hfb
        · exact ⟨hholds, trivial⟩
        · exact ⟨trivial, hholds⟩
        · exact ⟨hholds, trivial⟩
        · exact ⟨trivial, hholds⟩
      | _ => simp [ho, hb] at hfb

private def foldRatFacetBounds (acc : RatBounds) : List Facet → Option RatBounds
  | [] => some acc
  | f :: fs => do
    let fb ← ratFacetBounds f
    foldRatFacetBounds (acc.intersect fb) fs

private theorem foldRatFacetBounds_sound {t : IRI} {fs : List Facet} {acc res : RatBounds}
    (hfold : foldRatFacetBounds acc fs = some res) {i : Interpretation datatypeMap} {q : Rat}
    (hacc : acc.contains q) (hfs : ∀ f ∈ fs, facetHolds i t f (i.embedValue (.number q))) :
    res.contains q := by
  induction fs generalizing acc with
  | nil =>
    cases hfold
    exact hacc
  | cons f tail ih =>
    simp only [foldRatFacetBounds] at hfold
    obtain ⟨fb, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    have hcur := RatBounds.contains_intersect_of hacc
      (ratFacetBounds_sound hfb (hfs f (List.mem_cons_self ..)))
    exact ih htail hcur (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

private theorem decimal_member_embedded {i : Interpretation datatypeMap} {y : i.Data}
    (hy : i.datatypes (xsd "decimal") y) :
    ∃ q : Rat, DecimalValue q ∧ i.embedValue (.number q) = y := by
  have hsup : datatypeMap.builtin (xsd "decimal") :=
    (show supportedDatatype (xsd "decimal") = true by decide)
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement (xsd "decimal") hsup y).mp hy
  obtain ⟨q, hq, rfl⟩ := (valueSpace_decimal_iff v).mp hv
  exact ⟨q, hq, rfl⟩

private theorem rational_member_embedded {i : Interpretation datatypeMap} {y : i.Data}
    (hy : i.datatypes owlRational y) :
    ∃ q : Rat, i.embedValue (.number q) = y := by
  have hsup : datatypeMap.builtin owlRational :=
    (show supportedDatatype owlRational = true by decide)
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement owlRational hsup y).mp hy
  obtain ⟨q, rfl⟩ := (valueSpace_rational_iff v).mp hv
  exact ⟨q, rfl⟩

/-- Compile `xsd:decimal` or `owl:rational` (with order facets and intersections)
    into a sound `RatInterval`. -/
def compileRatInterval : (r : DataRange) → Option (RatInterval r)
  | .datatype t =>
    if ht : t = xsd "decimal" then
      match compile (.datatype t) with
      | some compiled =>
        some ⟨true, {}, compiled, by
          intro i y hy
          subst ht
          obtain ⟨q, hq, rfl⟩ := decimal_member_embedded hy
          exact ⟨q, fun _ => hq, ⟨trivial, trivial⟩, rfl⟩⟩
      | none => none
    else if ht' : t = owlRational then
      match compile (.datatype t) with
      | some compiled =>
        some ⟨false, {}, compiled, by
          intro i y hy
          subst ht'
          obtain ⟨q, rfl⟩ := rational_member_embedded hy
          exact ⟨q, (fun h => by cases h), ⟨trivial, trivial⟩, rfl⟩⟩
      | none => none
    else none
  | .restriction t fs =>
    if ht : t = xsd "decimal" then
      match compile (.restriction t fs), hfold : foldRatFacetBounds {} fs with
      | some compiled, some bounds =>
        some ⟨true, bounds, compiled, by
          intro i y hy
          subst ht
          obtain ⟨q, hq, rfl⟩ := decimal_member_embedded hy.1
          exact ⟨q, fun _ => hq, foldRatFacetBounds_sound hfold ⟨trivial, trivial⟩ hy.2, rfl⟩⟩
      | _, _ => none
    else if ht' : t = owlRational then
      match compile (.restriction t fs), hfold : foldRatFacetBounds {} fs with
      | some compiled, some bounds =>
        some ⟨false, bounds, compiled, by
          intro i y hy
          subst ht'
          obtain ⟨q, rfl⟩ := rational_member_embedded hy.1
          exact ⟨q, (fun h => by cases h),
            foldRatFacetBounds_sound hfold ⟨trivial, trivial⟩ hy.2, rfl⟩⟩
      | _, _ => none
    else none
  | .intersection a b =>
    match compileRatInterval a, compileRatInterval b, compile (.intersection a b) with
    | some ia, some ib, some compiled =>
      some ⟨ia.decimalOnly || ib.decimalOnly, ia.bounds.intersect ib.bounds, compiled, by
        intro i y hy
        obtain ⟨qa, hda, hba, hya⟩ := ia.member_bounds i y hy.1
        obtain ⟨qb, hdb, hbb, hyb⟩ := ib.member_bounds i y hy.2
        have hqeq : qa = qb := Value.number.inj (i.embedValue_injective (hya.trans hyb.symm))
        subst hqeq
        refine ⟨qa, ?_, RatBounds.contains_intersect_of hba hbb, hya⟩
        intro hd
        rcases Bool.or_eq_true_iff.mp hd with h1 | h2
        · exact hda h1
        · exact hdb h2⟩
    | _, _, _ => none
  | _ => none

theorem RatInterval.empty_sound {r : DataRange} (interval : RatInterval r)
    (he : interval.bounds.isEmpty interval.decimalOnly = true)
    (i : Interpretation datatypeMap) (y : i.Data) : ¬ dataHolds i y r := by
  intro hy
  obtain ⟨q, hdec, hq, _⟩ := interval.member_bounds i y hy
  exact RatBounds.isEmpty_sound he hdec hq

/-- A data range whose members across every interpretation are drawn from a finite
    list of decoded values (e.g. `xsd:boolean`, `oneOf`, bounded integer intervals,
    and intersections thereof). -/
structure FiniteDomain (r : DataRange) where
  values : List Value
  compiled : Compiled r
  member_in : ∀ (i : Interpretation datatypeMap) (y : i.Data),
    dataHolds i y r → ∃ v ∈ values, i.embedValue v = y

private def decodeAllLiterals : List Literal → Option (List Value)
  | [] => some []
  | l :: ls => do
    let v ← decodeLiteral l
    let rest ← decodeAllLiterals ls
    return v :: rest

private theorem decodeAllLiterals_mem {ls : List Literal} {vs : List Value}
    (h : decodeAllLiterals ls = some vs) {l : Literal} (hl : l ∈ ls) :
    ∃ v ∈ vs, decodeLiteral l = some v := by
  induction ls generalizing vs with
  | nil => cases hl
  | cons a tail ih =>
    simp only [decodeAllLiterals] at h
    obtain ⟨va, hva, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vt, hvt, hcons⟩ := Option.bind_eq_some_iff.mp hrest
    cases hcons
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨va, List.mem_cons_self .., hva⟩
    · obtain ⟨v, hv, hdv⟩ := ih hvt hl'
      exact ⟨v, List.mem_cons_of_mem _ hv, hdv⟩

def compileFiniteDomain : (r : DataRange) → Option (FiniteDomain r)
  | .datatype t =>
    if ht : t = xsd "boolean" then
      match compile (.datatype t) with
      | some compiled =>
        some ⟨[.boolean false, .boolean true], compiled, by
          intro i y hy
          subst ht
          have hsup : datatypeMap.builtin (xsd "boolean") :=
            (show supportedDatatype (xsd "boolean") = true by decide)
          obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement (xsd "boolean") hsup y).mp hy
          obtain ⟨b, rfl⟩ := (valueSpace_boolean_iff v).mp hv
          cases b <;> exact ⟨_, by simp, rfl⟩⟩
      | none => none
    else none
  | .oneOf ls =>
    match hdec : decodeAllLiterals ls, compile (.oneOf ls) with
    | some vs, some compiled =>
      some ⟨vs.eraseDups, compiled, by
        intro i y hy
        obtain ⟨l, hl, rfl⟩ := hy
        obtain ⟨v, hv, hdv⟩ := decodeAllLiterals_mem hdec hl
        exact ⟨v, List.mem_eraseDups.mpr hv, (i.lexicalAgreement l v hdv).symm⟩⟩
    | _, _ => none
  | .intersection a b =>
    match compileFiniteDomain a, compile b, compile (.intersection a b) with
    | some fa, some cb, some compiled =>
      some ⟨fa.values.filter cb.holds, compiled, by
        intro i y hy
        obtain ⟨v, hv, rfl⟩ := fa.member_in i y hy.1
        have hcb := (cb.holds_iff i v).mpr hy.2
        exact ⟨v, List.mem_filter.mpr ⟨hv, hcb⟩, rfl⟩⟩
    | _, _, _ =>
      match compile a, compileFiniteDomain b, compile (.intersection a b) with
      | some ca, some fb, some compiled =>
        some ⟨fb.values.filter ca.holds, compiled, by
          intro i y hy
          obtain ⟨v, hv, rfl⟩ := fb.member_in i y hy.2
          have hca := (ca.holds_iff i v).mpr hy.1
          exact ⟨v, List.mem_filter.mpr ⟨hv, hca⟩, rfl⟩⟩
      | _, _, _ => none
  | .union a b =>
    match compileFiniteDomain a, compileFiniteDomain b, compile (.union a b) with
    | some fa, some fb, some compiled =>
      some ⟨(fa.values ++ fb.values).eraseDups, compiled, by
        intro i y hy
        rcases hy with ha | hb
        · obtain ⟨v, hv, rfl⟩ := fa.member_in i y ha
          exact ⟨v, List.mem_eraseDups.mpr (List.mem_append_left _ hv), rfl⟩
        · obtain ⟨v, hv, rfl⟩ := fb.member_in i y hb
          exact ⟨v, List.mem_eraseDups.mpr (List.mem_append_right _ hv), rfl⟩⟩
    | _, _, _ => none
  | _ => none

/-- Length bounds on `xsd:string` values. -/
structure StringLengthBounds where
  minLen : Nat := 0
  maxLen : Option Nat := none
  deriving DecidableEq, Repr

def StringLengthBounds.contains (b : StringLengthBounds) (s : String) : Prop :=
  b.minLen ≤ s.length ∧ b.maxLen.elim True (s.length ≤ ·)

def StringLengthBounds.intersect (a b : StringLengthBounds) : StringLengthBounds :=
  { minLen := max a.minLen b.minLen,
    maxLen := match a.maxLen, b.maxLen with
      | none, y => y
      | x, none => x
      | some x, some y => some (min x y) }

theorem StringLengthBounds.contains_intersect (a b : StringLengthBounds) (s : String) :
    (a.intersect b).contains s ↔ a.contains s ∧ b.contains s := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp [StringLengthBounds.intersect, StringLengthBounds.contains] <;> omega

def StringLengthBounds.isEmpty (b : StringLengthBounds) : Bool :=
  match b.maxLen with
  | some hi => decide (hi < b.minLen)
  | none => false

theorem StringLengthBounds.isEmpty_sound {b : StringLengthBounds}
    (he : b.isEmpty = true) {s : String} (hc : b.contains s) : False := by
  unfold StringLengthBounds.isEmpty at he
  cases hu : b.maxLen with
  | none => simp [hu] at he
  | some hi =>
    simp only [hu] at he
    have hlt : hi < b.minLen := of_decide_eq_true he
    simp only [StringLengthBounds.contains, hu, Option.elim] at hc
    omega

structure StringInterval (r : DataRange) where
  bounds : StringLengthBounds
  compiled : Compiled r
  member_bounds : ∀ (i : Interpretation datatypeMap) (y : i.Data),
    dataHolds i y r → ∃ s : String, bounds.contains s ∧ i.embedValue (.string s) = y

private def decodeNatBound (l : Literal) : Option Nat :=
  match decodeLiteral l with
  | some (.number q) => if q.den = 1 ∧ 0 ≤ q.num then some q.num.toNat else none
  | _ => none

private theorem decodeNatBound_eq {l : Literal} {n : Nat}
    (h : decodeNatBound l = some n) : decodeLiteral l = some (.integer (n : Int)) := by
  unfold decodeNatBound at h
  cases hd : decodeLiteral l with
  | none => simp [hd] at h
  | some v =>
    cases v with
    | number q =>
      simp only [hd] at h
      split at h
      · rename_i hcond
        cases h
        have hq : Rat.ofInt (q.num.toNat : Int) = q := by
          apply Rat.ext
          · simp; omega
          · simp [hcond.1]
        simp only [Value.integer]
        congr 2
        exact hq.symm
      · cases h
    | _ => simp [hd] at h

private def stringFacetBounds (f : Facet) : Option StringLengthBounds :=
  if f.name == xsd "pattern" then some {}
  else match lengthFacet f.name, decodeNatBound f.bound with
    | some .length, some n => some { minLen := n, maxLen := some n }
    | some .minLength, some n => some { minLen := n }
    | some .maxLength, some n => some { maxLen := some n }
    | _, _ => none

private theorem stringFacetBounds_sound {t : IRI} {f : Facet} {fb : StringLengthBounds}
    (hfb : stringFacetBounds f = some fb) {i : Interpretation datatypeMap} {s : String}
    (hf : facetHolds i t f (i.embedValue (.string s))) : fb.contains s := by
  unfold stringFacetBounds at hfb
  split at hfb
  · cases hfb
    exact ⟨Nat.zero_le _, trivial⟩
  · cases ho : lengthFacet f.name with
    | none => simp [ho] at hfb
    | some lf =>
      cases hb : decodeNatBound f.bound with
      | none => simp [ho, hb] at hfb
      | some n =>
        have hl : decodeLiteral f.bound = some (.integer (n : Int)) := decodeNatBound_eq hb
        have hcheck := (facetHolds_iff_check i t f (.integer (n : Int)) (.string s) hl).mp hf
        have hspace := (checkFacet_iff t f.name (.integer (n : Int)) (.string s)).mp hcheck
        obtain ⟨_, _, _, lf', hlf', hholds⟩ := hspace
        have heq : lf' = lf := Option.some.inj (hlf'.symm.trans ho)
        subst heq
        have hnum : (Rat.ofInt (n : Int)).num.toNat = n := by simp
        rw [hnum] at hholds
        cases lf' <;> simp only [ho, hb, Option.some.injEq] at hfb <;> subst hfb
        · exact ⟨show n ≤ s.length by simp [LengthFacet.holds] at hholds; omega,
            show s.length ≤ n by simp [LengthFacet.holds] at hholds; omega⟩
        · exact ⟨hholds, trivial⟩
        · exact ⟨Nat.zero_le _, hholds⟩

private def foldStringFacetBounds (acc : StringLengthBounds) : List Facet → Option StringLengthBounds
  | [] => some acc
  | f :: fs => do
    let fb ← stringFacetBounds f
    foldStringFacetBounds (acc.intersect fb) fs

private theorem foldStringFacetBounds_sound {t : IRI} {fs : List Facet}
    {acc res : StringLengthBounds} (hfold : foldStringFacetBounds acc fs = some res)
    {i : Interpretation datatypeMap} {s : String} (hacc : acc.contains s)
    (hfs : ∀ f ∈ fs, facetHolds i t f (i.embedValue (.string s))) : res.contains s := by
  induction fs generalizing acc with
  | nil => cases hfold; exact hacc
  | cons f tail ih =>
    simp only [foldStringFacetBounds] at hfold
    obtain ⟨fb, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    have hcur := (StringLengthBounds.contains_intersect acc fb s).mpr
      ⟨hacc, stringFacetBounds_sound hfb (hfs f (List.mem_cons_self ..))⟩
    exact ih htail hcur (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

private theorem string_member_embedded {i : Interpretation datatypeMap} {y : i.Data}
    (hy : i.datatypes (xsd "string") y) : ∃ s : String, i.embedValue (.string s) = y := by
  have hsup : datatypeMap.builtin (xsd "string") :=
    (show supportedDatatype (xsd "string") = true by decide)
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement (xsd "string") hsup y).mp hy
  obtain ⟨s, rfl⟩ := (valueSpace_string_iff v).mp hv
  exact ⟨s, rfl⟩

def compileStringInterval : (r : DataRange) → Option (StringInterval r)
  | .datatype t =>
    if ht : t = xsd "string" then
      match compile (.datatype t) with
      | some compiled =>
        some ⟨{}, compiled, by
          intro i y hy
          subst ht
          obtain ⟨s, rfl⟩ := string_member_embedded hy
          exact ⟨s, ⟨Nat.zero_le _, trivial⟩, rfl⟩⟩
      | none => none
    else none
  | .restriction t fs =>
    if ht : t = xsd "string" then
      match compile (.restriction t fs), hfold : foldStringFacetBounds {} fs with
      | some compiled, some bounds =>
        some ⟨bounds, compiled, by
          intro i y hy
          subst ht
          obtain ⟨s, rfl⟩ := string_member_embedded hy.1
          exact ⟨s, foldStringFacetBounds_sound hfold ⟨Nat.zero_le _, trivial⟩ hy.2, rfl⟩⟩
      | _, _ => none
    else none
  | .intersection a b =>
    match compileStringInterval a, compileStringInterval b, compile (.intersection a b) with
    | some ia, some ib, some compiled =>
      some ⟨ia.bounds.intersect ib.bounds, compiled, by
        intro i y hy
        obtain ⟨sa, hsa, hya⟩ := ia.member_bounds i y hy.1
        obtain ⟨sb, hsb, hyb⟩ := ib.member_bounds i y hy.2
        have hseq : sa = sb := (Value.plainLiteral.inj (i.embedValue_injective (hya.trans hyb.symm))).1
        subst hseq
        exact ⟨sa, (StringLengthBounds.contains_intersect _ _ _).mpr ⟨hsa, hsb⟩, hya⟩⟩
    | _, _, _ => none
  | _ => none

theorem StringInterval.empty_sound {r : DataRange} (interval : StringInterval r)
    (he : interval.bounds.isEmpty = true) (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ dataHolds i y r := by
  intro hy
  obtain ⟨s, hs, _⟩ := interval.member_bounds i y hy
  exact StringLengthBounds.isEmpty_sound he hs

/-- Unified range descriptor for existential and cardinality reasoning over the
    supported Boolean, integer, decimal, rational, and string datatype map. -/
inductive SolvedRange (r : DataRange) where
  | intInterval (interval : IntInterval r)
  | ratInterval (interval : RatInterval r)
  | stringInterval (interval : StringInterval r)
  | finite (domain : FiniteDomain r)

def SolvedRange.compiled : SolvedRange r → Compiled r
  | .intInterval i => i.compiled
  | .ratInterval i => i.compiled
  | .stringInterval i => i.compiled
  | .finite f => f.compiled

def compileBaseSolvedRange (r : DataRange) : Option (SolvedRange r) :=
  match compileFiniteDomain r with
  | some f => some (.finite f)
  | none =>
    match compileIntInterval r with
    | some i => some (.intInterval i)
    | none =>
      match compileRatInterval r with
      | some i => some (.ratInterval i)
      | none => (compileStringInterval r).map .stringInterval

/-- Extract an upper-bounding finite list of decoded values when a solved range is
    provably finite (e.g. `xsd:boolean`, `oneOf`, bounded integer intervals, or empty). -/
def SolvedRange.finiteValues? : SolvedRange r → Option (List Value)
  | .finite f => some f.values.eraseDups
  | .intInterval i =>
    match i.bounds.lower, i.bounds.upper with
    | some lo, some hi =>
      if hi < lo then some []
      else some ((List.range ((hi - lo).toNat + 1)).map fun (k : Nat) => Value.integer (lo + (k : Int)))
    | _, _ => none
  | .ratInterval i =>
    if i.bounds.isEmpty i.decimalOnly then some [] else none
  | .stringInterval i =>
    if i.bounds.isEmpty then some []
    else if i.bounds.maxLen == some 0 then some [.string ""]
    else none

theorem SolvedRange.finiteValues?_sound {r : DataRange} (sr : SolvedRange r) {vs : List Value}
    (hvs : sr.finiteValues? = some vs) (i : Interpretation datatypeMap) (y : i.Data)
    (hy : dataHolds i y r) : ∃ v ∈ vs, i.embedValue v = y := by
  cases sr with
  | finite f =>
    simp only [SolvedRange.finiteValues?, Option.some.injEq] at hvs
    subst hvs
    obtain ⟨v, hv, rfl⟩ := f.member_in i y hy
    exact ⟨v, List.mem_eraseDups.mpr hv, rfl⟩
  | intInterval iv =>
    simp only [SolvedRange.finiteValues?] at hvs
    cases hlo : iv.bounds.lower with
    | none => simp [hlo] at hvs
    | some lo =>
      cases hhi : iv.bounds.upper with
      | none => simp [hlo, hhi] at hvs
      | some hi =>
        simp only [hlo, hhi] at hvs
        split at hvs
        · rename_i hlt
          exact False.elim (iv.empty_sound hlo hhi hlt i y hy)
        · cases hvs
          obtain ⟨z, hz, rfl⟩ := iv.member_bounds i y hy
          simp only [IntegerBounds.contains, hlo, hhi, Option.elim] at hz
          refine ⟨.integer z, ?_, rfl⟩
          rw [List.mem_map]
          refine ⟨(z - lo).toNat, ?_, ?_⟩
          · rw [List.mem_range]; omega
          · congr 1; omega
  | ratInterval rv =>
    simp only [SolvedRange.finiteValues?] at hvs
    split at hvs
    · rename_i he
      exact False.elim (rv.empty_sound he i y hy)
    · cases hvs
  | stringInterval sv =>
    simp only [SolvedRange.finiteValues?] at hvs
    split at hvs
    · rename_i he
      exact False.elim (sv.empty_sound he i y hy)
    · split at hvs
      · rename_i _ hmax0
        cases hvs
        obtain ⟨s, hs, rfl⟩ := sv.member_bounds i y hy
        have hmax : sv.bounds.maxLen = some 0 := beq_iff_eq.mp hmax0
        simp only [StringLengthBounds.contains, hmax, Option.elim] at hs
        have hempty : s = "" := String.length_eq_zero_iff.mp (by omega)
        subst hempty
        exact ⟨.string "", List.mem_singleton_self _, rfl⟩
      · cases hvs

def SolvedRange.isEmpty : SolvedRange r → Bool
  | .finite f => f.values.isEmpty
  | .intInterval iv =>
    match iv.bounds.lower, iv.bounds.upper with
    | some lo, some hi => decide (hi < lo)
    | _, _ => false
  | .ratInterval rv => rv.bounds.isEmpty rv.decimalOnly
  | .stringInterval sv => sv.bounds.isEmpty

theorem SolvedRange.isEmpty_sound {r : DataRange} (sr : SolvedRange r)
    (h : sr.isEmpty = true) (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ dataHolds i y r := by
  cases sr with
  | finite f =>
    intro hy
    obtain ⟨v, hv, _⟩ := f.member_in i y hy
    cases hval : f.values with
    | nil => simp [hval] at hv
    | cons _ _ => simp [SolvedRange.isEmpty, hval] at h
  | intInterval iv =>
    simp only [SolvedRange.isEmpty] at h
    cases hlo : iv.bounds.lower with
    | none => simp [hlo] at h
    | some lo =>
      cases hhi : iv.bounds.upper with
      | none => simp [hlo, hhi] at h
      | some hi =>
        simp only [hlo, hhi] at h
        exact iv.empty_sound hlo hhi (of_decide_eq_true h) i y
  | ratInterval rv =>
    exact rv.empty_sound h i y
  | stringInterval sv =>
    exact sv.empty_sound h i y

private theorem emptyEnumeration_iff {r : DataRange}
    (h : ∀ (i : Interpretation datatypeMap) (y : i.Data), ¬ dataHolds i y r)
    (i : Interpretation datatypeMap) (y : i.Data) :
    dataHolds i y (.oneOf []) ↔ dataHolds i y r := by
  simp [dataHolds, h i y]

private def lowerSmallRestriction (t : IRI) (fs : List Facet) :
    { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y r ↔ dataHolds i y (.restriction t fs) } :=
  let source := DataRange.restriction t fs
  match compileBaseSolvedRange source with
  | none => ⟨source, fun _ _ => Iff.rfl⟩
  | some solved =>
    if empty : solved.isEmpty = true then
      ⟨.oneOf [], emptyEnumeration_iff (solved.isEmpty_sound empty)⟩
    else
      match solved with
      | .stringInterval interval =>
        if upper : interval.bounds.maxLen = some 0 then
          if accepted : interval.compiled.holds (.string "") = true then
            let l : Literal := ⟨"", xsd "string"⟩
            ⟨.oneOf [l], fun i y => by
              have hdecode : decodeLiteral l = some (.string "") := by decide
              simp only [dataHolds, List.mem_singleton, exists_eq_left,
                i.lexicalAgreement l (.string "") hdecode]
              refine ⟨fun he => ?_, fun hy => ?_⟩
              · rw [← he]
                exact (interval.compiled.holds_iff i (.string "")).mp accepted
              · obtain ⟨s, hs, he⟩ := interval.member_bounds i y hy
                simp only [StringLengthBounds.contains, upper, Option.elim] at hs
                have : s = "" := String.length_eq_zero_iff.mp (by omega)
                simpa [this] using he⟩
          else ⟨.oneOf [], emptyEnumeration_iff fun i y hy => by
              obtain ⟨s, hs, rfl⟩ := interval.member_bounds i y hy
              simp only [StringLengthBounds.contains, upper, Option.elim] at hs
              have : s = "" := String.length_eq_zero_iff.mp (by omega)
              subst s
              exact accepted ((interval.compiled.holds_iff i (.string "")).mpr hy)⟩
        else ⟨source, fun _ _ => Iff.rfl⟩
      | _ => ⟨source, fun _ _ => Iff.rfl⟩

def isNumericLengthFacet (f : Facet) : Bool :=
  (lengthFacet f.name).isSome && (decodeNatBound f.bound).isSome

/-- A length restriction on a string subtype is the intersection of the subtype
and the same length restriction on `xsd:string` in every interpretation. -/
theorem stringSubtypeLengthRestriction_iff {t : IRI} {fs : List Facet}
    (ht : isStringSubtype t = true) (hfs : fs.all isNumericLengthFacet = true)
    (i : Interpretation datatypeMap) (y : i.Data) :
    dataHolds i y (.intersection (.datatype t) (.restriction (xsd "string") fs)) ↔
      dataHolds i y (.restriction t fs) := by
  simp only [dataHolds]
  have transfer (hy : i.datatypes t y) :
      i.datatypes (xsd "string") y ∧
        ∀ f ∈ fs, facetHolds i (xsd "string") f y ↔ facetHolds i t f y := by
    obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement t (isStringSubtype_builtin ht) y).mp hy
    have hstr := valueSpace_string_of_subtype ht hv
    refine ⟨(i.datatypeAgreement (xsd "string") rfl _).mpr ⟨v, hstr, rfl⟩, ?_⟩
    obtain ⟨s, rfl⟩ := (valueSpace_string_iff v).mp hstr
    change valueSpace t (.string s) at hv
    intro f hf
    have hfacet := List.all_eq_true.mp hfs f hf
    simp only [isNumericLengthFacet, Bool.and_eq_true] at hfacet
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hfacet.2
    have hl := decodeNatBound_eq hn
    rw [facetHolds_iff_check i (xsd "string") f _ _ hl,
      facetHolds_iff_check i t f _ _ hl, checkFacet_iff, checkFacet_iff]
    simp only [facetSpace, hv, hstr, true_and]
  constructor
  · rintro ⟨hy, _, hf⟩
    exact ⟨hy, fun f hm => ((transfer hy).2 f hm).mp (hf f hm)⟩
  · rintro ⟨hy, hf⟩
    obtain ⟨hs, he⟩ := transfer hy
    exact ⟨hy, hs, fun f hm => (he f hm).mpr (hf f hm)⟩

private def lowerRestriction (t : IRI) (fs : List Facet) :
    { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y r ↔ dataHolds i y (.restriction t fs) } :=
  if ht : isStringSubtype t = true then
    if hfs : !fs.isEmpty && fs.all isNumericLengthFacet then
      let lengths := lowerSmallRestriction (xsd "string") fs
      ⟨.intersection (.datatype t) lengths.1, fun i y => by
        simp only [Bool.and_eq_true] at hfs
        exact (and_congr Iff.rfl (lengths.2 i y)).trans
          (stringSubtypeLengthRestriction_iff ht hfs.2 i y)⟩
    else lowerSmallRestriction t fs
  else lowerSmallRestriction t fs

private def namePatternLength : Facet := ⟨xsd "length", ⟨"1", xsd "integer"⟩⟩

def namePatternRange : NamePattern → DataRange
  | .startChar => .intersection (.datatype (xsd "Name"))
      (.restriction (xsd "string") [namePatternLength])
  | .nameChar => .intersection (.datatype (xsd "NMTOKEN"))
      (.restriction (xsd "string") [namePatternLength])
  | .name => .datatype (xsd "Name")
  | .nmtoken => .datatype (xsd "NMTOKEN")

private theorem datatype_embed_iff (i : Interpretation datatypeMap) (t : IRI)
    (ht : supportedDatatype t = true) (v : Value) :
    i.datatypes t (i.embedValue v) ↔ valueSpace t v := by
  rw [i.datatypeAgreement t ht]
  exact ⟨fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

theorem namePatternRange_iff (p : NamePattern) (i : Interpretation datatypeMap) (s : String) :
    dataHolds i (i.embedValue (.string s)) (namePatternRange p) ↔ p.holds s := by
  have hName : i.datatypes (xsd "Name") (i.embedValue (.string s)) ↔ XMLNames.Name s.toList := by
    rw [datatype_embed_iff i _ rfl, ← checkValue_iff, ← isName_iff]
    rfl
  have hToken : i.datatypes (xsd "NMTOKEN") (i.embedValue (.string s)) ↔
      XMLNames.Nmtoken s.toList := by
    rw [datatype_embed_iff i _ rfl, ← checkValue_iff, ← isNMTOKEN_iff]
    rfl
  have hString : valueSpace (xsd "string") (.string s) :=
    (valueSpace_string_iff _).mpr ⟨s, rfl⟩
  have hLength : dataHolds i (i.embedValue (.string s))
      (.restriction (xsd "string") [namePatternLength]) ↔ s.length = 1 := by
    have hBound : decodeLiteral namePatternLength.bound = some (.integer 1) := by decide
    simp only [dataHolds, datatype_embed_iff i (xsd "string") rfl, hString,
      true_and, List.forall_mem_singleton,
      facetHolds_iff_check i _ _ _ _ hBound, checkFacet_iff]
    change (_ ∧ _ ∧ _ ∧ ∃ lf, some LengthFacet.length = some lf ∧ lf.holds 1 s) ↔ _
    simp [hString, LengthFacet.holds]
  cases p with
  | startChar =>
    change (i.datatypes (xsd "Name") _ ∧ dataHolds i _ (.restriction (xsd "string") _)) ↔ _
    rw [hName, hLength, and_comm]
    rfl
  | nameChar =>
    change (i.datatypes (xsd "NMTOKEN") _ ∧ dataHolds i _ (.restriction (xsd "string") _)) ↔ _
    rw [hToken, hLength, and_comm]
    rfl
  | name => exact hName
  | nmtoken => exact hToken

private def isXsdStringType (t : IRI) : Bool :=
  (t == xsd "string") || isStringSubtype t

private theorem stringFacet_namePattern_iff {t : IRI} {f : Facet} {p : NamePattern}
    (ht : isXsdStringType t = true) (hf : f.name = xsd "pattern")
    (hb : decodeLiteral f.bound = some (.string p.source))
    (i : Interpretation datatypeMap) (y : i.Data) (hy : i.datatypes t y) :
    dataHolds i y (namePatternRange p) ↔ facetHolds i t f y := by
  have hmem : supportedDatatype t = true ∧
      ∀ v, valueSpace t v → valueSpace (xsd "string") v := by
    rcases Bool.or_eq_true_iff.mp ht with heq | hs
    · obtain rfl := beq_iff_eq.mp heq
      exact ⟨rfl, fun _ h => h⟩
    · exact ⟨isStringSubtype_builtin hs, fun _ => valueSpace_string_of_subtype hs⟩
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement t hmem.1 y).mp hy
  obtain ⟨s, rfl⟩ := (valueSpace_string_iff _).mp (hmem.2 v hv)
  change valueSpace t (.string s) at hv
  rw [namePatternRange_iff, facetHolds_iff_check i t f _ _ hb, checkFacet_iff, hf]
  simp [facetSpace, hv, namePattern_matches_iff, show xsd "pattern" ≠ rdf "langRange" by decide]

private def lowerStringFacet (t : IRI) (ht : isXsdStringType t = true) (f : Facet) :
    Option { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      i.datatypes t y → (dataHolds i y r ↔ facetHolds i t f y) } :=
  if hf : f.name = xsd "pattern" then
    match hb : decodeLiteral f.bound with
    | some (.plainLiteral s "") => do
      let ⟨p, hp⟩ ← parseNamePattern s
      return ⟨namePatternRange p, stringFacet_namePattern_iff ht hf (by simpa [hp] using hb)⟩
    | _ => none
  else if isNumericLengthFacet f then
    let lowered := lowerRestriction t [f]
    some ⟨lowered.1, fun i y hy => by simpa [dataHolds, hy] using lowered.2 i y⟩
  else none

private def lowerStringPatterns (t : IRI) (ht : isXsdStringType t = true) :
    (fs : List Facet) →
    Option { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y r ↔ dataHolds i y (.restriction t fs) }
  | [] => some ⟨.datatype t, fun _ _ => by simp [dataHolds]⟩
  | f :: fs => do
    let head ← lowerStringFacet t ht f
    let tail ← lowerStringPatterns t ht fs
    return ⟨.intersection head.1 tail.1, fun i y => by
      simp only [dataHolds, List.forall_mem_cons] at *
      constructor
      · rintro ⟨hf, hs⟩
        have ⟨hy, hfs⟩ := (tail.2 i y).mp hs
        exact ⟨hy, (head.2 i y hy).mp hf, hfs⟩
      · rintro ⟨hy, hf, hfs⟩
        exact ⟨(head.2 i y hy).mpr hf, (tail.2 i y).mpr ⟨hy, hfs⟩⟩⟩

private def lowerDataRestriction (t : IRI) (fs : List Facet) :
    { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y r ↔ dataHolds i y (.restriction t fs) } :=
  if ht : isXsdStringType t = true then
    if fs.any (fun f => f.name == xsd "pattern") then
      (lowerStringPatterns t ht fs).getD (lowerRestriction t fs)
    else lowerRestriction t fs
  else lowerRestriction t fs

private def keepLiteral {r : DataRange} (c : Compiled r) (l : Literal) : Bool :=
  (decodeLiteral l).any c.holds

private theorem filterEnumeration_iff {r : DataRange} (c : Compiled r)
    (ls : List Literal) (h : ls.all (fun l => (decodeLiteral l).isSome) = true)
    (i : Interpretation datatypeMap) (y : i.Data) :
    dataHolds i y (.oneOf (ls.filter (keepLiteral c))) ↔
      dataHolds i y (.oneOf ls) ∧ dataHolds i y r := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hl, hp⟩ := List.mem_filter.mp hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h l hl)
    refine ⟨⟨l, hl, rfl⟩, ?_⟩
    rw [i.lexicalAgreement l v hv]
    exact (c.holds_iff i v).mp (by simpa [keepLiteral, hv] using hp)
  · rintro ⟨⟨l, hl, rfl⟩, hp⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h l hl)
    rw [i.lexicalAgreement l v hv] at hp
    exact ⟨l, List.mem_filter.mpr ⟨hl,
      by simpa [keepLiteral, hv] using (c.holds_iff i v).mpr hp⟩, rfl⟩

private def lowerEnumerationRestriction (ls : List Literal) (r : DataRange) :
    { out : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y out ↔ dataHolds i y (.oneOf ls) ∧ dataHolds i y r } :=
  if h : ls.all (fun l => (decodeLiteral l).isSome) = true then
    match compile r with
    | some c => ⟨.oneOf (ls.filter (keepLiteral c)), filterEnumeration_iff c ls h⟩
    | none => ⟨.intersection (.oneOf ls) r, fun _ _ => Iff.rfl⟩
  else ⟨.intersection (.oneOf ls) r, fun _ _ => Iff.rfl⟩

private def lowerIntersection (a b : DataRange) :
    { out : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y out ↔ dataHolds i y (.intersection a b) } :=
  match a, b with
  | .oneOf ls, r => lowerEnumerationRestriction ls r
  | r, .oneOf ls =>
    let c := lowerEnumerationRestriction ls r
    ⟨c.1, fun i y => (c.2 i y).trans and_comm⟩
  | a, b => ⟨.intersection a b, fun _ _ => Iff.rfl⟩

/-- Lower supported name patterns and subtype length facets to intersections,
and filter explicit enumerations by compiled range membership. -/
def lowerSmallRanges : (source : DataRange) →
    { r : DataRange // ∀ (i : Interpretation datatypeMap) (y : i.Data),
      dataHolds i y r ↔ dataHolds i y source }
  | .restriction t fs => lowerDataRestriction t fs
  | .complement a =>
    let a' := lowerSmallRanges a
    ⟨.complement a'.1, fun i y => not_congr (a'.2 i y)⟩
  | .intersection a b =>
    let a' := lowerSmallRanges a
    let b' := lowerSmallRanges b
    let lowered := lowerIntersection a'.1 b'.1
    ⟨lowered.1, fun i y => (lowered.2 i y).trans (and_congr (a'.2 i y) (b'.2 i y))⟩
  | .union a b =>
    let a' := lowerSmallRanges a
    let b' := lowerSmallRanges b
    ⟨.union a'.1 b'.1, fun i y => or_congr (a'.2 i y) (b'.2 i y)⟩
  | r => ⟨r, fun _ _ => Iff.rfl⟩

/-- Executable whole-domain disjointness check between any two solved ranges. -/
def SolvedRange.disjoint {r1 r2 : DataRange} (s1 : SolvedRange r1) (s2 : SolvedRange r2) : Bool :=
  match s1, s2 with
  | .finite f1, _ => f1.values.all fun v => !s2.compiled.holds v
  | _, .finite f2 => f2.values.all fun v => !s1.compiled.holds v
  | .intInterval i1, .intInterval i2 =>
    let inter := i1.bounds.intersect i2.bounds
    match inter.lower, inter.upper with
    | some lo, some hi => decide (hi < lo)
    | _, _ => false
  | .ratInterval r1, .ratInterval r2 =>
    (r1.bounds.intersect r2.bounds).isEmpty (r1.decimalOnly || r2.decimalOnly)
  | .stringInterval st1, .stringInterval st2 =>
    (st1.bounds.intersect st2.bounds).isEmpty
  | .stringInterval _, .intInterval _ | .stringInterval _, .ratInterval _
  | .intInterval _, .stringInterval _ | .ratInterval _, .stringInterval _ => true
  | .intInterval _, .ratInterval _ | .ratInterval _, .intInterval _ => false

theorem SolvedRange.disjoint_sound {r1 r2 : DataRange}
    (s1 : SolvedRange r1) (s2 : SolvedRange r2) (h : s1.disjoint s2 = true)
    (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ (dataHolds i y r1 ∧ dataHolds i y r2) := by
  rintro ⟨h1, h2⟩
  cases s1 with
  | finite f1 =>
    obtain ⟨v, hv, rfl⟩ := f1.member_in i y h1
    have hall := List.all_eq_true.mp h v hv
    rw [(s2.compiled.holds_iff i v).mpr h2] at hall
    cases hall
  | intInterval i1 =>
    cases s2 with
    | finite f2 =>
      obtain ⟨v, hv, rfl⟩ := f2.member_in i y h2
      have hall := List.all_eq_true.mp h v hv
      simp only [SolvedRange.compiled] at hall
      rw [(i1.compiled.holds_iff i v).mpr h1] at hall
      cases hall
    | intInterval i2 =>
      simp only [SolvedRange.disjoint] at h
      cases hlo : (i1.bounds.intersect i2.bounds).lower with
      | none => simp [hlo] at h
      | some lo =>
        cases hhi : (i1.bounds.intersect i2.bounds).upper with
        | none => simp [hlo, hhi] at h
        | some hi =>
          simp only [hlo, hhi] at h
          exact i1.disjoint_sound i2 hlo hhi (of_decide_eq_true h) i y ⟨h1, h2⟩
    | stringInterval st2 =>
      obtain ⟨z, _, hy1⟩ := i1.member_bounds i y h1
      obtain ⟨s, _, hy2⟩ := st2.member_bounds i y h2
      have heq := i.embedValue_injective (hy1.trans hy2.symm)
      cases heq
    | ratInterval _ => cases h
  | ratInterval rv1 =>
    cases s2 with
    | finite f2 =>
      obtain ⟨v, hv, rfl⟩ := f2.member_in i y h2
      have hall := List.all_eq_true.mp h v hv
      simp only [SolvedRange.compiled] at hall
      rw [(rv1.compiled.holds_iff i v).mpr h1] at hall
      cases hall
    | ratInterval rv2 =>
      obtain ⟨q1, hd1, hb1, hy1⟩ := rv1.member_bounds i y h1
      obtain ⟨q2, hd2, hb2, hy2⟩ := rv2.member_bounds i y h2
      have hqeq : q1 = q2 := Value.number.inj (i.embedValue_injective (hy1.trans hy2.symm))
      subst hqeq
      refine RatBounds.isEmpty_sound h ?_ (RatBounds.contains_intersect_of hb1 hb2)
      intro hd
      rcases Bool.or_eq_true_iff.mp hd with h1' | h2'
      · exact hd1 h1'
      · exact hd2 h2'
    | stringInterval st2 =>
      obtain ⟨q, _, _, hy1⟩ := rv1.member_bounds i y h1
      obtain ⟨s, _, hy2⟩ := st2.member_bounds i y h2
      have heq := i.embedValue_injective (hy1.trans hy2.symm)
      cases heq
    | intInterval _ => cases h
  | stringInterval st1 =>
    cases s2 with
    | finite f2 =>
      obtain ⟨v, hv, rfl⟩ := f2.member_in i y h2
      have hall := List.all_eq_true.mp h v hv
      simp only [SolvedRange.compiled] at hall
      rw [(st1.compiled.holds_iff i v).mpr h1] at hall
      cases hall
    | stringInterval st2 =>
      obtain ⟨s1', hs1, hy1⟩ := st1.member_bounds i y h1
      obtain ⟨s2', hs2, hy2⟩ := st2.member_bounds i y h2
      have hseq : s1' = s2' := (Value.plainLiteral.inj (i.embedValue_injective (hy1.trans hy2.symm))).1
      subst hseq
      exact StringLengthBounds.isEmpty_sound h
        ((StringLengthBounds.contains_intersect _ _ _).mpr ⟨hs1, hs2⟩)
    | intInterval i2 =>
      obtain ⟨s, _, hy1⟩ := st1.member_bounds i y h1
      obtain ⟨z, _, hy2⟩ := i2.member_bounds i y h2
      have heq := i.embedValue_injective (hy1.trans hy2.symm)
      cases heq
    | ratInterval rv2 =>
      obtain ⟨s, _, hy1⟩ := st1.member_bounds i y h1
      obtain ⟨q, _, _, hy2⟩ := rv2.member_bounds i y h2
      have heq := i.embedValue_injective (hy1.trans hy2.symm)
      cases heq

/-- Compile a `DataRange` into a `SolvedRange`, closing recursively under
    disjoint intersections, finite intersections with arbitrary compiled ranges
    (including `complement`, `pattern`, `langRange`), and finite/empty unions. -/
def compileSolvedRange : (r : DataRange) → Option (SolvedRange r)
  | .intersection a b =>
    match compileBaseSolvedRange (.intersection a b) with
    | some sr => some sr
    | none =>
      match compile (.intersection a b) with
      | none => none
      | some comp =>
        match compileSolvedRange a, compileSolvedRange b with
        | some sa, some sb =>
          if hd : sa.disjoint sb = true then
            some (.finite ⟨[], comp, fun i y hy => (sa.disjoint_sound sb hd i y hy).elim⟩)
          else if ha : sa.isEmpty = true then
            some (.finite ⟨[], comp, fun i y hy => (sa.isEmpty_sound ha i y hy.1).elim⟩)
          else if hb : sb.isEmpty = true then
            some (.finite ⟨[], comp, fun i y hy => (sb.isEmpty_sound hb i y hy.2).elim⟩)
          else match hfa : sa.finiteValues?, compile b with
            | some vs, some cb =>
              some (.finite ⟨vs.filter cb.holds, comp, fun i y hy => by
                obtain ⟨v, hv, rfl⟩ := sa.finiteValues?_sound hfa i y hy.1
                exact ⟨v, List.mem_filter.mpr ⟨hv, (cb.holds_iff i v).mpr hy.2⟩, rfl⟩⟩)
            | _, _ =>
              match compile a, hfb : sb.finiteValues? with
              | some ca, some vs =>
                some (.finite ⟨vs.filter ca.holds, comp, fun i y hy => by
                  obtain ⟨v, hv, rfl⟩ := sb.finiteValues?_sound hfb i y hy.2
                  exact ⟨v, List.mem_filter.mpr ⟨hv, (ca.holds_iff i v).mpr hy.1⟩, rfl⟩⟩)
              | _, _ => none
        | some sa, none =>
          if ha : sa.isEmpty = true then
            some (.finite ⟨[], comp, fun i y hy => (sa.isEmpty_sound ha i y hy.1).elim⟩)
          else match hfa : sa.finiteValues?, compile b with
            | some vs, some cb =>
              some (.finite ⟨vs.filter cb.holds, comp, fun i y hy => by
                obtain ⟨v, hv, rfl⟩ := sa.finiteValues?_sound hfa i y hy.1
                exact ⟨v, List.mem_filter.mpr ⟨hv, (cb.holds_iff i v).mpr hy.2⟩, rfl⟩⟩)
            | _, _ => none
        | none, some sb =>
          if hb : sb.isEmpty = true then
            some (.finite ⟨[], comp, fun i y hy => (sb.isEmpty_sound hb i y hy.2).elim⟩)
          else match compile a, hfb : sb.finiteValues? with
            | some ca, some vs =>
              some (.finite ⟨vs.filter ca.holds, comp, fun i y hy => by
                obtain ⟨v, hv, rfl⟩ := sb.finiteValues?_sound hfb i y hy.2
                exact ⟨v, List.mem_filter.mpr ⟨hv, (ca.holds_iff i v).mpr hy.1⟩, rfl⟩⟩)
            | _, _ => none
        | none, none => none
  | .union a b =>
    match compileBaseSolvedRange (.union a b) with
    | some sr => some sr
    | none =>
      match compile (.union a b), compileSolvedRange a, compileSolvedRange b with
      | some comp, some sa, some sb =>
        if ha : sa.isEmpty = true then
          if hb : sb.isEmpty = true then
            some (.finite ⟨[], comp, fun i y hy =>
              hy.elim (fun h1 => (sa.isEmpty_sound ha i y h1).elim)
                      (fun h2 => (sb.isEmpty_sound hb i y h2).elim)⟩)
          else none
        else match hfa : sa.finiteValues?, hfb : sb.finiteValues? with
          | some vsa, some vsb =>
            some (.finite ⟨(vsa ++ vsb).eraseDups, comp, fun i y hy => by
              rcases hy with h1 | h2
              · obtain ⟨v, hv, rfl⟩ := sa.finiteValues?_sound hfa i y h1
                exact ⟨v, List.mem_eraseDups.mpr (List.mem_append_left _ hv), rfl⟩
              · obtain ⟨v, hv, rfl⟩ := sb.finiteValues?_sound hfb i y h2
                exact ⟨v, List.mem_eraseDups.mpr (List.mem_append_right _ hv), rfl⟩⟩)
          | _, _ => none
      | _, _, _ => none
  | r => compileBaseSolvedRange r

private theorem minInclusive_bound {i : Interpretation datatypeMap} {l : Literal} {lo z : Int}
    (hl : decodeLiteral l = some (.integer lo))
    (hf : facetHolds i (xsd "integer") ⟨xsd "minInclusive", l⟩ (i.embedValue (.integer z))) :
    lo ≤ z := by
  have hcheck := (facetHolds_iff_check i (xsd "integer") ⟨xsd "minInclusive", l⟩
    (.integer lo) (.integer z) hl).mp hf
  have hspace := (checkFacet_iff (xsd "integer") (xsd "minInclusive")
    (.integer lo) (.integer z)).mp hcheck
  obtain ⟨_, order, horder, hholds⟩ := hspace
  have hord : order = .minInclusive := Option.some.inj horder.symm
  subst hord
  exact ofInt_le_ofInt hholds

private theorem maxInclusive_bound {i : Interpretation datatypeMap} {l : Literal} {hi z : Int}
    (hl : decodeLiteral l = some (.integer hi))
    (hf : facetHolds i (xsd "integer") ⟨xsd "maxInclusive", l⟩ (i.embedValue (.integer z))) :
    z ≤ hi := by
  have hcheck := (facetHolds_iff_check i (xsd "integer") ⟨xsd "maxInclusive", l⟩
    (.integer hi) (.integer z) hl).mp hf
  have hspace := (checkFacet_iff (xsd "integer") (xsd "maxInclusive")
    (.integer hi) (.integer z)).mp hcheck
  obtain ⟨_, order, horder, hholds⟩ := hspace
  have hord : order = .maxInclusive := Option.some.inj horder.symm
  subst hord
  exact ofInt_le_ofInt hholds

private theorem integer_member_embedded {i : Interpretation datatypeMap} {y : i.Data}
    (hy : i.datatypes (xsd "integer") y) : ∃ z : Int, i.embedValue (.integer z) = y := by
  have hint : datatypeMap.builtin (xsd "integer") :=
    (show supportedDatatype (xsd "integer") = true by decide)
  obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement (xsd "integer") hint y).mp hy
  obtain ⟨z, rfl⟩ := (valueSpace_integer_iff v).mp hv
  exact ⟨z, rfl⟩

/-- Recognize `xsd:integer` restricted by `minInclusive` and `maxInclusive`
    with decoded integer bounds (in either facet order). -/
def compileClosedIntInterval : (r : DataRange) → Option (ClosedIntInterval r)
  | .restriction t [⟨f1, l1⟩, ⟨f2, l2⟩] =>
    if ht : t = xsd "integer" then
      if hf : f1 = xsd "minInclusive" ∧ f2 = xsd "maxInclusive" then
        match hlo : decodeIntBound l1, hhi : decodeIntBound l2, compile (.restriction t [⟨f1, l1⟩, ⟨f2, l2⟩]) with
        | some lo, some hi, some compiled =>
          some ⟨lo, hi, compiled, by
            intro i y hy
            subst ht
            rcases hf with ⟨rfl, rfl⟩
            obtain ⟨z, rfl⟩ := integer_member_embedded hy.1
            have hlo' := minInclusive_bound (decodeIntBound_eq hlo) (hy.2 _ (by simp))
            have hhi' := maxInclusive_bound (decodeIntBound_eq hhi) (hy.2 _ (by simp))
            exact ⟨z, hlo', hhi', rfl⟩⟩
        | _, _, _ => none
      else if hf' : f1 = xsd "maxInclusive" ∧ f2 = xsd "minInclusive" then
        match hhi : decodeIntBound l1, hlo : decodeIntBound l2, compile (.restriction t [⟨f1, l1⟩, ⟨f2, l2⟩]) with
        | some hi, some lo, some compiled =>
          some ⟨lo, hi, compiled, by
            intro i y hy
            subst ht
            rcases hf' with ⟨rfl, rfl⟩
            obtain ⟨z, rfl⟩ := integer_member_embedded hy.1
            have hhi' := maxInclusive_bound (decodeIntBound_eq hhi) (hy.2 _ (by simp))
            have hlo' := minInclusive_bound (decodeIntBound_eq hlo) (hy.2 _ (by simp))
            exact ⟨z, hlo', hhi', rfl⟩⟩
        | _, _, _ => none
      else none
    else none
  | _ => none

theorem ClosedIntInterval.empty_sound {r : DataRange} (interval : ClosedIntInterval r)
    (h : interval.upper < interval.lower) (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ dataHolds i y r := by
  intro hy
  obtain ⟨z, hlo, hhi, _⟩ := interval.member_bounds i y hy
  omega

/-- Executable evidence that a data range is inhabited or empty across every
    data domain extending `datatypeMap`. -/
inductive RangeEvidence where
  | witness (value : Value)
  | emptyIntInterval (lower upper : Int)
  deriving DecidableEq, Repr

def RangeClaim (r : DataRange) : RangeEvidence → Prop
  | .witness v => ∀ i : Interpretation datatypeMap, dataHolds i (i.embedValue v) r
  | .emptyIntInterval _ _ => ∀ (i : Interpretation datatypeMap) (y : i.Data), ¬ dataHolds i y r

def checkRangeEvidence (r : DataRange) : RangeEvidence → Bool
  | .witness v =>
    match compile r with
    | some compiled => compiled.holds v
    | none => false
  | .emptyIntInterval lo hi =>
    match compileClosedIntInterval r with
    | some interval => decide (interval.lower = lo ∧ interval.upper = hi ∧ hi < lo)
    | none => false

theorem checkRangeEvidence_sound {r : DataRange} {e : RangeEvidence}
    (h : checkRangeEvidence r e = true) : RangeClaim r e := by
  cases e with
  | witness v =>
    simp only [checkRangeEvidence] at h
    split at h
    next compiled _ =>
      intro i
      exact (compiled.holds_iff i v).mp h
    next => contradiction
  | emptyIntInterval lo hi =>
    simp only [checkRangeEvidence] at h
    split at h
    next interval _ =>
      obtain ⟨rfl, rfl, hlt⟩ := of_decide_eq_true h
      exact interval.empty_sound hlt
    next => contradiction

end Sabrina.OWL2.DataRanges
