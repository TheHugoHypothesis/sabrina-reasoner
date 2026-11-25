import Sabrina.OWL2.DataRanges
import Sabrina.OWL2.SROIQD.Model

/-!
Exact Boolean-closed `DataRange` decision algebra and bounded witness sampler
for `SROIQ(D)`.

Covers `rdfs:Literal`, `xsd:boolean`, `xsd:integer` and all 12 named integer
subtypes with arbitrary order facets (`minInclusive`, `maxInclusive`,
`minExclusive`, `maxExclusive`), `xsd:string`, `xsd:anyURI`, `rdf:XMLLiteral`,
`xsd:hexBinary`, `xsd:base64Binary`, arbitrary `oneOf` literal enumerations,
and arbitrary nested `complement`, `intersection`, and `union` combinations.
-/

namespace Sabrina.OWL2.SROIQD

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.DataRanges

/-! ### 1. Exact decidable `DataRange` fragment (`DataRange.isSROIQD`) -/

def isNumericFacetBound (l : Literal) : Bool :=
  match decodeLiteral l with
  | some (.number _) => true
  | _ => false

def isOrderIntFacet (f : Facet) : Bool :=
  (orderFacet f.name).isSome && isNumericFacetBound f.bound

def isExactAtomicDataRange : DataRange → Bool
  | .datatype t =>
    t == literalDatatype ||
    t == xsd "boolean" ||
    (integerBounds t).isSome ||
    t == xsd "string" ||
    t == xsd "anyURI" ||
    t == rdf "XMLLiteral" ||
    t == xsd "hexBinary" ||
    t == xsd "base64Binary"
  | .restriction t fs =>
    (integerBounds t).isSome && fs.all isOrderIntFacet
  | .oneOf ls =>
    ls.all fun l => (decodeLiteral l).isSome
  | _ => false

def _root_.Sabrina.OWL2.DataRange.isSROIQD : DataRange → Bool
  | .complement r => r.isSROIQD
  | .intersection a b => a.isSROIQD && b.isSROIQD
  | .union a b => a.isSROIQD && b.isSROIQD
  | r => isExactAtomicDataRange r

@[simp] theorem DataRange.isSROIQD_complement (r : DataRange) :
    (DataRange.complement r).isSROIQD = r.isSROIQD := rfl

@[simp] theorem DataRange.isSROIQD_intersection (a b : DataRange) :
    (DataRange.intersection a b).isSROIQD = (a.isSROIQD && b.isSROIQD) := rfl

@[simp] theorem DataRange.isSROIQD_union (a b : DataRange) :
    (DataRange.union a b).isSROIQD = (a.isSROIQD && b.isSROIQD) := rfl

namespace Termination

/-! ### 2. Exact integer interval difference and bounded sampling -/

def subtractBoundsOne (cur neg : IntegerBounds) : List IntegerBounds :=
  let left : List IntegerBounds :=
    match neg.lower with
    | none => []
    | some nlo =>
      [{ lower := cur.lower,
         upper := match cur.upper with
           | none => some (nlo - 1)
           | some chi => some (min chi (nlo - 1)) }]
  let right : List IntegerBounds :=
    match neg.upper with
    | none => []
    | some nhi =>
      [{ lower := match cur.lower with
           | none => some (nhi + 1)
           | some clo => some (max clo (nhi + 1)),
         upper := cur.upper }]
  left ++ right

theorem mem_subtractBoundsOne_iff (cur neg : IntegerBounds) (z : Int) :
    (∃ b ∈ subtractBoundsOne cur neg, b.contains z) ↔ (cur.contains z ∧ ¬ neg.contains z) := by
  rcases cur with ⟨clo, chi⟩
  rcases neg with ⟨nlo, nhi⟩
  cases clo <;> cases chi <;> cases nlo <;> cases nhi <;>
    simp [subtractBoundsOne, IntegerBounds.contains] <;> omega

def foldSubtractBounds : List IntegerBounds → List IntegerBounds → List IntegerBounds
  | bs, [] => bs
  | bs, neg :: rest => foldSubtractBounds (bs.flatMap (subtractBoundsOne · neg)) rest

theorem mem_foldSubtractBounds_iff (bs negs : List IntegerBounds) (z : Int) :
    (∃ b ∈ foldSubtractBounds bs negs, b.contains z) ↔
      ((∃ b ∈ bs, b.contains z) ∧ ∀ n ∈ negs, ¬ n.contains z) := by
  induction negs generalizing bs with
  | nil => simp [foldSubtractBounds]
  | cons neg rest ih =>
    simp only [foldSubtractBounds, ih, List.mem_flatMap, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨b, ⟨b₀, hb₀, hb⟩, hz⟩, hrest⟩
      have ⟨h1, h2⟩ := (mem_subtractBoundsOne_iff b₀ neg z).mp ⟨b, hb, hz⟩
      exact ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
    · rintro ⟨⟨b₀, hb₀, h1⟩, h2, hrest⟩
      obtain ⟨b, hb, hz⟩ := (mem_subtractBoundsOne_iff b₀ neg z).mpr ⟨h1, h2⟩
      exact ⟨⟨b, ⟨b₀, hb₀, hb⟩, hz⟩, hrest⟩

def sampleIntBounds (K : Nat) (b : IntegerBounds) : List Int :=
  match b.lower, b.upper with
  | some lo, some hi =>
    if hi < lo then []
    else
      let cnt := min K ((hi - lo).toNat + 1)
      (List.range cnt).map fun k => lo + Int.ofNat k
  | some lo, none =>
    (List.range K).map fun k => lo + Int.ofNat k
  | none, some hi =>
    (List.range K).map fun k => hi - Int.ofNat k
  | none, none =>
    (List.range K).map fun k => Int.ofNat k

theorem sampleIntBounds_nodup (K : Nat) (b : IntegerBounds) :
    (sampleIntBounds K b).Nodup := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleIntBounds]
  · exact nodup_map_inj (fun {_ _} h => by simp only [Int.ofNat_eq_natCast] at h; omega) List.nodup_range
  · exact nodup_map_inj (fun {_ _} h => by simp only [Int.ofNat_eq_natCast] at h; omega) List.nodup_range
  · exact nodup_map_inj (fun {_ _} h => by simp only [Int.ofNat_eq_natCast] at h; omega) List.nodup_range
  · split
    · exact List.nodup_nil
    · exact nodup_map_inj (fun {_ _} h => by simp only [Int.ofNat_eq_natCast] at h; omega) List.nodup_range

theorem sampleIntBounds_sound (K : Nat) (b : IntegerBounds) {z : Int}
    (hz : z ∈ sampleIntBounds K b) : b.contains z := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleIntBounds] at hz
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    exact ⟨trivial, trivial⟩
  · rename_i hi
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    exact ⟨trivial, by simp [Option.elim]; omega⟩
  · rename_i lo
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    exact ⟨by simp [Option.elim]; omega, trivial⟩
  · rename_i lo hi
    split at hz
    · cases hz
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
      rw [List.mem_range] at hk
      exact ⟨by simp [Option.elim]; omega, by simp [Option.elim]; omega⟩

theorem sampleIntBounds_complete_of_lt (K : Nat) (b : IntegerBounds)
    (hlt : (sampleIntBounds K b).length < K) {z : Int} (hz : b.contains z) :
    z ∈ sampleIntBounds K b := by
  rcases b with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp only [sampleIntBounds] at hlt ⊢
  · simp at hlt
  · simp at hlt
  · simp at hlt
  · rename_i lo hi
    simp only [IntegerBounds.contains, Option.elim] at hz
    by_cases hcond : hi < lo
    · omega
    · simp only [hcond, ↓reduceIte, List.length_map, List.length_range] at hlt ⊢
      rw [List.mem_map]
      refine ⟨(z - lo).toNat, ?_, by simp only [Int.ofNat_eq_natCast]; omega⟩
      rw [List.mem_range]
      omega

def sampleIntSet (K : Nat) (bs : List IntegerBounds) : List Int :=
  (bs.flatMap (sampleIntBounds K)).eraseDups

theorem sampleIntSet_nodup (K : Nat) (bs : List IntegerBounds) :
    (sampleIntSet K bs).Nodup :=
  nodup_eraseDups_list _

theorem sampleIntSet_sound (K : Nat) (bs : List IntegerBounds) {z : Int}
    (hz : z ∈ sampleIntSet K bs) : ∃ b ∈ bs, b.contains z := by
  have hz' := List.mem_eraseDups.mp hz
  obtain ⟨b, hb, hzb⟩ := List.mem_flatMap.mp hz'
  exact ⟨b, hb, sampleIntBounds_sound K b hzb⟩

theorem sampleIntSet_complete_of_lt (K : Nat) (bs : List IntegerBounds)
    (hlt : (sampleIntSet K bs).length < K) {z : Int}
    (hz : ∃ b ∈ bs, b.contains z) : z ∈ sampleIntSet K bs := by
  obtain ⟨b, hb, hzb⟩ := hz
  have hsub : ∀ x ∈ sampleIntBounds K b, x ∈ sampleIntSet K bs := fun x hx =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hx⟩)
  have hle : (sampleIntBounds K b).length ≤ (sampleIntSet K bs).length :=
    (sampleIntBounds_nodup K b).length_le_of_subset hsub
  exact hsub z (sampleIntBounds_complete_of_lt K b (Nat.lt_of_le_of_lt hle hlt) hzb)

/-! ### 3. Counting lemma for infinite families avoiding a finite exclusion list -/

private theorem filter_sub_add_filter_not {α : Type} (p : α → Bool) (xs : List α) :
    xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.filter]
    cases p a <;> simp [ih] <;> omega

private theorem filter_mem_length_le {α : Type} [DecidableEq α] (xs bad : List α)
    (hnd : xs.Nodup) :
    (xs.filter (fun x => bad.contains x)).length ≤ bad.length := by
  have hnd' : (xs.filter (fun x => bad.contains x)).Nodup := List.filter_sublist.nodup hnd
  have hsub : ∀ x ∈ xs.filter (fun x => bad.contains x), x ∈ bad.eraseDups := fun x hx => by
    have h := (List.mem_filter.mp hx).2
    exact List.mem_eraseDups.mpr (List.contains_iff_mem.mp h)
  have h1 := hnd'.length_le_of_subset hsub
  have h2 : bad.eraseDups.length ≤ bad.length := by
    have hsub2 : ∀ x ∈ bad.eraseDups, x ∈ bad := fun x hx => List.mem_eraseDups.mp hx
    exact (nodup_eraseDups_list bad).length_le_of_subset hsub2
  omega

theorem filter_not_contains_length_ge {α : Type} [DecidableEq α] (xs bad : List α)
    (hnd : xs.Nodup) :
    xs.length - bad.length ≤ (xs.filter (fun x => !bad.contains x)).length := by
  have hsum := filter_sub_add_filter_not (fun x => bad.contains x) xs
  have hle := filter_mem_length_le xs bad hnd
  omega

theorem filter_pred_length_ge_of_avoid {α : Type} [DecidableEq α]
    (xs bad : List α) (pred : α → Bool) (hnd : xs.Nodup)
    (hgood : ∀ x ∈ xs, x ∉ bad → pred x = true) :
    xs.length - bad.length ≤ (xs.filter pred).length := by
  have h1 := filter_not_contains_length_ge xs bad hnd
  have hsub : ∀ x ∈ xs.filter (fun x => !bad.contains x), x ∈ xs.filter pred := fun x hx => by
    obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hx
    have hnb : x ∉ bad := fun hb => by
      rw [List.contains_iff_mem.mpr hb] at hnot; cases hnot
    exact List.mem_filter.mpr ⟨hmem, hgood x hmem hnb⟩
  have h2 := (List.filter_sublist.nodup hnd).length_le_of_subset hsub
  omega

/-! ### 4. Exact two-way integer interval characterization -/

def intFacetBounds (f : Facet) : Option IntegerBounds :=
  match orderFacet f.name, decodeLiteral f.bound with
  | some .minInclusive, some (.number b) => some { lower := some b.ceil }
  | some .maxInclusive, some (.number b) => some { upper := some b.floor }
  | some .minExclusive, some (.number b) => some { lower := some (b.floor + 1) }
  | some .maxExclusive, some (.number b) => some { upper := some (b.ceil - 1) }
  | _, _ => none

theorem intFacetBounds_iff {t : IRI} {base : IntegerBounds}
    (ht : integerBounds t = some base) {f : Facet} {fb : IntegerBounds}
    (hfb : intFacetBounds f = some fb) (i : Interpretation datatypeMap) (z : Int)
    (hbase : base.contains z) :
    facetHolds i t f (i.embedValue (.integer z)) ↔ fb.contains z := by
  unfold intFacetBounds at hfb
  cases ho : orderFacet f.name with
  | none => simp [ho] at hfb
  | some ord =>
    cases hb : decodeLiteral f.bound with
    | none => simp [ho, hb] at hfb
    | some v =>
      cases v <;> simp only [ho, hb] at hfb
      case number b =>
        rw [facetHolds_iff_check i t f (.number b) (.integer z) hb,
            checkFacet_iff t f.name (.number b) (.integer z)]
        have hvs : valueSpace t (.integer z) :=
          (valueSpace_integerSubtype_iff ht (.integer z)).mpr ⟨z, hbase, rfl⟩
        simp only [facetSpace, hvs, true_and, ho, Option.some.injEq, exists_eq_left']
        cases ord <;> simp only [Option.some.injEq] at hfb <;> subst hfb <;>
          simp only [OrderFacet.holds, IntegerBounds.contains, Option.elim, true_and, and_true]
        · exact Rat.ceil_le_iff.symm
        · exact Rat.le_floor_iff.symm
        · change b < (z : Rat) ↔ b.floor + 1 ≤ z
          rw [← Rat.floor_lt_iff]
          omega
        · change (z : Rat) < b ↔ z ≤ b.ceil - 1
          rw [← Rat.lt_ceil_iff]
          omega
      all_goals cases ord <;> contradiction

def foldIntFacetBounds (acc : IntegerBounds) : List Facet → Option IntegerBounds
  | [] => some acc
  | f :: fs => do
    let fb ← intFacetBounds f
    foldIntFacetBounds (acc.intersect fb) fs

theorem foldIntFacetBounds_iff {t : IRI} {base : IntegerBounds}
    (ht : integerBounds t = some base) {fs : List Facet} {acc res : IntegerBounds}
    (hfold : foldIntFacetBounds acc fs = some res) (i : Interpretation datatypeMap) (z : Int)
    (hbase : base.contains z) :
    (acc.contains z ∧ ∀ f ∈ fs, facetHolds i t f (i.embedValue (.integer z))) ↔
      res.contains z := by
  induction fs generalizing acc with
  | nil =>
    cases hfold
    simp
  | cons f tail ih =>
    simp only [foldIntFacetBounds] at hfold
    obtain ⟨fb, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    rw [← ih htail, IntegerBounds.contains_intersect, List.forall_mem_cons,
        intFacetBounds_iff ht hfb i z hbase]
    exact ⟨fun ⟨ha, hf, hrest⟩ => ⟨⟨ha, hf⟩, hrest⟩,
           fun ⟨⟨ha, hf⟩, hrest⟩ => ⟨ha, hf, hrest⟩⟩

def extractIntAtomBounds : DataRange → Option IntegerBounds
  | .datatype t => integerBounds t
  | .restriction t fs => do
    let base ← integerBounds t
    foldIntFacetBounds base fs
  | _ => none

theorem extractIntAtomBounds_iff {a : DataRange} {b : IntegerBounds}
    (h : extractIntAtomBounds a = some b) (i : Interpretation datatypeMap) (y : i.Data) :
    dataHolds i y a ↔ ∃ z : Int, b.contains z ∧ i.embedValue (.integer z) = y := by
  cases a with
  | datatype t =>
    simp only [extractIntAtomBounds] at h
    have hsup : datatypeMap.builtin t := integerBounds_supported h
    constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy
      obtain ⟨z, hz, rfl⟩ := (valueSpace_integerSubtype_iff h v).mp hv
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact (i.datatypeAgreement t hsup _).mpr
        ⟨.integer z, (valueSpace_integerSubtype_iff h _).mpr ⟨z, hz, rfl⟩, rfl⟩
  | restriction t fs =>
    simp only [extractIntAtomBounds] at h
    obtain ⟨base, ht, hfold⟩ := Option.bind_eq_some_iff.mp h
    have hsup : datatypeMap.builtin t := integerBounds_supported ht
    constructor
    · rintro ⟨hy, hfs⟩
      obtain ⟨v, hv, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy
      obtain ⟨z, hz, rfl⟩ := (valueSpace_integerSubtype_iff ht v).mp hv
      exact ⟨z, (foldIntFacetBounds_iff ht hfold i z hz).mp ⟨hz, hfs⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hsub : ∀ (l : List Facet) (acc : IntegerBounds),
          foldIntFacetBounds acc l = some b → b.contains z → acc.contains z := by
        intro l
        induction l with
        | nil => intro acc hf hres; cases hf; exact hres
        | cons f tail ihf =>
          intro acc hf hres
          obtain ⟨fb, _, htail⟩ := Option.bind_eq_some_iff.mp hf
          exact ((IntegerBounds.contains_intersect acc fb z).mp (ihf (acc.intersect fb) htail hres)).1
      have hbase : base.contains z := hsub fs base hfold hz
      have ⟨_, hfs⟩ := (foldIntFacetBounds_iff ht hfold i z hbase).mpr hz
      refine ⟨(i.datatypeAgreement t hsup _).mpr
        ⟨.integer z, (valueSpace_integerSubtype_iff ht _).mpr ⟨z, hbase, rfl⟩, rfl⟩, hfs⟩
  | _ => cases h

theorem extractIntAtomBounds_isSome_of_restriction {t : IRI} {fs : List Facet}
    (ha : isExactAtomicDataRange (.restriction t fs) = true) :
    (extractIntAtomBounds (.restriction t fs)).isSome = true := by
  simp only [isExactAtomicDataRange, Bool.and_eq_true, List.all_eq_true, extractIntAtomBounds] at ha ⊢
  rcases ha with ⟨ht, hfs⟩
  obtain ⟨base, hbase⟩ := Option.isSome_iff_exists.mp ht
  rw [hbase]
  have hfold : ∀ (acc : IntegerBounds) (l : List Facet),
      (∀ f ∈ l, isOrderIntFacet f = true) → (foldIntFacetBounds acc l).isSome = true := by
    intro acc l
    induction l generalizing acc with
    | nil => intro _; rfl
    | cons f tail ih =>
      intro hl
      have hf := hl f (List.mem_cons_self ..)
      simp only [isOrderIntFacet, Bool.and_eq_true] at hf
      obtain ⟨ord, hord⟩ := Option.isSome_iff_exists.mp hf.1
      have hfb : (intFacetBounds f).isSome = true := by
        cases hb : decodeLiteral f.bound with
        | none => simp [isNumericFacetBound, hb] at hf
        | some v =>
          cases v <;> simp [isNumericFacetBound, hb] at hf
          case number b => cases ord <;> simp [intFacetBounds, hord, hb]
      obtain ⟨fb, hfb'⟩ := Option.isSome_iff_exists.mp hfb
      simp only [foldIntFacetBounds, hfb']
      exact ih (acc.intersect fb) (fun g hg => hl g (List.mem_cons_of_mem _ hg))
  exact hfold base fs hfs

/-! ### 5. Exact `oneOf` literal decoding and total atomic evaluation -/

def decodeLiteralsList : List Literal → Option (List Value)
  | [] => some []
  | l :: ls => (decodeLiteral l).bind fun v => (decodeLiteralsList ls).map (v :: ·)

theorem decodeLiteralsList_isSome {ls : List Literal}
    (h : ls.all (fun l => (decodeLiteral l).isSome) = true) :
    (decodeLiteralsList ls).isSome = true := by
  induction ls with
  | nil => rfl
  | cons l tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h.1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (ih h.2)
    simp [decodeLiteralsList, hv, hvs]

theorem decodeLiteralsList_mem_decoded {ls : List Literal} {vs : List Value} {v : Value}
    (h : decodeLiteralsList ls = some vs) (hm : v ∈ vs) :
    ∃ l ∈ ls, decodeLiteral l = some v := by
  induction ls generalizing vs with
  | nil => cases h; cases hm
  | cons l ls ih =>
    simp only [decodeLiteralsList] at h
    obtain ⟨w, hw, ht⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp ht
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨l, List.mem_cons_self .., hw⟩
    · obtain ⟨r, hr, hd⟩ := ih hws hm
      exact ⟨r, List.mem_cons_of_mem _ hr, hd⟩

theorem decodeLiteralsList_iff {ls : List Literal} {vs : List Value}
    (h : decodeLiteralsList ls = some vs) (i : Interpretation datatypeMap) (y : i.Data) :
    dataHolds i y (.oneOf ls) ↔ ∃ v ∈ vs, i.embedValue v = y := by
  induction ls generalizing vs with
  | nil =>
    cases h
    simp [dataHolds]
  | cons l tail ih =>
    simp only [decodeLiteralsList] at h
    obtain ⟨v, hv, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vt, hvt, hcons⟩ := Option.map_eq_some_iff.mp hrest
    subst hcons
    have htail := ih hvt
    simp only [dataHolds] at htail ⊢
    simp only [List.mem_cons, exists_eq_or_imp, i.lexicalAgreement l v hv, htail]

def evalAtom : DataRange → Value → Bool
  | .datatype t, v =>
    if t == literalDatatype then true else checkValue t v
  | .restriction t fs, v =>
    match extractIntAtomBounds (.restriction t fs), v with
    | some b, .number q => decide (q.den = 1 ∧ b.contains q.num)
    | _, _ => false
  | .oneOf ls, v =>
    match decodeLiteralsList ls with
    | some vs => vs.contains v
    | none => false
  | _, _ => false

theorem exactDatatype_supported {t : IRI}
    (h : isExactAtomicDataRange (.datatype t) = true) (hne : t ≠ literalDatatype) :
    supportedDatatype t = true := by
  simp only [isExactAtomicDataRange, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((((rfl | rfl) | hint) | rfl) | rfl) | rfl) | rfl) | rfl)
  · exact (hne rfl).elim
  · decide
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hint
    exact integerBounds_supported hb
  · decide
  · decide
  · decide
  · decide
  · decide

theorem evalAtom_iff {a : DataRange} (ha : isExactAtomicDataRange a = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalAtom a v = true ↔ dataHolds i (i.embedValue v) a := by
  cases a with
  | datatype t =>
    simp only [evalAtom]
    by_cases hlit : t = literalDatatype
    · subst hlit
      simp [dataHolds, i.literalDatatypeExt]
    · have hbeq : (t == literalDatatype) = false := beq_false_of_ne hlit
      have hsup : datatypeMap.builtin t := exactDatatype_supported ha hlit
      rw [hbeq]
      change checkValue t v = true ↔ i.datatypes t (i.embedValue v)
      rw [checkValue_iff, i.datatypeAgreement t hsup (i.embedValue v)]
      exact ⟨fun hv => ⟨v, hv, rfl⟩,
             fun ⟨w, hw, heq⟩ => i.embedValue_injective heq ▸ hw⟩
  | restriction t fs =>
    have his := extractIntAtomBounds_isSome_of_restriction ha
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp his
    rw [extractIntAtomBounds_iff hb i (i.embedValue v)]
    cases v with
    | number q =>
      simp only [evalAtom, hb, decide_eq_true_eq]
      constructor
      · rintro ⟨hden, hz⟩
        refine ⟨q.num, hz, congrArg i.embedValue ?_⟩
        simp only [Value.integer]
        congr 1
        apply Rat.ext <;> simp [hden]
      · rintro ⟨z, hz, heq⟩
        have hq : Rat.ofInt z = q := Value.number.inj (i.embedValue_injective heq)
        subst hq
        exact ⟨rfl, hz⟩
    | boolean _ | float _ | double _ | plainLiteral _ _ | anyURI _
    | hexBinary _ | base64Binary _ | dateTime _ | xmlLiteral _ | irrational _ =>
      simp only [evalAtom, hb, Bool.false_eq_true, false_iff]
      rintro ⟨z, _, heq⟩
      have h := i.embedValue_injective heq
      cases h
  | oneOf ls =>
    simp only [isExactAtomicDataRange] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    rw [decodeLiteralsList_iff hvs i (i.embedValue v)]
    simp only [evalAtom, hvs, List.contains_iff_mem]
    exact ⟨fun hv => ⟨v, hv, rfl⟩,
           fun ⟨w, hw, heq⟩ => i.embedValue_injective heq ▸ hw⟩
  | complement _ | intersection _ _ | union _ _ => cases ha

/-! ### 6. Atomic decomposition, Venn partitions, and Boolean evaluation -/

def atomsOfDataRange : DataRange → List DataRange
  | .complement r => atomsOfDataRange r
  | .intersection a b => (atomsOfDataRange a ++ atomsOfDataRange b).eraseDups
  | .union a b => (atomsOfDataRange a ++ atomsOfDataRange b).eraseDups
  | a => [a]

theorem atomsOfDataRange_exact {r : DataRange} (hr : r.isSROIQD = true) :
    ∀ a ∈ atomsOfDataRange r, isExactAtomicDataRange a = true := by
  induction r with
  | complement r ih => exact ih hr
  | intersection a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hr
    intro x hx
    rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with h1 | h2
    · exact iha ha x h1
    · exact ihb hb x h2
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hr
    intro x hx
    rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with h1 | h2
    · exact iha ha x h1
    · exact ihb hb x h2
  | datatype _ | restriction _ _ | oneOf _ =>
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact hr

def allPartitions : List DataRange → List (List DataRange × List DataRange)
  | [] => [([], [])]
  | a :: rest =>
    (allPartitions rest).flatMap fun (p, n) => [(a :: p, n), (p, a :: n)]

def vennPartitions (atoms : List DataRange) : List (List DataRange × List DataRange) :=
  (allPartitions atoms).eraseDups

theorem vennPartitions_nodup (atoms : List DataRange) :
    (vennPartitions atoms).Nodup :=
  nodup_eraseDups_list _

theorem mem_allPartitions_sub {atoms pos neg : List DataRange}
    (h : (pos, neg) ∈ allPartitions atoms) :
    (∀ a ∈ pos, a ∈ atoms) ∧ (∀ a ∈ neg, a ∈ atoms) ∧
    (∀ a ∈ atoms, a ∈ pos ∨ a ∈ neg) ∧
    (atoms.Nodup → ∀ a, ¬ (a ∈ pos ∧ a ∈ neg)) := by
  induction atoms generalizing pos neg with
  | nil =>
    simp only [allPartitions, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | cons hd tail ih =>
    simp only [allPartitions, List.mem_flatMap] at h
    obtain ⟨⟨p, n⟩, hpn, hcase⟩ := h
    obtain ⟨hp, hn, hcov, hdisj⟩ := ih hpn
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hcase
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; rcases List.mem_cons.mp ha with rfl | ha'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hp a ha')
      · intro a ha; exact List.mem_cons_of_mem _ (hn a ha)
      · intro a ha; rcases List.mem_cons.mp ha with rfl | ha'
        · exact .inl (List.mem_cons_self ..)
        · rcases hcov a ha' with h1 | h2
          · exact .inl (List.mem_cons_of_mem _ h1)
          · exact .inr h2
      · intro hnd a ⟨h1, h2⟩
        obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
        rcases List.mem_cons.mp h1 with rfl | h1'
        · exact hnot (hn a h2)
        · exact hdisj hnd' a ⟨h1', h2⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; exact List.mem_cons_of_mem _ (hp a ha)
      · intro a ha; rcases List.mem_cons.mp ha with rfl | ha'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hn a ha')
      · intro a ha; rcases List.mem_cons.mp ha with rfl | ha'
        · exact .inr (List.mem_cons_self ..)
        · rcases hcov a ha' with h1 | h2
          · exact .inl h1
          · exact .inr (List.mem_cons_of_mem _ h2)
      · intro hnd a ⟨h1, h2⟩
        obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
        rcases List.mem_cons.mp h2 with rfl | h2'
        · exact hnot (hp a h1)
        · exact hdisj hnd' a ⟨h1, h2'⟩

theorem mem_vennPartitions_sub {atoms pos neg : List DataRange}
    (h : (pos, neg) ∈ vennPartitions atoms) :
    (∀ a ∈ pos, a ∈ atoms) ∧ (∀ a ∈ neg, a ∈ atoms) ∧
    (∀ a ∈ atoms, a ∈ pos ∨ a ∈ neg) ∧
    (atoms.Nodup → ∀ a, ¬ (a ∈ pos ∧ a ∈ neg)) :=
  mem_allPartitions_sub (List.mem_eraseDups.mp h)

def partitionRange (pos neg : List DataRange) : DataRange :=
  pos.foldr DataRange.intersection
    (neg.foldr (fun a acc => DataRange.intersection (.complement a) acc)
      (.datatype literalDatatype))

theorem dataHolds_partitionRange_iff {dm : DatatypeMap} (i : Interpretation dm) (y : i.Data)
    (pos neg : List DataRange) :
    dataHolds i y (partitionRange pos neg) ↔
      (∀ a ∈ pos, dataHolds i y a) ∧ (∀ a ∈ neg, ¬ dataHolds i y a) := by
  have hneg : ∀ (ns : List DataRange),
      dataHolds i y (ns.foldr (fun a acc => DataRange.intersection (.complement a) acc)
        (.datatype literalDatatype)) ↔
      (∀ a ∈ ns, ¬ dataHolds i y a) := by
    intro ns
    induction ns with
    | nil => simp [dataHolds, i.literalDatatypeExt]
    | cons a tail ih =>
      simp only [List.foldr_cons, dataHolds, ih, List.forall_mem_cons]
  have hpos : ∀ (ps : List DataRange) (base : DataRange),
      dataHolds i y (ps.foldr DataRange.intersection base) ↔
      (∀ a ∈ ps, dataHolds i y a) ∧ dataHolds i y base := by
    intro ps base
    induction ps with
    | nil => simp
    | cons a tail ih =>
      simp only [List.foldr_cons, dataHolds, ih, List.forall_mem_cons, and_assoc]
  rw [partitionRange, hpos, hneg]

def evalPartition (pos neg : List DataRange) (v : Value) : Bool :=
  pos.all (evalAtom · v) && neg.all (fun a => !evalAtom a v)

theorem evalPartition_iff {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalPartition pos neg v = true ↔
      dataHolds i (i.embedValue v) (partitionRange pos neg) := by
  rw [dataHolds_partitionRange_iff]
  simp only [evalPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  exact and_congr
    ⟨fun h a ha => (evalAtom_iff (hpos a ha) i v).mp (h a ha),
     fun h a ha => (evalAtom_iff (hpos a ha) i v).mpr (h a ha)⟩
    ⟨fun h a ha hd => (by
      have h1 := (evalAtom_iff (hneg a ha) i v).mpr hd
      rw [h a ha] at h1; cases h1),
     fun h a ha => Bool.eq_false_iff.mpr fun he =>
      h a ha ((evalAtom_iff (hneg a ha) i v).mp he)⟩

theorem exists_vennPartition {dm : DatatypeMap} (i : Interpretation dm) (y : i.Data)
    (atoms : List DataRange) :
    ∃ pq ∈ vennPartitions atoms, dataHolds i y (partitionRange pq.1 pq.2) := by
  classical
  have haux : ∃ pq ∈ allPartitions atoms,
      (∀ a ∈ pq.1, dataHolds i y a) ∧ (∀ a ∈ pq.2, ¬ dataHolds i y a) := by
    induction atoms with
    | nil => exact ⟨([], []), List.mem_singleton_self _, by simp, by simp⟩
    | cons a rest ih =>
      obtain ⟨⟨p, n⟩, hpn, hp, hn⟩ := ih
      by_cases ha : dataHolds i y a
      · refine ⟨(a :: p, n), List.mem_flatMap.mpr ⟨(p, n), hpn, by simp⟩, ?_, hn⟩
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · exact hp x hx'
      · refine ⟨(p, a :: n), List.mem_flatMap.mpr ⟨(p, n), hpn, by simp⟩, hp, ?_⟩
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · exact hn x hx'
  obtain ⟨pq, hpq, h1, h2⟩ := haux
  exact ⟨pq, List.mem_eraseDups.mpr hpq, (dataHolds_partitionRange_iff i y pq.1 pq.2).mpr ⟨h1, h2⟩⟩

private theorem allPartitions_unique {dm : DatatypeMap} {i : Interpretation dm} {y : i.Data}
    {atoms : List DataRange} {p₁ n₁ p₂ n₂ : List DataRange}
    (hm₁ : (p₁, n₁) ∈ allPartitions atoms) (hm₂ : (p₂, n₂) ∈ allPartitions atoms)
    (hp₁ : ∀ a ∈ p₁, dataHolds i y a) (hn₁ : ∀ a ∈ n₁, ¬ dataHolds i y a)
    (hp₂ : ∀ a ∈ p₂, dataHolds i y a) (hn₂ : ∀ a ∈ n₂, ¬ dataHolds i y a) :
    (p₁, n₁) = (p₂, n₂) := by
  induction atoms generalizing p₁ n₁ p₂ n₂ with
  | nil =>
    simp only [allPartitions, List.mem_singleton] at hm₁ hm₂
    exact hm₁.trans hm₂.symm
  | cons a rest ih =>
    simp only [allPartitions, List.mem_flatMap] at hm₁ hm₂
    obtain ⟨⟨pa₁, na₁⟩, hmem₁, hcase₁⟩ := hm₁
    obtain ⟨⟨pa₂, na₂⟩, hmem₂, hcase₂⟩ := hm₂
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hcase₁ hcase₂
    rcases hcase₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hcase₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have heq := ih hmem₁ hmem₂
        (fun x hx => hp₁ x (List.mem_cons_of_mem _ hx)) hn₁
        (fun x hx => hp₂ x (List.mem_cons_of_mem _ hx)) hn₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rfl
    · exact (hn₂ a (List.mem_cons_self ..) (hp₁ a (List.mem_cons_self ..))).elim
    · exact (hn₁ a (List.mem_cons_self ..) (hp₂ a (List.mem_cons_self ..))).elim
    · have heq := ih hmem₁ hmem₂
        hp₁ (fun x hx => hn₁ x (List.mem_cons_of_mem _ hx))
        hp₂ (fun x hx => hn₂ x (List.mem_cons_of_mem _ hx))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rfl

theorem vennPartitions_unique {dm : DatatypeMap} {i : Interpretation dm} {y : i.Data}
    {atoms : List DataRange} {pq₁ pq₂ : List DataRange × List DataRange}
    (hm₁ : pq₁ ∈ vennPartitions atoms) (hm₂ : pq₂ ∈ vennPartitions atoms)
    (h₁ : dataHolds i y (partitionRange pq₁.1 pq₁.2))
    (h₂ : dataHolds i y (partitionRange pq₂.1 pq₂.2)) : pq₁ = pq₂ := by
  rcases pq₁ with ⟨p₁, n₁⟩
  rcases pq₂ with ⟨p₂, n₂⟩
  obtain ⟨hp₁, hn₁⟩ := (dataHolds_partitionRange_iff i y p₁ n₁).mp h₁
  obtain ⟨hp₂, hn₂⟩ := (dataHolds_partitionRange_iff i y p₂ n₂).mp h₂
  exact allPartitions_unique (List.mem_eraseDups.mp hm₁) (List.mem_eraseDups.mp hm₂)
    hp₁ hn₁ hp₂ hn₂

def evalOnPartition (pos : List DataRange) : DataRange → Bool
  | .complement r => !evalOnPartition pos r
  | .intersection a b => evalOnPartition pos a && evalOnPartition pos b
  | .union a b => evalOnPartition pos a || evalOnPartition pos b
  | a => pos.contains a

theorem evalOnPartition_iff {dm : DatatypeMap} {i : Interpretation dm} {y : i.Data}
    {atoms pos neg : List DataRange}
    (hpart : (pos, neg) ∈ vennPartitions atoms)
    (hy : dataHolds i y (partitionRange pos neg))
    {d : DataRange} (hd : ∀ a ∈ atomsOfDataRange d, a ∈ atoms) :
    evalOnPartition pos d = true ↔ dataHolds i y d := by
  obtain ⟨_, _, hcov, _⟩ := mem_vennPartitions_sub hpart
  obtain ⟨hpos, hneg⟩ := (dataHolds_partitionRange_iff i y pos neg).mp hy
  induction d with
  | complement r ih =>
    simp only [evalOnPartition, Bool.not_eq_true', Bool.eq_false_iff, dataHolds]
    exact not_congr (ih hd)
  | intersection a b iha ihb =>
    simp only [evalOnPartition, Bool.and_eq_true, dataHolds]
    refine and_congr (iha fun x hx => hd x ?_) (ihb fun x hx => hd x ?_)
    · exact List.mem_eraseDups.mpr (List.mem_append_left _ hx)
    · exact List.mem_eraseDups.mpr (List.mem_append_right _ hx)
  | union a b iha ihb =>
    simp only [evalOnPartition, Bool.or_eq_true, dataHolds]
    refine or_congr (iha fun x hx => hd x ?_) (ihb fun x hx => hd x ?_)
    · exact List.mem_eraseDups.mpr (List.mem_append_left _ hx)
    · exact List.mem_eraseDups.mpr (List.mem_append_right _ hx)
  | datatype t =>
    have hmem : .datatype t ∈ atoms := hd _ (List.mem_singleton_self _)
    simp only [evalOnPartition, List.contains_iff_mem]
    exact ⟨fun hp => hpos _ hp, fun hh => (hcov _ hmem).resolve_right fun hn => hneg _ hn hh⟩
  | restriction t fs =>
    have hmem : .restriction t fs ∈ atoms := hd _ (List.mem_singleton_self _)
    simp only [evalOnPartition, List.contains_iff_mem]
    exact ⟨fun hp => hpos _ hp, fun hh => (hcov _ hmem).resolve_right fun hn => hneg _ hn hh⟩
  | oneOf ls =>
    have hmem : .oneOf ls ∈ atoms := hd _ (List.mem_singleton_self _)
    simp only [evalOnPartition, List.contains_iff_mem]
    exact ⟨fun hp => hpos _ hp, fun hh => (hcov _ hmem).resolve_right fun hn => hneg _ hn hh⟩

/-! ### 7. Bounded witness sampling for atomic Venn partitions -/

def oneOfValuesOfAtom : DataRange → List Value
  | .oneOf ls => (decodeLiteralsList ls).getD []
  | _ => []

def allOneOfValues (atoms : List DataRange) : List Value :=
  atoms.flatMap oneOfValuesOfAtom

def negIntBoundsOfAtom : DataRange → List IntegerBounds
  | .oneOf ls =>
    ((decodeLiteralsList ls).getD []).filterMap fun
      | .number q => if q.den == 1 then some { lower := some q.num, upper := some q.num } else none
      | _ => none
  | a =>
    match extractIntAtomBounds a with
    | some b => [b]
    | none => []

def vennIntSet (pos neg : List DataRange) : List IntegerBounds :=
  let posBounds := pos.filterMap extractIntAtomBounds
  let base : IntegerBounds := posBounds.foldr IntegerBounds.intersect {}
  let negBounds := neg.flatMap negIntBoundsOfAtom
  foldSubtractBounds [base] negBounds

theorem mem_vennIntSet_iff (pos neg : List DataRange) (z : Int) :
    (∃ b ∈ vennIntSet pos neg, b.contains z) ↔
      (∀ a ∈ pos, ∀ b, extractIntAtomBounds a = some b → b.contains z) ∧
      (∀ a ∈ neg, ∀ b ∈ negIntBoundsOfAtom a, ¬ b.contains z) := by
  unfold vennIntSet
  rw [mem_foldSubtractBounds_iff]
  simp only [List.mem_singleton, exists_eq_left, List.mem_flatMap]
  have hpos : ∀ (ps : List DataRange),
      ((ps.filterMap extractIntAtomBounds).foldr IntegerBounds.intersect {}).contains z ↔
      (∀ a ∈ ps, ∀ b, extractIntAtomBounds a = some b → b.contains z) := by
    intro ps
    induction ps with
    | nil => simp [IntegerBounds.contains]
    | cons a tail ih =>
      simp only [List.filterMap_cons]
      cases hb : extractIntAtomBounds a with
      | none =>
        simp only [ih, List.forall_mem_cons, hb, reduceCtorEq, false_imp_iff, implies_true, true_and]
      | some b =>
        simp only [List.foldr_cons, IntegerBounds.contains_intersect, ih, List.forall_mem_cons,
          hb, Option.some.injEq, forall_eq']
  rw [hpos]
  exact and_congr Iff.rfl
    ⟨fun h a ha b hb => h b ⟨a, ha, hb⟩,
     fun h b ⟨a, ha, hb⟩ => h a ha b hb⟩

def ratWitness (k : Nat) : Value :=
  .number (mkRat 1 (k + 2))

private theorem ratWitness_den (k : Nat) : (mkRat 1 (k + 2)).den = k + 2 := by
  have hne : k + 2 ≠ 0 := by omega
  rw [Rat.den_mkRat, ite_eq_right hne]
  have hgcd : (k + 2).gcd (Int.natAbs 1) = 1 := Nat.gcd_one_right (k + 2)
  rw [hgcd, Nat.div_one]

private theorem ratWitness_inj {k₁ k₂ : Nat} (h : ratWitness k₁ = ratWitness k₂) : k₁ = k₂ := by
  have hq : mkRat 1 (k₁ + 2) = mkRat 1 (k₂ + 2) := Value.number.inj h
  have hd := congrArg Rat.den hq
  rw [ratWitness_den, ratWitness_den] at hd
  omega

private def repStr (k : Nat) : String :=
  String.ofList (List.replicate k 'a')

private theorem repStr_inj {k₁ k₂ : Nat} (h : repStr k₁ = repStr k₂) : k₁ = k₂ := by
  have hl := congrArg String.length h
  simpa [repStr, String.length] using hl

private def repBytes (k : Nat) : List UInt8 :=
  List.replicate k 0

private theorem repBytes_inj {k₁ k₂ : Nat} (h : repBytes k₁ = repBytes k₂) : k₁ = k₂ := by
  have hl := congrArg List.length h
  simpa [repBytes] using hl

def vennCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  let M := K + (allOneOfValues neg).length
  let bools := [Value.boolean false, Value.boolean true]
  let oneOfs := allOneOfValues pos ++ allOneOfValues neg
  let ints := (sampleIntSet K (vennIntSet pos neg)).map Value.integer
  let strs := (List.range M).map fun k => Value.string (repStr k)
  let uris := (List.range M).map fun k => Value.anyURI (repStr k)
  let xmls := (List.range M).map fun k => Value.xmlLiteral (repStr k)
  let hexs := (List.range M).map fun k => Value.hexBinary (repBytes k)
  let b64s := (List.range M).map fun k => Value.base64Binary (repBytes k)
  let rats := (List.range M).map ratWitness
  bools ++ oneOfs ++ ints ++ strs ++ uris ++ xmls ++ hexs ++ b64s ++ rats

def samplePartition (K : Nat) (pos neg : List DataRange) : List Value :=
  (((vennCandidates K pos neg).eraseDups).filter (evalPartition pos neg)).take K

theorem samplePartition_nodup (K : Nat) (pos neg : List DataRange) :
    (samplePartition K pos neg).Nodup :=
  (List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _))

theorem samplePartition_length_le (K : Nat) (pos neg : List DataRange) :
    (samplePartition K pos neg).length ≤ K :=
  List.length_take_le K _

theorem samplePartition_sound {K : Nat} {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    {v : Value} (hv : v ∈ samplePartition K pos neg)
    (i : Interpretation datatypeMap) :
    dataHolds i (i.embedValue v) (partitionRange pos neg) := by
  have hmem := List.mem_of_mem_take hv
  have heval := (List.mem_filter.mp hmem).2
  exact (evalPartition_iff hpos hneg i v).mp heval

private theorem filter_length_le_of_sub_eraseDups {α : Type} [DecidableEq α]
    (xs cands : List α) (pred : α → Bool) (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ cands) :
    (xs.filter pred).length ≤ (cands.eraseDups.filter pred).length := by
  refine (List.filter_sublist.nodup hnd).length_le_of_subset fun x hx => ?_
  obtain ⟨hm, hp⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (hsub x hm), hp⟩

private theorem evalAtom_oneOf_mem {ls : List Literal} {v : Value}
    (h : evalAtom (.oneOf ls) v = true) :
    v ∈ oneOfValuesOfAtom (.oneOf ls) := by
  simp only [evalAtom, oneOfValuesOfAtom] at h ⊢
  cases hd : decodeLiteralsList ls with
  | none => simp [hd] at h
  | some vs =>
    simp only [hd, List.contains_iff_mem] at h
    exact h

private theorem evalAtom_oneOf_not_mem {ls : List Literal} {v : Value}
    (hnot : v ∉ oneOfValuesOfAtom (.oneOf ls)) :
    evalAtom (.oneOf ls) v = false := by
  cases h : evalAtom (.oneOf ls) v with
  | false => rfl
  | true => exact (hnot (evalAtom_oneOf_mem h)).elim

private theorem checkValue_integerSubtype_iff {t : IRI} {b : IntegerBounds}
    (ht : integerBounds t = some b) (v : Value) :
    checkValue t v = true ↔ ∃ z : Int, b.contains z ∧ v = .integer z := by
  rw [checkValue_iff, valueSpace_integerSubtype_iff ht]

private theorem extractIntAtomBounds_evalAtom_iff {a : DataRange} {b : IntegerBounds}
    (hb : extractIntAtomBounds a = some b) (v : Value) :
    evalAtom a v = true ↔ ∃ z : Int, b.contains z ∧ v = .integer z := by
  cases a with
  | datatype t =>
    simp only [extractIntAtomBounds] at hb
    have hne : t ≠ literalDatatype := by
      intro rfl
      have : integerBounds literalDatatype = none := by decide
      rw [this] at hb; cases hb
    simp only [evalAtom, beq_false_of_ne hne]
    exact checkValue_integerSubtype_iff hb v
  | restriction t fs =>
    cases v with
    | number q =>
      simp only [evalAtom, hb, decide_eq_true_eq]
      constructor
      · rintro ⟨hden, hz⟩
        refine ⟨q.num, hz, ?_⟩
        simp only [Value.integer]; congr 1; apply Rat.ext <;> simp [hden]
      · rintro ⟨z, hz, heq⟩
        have hq : q = Rat.ofInt z := Value.number.inj heq
        subst hq
        exact ⟨rfl, hz⟩
    | _ =>
      simp only [evalAtom, hb, Bool.false_eq_true, false_iff]
      rintro ⟨z, _, heq⟩; cases heq
  | _ => cases hb

private theorem evalAtom_ratWitness_false {a : DataRange}
    (ha : isExactAtomicDataRange a = true)
    (hne : a ≠ .datatype literalDatatype)
    (k : Nat) (hnot : ratWitness k ∉ oneOfValuesOfAtom a) :
    evalAtom a (ratWitness k) = false := by
  cases a with
  | datatype t =>
    have hne' : t ≠ literalDatatype := fun h => hne (congrArg DataRange.datatype h)
    simp only [isExactAtomicDataRange, Bool.or_eq_true, beq_iff_eq] at ha
    simp only [evalAtom, beq_false_of_ne hne']
    rcases ha with (((((((rfl | rfl) | hint) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact (hne' rfl).elim
    · rfl
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hint
      cases hc : checkValue t (ratWitness k) with
      | false => rfl
      | true =>
        obtain ⟨z, _, heq⟩ := (checkValue_integerSubtype_iff hb (ratWitness k)).mp hc
        have hden := congrArg Rat.den (Value.number.inj heq)
        rw [ratWitness_den] at hden
        simp at hden
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  | restriction t fs =>
    simp only [evalAtom]
    cases extractIntAtomBounds (.restriction t fs) with
    | none => rfl
    | some b =>
      simp only [ratWitness, decide_eq_false_iff_not, not_and]
      intro hden
      rw [ratWitness_den] at hden
      omega
  | oneOf ls => exact evalAtom_oneOf_not_mem hnot
  | _ => cases ha

private theorem mem_allOneOfValues_of_mem {atoms : List DataRange} {a : DataRange} {v : Value}
    (ha : a ∈ atoms) (hv : v ∈ oneOfValuesOfAtom a) : v ∈ allOneOfValues atoms :=
  List.mem_flatMap.mpr ⟨a, ha, hv⟩

private theorem embedded_of_nonLiteral_atom {a : DataRange}
    (ha : isExactAtomicDataRange a = true) (hne : a ≠ .datatype literalDatatype)
    {i : Interpretation datatypeMap} {y : i.Data} (hy : dataHolds i y a) :
    ∃ v : Value, i.embedValue v = y := by
  cases a with
  | datatype t =>
    have hne' : t ≠ literalDatatype := fun h => hne (congrArg DataRange.datatype h)
    have hsup : datatypeMap.builtin t := exactDatatype_supported ha hne'
    obtain ⟨v, _, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy
    exact ⟨v, rfl⟩
  | restriction t fs =>
    have his := extractIntAtomBounds_isSome_of_restriction ha
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp his
    obtain ⟨z, _, rfl⟩ := (extractIntAtomBounds_iff hb i y).mp hy
    exact ⟨.integer z, rfl⟩
  | oneOf ls =>
    simp only [isExactAtomicDataRange] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    obtain ⟨v, _, rfl⟩ := (decodeLiteralsList_iff hvs i y).mp hy
    exact ⟨v, rfl⟩
  | _ => cases ha

private theorem evalAtom_nonOneOf_cases {a : DataRange}
    (ha : isExactAtomicDataRange a = true)
    (hnoOneOf : ∀ ls, a ≠ .oneOf ls) :
    a = .datatype literalDatatype ∨
    a = .datatype (xsd "boolean") ∨
    (∃ b, extractIntAtomBounds a = some b) ∨
    a = .datatype (xsd "string") ∨
    a = .datatype (xsd "anyURI") ∨
    a = .datatype (rdf "XMLLiteral") ∨
    a = .datatype (xsd "hexBinary") ∨
    a = .datatype (xsd "base64Binary") := by
  cases a with
  | datatype t =>
    simp only [isExactAtomicDataRange, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with (((((((rfl | rfl) | hint) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hint
      exact .inr (.inr (.inl ⟨b, hb⟩))
    · exact .inr (.inr (.inr (.inl rfl)))
    · exact .inr (.inr (.inr (.inr (.inl rfl))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  | restriction t fs =>
    have his := extractIntAtomBounds_isSome_of_restriction ha
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp his
    exact .inr (.inr (.inl ⟨b, hb⟩))
  | oneOf ls => exact (hnoOneOf ls rfl).elim
  | _ => cases ha

private theorem evalAtom_integer_iff {a : DataRange}
    (ha : isExactAtomicDataRange a = true) (z : Int) :
    evalAtom a (.integer z) = true ↔
      (a = .datatype literalDatatype ∨
       (.integer z ∈ oneOfValuesOfAtom a) ∨
       (∃ b, extractIntAtomBounds a = some b ∧ b.contains z)) := by
  by_cases hone : ∃ ls, a = .oneOf ls
  · obtain ⟨ls, rfl⟩ := hone
    simp only [isExactAtomicDataRange] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    simp [evalAtom, oneOfValuesOfAtom, extractIntAtomBounds, hvs]
  · have hno : ∀ ls, a ≠ .oneOf ls := fun ls h => hone ⟨ls, h⟩
    have hnoMem : .integer z ∉ oneOfValuesOfAtom a := by
      cases a <;> simp [oneOfValuesOfAtom]
      rename_i ls; exact (hno ls rfl).elim
    rcases evalAtom_nonOneOf_cases ha hno with
      rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
    · have hnone : extractIntAtomBounds (.datatype literalDatatype) = none := by decide
      simp [evalAtom, hnone]
    · have hnone : extractIntAtomBounds (.datatype (xsd "boolean")) = none := by decide
      have hc : checkValue (xsd "boolean") (.integer z) = false := rfl
      have hne : xsd "boolean" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]
    · rw [extractIntAtomBounds_evalAtom_iff hb (.integer z)]
      have hne : a ≠ .datatype literalDatatype := by
        intro rfl; have : extractIntAtomBounds (.datatype literalDatatype) = none := by decide
        rw [this] at hb; cases hb
      simp only [hne, hnoMem, hb, Option.some.injEq, false_or]
      exact ⟨fun ⟨z', hz', heq⟩ => by
        have hzeq : z' = z := (congrArg Rat.num (Value.number.inj heq)).symm
        subst hzeq; exact ⟨b, rfl, hz'⟩,
        fun ⟨b', hb', hz⟩ => by subst hb'; exact ⟨z, hz, rfl⟩⟩
    · have hnone : extractIntAtomBounds (.datatype (xsd "string")) = none := by decide
      have hc : checkValue (xsd "string") (.integer z) = false := rfl
      have hne : xsd "string" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]
    · have hnone : extractIntAtomBounds (.datatype (xsd "anyURI")) = none := by decide
      have hc : checkValue (xsd "anyURI") (.integer z) = false := rfl
      have hne : xsd "anyURI" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]
    · have hnone : extractIntAtomBounds (.datatype (rdf "XMLLiteral")) = none := by decide
      have hc : checkValue (rdf "XMLLiteral") (.integer z) = false := rfl
      have hne : rdf "XMLLiteral" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]
    · have hnone : extractIntAtomBounds (.datatype (xsd "hexBinary")) = none := by decide
      have hc : checkValue (xsd "hexBinary") (.integer z) = false := rfl
      have hne : xsd "hexBinary" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]
    · have hnone : extractIntAtomBounds (.datatype (xsd "base64Binary")) = none := by decide
      have hc : checkValue (xsd "base64Binary") (.integer z) = false := rfl
      have hne : xsd "base64Binary" ≠ literalDatatype := by decide
      simp [evalAtom, hnoMem, hnone, hc, hne]

private theorem evalAtom_neg_integer_iff {a : DataRange}
    (ha : isExactAtomicDataRange a = true)
    (hnolit : a ≠ .datatype literalDatatype) (z : Int) :
    evalAtom a (.integer z) = false ↔
      ∀ b ∈ negIntBoundsOfAtom a, ¬ b.contains z := by
  rw [← Bool.not_eq_true, evalAtom_integer_iff ha z]
  simp only [hnolit, false_or, not_or]
  cases a with
  | oneOf ls =>
    simp only [isExactAtomicDataRange] at ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    simp only [oneOfValuesOfAtom, negIntBoundsOfAtom, extractIntAtomBounds, hvs, Option.getD_some,
      reduceCtorEq, false_and, exists_false, List.mem_filterMap]
    constructor
    · intro hnot b ⟨v, hv, hfb⟩
      cases v with
      | number q =>
        simp only at hfb
        split at hfb
        · rename_i hden
          cases hfb
          have hq : q = Rat.ofInt q.num := by
            apply Rat.ext <;> simp [beq_iff_eq.mp hden]
          intro hcon
          simp only [IntegerBounds.contains, Option.elim] at hcon
          have hzeq : q.num = z := by omega
          subst hzeq
          exact hnot.1 (hq ▸ hv)
        · cases hfb
      | _ => simp at hfb
    · intro hall
      refine ⟨fun hv => ?_, not_false⟩
      exact hall { lower := some z, upper := some z }
        ⟨.integer z, hv, by simp⟩ ⟨Int.le_refl _, Int.le_refl _⟩
  | datatype t =>
    have hno : .integer z ∉ oneOfValuesOfAtom (.datatype t) := by simp [oneOfValuesOfAtom]
    simp only [hno, negIntBoundsOfAtom]
    cases hb : extractIntAtomBounds (.datatype t) with
    | none => simp
    | some b => simp
  | restriction t fs =>
    have hno : .integer z ∉ oneOfValuesOfAtom (.restriction t fs) := by simp [oneOfValuesOfAtom]
    simp only [hno, negIntBoundsOfAtom]
    cases hb : extractIntAtomBounds (.restriction t fs) with
    | none => simp
    | some b => simp
  | _ => cases ha

private theorem infinite_family_ge_K {pos neg : List DataRange} (K : Nat)
    (mkVal : Nat → Value) (hinj : ∀ {k₁ k₂}, mkVal k₁ = mkVal k₂ → k₁ = k₂)
    (hsub : ∀ x ∈ (List.range (K + (allOneOfValues neg).length)).map mkVal,
      x ∈ vennCandidates K pos neg)
    (heval : ∀ k, mkVal k ∉ allOneOfValues neg → evalPartition pos neg (mkVal k) = true) :
    K ≤ ((vennCandidates K pos neg).eraseDups.filter (evalPartition pos neg)).length := by
  let xs := (List.range (K + (allOneOfValues neg).length)).map mkVal
  have hnd : xs.Nodup := nodup_map_inj hinj List.nodup_range
  have h1 := filter_pred_length_ge_of_avoid xs (allOneOfValues neg) (evalPartition pos neg) hnd
    (fun x hx hnb => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact heval k hnb)
  have h2 := filter_length_le_of_sub_eraseDups xs (vennCandidates K pos neg) (evalPartition pos neg) hnd hsub
  have hlen : xs.length = K + (allOneOfValues neg).length := by simp [xs]
  omega

private theorem evalPartition_infinite_sort {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    (hnoOneOfPos : ∀ a ∈ pos, ∀ ls, a ≠ .oneOf ls)
    (_hnolit : ∀ a ∈ neg, a ≠ .datatype literalDatatype)
    {v₀ v : Value} (hnotInt : ∀ z, v ≠ .integer z) (hnotInt₀ : ∀ z, v₀ ≠ .integer z)
    (hnotNegOneOf : v ∉ allOneOfValues neg)
    (hposEv : ∀ a ∈ pos, evalAtom a v₀ = true)
    (hnegEv : ∀ a ∈ neg, evalAtom a v₀ = false)
    (hagree : ∀ t : IRI,
      (t = xsd "boolean" ∨ t = xsd "string" ∨ t = xsd "anyURI" ∨
       t = rdf "XMLLiteral" ∨ t = xsd "hexBinary" ∨ t = xsd "base64Binary") →
      checkValue t v = checkValue t v₀) :
    evalPartition pos neg v = true := by
  have hAtomEq (a : DataRange) (ha : isExactAtomicDataRange a = true)
      (hno : ∀ ls, a ≠ .oneOf ls) : evalAtom a v = evalAtom a v₀ := by
    rcases evalAtom_nonOneOf_cases ha hno with
      rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hagree (xsd "boolean") (.inl rfl)
    · have hf1 : evalAtom a v = false := by
        cases h1 : evalAtom a v with
        | false => rfl
        | true =>
          obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb v).mp h1
          exact (hnotInt z heq).elim
      have hf0 : evalAtom a v₀ = false := by
        cases h0 : evalAtom a v₀ with
        | false => rfl
        | true =>
          obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb v₀).mp h0
          exact (hnotInt₀ z heq).elim
      exact hf1.trans hf0.symm
    · exact hagree (xsd "string") (.inr (.inl rfl))
    · exact hagree (xsd "anyURI") (.inr (.inr (.inl rfl)))
    · exact hagree (rdf "XMLLiteral") (.inr (.inr (.inr (.inl rfl))))
    · exact hagree (xsd "hexBinary") (.inr (.inr (.inr (.inr (.inl rfl)))))
    · exact hagree (xsd "base64Binary") (.inr (.inr (.inr (.inr (.inr rfl)))))
  simp only [evalPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [hAtomEq a (hpos a ha) (hnoOneOfPos a ha)]
    exact hposEv a ha
  · by_cases hone : ∃ ls, a = .oneOf ls
    · obtain ⟨ls, rfl⟩ := hone
      exact evalAtom_oneOf_not_mem (fun hm => hnotNegOneOf (mem_allOneOfValues_of_mem ha hm))
    · rw [hAtomEq a (hneg a ha) (fun ls h => hone ⟨ls, h⟩)]
      exact hnegEv a ha

private theorem cover_of_evalPartition {K : Nat} {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    {v₀ : Value} (hv₀ : evalPartition pos neg v₀ = true)
    (ha₀ : ∃ a₀ ∈ pos, a₀ ≠ .datatype literalDatatype) :
    K ≤ ((vennCandidates K pos neg).eraseDups.filter (evalPartition pos neg)).length ∨
      v₀ ∈ vennCandidates K pos neg := by
  obtain ⟨hposAll, hnegAll⟩ := Bool.and_eq_true_iff.mp hv₀
  have hposEv (a : DataRange) (ha : a ∈ pos) : evalAtom a v₀ = true :=
    List.all_eq_true.mp hposAll a ha
  have hnegEv (a : DataRange) (ha : a ∈ neg) : evalAtom a v₀ = false := by
    have h := List.all_eq_true.mp hnegAll a ha
    simpa only [Bool.not_eq_true'] using h
  have hnolit (a : DataRange) (ha : a ∈ neg) : a ≠ .datatype literalDatatype := by
    intro rfl
    have := hnegEv (.datatype literalDatatype) ha
    simp [evalAtom] at this
  by_cases honePos : ∃ ls, DataRange.oneOf ls ∈ pos
  · obtain ⟨ls, hls⟩ := honePos
    have hmem : v₀ ∈ allOneOfValues pos :=
      mem_allOneOfValues_of_mem hls (evalAtom_oneOf_mem (hposEv (.oneOf ls) hls))
    refine .inr ?_
    simp only [vennCandidates, List.mem_append]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.inl hmem))))))))
  · have hnoOneOfPos (a : DataRange) (ha : a ∈ pos) (ls : List Literal) : a ≠ .oneOf ls :=
      fun h => honePos ⟨ls, h ▸ ha⟩
    obtain ⟨a₀, ha₀Mem, ha₀Ne⟩ := ha₀
    have ha₀Ev := hposEv a₀ ha₀Mem
    cases v₀ with
    | boolean b =>
      refine .inr ?_
      simp only [vennCandidates, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (by cases b <;> simp))))))))
    | float _ | double _ | dateTime _ | irrational _ =>
      rcases evalAtom_nonOneOf_cases (hpos a₀ ha₀Mem) (hnoOneOfPos a₀ ha₀Mem) with
        rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
      · exact (ha₀Ne rfl).elim
      · cases ha₀Ev
      · obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb _).mp ha₀Ev; cases heq
      · cases ha₀Ev
      · cases ha₀Ev
      · cases ha₀Ev
      · cases ha₀Ev
      · cases ha₀Ev
    | number q =>
      have hqInt : q.den = 1 := by
        rcases evalAtom_nonOneOf_cases (hpos a₀ ha₀Mem) (hnoOneOfPos a₀ ha₀Mem) with
          rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
        · exact (ha₀Ne rfl).elim
        · cases ha₀Ev
        · obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb _).mp ha₀Ev
          have hq : q = Rat.ofInt z := Value.number.inj heq
          subst hq; rfl
        · cases ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
      have hqEq : Value.number q = Value.integer q.num := by
        simp only [Value.integer]; congr 1; apply Rat.ext <;> simp [hqInt]
      have hposOnlyInt (a : DataRange) (ha : a ∈ pos) :
          a = .datatype literalDatatype ∨ ∃ b, extractIntAtomBounds a = some b := by
        have hev : evalAtom a (.integer q.num) = true := hqEq ▸ hposEv a ha
        rcases (evalAtom_integer_iff (hpos a ha) q.num).mp hev with rfl | h1 | ⟨b, hb, _⟩
        · exact .inl rfl
        · cases a <;> simp [oneOfValuesOfAtom] at h1
          rename_i ls; exact (hnoOneOfPos _ ha ls rfl).elim
        · exact .inr ⟨b, hb⟩
      have hevalInt (z : Int) :
          evalPartition pos neg (.integer z) = true ↔
            ∃ b ∈ vennIntSet pos neg, b.contains z := by
        rw [mem_vennIntSet_iff]
        simp only [evalPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
        refine and_congr ?_ ?_
        · constructor
          · intro h a ha b hb
            have hev := (evalAtom_integer_iff (hpos a ha) z).mp (h a ha)
            rcases hev with rfl | h1 | ⟨b', hb', hcon⟩
            · have : extractIntAtomBounds (.datatype literalDatatype) = none := by decide
              rw [this] at hb; cases hb
            · cases a <;> simp [oneOfValuesOfAtom] at h1
              rename_i ls; exact (hnoOneOfPos _ ha ls rfl).elim
            · rw [hb] at hb'; cases hb'; exact hcon
          · intro h a ha
            rw [evalAtom_integer_iff (hpos a ha) z]
            rcases hposOnlyInt a ha with rfl | ⟨b, hb⟩
            · exact .inl rfl
            · exact .inr (.inr ⟨b, hb, h a ha b hb⟩)
        · exact ⟨fun h a ha => (evalAtom_neg_integer_iff (hneg a ha) (hnolit a ha) z).mp (h a ha),
                 fun h a ha => (evalAtom_neg_integer_iff (hneg a ha) (hnolit a ha) z).mpr (h a ha)⟩
      let sInts := sampleIntSet K (vennIntSet pos neg)
      by_cases hlt : sInts.length < K
      · have hqIn : ∃ b ∈ vennIntSet pos neg, b.contains q.num :=
          (hevalInt q.num).mp (hqEq ▸ hv₀)
        have hmem : q.num ∈ sInts := sampleIntSet_complete_of_lt K _ hlt hqIn
        refine .inr ?_
        rw [hqEq]
        simp only [vennCandidates, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (List.mem_map_of_mem hmem)))))))
      · refine .inl ?_
        let xs := sInts.map Value.integer
        have hnd : xs.Nodup := nodup_map_inj
          (fun h => congrArg Rat.num (Value.number.inj h)) (sampleIntSet_nodup K _)
        have hsub : ∀ x ∈ xs, x ∈ vennCandidates K pos neg := fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hx))))))
        have hall : (xs.filter (evalPartition pos neg)).length = xs.length := by
          have hfeq : xs.filter (evalPartition pos neg) = xs :=
            List.filter_eq_self.mpr fun x hx => by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
              exact (hevalInt z).mpr (sampleIntSet_sound K _ hz)
          rw [hfeq]
        have hle := filter_length_le_of_sub_eraseDups xs (vennCandidates K pos neg)
          (evalPartition pos neg) hnd hsub
        have hlen : xs.length = sInts.length := List.length_map Value.integer
        omega
    | plainLiteral s lang =>
      have hlang : lang = "" := by
        rcases evalAtom_nonOneOf_cases (hpos a₀ ha₀Mem) (hnoOneOfPos a₀ ha₀Mem) with
          rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
        · exact (ha₀Ne rfl).elim
        · cases ha₀Ev
        · obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb _).mp ha₀Ev; cases heq
        · have hne : xsd "string" ≠ literalDatatype := by decide
          simp only [evalAtom, beq_false_of_ne hne] at ha₀Ev
          obtain ⟨s', hs'⟩ := (valueSpace_string_iff _).mp ((checkValue_iff _ _).mp ha₀Ev)
          exact (Value.plainLiteral.inj hs').2
        · cases ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
      subst hlang
      refine .inl (infinite_family_ge_K K (fun k => Value.string (repStr k))
        (fun h => repStr_inj (Value.plainLiteral.inj h).1)
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inl (.inl (.inl (.inl (.inr hx))))))
        fun k hnb => evalPartition_infinite_sort hpos hneg hnoOneOfPos hnolit
          (fun _ h => by cases h) (fun _ h => by cases h) hnb hposEv hnegEv
          (fun t ht => by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))
    | anyURI s =>
      refine .inl (infinite_family_ge_K K (fun k => Value.anyURI (repStr k))
        (fun h => repStr_inj (Value.anyURI.inj h))
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inl (.inl (.inl (.inr hx)))))
        fun k hnb => evalPartition_infinite_sort hpos hneg hnoOneOfPos hnolit
          (fun _ h => by cases h) (fun _ h => by cases h) hnb hposEv hnegEv
          (fun t ht => by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))
    | xmlLiteral s =>
      have hcanonS : checkValue (rdf "XMLLiteral") (.xmlLiteral s) = true := by
        rcases evalAtom_nonOneOf_cases (hpos a₀ ha₀Mem) (hnoOneOfPos a₀ ha₀Mem) with
          rfl | rfl | ⟨b, hb⟩ | rfl | rfl | rfl | rfl | rfl
        · exact (ha₀Ne rfl).elim
        · cases ha₀Ev
        · obtain ⟨z, _, heq⟩ := (extractIntAtomBounds_evalAtom_iff hb _).mp ha₀Ev; cases heq
        · cases ha₀Ev
        · cases ha₀Ev
        · have hne : rdf "XMLLiteral" ≠ literalDatatype := by decide
          simpa [evalAtom, beq_false_of_ne hne] using ha₀Ev
        · cases ha₀Ev
        · cases ha₀Ev
      refine .inl (infinite_family_ge_K K (fun k => Value.xmlLiteral (repStr k))
        (fun h => repStr_inj (Value.xmlLiteral.inj h))
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inl (.inl (.inr hx))))
        fun k hnb => evalPartition_infinite_sort hpos hneg hnoOneOfPos hnolit
          (fun _ h => by cases h) (fun _ h => by cases h) hnb hposEv hnegEv
          (fun t ht => by
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
            · rfl
            · rfl
            · rfl
            · have hk : checkValue (rdf "XMLLiteral") (.xmlLiteral (repStr k)) = true :=
                (checkValue_iff _ _).mpr ((valueSpace_xmlLiteral_iff _).mpr
                  ⟨repStr k, checkCanonicalXMLLiteral_replicate_a k, rfl⟩)
              exact hk.trans hcanonS.symm
            · rfl
            · rfl))
    | hexBinary bs =>
      refine .inl (infinite_family_ge_K K (fun k => Value.hexBinary (repBytes k))
        (fun h => repBytes_inj (Value.hexBinary.inj h))
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inl (.inr hx)))
        fun k hnb => evalPartition_infinite_sort hpos hneg hnoOneOfPos hnolit
          (fun _ h => by cases h) (fun _ h => by cases h) hnb hposEv hnegEv
          (fun t ht => by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))
    | base64Binary bs =>
      refine .inl (infinite_family_ge_K K (fun k => Value.base64Binary (repBytes k))
        (fun h => repBytes_inj (Value.base64Binary.inj h))
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inl (.inr hx))
        fun k hnb => evalPartition_infinite_sort hpos hneg hnoOneOfPos hnolit
          (fun _ h => by cases h) (fun _ h => by cases h) hnb hposEv hnegEv
          (fun t ht => by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))

theorem samplePartition_complete_of_lt {K : Nat} {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    (hlt : (samplePartition K pos neg).length < K)
    (i : Interpretation datatypeMap) (y : i.Data)
    (hy : dataHolds i y (partitionRange pos neg)) :
    ∃ v ∈ samplePartition K pos neg, i.embedValue v = y := by
  classical
  have hfullLt : (((vennCandidates K pos neg).eraseDups).filter (evalPartition pos neg)).length < K := by
    unfold samplePartition at hlt
    rw [List.length_take] at hlt
    omega
  have htakeEq : samplePartition K pos neg =
      ((vennCandidates K pos neg).eraseDups).filter (evalPartition pos neg) :=
    List.take_of_length_le (Nat.le_of_lt hfullLt)
  obtain ⟨hyPos, hyNeg⟩ := (dataHolds_partitionRange_iff i y pos neg).mp hy
  by_cases ha₀ : ∃ a₀ ∈ pos, a₀ ≠ .datatype literalDatatype
  · obtain ⟨a₀, ha₀Mem, ha₀Ne⟩ := ha₀
    obtain ⟨v₀, rfl⟩ := embedded_of_nonLiteral_atom (hpos a₀ ha₀Mem) ha₀Ne (hyPos a₀ ha₀Mem)
    have hv₀ : evalPartition pos neg v₀ = true :=
      (evalPartition_iff hpos hneg i v₀).mpr hy
    rcases cover_of_evalPartition (K := K) hpos hneg hv₀ ⟨a₀, ha₀Mem, ha₀Ne⟩ with hge | hmem
    · omega
    · refine ⟨v₀, ?_, rfl⟩
      rw [htakeEq]
      exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr hmem, hv₀⟩
  · have hposLit : ∀ a ∈ pos, a = .datatype literalDatatype := fun a ha =>
      Classical.byContradiction fun hne => ha₀ ⟨a, ha, hne⟩
    have hnegNoLit : ∀ a ∈ neg, a ≠ .datatype literalDatatype := fun a ha hlit =>
      hyNeg a ha (hlit ▸ i.literalDatatypeExt y)
    have hge : K ≤ (((vennCandidates K pos neg).eraseDups).filter (evalPartition pos neg)).length :=
      infinite_family_ge_K K ratWitness ratWitness_inj
        (fun x hx => by
          simp only [vennCandidates, List.mem_append]
          exact .inr hx)
        (fun k hnb => by
          simp only [evalPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
          refine ⟨fun a ha => by rw [hposLit a ha]; rfl, fun a ha => ?_⟩
          exact evalAtom_ratWitness_false (hneg a ha) (hnegNoLit a ha) k
            (fun hm => hnb (mem_allOneOfValues_of_mem ha hm)))
    omega

#print axioms samplePartition_nodup
#print axioms samplePartition_length_le
#print axioms samplePartition_sound
#print axioms samplePartition_complete_of_lt
#print axioms evalOnPartition_iff
#print axioms exists_vennPartition
#print axioms vennPartitions_unique

end Termination
end Sabrina.OWL2.SROIQD
