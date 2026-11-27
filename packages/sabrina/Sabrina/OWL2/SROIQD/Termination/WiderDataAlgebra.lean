import Sabrina.OWL2.SROIQD.Termination.WiderOrderCells
import Sabrina.OWL2.SROIQD.Termination.StringFacetCells

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2 Sabrina.OWL2.Datatypes Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination

/-! The combined exact datatype sampler. Floating-point, date/time, and
string/URI lexical-facet strata use the same Venn partition interface as the
existing numeric, string, and other datatype strata. -/

def isOrderedDatatype (t : IRI) : Bool :=
  t == xsd "float" || t == xsd "double" || t == xsd "dateTime" || t == xsd "dateTimeStamp"

def isOrderedExactAtom : DataRange → Bool
  | .datatype t => isOrderedDatatype t
  | .restriction t fs => isOrderedDatatype t && fs.all (fun f =>
      (decodeLiteral f.bound).any (checkApplicableFacet t f.name))
  | _ => false

def isStringFacetExtraAtom (a : DataRange) : Bool :=
  isStringFacetExactAtom a && !legacy_isWiderExactAtom a

def isWiderExactAtom (a : DataRange) : Bool :=
  legacy_isWiderExactAtom a || isOrderedExactAtom a || isStringFacetExactAtom a

def isWiderDataRange : DataRange → Bool
  | .complement r => isWiderDataRange r
  | .intersection a b | .union a b => isWiderDataRange a && isWiderDataRange b
  | a => isWiderExactAtom a

def widerAtomsAdmissible (atoms : List DataRange) : Bool :=
  atoms.all isWiderExactAtom

private theorem orderedDatatype_supported {t : IRI} (h : isOrderedDatatype t = true) :
    supportedDatatype t = true := by
  simp only [isOrderedDatatype, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

theorem widerDatatype_supported {t : IRI} (h : isWiderExactAtom (.datatype t) = true)
    (hne : t ≠ literalDatatype) : supportedDatatype t = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact legacy_widerDatatype_supported h hne
    · exact orderedDatatype_supported h
  · exact lexicalDatatype_supported h

theorem widerRestriction_supported {t : IRI} {fs : List Facet}
    (h : isWiderExactAtom (.restriction t fs) = true) :
    supportedDatatype t = true ∧ ∀ f ∈ fs, (decodeLiteral f.bound).isSome = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact legacy_widerRestriction_supported h
    · obtain ⟨ht, hfs⟩ := Bool.and_eq_true_iff.mp h
      refine ⟨orderedDatatype_supported ht, fun f hf => ?_⟩
      have hb := List.all_eq_true.mp hfs f hf
      cases hl : decodeLiteral f.bound <;> simp [hl] at hb ⊢
  · exact stringFacetRestriction_supported h

theorem widerOneOf_decoded {ls : List Literal}
    (h : isWiderExactAtom (.oneOf ls) = true) :
    ls.all (fun l => (decodeLiteral l).isSome) = true := by
  simpa [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom, legacy_isWiderExactAtom] using h

theorem evalWiderAtom_iff {a : DataRange} (ha : isWiderExactAtom a = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalWiderAtom a v = true ↔ dataHolds i (i.embedValue v) a := by
  cases a with
  | datatype t =>
    simp only [evalWiderAtom]
    by_cases hlit : t = literalDatatype
    · subst hlit; simp [dataHolds, i.literalDatatypeExt]
    · have hsup : datatypeMap.builtin t := widerDatatype_supported ha hlit
      rw [beq_false_of_ne hlit]
      change checkValue t v = true ↔ i.datatypes t (i.embedValue v)
      rw [checkValue_iff, i.datatypeAgreement t hsup (i.embedValue v)]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
  | restriction t fs =>
    have ⟨hsup, hbounds⟩ := widerRestriction_supported ha
    simp only [evalWiderAtom, Bool.and_eq_true, List.all_eq_true, dataHolds]
    refine and_congr ?_ ?_
    · rw [checkValue_iff, i.datatypeAgreement t hsup (i.embedValue v)]
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
    · refine forall_congr' fun f => imp_congr_right fun hf => ?_
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hbounds f hf)
      simp only [hb]
      exact (facetHolds_iff_check i t f b v hb).symm
  | oneOf ls =>
    have ha : ls.all (fun l => (decodeLiteral l).isSome) = true := by
      simpa [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom, legacy_isWiderExactAtom] using ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    rw [decodeLiteralsList_iff hvs i (i.embedValue v)]
    simp only [evalWiderAtom, hvs, List.contains_iff_mem]
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw⟩
  | complement _ | intersection _ _ | union _ _ =>
    simp [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom, legacy_isWiderExactAtom] at ha

theorem evalWiderDataRange_iff {d : DataRange} (hd : isWiderDataRange d = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalWiderDataRange d v = true ↔ dataHolds i (i.embedValue v) d := by
  induction d with
  | complement r ih =>
    simp only [evalWiderDataRange, Bool.not_eq_true', Bool.eq_false_iff, dataHolds]
    exact not_congr (ih hd)
  | intersection a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalWiderDataRange, Bool.and_eq_true, dataHolds]
    exact and_congr (iha ha) (ihb hb)
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalWiderDataRange, Bool.or_eq_true, dataHolds]
    exact or_congr (iha ha) (ihb hb)
  | datatype _ | restriction _ _ | oneOf _ =>
    exact evalWiderAtom_iff hd i v

theorem evalWiderPartition_iff {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isWiderExactAtom a = true)
    (hneg : ∀ a ∈ neg, isWiderExactAtom a = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalWiderPartition pos neg v = true ↔
      dataHolds i (i.embedValue v) (partitionRange pos neg) := by
  rw [dataHolds_partitionRange_iff]
  simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine and_congr
    ⟨fun h a ha => (evalWiderAtom_iff (hpos a ha) i v).mp (h a ha),
     fun h a ha => (evalWiderAtom_iff (hpos a ha) i v).mpr (h a ha)⟩
    ⟨fun h a ha hd => ?_, fun h a ha => ?_⟩
  · have h1 := (evalWiderAtom_iff (hneg a ha) i v).mpr hd
    rw [h a ha] at h1; cases h1
  · cases h1 : evalWiderAtom a v
    · rfl
    · exact (h a ha ((evalWiderAtom_iff (hneg a ha) i v).mp h1)).elim

theorem widerEmbedded_of_nonLiteral_atom {a : DataRange}
    (ha : isWiderExactAtom a = true) (hne : a ≠ .datatype literalDatatype)
    {i : Interpretation datatypeMap} {y : i.Data} (hy : dataHolds i y a) :
    ∃ v : Value, i.embedValue v = y := by
  cases a with
  | datatype t =>
    have hne' : t ≠ literalDatatype := fun h => hne (congrArg DataRange.datatype h)
    have hsup : datatypeMap.builtin t := widerDatatype_supported ha hne'
    obtain ⟨v, _, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy
    exact ⟨v, rfl⟩
  | restriction t fs =>
    have ⟨hsup, _⟩ := widerRestriction_supported ha
    obtain ⟨v, _, rfl⟩ := (i.datatypeAgreement t hsup y).mp hy.1
    exact ⟨v, rfl⟩
  | oneOf ls =>
    have ha : ls.all (fun l => (decodeLiteral l).isSome) = true := by
      simpa [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom, legacy_isWiderExactAtom] using ha
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome ha)
    obtain ⟨v, _, rfl⟩ := (decodeLiteralsList_iff hvs i y).mp hy
    exact ⟨v, rfl⟩
  | _ => simp [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom, legacy_isWiderExactAtom] at ha

def isOrderedValue : Value → Bool
  | .float _ | .double _ | .dateTime _ => true
  | _ => false

def isLexicalValue : Value → Bool
  | .plainLiteral _ _ | .anyURI _ => true
  | _ => false

theorem checkValue_ordered_false {t : IRI} {v : Value}
    (ht : isOrderedDatatype t = true) (hv : isOrderedValue v = false) : checkValue t v = false := by
  simp only [isOrderedDatatype, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with ((rfl | rfl) | rfl) | rfl <;> cases v <;> first | rfl | cases hv

theorem checkValue_lexical_false {t : IRI} {v : Value}
    (ht : isLexicalDatatype t = true) (hv : isLexicalValue v = false) : checkValue t v = false := by
  simp only [isLexicalDatatype, isStringDatatype, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with (((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;>
    cases v <;> first | rfl | cases hv

private theorem orderedType_of_checkValue {t : IRI} {v : Value}
    (hv : isOrderedValue v = true) (hc : checkValue t v = true) : isOrderedDatatype t = true := by
  cases v <;> try (cases hv)
  case float f =>
    have h := (valueSpace_float_iff t f).mp ((checkValue_iff _ _).mp hc)
    simp [isOrderedDatatype, h.1]
  case double f =>
    have h := (valueSpace_double_iff t f).mp ((checkValue_iff _ _).mp hc)
    simp [isOrderedDatatype, h.1]
  case dateTime dt =>
    rcases ((valueSpace_dateTime_iff t dt).mp ((checkValue_iff _ _).mp hc)).2 with rfl | ⟨rfl, _⟩ <;>
      simp [isOrderedDatatype]

private theorem lexicalType_of_checkValue {t : IRI} {v : Value}
    (hv : isLexicalValue v = true) (hc : checkValue t v = true) : isLexicalDatatype t = true := by
  cases v <;> try (cases hv)
  case plainLiteral s lang =>
    rcases valueSpace_plainLiteral_iri ((checkValue_iff _ _).mp hc) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  case anyURI s =>
    rw [(valueSpace_anyURI_iff t s).mp ((checkValue_iff _ _).mp hc)]
    decide

private theorem eval_orderedAtom_false {a : DataRange} {v : Value}
    (ha : isOrderedExactAtom a = true) (hv : isOrderedValue v = false) :
    evalWiderAtom a v = false := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := by
      intro he
      subst t
      cases ha
    simp [evalWiderAtom, hne, checkValue_ordered_false ha hv]
  | restriction t fs =>
    exact Bool.and_eq_false_iff.mpr (.inl (checkValue_ordered_false (Bool.and_eq_true_iff.mp ha).1 hv))
  | _ => cases ha

private theorem eval_lexicalAtom_false {a : DataRange} {v : Value}
    (ha : isStringFacetExactAtom a = true) (hv : isLexicalValue v = false) :
    evalWiderAtom a v = false := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := by
      intro he
      subst t
      cases ha
    simp [evalWiderAtom, hne, checkValue_lexical_false ha hv]
  | restriction t fs =>
    exact Bool.and_eq_false_iff.mpr (.inl (checkValue_lexical_false (Bool.and_eq_true_iff.mp ha).1 hv))
  | _ => cases ha

private theorem stringFacetSupported_of_lenFacet {t : IRI} {f : Facet}
    (ht : isLexicalDatatype t = true) (hlen : (lenFacetBounds f).isSome = true) :
    isStringFacetSupported t f = true := by
  unfold lenFacetBounds at hlen
  cases hlf : lengthFacet f.name with
  | none => simp [hlf] at hlen
  | some lf =>
    cases hdec : decodeLiteral f.bound with
    | none => simp [hlf, hdec] at hlen
    | some bound =>
      cases bound with
      | number q =>
        cases lf <;> simp only [hlf, hdec] at hlen
        all_goals
          split at hlen
          · rename_i hq
            have hne : f.name ≠ xsd "pattern" := by
              intro heq; rw [heq] at hlf; cases hlf
            have happ : checkApplicableFacet t f.name (.number q) = true := by
              apply (checkApplicableFacet_iff t f.name (.number q)).mpr
              simp only [isLexicalDatatype, isStringDatatype, Bool.or_eq_true, beq_iff_eq] at ht
              rcases ht with (((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
              all_goals exact ⟨hq.1, hq.2, by simp [hlf]⟩
            simp [isStringFacetSupported, hdec, happ, beq_false_of_ne hne]
          · cases hlen
      | _ => cases lf <;> simp [hlf, hdec] at hlen

private theorem widerRestriction_stringFacets_supported {t : IRI} {fs : List Facet}
    (ha : isWiderExactAtom (.restriction t fs) = true) (ht : isLexicalDatatype t = true) :
    ∀ f ∈ fs, isStringFacetSupported t f = true := by
  rcases Bool.or_eq_true_iff.mp ha with ha | ha
  · rcases Bool.or_eq_true_iff.mp ha with ha | ha
    · have hnotNum : (numericBase t).isSome = false := by
        simp only [isLexicalDatatype, isStringDatatype, Bool.or_eq_true, beq_iff_eq] at ht
        rcases ht with (((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;> decide
      simp only [legacy_isWiderExactAtom, hnotNum, Bool.false_and, Bool.false_or,
        Bool.and_eq_true, List.all_eq_true] at ha
      intro f hf
      exact stringFacetSupported_of_lenFacet ht (ha.2 f hf)
    · have hnotOrd : isOrderedDatatype t = false := by
        simp only [isLexicalDatatype, isStringDatatype, Bool.or_eq_true, beq_iff_eq] at ht
        rcases ht with (((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;> decide
      simp [isOrderedExactAtom, hnotOrd] at ha
  · exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).2

private def atomDatatype : DataRange → Option IRI
  | .datatype t | .restriction t _ => some t
  | _ => none

private theorem atomDatatype_of_positive {a : DataRange} {v : Value}
    (h : evalWiderAtom a v = true) (hn : a ≠ .datatype literalDatatype)
    (he : ∀ ls, a ≠ .oneOf ls) :
    ∃ t, atomDatatype a = some t ∧ checkValue t v = true := by
  cases a with
  | datatype t =>
    have hne : t ≠ literalDatatype := fun h => hn (congrArg DataRange.datatype h)
    exact ⟨t, rfl, by simpa [evalWiderAtom, hne] using h⟩
  | restriction t fs => exact ⟨t, rfl, (Bool.and_eq_true_iff.mp h).1⟩
  | oneOf ls => exact (he ls rfl).elim
  | _ => cases h

private theorem eval_pos_of_checkValue {a : DataRange} {v : Value} {t : IRI}
    (ha : atomDatatype a = some t) (h : evalWiderAtom a v = true)
    (hn : a ≠ .datatype literalDatatype) : checkValue t v = true := by
  obtain ⟨s, hs, hc⟩ := atomDatatype_of_positive h hn (by intro ls he; subst a; cases ha)
  exact Option.some.inj (hs.symm.trans ha) ▸ hc

private def legacyAtoms (as : List DataRange) : List DataRange :=
  as.filter legacy_isWiderExactAtom

private def hasOrderedConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => (atomDatatype a).any isOrderedDatatype

private def hasStringConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => (atomDatatype a).any isStringDatatype

private def hasURIConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => atomDatatype a == some (xsd "anyURI")

private def hasStringFacetExtra (pos neg : List DataRange) : Bool :=
  (pos ++ neg).any isStringFacetExtraAtom

private def hasOneOfConstraint (pos : List DataRange) : Bool :=
  pos.any fun | .oneOf _ => true | _ => false

private def hasBoolConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => atomDatatype a == some (xsd "boolean")

private def hasFloatConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => atomDatatype a == some (xsd "float")

private def hasDoubleConstraint (pos : List DataRange) : Bool :=
  pos.any fun a => atomDatatype a == some (xsd "double")

private def hasDateConstraint (pos : List DataRange) : Bool :=
  pos.any fun a =>
    atomDatatype a == some (xsd "dateTime") || atomDatatype a == some (xsd "dateTimeStamp")

private def orderedCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  (if hasFloatConstraint pos then orderedFloatCandidates .binary32 K pos neg else []) ++
  (if hasDoubleConstraint pos then orderedFloatCandidates .binary64 K pos neg else []) ++
  (if hasDateConstraint pos then orderedDateCandidates K pos neg else [])

def widerCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  if hasOneOfConstraint pos then
    allOneOfValues pos
  else if hasBoolConstraint pos then
    [Value.boolean false, Value.boolean true]
  else if hasOrderedConstraint pos then
    orderedCandidates K pos neg
  else if hasStringFacetExtra pos neg && hasStringConstraint pos then
    stringFacetPlainCandidates K pos neg
  else if hasStringFacetExtra pos neg && hasURIConstraint pos then
    stringFacetURICandidates K pos neg
  else
    legacy_widerCandidates K (legacyAtoms pos) (legacyAtoms neg)

/-- Collect at most `K` distinct elements of `xs` satisfying `p`, stopping early
    as soon as `K` matches are found (avoiding quadratic `eraseDups` on non-matching
    candidates). Semantically equal to `(xs.eraseDups.filter p).take K`. -/
def takeDistinctFilter {α : Type} [BEq α] (K : Nat) (p : α → Bool) (xs : List α) : List α :=
  go K xs []
where
  go : Nat → List α → List α → List α
  | 0, _, acc => acc.reverse
  | _, [], acc => acc.reverse
  | rem + 1, x :: rest, acc =>
    if p x && !acc.contains x then
      go rem rest (x :: acc)
    else
      go (rem + 1) rest acc

private theorem nodup_reverse_aux {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    obtain ⟨hna, hnd⟩ := List.nodup_cons.mp h
    rw [List.reverse_cons]
    exact List.pairwise_append.mpr ⟨ih hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      intro he; subst he; exact hna (List.mem_reverse.mp hx)⟩

private theorem takeDistinctFilter_go_nodup {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool)
    (rem : Nat) (xs acc : List α) (hnd : acc.Nodup) :
    (takeDistinctFilter.go p rem xs acc).Nodup := by
  induction rem generalizing xs acc with
  | zero => simpa [takeDistinctFilter.go] using nodup_reverse_aux hnd
  | succ k ih =>
    induction xs generalizing acc with
    | nil => simpa [takeDistinctFilter.go] using nodup_reverse_aux hnd
    | cons x rest ihx =>
      unfold takeDistinctFilter.go
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hnot : x ∉ acc := fun hm => Bool.false_ne_true (hc.2 ▸ List.contains_iff_mem.mpr hm)
        exact ih rest (x :: acc) (List.nodup_cons.mpr ⟨hnot, hnd⟩)
      · exact ihx acc hnd

private theorem takeDistinctFilter_go_length_le {α : Type} [BEq α] (p : α → Bool)
    (rem : Nat) (xs acc : List α) :
    (takeDistinctFilter.go p rem xs acc).length ≤ rem + acc.length := by
  induction rem generalizing xs acc with
  | zero => simp [takeDistinctFilter.go]
  | succ k ih =>
    induction xs generalizing acc with
    | nil => simp [takeDistinctFilter.go]
    | cons x rest ihx =>
      unfold takeDistinctFilter.go
      split
      · have h := ih rest (x :: acc)
        simp only [List.length_cons] at h; omega
      · exact ihx acc

private theorem takeDistinctFilter_go_mem {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool)
    (rem : Nat) (xs acc : List α) (hacc : ∀ y ∈ acc, p y = true) :
    ∀ y ∈ takeDistinctFilter.go p rem xs acc, (y ∈ acc ∨ y ∈ xs) ∧ p y = true := by
  induction rem generalizing xs acc with
  | zero =>
    intro y hy
    simp only [takeDistinctFilter.go, List.mem_reverse] at hy
    exact ⟨Or.inl hy, hacc y hy⟩
  | succ k ih =>
    induction xs generalizing acc with
    | nil =>
      intro y hy
      simp only [takeDistinctFilter.go, List.mem_reverse] at hy
      exact ⟨Or.inl hy, hacc y hy⟩
    | cons x rest ihx =>
      intro y hy
      unfold takeDistinctFilter.go at hy
      split at hy
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have hrec := ih rest (x :: acc) (fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hc.1
          · exact hacc z hz') y hy
        refine ⟨?_, hrec.2⟩
        rcases hrec.1 with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1'
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h1'
        · exact Or.inr (List.mem_cons_of_mem _ h2)
      · have hrec := ihx acc hacc y hy
        exact ⟨hrec.1.elim Or.inl (fun hr => Or.inr (List.mem_cons_of_mem _ hr)), hrec.2⟩

private theorem takeDistinctFilter_go_acc_sub {α : Type} [BEq α] (p : α → Bool)
    (rem : Nat) (xs acc : List α) :
    ∀ z ∈ acc, z ∈ takeDistinctFilter.go p rem xs acc := by
  induction rem generalizing xs acc with
  | zero => intro z hz; simp [takeDistinctFilter.go, hz]
  | succ k ih =>
    induction xs generalizing acc with
    | nil => intro z hz; simp [takeDistinctFilter.go, hz]
    | cons u us ihl =>
      intro z hz
      unfold takeDistinctFilter.go
      split
      · exact ih us (u :: acc) z (List.mem_cons_of_mem _ hz)
      · exact ihl acc z hz

private theorem takeDistinctFilter_go_complete_of_lt {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool)
    (rem : Nat) (xs acc : List α)
    (hlt : (takeDistinctFilter.go p rem xs acc).length < rem + acc.length) :
    ∀ y ∈ xs, p y = true → y ∈ takeDistinctFilter.go p rem xs acc := by
  induction rem generalizing xs acc with
  | zero =>
    simp [takeDistinctFilter.go] at hlt
  | succ k ih =>
    induction xs generalizing acc with
    | nil => intro _ hx; cases hx
    | cons x rest ihx =>
      intro y hy hpy
      unfold takeDistinctFilter.go at hlt ⊢
      split at hlt
      · rename_i hc
        simp only [hc, ↓reduceIte]
        have hlt' : (takeDistinctFilter.go p k rest (x :: acc)).length < k + (x :: acc).length := by
          simp only [List.length_cons]; omega
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact takeDistinctFilter_go_acc_sub p k rest (y :: acc) y (List.mem_cons_self ..)
        · exact ih rest (x :: acc) hlt' y hy' hpy
      · rename_i hnc
        simp only [hnc]
        rcases List.mem_cons.mp hy with rfl | hy'
        · have hmemA : y ∈ acc := by
            simp only [hpy, Bool.true_and, Bool.not_eq_true'] at hnc
            cases hc : acc.contains y with
            | true => exact List.contains_iff_mem.mp hc
            | false => exact absurd hc hnc
          exact takeDistinctFilter_go_acc_sub p (k + 1) rest acc y hmemA
        · exact ihx acc hlt y hy' hpy

private theorem takeDistinctFilter_length_eq {α : Type} [BEq α] [LawfulBEq α]
    (K : Nat) (p : α → Bool) (xs : List α)
    (hlt : (takeDistinctFilter K p xs).length < K) :
    (xs.eraseDups.filter p).length < K := by
  have hsub : ∀ x ∈ xs.eraseDups.filter p, x ∈ takeDistinctFilter K p xs := by
    intro x hx
    obtain ⟨hxe, hpx⟩ := List.mem_filter.mp hx
    exact takeDistinctFilter_go_complete_of_lt p K xs [] (by simpa [takeDistinctFilter] using hlt)
      x (List.mem_eraseDups.mp hxe) hpx
  have hle := (List.filter_sublist.nodup (nodup_eraseDups_list xs)).length_le_of_subset hsub
  exact Nat.lt_of_le_of_lt hle hlt

def sampleWiderCell (K : Nat) (pos neg : List DataRange) : List Value :=
  takeDistinctFilter K (evalWiderPartition pos neg) (widerCandidates K pos neg)

theorem sampleWiderCell_nodup (K : Nat) (pos neg : List DataRange) :
    (sampleWiderCell K pos neg).Nodup :=
  takeDistinctFilter_go_nodup (evalWiderPartition pos neg) K _ [] List.nodup_nil

theorem sampleWiderCell_length_le (K : Nat) (pos neg : List DataRange) :
    (sampleWiderCell K pos neg).length ≤ K := by
  simpa [sampleWiderCell, takeDistinctFilter] using
    takeDistinctFilter_go_length_le (evalWiderPartition pos neg) K (widerCandidates K pos neg) []

theorem sampleWiderCell_eval {K : Nat} {pos neg : List DataRange} {v : Value}
    (hv : v ∈ sampleWiderCell K pos neg) :
    evalWiderPartition pos neg v = true :=
  (takeDistinctFilter_go_mem (evalWiderPartition pos neg) K _ [] (fun _ h => by cases h) v hv).2

theorem sampleWiderCell_sound {K : Nat} {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isWiderExactAtom a = true)
    (hneg : ∀ a ∈ neg, isWiderExactAtom a = true)
    {v : Value} (hv : v ∈ sampleWiderCell K pos neg)
    (i : Interpretation datatypeMap) :
    dataHolds i (i.embedValue v) (partitionRange pos neg) := by
  have heval := (takeDistinctFilter_go_mem (evalWiderPartition pos neg) K _ []
    (fun _ h => by cases h) v hv).2
  exact (evalWiderPartition_iff hpos hneg i v).mp heval

private theorem filteredCandidates_bound {pos neg : List DataRange}
    {xs ys : List Value} (hsub : ∀ v ∈ xs, v ∈ ys) :
    (xs.eraseDups.filter (evalWiderPartition pos neg)).length ≤
      (ys.eraseDups.filter (evalWiderPartition pos neg)).length :=
  (List.filter_sublist.nodup (nodup_eraseDups_list _)).length_le_of_subset fun v hv =>
    let ⟨hx, he⟩ := List.mem_filter.mp hv
    List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (hsub v (List.mem_eraseDups.mp hx)), he⟩

private theorem eval_legacyPartition_iff {pos neg : List DataRange}
    (hnadm : ∀ a ∈ neg, isWiderExactAtom a = true)
    {v : Value} (hv : isOrderedValue v = false)
    (hlex : hasStringFacetExtra pos neg = false ∨ isLexicalValue v = false) :
    evalWiderPartition pos (legacyAtoms neg) v = true ↔ evalWiderPartition pos neg v = true := by
  simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine and_congr Iff.rfl ?_
  constructor
  · intro he a ha
    cases h : legacy_isWiderExactAtom a
    · rcases Bool.or_eq_true_iff.mp (hnadm a ha) with ha' | ha'
      · have hord : isOrderedExactAtom a = true := by simpa [h] using ha'
        exact eval_orderedAtom_false hord hv
      · rcases hlex with hnoex | hnotlex
        · have hex : hasStringFacetExtra pos neg = true :=
            List.any_eq_true.mpr ⟨a, List.mem_append_right pos ha, by simp [isStringFacetExtraAtom, ha', h]⟩
          rw [hnoex] at hex; cases hex
        · exact eval_lexicalAtom_false ha' hnotlex
    · exact he a (List.mem_filter.mpr ⟨ha, h⟩)
  · intro he a ha
    exact he a (List.mem_filter.mp ha).1

private theorem orderedCell_cover {K : Nat} {pos neg : List DataRange} {v : Value}
    (hadm : widerAtomsAdmissible (pos ++ neg) = true)
    (i : Interpretation datatypeMap)
    (hev : evalWiderPartition pos neg v = true)
    (hsome : ∃ a ∈ pos, a ≠ .datatype literalDatatype)
    (hshort : ((widerCandidates K pos neg).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    v ∈ widerCandidates K pos neg := by
  have hp a ha := List.all_eq_true.mp hadm a (List.mem_append_left neg ha)
  have hn a ha := List.all_eq_true.mp hadm a (List.mem_append_right pos ha)
  have hpos := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hev).1
  -- Branch 1: `pos` contains a `oneOf` enumeration
  cases hOne : hasOneOfConstraint pos with
  | true =>
    unfold widerCandidates
    simp only [hOne, ↓reduceIte]
    obtain ⟨b, hb, hbo⟩ := List.any_eq_true.mp hOne
    cases b with
    | oneOf ls =>
      exact List.mem_flatMap.mpr ⟨.oneOf ls, hb, evalWiderAtom_oneOf_mem (hpos _ hb)⟩
    | _ => simp at hbo
  | false =>
    have hen : ¬ ∃ ls, DataRange.oneOf ls ∈ pos := by
      rintro ⟨ls, hl⟩
      have : hasOneOfConstraint pos = true := List.any_eq_true.mpr ⟨.oneOf ls, hl, rfl⟩
      rw [hOne] at this; cases this
    -- Branch 2: `pos` contains a `xsd:boolean` constraint
    cases hBool : hasBoolConstraint pos with
    | true =>
      unfold widerCandidates
      simp only [hOne, hBool, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp hBool
      have hbt' : atomDatatype b = some (xsd "boolean") := by
        simpa [beq_iff_eq] using hbt
      have hneLit : b ≠ .datatype literalDatatype := by
        intro he; subst he; simp [atomDatatype, literalDatatype, xsd] at hbt'
      have hcv := eval_pos_of_checkValue hbt' (hpos b hb) hneLit
      obtain ⟨bv, rfl⟩ := (valueSpace_boolean_iff v).mp ((checkValue_iff _ _).mp hcv)
      cases bv <;> simp
    | false =>
      obtain ⟨a, ha, hane⟩ := hsome
      obtain ⟨t, ht, htv⟩ := atomDatatype_of_positive (hpos a ha) hane
        (fun ls he => hen ⟨ls, he ▸ ha⟩)
      -- Branch 3: `pos` contains an ordered datatype constraint (`float`/`double`/`dateTime`)
      cases hOrd : hasOrderedConstraint pos with
      | true =>
        have hwc : widerCandidates K pos neg = orderedCandidates K pos neg := by
          simp [widerCandidates, hOne, hBool, hOrd]
        obtain ⟨b, hb, hbo⟩ := List.any_eq_true.mp hOrd
        cases htb : atomDatatype b with
        | none => simp [htb] at hbo
        | some tb =>
          have hordB : isOrderedDatatype tb = true := by simpa [htb] using hbo
          have hneLitB : b ≠ .datatype literalDatatype := by
            intro he; subst he; simp [atomDatatype] at htb; subst htb; simp [isOrderedDatatype, literalDatatype, xsd] at hordB
          have hcvB := eval_pos_of_checkValue htb (hpos b hb) hneLitB
          cases hv' : v with
          | float f =>
            subst hv'
            have htf : tb = xsd "float" :=
              ((valueSpace_float_iff tb f).mp ((checkValue_iff _ _).mp hcvB)).1
            have hhf : hasFloatConstraint pos = true :=
              List.any_eq_true.mpr ⟨b, hb, by simp [htb, htf]⟩
            have hsub : ∀ w ∈ orderedFloatCandidates .binary32 K pos neg,
                w ∈ widerCandidates K pos neg := fun w hw => by
              rw [hwc]; simp only [orderedCandidates, hhf, ↓reduceIte]
              exact List.mem_append_left _ (List.mem_append_left _ hw)
            exact hsub _ (orderedFloatCandidates_cover .binary32
              ((valueSpace_float_iff t f).mp ((checkValue_iff _ _).mp htv)).2
              hev (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
          | double f =>
            subst hv'
            have htd : tb = xsd "double" :=
              ((valueSpace_double_iff tb f).mp ((checkValue_iff _ _).mp hcvB)).1
            have hhd : hasDoubleConstraint pos = true :=
              List.any_eq_true.mpr ⟨b, hb, by simp [htb, htd]⟩
            have hsub : ∀ w ∈ orderedFloatCandidates .binary64 K pos neg,
                w ∈ widerCandidates K pos neg := fun w hw => by
              rw [hwc]; simp only [orderedCandidates, hhd, ↓reduceIte]
              exact List.mem_append_left _ (List.mem_append_right _ hw)
            exact hsub _ (orderedFloatCandidates_cover .binary64
              ((valueSpace_double_iff t f).mp ((checkValue_iff _ _).mp htv)).2
              hev (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
          | dateTime dt =>
            subst hv'
            have htdt := ((valueSpace_dateTime_iff tb dt).mp ((checkValue_iff _ _).mp hcvB)).2
            have hhdt : hasDateConstraint pos = true :=
              List.any_eq_true.mpr ⟨b, hb, by
                rcases htdt with h1 | ⟨h2, _⟩
                · simp [htb, h1]
                · simp [htb, h2]⟩
            have hsub : ∀ w ∈ orderedDateCandidates K pos neg,
                w ∈ widerCandidates K pos neg := fun w hw => by
              rw [hwc]; simp only [orderedCandidates, hhdt, ↓reduceIte]
              exact List.mem_append_right _ hw
            exact hsub _ (orderedDateCandidates_cover
              (((valueSpace_dateTime_iff t dt).mp ((checkValue_iff _ _).mp htv)).1)
              hev (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
          | _ =>
            have hnotOrdV : isOrderedValue v = false := by subst hv'; rfl
            rw [checkValue_ordered_false hordB hnotOrdV] at hcvB; cases hcvB
      | false =>
        have hnotOrdV : isOrderedValue v = false := by
          cases hv' : isOrderedValue v with
          | false => rfl
          | true =>
            have : hasOrderedConstraint pos = true :=
              List.any_eq_true.mpr ⟨a, ha, by simp [ht, orderedType_of_checkValue hv' htv]⟩
            rw [hOrd] at this; cases this
        -- Branch 4: string extra facets + string constraint in `pos`
        cases hStrEx : (hasStringFacetExtra pos neg && hasStringConstraint pos) with
        | true =>
          have hwc : widerCandidates K pos neg = stringFacetPlainCandidates K pos neg := by
            simp [widerCandidates, hOne, hBool, hOrd, hStrEx]
          simp only [Bool.and_eq_true] at hStrEx
          obtain ⟨b, hb, hbs⟩ := List.any_eq_true.mp hStrEx.2
          cases htb : atomDatatype b with
          | none => simp [htb] at hbs
          | some tb =>
            have hstrB : isStringDatatype tb = true := by simpa [htb] using hbs
            have hneLitB : b ≠ .datatype literalDatatype := by
              intro he; subst he; simp [atomDatatype] at htb; subst htb
              simp [isStringDatatype, literalDatatype, rdf, xsd] at hstrB
            have hcvB := eval_pos_of_checkValue htb (hpos b hb) hneLitB
            cases hv' : v with
            | plainLiteral s lang =>
              subst hv'
              have hsub : ∀ w ∈ stringFacetPlainCandidates K pos neg, w ∈ widerCandidates K pos neg := by
                intro w hw; rw [hwc]; exact hw
              have hsfAdm : ∀ c ∈ pos ++ neg, match c with
                  | .restriction t' fs => isStringDatatype t' = true → ∀ f ∈ fs, isStringFacetSupported t' f = true
                  | _ => True := by
                intro c hc
                cases c with
                | restriction t' fs =>
                  intro hst'
                  exact widerRestriction_stringFacets_supported (List.all_eq_true.mp hadm _ hc)
                    (by simp [isLexicalDatatype, hst'])
                | _ => trivial
              exact hsub _ (stringFacetPlainCandidates_cover hsfAdm hev
                (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
            | anyURI s =>
              subst hv'
              have h := (valueSpace_anyURI_iff tb s).mp ((checkValue_iff _ _).mp hcvB)
              subst h; simp [isStringDatatype, rdf, xsd] at hstrB
            | _ =>
              subst hv'
              rw [checkValue_lexical_false (by simp [isLexicalDatatype, hstrB]) (by rfl)] at hcvB
              cases hcvB
        | false =>
          -- Branch 5: string extra facets + anyURI constraint in `pos`
          cases hUriEx : (hasStringFacetExtra pos neg && hasURIConstraint pos) with
          | true =>
            have hwc : widerCandidates K pos neg = stringFacetURICandidates K pos neg := by
              simp [widerCandidates, hOne, hBool, hOrd, hStrEx, hUriEx]
            simp only [Bool.and_eq_true] at hUriEx
            obtain ⟨b, hb, hbu⟩ := List.any_eq_true.mp hUriEx.2
            have htb : atomDatatype b = some (xsd "anyURI") := by simpa [beq_iff_eq] using hbu
            have hneLitB : b ≠ .datatype literalDatatype := by
              intro he; subst he; simp [atomDatatype, literalDatatype, xsd] at htb
            have hcvB := eval_pos_of_checkValue htb (hpos b hb) hneLitB
            cases hv' : v with
            | anyURI s =>
              subst hv'
              have hsub : ∀ w ∈ stringFacetURICandidates K pos neg, w ∈ widerCandidates K pos neg := by
                intro w hw; rw [hwc]; exact hw
              have hsfAdm : ∀ c ∈ pos ++ neg, match c with
                  | .restriction t' fs => t' = xsd "anyURI" → ∀ f ∈ fs, isStringFacetSupported t' f = true
                  | _ => True := by
                intro c hc
                cases c with
                | restriction t' fs =>
                  intro hut'
                  exact widerRestriction_stringFacets_supported (List.all_eq_true.mp hadm _ hc)
                    (by simp [isLexicalDatatype, hut'])
                | _ => trivial
              exact hsub _ (stringFacetURICandidates_cover hsfAdm hev
                (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
            | plainLiteral s lang =>
              subst hv'
              rcases valueSpace_plainLiteral_iri ((checkValue_iff _ _).mp hcvB) with
                h | h | h | h | h | h | h | h <;> simp [rdf, xsd] at h
            | _ =>
              subst hv'
              rw [checkValue_lexical_false (by decide : isLexicalDatatype (xsd "anyURI") = true) (by rfl)] at hcvB
              cases hcvB
          | false =>
            -- Branch 6: standard legacy candidates
            have hwc : widerCandidates K pos neg = legacy_widerCandidates K (legacyAtoms pos) (legacyAtoms neg) := by
              simp [widerCandidates, hOne, hBool, hOrd, hStrEx, hUriEx]
            have hlex : hasStringFacetExtra pos neg = false ∨ isLexicalValue v = false := by
              cases hex : hasStringFacetExtra pos neg with
              | false => exact .inl rfl
              | true =>
                right
                cases hv' : v with
                | plainLiteral s lang =>
                  have hstrT : isStringDatatype t = true := by
                    rcases valueSpace_plainLiteral_iri ((checkValue_iff _ _).mp (hv' ▸ htv)) with
                      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
                  have hhas : hasStringConstraint pos = true :=
                    List.any_eq_true.mpr ⟨a, ha, by simp [ht, hstrT]⟩
                  simp [hex, hhas] at hStrEx
                | anyURI s =>
                  have huriT : t = xsd "anyURI" := (valueSpace_anyURI_iff t s).mp ((checkValue_iff _ _).mp (hv' ▸ htv))
                  have hhas : hasURIConstraint pos = true :=
                    List.any_eq_true.mpr ⟨a, ha, by simp [ht, huriT]⟩
                  simp [hex, hhas] at hUriEx
                | _ => rfl
            have hposScope : legacyAtoms pos = pos := by
              apply List.filter_eq_self.mpr
              intro b hb
              cases h : legacy_isWiderExactAtom b
              · rcases Bool.or_eq_true_iff.mp (hp b hb) with hc | hc
                · have hord : isOrderedExactAtom b = true := by simpa [h] using hc
                  have hpass := hpos b hb
                  rw [eval_orderedAtom_false hord hnotOrdV] at hpass
                  contradiction
                · rcases hlex with hnoex | hnotlex
                  · have hex : hasStringFacetExtra pos neg = true :=
                      List.any_eq_true.mpr ⟨b, List.mem_append_left neg hb, by simp [isStringFacetExtraAtom, hc, h]⟩
                    rw [hnoex] at hex; cases hex
                  · have hpass := hpos b hb
                    rw [eval_lexicalAtom_false hc hnotlex] at hpass
                    contradiction
              · rfl
            have hall : legacy_widerAtomsAdmissible (pos ++ legacyAtoms neg) = true := by
              apply List.all_eq_true.mpr
              intro b hb
              rcases List.mem_append.mp hb with hb | hb
              · exact (List.mem_filter.mp (hposScope ▸ hb)).2
              · exact (List.mem_filter.mp hb).2
            have hpart := (eval_legacyPartition_iff hn hnotOrdV hlex).mpr hev
            have hasTag (w : Value) (hw : evalWiderPartition pos (legacyAtoms neg) w = true) :
                isOrderedValue w = false := by
              cases hw' : isOrderedValue w
              · rfl
              · have hc := eval_pos_of_checkValue ht
                  (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).1 a ha) hane
                exact False.elim (by rw [checkValue_ordered_false (orderedType_of_checkValue hw' hc) hnotOrdV] at htv
                                     cases htv)
            have hasLexTag (w : Value) (hw : evalWiderPartition pos (legacyAtoms neg) w = true) :
                hasStringFacetExtra pos neg = false ∨ isLexicalValue w = false := by
              rcases hlex with hnoex | hnotlex
              · exact .inl hnoex
              · right
                cases hw' : isLexicalValue w
                · rfl
                · have hc := eval_pos_of_checkValue ht
                    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).1 a ha) hane
                  exact False.elim (by rw [checkValue_lexical_false (lexicalType_of_checkValue hw' hc) hnotlex] at htv
                                       cases htv)
            have hle : ((legacy_widerCandidates K pos (legacyAtoms neg)).eraseDups.filter
                (evalWiderPartition pos (legacyAtoms neg))).length ≤
                ((widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).length := by
              apply (List.filter_sublist.nodup (nodup_eraseDups_list _)).length_le_of_subset
              intro w hw
              obtain ⟨hm, he⟩ := List.mem_filter.mp hw
              refine List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (by rw [hwc, hposScope]; exact List.mem_eraseDups.mp hm), ?_⟩
              exact (eval_legacyPartition_iff hn (hasTag w he) (hasLexTag w he)).mp he
            rcases legacy_cover_of_evalWiderPartition (K := K) hall i hpart ⟨a, ha, hane⟩ (by
              intro dt he; rw [he] at hnotOrdV; cases hnotOrdV) with hge | hm
            · omega
            · rw [hwc, hposScope]; exact hm

/-- Below the witness cap the sampler returns every value of a supported cell
that contains a positive, non-universal datatype or enumeration. -/
theorem sampleWiderCell_complete_of_lt {K : Nat} {pos neg : List DataRange}
    (hadm : widerAtomsAdmissible (pos ++ neg) = true)
    (hlt : (sampleWiderCell K pos neg).length < K)
    (hpos : ∃ a ∈ pos, a ≠ .datatype literalDatatype)
    (i : Interpretation datatypeMap) (y : i.Data)
    (hy : dataHolds i y (partitionRange pos neg)) :
    ∃ v ∈ sampleWiderCell K pos neg, i.embedValue v = y := by
  have hp a ha := List.all_eq_true.mp hadm a (List.mem_append_left neg ha)
  have hn a ha := List.all_eq_true.mp hadm a (List.mem_append_right pos ha)
  have hshort : (((widerCandidates K pos neg).eraseDups).filter
      (evalWiderPartition pos neg)).length < K :=
    takeDistinctFilter_length_eq K (evalWiderPartition pos neg) (widerCandidates K pos neg) hlt
  obtain ⟨a, ha, hne⟩ := hpos
  obtain ⟨v, rfl⟩ := widerEmbedded_of_nonLiteral_atom (hp a ha) hne
    ((dataHolds_partitionRange_iff i y pos neg).mp hy |>.1 a ha)
  have hev := (evalWiderPartition_iff hp hn i v).mpr hy
  refine ⟨v, ?_, rfl⟩
  have hmem := orderedCell_cover hadm i hev ⟨a, ha, hne⟩ hshort
  exact takeDistinctFilter_go_complete_of_lt (evalWiderPartition pos neg) K (widerCandidates K pos neg) []
    (by simpa [sampleWiderCell, takeDistinctFilter] using hlt) v hmem hev

theorem sampleWiderCell_complete_value_of_lt {K : Nat} {pos neg : List DataRange} {v : Value}
    (hadm : widerAtomsAdmissible (pos ++ neg) = true)
    (hlt : (sampleWiderCell K pos neg).length < K)
    (hpos : ∃ a ∈ pos, a ≠ .datatype literalDatatype)
    (hv : evalWiderPartition pos neg v = true) :
    v ∈ sampleWiderCell K pos neg := by
  let i := observationInterpretation
  have hp a ha := List.all_eq_true.mp hadm a (List.mem_append_left neg ha)
  have hn a ha := List.all_eq_true.mp hadm a (List.mem_append_right pos ha)
  have hy := (evalWiderPartition_iff hp hn i v).mp hv
  obtain ⟨w, hw, he⟩ := sampleWiderCell_complete_of_lt hadm hlt hpos i (i.embedValue v) hy
  exact i.embedValue_injective he ▸ hw

#print axioms sampleWiderCell_sound
#print axioms sampleWiderCell_complete_of_lt

end Sabrina.OWL2.SROIQD.Termination.WiderData
