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

private def isOrderedValue : Value → Bool
  | .float _ | .double _ | .dateTime _ => true
  | _ => false

private def isLexicalValue : Value → Bool
  | .plainLiteral _ _ | .anyURI _ => true
  | _ => false

private theorem checkValue_ordered_false {t : IRI} {v : Value}
    (ht : isOrderedDatatype t = true) (hv : isOrderedValue v = false) : checkValue t v = false := by
  simp only [isOrderedDatatype, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with ((rfl | rfl) | rfl) | rfl <;> cases v <;> first | rfl | cases hv

private theorem checkValue_lexical_false {t : IRI} {v : Value}
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

private def orderedCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  orderedFloatCandidates .binary32 K pos neg ++ orderedFloatCandidates .binary64 K pos neg ++
  orderedDateCandidates K pos neg

def widerCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  legacy_widerCandidates K (legacyAtoms pos) (legacyAtoms neg) ++
    (if hasOrderedConstraint pos then orderedCandidates K pos neg else []) ++
    (if hasStringFacetExtra pos neg then
      (if hasStringConstraint pos then stringFacetPlainCandidates K pos neg else []) ++
      (if hasURIConstraint pos then stringFacetURICandidates K pos neg else [])
     else [])

def sampleWiderCell (K : Nat) (pos neg : List DataRange) : List Value :=
    ((widerCandidates K pos neg).eraseDups.filter (evalWiderPartition pos neg)).take K

theorem sampleWiderCell_nodup (K : Nat) (pos neg : List DataRange) :
    (sampleWiderCell K pos neg).Nodup :=
  (List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _))

theorem sampleWiderCell_length_le (K : Nat) (pos neg : List DataRange) :
    (sampleWiderCell K pos neg).length ≤ K :=
  List.length_take_le ..

theorem sampleWiderCell_sound {K : Nat} {pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isWiderExactAtom a = true)
    (hneg : ∀ a ∈ neg, isWiderExactAtom a = true)
    {v : Value} (hv : v ∈ sampleWiderCell K pos neg)
    (i : Interpretation datatypeMap) :
    dataHolds i (i.embedValue v) (partitionRange pos neg) := by
  have heval := (List.mem_filter.mp (List.mem_of_mem_take hv)).2
  exact (evalWiderPartition_iff hpos hneg i v).mp heval

private theorem filteredCandidates_bound {pos neg : List DataRange}
    {xs ys : List Value} (hsub : ∀ v ∈ xs, v ∈ ys) :
    (xs.eraseDups.filter (evalWiderPartition pos neg)).length ≤
      (ys.eraseDups.filter (evalWiderPartition pos neg)).length :=
  (List.filter_sublist.nodup (nodup_eraseDups_list _)).length_le_of_subset fun v hv =>
    let ⟨hx, he⟩ := List.mem_filter.mp hv
    List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (hsub v (List.mem_eraseDups.mp hx)), he⟩

private theorem mem_legacyCandidate_of_oneOf {K : Nat} {pos neg : List DataRange} {v : Value}
    (hv : v ∈ allOneOfValues pos) : v ∈ legacy_widerCandidates K pos neg := by
  simp only [legacy_widerCandidates, List.mem_append]
  right
  left; left; left; left; left; left; left; left; left; left; left; left; right; left
  exact hv

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
  have hcore : ∀ w ∈ legacy_widerCandidates K (legacyAtoms pos) (legacyAtoms neg),
      w ∈ widerCandidates K pos neg := fun w hw =>
    List.mem_append_left _ (List.mem_append_left _ hw)
  by_cases hen : ∃ ls, DataRange.oneOf ls ∈ pos
  · obtain ⟨ls, hl⟩ := hen
    have hkeep : legacy_isWiderExactAtom (.oneOf ls) = true := by
      simpa [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom] using hp _ hl
    have hm : DataRange.oneOf ls ∈ legacyAtoms pos := List.mem_filter.mpr ⟨hl, hkeep⟩
    have hv : v ∈ allOneOfValues (legacyAtoms pos) :=
      List.mem_flatMap.mpr ⟨DataRange.oneOf ls, hm, evalWiderAtom_oneOf_mem (hpos _ hl)⟩
    exact hcore _ (mem_legacyCandidate_of_oneOf hv)
  obtain ⟨a, ha, hane⟩ := hsome
  obtain ⟨t, ht, htv⟩ := atomDatatype_of_positive (hpos a ha) hane
    (fun ls he => hen ⟨ls, he ▸ ha⟩)
  have hordered (hv : isOrderedValue v = true) :
      ∀ w ∈ orderedCandidates K pos neg, w ∈ widerCandidates K pos neg := by
    have hhas : hasOrderedConstraint pos = true :=
      List.any_eq_true.mpr ⟨a, ha, by simp [ht, orderedType_of_checkValue hv htv]⟩
    intro w hw
    exact List.mem_append_left _ (List.mem_append_right _ (by simp only [hhas, ↓reduceIte]; exact hw))
  have ordinary (hv : isOrderedValue v = false)
      (hlex : hasStringFacetExtra pos neg = false ∨ isLexicalValue v = false) :
      v ∈ widerCandidates K pos neg := by
    have hposScope : legacyAtoms pos = pos := by
      apply List.filter_eq_self.mpr
      intro b hb
      cases h : legacy_isWiderExactAtom b
      · rcases Bool.or_eq_true_iff.mp (hp b hb) with hc | hc
        · have hord : isOrderedExactAtom b = true := by simpa [h] using hc
          have hpass := hpos b hb
          rw [eval_orderedAtom_false hord hv] at hpass
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
    have hpart := (eval_legacyPartition_iff hn hv hlex).mpr hev
    have hasTag (w : Value) (hw : evalWiderPartition pos (legacyAtoms neg) w = true) :
        isOrderedValue w = false := by
      cases hw' : isOrderedValue w
      · rfl
      · have hc := eval_pos_of_checkValue ht
          (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).1 a ha) hane
        exact False.elim (by rw [checkValue_ordered_false (orderedType_of_checkValue hw' hc) hv] at htv
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
      refine List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (hcore w ?_), ?_⟩
      · rw [hposScope]
        exact List.mem_eraseDups.mp hm
      · exact (eval_legacyPartition_iff hn (hasTag w he) (hasLexTag w he)).mp he
    rcases legacy_cover_of_evalWiderPartition (K := K) hall i hpart ⟨a, ha, hane⟩ (by
      intro dt he; rw [he] at hv; cases hv) with hge | hm
    · omega
    · apply hcore
      rwa [hposScope]
  cases v <;> try exact ordinary rfl (.inr rfl)
  case float f =>
    have hsub : ∀ w ∈ orderedFloatCandidates .binary32 K pos neg,
        w ∈ widerCandidates K pos neg := fun w hw =>
      hordered rfl w (List.mem_append_left _ (List.mem_append_left _ hw))
    have hv := ((valueSpace_float_iff t f).mp ((checkValue_iff _ _).mp htv)).2
    exact hsub _ (orderedFloatCandidates_cover .binary32 hv hev
      (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
  case double f =>
    have hsub : ∀ w ∈ orderedFloatCandidates .binary64 K pos neg,
        w ∈ widerCandidates K pos neg := fun w hw =>
      hordered rfl w (List.mem_append_left _ (List.mem_append_right _ hw))
    have hv := ((valueSpace_double_iff t f).mp ((checkValue_iff _ _).mp htv)).2
    exact hsub _ (orderedFloatCandidates_cover .binary64 hv hev
      (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
  case dateTime dt =>
    have hsub : ∀ w ∈ orderedDateCandidates K pos neg, w ∈ widerCandidates K pos neg :=
      fun w hw => hordered rfl w (List.mem_append_right _ hw)
    have hv := ((valueSpace_dateTime_iff t dt).mp ((checkValue_iff _ _).mp htv)).1
    exact hsub _ (orderedDateCandidates_cover hv hev
      (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
  case plainLiteral s lang =>
    cases hex : hasStringFacetExtra pos neg
    · exact ordinary rfl (.inl hex)
    · have hstrT : isStringDatatype t = true := by
        rcases valueSpace_plainLiteral_iri ((checkValue_iff _ _).mp htv) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hhas : hasStringConstraint pos = true :=
        List.any_eq_true.mpr ⟨a, ha, by simp [ht, hstrT]⟩
      have hsub : ∀ w ∈ stringFacetPlainCandidates K pos neg, w ∈ widerCandidates K pos neg := by
        intro w hw
        exact List.mem_append_right _ (by simp only [hex, hhas, ↓reduceIte]; exact List.mem_append_left _ hw)
      have hsfAdm : ∀ b ∈ pos ++ neg, match b with
          | .restriction t' fs => isStringDatatype t' = true → ∀ f ∈ fs, isStringFacetSupported t' f = true
          | _ => True := by
        intro b hb
        cases b with
        | restriction t' fs =>
          intro hst'
          exact widerRestriction_stringFacets_supported (List.all_eq_true.mp hadm _ hb)
            (by simp [isLexicalDatatype, hst'])
        | _ => trivial
      exact hsub _ (stringFacetPlainCandidates_cover hsfAdm hev
        (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))
  case anyURI s =>
    cases hex : hasStringFacetExtra pos neg
    · exact ordinary rfl (.inl hex)
    · have huriT : t = xsd "anyURI" := (valueSpace_anyURI_iff t s).mp ((checkValue_iff _ _).mp htv)
      have hhas : hasURIConstraint pos = true :=
        List.any_eq_true.mpr ⟨a, ha, by simp [ht, huriT]⟩
      have hsub : ∀ w ∈ stringFacetURICandidates K pos neg, w ∈ widerCandidates K pos neg := by
        intro w hw
        exact List.mem_append_right _ (by simp only [hex, hhas, ↓reduceIte]; exact List.mem_append_right _ hw)
      have hsfAdm : ∀ b ∈ pos ++ neg, match b with
          | .restriction t' fs => t' = xsd "anyURI" → ∀ f ∈ fs, isStringFacetSupported t' f = true
          | _ => True := by
        intro b hb
        cases b with
        | restriction t' fs =>
          intro hut'
          exact widerRestriction_stringFacets_supported (List.all_eq_true.mp hadm _ hb)
            (by simp [isLexicalDatatype, hut'])
        | _ => trivial
      exact hsub _ (stringFacetURICandidates_cover hsfAdm hev
        (Nat.lt_of_le_of_lt (filteredCandidates_bound hsub) hshort))

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
      (evalWiderPartition pos neg)).length < K := by
    unfold sampleWiderCell at hlt
    rw [List.length_take] at hlt
    omega
  obtain ⟨a, ha, hne⟩ := hpos
  obtain ⟨v, rfl⟩ := widerEmbedded_of_nonLiteral_atom (hp a ha) hne
    ((dataHolds_partitionRange_iff i y pos neg).mp hy |>.1 a ha)
  have hev := (evalWiderPartition_iff hp hn i v).mpr hy
  refine ⟨v, ?_, rfl⟩
  unfold sampleWiderCell
  rw [List.take_of_length_le (Nat.le_of_lt hshort)]
  exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr
    (orderedCell_cover hadm i hev ⟨a, ha, hne⟩ hshort), hev⟩

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
