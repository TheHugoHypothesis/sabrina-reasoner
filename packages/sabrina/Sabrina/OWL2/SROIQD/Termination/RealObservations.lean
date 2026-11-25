import Sabrina.OWL2.Datatypes.RealDatatype
import Sabrina.OWL2.SROIQD.Termination.WiderDataAlgebra

/-! OWL facet bounds are literals. A finite set of atoms can observe only
the position of an irrational value relative to its rational endpoints.
This module relates those observations to the executable datatype map. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Datatypes

def rationalEndpoints : DataRange → List Rat
  | .restriction _ fs => fs.filterMap fun f =>
      match decodeLiteral f.bound with
      | some (.number b) => some b
      | _ => none
  | _ => []

private theorem cutBracket (c : IrrationalCut) (qs : List Rat) :
    ∃ a b, c.lower a ∧ ¬ c.lower b ∧
      ∀ q ∈ qs, (c.lower q → q ≤ a) ∧ (¬ c.lower q → b ≤ q) := by
  classical
  induction qs with
  | nil =>
    obtain ⟨a, ha⟩ := c.inhabited
    obtain ⟨b, hb⟩ := c.proper
    exact ⟨a, b, ha, hb, by simp⟩
  | cons q rest ih =>
    obtain ⟨a, b, ha, hb, hs⟩ := ih
    by_cases hq : c.lower q
    · rcases (Rat.le_total : q ≤ a ∨ a ≤ q) with hqa | haq
      · exact ⟨a, b, ha, hb, by simpa [hq, hqa] using hs⟩
      · refine ⟨q, b, hq, hb, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨fun _ => Rat.le_refl, fun h => (h hq).elim⟩
        · exact ⟨fun h => Rat.le_trans ((hs r hr).1 h) haq, (hs r hr).2⟩
    · rcases (Rat.le_total : b ≤ q ∨ q ≤ b) with hbq | hqb
      · exact ⟨a, b, ha, hb, by simpa [hq, hbq] using hs⟩
      · refine ⟨a, q, ha, hq, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨fun h => (hq h).elim, fun _ => Rat.le_refl⟩
        · exact ⟨(hs r hr).1, fun h => Rat.le_trans hqb ((hs r hr).2 h)⟩

theorem cut_has_proxies (c : IrrationalCut) (qs : List Rat) (K : Nat) :
    ∃ ws : List Rat, ws.length = K ∧ ws.Nodup ∧ ∀ q ∈ ws,
      (DecimalValue q ∧ q.den ≠ 1) ∧ ∀ b ∈ qs, b ≤ q ↔ c.lower b := by
  classical
  obtain ⟨a, b, ha, hb, hs⟩ := cutBracket c qs
  obtain ⟨ws, hlen, hnd, hw⟩ := properDecimalWitnesses_between K (c.separated ha hb)
  refine ⟨ws, hlen, hnd, fun q hq => ?_⟩
  obtain ⟨hlo, hhi, hdec, hden⟩ := hw q hq
  refine ⟨⟨hdec, hden⟩, fun bound hbound => ?_⟩
  constructor
  · intro hle
    exact Classical.byContradiction fun hn =>
      Rat.not_le.mpr hhi (Rat.le_trans ((hs bound hbound).2 hn) hle)
  · intro h
    exact Rat.le_trans ((hs bound hbound).1 h) (Rat.le_of_lt hlo)

private theorem nextEndpoint (q : Rat) (qs : List Rat) :
    ∃ u, q < u ∧ ∀ b ∈ qs, q < b → u ≤ b := by
  induction qs with
  | nil =>
    refine ⟨q + 1, ?_, by simp⟩
    have h : q + 0 < q + 1 := Rat.add_lt_add_left.mpr (by decide : (0 : Rat) < 1)
    simpa only [Rat.add_zero] using h
  | cons b bs ih =>
    obtain ⟨u, hqu, hu⟩ := ih
    by_cases h : q < b ∧ b < u
    · refine ⟨b, h.1, fun x hx hqx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Rat.le_refl
      · exact Rat.le_trans (Rat.le_of_lt h.2) (hu x hx hqx)
    · refine ⟨u, hqu, fun x hx hqx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Rat.not_lt.mp fun hb => h ⟨hqx, hb⟩
      · exact hu x hx hqx

theorem realize_proxy (q : Rat) (qs : List Rat) :
    ∃ c : IrrationalCut, c.lower q ∧ ∀ b ∈ qs, b ≤ q ↔ c.lower b := by
  obtain ⟨u, hqu, hu⟩ := nextEndpoint q qs
  obtain ⟨c, hq, hn⟩ := IrrationalCut.exists_between hqu
  refine ⟨c, hq, fun b hb => ?_⟩
  constructor
  · intro hle
    by_cases he : b = q
    · exact he ▸ hq
    · exact c.downward (Rat.not_le.mp fun h => he (Rat.le_antisymm hle h)) hq
  · intro h
    by_cases hle : b ≤ q
    · exact hle
    · have huc := hu b hb (Rat.not_le.mp hle)
      exact False.elim (Rat.not_le.mpr (c.separated h hn) huc)

theorem proxyFacet_iff (c : IrrationalCut) (q : Rat) (t : IRI) (f : Facet) (b : Value)
    (hq : DecimalValue q ∧ q.den ≠ 1)
    (hobs : ∀ r, b = .number r → (r ≤ q ↔ c.lower r)) :
    facetSpace t f.name b (.irrational q) ↔ realFacetSpace t f.name (.inl b) (.inr c) := by
  cases b <;> try exact Iff.rfl
  case number r =>
    have hr := hobs r rfl
    simp only [facetSpace, realFacetSpace, valueSpace_irrational_iff, hq.1, true_and]
    exact and_congr ⟨And.left, fun h => ⟨h, hq.2⟩⟩ (exists_congr fun order => and_congr Iff.rfl (by
      cases order <;> simp [OrderFacet.holdsAbove, IrrationalCut.atFacet, ← Rat.not_le, hr]))

private theorem refType_iff (i : Interpretation realDatatypeMap)
    (t : IRI) (hs : supportedDatatype t = true) (v : RealValue) :
    i.datatypes t (i.embedValue v) ↔ realValueSpace t v := by
  rw [i.datatypeAgreement t hs]
  exact ⟨fun ⟨w, hw, he⟩ => i.embedValue_injective he ▸ hw, fun h => ⟨v, h, rfl⟩⟩

private theorem refFacet_iff (i : Interpretation realDatatypeMap) (t : IRI) (f : Facet)
    {b : Value} (hb : decodeLiteral f.bound = some b) (v : RealValue) :
    facetHolds i t f (i.embedValue v) ↔ realFacetSpace t f.name (.inl b) v := by
  constructor
  · rintro ⟨_, _, hl, hs, hv⟩
    have he := Option.some.inj ((realDatatypeMap_lexical _ _ hb).symm.trans hl)
    subst he
    cases i.embedValue_injective hv
    exact hs
  · intro h
    exact ⟨.inl b, v, realDatatypeMap_lexical _ _ hb, h, rfl⟩

private theorem refEnumeration_iff (i : Interpretation realDatatypeMap) (y : i.Data)
    {ls : List Literal} {vs : List Value} (hv : decodeLiteralsList ls = some vs) :
    dataHolds i y (.oneOf ls) ↔ ∃ w ∈ vs, i.embedValue (.inl w) = y := by
  induction ls generalizing vs with
  | nil => cases hv; simp [dataHolds]
  | cons l ls ih =>
    simp only [decodeLiteralsList] at hv
    obtain ⟨v, hdl, hv'⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hv'
    have hl := i.lexicalAgreement _ _ (realDatatypeMap_lexical _ _ hdl)
    simp only [dataHolds, List.mem_cons, exists_eq_or_imp, hl]
    exact or_congr Iff.rfl (ih hws)

theorem realEmbedded_of_nonLiteralAtom {a : DataRange} (ha : isWiderExactAtom a = true)
    (hn : a ≠ .datatype literalDatatype) {i : Interpretation realDatatypeMap} {y : i.Data}
    (hy : dataHolds i y a) :
    ∃ v, i.embedValue v = y ∧ ∀ q, v ≠ .inl (.irrational q) := by
  cases a with
  | datatype t =>
    have hs := widerDatatype_supported ha (fun h => hn (congrArg DataRange.datatype h))
    obtain ⟨v, hv, he⟩ := (i.datatypeAgreement t hs y).mp hy
    exact ⟨v, he, fun q h => Bool.noConfusion ((h ▸ hv).1)⟩
  | restriction t fs =>
    obtain ⟨v, hv, he⟩ := (i.datatypeAgreement t (widerRestriction_supported ha).1 y).mp hy.1
    exact ⟨v, he, fun q h => Bool.noConfusion ((h ▸ hv).1)⟩
  | oneOf ls =>
    obtain ⟨vs, hv⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome (widerOneOf_decoded ha))
    obtain ⟨v, hmem, he⟩ := (refEnumeration_iff i y hv).mp hy
    obtain ⟨l, _, hdl⟩ := decodeLiteralsList_mem_decoded hv hmem
    exact ⟨.inl v, he, fun q h => decodeLiteral_ne_irrational l q (Sum.inl.inj h ▸ hdl)⟩
  | _ => cases ha

/-- For ordinary values and unused witness codes outside the real value space,
the original atom test has the same meaning in the cut model. -/
theorem evalWiderAtom_real_ordinary {a : DataRange} (ha : isWiderExactAtom a = true)
    (i : Interpretation realDatatypeMap) (v : Value)
    (hv : ∀ t, valueSpace t v → v.isIrrationalWitness = false) :
    evalWiderAtom a v = true ↔ dataHolds i (i.embedValue (.inl v)) a := by
  cases a with
  | datatype t =>
    by_cases h : t = literalDatatype
    · subst h; simp [evalWiderAtom, dataHolds, i.literalDatatypeExt]
    · simp only [evalWiderAtom, beq_false_of_ne h, Bool.false_eq_true, ↓reduceIte, checkValue_iff, dataHolds,
        refType_iff i t (widerDatatype_supported ha h), realValueSpace]
      exact ⟨fun ht => ⟨hv t ht, ht⟩, And.right⟩
  | restriction t fs =>
    obtain ⟨hs, hfs⟩ := widerRestriction_supported ha
    simp only [evalWiderAtom, Bool.and_eq_true, List.all_eq_true, checkValue_iff, dataHolds,
      refType_iff i t hs, realValueSpace]
    have hf (f : Facet) (h : f ∈ fs) (ht : valueSpace t v) :
        (match decodeLiteral f.bound with
          | some b => checkFacet t f.name b v
          | none => false) = true ↔
          facetHolds i t f (i.embedValue (.inl v)) := by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hfs f h)
      rw [refFacet_iff i t f hb]
      simp [hb, checkFacet_iff, realFacetSpace, hv t ht]
    exact ⟨fun ⟨ht, hall⟩ => ⟨⟨hv t ht, ht⟩, fun f h => (hf f h ht).mp (hall f h)⟩,
      fun ⟨⟨_, ht⟩, hall⟩ => ⟨ht, fun f h => (hf f h ht).mpr (hall f h)⟩⟩
  | oneOf ls =>
    obtain ⟨vs, hb⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome (widerOneOf_decoded ha))
    rw [refEnumeration_iff i _ hb]
    simp only [evalWiderAtom, hb, List.contains_iff_mem]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have eq := Sum.inl.inj (i.embedValue_injective he)
      exact eq ▸ hw
  | _ => cases ha

/-- Real order facets can observe the side of each rational bound. Equality
to the bound is impossible for an irrational cut. -/
theorem evalWiderAtom_real_cut {a : DataRange} (ha : isWiderExactAtom a = true)
    (i : Interpretation realDatatypeMap) (c : IrrationalCut) (q : Rat)
    (hvalid : DecimalValue q ∧ q.den ≠ 1)
    (hobs : ∀ b ∈ rationalEndpoints a, b ≤ q ↔ c.lower b) :
    evalWiderAtom a (.irrational q) = true ↔ dataHolds i (i.embedValue (.inr c)) a := by
  cases a with
  | datatype t =>
    by_cases h : t = literalDatatype
    · subst h; simp [dataHolds, evalWiderAtom, i.literalDatatypeExt]
    · simp only [evalWiderAtom, beq_false_of_ne h, Bool.false_eq_true, ↓reduceIte,
        checkValue_iff, valueSpace_irrational_iff, dataHolds,
        refType_iff i t (widerDatatype_supported ha h), realValueSpace]
      exact ⟨And.left, fun he => ⟨he, hvalid⟩⟩
  | restriction t fs =>
    obtain ⟨hs, hfs⟩ := widerRestriction_supported ha
    simp only [evalWiderAtom, Bool.and_eq_true, List.all_eq_true, checkValue_iff,
      valueSpace_irrational_iff, dataHolds, refType_iff i t hs, realValueSpace]
    by_cases ht : t = owlReal
    · subst t
      rw [show (owlReal = owlReal ∧ DecimalValue q ∧ q.den ≠ 1) ↔ True from
        ⟨fun _ => trivial, fun _ => ⟨rfl, hvalid⟩⟩]
      simp only [true_and]
      refine forall_congr' fun f => imp_congr_right fun hf => ?_
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hfs f hf)
      rw [refFacet_iff i owlReal f hb]
      simp only [hb, checkFacet_iff]
      exact proxyFacet_iff c q owlReal f b hvalid fun r hr =>
        hobs r (List.mem_filterMap.mpr ⟨f, hf, by simp [hb, hr]⟩)
    · simp [ht]
  | oneOf ls =>
    obtain ⟨vs, hv⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome (widerOneOf_decoded ha))
    rw [refEnumeration_iff i _ hv]
    simp only [evalWiderAtom, hv, List.contains_iff_mem]
    constructor
    · intro hmem
      obtain ⟨l, _, hl⟩ := decodeLiteralsList_mem_decoded hv hmem
      exact (decodeLiteral_ne_irrational l q hl).elim
    · rintro ⟨v, _, h⟩
      cases i.embedValue_injective h
  | _ => cases ha

end Sabrina.OWL2.SROIQD.Termination.WiderData
