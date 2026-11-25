import Sabrina.OWL2.SROIQD.Termination.RealObservations
import Sabrina.OWL2.DataRanges

/-! Pointwise preservation of datatype range lowering for the real map.
The symbolic point need only preserve the rational endpoints of the two
ranges involved in a rewrite. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Datatypes

private def facetEndpoints : DataRange → List Rat
  | .complement a => facetEndpoints a
  | .intersection a b | .union a b => facetEndpoints a ++ facetEndpoints b
  | a => rationalEndpoints a

private abbrev SymbolicData := Value ⊕ Bool

private structure Point (i : Interpretation realDatatypeMap) (y : i.Data) (qs : List Rat) where
  point : SymbolicData
  literal : ∀ v, v.isIrrationalWitness = false → (Sum.inl v = point ↔ i.embedValue (.inl v) = y)
  type : ∀ t, datatypeMap.builtin t →
    ((∃ v, valueSpace t v ∧ Sum.inl v = point) ↔ i.datatypes t y)
  facet : ∀ t f b, decodeLiteral f.bound = some b →
    (∀ r, b = .number r → r ∈ qs) →
    ((∃ v, facetSpace t f.name b v ∧ Sum.inl v = point) ↔ facetHolds i t f y)

private theorem point_exists (i : Interpretation realDatatypeMap) (y : i.Data) (qs : List Rat) :
    Nonempty (Point i y qs) := by
  classical
  by_cases ho : ∃ v : Value, v.isIrrationalWitness = false ∧ i.embedValue (.inl v) = y
  · obtain ⟨v, hv, rfl⟩ := ho
    refine ⟨⟨.inl v, ?_, ?_, ?_⟩⟩
    · intro w _
      exact ⟨fun h => congrArg (fun v => i.embedValue (.inl v)) (Sum.inl.inj h),
        fun h => congrArg Sum.inl (Sum.inl.inj (i.embedValue_injective h))⟩
    · intro t ht
      rw [i.datatypeAgreement t ht]
      constructor
      · rintro ⟨w, hw, he⟩
        exact ⟨.inl v, ⟨hv, Sum.inl.inj he ▸ hw⟩, rfl⟩
      · rintro ⟨w, hw, he⟩
        cases i.embedValue_injective he
        exact ⟨v, hw.2, rfl⟩
    · intro t f b hb _
      constructor
      · rintro ⟨w, hw, he⟩
        exact ⟨.inl b, .inl v, realDatatypeMap_lexical _ _ hb,
          ⟨hv, Sum.inl.inj he ▸ hw⟩, rfl⟩
      · rintro ⟨b', w, hb', hw, he⟩
        cases Option.some.inj ((realDatatypeMap_lexical _ _ hb).symm.trans hb')
        cases i.embedValue_injective he
        exact ⟨v, hw.2, rfl⟩
  · by_cases hc : ∃ c : IrrationalCut, i.embedValue (.inr c) = y
    · obtain ⟨c, rfl⟩ := hc
      obtain ⟨ws, hlen, _, hw⟩ := cut_has_proxies c qs 1
      obtain ⟨q, hq, hobs⟩ : ∃ q, (DecimalValue q ∧ q.den ≠ 1) ∧
          ∀ b ∈ qs, b ≤ q ↔ c.lower b := by
        cases ws with
        | nil => simp at hlen
        | cons q ws => exact ⟨q, hw q (List.mem_cons_self ..)⟩
      refine ⟨⟨.inl (.irrational q), ?_, ?_, ?_⟩⟩
      · intro v hv
        constructor
        · intro he
          cases Sum.inl.inj he
          cases hv
        · intro he
          cases i.embedValue_injective he
      · intro t ht
        rw [i.datatypeAgreement t ht]
        constructor
        · rintro ⟨w, hw, he⟩
          cases Sum.inl.inj he
          exact ⟨.inr c, ((valueSpace_irrational_iff t q).mp hw).1, rfl⟩
        · rintro ⟨w, hw, he⟩
          cases i.embedValue_injective he
          exact ⟨.irrational q, (valueSpace_irrational_iff t q).mpr ⟨hw, hq⟩, rfl⟩
      · intro t f b hb hbound
        have hf := proxyFacet_iff c q t f b hq fun r hr => hobs r (hbound r hr)
        constructor
        · rintro ⟨v, hv, he⟩
          cases Sum.inl.inj he
          exact ⟨.inl b, .inr c, realDatatypeMap_lexical _ _ hb, hf.mp hv, rfl⟩
        · rintro ⟨b', w, hb', hw, he⟩
          cases Option.some.inj ((realDatatypeMap_lexical _ _ hb).symm.trans hb')
          cases i.embedValue_injective he
          exact ⟨.irrational q, hf.mpr hw, rfl⟩
    · refine ⟨⟨.inr false, ?_, ?_, ?_⟩⟩
      · intro v hv
        exact ⟨ (fun h => nomatch h), fun h => (ho ⟨v, hv, h⟩).elim⟩
      · intro t ht
        rw [i.datatypeAgreement t ht]
        constructor
        · rintro ⟨v, _, he⟩; cases he
        · rintro ⟨v, hv, he⟩
          cases v with
          | inl v => exact (ho ⟨v, hv.1, he⟩).elim
          | inr c => exact (hc ⟨c, he⟩).elim
      · intro t f b hb _
        constructor
        · rintro ⟨v, _, he⟩; cases he
        · rintro ⟨b', v, hb', hv, he⟩
          cases Option.some.inj ((realDatatypeMap_lexical _ _ hb).symm.trans hb')
          cases v with
          | inl v => exact (ho ⟨v, hv.1, he⟩).elim
          | inr c => exact (hc ⟨c, he⟩).elim

private noncomputable def Point.view {i : Interpretation realDatatypeMap} {y : i.Data} {qs}
    (p : Point i y qs) : Interpretation datatypeMap := by
  classical
  exact {
    Object := Unit
    objectNonempty := ⟨()⟩
    Data := SymbolicData
    dataNonempty := ⟨p.point⟩
    embedValue := Sum.inl
    embedValue_injective := Sum.inl.inj
    classes := fun t _ => t = thing
    objectProperties := fun t _ _ => t = topObjectProperty
    dataProperties := fun t _ _ => t = topDataProperty
    individuals := fun _ => ()
    datatypes := fun t z => if datatypeMap.builtin t then
      ∃ v, valueSpace t v ∧ Sum.inl v = z
      else i.datatypes t y
    literalValue := fun l => match decodeLiteral l with
      | some v => .inl v
      | none => if i.literalValue l = y then p.point else
          if p.point = .inr false then .inr true else .inr false
    lexicalAgreement := fun l v h => by change decodeLiteral l = some v at h; rw [h]; rfl
    named := fun _ => True
    namedIndividual := fun _ => trivial
    thingExt := fun _ => rfl
    nothingExt := fun _ => by decide
    topObjectExt := fun _ _ => rfl
    bottomObjectExt := fun _ _ => by decide
    topDataExt := fun _ _ => rfl
    bottomDataExt := fun _ _ => by decide
    literalDatatypeExt := fun _ => by
      simp [datatypeMap.literal_not_builtin, i.literalDatatypeExt]
    datatypeAgreement := fun t ht _ => by rw [ite_eq_left ht]; exact Iff.rfl }

private theorem Point.viewType {i : Interpretation realDatatypeMap} {y : i.Data} {qs}
    (p : Point i y qs) (t : IRI) : p.view.datatypes t p.point ↔ i.datatypes t y := by
  classical
  change (if datatypeMap.builtin t then _ else _) ↔ _
  by_cases ht : datatypeMap.builtin t
  · rw [ite_eq_left ht]
    exact p.type t ht
  · rw [ite_eq_right ht]

private theorem Point.viewLiteral {i : Interpretation realDatatypeMap} {y : i.Data} {qs}
    (p : Point i y qs) (l : Literal) :
    p.view.literalValue l = p.point ↔ i.literalValue l = y := by
  classical
  change (match decodeLiteral l with | some v => Sum.inl v | none => _) = p.point ↔ _
  cases h : decodeLiteral l with
  | some v =>
    rw [i.lexicalAgreement _ _ (realDatatypeMap_lexical _ _ h)]
    exact p.literal v (decodeLiteral_not_witness h)
  | none =>
    by_cases hy : i.literalValue l = y
    · simp [hy]
    · by_cases hp : p.point = .inr false
      · simp [hy, hp]
      · simp [hy, hp, Ne.symm hp]

private theorem Point.viewFacet {i : Interpretation realDatatypeMap} {y : i.Data} {qs}
    (p : Point i y qs) (t : IRI) (f : Facet)
    (hmem : ∀ r, decodeLiteral f.bound = some (.number r) → r ∈ qs) :
    facetHolds p.view t f p.point ↔ facetHolds i t f y := by
  constructor
  · rintro ⟨b, v, hb, hv, he⟩
    exact (p.facet t f b hb (fun r hr => hmem r (hr ▸ hb))).mp ⟨v, hv, he⟩
  · rintro ⟨b, v, hb, hv, he⟩
    obtain ⟨b', hb', eq⟩ := Option.map_eq_some_iff.mp hb
    subst eq
    obtain ⟨w, hwm, hwe⟩ := (p.facet t f b' hb' (fun r hr => hmem r (hr ▸ hb'))).mpr
      ⟨.inl b', v, hb, hv, he⟩
    exact ⟨b', w, hb', hwm, hwe⟩

private theorem Point.viewRange {i : Interpretation realDatatypeMap} {y : i.Data} {qs}
    (p : Point i y qs) (r : DataRange) (hs : ∀ q ∈ facetEndpoints r, q ∈ qs) :
    dataHolds p.view p.point r ↔ dataHolds i y r := by
  induction r with
  | datatype t => exact p.viewType t
  | complement a ih => exact not_congr (ih hs)
  | intersection a b ia ib | union a b ia ib =>
    have ha := ia (fun q hq => hs q (List.mem_append_left _ hq))
    have hb := ib (fun q hq => hs q (List.mem_append_right _ hq))
    first | exact and_congr ha hb | exact or_congr ha hb
  | oneOf ls =>
    exact exists_congr fun l => and_congr Iff.rfl (p.viewLiteral l)
  | restriction t fs =>
    refine and_congr (p.viewType t) (forall_congr' fun f => imp_congr_right fun hf => ?_)
    exact p.viewFacet t f fun q hq => hs q (List.mem_filterMap.mpr ⟨f, hf, by simp [hq]⟩)

theorem lowerSmallRanges_real_iff (d : DataRange) (i : Interpretation realDatatypeMap) (y : i.Data) :
    dataHolds i y (DataRanges.lowerSmallRanges d).1 ↔ dataHolds i y d := by
  let e := (DataRanges.lowerSmallRanges d).1
  obtain ⟨p⟩ := point_exists i y (facetEndpoints e ++ facetEndpoints d)
  exact (p.viewRange e (fun _ h => List.mem_append_left _ h)).symm.trans
    (((DataRanges.lowerSmallRanges d).2 p.view p.point).trans
      (p.viewRange d (fun _ h => List.mem_append_right _ h)))

#print axioms lowerSmallRanges_real_iff

end Sabrina.OWL2.SROIQD.Termination.WiderData
