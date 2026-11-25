import Sabrina.OWL2.SROIQD.Termination.RealNormalization
import Sabrina.OWL2.SROIQD.Termination.WiderDataReduction

/-! Correctness of the finite data encoding against a datatype map whose
irrational values range over all irrational Dedekind cuts. The real witnesses
are shared across the encoded model and realized injectively. In the other
direction every nonempty irrational cell can fill the full witness cap. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Datatypes
open Sabrina.RoleChains (findRank)
open Sabrina.OWL2.SROIQD.Termination.BlockedForest

private theorem evalPartition_from_atoms {i : Interpretation realDatatypeMap}
    {y : i.Data} {v : Value} {pos neg : List DataRange}
    (ha : ∀ a ∈ pos ++ neg, evalWiderAtom a v = true ↔ dataHolds i y a)
    (h : dataHolds i y (partitionRange pos neg)) : evalWiderPartition pos neg v = true := by
  obtain ⟨hp, hn⟩ := (dataHolds_partitionRange_iff i y pos neg).mp h
  refine Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr (fun a h => ?_),
    List.all_eq_true.mpr (fun a h => ?_)⟩
  · exact (ha a (List.mem_append_left _ h)).mpr (hp a h)
  · cases he : evalWiderAtom a v
    · rfl
    · exact (hn a h ((ha a (List.mem_append_right _ h)).mp he)).elim

private theorem realCoverSmall {K : Nat} {pos neg : List DataRange}
    (hadm : widerAtomsAdmissible (pos ++ neg) = true)
    (hlt : (sampleWiderCell K pos neg).length < K)
    (hpos : ∃ a ∈ pos, a ≠ .datatype literalDatatype)
    (i : Interpretation realDatatypeMap) (y : i.Data)
    (hy : dataHolds i y (partitionRange pos neg)) :
    ∃ v ∈ sampleWiderCell K pos neg, i.embedValue (.inl v) = y := by
  have head := hpos
  obtain ⟨a, ha, hn⟩ := head
  have adm := List.all_eq_true.mp hadm
  obtain ⟨v, rfl, hordinary⟩ :=
    realEmbedded_of_nonLiteralAtom (adm a (List.mem_append_left _ ha)) hn
      ((dataHolds_partitionRange_iff i y pos neg).mp hy |>.1 a ha)
  cases v with
  | inl v =>
    have htag : v.isIrrationalWitness = false := by
      cases v <;> try rfl
      case irrational q => exact (hordinary q rfl).elim
    have he := evalPartition_from_atoms (v := v)
      (fun a ha => evalWiderAtom_real_ordinary (adm a ha) i v (fun _ _ => htag)) hy
    exact ⟨v, sampleWiderCell_complete_value_of_lt hadm hlt hpos he, rfl⟩
  | inr c =>
    let endpoints := (pos ++ neg).flatMap rationalEndpoints
    obtain ⟨ws, hlen, hnd, hw⟩ := cut_has_proxies c endpoints K
    have hsub : ∀ v ∈ ws.map Value.irrational, v ∈ sampleWiderCell K pos neg := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      obtain ⟨hqv, hc⟩ := hw q hq
      have he := evalPartition_from_atoms (v := .irrational q)
        (fun a ha => evalWiderAtom_real_cut (adm a ha) i c q hqv fun bound hb =>
          hc bound (List.mem_flatMap.mpr ⟨a, ha, hb⟩)) hy
      exact sampleWiderCell_complete_value_of_lt hadm hlt hpos he
    have hdn : (ws.map Value.irrational).Nodup := hnd.map Value.irrational
      (fun _ _ hne he => hne (Value.irrational.inj he))
    have hle := StringLengthCells.length_le_of_nodup_subset hdn hsub
    simp only [List.length_map, hlen] at hle
    omega

private def realSource {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) (i : Interpretation realDatatypeMap) : enc.Source i where
  value v := i.embedValue (.inl v)
  injective h := Sum.inl.inj (i.embedValue_injective h)
  literal l _ v hv := i.lexicalAgreement l (.inl v) (realDatatypeMap_lexical l v hv)
  evalLiteral v hv r hr := by
    obtain ⟨l, _, hl⟩ := enc.literal_decoded h hv
    exact evalWiderDataRange_of_atoms i _ v r fun a ha =>
      evalWiderAtom_real_ordinary (enc.atom_admitted h (hr a ha)) i v
        (fun _ _ => decodeLiteral_not_witness hl)
  coverSmall ha hl hp y hy := realCoverSmall ha hl hp i y hy

private def concreteValues (enc : WiderEncoding) : List Value :=
  enc.litVals ++ enc.cells.flatMap (fun c => c.values.getD [])

private theorem usesValue_iff (enc : WiderEncoding) (v : Value) :
    enc.UsesValue v ↔ v ∈ concreteValues enc := by
  simp only [WiderEncoding.UsesValue, concreteValues, List.mem_append, List.mem_flatMap]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨c, hc, ws, hws, hv⟩
    exact ⟨c, hc, by simpa [hws] using hv⟩
  · rintro ⟨c, hc, hv⟩
    cases h : c.values with
    | none => simp [h] at hv
    | some ws => exact ⟨c, hc, ws, h, by simpa [h] using hv⟩

private def observationPoints (enc : WiderEncoding) : List Rat :=
  enc.atoms.flatMap rationalEndpoints ++ (concreteValues enc).filterMap
    (fun | .irrational q => some q | _ => none)

private noncomputable def realizedCut (enc : WiderEncoding) (q : Rat) : IrrationalCut :=
  Classical.choose (realize_proxy q (observationPoints enc))

private theorem cutObserves (enc : WiderEncoding) (q : Rat) :
    (realizedCut enc q).lower q ∧
      ∀ b ∈ observationPoints enc, b ≤ q ↔ (realizedCut enc q).lower b :=
  Classical.choose_spec (realize_proxy q (observationPoints enc))

private noncomputable def realizeValue (enc : WiderEncoding) : Value → RealValue
  | .irrational q => if DecimalValue q ∧ q.den ≠ 1 ∧ .irrational q ∈ concreteValues enc
      then .inr (realizedCut enc q) else .inl (.irrational q)
  | v => .inl v

private theorem lt_realizedCut_ne {enc : WiderEncoding} {q r : Rat}
    (hr : .irrational r ∈ concreteValues enc) (hlt : q < r) :
    realizedCut enc q ≠ realizedCut enc r := by
  intro he
  have hm : r ∈ observationPoints enc :=
    List.mem_append_right _ (List.mem_filterMap.mpr ⟨.irrational r, hr, rfl⟩)
  have hlow := (cutObserves enc r).1
  have hle := ((cutObserves enc q).2 r hm).mpr (he.symm ▸ hlow)
  exact Rat.not_le.mpr hlt hle

private theorem realizeValue_inj {enc : WiderEncoding} {v w : Value}
    (h : realizeValue enc v = realizeValue enc w) : v = w := by
  cases v <;> cases w <;> simp only [realizeValue, Sum.inl.injEq] at h
  all_goals first
    | exact h
    | (split at h <;> cases h)
    | (split at h <;> split at h <;> try contradiction <;> try exact Sum.inl.inj h)
  all_goals try exact Sum.inl.inj h
  rename_i q r hq hr
  have he := Sum.inr.inj h
  rcases (Rat.le_total : q ≤ r ∨ r ≤ q) with hqr | hrq
  · by_cases hrq : r ≤ q
    · exact congrArg Value.irrational (Rat.le_antisymm hqr hrq)
    · exact (lt_realizedCut_ne hr.2.2 (Rat.not_le.mp hrq) he).elim
  · by_cases hqr : q ≤ r
    · exact congrArg Value.irrational (Rat.le_antisymm hqr hrq)
    · exact (lt_realizedCut_ne hq.2.2 (Rat.not_le.mp hqr) he.symm).elim

private noncomputable def realTarget {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) : enc.Target realDatatypeMap where
  value := realizeValue enc
  injective := realizeValue_inj
  builtin := fun _ hs => hs
  lexical l v hv := by
    have he := realDatatypeMap_lexical l v hv
    cases v <;> try exact he
    case irrational q => exact (decodeLiteral_ne_irrational l q hv).elim
  evalAtom a ha v hv i := by
    have admitted := enc.atom_admitted h ha
    cases v <;> try exact evalWiderAtom_real_ordinary admitted i _ (fun _ _ => rfl)
    case irrational q =>
      have hm := (usesValue_iff enc _).mp hv
      by_cases hq : DecimalValue q ∧ q.den ≠ 1
      · rw [realizeValue, ite_eq_left ⟨hq.1, hq.2, hm⟩]
        exact evalWiderAtom_real_cut admitted i (realizedCut enc q) q hq fun b hb =>
          (cutObserves enc q).2 b
            (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, ha, hb⟩))
      · rw [realizeValue, ite_eq_right (fun h => hq ⟨h.1, h.2.1⟩)]
        exact evalWiderAtom_real_ordinary admitted i _ fun t ht =>
          (hq ((valueSpace_irrational_iff t q).mp ht).2).elim

/-- Exact abstraction for the normalized wider fragment, with keys and
qualified cardinalities preserved in both directions. -/
theorem encodeWiderData_real_sat_iff {p p' : Problem} (h : encodeWiderData p = some p') :
    p'.Sat ↔ p.SatWith realDatatypeMap := by
  obtain ⟨enc, henc, rfl⟩ := Option.map_eq_some_iff.mp h
  constructor
  · exact enc.decode_with_target henc (realTarget henc)
  · rintro ⟨i, hm, x, hx⟩
    exact enc.encode_of_source henc i (realSource henc i) hm hx

theorem encodeWiderData_symbolic_real_iff {p p' : Problem} (h : encodeWiderData p = some p') :
    p.Sat ↔ p.SatWith realDatatypeMap :=
  (encodeWiderData_sat_iff h).symm.trans (encodeWiderData_real_sat_iff h)

/-- Execute the wider encoding with correctness against the cut model.
Lowers both `owl:bottomObjectProperty`/`owl:bottomDataProperty` and
`owl:topDataProperty` before finite-cap data encoding. -/
def decideRealProblem? (p : Problem) : Option Bool :=
  (lowerTopData? p.lowerBottom).bind fun p1 =>
    (encodeWiderData p1).bind fun q =>
      let lowered := q.lowerAllTopRoleAxioms
      (findRank lowered.rules lowered.chains).bind fun rank =>
        if h : lowered.isSROIQDWithTop rank = true then
          some (decideSROIQDWithTopBool h)
        else
          none

theorem decideRealProblem_iff {p : Problem} {answer : Bool}
    (h : decideRealProblem? p = some answer) :
    answer = true ↔ p.SatWith realDatatypeMap := by
  simp only [decideRealProblem?, Option.bind_eq_some_iff] at h
  obtain ⟨p1, hp1, q, hq, rank, _, hanswer⟩ := h
  split at hanswer
  · rename_i hadmitted
    cases hanswer
    exact (decideSROIQDWithTopBool_iff hadmitted).trans
      (q.lowerAllTopRoleAxioms_sat_iff.trans
        ((encodeWiderData_real_sat_iff hq).trans
          ((lowerTopData_real_sat_iff hp1).trans p.lowerBottom_satWith_iff)))
  · contradiction

theorem satisfiable_real_iff_satWith (p : Problem) (hroot : p.root = .top) :
    Satisfiable realDatatypeMap p.toOntology ↔ p.SatWith realDatatypeMap := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    let j := i.withAnonymous assign
    obtain ⟨x⟩ := j.objectNonempty
    exact ⟨j, (satisfies_toOntology_iff j p).mp hsat, x, by rw [hroot]; trivial⟩
  · rintro ⟨i, hm, _⟩
    exact ⟨i, satisfies_models ((satisfies_toOntology_iff i p).mpr hm)⟩

theorem decideRealProblem_ontology_iff {p : Problem} {answer : Bool}
    (hroot : p.root = .top) (h : decideRealProblem? p = some answer) :
    answer = true ↔ Satisfiable realDatatypeMap p.toOntology :=
  (decideRealProblem_iff h).trans (satisfiable_real_iff_satWith p hroot).symm

/-- Typed OWL decision on the admitted wider fragment with the cut semantics for real values. -/
def decideRealOntology? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    if p.root = .top ∧ p.checkSimpleWithTop = true then decideRealProblem? p else none

theorem decideRealOntology_iff {o : Ontology} {answer : Bool}
    (h : decideRealOntology? o = some answer) :
    answer = true ↔ Satisfiable realDatatypeMap o := by
  simp only [decideRealOntology?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hn, hanswer⟩ := h
  split at hanswer
  · rename_i hroot
    exact (decideRealProblem_ontology_iff hroot.1 hanswer).trans
      (Normalize.normalizeWithDefs_sat_iff_with (dm := realDatatypeMap)
        (fun _ ht => ht) lowerSmallRanges_real_iff hn).symm
  · contradiction

#print axioms encodeWiderData_real_sat_iff
#print axioms encodeWiderData_symbolic_real_iff
#print axioms decideRealProblem_ontology_iff
#print axioms decideRealOntology_iff

end Sabrina.OWL2.SROIQD.Termination.WiderData
