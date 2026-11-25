import Sabrina.OWL2.SROIQD.Termination.BottomProperties
import Sabrina.OWL2.SROIQD.Termination.RealObservations

/-! Exact elimination of `owl:topDataProperty` (and any data properties forced
universal by `SubDataPropertyOf(owl:topDataProperty, ...)`) over both the
standard `datatypeMap` and the Dedekind-cut `realDatatypeMap`.

Every admitted `DataRange` (`isWiderDataRange d = true`) has an interpretation-
independent cardinality across `i.Data`:
- If non-builtin elements satisfy `d` (`evalExtraDataRange d = true`), there are
  infinitely many distinct witnesses in every interpretation of both maps
  (already embedded via unused `Value.irrational (Rat.ofInt k)` codes).
- Otherwise (`evalExtraDataRange d = false`), every element of `i.Data`
  satisfying `d` lies in a Venn cell with a positive non-`rdfs:Literal` atom,
  where `sampleWiderCell` counts distinct values up to `n` exactly.

Consequently, every occurrence of `owl:topDataProperty` in class expressions
(`dataSome`, `dataAll`, `dataMin`, `dataMax`, `dataValue`), data-property
axioms (`subData`, `disjointData`, `funcData`, `dataRanges`), `HasKey`, and
positive/negative data assertions reduces exactly without losing completeness
or termination. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination

/-! ### 1. Exact data-domain cardinality decider -/

/-- Truth value of an admitted `DataRange` on elements that satisfy `rdfs:Literal`
and no built-in datatype or decoded literal. -/
def evalExtraDataRange : DataRange → Bool
  | .datatype t => t == literalDatatype
  | .restriction _ _ => false
  | .oneOf _ => false
  | .complement r => !evalExtraDataRange r
  | .intersection a b => evalExtraDataRange a && evalExtraDataRange b
  | .union a b => evalExtraDataRange a || evalExtraDataRange b

private def IsExtraElement {dm : DatatypeMap} (i : Interpretation dm) (y : i.Data) : Prop :=
  (∀ t, dm.builtin t → ¬ i.datatypes t y) ∧
  (∀ l, (decodeLiteral l).isSome = true → i.literalValue l ≠ y)

private theorem evalExtraDataRange_iff {dm : DatatypeMap}
    (hbuiltin : ∀ t, supportedDatatype t = true → dm.builtin t)
    (i : Interpretation dm) {y : i.Data} (hy : IsExtraElement i y)
    {d : DataRange} (hd : isWiderDataRange d = true) :
    dataHolds i y d ↔ evalExtraDataRange d = true := by
  induction d with
  | datatype t =>
    by_cases hlit : t = literalDatatype
    · subst hlit
      simp [evalExtraDataRange, dataHolds, i.literalDatatypeExt]
    · have hsup : dm.builtin t := hbuiltin t (widerDatatype_supported hd hlit)
      simp [evalExtraDataRange, beq_false_of_ne hlit, dataHolds, hy.1 t hsup]
  | restriction t fs =>
    have hsup : dm.builtin t := hbuiltin t (widerRestriction_supported hd).1
    simp [evalExtraDataRange, dataHolds, hy.1 t hsup]
  | oneOf ls =>
    have hdec := List.all_eq_true.mp (widerOneOf_decoded hd)
    simp only [evalExtraDataRange, Bool.false_eq_true, iff_false, dataHolds, not_exists, not_and]
    intro l hl
    exact hy.2 l (hdec l hl)
  | complement r ih =>
    simp only [evalExtraDataRange, Bool.not_eq_true', Bool.eq_false_iff, dataHolds]
    exact not_congr (ih hd)
  | intersection a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalExtraDataRange, Bool.and_eq_true, dataHolds]
    exact and_congr (iha ha) (ihb hb)
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalExtraDataRange, Bool.or_eq_true, dataHolds]
    exact or_congr (iha ha) (ihb hb)

private theorem exists_infinite_extra_std (i : Interpretation datatypeMap) :
    ∃ f : Nat → i.Data, (∀ a b, f a = f b → a = b) ∧ ∀ k, IsExtraElement i (f k) := by
  refine ⟨fun k => i.embedValue (.irrational (Rat.ofInt k)), ?_, ?_⟩
  · intro a b hab
    have h1 := Value.irrational.inj (i.embedValue_injective hab)
    have h2 : (a : Int) = (b : Int) := congrArg Rat.num h1
    omega
  · intro k
    refine ⟨fun t ht hmem => ?_, fun l hl heq => ?_⟩
    · obtain ⟨v, hv, hveq⟩ := (i.datatypeAgreement t ht _).mp hmem
      have hvEq : v = .irrational (Rat.ofInt k) := i.embedValue_injective hveq
      subst hvEq
      have hden := ((valueSpace_irrational_iff t (Rat.ofInt k)).mp hv).2.2
      exact hden rfl
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
      rw [i.lexicalAgreement l v hv] at heq
      have hvEq : v = .irrational (Rat.ofInt k) := i.embedValue_injective heq
      subst hvEq
      exact decodeLiteral_ne_irrational l (Rat.ofInt k) hv

private theorem exists_infinite_extra_real (i : Interpretation realDatatypeMap) :
    ∃ f : Nat → i.Data, (∀ a b, f a = f b → a = b) ∧ ∀ k, IsExtraElement i (f k) := by
  refine ⟨fun k => i.embedValue (.inl (.irrational (Rat.ofInt k))), ?_, ?_⟩
  · intro a b hab
    have h1 := Value.irrational.inj (Sum.inl.inj (i.embedValue_injective hab))
    have h2 : (a : Int) = (b : Int) := congrArg Rat.num h1
    omega
  · intro k
    refine ⟨fun t ht hmem => ?_, fun l hl heq => ?_⟩
    · obtain ⟨v, hv, hveq⟩ := (i.datatypeAgreement t ht _).mp hmem
      have hvEq : v = .inl (.irrational (Rat.ofInt k)) := i.embedValue_injective hveq
      subst hvEq
      exact Bool.noConfusion hv.1
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hl
      rw [i.lexicalAgreement l (.inl v) (realDatatypeMap_lexical l v hv)] at heq
      have hvEq : v = .irrational (Rat.ofInt k) := Sum.inl.inj (i.embedValue_injective heq)
      subst hvEq
      exact decodeLiteral_ne_irrational l (Rat.ofInt k) hv

private theorem atLeast_of_infinite_extra {dm : DatatypeMap}
    (hbuiltin : ∀ t, supportedDatatype t = true → dm.builtin t)
    (i : Interpretation dm)
    (hex : ∃ f : Nat → i.Data, (∀ a b, f a = f b → a = b) ∧ ∀ k, IsExtraElement i (f k))
    {d : DataRange} (hd : isWiderDataRange d = true) (hExtra : evalExtraDataRange d = true)
    (n : Nat) : AtLeast n (fun y => dataHolds i y d) := by
  obtain ⟨f, hfInj, hfExtra⟩ := hex
  refine ⟨(List.range n).map f, by simp, ?_, ?_⟩
  · exact List.nodup_range.map f fun _ _ hne heq => hne (hfInj _ _ heq)
  · intro y hy
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
    exact (evalExtraDataRange_iff hbuiltin i (hfExtra k) hd).mpr hExtra

private theorem atomsOfDataRange_wider {d : DataRange} (hd : isWiderDataRange d = true) :
    ∀ a ∈ atomsOfDataRange d, isWiderExactAtom a = true := by
  induction d with
  | complement r ih => exact ih hd
  | intersection a b iha ihb | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    intro x hx
    rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with h1 | h2
    · exact iha ha x h1
    · exact ihb hb x h2
  | datatype _ | restriction _ _ | oneOf _ =>
    intro x hx
    simp only [atomsOfDataRange, List.mem_singleton] at hx
    exact hx ▸ hd

private theorem atomsOfDataRange_admissible {d : DataRange} (hd : isWiderDataRange d = true)
    {pos neg : List DataRange} (hpart : (pos, neg) ∈ vennPartitions (atomsOfDataRange d)) :
    widerAtomsAdmissible (pos ++ neg) = true := by
  obtain ⟨hp, hn, _, _⟩ := mem_vennPartitions_sub hpart
  apply List.all_eq_true.mpr
  intro a ha
  rcases List.mem_append.mp ha with h1 | h2
  · exact atomsOfDataRange_wider hd a (hp a h1)
  · exact atomsOfDataRange_wider hd a (hn a h2)

/-- Collect up to `n` distinct witness values satisfying `d` across all
non-universal Venn cells of `atomsOfDataRange d`. -/
def sampleDataRange (d : DataRange) (n : Nat) : List Value :=
  let atoms := atomsOfDataRange d
  let parts := vennPartitions atoms
  let raw := parts.flatMap fun (pos, neg) =>
    if !neg.contains (.datatype literalDatatype) && evalOnPartition pos d then
      sampleWiderCell n pos neg
    else []
  raw.eraseDups.take n

/-- Exact decision procedure for `AtLeast n (fun y => dataHolds i y d)` over
both `datatypeMap` and `realDatatypeMap` for any `isWiderDataRange d = true`. -/
def dataRangeHasAtLeast (d : DataRange) (n : Nat) : Bool :=
  n == 0 || evalExtraDataRange d || decide (n ≤ (sampleDataRange d n).length)

private theorem sampleDataRange_nodup (d : DataRange) (n : Nat) :
    (sampleDataRange d n).Nodup :=
  (List.take_sublist ..).nodup (nodup_eraseDups_list _)

private theorem sampleDataRange_length_le (d : DataRange) (n : Nat) :
    (sampleDataRange d n).length ≤ n :=
  List.length_take_le ..

private theorem sampleDataRange_mem_cell {d : DataRange} {n : Nat} {v : Value}
    (hv : v ∈ sampleDataRange d n) :
    ∃ pos neg, (pos, neg) ∈ vennPartitions (atomsOfDataRange d) ∧
      neg.contains (.datatype literalDatatype) = false ∧
      evalOnPartition pos d = true ∧
      v ∈ sampleWiderCell n pos neg := by
  have h1 := List.mem_eraseDups.mp (List.mem_of_mem_take hv)
  obtain ⟨⟨pos, neg⟩, hpart, hmem⟩ := List.mem_flatMap.mp h1
  dsimp only at hmem
  split at hmem
  · rename_i hcond
    have ⟨hneg, heval⟩ := Bool.and_eq_true_iff.mp hcond
    exact ⟨pos, neg, hpart, by simpa using hneg, heval, hmem⟩
  · cases hmem

private theorem pos_has_nonLiteral_of_not_extra {dm : DatatypeMap}
    (hbuiltin : ∀ t, supportedDatatype t = true → dm.builtin t)
    (i : Interpretation dm) {y₀ : i.Data} (hy₀ : IsExtraElement i y₀)
    {d : DataRange} (hd : isWiderDataRange d = true)
    (hNotExtra : evalExtraDataRange d = false)
    {pos neg : List DataRange} (hpart : (pos, neg) ∈ vennPartitions (atomsOfDataRange d))
    (hNegLit : neg.contains (.datatype literalDatatype) = false)
    (hEval : evalOnPartition pos d = true) :
    ∃ a ∈ pos, a ≠ .datatype literalDatatype := by
  classical
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ a ∈ pos, a = .datatype literalDatatype :=
    fun a ha => Classical.byContradiction fun hne => hno ⟨a, ha, hne⟩
  obtain ⟨_, hnSub, _, _⟩ := mem_vennPartitions_sub hpart
  have hHoldPart : dataHolds i y₀ (partitionRange pos neg) := by
    rw [dataHolds_partitionRange_iff]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [hno' a ha]; exact i.literalDatatypeExt y₀
    · have hne : a ≠ .datatype literalDatatype := fun heq => by
        have hc : neg.contains (.datatype literalDatatype) = true :=
          List.contains_iff_mem.mpr (heq ▸ ha)
        rw [hNegLit] at hc; cases hc
      have haWider : isWiderExactAtom a = true := atomsOfDataRange_wider hd a (hnSub a ha)
      have haExtra : evalExtraDataRange a = false := by
        cases a with
        | datatype t =>
          have hne' : t ≠ literalDatatype := fun h => hne (congrArg DataRange.datatype h)
          simp [evalExtraDataRange, beq_false_of_ne hne']
        | restriction _ _ | oneOf _ => rfl
        | complement _ | intersection _ _ | union _ _ =>
          simp [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom,
            legacy_isWiderExactAtom] at haWider
      have haRange : isWiderDataRange a = true := by
        cases a <;> first | exact haWider |
          (simp [isWiderExactAtom, isOrderedExactAtom, isStringFacetExactAtom,
            legacy_isWiderExactAtom] at haWider)
      rw [evalExtraDataRange_iff hbuiltin i hy₀ haRange, haExtra]
      decide
  have hdY0 : dataHolds i y₀ d :=
    (evalOnPartition_iff hpart hHoldPart (fun _ h => h)).mp hEval
  have hdF := (evalExtraDataRange_iff hbuiltin i hy₀ hd).mp hdY0
  rw [hNotExtra] at hdF; cases hdF

theorem dataRangeHasAtLeast_iff {d : DataRange} (hd : isWiderDataRange d = true)
    (n : Nat) (i : Interpretation datatypeMap) :
    dataRangeHasAtLeast d n = true ↔ AtLeast n (fun y => dataHolds i y d) := by
  unfold dataRangeHasAtLeast
  cases n with
  | zero =>
    simp only [beq_self_eq_true, Bool.true_or, true_iff]
    exact ⟨[], rfl, List.nodup_nil, by simp⟩
  | succ k =>
    have hne : (k + 1 == 0) = false := rfl
    simp only [hne, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hExtra : evalExtraDataRange d = true
    · simp only [hExtra, true_or, true_iff]
      exact atLeast_of_infinite_extra (fun _ h => h) i (exists_infinite_extra_std i) hd hExtra (k + 1)
    · have hExtraF : evalExtraDataRange d = false := Bool.eq_false_iff.mpr hExtra
      simp only [hExtraF, Bool.false_eq_true, false_or]
      constructor
      · intro hge
        have hlen : (sampleDataRange d (k + 1)).length = k + 1 :=
          Nat.le_antisymm (sampleDataRange_length_le d (k + 1)) hge
        refine ⟨(sampleDataRange d (k + 1)).map (fun v : Value => i.embedValue v), by simp [hlen], ?_, ?_⟩
        · exact (sampleDataRange_nodup d (k + 1)).map (fun v : Value => i.embedValue v)
            fun _ _ hne heq => hne (i.embedValue_injective heq)
        · intro y hy
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
          obtain ⟨pos, neg, hpart, _, hEval, hCell⟩ := sampleDataRange_mem_cell hv
          have hadm := atomsOfDataRange_admissible hd hpart
          have hpos a ha := List.all_eq_true.mp hadm a (List.mem_append_left neg ha)
          have hneg a ha := List.all_eq_true.mp hadm a (List.mem_append_right pos ha)
          have hHold := sampleWiderCell_sound hpos hneg hCell i
          exact (evalOnPartition_iff hpart hHold (fun _ h => h)).mp hEval
      · rintro ⟨ys, hlen, hnd, hmem⟩
        apply Classical.byContradiction
        intro hnotGe
        have hlt : (sampleDataRange d (k + 1)).length < k + 1 := Nat.lt_of_not_ge hnotGe
        let raw := (vennPartitions (atomsOfDataRange d)).flatMap fun (pos, neg) =>
          if !neg.contains (.datatype literalDatatype) && evalOnPartition pos d then
            sampleWiderCell (k + 1) pos neg
          else []
        have hrawLt : raw.eraseDups.length < k + 1 := by
          change (raw.eraseDups.take (k + 1)).length < k + 1 at hlt
          rw [List.length_take] at hlt
          omega
        have hTakeEq : sampleDataRange d (k + 1) = raw.eraseDups := by
          change raw.eraseDups.take (k + 1) = raw.eraseDups
          exact List.take_of_length_le (Nat.le_of_lt hrawLt)
        obtain ⟨f, _, hfExtra⟩ := exists_infinite_extra_std i
        have hsub : ∀ y ∈ ys, y ∈ (sampleDataRange d (k + 1)).map (fun v : Value => i.embedValue v) := by
          intro y hy
          have hyd := hmem y hy
          obtain ⟨⟨pos, neg⟩, hpart, hHold⟩ := exists_vennPartition i y (atomsOfDataRange d)
          have hEval : evalOnPartition pos d = true :=
            (evalOnPartition_iff hpart hHold (fun _ h => h)).mpr hyd
          have hNegLit : neg.contains (.datatype literalDatatype) = false := by
            cases hc : neg.contains (.datatype literalDatatype)
            · rfl
            · exfalso
              have hm := List.contains_iff_mem.mp hc
              exact ((dataHolds_partitionRange_iff i y pos neg).mp hHold).2 _ hm (i.literalDatatypeExt y)
          have hPosNonLit := pos_has_nonLiteral_of_not_extra (fun _ h => h) i (hfExtra 0)
            hd hExtraF hpart hNegLit hEval
          have hCellSub : ∀ v ∈ sampleWiderCell (k + 1) pos neg, v ∈ raw.eraseDups := by
            intro v hv
            refine List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(pos, neg), hpart, ?_⟩)
            simp only [hNegLit, Bool.not_false, hEval, Bool.and_self, ↓reduceIte, hv]
          have hCellLt : (sampleWiderCell (k + 1) pos neg).length < k + 1 :=
            Nat.lt_of_le_of_lt ((sampleWiderCell_nodup (k + 1) pos neg).length_le_of_subset hCellSub) hrawLt
          obtain ⟨v, hvCell, rfl⟩ := sampleWiderCell_complete_of_lt
            (atomsOfDataRange_admissible hd hpart) hCellLt hPosNonLit i y hHold
          refine List.mem_map.mpr ⟨v, ?_, rfl⟩
          rw [hTakeEq]
          exact hCellSub v hvCell
        have hle := hnd.length_le_of_subset hsub
        simp only [List.length_map, hlen] at hle
        omega

/-! ### 2. Cut-semantics equivalence (`realDatatypeMap`) for `dataRangeHasAtLeast` -/

private theorem evalWiderDataRange_of_real_atoms {i : Interpretation realDatatypeMap}
    {y : i.Data} {v : Value} {d : DataRange}
    (ha : ∀ a ∈ atomsOfDataRange d, evalWiderAtom a v = true ↔ dataHolds i y a) :
    evalWiderDataRange d v = true ↔ dataHolds i y d := by
  induction d with
  | complement r ih =>
    simp only [evalWiderDataRange, Bool.not_eq_true', Bool.eq_false_iff, dataHolds]
    exact not_congr (ih ha)
  | intersection a b iha ihb =>
    simp only [evalWiderDataRange, Bool.and_eq_true, dataHolds]
    exact and_congr
      (iha fun x hx => ha x (List.mem_eraseDups.mpr (List.mem_append_left _ hx)))
      (ihb fun x hx => ha x (List.mem_eraseDups.mpr (List.mem_append_right _ hx)))
  | union a b iha ihb =>
    simp only [evalWiderDataRange, Bool.or_eq_true, dataHolds]
    exact or_congr
      (iha fun x hx => ha x (List.mem_eraseDups.mpr (List.mem_append_left _ hx)))
      (ihb fun x hx => ha x (List.mem_eraseDups.mpr (List.mem_append_right _ hx)))
  | datatype _ | restriction _ _ | oneOf _ =>
    exact ha _ (List.mem_singleton.mpr rfl)

private theorem evalPartition_from_real_atoms {i : Interpretation realDatatypeMap}
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

private theorem realCoverCell {K : Nat} {pos neg : List DataRange}
    (hadm : widerAtomsAdmissible (pos ++ neg) = true)
    (hlt : (sampleWiderCell K pos neg).length < K)
    (hpos : ∃ a ∈ pos, a ≠ .datatype literalDatatype)
    (i : Interpretation realDatatypeMap) (y : i.Data)
    (hy : dataHolds i y (partitionRange pos neg)) :
    ∃ v ∈ sampleWiderCell K pos neg, i.embedValue (.inl v) = y := by
  obtain ⟨a, ha, hn⟩ := hpos
  have adm := List.all_eq_true.mp hadm
  obtain ⟨v, rfl, hordinary⟩ :=
    realEmbedded_of_nonLiteralAtom (adm a (List.mem_append_left _ ha)) hn
      ((dataHolds_partitionRange_iff i y pos neg).mp hy |>.1 a ha)
  cases v with
  | inl v =>
    have htag : v.isIrrationalWitness = false := by
      cases v <;> try rfl
      case irrational q => exact (hordinary q rfl).elim
    have he := evalPartition_from_real_atoms (v := v)
      (fun a ha => evalWiderAtom_real_ordinary (adm a ha) i v (fun _ _ => htag)) hy
    exact ⟨v, sampleWiderCell_complete_value_of_lt hadm hlt ⟨a, ha, hn⟩ he, rfl⟩
  | inr c =>
    let endpoints := (pos ++ neg).flatMap rationalEndpoints
    obtain ⟨ws, hlen, hnd, hw⟩ := cut_has_proxies c endpoints K
    have hsub : ∀ v ∈ ws.map Value.irrational, v ∈ sampleWiderCell K pos neg := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      obtain ⟨hqv, hc⟩ := hw q hq
      have he := evalPartition_from_real_atoms (v := .irrational q)
        (fun a ha => evalWiderAtom_real_cut (adm a ha) i c q hqv fun bound hb =>
          hc bound (List.mem_flatMap.mpr ⟨a, ha, hb⟩)) hy
      exact sampleWiderCell_complete_value_of_lt hadm hlt ⟨a, ha, hn⟩ he
    have hdn : (ws.map Value.irrational).Nodup := hnd.map Value.irrational
      (fun _ _ hne he => hne (Value.irrational.inj he))
    have hle := hdn.length_le_of_subset hsub
    simp only [List.length_map, hlen] at hle
    omega

private def rangeObsPoints (d : DataRange) (ws : List Value) : List Rat :=
  (atomsOfDataRange d).flatMap rationalEndpoints ++
    ws.filterMap (fun | .irrational q => some q | _ => none)

private noncomputable def rangeCut (d : DataRange) (ws : List Value) (q : Rat) : IrrationalCut :=
  Classical.choose (realize_proxy q (rangeObsPoints d ws))

private theorem rangeCut_spec (d : DataRange) (ws : List Value) (q : Rat) :
    (rangeCut d ws q).lower q ∧
      ∀ b ∈ rangeObsPoints d ws, b ≤ q ↔ (rangeCut d ws q).lower b :=
  Classical.choose_spec (realize_proxy q (rangeObsPoints d ws))

private noncomputable def realizeForRange (d : DataRange) (ws : List Value) : Value → RealValue
  | .irrational q =>
    if DecimalValue q ∧ q.den ≠ 1 ∧ .irrational q ∈ ws then .inr (rangeCut d ws q)
    else .inl (.irrational q)
  | v => .inl v

private theorem rangeCut_lt_ne {d : DataRange} {ws : List Value} {q r : Rat}
    (hr : .irrational r ∈ ws) (hlt : q < r) :
    rangeCut d ws q ≠ rangeCut d ws r := by
  intro he
  have hm : r ∈ rangeObsPoints d ws :=
    List.mem_append_right _ (List.mem_filterMap.mpr ⟨.irrational r, hr, rfl⟩)
  have hlow := (rangeCut_spec d ws r).1
  have hle := ((rangeCut_spec d ws q).2 r hm).mpr (he.symm ▸ hlow)
  exact Rat.not_le.mpr hlt hle

private theorem realizeForRange_inj {d : DataRange} {ws : List Value} {v w : Value}
    (h : realizeForRange d ws v = realizeForRange d ws w) : v = w := by
  cases v <;> cases w <;> simp only [realizeForRange, Sum.inl.injEq] at h
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
    · exact (rangeCut_lt_ne hr.2.2 (Rat.not_le.mp hrq) he).elim
  · by_cases hqr : q ≤ r
    · exact congrArg Value.irrational (Rat.le_antisymm hqr hrq)
    · exact (rangeCut_lt_ne hq.2.2 (Rat.not_le.mp hqr) he.symm).elim

theorem dataRangeHasAtLeast_real_iff {d : DataRange} (hd : isWiderDataRange d = true)
    (n : Nat) (i : Interpretation realDatatypeMap) :
    dataRangeHasAtLeast d n = true ↔ AtLeast n (fun y => dataHolds i y d) := by
  unfold dataRangeHasAtLeast
  cases n with
  | zero =>
    simp only [beq_self_eq_true, Bool.true_or, true_iff]
    exact ⟨[], rfl, List.nodup_nil, by simp⟩
  | succ k =>
    have hne : (k + 1 == 0) = false := rfl
    simp only [hne, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hExtra : evalExtraDataRange d = true
    · simp only [hExtra, true_or, true_iff]
      exact atLeast_of_infinite_extra (fun _ h => h) i (exists_infinite_extra_real i) hd hExtra (k + 1)
    · have hExtraF : evalExtraDataRange d = false := Bool.eq_false_iff.mpr hExtra
      simp only [hExtraF, Bool.false_eq_true, false_or]
      constructor
      · intro hge
        let ws := sampleDataRange d (k + 1)
        have hlen : ws.length = k + 1 := Nat.le_antisymm (sampleDataRange_length_le d (k + 1)) hge
        refine ⟨ws.map (fun v => i.embedValue (realizeForRange d ws v)), by simp [hlen], ?_, ?_⟩
        · exact (sampleDataRange_nodup d (k + 1)).map _
            fun _ _ hne heq => hne (realizeForRange_inj (i.embedValue_injective heq))
        · intro y hy
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
          obtain ⟨pos, neg, hpart, _, hEval, hCell⟩ := sampleDataRange_mem_cell hv
          have hadm := atomsOfDataRange_admissible hd hpart
          have hpos a ha := List.all_eq_true.mp hadm a (List.mem_append_left neg ha)
          have hneg a ha := List.all_eq_true.mp hadm a (List.mem_append_right pos ha)
          have hHoldStd := sampleWiderCell_sound hpos hneg hCell observationInterpretation
          have hdStd := (evalOnPartition_iff hpart hHoldStd (fun _ h => h)).mp hEval
          have hevalD : evalWiderDataRange d v = true :=
            (evalWiderDataRange_iff hd observationInterpretation v).mpr hdStd
          refine (evalWiderDataRange_of_real_atoms ?_).mp hevalD
          intro a ha
          have haAdm := atomsOfDataRange_wider hd a ha
          cases v with
          | irrational q =>
            by_cases hq : DecimalValue q ∧ q.den ≠ 1
            · rw [realizeForRange, ite_eq_left ⟨hq.1, hq.2, hv⟩]
              exact evalWiderAtom_real_cut haAdm i (rangeCut d ws q) q hq fun b hb =>
                (rangeCut_spec d ws q).2 b
                  (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, ha, hb⟩))
            · rw [realizeForRange, ite_eq_right (fun h => hq ⟨h.1, h.2.1⟩)]
              exact evalWiderAtom_real_ordinary haAdm i _ fun t ht =>
                (hq ((valueSpace_irrational_iff t q).mp ht).2).elim
          | _ =>
            exact evalWiderAtom_real_ordinary haAdm i _ (fun _ _ => rfl)
      · rintro ⟨ys, hlen, hnd, hmem⟩
        apply Classical.byContradiction
        intro hnotGe
        have hlt : (sampleDataRange d (k + 1)).length < k + 1 := Nat.lt_of_not_ge hnotGe
        let raw := (vennPartitions (atomsOfDataRange d)).flatMap fun (pos, neg) =>
          if !neg.contains (.datatype literalDatatype) && evalOnPartition pos d then
            sampleWiderCell (k + 1) pos neg
          else []
        have hrawLt : raw.eraseDups.length < k + 1 := by
          change (raw.eraseDups.take (k + 1)).length < k + 1 at hlt
          rw [List.length_take] at hlt
          omega
        have hTakeEq : sampleDataRange d (k + 1) = raw.eraseDups := by
          change raw.eraseDups.take (k + 1) = raw.eraseDups
          exact List.take_of_length_le (Nat.le_of_lt hrawLt)
        obtain ⟨f, _, hfExtra⟩ := exists_infinite_extra_real i
        have hsub : ∀ y ∈ ys, y ∈ (sampleDataRange d (k + 1)).map (fun v => i.embedValue (.inl v)) := by
          intro y hy
          have hyd := hmem y hy
          obtain ⟨⟨pos, neg⟩, hpart, hHold⟩ := exists_vennPartition i y (atomsOfDataRange d)
          have hEval : evalOnPartition pos d = true :=
            (evalOnPartition_iff hpart hHold (fun _ h => h)).mpr hyd
          have hNegLit : neg.contains (.datatype literalDatatype) = false := by
            cases hc : neg.contains (.datatype literalDatatype)
            · rfl
            · exfalso
              have hm := List.contains_iff_mem.mp hc
              exact ((dataHolds_partitionRange_iff i y pos neg).mp hHold).2 _ hm (i.literalDatatypeExt y)
          have hPosNonLit := pos_has_nonLiteral_of_not_extra (fun _ h => h) i (hfExtra 0)
            hd hExtraF hpart hNegLit hEval
          have hCellSub : ∀ v ∈ sampleWiderCell (k + 1) pos neg, v ∈ raw.eraseDups := by
            intro v hv
            refine List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(pos, neg), hpart, ?_⟩)
            simp only [hNegLit, Bool.not_false, hEval, Bool.and_self, ↓reduceIte, hv]
          have hCellLt : (sampleWiderCell (k + 1) pos neg).length < k + 1 :=
            Nat.lt_of_le_of_lt ((sampleWiderCell_nodup (k + 1) pos neg).length_le_of_subset hCellSub) hrawLt
          obtain ⟨v, hvCell, rfl⟩ := realCoverCell
            (atomsOfDataRange_admissible hd hpart) hCellLt hPosNonLit i y hHold
          refine List.mem_map.mpr ⟨v, ?_, rfl⟩
          rw [hTakeEq]
          exact hCellSub v hvCell
        have hle := hnd.length_le_of_subset hsub
        simp only [List.length_map, hlen] at hle
        omega

/-! ### 3. Universal data-property closure (`SubDataPropertyOf(owl:topDataProperty, ...)`) -/

private def univDataStep (subData : List (IRI × IRI)) (u : List IRI) : List IRI :=
  u ++ (subData.filterMap fun rs => if u.contains rs.1 && !u.contains rs.2 then some rs.2 else none).eraseDups

private def univDataLoop (subData : List (IRI × IRI)) : Nat → List IRI → List IRI
  | 0, u => u
  | n + 1, u =>
    let u' := univDataStep subData u
    if u'.length == u.length then u else univDataLoop subData n u'

/-- Least fixed point of data properties forced universal by `subData`,
starting from `owl:topDataProperty`. -/
def univDataProps (subData : List (IRI × IRI)) : List IRI :=
  univDataLoop subData (subData.length + 1) [topDataProperty]

private theorem univDataStep_subset (subData : List (IRI × IRI)) (u : List IRI) :
    ∀ dp ∈ u, dp ∈ univDataStep subData u :=
  fun _ h => List.mem_append_left _ h

private theorem univDataStep_nodup (subData : List (IRI × IRI)) {u : List IRI} (hnd : u.Nodup) :
    (univDataStep subData u).Nodup := by
  unfold univDataStep
  rw [List.nodup_append]
  refine ⟨hnd, nodup_eraseDups_list _, ?_⟩
  intro a ha b hb heq
  subst heq
  obtain ⟨rs, _, hres⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hb)
  split at hres
  · rename_i hc
    simp only [Option.some.injEq] at hres
    subst hres
    have h2 := (Bool.and_eq_true_iff.mp hc).2
    simp only [Bool.not_eq_true'] at h2
    have hm := List.contains_iff_mem.mpr ha
    rw [h2] at hm; cases hm
  · cases hres

private theorem univDataStep_in_pool (subData : List (IRI × IRI)) {u : List IRI}
    (hu : ∀ dp ∈ u, dp ∈ topDataProperty :: subData.map Prod.snd) :
    ∀ dp ∈ univDataStep subData u, dp ∈ topDataProperty :: subData.map Prod.snd := by
  intro dp hdp
  rcases List.mem_append.mp hdp with h1 | h2
  · exact hu dp h1
  · obtain ⟨rs, hrs, hres⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp h2)
    split at hres
    · simp only [Option.some.injEq] at hres
      subst hres
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨rs, hrs, rfl⟩)
    · cases hres

private theorem univDataStep_fixed_closed {subData : List (IRI × IRI)} {u : List IRI}
    (hfix : (univDataStep subData u).length = u.length)
    {r s : IRI} (hrs : (r, s) ∈ subData) (hr : r ∈ u) : s ∈ u := by
  classical
  apply Classical.byContradiction
  intro hs
  have h1 : u.contains r = true := List.contains_iff_mem.mpr hr
  have h2 : u.contains s = false := by
    cases hc : u.contains s
    · rfl
    · exact (hs (List.contains_iff_mem.mp hc)).elim
  have hmemNew : s ∈ (subData.filterMap fun rs =>
      if u.contains rs.1 && !u.contains rs.2 then some rs.2 else none).eraseDups := by
    refine List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨(r, s), hrs, ?_⟩)
    simp only [h1, h2, Bool.not_false, Bool.and_self, ↓reduceIte]
  have hpos : 0 < ((subData.filterMap fun rs =>
      if u.contains rs.1 && !u.contains rs.2 then some rs.2 else none).eraseDups).length :=
    List.length_pos_of_mem hmemNew
  simp only [univDataStep, List.length_append] at hfix
  omega

private theorem univDataStep_universal {dm : DatatypeMap} (i : Interpretation dm)
    {subData : List (IRI × IRI)}
    (hsub : ∀ rs ∈ subData, ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y)
    {u : List IRI} (hu : ∀ dp ∈ u, ∀ x y, i.dataProperties dp x y) :
    ∀ dp ∈ univDataStep subData u, ∀ x y, i.dataProperties dp x y := by
  intro dp hdp x y
  rcases List.mem_append.mp hdp with h1 | h2
  · exact hu dp h1 x y
  · obtain ⟨rs, hrs, hres⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp h2)
    split at hres
    · rename_i hc
      simp only [Option.some.injEq] at hres
      subst hres
      have hr : rs.1 ∈ u := List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hc).1
      exact hsub rs hrs x y (hu rs.1 hr x y)
    · cases hres

private theorem univDataLoop_spec (subData : List (IRI × IRI)) (n : Nat) (u : List IRI)
    (hnd : u.Nodup)
    (hpool : ∀ dp ∈ u, dp ∈ topDataProperty :: subData.map Prod.snd)
    (hroom : subData.length + 1 ≤ u.length + n) :
    (∀ dp ∈ u, dp ∈ univDataLoop subData n u) ∧
    (∀ r s, (r, s) ∈ subData → r ∈ univDataLoop subData n u → s ∈ univDataLoop subData n u) := by
  induction n generalizing u with
  | zero =>
    have hle : u.length ≤ (topDataProperty :: subData.map Prod.snd).length :=
      hnd.length_le_of_subset hpool
    simp only [List.length_cons, List.length_map] at hle
    have hfull : u.length = subData.length + 1 := by omega
    have hnd' := univDataStep_nodup subData hnd
    have hle' : (univDataStep subData u).length ≤ subData.length + 1 := by
      have := hnd'.length_le_of_subset (univDataStep_in_pool subData hpool)
      simpa using this
    have hge' : u.length ≤ (univDataStep subData u).length := by
      simp [univDataStep]
    have hfix : (univDataStep subData u).length = u.length := by omega
    exact ⟨fun _ h => h, fun r s hrs hr => univDataStep_fixed_closed hfix hrs hr⟩
  | succ k ih =>
    unfold univDataLoop
    dsimp only
    by_cases hfix : (univDataStep subData u).length = u.length
    · simp only [beq_iff_eq, hfix, ↓reduceIte]
      exact ⟨fun _ h => h, fun r s hrs hr => univDataStep_fixed_closed hfix hrs hr⟩
    · have hge : u.length ≤ (univDataStep subData u).length := by simp [univDataStep]
      have hgt : u.length < (univDataStep subData u).length := by omega
      simp only [beq_iff_eq, hfix, ↓reduceIte]
      obtain ⟨hsub, hcl⟩ := ih (univDataStep subData u)
        (univDataStep_nodup subData hnd)
        (univDataStep_in_pool subData hpool)
        (by omega)
      exact ⟨fun dp hdp => hsub dp (univDataStep_subset subData u dp hdp), hcl⟩

private theorem univDataLoop_universal {dm : DatatypeMap} (i : Interpretation dm)
    {subData : List (IRI × IRI)}
    (hsub : ∀ rs ∈ subData, ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y)
    (n : Nat) (u : List IRI)
    (hu : ∀ dp ∈ u, ∀ x y, i.dataProperties dp x y) :
    ∀ dp ∈ univDataLoop subData n u, ∀ x y, i.dataProperties dp x y := by
  induction n generalizing u with
  | zero => exact hu
  | succ k ih =>
    unfold univDataLoop
    dsimp only
    split
    · exact hu
    · exact ih (univDataStep subData u) (univDataStep_universal i hsub hu)

theorem topDataProperty_mem_univDataProps (subData : List (IRI × IRI)) :
    topDataProperty ∈ univDataProps subData := by
  have ⟨hsub, _⟩ := univDataLoop_spec subData (subData.length + 1) [topDataProperty]
    (by simp) (fun dp h => by simp at h; simp [h]) (by simp)
  exact hsub topDataProperty (List.mem_cons_self ..)

theorem univDataProps_closed {subData : List (IRI × IRI)} {r s : IRI}
    (hrs : (r, s) ∈ subData) (hr : r ∈ univDataProps subData) :
    s ∈ univDataProps subData := by
  have ⟨_, hcl⟩ := univDataLoop_spec subData (subData.length + 1) [topDataProperty]
    (by simp) (fun dp h => by simp at h; simp [h]) (by simp)
  exact hcl r s hrs hr

theorem univDataProps_universal {dm : DatatypeMap} (i : Interpretation dm)
    {subData : List (IRI × IRI)}
    (hsub : ∀ rs ∈ subData, ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y) :
    ∀ dp ∈ univDataProps subData, ∀ x y, i.dataProperties dp x y :=
  univDataLoop_universal i hsub (subData.length + 1) [topDataProperty]
    (fun dp h x y => by simp only [List.mem_singleton] at h; subst h; exact i.topDataExt x y)

def substUnivData (u : List IRI) (dp : IRI) : IRI :=
  if u.contains dp then topDataProperty else dp

def substUnivDataConcept (u : List IRI) : Concept → Concept
  | .conj a b => .conj (substUnivDataConcept u a) (substUnivDataConcept u b)
  | .disj a b => .disj (substUnivDataConcept u a) (substUnivDataConcept u b)
  | .some r c => .some r (substUnivDataConcept u c)
  | .all r c => .all r (substUnivDataConcept u c)
  | .min n r c => .min n r (substUnivDataConcept u c)
  | .max n r c => .max n r (substUnivDataConcept u c)
  | .dataSome dp d => .dataSome (substUnivData u dp) d
  | .dataAll dp d => .dataAll (substUnivData u dp) d
  | .dataValue dp l b => .dataValue (substUnivData u dp) l b
  | .dataMin n dp d => .dataMin n (substUnivData u dp) d
  | .dataMax n dp d => .dataMax n (substUnivData u dp) d
  | c => c

private theorem holds_substUnivData_iff {dm : DatatypeMap} (i : Interpretation dm)
    (u : List IRI) (hu : ∀ dp ∈ u, ∀ x y, i.dataProperties dp x y)
    (x : i.Object) (c : Concept) :
    holds i x (substUnivDataConcept u c) ↔ holds i x c := by
  have hdp (dp : IRI) (a : i.Object) (y : i.Data) :
      i.dataProperties (substUnivData u dp) a y ↔ i.dataProperties dp a y := by
    unfold substUnivData
    split
    · rename_i hm
      exact ⟨fun _ => hu dp (List.contains_iff_mem.mp hm) a y, fun _ => i.topDataExt a y⟩
    · exact Iff.rfl
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b | nom _ b | self _ b => cases b <;> rfl
  | conj a b ha hb => exact and_congr (ha x) (hb x)
  | disj a b ha hb => exact or_congr (ha x) (hb x)
  | some r c ih => exact exists_congr fun y => and_congr Iff.rfl (ih y)
  | all r c ih => exact forall_congr' fun y => imp_congr Iff.rfl (ih y)
  | min n r c ih =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y))))
  | max n r c ih =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y)))))
  | dataSome dp d => exact exists_congr fun y => and_congr (hdp dp x y) Iff.rfl
  | dataAll dp d => exact forall_congr' fun y => imp_congr (hdp dp x y) Iff.rfl
  | dataValue dp l b => cases b <;> simp [substUnivDataConcept, holds, hdp]
  | dataMin n dp d =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr (hdp dp x y) Iff.rfl)))
  | dataMax n dp d =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr (hdp dp x y) Iff.rfl))))

def unsatDataProblem : Problem :=
  { tbox := [⟨.top, .bottom⟩], root := .top }

private theorem not_unsatDataProblem_satWith (dm : DatatypeMap) :
    ¬ unsatDataProblem.SatWith dm := by
  rintro ⟨i, hm, x, _⟩
  exact hm.tbox ⟨.top, .bottom⟩ (List.mem_cons_self ..) x trivial

def collapseUnivDataProps (p : Problem) : Problem :=
  let u := univDataProps p.subData
  if u.contains bottomDataProperty then unsatDataProblem
  else
    { p with
      tbox := p.tbox.map fun q => ⟨substUnivDataConcept u q.sub, substUnivDataConcept u q.sup⟩
      subData := p.subData.map fun (r, s) => (substUnivData u r, substUnivData u s)
      disjointData := p.disjointData.map fun (r, s) => (substUnivData u r, substUnivData u s)
      funcData := p.funcData.map (substUnivData u)
      dataRanges := p.dataRanges.map fun (r, d) => (substUnivData u r, d)
      keys := p.keys.map fun k => { k with cls := substUnivDataConcept u k.cls, dataProps := k.dataProps.map (substUnivData u) }
      classAssertions := p.classAssertions.map fun (a, c) => (a, substUnivDataConcept u c)
      dataAssertions := p.dataAssertions.map fun (r, a, l) => (substUnivData u r, a, l)
      negDataAssertions := p.negDataAssertions.map fun (r, a, l) => (substUnivData u r, a, l)
      root := substUnivDataConcept u p.root }

private def withUnivDataProps {dm : DatatypeMap} (i : Interpretation dm) (u : List IRI)
    (hnoBot : u.contains bottomDataProperty = false) : Interpretation dm where
  Object := i.Object
  objectNonempty := i.objectNonempty
  Data := i.Data
  dataNonempty := i.dataNonempty
  embedValue := i.embedValue
  embedValue_injective := i.embedValue_injective
  classes := i.classes
  objectProperties := i.objectProperties
  dataProperties := fun dp x y => if u.contains dp then True else i.dataProperties dp x y
  individuals := i.individuals
  datatypes := i.datatypes
  literalValue := i.literalValue
  lexicalAgreement := i.lexicalAgreement
  named := i.named
  namedIndividual := i.namedIndividual
  thingExt := i.thingExt
  nothingExt := i.nothingExt
  topObjectExt := i.topObjectExt
  bottomObjectExt := i.bottomObjectExt
  topDataExt := fun x y => by
    split
    · trivial
    · exact i.topDataExt x y
  bottomDataExt := fun x y => by
    simp only [hnoBot, Bool.false_eq_true, ↓reduceIte]
    exact i.bottomDataExt x y
  literalDatatypeExt := i.literalDatatypeExt
  datatypeAgreement := i.datatypeAgreement

private theorem objPath_withUnivDataProps {dm : DatatypeMap} (i : Interpretation dm)
    (u : List IRI) (hnoBot : u.contains bottomDataProperty = false)
    (rs : List Sabrina.ALC.OrientedRole) (x y : i.Object) :
    objPath (withUnivDataProps i u hnoBot) rs x y ↔ objPath i rs x y := by
  induction rs generalizing x with
  | nil => exact Iff.rfl
  | cons r rest ih =>
    have hr (z : i.Object) : holdsOriented (withUnivDataProps i u hnoBot) r x z ↔ holdsOriented i r x z := by
      rcases r with ⟨_, _ | _⟩ <;> rfl
    exact exists_congr fun z => and_congr (hr z) (ih z)

private theorem dataHolds_withUnivDataProps {dm : DatatypeMap} (i : Interpretation dm)
    (u : List IRI) (hnoBot : u.contains bottomDataProperty = false) (y : i.Data) (d : DataRange) :
    dataHolds (withUnivDataProps i u hnoBot) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => exact Iff.rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ia ib => exact and_congr ia ib
  | union _ _ ia ib => exact or_congr ia ib

private theorem holds_withUnivDataProps_subst {dm : DatatypeMap} (i : Interpretation dm)
    (u : List IRI) (hnoBot : u.contains bottomDataProperty = false)
    (x : i.Object) (c : Concept) :
    holds (withUnivDataProps i u hnoBot) x c ↔ holds i x (substUnivDataConcept u c) := by
  have hdp (dp : IRI) (a : i.Object) (y : i.Data) :
      (withUnivDataProps i u hnoBot).dataProperties dp a y ↔
        i.dataProperties (substUnivData u dp) a y := by
    simp only [withUnivDataProps, substUnivData]
    split
    · exact ⟨fun _ => i.topDataExt a y, fun _ => trivial⟩
    · exact Iff.rfl
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b | nom _ b | self _ b => cases b <;> rfl
  | conj a b ha hb => exact and_congr (ha x) (hb x)
  | disj a b ha hb => exact or_congr (ha x) (hb x)
  | some r c ih => exact exists_congr fun y => and_congr Iff.rfl (ih y)
  | all r c ih => exact forall_congr' fun y => imp_congr Iff.rfl (ih y)
  | min n r c ih =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y))))
  | max n r c ih =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y)))))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr (hdp dp x y) (dataHolds_withUnivDataProps i u hnoBot y d)
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr (hdp dp x y) (dataHolds_withUnivDataProps i u hnoBot y d)
  | dataValue dp l b =>
    cases b
    · exact not_congr (hdp dp x (i.literalValue l))
    · exact hdp dp x (i.literalValue l)
  | dataMin n dp d =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl
        (and_congr (hdp dp x y) (dataHolds_withUnivDataProps i u hnoBot y d))))
  | dataMax n dp d =>
    simp only [substUnivDataConcept, holds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl
        (and_congr (hdp dp x y) (dataHolds_withUnivDataProps i u hnoBot y d)))))

private theorem collapseUnivDataProps_satWith_iff {dm : DatatypeMap} (p : Problem) :
    (collapseUnivDataProps p).SatWith dm ↔ p.SatWith dm := by
  unfold collapseUnivDataProps
  dsimp only
  cases hbot : (univDataProps p.subData).contains bottomDataProperty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let u := univDataProps p.subData
    constructor
    · rintro ⟨i, hm, x₀, hx₀⟩
      let j := withUnivDataProps i u hbot
      have hdp (dp : IRI) (a : i.Object) (y : i.Data) :
          j.dataProperties dp a y ↔ i.dataProperties (substUnivData u dp) a y := by
        simp only [j, withUnivDataProps, substUnivData]
        split
        · exact ⟨fun _ => i.topDataExt a y, fun _ => trivial⟩
        · exact Iff.rfl
      refine ⟨j, ?_, x₀, (holds_withUnivDataProps_subst i u hbot x₀ p.root).mpr hx₀⟩
      refine ⟨?_, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        ?_, ?_, ?_, ?_, ?_, ?_, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        ?_, ?_⟩
      · intro q hq x hx
        have := hm.tbox ⟨substUnivDataConcept u q.sub, substUnivDataConcept u q.sup⟩
          (List.mem_map.mpr ⟨q, hq, rfl⟩) x ((holds_withUnivDataProps_subst i u hbot x q.sub).mp hx)
        exact (holds_withUnivDataProps_subst i u hbot x q.sup).mpr this
      · intro c hc x y hpath
        exact hm.chains c hc x y ((objPath_withUnivDataProps i u hbot c.body x y).mp hpath)
      · rintro ⟨r, s⟩ hrs x y hxy
        exact (hdp s x y).mpr (hm.subData (substUnivData u r, substUnivData u s)
          (List.mem_map.mpr ⟨(r, s), hrs, rfl⟩) x y ((hdp r x y).mp hxy))
      · rintro ⟨r, s⟩ hrs x y ⟨h1, h2⟩
        exact hm.disjointData (substUnivData u r, substUnivData u s)
          (List.mem_map.mpr ⟨(r, s), hrs, rfl⟩) x y ⟨(hdp r x y).mp h1, (hdp s x y).mp h2⟩
      · intro r hr x y z hy hz
        exact hm.funcData (substUnivData u r) (List.mem_map.mpr ⟨r, hr, rfl⟩)
          x y z ((hdp r x y).mp hy) ((hdp r x z).mp hz)
      · rintro ⟨r, d⟩ hrd x y hxy
        exact (dataHolds_withUnivDataProps i u hbot y d).mpr
          (hm.dataRanges (substUnivData u r, d) (List.mem_map.mpr ⟨(r, d), hrd, rfl⟩)
            x y ((hdp r x y).mp hxy))
      · intro k hk x y hx hy hnx hny ho hd
        refine hm.keys { k with cls := substUnivDataConcept u k.cls, dataProps := k.dataProps.map (substUnivData u) }
          (List.mem_map.mpr ⟨k, hk, rfl⟩) x y
          ((holds_withUnivDataProps_subst i u hbot x k.cls).mp hx)
          ((holds_withUnivDataProps_subst i u hbot y k.cls).mp hy) hnx hny ho ?_
        intro dp hdpM
        obtain ⟨dp0, hdp0, rfl⟩ := List.mem_map.mp hdpM
        obtain ⟨z, hxz, hyz⟩ := hd dp0 hdp0
        exact ⟨z, (hdp dp0 x z).mp hxz, (hdp dp0 y z).mp hyz⟩
      · rintro ⟨a, c⟩ hac
        exact (holds_withUnivDataProps_subst i u hbot _ c).mpr
          (hm.classAssertions (a, substUnivDataConcept u c) (List.mem_map.mpr ⟨(a, c), hac, rfl⟩))
      · rintro ⟨r, a, l⟩ hral
        exact (hdp r _ _).mpr (hm.dataAssertions (substUnivData u r, a, l) (List.mem_map.mpr ⟨(r, a, l), hral, rfl⟩))
      · rintro ⟨r, a, l⟩ hral hrel
        exact hm.negDataAssertions (substUnivData u r, a, l)
          (List.mem_map.mpr ⟨(r, a, l), hral, rfl⟩) ((hdp r _ _).mp hrel)
    · rintro ⟨i, hm, x₀, hx₀⟩
      have hu := univDataProps_universal i hm.subData
      have hdp (dp : IRI) (a : i.Object) (y : i.Data) :
          i.dataProperties (substUnivData u dp) a y ↔ i.dataProperties dp a y := by
        unfold substUnivData
        split
        · rename_i hmU
          exact ⟨fun _ => hu dp (List.contains_iff_mem.mp hmU) a y, fun _ => i.topDataExt a y⟩
        · exact Iff.rfl
      refine ⟨i, ?_, x₀, (holds_substUnivData_iff i u hu x₀ p.root).mpr hx₀⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        ?_, ?_, ?_, ?_, ?_, ?_, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        ?_, ?_⟩
      · intro q hq x hx
        obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
        exact (holds_substUnivData_iff i u hu x q0.sup).mpr
          (hm.tbox q0 hq0 x ((holds_substUnivData_iff i u hu x q0.sub).mp hx))
      · intro rs hrs x y hxy
        obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
        exact (hdp rs0.2 x y).mpr (hm.subData rs0 hrs0 x y ((hdp rs0.1 x y).mp hxy))
      · intro rs hrs x y ⟨h1, h2⟩
        obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
        exact hm.disjointData rs0 hrs0 x y ⟨(hdp rs0.1 x y).mp h1, (hdp rs0.2 x y).mp h2⟩
      · intro r hr x y z hy hz
        obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
        exact hm.funcData r0 hr0 x y z ((hdp r0 x y).mp hy) ((hdp r0 x z).mp hz)
      · intro rd hrd x y hxy
        obtain ⟨rd0, hrd0, rfl⟩ := List.mem_map.mp hrd
        exact hm.dataRanges rd0 hrd0 x y ((hdp rd0.1 x y).mp hxy)
      · intro k hk x y hx hy hnx hny ho hd
        obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
        refine hm.keys k0 hk0 x y
          ((holds_substUnivData_iff i u hu x k0.cls).mp hx)
          ((holds_substUnivData_iff i u hu y k0.cls).mp hy) hnx hny ho ?_
        intro dp hdp0
        obtain ⟨z, hxz, hyz⟩ := hd (substUnivData u dp) (List.mem_map_of_mem hdp0)
        exact ⟨z, (hdp dp x z).mp hxz, (hdp dp y z).mp hyz⟩
      · intro ac hac
        obtain ⟨ac0, hac0, rfl⟩ := List.mem_map.mp hac
        exact (holds_substUnivData_iff i u hu _ ac0.2).mpr (hm.classAssertions ac0 hac0)
      · intro ral hral
        obtain ⟨ral0, hral0, rfl⟩ := List.mem_map.mp hral
        exact (hdp ral0.1 _ _).mpr (hm.dataAssertions ral0 hral0)
      · intro ral hral hrel
        obtain ⟨ral0, hral0, rfl⟩ := List.mem_map.mp hral
        exact hm.negDataAssertions ral0 hral0 ((hdp ral0.1 _ _).mp hrel)
  · simp only [↓reduceIte]
    constructor
    · intro h; exact (not_unsatDataProblem_satWith dm h).elim
    · rintro ⟨i, hm, _⟩
      obtain ⟨x⟩ := i.objectNonempty
      obtain ⟨y⟩ := i.dataNonempty
      have hbotMem := List.contains_iff_mem.mp hbot
      exact (i.bottomDataExt x y (univDataProps_universal i hm.subData bottomDataProperty hbotMem x y)).elim

/-! ### 4. Lowering `owl:topDataProperty` from concepts and problems -/

def isTopData (dp : IRI) : Bool := dp == topDataProperty

private theorem isTopData_eq {dp : IRI} (h : isTopData dp = true) : dp = topDataProperty :=
  beq_iff_eq.mp h

def lowerTopDataConcept? : Concept → Option Concept
  | .conj a b => (lowerTopDataConcept? a).bind fun a' => (lowerTopDataConcept? b).map fun b' => .conj a' b'
  | .disj a b => (lowerTopDataConcept? a).bind fun a' => (lowerTopDataConcept? b).map fun b' => .disj a' b'
  | .some r c => (lowerTopDataConcept? c).map fun c' => .some r c'
  | .all r c => (lowerTopDataConcept? c).map fun c' => .all r c'
  | .min n r c => (lowerTopDataConcept? c).map fun c' => .min n r c'
  | .max n r c => (lowerTopDataConcept? c).map fun c' => .max n r c'
  | .dataSome dp d =>
    if isTopData dp then
      if isWiderDataRange d then some (if dataRangeHasAtLeast d 1 then .top else .bottom) else none
    else some (.dataSome dp d)
  | .dataAll dp d =>
    if isTopData dp then
      if isWiderDataRange d then
        some (if dataRangeHasAtLeast (.complement d) 1 then .bottom else .top)
      else none
    else some (.dataAll dp d)
  | .dataValue dp l b =>
    if isTopData dp then some (if b then .top else .bottom)
    else some (.dataValue dp l b)
  | .dataMin n dp d =>
    if isTopData dp then
      if isWiderDataRange d then some (if dataRangeHasAtLeast d n then .top else .bottom) else none
    else some (.dataMin n dp d)
  | .dataMax n dp d =>
    if isTopData dp then
      if isWiderDataRange d then
        some (if dataRangeHasAtLeast d (n + 1) then .bottom else .top)
      else none
    else some (.dataMax n dp d)
  | c => some c

private theorem atLeast_one_iff {α : Type} (p : α → Prop) :
    AtLeast 1 p ↔ ∃ y, p y := by
  constructor
  · rintro ⟨xs, hlen, _, hmem⟩
    cases xs with
    | nil => simp at hlen
    | cons y _ => exact ⟨y, hmem y (List.mem_cons_self ..)⟩
  · rintro ⟨y, hy⟩
    exact ⟨[y], rfl, by simp, fun z hz => by simp at hz; exact hz ▸ hy⟩

private theorem holds_lowerTopData_iff_gen {dm : DatatypeMap} (i : Interpretation dm)
    (hcard : ∀ d n, isWiderDataRange d = true →
      (dataRangeHasAtLeast d n = true ↔ AtLeast n (fun y => dataHolds i y d)))
    {c c' : Concept} (h : lowerTopDataConcept? c = some c') (x : i.Object) :
    holds i x c' ↔ holds i x c := by
  induction c generalizing c' x with
  | top | bottom | lit | nom | self =>
    cases h; rfl
  | conj a b iha ihb =>
    simp only [lowerTopDataConcept?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a', ha', b', hb', rfl⟩ := h
    exact and_congr (iha ha' x) (ihb hb' x)
  | disj a b iha ihb =>
    simp only [lowerTopDataConcept?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a', ha', b', hb', rfl⟩ := h
    exact or_congr (iha ha' x) (ihb hb' x)
  | some r c ih =>
    obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.mp h
    exact exists_congr fun y => and_congr Iff.rfl (ih hc1 y)
  | all r c ih =>
    obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.mp h
    exact forall_congr' fun y => imp_congr Iff.rfl (ih hc1 y)
  | min n r c ih =>
    obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [holds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih hc1 y))))
  | max n r c ih =>
    obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [holds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih hc1 y)))))
  | dataSome dp d =>
    unfold lowerTopDataConcept? at h
    cases htop : isTopData dp
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · have hdp := isTopData_eq htop; subst hdp
      simp only [htop, ↓reduceIte] at h
      cases hd : isWiderDataRange d
      · simp [hd] at h
      · simp only [hd, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hAt := (hcard d 1 hd).trans (atLeast_one_iff _)
        have hholds : holds i x (.dataSome topDataProperty d) ↔ ∃ y, dataHolds i y d := by
          simp [holds, i.topDataExt]
        rw [hholds]
        cases hres : dataRangeHasAtLeast d 1
        · simp only [Bool.false_eq_true, ↓reduceIte, holds, false_iff]
          intro hex; have := hAt.mpr hex; rw [hres] at this; cases this
        · simp only [↓reduceIte, holds, true_iff]
          exact hAt.mp hres
  | dataAll dp d =>
    unfold lowerTopDataConcept? at h
    cases htop : isTopData dp
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · have hdp := isTopData_eq htop; subst hdp
      simp only [htop, ↓reduceIte] at h
      cases hd : isWiderDataRange d
      · simp [hd] at h
      · simp only [hd, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hAt := (hcard (.complement d) 1 hd).trans (atLeast_one_iff _)
        have hholds : holds i x (.dataAll topDataProperty d) ↔ ¬ ∃ y, dataHolds i y (.complement d) := by
          classical
          simp [holds, i.topDataExt, dataHolds]
        rw [hholds]
        cases hres : dataRangeHasAtLeast (.complement d) 1
        · simp only [Bool.false_eq_true, ↓reduceIte, holds, true_iff]
          intro hex; have := hAt.mpr hex; rw [hres] at this; cases this
        · simp only [↓reduceIte, holds, false_iff, Classical.not_not]
          exact hAt.mp hres
  | dataValue dp l b =>
    unfold lowerTopDataConcept? at h
    cases htop : isTopData dp
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · have hdp := isTopData_eq htop; subst hdp
      simp only [htop, ↓reduceIte, Option.some.injEq] at h
      subst h
      cases b <;> simp [holds, i.topDataExt]
  | dataMin n dp d =>
    unfold lowerTopDataConcept? at h
    cases htop : isTopData dp
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · have hdp := isTopData_eq htop; subst hdp
      simp only [htop, ↓reduceIte] at h
      cases hd : isWiderDataRange d
      · simp [hd] at h
      · simp only [hd, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hAt := hcard d n hd
        have hholds : holds i x (.dataMin n topDataProperty d) ↔ AtLeast n (fun y => dataHolds i y d) := by
          simp [holds, AtLeast, i.topDataExt]
        rw [hholds]
        cases hres : dataRangeHasAtLeast d n
        · simp only [Bool.false_eq_true, ↓reduceIte, holds, false_iff]
          intro hex; have := hAt.mpr hex; rw [hres] at this; cases this
        · simp only [↓reduceIte, holds, true_iff]
          exact hAt.mp hres
  | dataMax n dp d =>
    unfold lowerTopDataConcept? at h
    cases htop : isTopData dp
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · have hdp := isTopData_eq htop; subst hdp
      simp only [htop, ↓reduceIte] at h
      cases hd : isWiderDataRange d
      · simp [hd] at h
      · simp only [hd, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hAt := hcard d (n + 1) hd
        have hholds : holds i x (.dataMax n topDataProperty d) ↔ ¬ AtLeast (n + 1) (fun y => dataHolds i y d) := by
          simp [holds, AtLeast, i.topDataExt]
        rw [hholds]
        cases hres : dataRangeHasAtLeast d (n + 1)
        · simp only [Bool.false_eq_true, ↓reduceIte, holds, true_iff]
          intro hex; have := hAt.mpr hex; rw [hres] at this; cases this
        · simp only [↓reduceIte, holds, false_iff, Classical.not_not]
          exact hAt.mp hres

def lowerInclusion? (q : Inclusion) : Option Inclusion :=
  (lowerTopDataConcept? q.sub).bind fun s1 =>
    (lowerTopDataConcept? q.sup).map fun s2 => ⟨s1, s2⟩

def lowerKey? (k : KeyAxiom) : Option KeyAxiom :=
  (lowerTopDataConcept? k.cls).map fun c' =>
    { k with cls := c', dataProps := k.dataProps.filter (!isTopData ·) }

def lowerClassAssertion? (ac : Individual × Concept) : Option (Individual × Concept) :=
  (lowerTopDataConcept? ac.2).map fun c' => (ac.1, c')

def lowerTopDataDirect? (p : Problem) : Option Problem :=
  let topRangeGCIs : List Inclusion :=
    p.dataRanges.filterMap fun (dp, d) =>
      if isTopData dp then some ⟨.top, .dataAll topDataProperty d⟩ else none
  let otherDataRanges := p.dataRanges.filter fun (dp, _) => !isTopData dp
  let tboxIn := p.tbox ++ topRangeGCIs
  (tboxIn.mapM lowerInclusion?).bind fun tbox' =>
  (p.keys.mapM lowerKey?).bind fun keys' =>
  (p.classAssertions.mapM lowerClassAssertion?).bind fun classAssertions' =>
  (lowerTopDataConcept? p.root).map fun root' =>
    let disjForbids : List Concept := p.disjointData.filterMap fun (r, s) =>
      if isTopData r && isTopData s then some .top
      else if isTopData r then some (.dataSome s (.datatype literalDatatype))
      else if isTopData s then some (.dataSome r (.datatype literalDatatype))
      else none
    let funcForbids : List Concept := p.funcData.filterMap fun r =>
      if isTopData r then some .top else none
    let negAssertForbids : List Concept := p.negDataAssertions.filterMap fun (r, _, _) =>
      if isTopData r then some .top else none
    let extra := (disjForbids ++ funcForbids ++ negAssertForbids).map (fun c => ⟨c, .bottom⟩)
    { p with
      tbox := tbox' ++ extra
      subData := p.subData.filter fun (r, s) => !isTopData r && !isTopData s
      disjointData := p.disjointData.filter fun (r, s) => !isTopData r && !isTopData s
      funcData := p.funcData.filter (!isTopData ·)
      dataRanges := otherDataRanges
      keys := keys'
      classAssertions := classAssertions'
      dataAssertions := p.dataAssertions.filter fun (r, _, _) => !isTopData r
      negDataAssertions := p.negDataAssertions.filter fun (r, _, _) => !isTopData r
      root := root' }

private theorem mapM_option_iff {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys →
    (∀ y ∈ ys, ∃ x ∈ xs, f x = some y) ∧ (∀ x ∈ xs, ∃ y ∈ ys, f x = some y) := by
  induction xs generalizing ys with
  | nil =>
    intro h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons a rest ih =>
    intro h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, tail, htail, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih tail htail
    refine ⟨fun y hy => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨a, List.mem_cons_self .., hb⟩
      · obtain ⟨x, hx, hfx⟩ := h1 y hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, List.mem_cons_self .., hb⟩
      · obtain ⟨y, hy, hfx⟩ := h2 x hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hfx⟩

private theorem lowerTopDataDirect_models_iff_gen {dm : DatatypeMap} (i : Interpretation dm)
    (htwo : ∃ v₁ v₂ : dm.Value, v₁ ≠ v₂)
    (hcard : ∀ d n, isWiderDataRange d = true →
      (dataRangeHasAtLeast d n = true ↔ AtLeast n (fun y => dataHolds i y d)))
    {p p' : Problem}
    (hclosed : ∀ rs ∈ p.subData, rs.1 = topDataProperty → rs.2 = topDataProperty)
    (h : lowerTopDataDirect? p = some p') :
    p'.Models i ↔ p.Models i := by
  unfold lowerTopDataDirect? at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨tbox', htbox', keys', hkeys', classAssertions', hca', root', hroot', rfl⟩ := h
  obtain ⟨ht1, ht2⟩ := mapM_option_iff _ _ _ htbox'
  obtain ⟨hk1, hk2⟩ := mapM_option_iff _ _ _ hkeys'
  obtain ⟨hc1, hc2⟩ := mapM_option_iff _ _ _ hca'
  have htwoData : ∃ y₁ y₂ : i.Data, y₁ ≠ y₂ := by
    obtain ⟨v₁, v₂, hne⟩ := htwo
    exact ⟨i.embedValue v₁, i.embedValue v₂, fun he => hne (i.embedValue_injective he)⟩
  have hTboxItem : ∀ q0 q1, lowerInclusion? q0 = some q1 →
      ((∀ x, holds i x q1.sub → holds i x q1.sup) ↔ (∀ x, holds i x q0.sub → holds i x q0.sup)) := by
    intro q0 q1 hq
    simp only [lowerInclusion?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
    obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hq
    exact forall_congr' fun x => imp_congr
      (holds_lowerTopData_iff_gen i hcard hs1 x)
      (holds_lowerTopData_iff_gen i hcard hs2 x)
  have hTboxEq :
      (∀ q ∈ tbox', ∀ x, holds i x q.sub → holds i x q.sup) ↔
        (∀ q ∈ p.tbox, ∀ x, holds i x q.sub → holds i x q.sup) ∧
        (∀ rd ∈ p.dataRanges, isTopData rd.1 = true → ∀ x y, i.dataProperties rd.1 x y → dataHolds i y rd.2) := by
    constructor
    · intro hAll
      refine ⟨fun q hq => ?_, fun rd hrd htop x y _ => ?_⟩
      · obtain ⟨q1, hq1, hmap⟩ := ht2 q (List.mem_append_left _ hq)
        exact (hTboxItem q q1 hmap).mp (hAll q1 hq1)
      · have hqMem : Inclusion.mk .top (.dataAll topDataProperty rd.2) ∈
            p.dataRanges.filterMap fun (dp, d) =>
              if isTopData dp then some ⟨.top, .dataAll topDataProperty d⟩ else none :=
          List.mem_filterMap.mpr ⟨rd, hrd, by simp [htop]⟩
        obtain ⟨q1, hq1, hmap⟩ := ht2 _ (List.mem_append_right _ hqMem)
        have htopHolds := (hTboxItem _ q1 hmap).mp (hAll q1 hq1) x trivial
        exact htopHolds y (i.topDataExt x y)
    · rintro ⟨hTbox, hTopDR⟩ q1 hq1
      obtain ⟨q0, hq0, hmap⟩ := ht1 q1 hq1
      apply (hTboxItem q0 q1 hmap).mpr
      rcases List.mem_append.mp hq0 with h1 | h2
      · exact hTbox q0 h1
      · obtain ⟨rd, hrd, hres⟩ := List.mem_filterMap.mp h2
        split at hres
        · rename_i htop
          simp only [Option.some.injEq] at hres
          subst hres
          intro x _ y _
          have hdp := isTopData_eq htop
          exact hTopDR rd hrd htop x y (hdp ▸ i.topDataExt x y)
        · cases hres
  have hSubEq :
      (∀ rs ∈ p.subData.filter (fun (r, s) => !isTopData r && !isTopData s),
          ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y) ↔
        ∀ rs ∈ p.subData, ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y := by
    constructor
    · intro hF rs hrs x y hxy
      cases h1 : isTopData rs.1 <;> cases h2 : isTopData rs.2
      · exact hF rs (List.mem_filter.mpr ⟨hrs, by simp [h1, h2]⟩) x y hxy
      · rw [isTopData_eq h2]; exact i.topDataExt x y
      · have hs := hclosed rs hrs (isTopData_eq h1)
        rw [hs]; exact i.topDataExt x y
      · rw [isTopData_eq h2]; exact i.topDataExt x y
    · intro hAll rs hrs
      exact hAll rs (List.mem_filter.mp hrs).1
  have hDisjEq :
      ((∀ rs ∈ p.disjointData.filter (fun (r, s) => !isTopData r && !isTopData s),
          ∀ x y, ¬ (i.dataProperties rs.1 x y ∧ i.dataProperties rs.2 x y)) ∧
       ∀ c ∈ p.disjointData.filterMap (fun (r, s) =>
          if isTopData r && isTopData s then some Concept.top
          else if isTopData r then some (.dataSome s (.datatype literalDatatype))
          else if isTopData s then some (.dataSome r (.datatype literalDatatype))
          else none), ∀ x, ¬ holds i x c) ↔
        ∀ rs ∈ p.disjointData, ∀ x y, ¬ (i.dataProperties rs.1 x y ∧ i.dataProperties rs.2 x y) := by
    constructor
    · rintro ⟨hF, hForb⟩ rs hrs x y ⟨h1, h2⟩
      cases hr : isTopData rs.1 <;> cases hs : isTopData rs.2
      · exact hF rs (List.mem_filter.mpr ⟨hrs, by simp [hr, hs]⟩) x y ⟨h1, h2⟩
      · exact hForb (.dataSome rs.1 (.datatype literalDatatype))
          (List.mem_filterMap.mpr ⟨rs, hrs, by simp [hr, hs]⟩) x ⟨y, h1, i.literalDatatypeExt y⟩
      · exact hForb (.dataSome rs.2 (.datatype literalDatatype))
          (List.mem_filterMap.mpr ⟨rs, hrs, by simp [hr, hs]⟩) x ⟨y, h2, i.literalDatatypeExt y⟩
      · exact hForb .top (List.mem_filterMap.mpr ⟨rs, hrs, by simp [hr, hs]⟩) x trivial
    · intro hAll
      refine ⟨fun rs hrs => hAll rs (List.mem_filter.mp hrs).1, fun c hc x hx => ?_⟩
      obtain ⟨rs, hrs, hres⟩ := List.mem_filterMap.mp hc
      cases hr : isTopData rs.1 <;> cases hs : isTopData rs.2 <;> simp only [hr, hs,
        Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hres
      · cases hres
      · subst hres
        obtain ⟨y, hy, _⟩ := hx
        exact hAll rs hrs x y ⟨hy, isTopData_eq hs ▸ i.topDataExt x y⟩
      · subst hres
        obtain ⟨y, hy, _⟩ := hx
        exact hAll rs hrs x y ⟨isTopData_eq hr ▸ i.topDataExt x y, hy⟩
      · subst hres
        obtain ⟨y⟩ := i.dataNonempty
        exact hAll rs hrs x y ⟨isTopData_eq hr ▸ i.topDataExt x y, isTopData_eq hs ▸ i.topDataExt x y⟩
  have hFuncEq :
      ((∀ r ∈ p.funcData.filter (!isTopData ·),
          ∀ x y z, i.dataProperties r x y → i.dataProperties r x z → y = z) ∧
       ∀ c ∈ p.funcData.filterMap (fun r => if isTopData r then some Concept.top else none),
          ∀ x, ¬ holds i x c) ↔
        ∀ r ∈ p.funcData, ∀ x y z, i.dataProperties r x y → i.dataProperties r x z → y = z := by
    constructor
    · rintro ⟨hF, hForb⟩ r hr x y z hy hz
      cases htop : isTopData r
      · exact hF r (List.mem_filter.mpr ⟨hr, by simp [htop]⟩) x y z hy hz
      · exact (hForb .top (List.mem_filterMap.mpr ⟨r, hr, by simp [htop]⟩) x trivial).elim
    · intro hAll
      refine ⟨fun r hr => hAll r (List.mem_filter.mp hr).1, fun c hc x _ => ?_⟩
      obtain ⟨r, hr, hres⟩ := List.mem_filterMap.mp hc
      cases htop : isTopData r <;> simp [htop] at hres
      obtain ⟨y₁, y₂, hne⟩ := htwoData
      have hdp := isTopData_eq htop
      exact hne (hAll r hr x y₁ y₂ (hdp ▸ i.topDataExt x y₁) (hdp ▸ i.topDataExt x y₂))
  have hNegDAEq :
      ((∀ ral ∈ p.negDataAssertions.filter (fun (r, _, _) => !isTopData r),
          ¬ i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2)) ∧
       ∀ c ∈ p.negDataAssertions.filterMap (fun (r, _, _) => if isTopData r then some Concept.top else none),
          ∀ x, ¬ holds i x c) ↔
        ∀ ral ∈ p.negDataAssertions, ¬ i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2) := by
    constructor
    · rintro ⟨hF, hForb⟩ ral hral
      cases htop : isTopData ral.1
      · exact hF ral (List.mem_filter.mpr ⟨hral, by simp [htop]⟩)
      · obtain ⟨x⟩ := i.objectNonempty
        exact (hForb .top (List.mem_filterMap.mpr ⟨ral, hral, by simp [htop]⟩) x trivial).elim
    · intro hAll
      refine ⟨fun ral hral => hAll ral (List.mem_filter.mp hral).1, fun c hc _ _ => ?_⟩
      obtain ⟨ral, hral, hres⟩ := List.mem_filterMap.mp hc
      cases htop : isTopData ral.1 <;> simp [htop] at hres
      exact hAll ral hral (isTopData_eq htop ▸ i.topDataExt _ _)
  have hDAEq :
      (∀ ral ∈ p.dataAssertions.filter (fun (r, _, _) => !isTopData r),
          i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2)) ↔
        ∀ ral ∈ p.dataAssertions, i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2) := by
    constructor
    · intro hF ral hral
      cases htop : isTopData ral.1
      · exact hF ral (List.mem_filter.mpr ⟨hral, by simp [htop]⟩)
      · exact isTopData_eq htop ▸ i.topDataExt _ _
    · intro hAll ral hral
      exact hAll ral (List.mem_filter.mp hral).1
  have hKeyEq :
      (∀ k ∈ keys', ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
          (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
          (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) ↔
        ∀ k ∈ p.keys, ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
          (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
          (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y := by
    have hSingle (k0 k1 : KeyAxiom) (hmap : lowerKey? k0 = some k1) :
        (∀ x y, holds i x k1.cls → holds i y k1.cls → i.named x → i.named y →
            (∀ r ∈ k1.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
            (∀ dp ∈ k1.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) ↔
          ∀ x y, holds i x k0.cls → holds i y k0.cls → i.named x → i.named y →
            (∀ r ∈ k0.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
            (∀ dp ∈ k0.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y := by
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hmap
      have hdpCond (x y : i.Object) :
          (∀ dp ∈ k0.dataProps.filter (!isTopData ·), ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) ↔
          (∀ dp ∈ k0.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) := by
        constructor
        · intro hF dp hdp
          cases htop : isTopData dp
          · exact hF dp (List.mem_filter.mpr ⟨hdp, by simp [htop]⟩)
          · obtain ⟨z⟩ := i.dataNonempty
            exact ⟨z, isTopData_eq htop ▸ i.topDataExt x z, isTopData_eq htop ▸ i.topDataExt y z⟩
        · intro hAll dp hdp
          exact hAll dp (List.mem_filter.mp hdp).1
      refine forall_congr' fun x => forall_congr' fun y =>
        imp_congr (holds_lowerTopData_iff_gen i hcard hc' x)
          (imp_congr (holds_lowerTopData_iff_gen i hcard hc' y)
            (imp_congr Iff.rfl (imp_congr Iff.rfl (imp_congr Iff.rfl
              (imp_congr (hdpCond x y) Iff.rfl)))))
    constructor
    · intro hAll k0 hk0
      obtain ⟨k1, hk1Mem, hmap⟩ := hk2 k0 hk0
      exact (hSingle k0 k1 hmap).mp (hAll k1 hk1Mem)
    · intro hAll k1 hk1Mem
      obtain ⟨k0, hk0, hmap⟩ := hk1 k1 hk1Mem
      exact (hSingle k0 k1 hmap).mpr (hAll k0 hk0)
  have hCAEq :
      (∀ ac ∈ classAssertions', holds i (i.individuals ac.1) ac.2) ↔
        ∀ ac ∈ p.classAssertions, holds i (i.individuals ac.1) ac.2 := by
    constructor
    · intro hAll ac hac
      obtain ⟨ac1, hac1, hmap⟩ := hc2 ac hac
      obtain ⟨c', hc', heq⟩ := Option.map_eq_some_iff.mp hmap
      cases heq
      exact (holds_lowerTopData_iff_gen i hcard hc' _).mp (hAll _ hac1)
    · intro hAll ac1 hac1
      obtain ⟨ac0, hac0, hmap⟩ := hc1 ac1 hac1
      obtain ⟨c', hc', heq⟩ := Option.map_eq_some_iff.mp hmap
      cases heq
      exact (holds_lowerTopData_iff_gen i hcard hc' _).mpr (hAll ac0 hac0)
  constructor
  · intro hm
    have ht := hm.tbox
    simp only [List.forall_mem_append, List.forall_mem_map, holds] at ht
    obtain ⟨htMain, ⟨hDisjF, hFuncF⟩, hNegF⟩ := ht
    obtain ⟨hTbox, hTopDR⟩ := hTboxEq.mp htMain
    refine ⟨hTbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hSubEq.mp hm.subData, hDisjEq.mp ⟨hm.disjointData, hDisjF⟩, hFuncEq.mp ⟨hm.funcData, hFuncF⟩,
      ?_, hKeyEq.mp hm.keys, hCAEq.mp hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
      hm.sameInds, hm.diffInds, hDAEq.mp hm.dataAssertions, hNegDAEq.mp ⟨hm.negDataAssertions, hNegF⟩⟩
    intro rd hrd x y hxy
    cases htop : isTopData rd.1
    · exact hm.dataRanges rd (List.mem_filter.mpr ⟨hrd, by simp [htop]⟩) x y hxy
    · exact hTopDR rd hrd htop x y hxy
  · intro hm
    obtain ⟨hDisjKeep, hDisjF⟩ := hDisjEq.mpr hm.disjointData
    obtain ⟨hFuncKeep, hFuncF⟩ := hFuncEq.mpr hm.funcData
    obtain ⟨hNegKeep, hNegF⟩ := hNegDAEq.mpr hm.negDataAssertions
    refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hSubEq.mpr hm.subData, hDisjKeep, hFuncKeep, ?_, hKeyEq.mpr hm.keys, hCAEq.mpr hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hDAEq.mpr hm.dataAssertions,
      hNegKeep⟩
    · simp only [List.forall_mem_append, List.forall_mem_map, holds]
      exact ⟨hTboxEq.mpr ⟨hm.tbox, fun rd hrd _ => hm.dataRanges rd hrd⟩, ⟨hDisjF, hFuncF⟩, hNegF⟩
    · intro rd hrd
      exact hm.dataRanges rd (List.mem_filter.mp hrd).1

def hasTopDataConcept : Concept → Bool
  | .conj a b | .disj a b => hasTopDataConcept a || hasTopDataConcept b
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => hasTopDataConcept c
  | .dataSome dp _ | .dataAll dp _ | .dataValue dp _ _ | .dataMin _ dp _ | .dataMax _ dp _ =>
    isTopData dp
  | _ => false

/-- Check whether a normalized problem mentions `owl:topDataProperty` anywhere. -/
def usesTopData (p : Problem) : Bool :=
  hasTopDataConcept p.root ||
  p.tbox.any (fun q => hasTopDataConcept q.sub || hasTopDataConcept q.sup) ||
  p.subData.any (fun (r, s) => isTopData r || isTopData s) ||
  p.disjointData.any (fun (r, s) => isTopData r || isTopData s) ||
  p.funcData.any isTopData ||
  p.dataRanges.any (fun (r, _) => isTopData r) ||
  p.keys.any (fun k => hasTopDataConcept k.cls || k.dataProps.any isTopData) ||
  p.classAssertions.any (fun (_, c) => hasTopDataConcept c) ||
  p.dataAssertions.any (fun (r, _, _) => isTopData r) ||
  p.negDataAssertions.any (fun (r, _, _) => isTopData r)

/-- Eliminate `owl:topDataProperty` (and every data property forced universal by
`subData`) from a normalized problem. Returns `some p` immediately with zero
overhead when `owl:topDataProperty` does not occur. -/
def lowerTopData? (p : Problem) : Option Problem :=
  if !usesTopData p then some p
  else lowerTopDataDirect? (collapseUnivDataProps p)

private theorem collapseUnivDataProps_closed (p : Problem) :
    ∀ rs ∈ (collapseUnivDataProps p).subData, rs.1 = topDataProperty → rs.2 = topDataProperty := by
  unfold collapseUnivDataProps
  dsimp only
  split
  · simp [unsatDataProblem]
  · intro rs hrs h1
    obtain ⟨⟨r, s⟩, hrs0, rfl⟩ := List.mem_map.mp hrs
    dsimp only at h1 ⊢
    unfold substUnivData at h1 ⊢
    by_cases hr : (univDataProps p.subData).contains r = true
    · have hs : s ∈ univDataProps p.subData :=
        univDataProps_closed hrs0 (List.contains_iff_mem.mp hr)
      simp only [List.contains_iff_mem.mpr hs, ↓reduceIte]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h1
      subst h1
      have htop : (univDataProps p.subData).contains topDataProperty = true :=
        List.contains_iff_mem.mpr (topDataProperty_mem_univDataProps p.subData)
      exact (hr htop).elim

private theorem lowerTopDataDirect_satWith_iff_gen {dm : DatatypeMap}
    (htwo : ∃ v₁ v₂ : dm.Value, v₁ ≠ v₂)
    (hcard : ∀ (i : Interpretation dm) d n, isWiderDataRange d = true →
      (dataRangeHasAtLeast d n = true ↔ AtLeast n (fun y => dataHolds i y d)))
    {p p' : Problem}
    (hclosed : ∀ rs ∈ p.subData, rs.1 = topDataProperty → rs.2 = topDataProperty)
    (h : lowerTopDataDirect? p = some p') :
    p'.SatWith dm ↔ p.SatWith dm := by
  have hroot : ∃ r', lowerTopDataConcept? p.root = some r' ∧ p'.root = r' := by
    unfold lowerTopDataDirect? at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, r', hr', rfl⟩ := h
    exact ⟨r', hr', rfl⟩
  obtain ⟨r', hr', hpr'⟩ := hroot
  simp only [Problem.SatWith]
  refine exists_congr fun i => and_congr
    (lowerTopDataDirect_models_iff_gen i htwo (hcard i) hclosed h) ?_
  rw [hpr']
  exact exists_congr fun x => holds_lowerTopData_iff_gen i (hcard i) hr' x

theorem lowerTopData_sat_iff {p p' : Problem} (h : lowerTopData? p = some p') :
    p'.Sat ↔ p.Sat := by
  unfold lowerTopData? at h
  split at h
  · cases h; exact Iff.rfl
  · exact (lowerTopDataDirect_satWith_iff_gen (dm := datatypeMap)
      ⟨.boolean true, .boolean false, fun h => by cases h⟩
      (fun i d n hd => dataRangeHasAtLeast_iff hd n i)
      (collapseUnivDataProps_closed p) h).trans
      (collapseUnivDataProps_satWith_iff p)

theorem lowerTopData_real_sat_iff {p p' : Problem} (h : lowerTopData? p = some p') :
    p'.SatWith realDatatypeMap ↔ p.SatWith realDatatypeMap := by
  unfold lowerTopData? at h
  split at h
  · cases h; exact Iff.rfl
  · exact (lowerTopDataDirect_satWith_iff_gen (dm := realDatatypeMap)
      ⟨.inl (.boolean true), .inl (.boolean false), fun h => by cases h⟩
      (fun i d n hd => dataRangeHasAtLeast_real_iff hd n i)
      (collapseUnivDataProps_closed p) h).trans
      (collapseUnivDataProps_satWith_iff p)

#print axioms dataRangeHasAtLeast_iff
#print axioms dataRangeHasAtLeast_real_iff
#print axioms lowerTopData_sat_iff
#print axioms lowerTopData_real_sat_iff

end Sabrina.OWL2.SROIQD.Termination.WiderData
