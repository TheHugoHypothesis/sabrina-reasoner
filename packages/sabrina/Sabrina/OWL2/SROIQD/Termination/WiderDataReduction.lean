import Sabrina.OWL2.SROIQD.Termination.OWLUniversal
import Sabrina.OWL2.SROIQD.Termination.WiderDataAlgebra
import Sabrina.OWL2.SROIQD.Termination.BuiltInDataProps
import Sabrina.OWL2.SROIQD.Termination.UniversalRoleAxioms

/-!
Verified finite-cap Venn-cell integer encoding for wider OWL 2 DL datatypes and
facets (`WiderDataReduction`).

Reduces any `Problem` using the wider exact datatype/facet fragment of
`WiderDataAlgebra` (`owl:real`, `owl:rational`, `xsd:decimal` with all four order
facets, `xsd:integer` + 12 subtypes, the string hierarchy, length facets
on `xsd:string`/`rdf:PlainLiteral`/`xsd:anyURI`/`xsd:hexBinary`/`xsd:base64Binary`,
`xsd:dateTime`/`xsd:dateTimeStamp`, `rdf:XMLLiteral`, `xsd:boolean`, and `oneOf`
enumerations) to an equisatisfiable `Problem` whose data ranges are finite unions
of `xsd:integer` intervals (`DataRange.isSROIQD = true`), and composes this
reduction with `decideWithTopRoleAxioms?` to obtain `decideWithWiderDataRanges?`.
-/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination
open Sabrina.OWL2.SROIQD.Termination.BlockedForest
open Sabrina.RoleChains (findRank)

/-! ### 1. Constructive base-10 natural literals and integer-interval data ranges -/

private def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

private theorem asciiDigit_digitChar (d : Nat) : AsciiDigit (digitChar d) := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => decide
  | _ + 9 => simp only [digitChar]; decide

private theorem decimalValue_digitChar {d : Nat} (hd : d < 10) :
    decimalValue [digitChar d] = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

def natToDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n]
  else natToDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n

private theorem decimalValue_append_singleton (cs : List Char) (c : Char) :
    decimalValue (cs ++ [c]) = decimalValue cs * 10 + decimalValue [c] := by
  induction cs with
  | nil => simp [decimalValue]
  | cons a rest ih =>
    simp only [List.cons_append, decimalValue, List.length_append, List.length_singleton, ih]
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem magnitudeLexical_natToDigits (n : Nat) :
    MagnitudeLexical (natToDigits n) n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natToDigits
    split
    · rename_i hlt
      refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact asciiDigit_digitChar n
      · exact (decimalValue_digitChar hlt).symm
    · rename_i hge
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      obtain ⟨hne, hall, hval⟩ := ih (n / 10) hlt
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hall c h1
        · simp only [List.mem_singleton] at h2; subst h2; exact asciiDigit_digitChar (n % 10)
      · rw [decimalValue_append_singleton, ← hval, decimalValue_digitChar (Nat.mod_lt n (by decide))]
        omega

/-- Constructive `xsd:integer` literal denoting `Int.ofNat n`. -/
def natLit (n : Nat) : Literal :=
  ⟨String.ofList (natToDigits n), xsd "integer"⟩

theorem decodeLiteral_natLit (n : Nat) :
    decodeLiteral (natLit n) = some (.integer (Int.ofNat n)) := by
  have hb : integerBounds (xsd "integer") = some {} := rfl
  rw [natLit, decodeInteger_iff hb]
  exact ⟨SignedIntegerLexical.unsigned (by simpa using magnitudeLexical_natToDigits n), trivial, trivial⟩

/-- Closed `xsd:integer` interval `[lo, hi]` as a `DataRange.isSROIQD` atom. -/
def intIntervalDR (lo hi : Nat) : DataRange :=
  .restriction (xsd "integer")
    [⟨xsd "minInclusive", natLit lo⟩, ⟨xsd "maxInclusive", natLit hi⟩]

private theorem rat_ofInt_le_iff (a b : Int) : Rat.ofInt a ≤ Rat.ofInt b ↔ a ≤ b := by
  simp [Rat.le_iff]

theorem dataHolds_intIntervalDR_iff (i : Interpretation datatypeMap) (y : i.Data) (lo hi : Nat) :
    dataHolds i y (intIntervalDR lo hi) ↔
      ∃ n : Nat, lo ≤ n ∧ n ≤ hi ∧ y = i.embedValue (.integer (Int.ofNat n)) := by
  have hsup : datatypeMap.builtin (xsd "integer") := (by decide : supportedDatatype (xsd "integer") = true)
  have hdecLo := decodeLiteral_natLit lo
  have hdecHi := decodeLiteral_natLit hi
  simp only [intIntervalDR, dataHolds, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, i.datatypeAgreement (xsd "integer") hsup y]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hlo, hhi⟩
    obtain ⟨z, _, rfl⟩ := (valueSpace_integerSubtype_iff (t := xsd "integer") (bounds := {}) rfl v).mp hv
    have hlo' := (checkFacet_iff _ _ _ _).mp ((facetHolds_iff_check i _ _ _ _ hdecLo).mp hlo)
    have hhi' := (checkFacet_iff _ _ _ _).mp ((facetHolds_iff_check i _ _ _ _ hdecHi).mp hhi)
    simp only [facetSpace] at hlo' hhi'
    obtain ⟨_, o1, ho1, hh1⟩ := hlo'
    obtain ⟨_, o2, ho2, hh2⟩ := hhi'
    have ho1' : o1 = .minInclusive := Option.some.inj (ho1.symm.trans (by decide))
    have ho2' : o2 = .maxInclusive := Option.some.inj (ho2.symm.trans (by decide))
    subst ho1'; subst ho2'
    simp only [OrderFacet.holds, rat_ofInt_le_iff, Int.ofNat_eq_natCast] at hh1 hh2
    have hlo' : (lo : Int) ≤ z := hh1
    have hhi' : z ≤ (hi : Int) := hh2
    refine ⟨z.toNat, by omega, by omega, ?_⟩
    congr 2
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]
  · rintro ⟨n, hlo, hhi, rfl⟩
    have hv : valueSpace (xsd "integer") (.integer (Int.ofNat n)) :=
      (valueSpace_integerSubtype_iff (t := xsd "integer") (bounds := {}) rfl _).mpr
        ⟨Int.ofNat n, ⟨trivial, trivial⟩, rfl⟩
    refine ⟨⟨.integer (Int.ofNat n), hv, rfl⟩, ?_, ?_⟩
    · apply (facetHolds_iff_check i _ _ _ _ hdecLo).mpr
      apply (checkFacet_iff _ _ _ _).mpr
      exact ⟨hv, .minInclusive, rfl, by simp [OrderFacet.holds, rat_ofInt_le_iff]; omega⟩
    · apply (facetHolds_iff_check i _ _ _ _ hdecHi).mpr
      apply (checkFacet_iff _ _ _ _).mpr
      exact ⟨hv, .maxInclusive, rfl, by simp [OrderFacet.holds, rat_ofInt_le_iff]; omega⟩

/-- Finite union of closed `xsd:integer` intervals. -/
def intIntervalsDR : List (Nat × Nat) → DataRange
  | [] => .complement (.datatype literalDatatype)
  | [p] => intIntervalDR p.1 p.2
  | p :: rest => .union (intIntervalDR p.1 p.2) (intIntervalsDR rest)

theorem dataHolds_intIntervalsDR_iff (i : Interpretation datatypeMap) (y : i.Data)
    (ivs : List (Nat × Nat)) :
    dataHolds i y (intIntervalsDR ivs) ↔
      ∃ p ∈ ivs, ∃ n : Nat, p.1 ≤ n ∧ n ≤ p.2 ∧ y = i.embedValue (.integer (Int.ofNat n)) := by
  induction ivs with
  | nil =>
    simp [intIntervalsDR, dataHolds, i.literalDatatypeExt y]
  | cons p rest ih =>
    cases rest with
    | nil =>
      simp only [intIntervalsDR, List.mem_singleton, exists_eq_left, dataHolds_intIntervalDR_iff]
    | cons q qs =>
      simp only [intIntervalsDR, dataHolds, dataHolds_intIntervalDR_iff, ih, List.mem_cons,
        exists_eq_or_imp]

def allSlotsDR (totalSlots : Nat) : DataRange :=
  if totalSlots = 0 then .complement (.datatype literalDatatype)
  else intIntervalDR 0 (totalSlots - 1)

theorem dataHolds_allSlotsDR_iff (i : Interpretation datatypeMap) (y : i.Data) (totalSlots : Nat) :
    dataHolds i y (allSlotsDR totalSlots) ↔
      ∃ n : Nat, n < totalSlots ∧ y = i.embedValue (.integer (Int.ofNat n)) := by
  unfold allSlotsDR
  split
  · rename_i hz
    subst hz
    simp [dataHolds, i.literalDatatypeExt y]
  · rename_i hnz
    rw [dataHolds_intIntervalDR_iff]
    constructor
    · rintro ⟨n, _, hle, rfl⟩; exact ⟨n, by omega, rfl⟩
    · rintro ⟨n, hlt, rfl⟩; exact ⟨n, Nat.zero_le _, by omega, rfl⟩

/-! ### 2. Problem-level data collection, witness demand, and admissibility -/

def _root_.Sabrina.OWL2.SROIQD.Concept.dataRangesOf : Concept → List DataRange
  | .conj a b | .disj a b => a.dataRangesOf ++ b.dataRangesOf
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.dataRangesOf
  | .dataSome _ d | .dataAll _ d | .dataMin _ _ d | .dataMax _ _ d => [d]
  | _ => []

def _root_.Sabrina.OWL2.SROIQD.Concept.dataLiteralsOf : Concept → List Literal
  | .conj a b | .disj a b => a.dataLiteralsOf ++ b.dataLiteralsOf
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.dataLiteralsOf
  | .dataValue _ l _ => [l]
  | _ => []

def _root_.Sabrina.OWL2.SROIQD.Concept.dataPropsOf : Concept → List IRI
  | .conj a b | .disj a b => a.dataPropsOf ++ b.dataPropsOf
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.dataPropsOf
  | .dataSome dp _ | .dataAll dp _ | .dataValue dp _ _
  | .dataMin _ dp _ | .dataMax _ dp _ => [dp]
  | _ => []

def _root_.Sabrina.OWL2.SROIQD.Concept.dataDemand : Concept → Nat
  | .conj a b | .disj a b => a.dataDemand + b.dataDemand
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.dataDemand
  | .dataSome _ _ => 1
  | .dataAll _ _ => 1
  | .dataMin n _ _ => n
  | .dataMax n _ _ => n + 1
  | _ => 0

def _root_.Sabrina.OWL2.SROIQD.Problem.allConcepts (p : Problem) : List Concept :=
  p.root ::
  (((p.tbox.flatMap fun q => [q.sub, q.sup]) ++
    (p.keys.map fun k => k.cls)) ++
    (p.classAssertions.map Prod.snd))

def _root_.Sabrina.OWL2.SROIQD.Problem.allDataProps (p : Problem) : List IRI :=
  ((p.allConcepts.flatMap Concept.dataPropsOf) ++
    (p.dataRanges.map Prod.fst) ++
    (p.subData.flatMap fun ab => [ab.1, ab.2]) ++
    (p.disjointData.flatMap fun ab => [ab.1, ab.2]) ++
    p.funcData ++
    (p.keys.flatMap KeyAxiom.dataProps) ++
    (p.dataAssertions.map Prod.fst) ++
    (p.negDataAssertions.map Prod.fst)).eraseDups

def _root_.Sabrina.OWL2.SROIQD.Problem.allDataLiterals (p : Problem) : List Literal :=
  ((p.allConcepts.flatMap Concept.dataLiteralsOf) ++
    (p.dataAssertions.map fun x => x.2.2) ++
    (p.negDataAssertions.map fun x => x.2.2)).eraseDups

def _root_.Sabrina.OWL2.SROIQD.Problem.allDataRanges (p : Problem) : List DataRange :=
  (p.allConcepts.flatMap Concept.dataRangesOf) ++ (p.dataRanges.map Prod.snd)

def _root_.Sabrina.OWL2.SROIQD.Problem.allDataAtoms (p : Problem) : List DataRange :=
  (p.allDataRanges.flatMap atomsOfDataRange).eraseDups

def _root_.Sabrina.OWL2.SROIQD.Problem.localDataDemand (p : Problem) : Nat :=
  (p.allConcepts.map Concept.dataDemand).sum

def _root_.Sabrina.OWL2.SROIQD.Problem.widerWitnessCap (p : Problem) : Nat :=
  let mult := if p.keys.all (fun k => k.dataProps.isEmpty) then 1 else 1 + p.nominals.length
  max 1 (mult * p.localDataDemand)

private theorem allPartitions_mem_sub {atoms pos neg : List DataRange}
    (hmem : (pos, neg) ∈ allPartitions atoms) :
    (∀ a ∈ pos, a ∈ atoms) ∧ (∀ a ∈ neg, a ∈ atoms) ∧
    (pos.length + neg.length = atoms.length) ∧
    (∀ a ∈ atoms, a ∈ pos ∨ a ∈ neg) := by
  induction atoms generalizing pos neg with
  | nil =>
    simp only [allPartitions, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    simp
  | cons a rest ih =>
    simp only [allPartitions, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨p', n'⟩, hpn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hmem
    · obtain ⟨hp, hn, hlen, hcov⟩ := ih hpn
      refine ⟨fun x hx => ?_, fun x hx => List.mem_cons_of_mem _ (hn x hx), by simp; omega, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hp x hx')
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact .inl (List.mem_cons_self ..)
        · rcases hcov x hx' with h1 | h2
          · exact .inl (List.mem_cons_of_mem _ h1)
          · exact .inr h2
    · obtain ⟨hp, hn, hlen, hcov⟩ := ih hpn
      refine ⟨fun x hx => List.mem_cons_of_mem _ (hp x hx), fun x hx => ?_, by simp; omega, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hn x hx')
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact .inr (List.mem_cons_self ..)
        · rcases hcov x hx' with h1 | h2
          · exact .inl h1
          · exact .inr (List.mem_cons_of_mem _ h2)

private theorem vennPartitions_mem_sub {atoms pos neg : List DataRange}
    (hpart : (pos, neg) ∈ vennPartitions atoms) :
    (∀ a ∈ pos, a ∈ atoms) ∧ (∀ a ∈ neg, a ∈ atoms) ∧
    (pos.length + neg.length = atoms.length) ∧
    (∀ a ∈ atoms, a ∈ pos ∨ a ∈ neg) :=
  allPartitions_mem_sub (List.mem_eraseDups.mp hpart)

private theorem allOneOfValues_length_of_allPartitions {atoms pos neg : List DataRange}
    (hmem : (pos, neg) ∈ allPartitions atoms) :
    (allOneOfValues (pos ++ neg)).length = (allOneOfValues atoms).length := by
  induction atoms generalizing pos neg with
  | nil =>
    simp only [allPartitions, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem; rfl
  | cons a rest ih =>
    simp only [allPartitions, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨p', n'⟩, hpn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hmem
    · have := ih hpn
      simp only [allOneOfValues, List.flatMap_append, List.flatMap_cons, List.length_append] at this ⊢
      omega
    · have := ih hpn
      simp only [allOneOfValues, List.flatMap_append, List.flatMap_cons, List.length_append] at this ⊢
      omega

private theorem widerAtomsAdmissible_partition {lits : List Literal}
    {atoms pos neg : List DataRange}
    (hadm : widerAtomsAdmissible (.oneOf lits :: atoms) = true)
    (hpart : (pos, neg) ∈ vennPartitions atoms) :
    widerAtomsAdmissible (pos ++ (.oneOf lits :: neg)) = true := by
  obtain ⟨hpSub, hnSub, _, _⟩ := vennPartitions_mem_sub hpart
  have hsub : ∀ a ∈ pos ++ (.oneOf lits :: neg), a ∈ DataRange.oneOf lits :: atoms := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact List.mem_cons_of_mem _ (hpSub a h1)
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hnSub a h3)
  exact List.all_eq_true.mpr fun a ha => List.all_eq_true.mp hadm a (hsub a ha)

/-! ### 3. Venn-cell slot table and problem encoding -/

structure CellSpec where
  pos : List DataRange
  neg : List DataRange
  lo : Nat
  values : Option (List Value)
  len : Nat
  deriving Repr

private def buildCellTable (K : Nat) (lits : List Literal) :
    Nat → List (List DataRange × List DataRange) → List CellSpec × Nat
  | offset, [] => ([], offset)
  | offset, (pos, neg) :: rest =>
    if neg.contains (.datatype literalDatatype) then
      buildCellTable K lits offset rest
    else if pos.all (· == .datatype literalDatatype) then
      let cs : CellSpec := ⟨pos, neg, offset, none, K⟩
      let (tail, total) := buildCellTable K lits (offset + K) rest
      (cs :: tail, total)
    else
      let ws := sampleWiderCell K pos (.oneOf lits :: neg)
      let cs : CellSpec := ⟨pos, neg, offset, some ws, ws.length⟩
      let (tail, total) := buildCellTable K lits (offset + ws.length) rest
      (cs :: tail, total)

private theorem buildCellTable_total_ge (K : Nat) (lits : List Literal)
    (offset : Nat) (parts : List (List DataRange × List DataRange)) :
    offset ≤ (buildCellTable K lits offset parts).2 := by
  induction parts generalizing offset with
  | nil => exact Nat.le_refl _
  | cons pn rest ih =>
    rcases pn with ⟨pos, neg⟩
    unfold buildCellTable
    split
    · exact ih offset
    · split
      · exact Nat.le_trans (Nat.le_add_right offset K) (ih (offset + K))
      · exact Nat.le_trans (Nat.le_add_right offset _) (ih (offset + _))

private theorem buildCellTable_spec (K : Nat) (lits : List Literal)
    (offset : Nat) (parts : List (List DataRange × List DataRange)) :
    (∀ cs ∈ (buildCellTable K lits offset parts).1,
      (cs.pos, cs.neg) ∈ parts ∧
      offset ≤ cs.lo ∧ cs.lo + cs.len ≤ (buildCellTable K lits offset parts).2 ∧
      cs.neg.contains (.datatype literalDatatype) = false ∧
      match cs.values with
      | none => cs.pos.all (· == .datatype literalDatatype) = true ∧ cs.len = K
      | some ws =>
        cs.pos.all (· == .datatype literalDatatype) = false ∧
        ws = sampleWiderCell K cs.pos (.oneOf lits :: cs.neg) ∧ cs.len = ws.length) ∧
    (∀ cs₁ ∈ (buildCellTable K lits offset parts).1, ∀ cs₂ ∈ (buildCellTable K lits offset parts).1, ∀ n : Nat,
      cs₁.lo ≤ n → n < cs₁.lo + cs₁.len →
      cs₂.lo ≤ n → n < cs₂.lo + cs₂.len → cs₁ = cs₂) ∧
    (∀ n : Nat, offset ≤ n → n < (buildCellTable K lits offset parts).2 →
      ∃ cs ∈ (buildCellTable K lits offset parts).1, cs.lo ≤ n ∧ n < cs.lo + cs.len) ∧
    (∀ pos neg, (pos, neg) ∈ parts → neg.contains (.datatype literalDatatype) = false →
      ∃ cs ∈ (buildCellTable K lits offset parts).1, cs.pos = pos ∧ cs.neg = neg) := by
  induction parts generalizing offset with
  | nil =>
    refine ⟨by simp [buildCellTable], by simp [buildCellTable],
      fun n h1 h2 => by simp [buildCellTable] at h2; omega, by simp [buildCellTable]⟩
  | cons pn rest ih =>
    rcases pn with ⟨pos, neg⟩
    unfold buildCellTable
    split
    · rename_i hnegLit
      obtain ⟨hmem, hdisj, hcov, hhas⟩ := ih offset
      refine ⟨fun cs hcs => ?_, hdisj, hcov, fun p' n' hpn hnlit => ?_⟩
      · obtain ⟨hm, h1, h2, h3, h4⟩ := hmem cs hcs
        exact ⟨List.mem_cons_of_mem _ hm, h1, h2, h3, h4⟩
      · rcases List.mem_cons.mp hpn with heq | hr
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; rw [hnegLit] at hnlit; cases hnlit
        · exact hhas p' n' hr hnlit
    · rename_i hnegNotLit
      have hnegF : neg.contains (.datatype literalDatatype) = false := Bool.eq_false_iff.mpr hnegNotLit
      split
      · rename_i hposLit
        obtain ⟨hmem, hdisj, hcov, hhas⟩ := ih (offset + K)
        have htotGe := buildCellTable_total_ge K lits (offset + K) rest
        refine ⟨fun cs hcs => ?_, ?_, ?_, fun p' n' hpn hnlit => ?_⟩
        · rcases List.mem_cons.mp hcs with rfl | hcs'
          · exact ⟨List.mem_cons_self .., Nat.le_refl _, htotGe, hnegF, hposLit, rfl⟩
          · obtain ⟨hm, h1, h2, h3, h4⟩ := hmem cs hcs'
            exact ⟨List.mem_cons_of_mem _ hm, by omega, h2, h3, h4⟩
        · intro c1 hc1 c2 hc2 n h1l h1h h2l h2h
          rcases List.mem_cons.mp hc1 with rfl | hc1' <;> rcases List.mem_cons.mp hc2 with rfl | hc2'
          · rfl
          · dsimp only at h1l h1h; have := (hmem c2 hc2').2.1; omega
          · dsimp only at h2l h2h; have := (hmem c1 hc1').2.1; omega
          · exact hdisj c1 hc1' c2 hc2' n h1l h1h h2l h2h
        · intro n hlo hhi
          by_cases hlt : n < offset + K
          · exact ⟨⟨pos, neg, offset, none, K⟩, List.mem_cons_self .., hlo, hlt⟩
          · obtain ⟨cs, hcs, h1, h2⟩ := hcov n (by omega) hhi
            exact ⟨cs, List.mem_cons_of_mem _ hcs, h1, h2⟩
        · rcases List.mem_cons.mp hpn with heq | hr
          · obtain ⟨hp', hn'⟩ := Prod.mk.inj heq
            exact ⟨⟨pos, neg, offset, none, K⟩, List.mem_cons_self .., hp'.symm, hn'.symm⟩
          · obtain ⟨cs, hcs, h1, h2⟩ := hhas p' n' hr hnlit
            exact ⟨cs, List.mem_cons_of_mem _ hcs, h1, h2⟩
      · rename_i hposNotLit
        have hposF : pos.all (· == .datatype literalDatatype) = false := Bool.eq_false_iff.mpr hposNotLit
        let ws := sampleWiderCell K pos (.oneOf lits :: neg)
        obtain ⟨hmem, hdisj, hcov, hhas⟩ := ih (offset + ws.length)
        have htotGe := buildCellTable_total_ge K lits (offset + ws.length) rest
        refine ⟨fun cs hcs => ?_, ?_, ?_, fun p' n' hpn hnlit => ?_⟩
        · rcases List.mem_cons.mp hcs with rfl | hcs'
          · exact ⟨List.mem_cons_self .., Nat.le_refl _, htotGe, hnegF, hposF, rfl, rfl⟩
          · obtain ⟨hm, h1, h2, h3, h4⟩ := hmem cs hcs'
            exact ⟨List.mem_cons_of_mem _ hm, by omega, h2, h3, h4⟩
        · intro c1 hc1 c2 hc2 n h1l h1h h2l h2h
          rcases List.mem_cons.mp hc1 with rfl | hc1' <;> rcases List.mem_cons.mp hc2 with rfl | hc2'
          · rfl
          · dsimp only [ws] at h1l h1h; have := (hmem c2 hc2').2.1; dsimp only [ws] at this; omega
          · dsimp only [ws] at h2l h2h; have := (hmem c1 hc1').2.1; dsimp only [ws] at this; omega
          · exact hdisj c1 hc1' c2 hc2' n h1l h1h h2l h2h
        · intro n hlo hhi
          by_cases hlt : n < offset + ws.length
          · exact ⟨⟨pos, neg, offset, some ws, ws.length⟩, List.mem_cons_self .., hlo, hlt⟩
          · obtain ⟨cs, hcs, h1, h2⟩ := hcov n (by omega) hhi
            exact ⟨cs, List.mem_cons_of_mem _ hcs, h1, h2⟩
        · rcases List.mem_cons.mp hpn with heq | hr
          · obtain ⟨hp', hn'⟩ := Prod.mk.inj heq
            exact ⟨⟨pos, neg, offset, some ws, ws.length⟩, List.mem_cons_self .., hp'.symm, hn'.symm⟩
          · obtain ⟨cs, hcs, h1, h2⟩ := hhas p' n' hr hnlit
            exact ⟨cs, List.mem_cons_of_mem _ hcs, h1, h2⟩

structure WiderEncoding where
  K : Nat
  lits : List Literal
  litVals : List Value
  atoms : List DataRange
  cells : List CellSpec
  totalSlots : Nat

def buildWiderEncoding (p : Problem) : Option WiderEncoding :=
  let dprops := p.allDataProps
  let lits := p.allDataLiterals
  let atoms := p.allDataAtoms
  let K := p.widerWitnessCap
  if dprops.all (fun dp => dp != topDataProperty && dp != bottomDataProperty) &&
     lits.all (fun l => (decodeLiteral l).isSome) &&
     widerAtomsAdmissible (.oneOf lits :: atoms) then
    let litVals := (lits.filterMap decodeLiteral).eraseDups
    let parts := vennPartitions atoms
    let (cells, totalSlots) := buildCellTable K lits litVals.length parts
    some ⟨K, lits, litVals, atoms, cells, totalSlots⟩
  else none

private def idxOfList {α : Type} [DecidableEq α] (xs : List α) (x : α) : Nat :=
  match xs with
  | [] => 0
  | a :: rest => if a = x then 0 else idxOfList rest x + 1

private theorem idxOfList_lt {α : Type} [DecidableEq α] {xs : List α} {x : α} (h : x ∈ xs) :
    idxOfList xs x < xs.length := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    simp only [idxOfList, List.length_cons]
    split
    · omega
    · rename_i hne
      rcases List.mem_cons.mp h with rfl | hr
      · exact (hne rfl).elim
      · have := ih hr; omega

private theorem getElem_idxOfList {α : Type} [DecidableEq α] {xs : List α} {x : α} (h : x ∈ xs) :
    xs[idxOfList xs x]'(idxOfList_lt h) = x := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    simp only [idxOfList]
    split
    · rename_i heq; exact heq
    · rename_i hne
      rcases List.mem_cons.mp h with rfl | hr
      · exact (hne rfl).elim
      · exact ih hr

private theorem idxOfList_getElem {α : Type} [DecidableEq α] {xs : List α} (hnd : xs.Nodup)
    {k : Nat} (hk : k < xs.length) :
    idxOfList xs xs[k] = k := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a rest ih =>
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    cases k with
    | zero => simp [idxOfList]
    | succ k' =>
      have hk' : k' < rest.length := by simpa using hk
      have hne : a ≠ rest[k'] := fun heq => hna (heq ▸ List.getElem_mem hk')
      simp only [List.getElem_cons_succ, idxOfList, hne, ↓reduceIte]
      rw [ih hnd' hk']

private theorem idxOfList_inj {α : Type} [DecidableEq α] {xs : List α} {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (heq : idxOfList xs x = idxOfList xs y) : x = y := by
  have h1 := getElem_idxOfList hx
  have h2 := getElem_idxOfList hy
  rw [← h1, ← h2]
  congr

def WiderEncoding.encodeLiteral (enc : WiderEncoding) (l : Literal) : Literal :=
  match decodeLiteral l with
  | some v => natLit (idxOfList enc.litVals v)
  | none => natLit 0

def WiderEncoding.encodeIntervals (enc : WiderEncoding) (d : DataRange) : List (Nat × Nat) :=
  let litIvs := (List.range enc.litVals.length).filterMap fun idx =>
    if h : idx < enc.litVals.length then
      if evalWiderDataRange d enc.litVals[idx] then some (idx, idx) else none
    else none
  let cellIvs := enc.cells.filterMap fun cs =>
    if 0 < cs.len && evalOnPartition cs.pos d then some (cs.lo, cs.lo + cs.len - 1) else none
  litIvs ++ cellIvs

def WiderEncoding.encodeDataRange (enc : WiderEncoding) (d : DataRange) : DataRange :=
  intIntervalsDR (enc.encodeIntervals d)

def WiderEncoding.encodeConcept (enc : WiderEncoding) : Concept → Concept
  | .top => .top
  | .bottom => .bottom
  | .lit n b => .lit n b
  | .nom a b => .nom a b
  | .self r b => .self r b
  | .conj a b => .conj (enc.encodeConcept a) (enc.encodeConcept b)
  | .disj a b => .disj (enc.encodeConcept a) (enc.encodeConcept b)
  | .some r c => .some r (enc.encodeConcept c)
  | .all r c => .all r (enc.encodeConcept c)
  | .min n r c => .min n r (enc.encodeConcept c)
  | .max n r c => .max n r (enc.encodeConcept c)
  | .dataSome dp d => .dataSome dp (enc.encodeDataRange d)
  | .dataAll dp d => .dataAll dp (enc.encodeDataRange d)
  | .dataValue dp l b => .dataValue dp (enc.encodeLiteral l) b
  | .dataMin n dp d => .dataMin n dp (enc.encodeDataRange d)
  | .dataMax n dp d => .dataMax n dp (enc.encodeDataRange d)

def WiderEncoding.encodeProblem (enc : WiderEncoding) (p : Problem) : Problem :=
  let domRanges := p.allDataProps.map fun dp => (dp, allSlotsDR enc.totalSlots)
  { p with
    root := enc.encodeConcept p.root
    tbox := p.tbox.map fun q => ⟨enc.encodeConcept q.sub, enc.encodeConcept q.sup⟩
    keys := p.keys.map fun k => { k with cls := enc.encodeConcept k.cls }
    classAssertions := p.classAssertions.map fun (a, c) => (a, enc.encodeConcept c)
    dataRanges := (p.dataRanges.map fun (dp, d) => (dp, enc.encodeDataRange d)) ++ domRanges
    dataAssertions := p.dataAssertions.map fun (dp, a, l) => (dp, a, enc.encodeLiteral l)
    negDataAssertions := p.negDataAssertions.map fun (dp, a, l) => (dp, a, enc.encodeLiteral l) }

/-- Encode a `Problem` in the wider exact datatype/facet fragment into an
equisatisfiable `Problem` whose data ranges are finite unions of `xsd:integer`
intervals (`DataRange.isSROIQD = true`). -/
def encodeWiderData (p : Problem) : Option Problem :=
  (buildWiderEncoding p).map (·.encodeProblem p)

/-! ### 4. Encoding invariants and reverse direction (`p'.Sat → p.Sat`) -/

private structure ValidEncoding (p : Problem) (enc : WiderEncoding) : Prop where
  hK : enc.K = p.widerWitnessCap
  hlits : enc.lits = p.allDataLiterals
  hatoms : enc.atoms = p.allDataAtoms
  hlitVals : enc.litVals = (enc.lits.filterMap decodeLiteral).eraseDups
  htable : (enc.cells, enc.totalSlots) =
    buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  hdprops : ∀ dp ∈ p.allDataProps, dp ≠ topDataProperty ∧ dp ≠ bottomDataProperty
  hdec : ∀ l ∈ enc.lits, (decodeLiteral l).isSome = true
  hadm : widerAtomsAdmissible (.oneOf enc.lits :: enc.atoms) = true

private theorem buildWiderEncoding_valid {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) : ValidEncoding p enc := by
  unfold buildWiderEncoding at h
  dsimp only at h
  split at h
  · rename_i hcond
    cases h
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hcond
    exact ⟨rfl, rfl, rfl, rfl, rfl, hcond.1.1, hcond.1.2, hcond.2⟩
  · cases h

private theorem validEncoding_litVals_nodup {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) : enc.litVals.Nodup := by
  rw [hv.hlitVals]; exact nodup_eraseDups_list _

private theorem validEncoding_atoms_wider {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) : ∀ a ∈ enc.atoms, isWiderExactAtom a = true := by
  have hall := hv.hadm
  intro a ha
  exact List.all_eq_true.mp hall a (List.mem_cons_of_mem _ ha)

private theorem validEncoding_dataRange_wider {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {d : DataRange} (hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) :
    isWiderDataRange d = true := by
  induction d with
  | complement r ih => exact ih hd
  | intersection a b iha ihb =>
    simp only [isWiderDataRange, Bool.and_eq_true]
    exact ⟨iha fun x hx => hd x (List.mem_eraseDups.mpr (List.mem_append_left _ hx)),
           ihb fun x hx => hd x (List.mem_eraseDups.mpr (List.mem_append_right _ hx))⟩
  | union a b iha ihb =>
    simp only [isWiderDataRange, Bool.and_eq_true]
    exact ⟨iha fun x hx => hd x (List.mem_eraseDups.mpr (List.mem_append_left _ hx)),
           ihb fun x hx => hd x (List.mem_eraseDups.mpr (List.mem_append_right _ hx))⟩
  | datatype _ | restriction _ _ | oneOf _ =>
    exact validEncoding_atoms_wider hv _ (hd _ (List.mem_singleton_self _))

private theorem mem_litVals_iff {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (v : Value) :
    v ∈ enc.litVals ↔ ∃ l ∈ enc.lits, decodeLiteral l = some v := by
  rw [hv.hlitVals, List.mem_eraseDups, List.mem_filterMap]

private theorem decodeLiteral_mem_litVals {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {l : Literal} (hl : l ∈ enc.lits) :
    ∃ v ∈ enc.litVals, decodeLiteral l = some v := by
  obtain ⟨v, hdv⟩ := Option.isSome_iff_exists.mp (hv.hdec l hl)
  exact ⟨v, (mem_litVals_iff hv v).mpr ⟨l, hl, hdv⟩, hdv⟩

private def slotVal_cell_lookup (enc : WiderEncoding) (n : Nat) :
    Option CellSpec :=
  enc.cells.find? fun cs => decide (cs.lo ≤ n ∧ n < cs.lo + cs.len)

private def slotVal (enc : WiderEncoding) (n : Nat) : Value ⊕ Int :=
  if h : n < enc.litVals.length then
    Sum.inl enc.litVals[n]
  else
    match slotVal_cell_lookup enc n with
    | some cs =>
      match cs.values with
      | some ws =>
        if h' : n - cs.lo < ws.length then Sum.inl ws[n - cs.lo] else Sum.inr (Int.ofNat n)
      | none => Sum.inr (Int.ofNat n)
    | none => Sum.inr (-1 - Int.ofNat n)

private theorem slotVal_lt_litVals (enc : WiderEncoding) {n : Nat} (hn : n < enc.litVals.length) :
    slotVal enc n = Sum.inl enc.litVals[n] := by
  simp [slotVal, hn]

private theorem slotVal_in_cell {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    {cs : CellSpec} (hcs : cs ∈ enc.cells) {n : Nat} (hlo : cs.lo ≤ n) (hhi : n < cs.lo + cs.len) :
    slotVal enc n =
      match cs.values with
      | some ws =>
        if h' : n - cs.lo < ws.length then Sum.inl ws[n - cs.lo] else Sum.inr (Int.ofNat n)
      | none => Sum.inr (Int.ofNat n) := by
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  obtain ⟨hmem, hdisj, _, _⟩ := hspec
  have hge : enc.litVals.length ≤ cs.lo := (hmem cs hcs).2.1
  have hnotlt : ¬ (n < enc.litVals.length) := by omega
  have hfind : slotVal_cell_lookup enc n = some cs := by
    unfold slotVal_cell_lookup
    cases hf : enc.cells.find? (fun c => decide (c.lo ≤ n ∧ n < c.lo + c.len)) with
    | none =>
      have := List.find?_eq_none.mp hf cs hcs
      simp [hlo, hhi] at this
    | some c' =>
      have hc'mem := List.mem_of_find?_eq_some hf
      have hc'p := List.find?_some hf
      simp only [decide_eq_true_eq] at hc'p
      have heq := hdisj c' hc'mem cs hcs n hc'p.1 hc'p.2 hlo hhi
      subst heq; rfl
  simp [slotVal, hnotlt, hfind]

private theorem slotVal_in_cell_some {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    {cs : CellSpec} (hcs : cs ∈ enc.cells) {ws : List Value} (hvs : cs.values = some ws)
    {n : Nat} (hlo : cs.lo ≤ n) (hhi : n < cs.lo + cs.len) :
    ∃ h' : n - cs.lo < ws.length, slotVal enc n = Sum.inl ws[n - cs.lo] := by
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  have hlen := (hspec.1 cs hcs).2.2.2.2
  rw [hvs] at hlen
  have h' : n - cs.lo < ws.length := by omega
  refine ⟨h', ?_⟩
  rw [slotVal_in_cell hv hcs hlo hhi, hvs]
  simp [h']

private theorem slotVal_in_cell_none {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    {cs : CellSpec} (hcs : cs ∈ enc.cells) (hvs : cs.values = none)
    {n : Nat} (hlo : cs.lo ≤ n) (hhi : n < cs.lo + cs.len) :
    slotVal enc n = Sum.inr (Int.ofNat n) := by
  rw [slotVal_in_cell hv hcs hlo hhi, hvs]

private theorem sampleWiderCell_not_mem_litVals {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {pos neg : List DataRange}
    {v : Value} (hmem : v ∈ sampleWiderCell enc.K pos (.oneOf enc.lits :: neg)) :
    v ∉ enc.litVals := by
  intro hlit
  obtain ⟨l, hl, hdl⟩ := (mem_litVals_iff hv v).mp hlit
  have hev := (List.mem_filter.mp (List.mem_of_mem_take hmem)).2
  simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, List.forall_mem_cons,
    Bool.not_eq_true'] at hev
  have hne := hev.2.1
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (decodeLiteralsList_isSome (List.all_eq_true.mpr hv.hdec))
  have hvMem : v ∈ vs := by
    have haux : ∀ (ls : List Literal) (ws : List Value),
        decodeLiteralsList ls = some ws → ∀ l' ∈ ls, ∀ v', decodeLiteral l' = some v' → v' ∈ ws := by
      intro ls
      induction ls with
      | nil => intro ws _ l' hl'; cases hl'
      | cons hd tl ih =>
        intro ws hdw l' hl' v' hdv'
        simp only [decodeLiteralsList, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hdw
        obtain ⟨vh, hdh, vt, hdt, rfl⟩ := hdw
        rcases List.mem_cons.mp hl' with rfl | htl
        · rw [hdh] at hdv'; cases hdv'; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih vt hdt l' htl v' hdv')
    exact haux enc.lits vs hvs l hl v hdl
  simp [evalWiderAtom, hvs, hvMem] at hne

/-- Values assigned to concrete slots in the finite data encoding. -/
def WiderEncoding.UsesValue (enc : WiderEncoding) (v : Value) : Prop :=
  v ∈ enc.litVals ∨ ∃ cs ∈ enc.cells, ∃ ws, cs.values = some ws ∧ v ∈ ws

/-- Realization of the concrete slots in a target datatype map. The common
injection preserves data value identity, including across the subjects of a key. -/
structure WiderEncoding.Target (enc : WiderEncoding) (dm : DatatypeMap) where
  value : Value → dm.Value
  injective : ∀ {v w}, value v = value w → v = w
  builtin : ∀ t, supportedDatatype t = true → dm.builtin t
  lexical : ∀ l v, decodeLiteral l = some v → dm.lexicalValue l = some (value v)
  evalAtom : ∀ a ∈ enc.atoms, ∀ v, enc.UsesValue v → ∀ i : Interpretation dm,
    evalWiderAtom a v = true ↔ dataHolds i (i.embedValue (value v)) a

private def standardTarget {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) : enc.Target datatypeMap where
  value := id
  injective := fun h => h
  builtin := fun _ h => h
  lexical := fun _ _ h => h
  evalAtom a ha v _ i := evalWiderAtom_iff (validEncoding_atoms_wider hv a ha) i v

private def WiderEncoding.Target.translate {enc : WiderEncoding} {dm : DatatypeMap}
    (target : enc.Target dm) : Value ⊕ Int → dm.Value ⊕ Int
  | .inl v => .inl (target.value v)
  | .inr n => .inr n

private theorem WiderEncoding.Target.translate_inj {enc : WiderEncoding} {dm : DatatypeMap}
    (target : enc.Target dm) {a b : Value ⊕ Int} (he : target.translate a = target.translate b) :
    a = b := by
  cases a <;> cases b <;> simp [WiderEncoding.Target.translate] at he ⊢ <;> try assumption
  exact target.injective he

private def targetSlot {enc : WiderEncoding} {dm : DatatypeMap}
    (target : enc.Target dm) (n : Nat) : dm.Value ⊕ Int :=
  target.translate (slotVal enc n)

private theorem targetSlot_standard {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (n : Nat) : targetSlot (standardTarget hv) n = slotVal enc n := by
  unfold targetSlot
  cases slotVal enc n <;> rfl

private theorem targetSlot_lit {enc : WiderEncoding} {dm : DatatypeMap}
    (target : enc.Target dm) {n : Nat} (hn : n < enc.litVals.length) :
    targetSlot target n = .inl (target.value enc.litVals[n]) := by
  rw [targetSlot, slotVal_lt_litVals enc hn]
  rfl

private def decodeInterp (i' : Interpretation datatypeMap) (enc : WiderEncoding)
    {dm : DatatypeMap} (target : enc.Target dm) : Interpretation dm where
  Object := i'.Object
  objectNonempty := i'.objectNonempty
  Data := dm.Value ⊕ Int
  dataNonempty := ⟨Sum.inr 0⟩
  embedValue := Sum.inl
  embedValue_injective := Sum.inl.inj
  classes := i'.classes
  objectProperties := i'.objectProperties
  dataProperties dp x y :=
    if dp = topDataProperty then True
    else if dp = bottomDataProperty then False
    else ∃ n : Nat, n < enc.totalSlots ∧ y = targetSlot target n ∧
      i'.dataProperties dp x (i'.embedValue (.integer (Int.ofNat n)))
  individuals := i'.individuals
  datatypes t y := t = literalDatatype ∨ ∃ v, dm.valueSpace t v ∧ Sum.inl v = y
  literalValue l := (dm.lexicalValue l).elim (Sum.inr 0) Sum.inl
  lexicalAgreement l v h := by rw [h]; rfl
  named := i'.named
  namedIndividual := i'.namedIndividual
  thingExt := i'.thingExt
  nothingExt := i'.nothingExt
  topObjectExt := i'.topObjectExt
  bottomObjectExt := i'.bottomObjectExt
  topDataExt _ _ := by simp
  bottomDataExt _ _ := by
    have h : bottomDataProperty ≠ topDataProperty := by decide
    simp [h]
  literalDatatypeExt _ := Or.inl rfl
  datatypeAgreement t ht y := by
    have hn : t ≠ literalDatatype := fun e => dm.literal_not_builtin (e ▸ ht)
    simp [hn]

private theorem slotVal_cell_partitionHolds {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (i' : Interpretation datatypeMap)
    {dm : DatatypeMap} (target : enc.Target dm)
    {cs : CellSpec} (hcs : cs ∈ enc.cells) {n : Nat} (hlo : cs.lo ≤ n) (hhi : n < cs.lo + cs.len) :
    dataHolds (decodeInterp i' enc target) (targetSlot target n) (partitionRange cs.pos cs.neg) := by
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  obtain ⟨hpart, _, _, hnegF, hvalSpec⟩ := hspec.1 cs hcs
  obtain ⟨hpSub, hnSub, _, _⟩ := vennPartitions_mem_sub hpart
  cases hvs : cs.values with
  | some ws =>
    rw [hvs] at hvalSpec
    obtain ⟨_, hwsEq, _⟩ := hvalSpec
    obtain ⟨hidx, hsv⟩ := slotVal_in_cell_some hv hcs hvs hlo hhi
    rw [targetSlot, hsv]
    have hmem : ws[n - cs.lo] ∈ sampleWiderCell enc.K cs.pos (.oneOf enc.lits :: cs.neg) :=
      hwsEq ▸ List.getElem_mem hidx
    have hUsed : enc.UsesValue ws[n - cs.lo] :=
      .inr ⟨cs, hcs, ws, hvs, List.getElem_mem hidx⟩
    have heval := (List.mem_filter.mp (List.mem_of_mem_take hmem)).2
    simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, List.forall_mem_cons,
      Bool.not_eq_true', Bool.eq_false_iff] at heval
    change dataHolds (decodeInterp i' enc target)
      ((decodeInterp i' enc target).embedValue (target.value ws[n - cs.lo])) _
    rw [dataHolds_partitionRange_iff]
    exact ⟨fun a ha => (target.evalAtom a (hpSub a ha) _ hUsed _).mp (heval.1 a ha),
      fun a ha h => heval.2.2 a ha ((target.evalAtom a (hnSub a ha) _ hUsed _).mpr h)⟩
  | none =>
    rw [hvs] at hvalSpec
    obtain ⟨hposLit, _⟩ := hvalSpec
    rw [targetSlot, slotVal_in_cell_none hv hcs hvs hlo hhi]
    refine (dataHolds_partitionRange_iff (decodeInterp i' enc target) (Sum.inr (Int.ofNat n))
      cs.pos cs.neg).mpr ⟨fun a ha => ?_, fun a ha hholds => ?_⟩
    · have heq := beq_iff_eq.mp (List.all_eq_true.mp hposLit a ha)
      subst heq
      exact (decodeInterp i' enc target).literalDatatypeExt _
    · have hne : a ≠ .datatype literalDatatype := by
        intro rfl
        have := List.contains_iff_mem.mpr ha
        rw [hnegF] at this; cases this
      have hAtom := validEncoding_atoms_wider hv a (hnSub a ha)
      cases a with
      | datatype t =>
        have hs := target.builtin t (widerDatatype_supported hAtom
          (fun h => hne (congrArg DataRange.datatype h)))
        obtain ⟨v, _, he⟩ := ((decodeInterp i' enc target).datatypeAgreement t hs _).mp hholds
        cases he
      | restriction t fs =>
        have hs := target.builtin t (widerRestriction_supported hAtom).1
        obtain ⟨v, _, he⟩ := ((decodeInterp i' enc target).datatypeAgreement t hs _).mp hholds.1
        cases he
      | oneOf ls =>
        obtain ⟨l, hl, he⟩ := hholds
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp (widerOneOf_decoded hAtom) l hl)
        rw [(decodeInterp i' enc target).lexicalAgreement l (target.value v) (target.lexical l v hv)] at he
        cases he
      | _ => cases hAtom

private theorem slotVal_inj {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    (i' : Interpretation datatypeMap) {n₁ n₂ : Nat}
    (h1 : n₁ < enc.totalSlots) (h2 : n₂ < enc.totalSlots)
    (heq : slotVal enc n₁ = slotVal enc n₂) : n₁ = n₂ := by
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  obtain ⟨hmem, hdisj, hcov, _⟩ := hspec
  by_cases hl1 : n₁ < enc.litVals.length <;> by_cases hl2 : n₂ < enc.litVals.length
  · rw [slotVal_lt_litVals enc hl1, slotVal_lt_litVals enc hl2] at heq
    have hvEq := Sum.inl.inj heq
    have hidx1 := idxOfList_getElem (validEncoding_litVals_nodup hv) hl1
    have hidx2 := idxOfList_getElem (validEncoding_litVals_nodup hv) hl2
    rw [← hidx1, ← hidx2, hvEq]
  · obtain ⟨c2, hc2, h2l, h2h⟩ := hcov n₂ (by omega) h2
    have hpart2 := (hmem c2 hc2).1
    have hval2 := (hmem c2 hc2).2.2.2.2
    rw [slotVal_lt_litVals enc hl1] at heq
    cases hvs2 : c2.values with
    | none => rw [slotVal_in_cell_none hv hc2 hvs2 h2l h2h] at heq; cases heq
    | some ws2 =>
      rw [hvs2] at hval2
      obtain ⟨hidx2, hsv2⟩ := slotVal_in_cell_some hv hc2 hvs2 h2l h2h
      rw [hsv2] at heq
      have hvEq := Sum.inl.inj heq
      have hmemWs : ws2[n₂ - c2.lo] ∈ sampleWiderCell enc.K c2.pos (.oneOf enc.lits :: c2.neg) := by
        rw [← hval2.2.1]; exact List.getElem_mem hidx2
      have hnot := sampleWiderCell_not_mem_litVals hv hmemWs
      exact (hnot (hvEq ▸ List.getElem_mem hl1)).elim
  · obtain ⟨c1, hc1, h1l, h1h⟩ := hcov n₁ (by omega) h1
    have hpart1 := (hmem c1 hc1).1
    have hval1 := (hmem c1 hc1).2.2.2.2
    rw [slotVal_lt_litVals enc hl2] at heq
    cases hvs1 : c1.values with
    | none => rw [slotVal_in_cell_none hv hc1 hvs1 h1l h1h] at heq; cases heq
    | some ws1 =>
      rw [hvs1] at hval1
      obtain ⟨hidx1, hsv1⟩ := slotVal_in_cell_some hv hc1 hvs1 h1l h1h
      rw [hsv1] at heq
      have hvEq := Sum.inl.inj heq
      have hmemWs : ws1[n₁ - c1.lo] ∈ sampleWiderCell enc.K c1.pos (.oneOf enc.lits :: c1.neg) := by
        rw [← hval1.2.1]; exact List.getElem_mem hidx1
      have hnot := sampleWiderCell_not_mem_litVals hv hmemWs
      exact (hnot (hvEq.symm ▸ List.getElem_mem hl2)).elim
  · obtain ⟨c1, hc1, h1l, h1h⟩ := hcov n₁ (by omega) h1
    obtain ⟨c2, hc2, h2l, h2h⟩ := hcov n₂ (by omega) h2
    have hpart1 := (hmem c1 hc1).1
    have hpart2 := (hmem c2 hc2).1
    have hval1 := (hmem c1 hc1).2.2.2.2
    have hval2 := (hmem c2 hc2).2.2.2.2
    cases hvs1 : c1.values with
    | none =>
      rw [slotVal_in_cell_none hv hc1 hvs1 h1l h1h] at heq
      cases hvs2 : c2.values with
      | none =>
        rw [slotVal_in_cell_none hv hc2 hvs2 h2l h2h] at heq
        exact Int.ofNat.inj (Sum.inr.inj heq)
      | some ws2 =>
        obtain ⟨_, hsv2⟩ := slotVal_in_cell_some hv hc2 hvs2 h2l h2h
        rw [hsv2] at heq; cases heq
    | some ws1 =>
      obtain ⟨hidx1, hsv1⟩ := slotVal_in_cell_some hv hc1 hvs1 h1l h1h
      cases hvs2 : c2.values with
      | none =>
        rw [hsv1, slotVal_in_cell_none hv hc2 hvs2 h2l h2h] at heq; cases heq
      | some ws2 =>
        obtain ⟨hidx2, hsv2⟩ := slotVal_in_cell_some hv hc2 hvs2 h2l h2h
        have hp1 := slotVal_cell_partitionHolds hv i' (standardTarget hv) hc1 h1l h1h
        have hp2 := slotVal_cell_partitionHolds hv i' (standardTarget hv) hc2 h2l h2h
        rw [targetSlot_standard] at hp1 hp2
        rw [heq] at hp1
        have hpeq := vennPartitions_unique hpart1 hpart2 hp1 hp2
        obtain ⟨hpEq, hnEq⟩ := Prod.mk.inj hpeq
        have hcEq : c1 = c2 := by
          have hndParts : (vennPartitions enc.atoms).Nodup := nodup_eraseDups_list _
          have haux : ∀ (off : Nat) (ps : List (List DataRange × List DataRange)),
              ps.Nodup → ∀ a ∈ (buildCellTable enc.K enc.lits off ps).1,
              ∀ b ∈ (buildCellTable enc.K enc.lits off ps).1,
              a.pos = b.pos → a.neg = b.neg → a = b := by
            intro off ps hnd
            induction ps generalizing off with
            | nil => intro a ha; cases ha
            | cons pq rest ih =>
              rcases pq with ⟨pp, nn⟩
              obtain ⟨hnpq, hnd'⟩ := List.nodup_cons.mp hnd
              unfold buildCellTable
              split
              · exact ih off hnd'
              · split
                · intro a ha b hb hap han
                  rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
                  · rfl
                  · have hmb := (buildCellTable_spec enc.K enc.lits (off + enc.K) rest).1 b hb'
                    dsimp only at hap han; rw [hap, han] at hnpq; exact (hnpq hmb.1).elim
                  · have hma := (buildCellTable_spec enc.K enc.lits (off + enc.K) rest).1 a ha'
                    dsimp only at hap han; rw [← hap, ← han] at hnpq; exact (hnpq hma.1).elim
                  · exact ih (off + enc.K) hnd' a ha' b hb' hap han
                · intro a ha b hb hap han
                  let ws := sampleWiderCell enc.K pp (.oneOf enc.lits :: nn)
                  rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
                  · rfl
                  · have hmb := (buildCellTable_spec enc.K enc.lits (off + ws.length) rest).1 b hb'
                    dsimp only at hap han; rw [hap, han] at hnpq; exact (hnpq hmb.1).elim
                  · have hma := (buildCellTable_spec enc.K enc.lits (off + ws.length) rest).1 a ha'
                    dsimp only at hap han; rw [← hap, ← han] at hnpq; exact (hnpq hma.1).elim
                  · exact ih (off + ws.length) hnd' a ha' b hb' hap han
          have := haux enc.litVals.length (vennPartitions enc.atoms) hndParts
          rw [hcellsEq] at this
          exact this c1 hc1 c2 hc2 hpEq hnEq
        subst hcEq
        rw [hvs1] at hvs2; cases hvs2
        rw [hsv1, hsv2] at heq
        have hvEq := Sum.inl.inj heq
        rw [hvs1] at hval1
        have hndWs : ws1.Nodup := hval1.2.1 ▸ sampleWiderCell_nodup ..
        have hi1 := idxOfList_getElem hndWs hidx1
        have hi2 := idxOfList_getElem hndWs hidx2
        have hsubEq : n₁ - c1.lo = n₂ - c1.lo := by rw [← hi1, ← hi2, hvEq]
        omega

private theorem targetSlot_inj {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    (i' : Interpretation datatypeMap) {dm : DatatypeMap} (target : enc.Target dm)
    {a b : Nat} (ha : a < enc.totalSlots) (hb : b < enc.totalSlots)
    (he : targetSlot target a = targetSlot target b) : a = b :=
  slotVal_inj hv i' ha hb (target.translate_inj he)

private theorem dataHolds_encodeDataRange_slot_iff {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (i' : Interpretation datatypeMap)
    {dm : DatatypeMap} (target : enc.Target dm)
    {d : DataRange} (hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms)
    {n : Nat} (hn : n < enc.totalSlots) :
    dataHolds i' (i'.embedValue (.integer (Int.ofNat n))) (enc.encodeDataRange d) ↔
      dataHolds (decodeInterp i' enc target) (targetSlot target n) d := by
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  obtain ⟨hmem, hdisj, hcov, _⟩ := hspec
  rw [WiderEncoding.encodeDataRange, dataHolds_intIntervalsDR_iff]
  have hnEq : ∀ m : Nat, i'.embedValue (.integer (Int.ofNat n)) = i'.embedValue (.integer (Int.ofNat m)) ↔ n = m := by
    intro m
    constructor
    · intro h
      have h1 := congrArg Rat.num (Value.number.inj (i'.embedValue_injective h))
      simp at h1; omega
    · rintro rfl; rfl
  simp only [hnEq, WiderEncoding.encodeIntervals, List.mem_append,
    List.mem_filterMap, List.mem_range]
  by_cases hlt : n < enc.litVals.length
  · rw [targetSlot_lit target hlt]
    change _ ↔ dataHolds (decodeInterp i' enc target)
      ((decodeInterp i' enc target).embedValue (target.value enc.litVals[n])) d
    rw [← evalWiderDataRange_of_atoms _ _ _ d
      (fun a ha => target.evalAtom a (hd a ha) _ (.inl (List.getElem_mem hlt)) _)]
    constructor
    · rintro ⟨iv, ⟨idx, hidx, hfilt⟩ | ⟨cs, hcs, hfilt⟩, m, hlo, hhi, rfl⟩
      · simp only [hidx, ↓reduceDIte] at hfilt
        split at hfilt
        · rename_i hev
          cases hfilt
          have hne : idx = n := by omega
          subst hne; exact hev
        · cases hfilt
      · split at hfilt
        · cases hfilt
          have := (hmem cs hcs).2.1; omega
        · cases hfilt
    · intro hev
      refine ⟨(n, n), .inl ⟨n, hlt, ?_⟩, n, Nat.le_refl _, Nat.le_refl _, rfl⟩
      simp [hlt, hev]
  · obtain ⟨cs, hcs, hlo, hhi⟩ := hcov n (by omega) hn
    have hpart := (hmem cs hcs).1
    have hcellHolds := slotVal_cell_partitionHolds hv i' target hcs hlo hhi
    rw [← evalOnPartition_iff hpart hcellHolds hd]
    constructor
    · rintro ⟨iv, ⟨idx, hidx, hfilt⟩ | ⟨cs', hcs', hfilt⟩, m, hil, hih, rfl⟩
      · simp only [hidx, ↓reduceDIte] at hfilt
        split at hfilt
        · cases hfilt; omega
        · cases hfilt
      · split at hfilt
        · rename_i hcond
          cases hfilt
          obtain ⟨hpos, hev⟩ := Bool.and_eq_true_iff.mp hcond
          have hpos' : 0 < cs'.len := decide_eq_true_eq.mp hpos
          have heq := hdisj cs hcs cs' hcs' n hlo hhi hil (by omega)
          subst heq; exact hev
        · cases hfilt
    · intro hev
      refine ⟨(cs.lo, cs.lo + cs.len - 1), .inr ⟨cs, hcs, ?_⟩, n, hlo, by omega, rfl⟩
      have hpos : 0 < cs.len := by omega
      simp [hpos, hev]

private theorem dataProp_decode_iff {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc) {dm : DatatypeMap} (target : enc.Target dm)
    {i' : Interpretation datatypeMap} (hm' : (enc.encodeProblem p).Models i')
    {dp : IRI} (hdp : dp ∈ p.allDataProps) (x : i'.Object) (z : i'.Data) :
    i'.dataProperties dp x z ↔
      ∃ n : Nat, n < enc.totalSlots ∧ z = i'.embedValue (.integer (Int.ofNat n)) ∧
        (decodeInterp i' enc target).dataProperties dp x (targetSlot target n) := by
  have ⟨hnt, hnb⟩ := hv.hdprops dp hdp
  constructor
  · intro hrel
    have hdomMem : (dp, allSlotsDR enc.totalSlots) ∈ (enc.encodeProblem p).dataRanges :=
      List.mem_append_right _ (List.mem_map_of_mem hdp)
    have hdom := hm'.dataRanges _ hdomMem x z hrel
    obtain ⟨n, hn, rfl⟩ := (dataHolds_allSlotsDR_iff i' z enc.totalSlots).mp hdom
    refine ⟨n, hn, rfl, ?_⟩
    simp only [decodeInterp, hnt, hnb, ↓reduceIte]
    exact ⟨n, hn, rfl, hrel⟩
  · rintro ⟨n, hn, rfl, hrel⟩
    simp only [decodeInterp, hnt, hnb, ↓reduceIte] at hrel
    obtain ⟨n', hn', hsv, hrel'⟩ := hrel
    have heq := targetSlot_inj hv i' target hn hn' hsv
    subst heq; exact hrel'

private theorem w_atLeast_congr {α : Type} {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) (n : Nat) :
    AtLeast n P ↔ AtLeast n Q :=
  ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun x hx => (h x).mp (hp x hx)⟩,
   fun ⟨xs, hl, hn, hq⟩ => ⟨xs, hl, hn, fun x hx => (h x).mpr (hq x hx)⟩⟩

private theorem atLeast_bijection {α β : Type} {P : α → Prop} {Q : β → Prop}
    (f : α → β) (hf : ∀ a, P a → Q (f a))
    (hinj : ∀ a₁ a₂, P a₁ → P a₂ → f a₁ = f a₂ → a₁ = a₂)
    (hsurj : ∀ b, Q b → ∃ a, P a ∧ f a = b) (n : Nat) :
    AtLeast n P ↔ AtLeast n Q := by
  constructor
  · rintro ⟨xs, hlen, hnd, hp⟩
    refine ⟨xs.map f, by simp [hlen], ?_, fun b hb => ?_⟩
    · clear hlen
      induction xs with
      | nil => exact List.nodup_nil
      | cons a rest ih =>
        obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
        refine List.nodup_cons.mpr ⟨?_, ih hnd' fun y hy => hp y (List.mem_cons_of_mem _ hy)⟩
        intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have heq := hinj y a (hp y (List.mem_cons_of_mem _ hy)) (hp a (List.mem_cons_self ..)) hfy
        exact hna (heq ▸ hy)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact hf a (hp a ha)
  · rintro ⟨ys, hlen, hnd, hq⟩
    have haux : ∀ (l : List β), l.Nodup → (∀ b ∈ l, Q b) →
        ∃ xs : List α, xs.length = l.length ∧ xs.Nodup ∧ (∀ a ∈ xs, P a) ∧ xs.map f = l := by
      intro l
      induction l with
      | nil => intro _ _; exact ⟨[], rfl, List.nodup_nil, by simp, rfl⟩
      | cons b rest ih =>
        intro hndl hql
        obtain ⟨hnb, hnd'⟩ := List.nodup_cons.mp hndl
        obtain ⟨a, hpa, hfa⟩ := hsurj b (hql b (List.mem_cons_self ..))
        obtain ⟨xs, hxl, hxnd, hxP, hxmap⟩ := ih hnd' fun y hy => hql y (List.mem_cons_of_mem _ hy)
        refine ⟨a :: xs, by simp [hxl], List.nodup_cons.mpr ⟨?_, hxnd⟩, ?_, by simp [hfa, hxmap]⟩
        · intro ha
          have hbm : b ∈ xs.map f := hfa ▸ List.mem_map_of_mem ha
          rw [hxmap] at hbm; exact hnb hbm
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hr
          · exact hpa
          · exact hxP x hr
    obtain ⟨xs, hxl, hxnd, hxP, _⟩ := haux ys hnd hq
    exact ⟨xs, hxl.trans hlen, hxnd, hxP⟩

private theorem holds_decodeInterp_iff {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {dm : DatatypeMap} (target : enc.Target dm)
    {i' : Interpretation datatypeMap}
    (hm' : (enc.encodeProblem p).Models i')
    {c : Concept}
    (hdpSub : ∀ dp ∈ c.dataPropsOf, dp ∈ p.allDataProps)
    (hlitSub : ∀ l ∈ c.dataLiteralsOf, l ∈ enc.lits)
    (hdrSub : ∀ d ∈ c.dataRangesOf, ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms)
    (x : i'.Object) :
    holds i' x (enc.encodeConcept c) ↔ holds (decodeInterp i' enc target) x c := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b => cases b <;> rfl
  | nom _ b => cases b <;> rfl
  | self r b => rcases r with ⟨_, _ | _⟩ <;> cases b <;> rfl
  | conj a b iha ihb =>
    exact and_congr
      (iha (fun dp h => hdpSub dp (List.mem_append_left _ h))
           (fun l h => hlitSub l (List.mem_append_left _ h))
           (fun d h => hdrSub d (List.mem_append_left _ h)) x)
      (ihb (fun dp h => hdpSub dp (List.mem_append_right _ h))
           (fun l h => hlitSub l (List.mem_append_right _ h))
           (fun d h => hdrSub d (List.mem_append_right _ h)) x)
  | disj a b iha ihb =>
    exact or_congr
      (iha (fun dp h => hdpSub dp (List.mem_append_left _ h))
           (fun l h => hlitSub l (List.mem_append_left _ h))
           (fun d h => hdrSub d (List.mem_append_left _ h)) x)
      (ihb (fun dp h => hdpSub dp (List.mem_append_right _ h))
           (fun l h => hlitSub l (List.mem_append_right _ h))
           (fun d h => hdrSub d (List.mem_append_right _ h)) x)
  | some r c ih =>
    exact exists_congr fun y => and_congr Iff.rfl (ih hdpSub hlitSub hdrSub y)
  | all r c ih =>
    exact forall_congr' fun y => imp_congr Iff.rfl (ih hdpSub hlitSub hdrSub y)
  | min n r c ih =>
    exact w_atLeast_congr (fun y => and_congr Iff.rfl (ih hdpSub hlitSub hdrSub y)) n
  | max n r c ih =>
    exact not_congr (w_atLeast_congr (fun y => and_congr Iff.rfl (ih hdpSub hlitSub hdrSub y)) (n + 1))
  | dataSome dp d =>
    have hdp : dp ∈ p.allDataProps := hdpSub dp (List.mem_singleton_self _)
    have hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms := hdrSub d (List.mem_singleton_self _)
    have ⟨hnt, hnb⟩ := hv.hdprops dp hdp
    simp only [WiderEncoding.encodeConcept, holds]
    constructor
    · rintro ⟨z, hz, hdz⟩
      obtain ⟨n, hn, rfl, hrel⟩ := (dataProp_decode_iff hv target hm' hdp x z).mp hz
      exact ⟨targetSlot target n, hrel, (dataHolds_encodeDataRange_slot_iff hv i' target hd hn).mp hdz⟩
    · rintro ⟨y, hy, hdy⟩
      simp only [decodeInterp, hnt, hnb, ↓reduceIte] at hy
      obtain ⟨n, hn, rfl, hrel⟩ := hy
      exact ⟨i'.embedValue (.integer (Int.ofNat n)), hrel,
        (dataHolds_encodeDataRange_slot_iff hv i' target hd hn).mpr hdy⟩
  | dataAll dp d =>
    have hdp : dp ∈ p.allDataProps := hdpSub dp (List.mem_singleton_self _)
    have hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms := hdrSub d (List.mem_singleton_self _)
    have ⟨hnt, hnb⟩ := hv.hdprops dp hdp
    simp only [WiderEncoding.encodeConcept, holds]
    constructor
    · intro hall y hy
      simp only [decodeInterp, hnt, hnb, ↓reduceIte] at hy
      obtain ⟨n, hn, rfl, hrel⟩ := hy
      exact (dataHolds_encodeDataRange_slot_iff hv i' target hd hn).mp (hall _ hrel)
    · intro hall z hz
      obtain ⟨n, hn, rfl, hrel⟩ := (dataProp_decode_iff hv target hm' hdp x z).mp hz
      exact (dataHolds_encodeDataRange_slot_iff hv i' target hd hn).mpr (hall _ hrel)
  | dataValue dp l b =>
    have hdp : dp ∈ p.allDataProps := hdpSub dp (List.mem_singleton_self _)
    have hl : l ∈ enc.lits := hlitSub l (List.mem_singleton_self _)
    obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv hl
    have hidxLt : idxOfList enc.litVals v < enc.litVals.length := idxOfList_lt hvMem
    have htotGe : enc.litVals.length ≤ enc.totalSlots := by
      have := buildCellTable_total_ge enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
      rw [congrArg Prod.snd hv.htable.symm] at this; exact this
    have hidxTot : idxOfList enc.litVals v < enc.totalSlots := by omega
    have hlit' : i'.literalValue (enc.encodeLiteral l) =
        i'.embedValue (.integer (Int.ofNat (idxOfList enc.litVals v))) := by
      simp only [WiderEncoding.encodeLiteral, hdl]
      exact i'.lexicalAgreement _ _ (decodeLiteral_natLit _)
    have hlitOrig : (decodeInterp i' enc target).literalValue l = targetSlot target (idxOfList enc.litVals v) := by
      simp only [decodeInterp, target.lexical _ _ hdl, Option.elim_some, targetSlot_lit target hidxLt, getElem_idxOfList hvMem]
    have hiff : i'.dataProperties dp x (i'.literalValue (enc.encodeLiteral l)) ↔
        (decodeInterp i' enc target).dataProperties dp x ((decodeInterp i' enc target).literalValue l) := by
      rw [hlit', hlitOrig]
      constructor
      · intro hrel
        obtain ⟨n, hn, heq, hdec⟩ := (dataProp_decode_iff hv target hm' hdp x _).mp hrel
        have hne : idxOfList enc.litVals v = n := by
          have := congrArg Rat.num (Value.number.inj (i'.embedValue_injective heq))
          simp at this; omega
        subst hne; exact hdec
      · intro hdec
        exact (dataProp_decode_iff hv target hm' hdp x _).mpr ⟨_, hidxTot, rfl, hdec⟩
    cases b <;> simp only [WiderEncoding.encodeConcept, holds, hiff]
  | dataMin n dp d =>
    have hdp : dp ∈ p.allDataProps := hdpSub dp (List.mem_singleton_self _)
    have hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms := hdrSub d (List.mem_singleton_self _)
    have ⟨hnt, hnb⟩ := hv.hdprops dp hdp
    simp only [WiderEncoding.encodeConcept, holds]
    refine (atLeast_bijection (f := fun (m : Nat) => i'.embedValue (.integer (Int.ofNat m)))
      (P := fun m => m < enc.totalSlots ∧ i'.dataProperties dp x (i'.embedValue (.integer (Int.ofNat m))) ∧
        dataHolds i' (i'.embedValue (.integer (Int.ofNat m))) (enc.encodeDataRange d))
      (fun _ h => ⟨h.2.1, h.2.2⟩)
      (fun m₁ m₂ _ _ heq => by
        have := congrArg Rat.num (Value.number.inj (i'.embedValue_injective heq))
        simp at this; omega)
      (fun z ⟨hz, hdz⟩ => by
        obtain ⟨m, hm, rfl, _⟩ := (dataProp_decode_iff hv target hm' hdp x z).mp hz
        exact ⟨m, ⟨hm, hz, hdz⟩, rfl⟩) n).symm.trans ?_
    refine atLeast_bijection (f := targetSlot target)
      (fun m ⟨hm, hrel, hdz⟩ =>
        ⟨(dataProp_decode_iff hv target hm' hdp x _).mp hrel |>.choose_spec.2.2 |> fun _ => by
          simp only [decodeInterp, hnt, hnb, ↓reduceIte]; exact ⟨m, hm, rfl, hrel⟩,
         (dataHolds_encodeDataRange_slot_iff hv i' target hd hm).mp hdz⟩)
      (fun m₁ m₂ h1 h2 heq => targetSlot_inj hv i' target h1.1 h2.1 heq)
      (fun y ⟨hy, hdy⟩ => by
        simp only [decodeInterp, hnt, hnb, ↓reduceIte] at hy
        obtain ⟨m, hm, rfl, hrel⟩ := hy
        exact ⟨m, ⟨hm, hrel, (dataHolds_encodeDataRange_slot_iff hv i' target hd hm).mpr hdy⟩, rfl⟩) n
  | dataMax n dp d =>
    have hdp : dp ∈ p.allDataProps := hdpSub dp (List.mem_singleton_self _)
    have hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms := hdrSub d (List.mem_singleton_self _)
    have ⟨hnt, hnb⟩ := hv.hdprops dp hdp
    simp only [WiderEncoding.encodeConcept, holds]
    apply not_congr
    refine (atLeast_bijection (f := fun (m : Nat) => i'.embedValue (.integer (Int.ofNat m)))
      (P := fun m => m < enc.totalSlots ∧ i'.dataProperties dp x (i'.embedValue (.integer (Int.ofNat m))) ∧
        dataHolds i' (i'.embedValue (.integer (Int.ofNat m))) (enc.encodeDataRange d))
      (fun _ h => ⟨h.2.1, h.2.2⟩)
      (fun m₁ m₂ _ _ heq => by
        have := congrArg Rat.num (Value.number.inj (i'.embedValue_injective heq))
        simp at this; omega)
      (fun z ⟨hz, hdz⟩ => by
        obtain ⟨m, hm, rfl, _⟩ := (dataProp_decode_iff hv target hm' hdp x z).mp hz
        exact ⟨m, ⟨hm, hz, hdz⟩, rfl⟩) (n + 1)).symm.trans ?_
    refine atLeast_bijection (f := targetSlot target)
      (fun m ⟨hm, hrel, hdz⟩ =>
        ⟨by simp only [decodeInterp, hnt, hnb, ↓reduceIte]; exact ⟨m, hm, rfl, hrel⟩,
         (dataHolds_encodeDataRange_slot_iff hv i' target hd hm).mp hdz⟩)
      (fun m₁ m₂ h1 h2 heq => targetSlot_inj hv i' target h1.1 h2.1 heq)
      (fun y ⟨hy, hdy⟩ => by
        simp only [decodeInterp, hnt, hnb, ↓reduceIte] at hy
        obtain ⟨m, hm, rfl, hrel⟩ := hy
        exact ⟨m, ⟨hm, hrel, (dataHolds_encodeDataRange_slot_iff hv i' target hd hm).mpr hdy⟩, rfl⟩) (n + 1)

private theorem mem_allConcepts_subs {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    {c : Concept} (hc : c ∈ p.allConcepts) :
    (∀ dp ∈ c.dataPropsOf, dp ∈ p.allDataProps) ∧
    (∀ l ∈ c.dataLiteralsOf, l ∈ enc.lits) ∧
    (∀ d ∈ c.dataRangesOf, ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) := by
  refine ⟨fun dp hdp => ?_, fun l hl => ?_, fun d hd a ha => ?_⟩
  · simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    left; left; left; left; left; left; left; exact ⟨c, hc, hdp⟩
  · rw [hv.hlits]
    simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    left; left; exact ⟨c, hc, hl⟩
  · rw [hv.hatoms]
    simp only [Problem.allDataAtoms, Problem.allDataRanges, List.mem_eraseDups, List.mem_flatMap,
      List.mem_append]
    exact ⟨d, .inl ⟨c, hc, hd⟩, ha⟩

private theorem objPath_eq_of_objProps {dm₁ dm₂ : DatatypeMap}
    {i₁ : Interpretation dm₁} {i₂ : Interpretation dm₂}
    (hObj : i₁.Object = i₂.Object)
    (hProp : ∀ r x y, i₁.objectProperties r x y ↔ i₂.objectProperties r (hObj ▸ x) (hObj ▸ y))
    (rs : List Sabrina.ALC.OrientedRole) (x y : i₁.Object) :
    objPath i₁ rs x y ↔ objPath i₂ rs (hObj ▸ x) (hObj ▸ y) := by
  cases i₁; cases i₂; dsimp only at hObj
  subst hObj
  induction rs generalizing x with
  | nil => rfl
  | cons r rest ih =>
    refine exists_congr fun z => and_congr ?_ (ih z)
    rcases r with ⟨rn, _ | _⟩ <;> exact hProp rn _ _

private theorem encodeWiderData_sat_with_target {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {dm : DatatypeMap} (target : enc.Target dm)
    (hsat' : (enc.encodeProblem p).Sat) : p.SatWith dm := by
  obtain ⟨i', hm', x₀, hx₀⟩ := hsat'
  let i := decodeInterp i' enc target
  have hconc (c : Concept) (hc : c ∈ p.allConcepts) (x : i'.Object) :
      holds i' x (enc.encodeConcept c) ↔ holds i x c := by
    have ⟨h1, h2, h3⟩ := mem_allConcepts_subs hv hc
    exact holds_decodeInterp_iff hv target hm' h1 h2 h3 x
  have htotGe : enc.litVals.length ≤ enc.totalSlots := by
    have := buildCellTable_total_ge enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
    rw [congrArg Prod.snd hv.htable.symm] at this; exact this
  refine ⟨i, ?_, x₀, (hconc p.root (List.mem_cons_self ..) x₀).mp hx₀⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq x hx
    have hsubC : q.sub ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; left; left; exact ⟨q, hq, by simp⟩
    have hsupC : q.sup ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; left; left; exact ⟨q, hq, by simp⟩
    exact (hconc q.sup hsupC x).mp (hm'.tbox _ (List.mem_map_of_mem hq) x ((hconc q.sub hsubC x).mpr hx))
  · exact hm'.rules
  · intro c hc x y hp
    exact hm'.chains c hc x y ((objPath_eq_of_objProps (i₁ := i) (i₂ := i') rfl (fun _ _ _ => Iff.rfl) c.body x y).mp hp)
  · exact hm'.reflexive
  · exact hm'.irreflexive
  · exact hm'.asymmetric
  · exact hm'.disjoint
  · intro rs hrs x y hy
    have hr1 : rs.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have hr2 : rs.2 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have ⟨ht1, hb1⟩ := hv.hdprops rs.1 hr1
    have ⟨ht2, hb2⟩ := hv.hdprops rs.2 hr2
    simp only [i, decodeInterp, ht1, hb1, ht2, hb2, ↓reduceIte] at hy ⊢
    obtain ⟨n, hn, rfl, hrel⟩ := hy
    exact ⟨n, hn, rfl, hm'.subData rs hrs x _ hrel⟩
  · intro rs hrs x y ⟨h1, h2⟩
    have hr1 : rs.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have hr2 : rs.2 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have ⟨ht1, hb1⟩ := hv.hdprops rs.1 hr1
    have ⟨ht2, hb2⟩ := hv.hdprops rs.2 hr2
    simp only [i, decodeInterp, ht1, hb1, ht2, hb2, ↓reduceIte] at h1 h2
    obtain ⟨n1, hn1, rfl, hr1'⟩ := h1
    obtain ⟨n2, hn2, heq, hr2'⟩ := h2
    have hne := targetSlot_inj hv i' target hn1 hn2 heq
    subst hne
    exact hm'.disjointData rs hrs x _ ⟨hr1', hr2'⟩
  · intro r hr x y z hy hz
    have hdp : r ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append]
      left; left; left; right; exact hr
    have ⟨ht, hb⟩ := hv.hdprops r hdp
    simp only [i, decodeInterp, ht, hb, ↓reduceIte] at hy hz
    obtain ⟨n1, _, rfl, hr1⟩ := hy
    obtain ⟨n2, _, rfl, hr2⟩ := hz
    have heq := hm'.funcData r hr x _ _ hr1 hr2
    have hne : n1 = n2 := by
      have := congrArg Rat.num (Value.number.inj (i'.embedValue_injective heq))
      simp at this; omega
    subst hne; rfl
  · intro rd hrd x y hy
    have hdp : rd.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; left; left; left; left; left; right; exact ⟨rd, hrd, rfl⟩
    have hd : ∀ a ∈ atomsOfDataRange rd.2, a ∈ enc.atoms := fun a ha => by
      rw [hv.hatoms]
      simp only [Problem.allDataAtoms, Problem.allDataRanges, List.mem_eraseDups, List.mem_flatMap,
        List.mem_append, List.mem_map]
      exact ⟨rd.2, .inr ⟨rd, hrd, rfl⟩, ha⟩
    have ⟨ht, hb⟩ := hv.hdprops rd.1 hdp
    simp only [i, decodeInterp, ht, hb, ↓reduceIte] at hy
    obtain ⟨n, hn, rfl, hrel⟩ := hy
    have hdrMem : (rd.1, enc.encodeDataRange rd.2) ∈ (enc.encodeProblem p).dataRanges :=
      List.mem_append_left _ (List.mem_map_of_mem hrd)
    exact (dataHolds_encodeDataRange_slot_iff hv i' target hd hn).mp (hm'.dataRanges _ hdrMem x _ hrel)
  · intro k hk x y hx hy hnx hny ho hd
    have hclsC : k.cls ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]
      right; left; right; exact ⟨k, hk, rfl⟩
    refine hm'.keys _ (List.mem_map_of_mem hk) x y ((hconc k.cls hclsC x).mpr hx)
      ((hconc k.cls hclsC y).mpr hy) hnx hny ho fun dp hdp => ?_
    have hdpAll : dp ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; right; exact ⟨k, hk, hdp⟩
    have ⟨ht, hb⟩ := hv.hdprops dp hdpAll
    obtain ⟨z, hzx, hzy⟩ := hd dp hdp
    simp only [i, decodeInterp, ht, hb, ↓reduceIte] at hzx hzy
    obtain ⟨n1, hn1, rfl, hr1⟩ := hzx
    obtain ⟨n2, hn2, heq, hr2⟩ := hzy
    have hne := targetSlot_inj hv i' target hn1 hn2 heq
    subst hne
    exact ⟨i'.embedValue (.integer (Int.ofNat n1)), hr1, hr2⟩
  · intro ac hac
    have hcaC : ac.2 ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]
      right; right; exact ⟨ac, hac, rfl⟩
    exact (hconc ac.2 hcaC _).mp (hm'.classAssertions _ (List.mem_map_of_mem hac))
  · exact hm'.objAssertions
  · exact hm'.negObjAssertions
  · exact hm'.sameInds
  · exact hm'.diffInds
  · intro ral hral
    have hdp : ral.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; right; exact ⟨ral, hral, rfl⟩
    have hl : ral.2.2 ∈ enc.lits := by
      rw [hv.hlits]
      simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; right; exact ⟨ral, hral, rfl⟩
    have ⟨ht, hb⟩ := hv.hdprops ral.1 hdp
    obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv hl
    have hidxLt := idxOfList_lt hvMem
    have hda' := hm'.dataAssertions _ (List.mem_map_of_mem hral)
    have hlit' : i'.literalValue (enc.encodeLiteral ral.2.2) =
        i'.embedValue (.integer (Int.ofNat (idxOfList enc.litVals v))) := by
      simp only [WiderEncoding.encodeLiteral, hdl]
      exact i'.lexicalAgreement _ _ (decodeLiteral_natLit _)
    rw [hlit'] at hda'
    simp only [i, decodeInterp, ht, hb, ↓reduceIte, target.lexical _ _ hdl, Option.elim_some]
    refine ⟨idxOfList enc.litVals v, by omega, ?_, hda'⟩
    rw [targetSlot_lit target hidxLt, getElem_idxOfList hvMem]
  · intro ral hral hda
    have hdp : ral.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
      right; exact ⟨ral, hral, rfl⟩
    have hl : ral.2.2 ∈ enc.lits := by
      rw [hv.hlits]
      simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_map]
      right; exact ⟨ral, hral, rfl⟩
    have ⟨ht, hb⟩ := hv.hdprops ral.1 hdp
    obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv hl
    have hidxLt := idxOfList_lt hvMem
    simp only [i, decodeInterp, ht, hb, ↓reduceIte, target.lexical _ _ hdl, Option.elim_some] at hda
    obtain ⟨n, hn, hsv, hrel⟩ := hda
    have hne : idxOfList enc.litVals v = n :=
      targetSlot_inj hv i' target (by omega) hn (by rw [targetSlot_lit target hidxLt, getElem_idxOfList hvMem]; exact hsv)
    subst hne
    have hnda' := hm'.negDataAssertions _ (List.mem_map_of_mem hral)
    have hlit' : i'.literalValue (enc.encodeLiteral ral.2.2) =
        i'.embedValue (.integer (Int.ofNat (idxOfList enc.litVals v))) := by
      simp only [WiderEncoding.encodeLiteral, hdl]
      exact i'.lexicalAgreement _ _ (decodeLiteral_natLit _)
    rw [hlit'] at hnda'
    exact hnda' hrel

private theorem encodeWiderData_sat_mp {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (hsat : (enc.encodeProblem p).Sat) : p.Sat :=
  encodeWiderData_sat_with_target hv (standardTarget hv) hsat

theorem WiderEncoding.decode_with_target {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) {dm : DatatypeMap} (target : enc.Target dm)
    (hsat : (enc.encodeProblem p).Sat) : p.SatWith dm :=
  encodeWiderData_sat_with_target (buildWiderEncoding_valid h) target hsat

/-! ### 5. Forward direction (`p.Sat → p'.Sat`) via finite witness extraction -/

private noncomputable def collectWitnesses {dm : DatatypeMap} (i : Interpretation dm) (x : i.Object) :
    Concept → List i.Data
  | .conj a b | .disj a b => collectWitnesses i x a ++ collectWitnesses i x b
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => collectWitnesses i x c
  | .dataSome dp d =>
    letI := Classical.propDecidable
    if h : ∃ y, i.dataProperties dp x y ∧ dataHolds i y d then [Classical.choose h] else []
  | .dataAll dp d =>
    letI := Classical.propDecidable
    if h : ∃ y, i.dataProperties dp x y ∧ ¬ dataHolds i y d then [Classical.choose h] else []
  | .dataMin n dp d =>
    letI := Classical.propDecidable
    if h : AtLeast n (fun y => i.dataProperties dp x y ∧ dataHolds i y d) then Classical.choose h else []
  | .dataMax n dp d =>
    letI := Classical.propDecidable
    if h : AtLeast (n + 1) (fun y => i.dataProperties dp x y ∧ dataHolds i y d) then Classical.choose h else []
  | _ => []

private theorem collectWitnesses_length_le {dm : DatatypeMap} (i : Interpretation dm) (x : i.Object) (c : Concept) :
    (collectWitnesses i x c).length ≤ c.dataDemand := by
  induction c with
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [collectWitnesses, Concept.dataDemand, List.length_append]; omega
  | some _ c ih | all _ c ih | min _ _ c ih | max _ _ c ih =>
    simpa [collectWitnesses, Concept.dataDemand] using ih
  | dataSome dp d =>
    simp only [collectWitnesses, Concept.dataDemand]
    split <;> simp
  | dataAll dp d =>
    simp only [collectWitnesses, Concept.dataDemand]
    split <;> simp
  | dataMin n dp d =>
    simp only [collectWitnesses, Concept.dataDemand]
    split
    · rename_i h; exact Nat.le_of_eq (Classical.choose_spec h).1
    · exact Nat.zero_le _
  | dataMax n dp d =>
    simp only [collectWitnesses, Concept.dataDemand]
    split
    · rename_i h; exact Nat.le_of_eq (Classical.choose_spec h).1
    · exact Nat.zero_le _
  | _ => simp [collectWitnesses, Concept.dataDemand]

private noncomputable def rawWitnesses {dm : DatatypeMap} (i : Interpretation dm) (p : Problem) (x : i.Object) :
    List i.Data :=
  p.allConcepts.flatMap (collectWitnesses i x)

private theorem rawWitnesses_length_le {dm : DatatypeMap} (i : Interpretation dm) (p : Problem) (x : i.Object) :
    (rawWitnesses i p x).length ≤ p.localDataDemand := by
  unfold rawWitnesses Problem.localDataDemand
  have aux : ∀ cs : List Concept,
      (cs.flatMap (collectWitnesses i x)).length ≤ (cs.map Concept.dataDemand).sum := by
    intro cs
    induction cs with
    | nil => simp
    | cons c rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      have := collectWitnesses_length_le i x c
      omega
  exact aux p.allConcepts

private theorem mem_collectWitnesses_sub_rawWitnesses {dm : DatatypeMap} (i : Interpretation dm) (p : Problem)
    (x : i.Object) {c : Concept} (hc : c ∈ p.allConcepts) :
    ∀ y ∈ collectWitnesses i x c, y ∈ rawWitnesses i p x := fun _ hy =>
  List.mem_flatMap.mpr ⟨c, hc, hy⟩

private theorem length_eraseDups_le {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.length ≤ xs.length := by
  classical
  have hnd : xs.eraseDups.Nodup := nodup_eraseDups_list xs
  have hsub : ∀ a ∈ xs.eraseDups, a ∈ xs := fun a ha => List.mem_eraseDups.mp ha
  have aux : ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ a ∈ l₁, a ∈ l₂) → l₁.length ≤ l₂.length := by
    intro l₁
    induction l₁ with
    | nil => intro _ _ _; exact Nat.zero_le _
    | cons a rest ih =>
      intro l₂ hnd' hsub'
      obtain ⟨hna, hndR⟩ := List.nodup_cons.mp hnd'
      have ha : a ∈ l₂ := hsub' a (List.mem_cons_self ..)
      have hle := ih (l₂.erase a) hndR fun x hx =>
        (List.mem_erase_of_ne fun he => hna (by rw [← he]; exact hx)).mpr (hsub' x (List.mem_cons_of_mem _ hx))
      have her : (l₂.erase a).length + 1 = l₂.length := by
        have := List.length_erase_of_mem ha
        have hpos : 0 < l₂.length := List.length_pos_of_mem ha
        omega
      simp only [List.length_cons]; omega
  exact aux xs.eraseDups xs hnd hsub

private theorem length_flatMap_le_mul {α β : Type} (xs : List α) (f : α → List β) (B : Nat)
    (hf : ∀ a ∈ xs, (f a).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := hf a (List.mem_cons_self ..)
    have h2 := ih fun x hx => hf x (List.mem_cons_of_mem _ hx)
    omega

/-- The observations needed to encode a model's data links. Large cells use
local slots and one shared slot map for the named individuals participating
in data keys. Small cells must account for every value individually. -/
structure WiderEncoding.Source (enc : WiderEncoding) {dm : DatatypeMap}
    (i : Interpretation dm) where
  value : Value → i.Data
  injective : ∀ {v w}, value v = value w → v = w
  literal : ∀ l ∈ enc.lits, ∀ v, decodeLiteral l = some v → i.literalValue l = value v
  evalLiteral : ∀ v ∈ enc.litVals, ∀ r : DataRange,
    (∀ a ∈ atomsOfDataRange r, a ∈ enc.atoms) →
    (evalWiderDataRange r v = true ↔ dataHolds i (value v) r)
  coverSmall : ∀ {pos neg : List DataRange},
    widerAtomsAdmissible (pos ++ neg) = true →
    (sampleWiderCell enc.K pos neg).length < enc.K →
    (∃ a ∈ pos, a ≠ .datatype literalDatatype) →
    ∀ y, dataHolds i y (partitionRange pos neg) →
    ∃ v ∈ sampleWiderCell enc.K pos neg, value v = y

/-- Given any finite list `raw : List i.Data` of length `≤ enc.K`, construct a
slot assignment `φ : i.Data → Nat` into `[0, enc.totalSlots - 1]` that:
1. Maps every literal value `i.embedValue v` (`v ∈ enc.litVals`) to `idxOfList enc.litVals v`;
2. Preserves all data ranges over `enc.atoms` on `raw ∪ (enc.litVals.map i.embedValue)`;
3. Is injective on `raw ∪ (enc.litVals.map i.embedValue)`. -/
private noncomputable def buildSlotMap {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {dm : DatatypeMap} (i : Interpretation dm)
    (source : enc.Source i) (raw : List i.Data) (hrawLen : raw.length ≤ enc.K) :
    { φ : i.Data → Nat //
      (∀ y ∈ raw ++ enc.litVals.map source.value, φ y < enc.totalSlots) ∧
      (∀ v ∈ enc.litVals, φ (source.value v) = idxOfList enc.litVals v) ∧
      (∀ y₁ ∈ raw ++ enc.litVals.map source.value, ∀ y₂ ∈ raw ++ enc.litVals.map source.value,
        φ y₁ = φ y₂ → y₁ = y₂) ∧
      (∀ y ∈ raw ++ enc.litVals.map source.value, ∀ d : DataRange,
        (∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) →
        (dataHolds i y d ↔
          ∃ iv ∈ enc.encodeIntervals d, iv.1 ≤ φ y ∧ φ y ≤ iv.2)) } := by
  classical
  letI : DecidableEq i.Data := fun a b => Classical.propDecidable (a = b)
  let rawDups := raw.eraseDups
  have hrawDupsNd : rawDups.Nodup := nodup_eraseDups_list raw
  have hrawDupsLen : rawDups.length ≤ enc.K := Nat.le_trans (length_eraseDups_le raw) hrawLen
  have hspec := buildCellTable_spec enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
  have hcellsEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).1 = enc.cells :=
    congrArg Prod.fst hv.htable.symm
  have htotEq : (buildCellTable enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)).2 = enc.totalSlots :=
    congrArg Prod.snd hv.htable.symm
  rw [hcellsEq, htotEq] at hspec
  obtain ⟨hmem, hdisj, _, hhas⟩ := hspec
  have htotGe : enc.litVals.length ≤ enc.totalSlots := by
    have := buildCellTable_total_ge enc.K enc.lits enc.litVals.length (vennPartitions enc.atoms)
    rw [congrArg Prod.snd hv.htable.symm] at this; exact this
  -- For any y not in litVals, find its unique cell cs in enc.cells.
  have hcellOf (y : i.Data) :
      ∃ cs ∈ enc.cells, dataHolds i y (partitionRange cs.pos cs.neg) := by
    obtain ⟨⟨pos, neg⟩, hpart, hholds⟩ := exists_vennPartition i y enc.atoms
    have hnlit : neg.contains (.datatype literalDatatype) = false := by
      cases h : neg.contains (.datatype literalDatatype)
      · rfl
      · have hml := List.contains_iff_mem.mp h
        have := ((dataHolds_partitionRange_iff i y pos neg).mp hholds).2 _ hml
        exact (this (i.literalDatatypeExt y)).elim
    obtain ⟨cs, hcs, rfl, rfl⟩ := hhas pos neg hpart hnlit
    exact ⟨cs, hcs, hholds⟩
  let cellOf (y : i.Data) : CellSpec := Classical.choose (hcellOf y)
  have cellOf_mem (y : i.Data) : cellOf y ∈ enc.cells := (Classical.choose_spec (hcellOf y)).1
  have cellOf_holds (y : i.Data) : dataHolds i y (partitionRange (cellOf y).pos (cellOf y).neg) :=
    (Classical.choose_spec (hcellOf y)).2
  let φ (y : i.Data) : Nat :=
    if hlit : ∃ v ∈ enc.litVals, source.value v = y then
      idxOfList enc.litVals (Classical.choose hlit)
    else
      let cs := cellOf y
      match cs.values with
      | none => cs.lo + idxOfList rawDups y
      | some ws =>
        if ws.length < enc.K then
          if hws : ∃ v ∈ ws, source.value v = y then
            cs.lo + idxOfList ws (Classical.choose hws)
          else cs.lo
        else cs.lo + idxOfList rawDups y
  have hφ_lit : ∀ v ∈ enc.litVals, φ (source.value v) = idxOfList enc.litVals v := by
    intro v hvMem
    have hex : ∃ w ∈ enc.litVals, source.value w = source.value v := ⟨v, hvMem, rfl⟩
    simp only [φ, hex, ↓reduceDIte]
    have hspec' := Classical.choose_spec hex
    have hwe : Classical.choose hex = v := source.injective hspec'.2
    rw [hwe]
  -- Helper: when y ∉ litVals and cs.values = some ws with ws.length < K, y is in ws!
  have hfinite_ws (y : i.Data) (hnotLit : ¬ ∃ v ∈ enc.litVals, source.value v = y)
      {ws : List Value} (hvs : (cellOf y).values = some ws) (hlt : ws.length < enc.K) :
      ∃ v ∈ ws, source.value v = y := by
    have hcs := cellOf_mem y
    have hcsSpec := hmem (cellOf y) hcs
    have hpart := hcsSpec.1
    have hvalS := hcsSpec.2.2.2.2
    rw [hvs] at hvalS
    obtain ⟨hposNotLit, hwsEq, _⟩ := hvalS
    have ha₀ : ∃ a₀ ∈ (cellOf y).pos, a₀ ≠ .datatype literalDatatype := by
      have hne : ¬ (cellOf y).pos.all (· == .datatype literalDatatype) = true := by
        rw [hposNotLit]; decide
      exact Classical.byContradiction fun hall => hne (List.all_eq_true.mpr fun a ha =>
        Classical.byContradiction fun hnea => hall ⟨a, ha, fun h => hnea (beq_iff_eq.mpr h)⟩)
    have hadmP := widerAtomsAdmissible_partition hv.hadm hpart
    have hnotOneOf : ¬ dataHolds i y (.oneOf enc.lits) := by
      rintro ⟨l, hl, he⟩
      obtain ⟨v, hv, hdl⟩ := decodeLiteral_mem_litVals hv hl
      exact hnotLit ⟨v, hv, (source.literal l hl v hdl).symm.trans he⟩
    have hholds' : dataHolds i y (partitionRange (cellOf y).pos (.oneOf enc.lits :: (cellOf y).neg)) := by
      have h0 := (dataHolds_partitionRange_iff i y (cellOf y).pos (cellOf y).neg).mp (cellOf_holds y)
      rw [dataHolds_partitionRange_iff]
      refine ⟨h0.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | hr
      · exact hnotOneOf
      · exact h0.2 a hr
    rw [hwsEq] at hlt ⊢
    exact source.coverSmall hadmP hlt ha₀ y hholds'
  -- Helper: when y ∈ raw and y ∉ litVals, φ y is in [cs.lo, cs.lo + cs.len - 1]
  have hφ_in_cell (y : i.Data) (hyRaw : y ∈ raw)
      (hnotLit : ¬ ∃ v ∈ enc.litVals, source.value v = y) :
      (cellOf y).lo ≤ φ y ∧ φ y < (cellOf y).lo + (cellOf y).len := by
    have hcs := cellOf_mem y
    have hvalS := (hmem (cellOf y) hcs).2.2.2.2
    have hyDups : y ∈ rawDups := List.mem_eraseDups.mpr hyRaw
    have hidxRaw : idxOfList rawDups y < enc.K := Nat.lt_of_lt_of_le (idxOfList_lt hyDups) hrawDupsLen
    simp only [φ, hnotLit, ↓reduceDIte]
    cases hvs : (cellOf y).values with
    | none =>
      rw [hvs] at hvalS
      dsimp only; rw [hvalS.2]; omega
    | some ws =>
      rw [hvs] at hvalS
      by_cases hlt : ws.length < enc.K
      · have hws := hfinite_ws y hnotLit hvs hlt
        simp only [hlt, ↓reduceIte, hws, ↓reduceDIte]
        have hidxW := idxOfList_lt (Classical.choose_spec hws).1
        rw [hvalS.2.2]; omega
      · simp only [hlt, ↓reduceIte]
        have hleK : ws.length ≤ enc.K := hvalS.2.1 ▸ sampleWiderCell_length_le ..
        rw [hvalS.2.2]; omega
  refine ⟨φ, ?_, hφ_lit, ?_, ?_⟩
  · -- Bound < enc.totalSlots
    intro y hy
    by_cases hlit : ∃ v ∈ enc.litVals, source.value v = y
    · obtain ⟨v, hvMem, rfl⟩ := hlit
      rw [hφ_lit v hvMem]
      exact Nat.lt_of_lt_of_le (idxOfList_lt hvMem) htotGe
    · have hyRaw : y ∈ raw := by
        rcases List.mem_append.mp hy with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2
          exact (hlit ⟨v, hvMem, rfl⟩).elim
      have ⟨_, hhi⟩ := hφ_in_cell y hyRaw hlit
      have htot := (hmem (cellOf y) (cellOf_mem y)).2.2.1
      omega
  · -- Injectivity on raw ++ enc.litVals.map source.value
    intro y₁ hy₁ y₂ hy₂ heq
    by_cases hl1 : ∃ v ∈ enc.litVals, source.value v = y₁ <;>
    by_cases hl2 : ∃ v ∈ enc.litVals, source.value v = y₂
    · obtain ⟨v1, hv1, rfl⟩ := hl1
      obtain ⟨v2, hv2, rfl⟩ := hl2
      rw [hφ_lit v1 hv1, hφ_lit v2 hv2] at heq
      rw [idxOfList_inj hv1 hv2 heq]
    · obtain ⟨v1, hv1, rfl⟩ := hl1
      have hy2Raw : y₂ ∈ raw := by
        rcases List.mem_append.mp hy₂ with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2; exact (hl2 ⟨v, hvMem, rfl⟩).elim
      have h1lt := idxOfList_lt hv1
      have h2lo := (hφ_in_cell y₂ hy2Raw hl2).1
      have hcsLo := (hmem (cellOf y₂) (cellOf_mem y₂)).2.1
      rw [hφ_lit v1 hv1] at heq; omega
    · obtain ⟨v2, hv2, rfl⟩ := hl2
      have hy1Raw : y₁ ∈ raw := by
        rcases List.mem_append.mp hy₁ with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2; exact (hl1 ⟨v, hvMem, rfl⟩).elim
      have h2lt := idxOfList_lt hv2
      have h1lo := (hφ_in_cell y₁ hy1Raw hl1).1
      have hcsLo := (hmem (cellOf y₁) (cellOf_mem y₁)).2.1
      rw [hφ_lit v2 hv2] at heq; omega
    · have hy1Raw : y₁ ∈ raw := by
        rcases List.mem_append.mp hy₁ with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2; exact (hl1 ⟨v, hvMem, rfl⟩).elim
      have hy2Raw : y₂ ∈ raw := by
        rcases List.mem_append.mp hy₂ with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2; exact (hl2 ⟨v, hvMem, rfl⟩).elim
      have ⟨h1l, h1h⟩ := hφ_in_cell y₁ hy1Raw hl1
      have ⟨h2l, h2h⟩ := hφ_in_cell y₂ hy2Raw hl2
      have hcsEq : cellOf y₁ = cellOf y₂ :=
        hdisj (cellOf y₁) (cellOf_mem y₁) (cellOf y₂) (cellOf_mem y₂) (φ y₁)
          h1l h1h (heq ▸ h2l) (heq ▸ h2h)
      simp only [φ, hl1, hl2, ↓reduceDIte, hcsEq] at heq
      cases hvs : (cellOf y₂).values with
      | none =>
        simp only [hvs] at heq
        exact idxOfList_inj (List.mem_eraseDups.mpr hy1Raw) (List.mem_eraseDups.mpr hy2Raw)
          (Nat.add_left_cancel heq)
      | some ws =>
        simp only [hvs] at heq
        by_cases hlt : ws.length < enc.K
        · have hws1 := hfinite_ws y₁ hl1 (hcsEq ▸ hvs) hlt
          have hws2 := hfinite_ws y₂ hl2 hvs hlt
          simp only [hlt, ↓reduceIte, hws1, hws2, ↓reduceDIte] at heq
          have hvEq := idxOfList_inj (Classical.choose_spec hws1).1 (Classical.choose_spec hws2).1
            (Nat.add_left_cancel heq)
          rw [← (Classical.choose_spec hws1).2, ← (Classical.choose_spec hws2).2, hvEq]
        · simp only [hlt, ↓reduceIte] at heq
          exact idxOfList_inj (List.mem_eraseDups.mpr hy1Raw) (List.mem_eraseDups.mpr hy2Raw)
            (Nat.add_left_cancel heq)
  · -- DataRange preservation
    intro y hy d hd
    simp only [WiderEncoding.encodeIntervals, List.mem_append, List.mem_filterMap, List.mem_range]
    by_cases hlit : ∃ v ∈ enc.litVals, source.value v = y
    · obtain ⟨v, hvMem, rfl⟩ := hlit
      have hidxLt := idxOfList_lt hvMem
      rw [hφ_lit v hvMem]
      rw [← source.evalLiteral v hvMem d hd]
      constructor
      · intro hev
        refine ⟨(idxOfList enc.litVals v, idxOfList enc.litVals v), .inl ⟨idxOfList enc.litVals v, hidxLt, ?_⟩,
          Nat.le_refl _, Nat.le_refl _⟩
        simp [hidxLt, getElem_idxOfList hvMem, hev]
      · rintro ⟨iv, ⟨idx, hidx, hfilt⟩ | ⟨cs, hcs, hfilt⟩, hlo, hhi⟩
        · simp only [hidx, ↓reduceDIte] at hfilt
          split at hfilt
          · rename_i hev
            cases hfilt
            have hne : idx = idxOfList enc.litVals v := by omega
            subst hne
            rwa [getElem_idxOfList hvMem] at hev
          · cases hfilt
        · split at hfilt
          · cases hfilt
            have := (hmem cs hcs).2.1; omega
          · cases hfilt
    · have hyRaw : y ∈ raw := by
        rcases List.mem_append.mp hy with h1 | h2
        · exact h1
        · obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp h2; exact (hlit ⟨v, hvMem, rfl⟩).elim
      have ⟨hlo, hhi⟩ := hφ_in_cell y hyRaw hlit
      have hcs := cellOf_mem y
      have hpart := (hmem (cellOf y) hcs).1
      rw [← evalOnPartition_iff hpart (cellOf_holds y) hd]
      constructor
      · intro hev
        refine ⟨((cellOf y).lo, (cellOf y).lo + (cellOf y).len - 1), .inr ⟨cellOf y, hcs, ?_⟩, hlo, by omega⟩
        have hpos : 0 < (cellOf y).len := by omega
        simp [hpos, hev]
      · rintro ⟨iv, ⟨idx, hidx, hfilt⟩ | ⟨cs', hcs', hfilt⟩, hil, hih⟩
        · simp only [hidx, ↓reduceDIte] at hfilt
          split at hfilt
          · cases hfilt
            have := (hmem (cellOf y) hcs).2.1; omega
          · cases hfilt
        · split at hfilt
          · rename_i hcond
            cases hfilt
            obtain ⟨hpos, hev⟩ := Bool.and_eq_true_iff.mp hcond
            have hpos' : 0 < cs'.len := decide_eq_true_eq.mp hpos
            have heq := hdisj (cellOf y) hcs cs' hcs' (φ y) hlo hhi hil (by omega)
            subst heq; exact hev
          · cases hfilt

private theorem encodeWiderData_sat_of_source {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) {dm : DatatypeMap} (i : Interpretation dm)
    (source : enc.Source i) (hm : p.Models i) {x₀ : i.Object}
    (hx₀ : holds i x₀ p.root) : (enc.encodeProblem p).Sat := by
  classical
  letI : DecidableEq i.Object := fun a b => Classical.propDecidable (a = b)
  -- Decide whether keys use any data properties (if so, share one slot map across all named objects)
  let hasDataKeys := !(p.keys.all fun k => k.dataProps.isEmpty)
  let namedObjs : List i.Object :=
    i.individuals (.named "") :: p.nominals.map fun a => i.individuals (.named a)
  let namedRaw : List i.Data := namedObjs.flatMap (rawWitnesses i p)
  have hnamedRawLen : hasDataKeys = true → namedRaw.length ≤ enc.K := by
    intro hdk
    have hkn : p.keys.all (fun k => k.dataProps.isEmpty) = false := by
      simp only [hasDataKeys, Bool.not_eq_true'] at hdk; exact hdk
    have hKeq : enc.K = max 1 ((1 + p.nominals.length) * p.localDataDemand) := by
      rw [hv.hK, Problem.widerWitnessCap, hkn]; rfl
    have hlen1 : namedRaw.length ≤ namedObjs.length * p.localDataDemand :=
      length_flatMap_le_mul namedObjs (rawWitnesses i p) p.localDataDemand
        fun x _ => rawWitnesses_length_le i p x
    have hlen2 : namedObjs.length = 1 + p.nominals.length := by simp [namedObjs]; omega
    rw [hKeq, ← hlen2]
    exact Nat.le_trans hlen1 (Nat.le_max_right _ _)
  have hlocalLen (x : i.Object) : (rawWitnesses i p x).length ≤ enc.K := by
    have h1 := rawWitnesses_length_le i p x
    rw [hv.hK, Problem.widerWitnessCap]
    split
    · simp only [Nat.one_mul]; exact Nat.le_trans h1 (Nat.le_max_right _ _)
    · have hge : p.localDataDemand ≤ (1 + p.nominals.length) * p.localDataDemand := by
        calc p.localDataDemand = 1 * p.localDataDemand := (Nat.one_mul _).symm
          _ ≤ (1 + p.nominals.length) * p.localDataDemand := Nat.mul_le_mul_right _ (by omega)
      exact Nat.le_trans h1 (Nat.le_trans hge (Nat.le_max_right _ _))
  -- Per-object kept witness list `W x` and slot map `φ x`
  let W (x : i.Object) : List i.Data :=
    (if hasDataKeys && decide (x ∈ namedObjs) then namedRaw else rawWitnesses i p x) ++
    enc.litVals.map source.value
  have hW_sub_raw (x : i.Object) : ∀ y ∈ rawWitnesses i p x, y ∈ W x := by
    intro y hy
    simp only [W, List.mem_append]
    left
    split
    · rename_i hcond
      have hmem := decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp hcond).2
      exact List.mem_flatMap.mpr ⟨x, hmem, hy⟩
    · exact hy
  have hW_lit (x : i.Object) : ∀ v ∈ enc.litVals, source.value v ∈ W x := fun v hvMem =>
    List.mem_append_right _ (List.mem_map_of_mem hvMem)
  let rawFor (x : i.Object) : List i.Data :=
    if hasDataKeys && decide (x ∈ namedObjs) then namedRaw else rawWitnesses i p x
  have hrawForLen (x : i.Object) : (rawFor x).length ≤ enc.K := by
    simp only [rawFor]
    split
    · rename_i hcond
      exact hnamedRawLen (Bool.and_eq_true_iff.mp hcond).1
    · exact hlocalLen x
  -- Notice: for all x ∈ namedObjs when hasDataKeys = true, `rawFor x = namedRaw` definitionally,
  -- so building the slot map purely as a function of `rawFor x` yields ONE IDENTICAL map!
  let slotMapFor (r : List i.Data) (hr : r.length ≤ enc.K) := buildSlotMap hv i source r hr
  let φ (x : i.Object) : i.Data → Nat := (slotMapFor (rawFor x) (hrawForLen x)).1
  have hφ_bound (x : i.Object) : ∀ y ∈ W x, φ x y < enc.totalSlots :=
    (slotMapFor (rawFor x) (hrawForLen x)).2.1
  have hφ_lit (x : i.Object) : ∀ v ∈ enc.litVals, φ x (source.value v) = idxOfList enc.litVals v :=
    (slotMapFor (rawFor x) (hrawForLen x)).2.2.1
  have hφ_inj (x : i.Object) : ∀ y₁ ∈ W x, ∀ y₂ ∈ W x, φ x y₁ = φ x y₂ → y₁ = y₂ :=
    (slotMapFor (rawFor x) (hrawForLen x)).2.2.2.1
  have hφ_dr (x : i.Object) : ∀ y ∈ W x, ∀ d : DataRange,
      (∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) →
      (dataHolds i y d ↔ ∃ iv ∈ enc.encodeIntervals d, iv.1 ≤ φ x y ∧ φ x y ≤ iv.2) :=
    (slotMapFor (rawFor x) (hrawForLen x)).2.2.2.2
  have hφ_named_eq (hdk : hasDataKeys = true) {x₁ x₂ : i.Object}
      (hx1 : x₁ ∈ namedObjs) (hx2 : x₂ ∈ namedObjs) : φ x₁ = φ x₂ := by
    have h1 : rawFor x₁ = namedRaw := by simp [rawFor, hdk, hx1]
    have h2 : rawFor x₂ = namedRaw := by simp [rawFor, hdk, hx2]
    have hproof (r₁ r₂ : List i.Data) (hr1 : r₁.length ≤ enc.K) (hr2 : r₂.length ≤ enc.K)
        (heq : r₁ = r₂) : (slotMapFor r₁ hr1).1 = (slotMapFor r₂ hr2).1 := by
      subst heq; rfl
    exact hproof _ _ _ _ (h1.trans h2.symm)
  have hW_named_eq (hdk : hasDataKeys = true) {x₁ x₂ : i.Object}
      (hx1 : x₁ ∈ namedObjs) (hx2 : x₂ ∈ namedObjs) : W x₁ = W x₂ := by
    simp [W, hdk, hx1, hx2]
  -- Construct i' : Interpretation datatypeMap
  let ind' : Individual → i.Object
    | .named a => if a ∈ p.nominals then i.individuals (.named a) else i.individuals (.named "")
    | .anonymous doc lid => i.individuals (.anonymous doc lid)
  have hind'_mem_named (a : IRI) : ind' (.named a) ∈ namedObjs := by
    simp only [ind', namedObjs, List.mem_cons, List.mem_map]
    split
    · rename_i ha; right; exact ⟨a, ha, rfl⟩
    · left; rfl
  have hnamed_imp_i (x : i.Object) (hx : x ∈ namedObjs) : i.named x := by
    simp only [namedObjs, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨a, _, rfl⟩
    · exact i.namedIndividual ""
    · exact i.namedIndividual a
  have hind'_eq (ind : Individual) (h : ind ∈ p.allIndividuals) : ind' ind = i.individuals ind := by
    cases ind with
    | anonymous doc lid => rfl
    | named a =>
      have ha : a ∈ p.nominals := by
        simp only [Problem.nominals, List.mem_filterMap]
        exact ⟨.named a, h, rfl⟩
      simp [ind', ha]
  let i' : Interpretation datatypeMap :=
    { Object := i.Object
      objectNonempty := i.objectNonempty
      Data := Option Value
      dataNonempty := ⟨none⟩
      embedValue := some
      embedValue_injective := Option.some.inj
      classes := i.classes
      objectProperties := i.objectProperties
      dataProperties := fun dp x z =>
        if dp = topDataProperty then True
        else if dp = bottomDataProperty then False
        else ∃ y ∈ W x, i.dataProperties dp x y ∧ z = some (.integer (Int.ofNat (φ x y)))
      individuals := ind'
      datatypes := fun t z => t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = z
      literalValue := decodeLiteral
      lexicalAgreement := fun _ _ h => h
      named := fun x => x ∈ namedObjs
      namedIndividual := hind'_mem_named
      thingExt := i.thingExt
      nothingExt := i.nothingExt
      topObjectExt := i.topObjectExt
      bottomObjectExt := i.bottomObjectExt
      topDataExt := fun _ _ => by simp
      bottomDataExt := fun _ _ => by
        have h : bottomDataProperty ≠ topDataProperty := by decide
        simp [h]
      literalDatatypeExt := fun _ => Or.inl rfl
      datatypeAgreement := fun t ht z => by
        have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
        simp [hn]; exact Iff.rfl }
  have hdataHolds_enc (x : i.Object) {y : i.Data} (hy : y ∈ W x) {d : DataRange}
      (hd : ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) :
      dataHolds i' (some (.integer (Int.ofNat (φ x y)))) (enc.encodeDataRange d) ↔ dataHolds i y d := by
    rw [WiderEncoding.encodeDataRange, dataHolds_intIntervalsDR_iff, hφ_dr x y hy d hd]
    constructor
    · rintro ⟨iv, hiv, m, hlo, hhi, heq⟩
      have hmeq : φ x y = m := by
        have := congrArg Rat.num (Value.number.inj (Option.some.inj heq))
        simp at this; omega
      subst hmeq; exact ⟨iv, hiv, hlo, hhi⟩
    · rintro ⟨iv, hiv, hlo, hhi⟩
      exact ⟨iv, hiv, φ x y, hlo, hhi, rfl⟩
  have hholds_iff : ∀ (c : Concept),
      (∀ ind ∈ c.individuals, ind ∈ p.allIndividuals) →
      (∀ dp ∈ c.dataPropsOf, dp ∈ p.allDataProps) →
      (∀ l ∈ c.dataLiteralsOf, l ∈ enc.lits) →
      (∀ d ∈ c.dataRangesOf, ∀ a ∈ atomsOfDataRange d, a ∈ enc.atoms) →
      (∀ x : i.Object, ∀ y ∈ collectWitnesses i x c, y ∈ W x) →
      ∀ x : i.Object, holds i' x (enc.encodeConcept c) ↔ holds i x c := by
    intro c
    induction c with
    | top | bottom => intro _ _ _ _ _ _; rfl
    | lit _ b => intro _ _ _ _ _ _; cases b <;> rfl
    | nom ind b =>
      intro hind _ _ _ _ x
      have heq := hind'_eq ind (hind ind (List.mem_singleton_self _))
      cases b <;> simp [WiderEncoding.encodeConcept, holds, i', heq]
    | self r b => intro _ _ _ _ _ _; rcases r with ⟨_, _ | _⟩ <;> cases b <;> rfl
    | conj a b iha ihb =>
      intro hind hdp hlit hdr hw x
      exact and_congr
        (iha (fun z hz => hind z (List.mem_append_left _ hz))
             (fun z hz => hdp z (List.mem_append_left _ hz))
             (fun z hz => hlit z (List.mem_append_left _ hz))
             (fun z hz => hdr z (List.mem_append_left _ hz))
             (fun u y hy => hw u y (List.mem_append_left _ hy)) x)
        (ihb (fun z hz => hind z (List.mem_append_right _ hz))
             (fun z hz => hdp z (List.mem_append_right _ hz))
             (fun z hz => hlit z (List.mem_append_right _ hz))
             (fun z hz => hdr z (List.mem_append_right _ hz))
             (fun u y hy => hw u y (List.mem_append_right _ hy)) x)
    | disj a b iha ihb =>
      intro hind hdp hlit hdr hw x
      exact or_congr
        (iha (fun z hz => hind z (List.mem_append_left _ hz))
             (fun z hz => hdp z (List.mem_append_left _ hz))
             (fun z hz => hlit z (List.mem_append_left _ hz))
             (fun z hz => hdr z (List.mem_append_left _ hz))
             (fun u y hy => hw u y (List.mem_append_left _ hy)) x)
        (ihb (fun z hz => hind z (List.mem_append_right _ hz))
             (fun z hz => hdp z (List.mem_append_right _ hz))
             (fun z hz => hlit z (List.mem_append_right _ hz))
             (fun z hz => hdr z (List.mem_append_right _ hz))
             (fun u y hy => hw u y (List.mem_append_right _ hy)) x)
    | some r c ih =>
      intro hind hdp hlit hdr hw x
      exact exists_congr fun y => and_congr Iff.rfl (ih hind hdp hlit hdr hw y)
    | all r c ih =>
      intro hind hdp hlit hdr hw x
      exact forall_congr' fun y => imp_congr Iff.rfl (ih hind hdp hlit hdr hw y)
    | min n r c ih =>
      intro hind hdp hlit hdr hw x
      exact w_atLeast_congr (fun y => and_congr Iff.rfl (ih hind hdp hlit hdr hw y)) n
    | max n r c ih =>
      intro hind hdp hlit hdr hw x
      exact not_congr (w_atLeast_congr (fun y => and_congr Iff.rfl (ih hind hdp hlit hdr hw y)) (n + 1))
    | dataSome dp d =>
      intro _ hdp _ hdr hw x
      have ⟨hnt, hnb⟩ := hv.hdprops dp (hdp dp (List.mem_singleton_self _))
      have hd := hdr d (List.mem_singleton_self _)
      simp only [WiderEncoding.encodeConcept, holds, i', hnt, hnb, ↓reduceIte]
      constructor
      · rintro ⟨z, ⟨y, hyW, hrel, rfl⟩, hdz⟩
        exact ⟨y, hrel, (hdataHolds_enc x hyW hd).mp hdz⟩
      · intro hex
        let y := Classical.choose hex
        have hySpec := Classical.choose_spec hex
        have hyW : y ∈ W x := hw x y (by simp [collectWitnesses, hex, y])
        exact ⟨some (.integer (Int.ofNat (φ x y))), ⟨y, hyW, hySpec.1, rfl⟩,
          (hdataHolds_enc x hyW hd).mpr hySpec.2⟩
    | dataAll dp d =>
      intro _ hdp _ hdr hw x
      have ⟨hnt, hnb⟩ := hv.hdprops dp (hdp dp (List.mem_singleton_self _))
      have hd := hdr d (List.mem_singleton_self _)
      simp only [WiderEncoding.encodeConcept, holds, i', hnt, hnb, ↓reduceIte]
      constructor
      · intro hall y hrel
        exact Classical.byContradiction fun hnd => by
          have hex : ∃ u, i.dataProperties dp x u ∧ ¬ dataHolds i u d := ⟨y, hrel, hnd⟩
          let u := Classical.choose hex
          have huSpec := Classical.choose_spec hex
          have huW : u ∈ W x := hw x u (by simp [collectWitnesses, hex, u])
          have hdz := hall (some (.integer (Int.ofNat (φ x u)))) ⟨u, huW, huSpec.1, rfl⟩
          exact huSpec.2 ((hdataHolds_enc x huW hd).mp hdz)
      · rintro hall z ⟨y, hyW, hrel, rfl⟩
        exact (hdataHolds_enc x hyW hd).mpr (hall y hrel)
    | dataValue dp l b =>
      intro _ hdp hlit _ _ x
      have ⟨hnt, hnb⟩ := hv.hdprops dp (hdp dp (List.mem_singleton_self _))
      obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv (hlit l (List.mem_singleton_self _))
      have hlitOrig : i.literalValue l = source.value v := source.literal l (hlit l (List.mem_singleton_self _)) v hdl
      have hlitEnc : i'.literalValue (enc.encodeLiteral l) =
          some (.integer (Int.ofNat (idxOfList enc.litVals v))) := by
        simp only [i', WiderEncoding.encodeLiteral, hdl, decodeLiteral_natLit]
      have hiff : i'.dataProperties dp x (i'.literalValue (enc.encodeLiteral l)) ↔
          i.dataProperties dp x (i.literalValue l) := by
        rw [hlitEnc, hlitOrig]
        simp only [i', hnt, hnb, ↓reduceIte]
        constructor
        · rintro ⟨y, hyW, hrel, heq⟩
          have hphiEq : φ x y = idxOfList enc.litVals v := by
            have := congrArg Rat.num (Value.number.inj (Option.some.inj heq))
            simp at this; omega
          have hyEq := hφ_inj x y hyW (source.value v) (hW_lit x v hvMem)
            (hphiEq.trans (hφ_lit x v hvMem).symm)
          rwa [← hyEq]
        · intro hrel
          exact ⟨source.value v, hW_lit x v hvMem, hrel, by rw [hφ_lit x v hvMem]⟩
      cases b <;> simp only [WiderEncoding.encodeConcept, holds, hiff]
    | dataMin n dp d =>
      intro _ hdp _ hdr hw x
      have ⟨hnt, hnb⟩ := hv.hdprops dp (hdp dp (List.mem_singleton_self _))
      have hd := hdr d (List.mem_singleton_self _)
      simp only [WiderEncoding.encodeConcept, holds, i', hnt, hnb, ↓reduceIte]
      constructor
      · rintro ⟨zs, hlen, hnd, hzp⟩
        have haux : ∀ l : List (Option Value), l.Nodup →
            (∀ z ∈ l, (∃ y ∈ W x, i.dataProperties dp x y ∧ z = some (Value.integer (Int.ofNat (φ x y)))) ∧
              dataHolds i' z (enc.encodeDataRange d)) →
            ∃ ys : List i.Data, ys.length = l.length ∧ ys.Nodup ∧
              (∀ y ∈ ys, i.dataProperties dp x y ∧ dataHolds i y d) ∧
              ys.map (fun y => some (Value.integer (Int.ofNat (φ x y)))) = l := by
          intro l
          induction l with
          | nil => intro _ _; exact ⟨[], rfl, List.nodup_nil, by simp, rfl⟩
          | cons z rest ih =>
            intro hndl hql
            obtain ⟨hnz, hnd'⟩ := List.nodup_cons.mp hndl
            obtain ⟨⟨y, hyW, hrel, rfl⟩, hdz⟩ := hql z (List.mem_cons_self ..)
            obtain ⟨ys, hyl, hynd, hyP, hymap⟩ := ih hnd' fun u hu => hql u (List.mem_cons_of_mem _ hu)
            refine ⟨y :: ys, by simp [hyl], List.nodup_cons.mpr ⟨?_, hynd⟩, ?_, by simp only [List.map_cons, hymap]⟩
            · intro hym
              have : some (Value.integer (Int.ofNat (φ x y))) ∈
                  ys.map (fun u => some (Value.integer (Int.ofNat (φ x u)))) :=
                List.mem_map_of_mem hym
              rw [hymap] at this; exact hnz this
            · intro u hu
              rcases List.mem_cons.mp hu with rfl | hr
              · exact ⟨hrel, (hdataHolds_enc x hyW hd).mp hdz⟩
              · exact hyP u hr
        obtain ⟨ys, hyl, hynd, hyP, _⟩ := haux zs hnd hzp
        exact ⟨ys, hyl.trans hlen, hynd, hyP⟩
      · intro hat
        have hmapNd : ∀ (l : List i.Data), l.Nodup → (∀ y ∈ l, y ∈ W x) →
            (l.map (fun y => some (Value.integer (Int.ofNat (φ x y))))).Nodup := by
          intro l
          induction l with
          | nil => intro _ _; exact List.nodup_nil
          | cons a rest ih =>
            intro hndl hlW
            obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hndl
            refine List.nodup_cons.mpr ⟨?_, ih hnd' fun u hu => hlW u (List.mem_cons_of_mem _ hu)⟩
            intro hm
            obtain ⟨b, hb, hfeq⟩ := List.mem_map.mp hm
            have hpeq : φ x b = φ x a := by
              have := congrArg Rat.num (Value.number.inj (Option.some.inj hfeq))
              simp at this; omega
            have hba := hφ_inj x b (hlW b (List.mem_cons_of_mem _ hb)) a (hlW a (List.mem_cons_self ..)) hpeq
            exact hna (hba ▸ hb)
        obtain ⟨hlen, hnd, hyp⟩ := Classical.choose_spec hat
        have hysW : ∀ y ∈ Classical.choose hat, y ∈ W x := fun y hy =>
          hw x y (by simp [collectWitnesses, hat, hy])
        refine ⟨(Classical.choose hat).map (fun y => some (Value.integer (Int.ofNat (φ x y)))),
          by rw [List.length_map]; exact hlen, hmapNd _ hnd hysW, ?_⟩
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        have ⟨hrel, hdy⟩ := hyp y hy
        exact ⟨⟨y, hysW y hy, hrel, rfl⟩, (hdataHolds_enc x (hysW y hy) hd).mpr hdy⟩
    | dataMax n dp d =>
      intro _ hdp _ hdr hw x
      have ⟨hnt, hnb⟩ := hv.hdprops dp (hdp dp (List.mem_singleton_self _))
      have hd := hdr d (List.mem_singleton_self _)
      simp only [WiderEncoding.encodeConcept, holds, i', hnt, hnb, ↓reduceIte]
      apply not_congr
      constructor
      · rintro ⟨zs, hlen, hnd, hzp⟩
        have haux : ∀ l : List (Option Value), l.Nodup →
            (∀ z ∈ l, (∃ y ∈ W x, i.dataProperties dp x y ∧ z = some (Value.integer (Int.ofNat (φ x y)))) ∧
              dataHolds i' z (enc.encodeDataRange d)) →
            ∃ ys : List i.Data, ys.length = l.length ∧ ys.Nodup ∧
              (∀ y ∈ ys, i.dataProperties dp x y ∧ dataHolds i y d) ∧
              ys.map (fun y => some (Value.integer (Int.ofNat (φ x y)))) = l := by
          intro l
          induction l with
          | nil => intro _ _; exact ⟨[], rfl, List.nodup_nil, by simp, rfl⟩
          | cons z rest ih =>
            intro hndl hql
            obtain ⟨hnz, hnd'⟩ := List.nodup_cons.mp hndl
            obtain ⟨⟨y, hyW, hrel, rfl⟩, hdz⟩ := hql z (List.mem_cons_self ..)
            obtain ⟨ys, hyl, hynd, hyP, hymap⟩ := ih hnd' fun u hu => hql u (List.mem_cons_of_mem _ hu)
            refine ⟨y :: ys, by simp [hyl], List.nodup_cons.mpr ⟨?_, hynd⟩, ?_, by simp only [List.map_cons, hymap]⟩
            · intro hym
              have : some (Value.integer (Int.ofNat (φ x y))) ∈
                  ys.map (fun u => some (Value.integer (Int.ofNat (φ x u)))) :=
                List.mem_map_of_mem hym
              rw [hymap] at this; exact hnz this
            · intro u hu
              rcases List.mem_cons.mp hu with rfl | hr
              · exact ⟨hrel, (hdataHolds_enc x hyW hd).mp hdz⟩
              · exact hyP u hr
        obtain ⟨ys, hyl, hynd, hyP, _⟩ := haux zs hnd hzp
        exact ⟨ys, hyl.trans hlen, hynd, hyP⟩
      · intro hat
        have hmapNd : ∀ (l : List i.Data), l.Nodup → (∀ y ∈ l, y ∈ W x) →
            (l.map (fun y => some (Value.integer (Int.ofNat (φ x y))))).Nodup := by
          intro l
          induction l with
          | nil => intro _ _; exact List.nodup_nil
          | cons a rest ih =>
            intro hndl hlW
            obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hndl
            refine List.nodup_cons.mpr ⟨?_, ih hnd' fun u hu => hlW u (List.mem_cons_of_mem _ hu)⟩
            intro hm
            obtain ⟨b, hb, hfeq⟩ := List.mem_map.mp hm
            have hpeq : φ x b = φ x a := by
              have := congrArg Rat.num (Value.number.inj (Option.some.inj hfeq))
              simp at this; omega
            have hba := hφ_inj x b (hlW b (List.mem_cons_of_mem _ hb)) a (hlW a (List.mem_cons_self ..)) hpeq
            exact hna (hba ▸ hb)
        obtain ⟨hlen, hnd, hyp⟩ := Classical.choose_spec hat
        have hysW : ∀ y ∈ Classical.choose hat, y ∈ W x := fun y hy =>
          hw x y (by simp [collectWitnesses, hat, hy])
        refine ⟨(Classical.choose hat).map (fun y => some (Value.integer (Int.ofNat (φ x y)))),
          by rw [List.length_map]; exact hlen, hmapNd _ hnd hysW, ?_⟩
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        have ⟨hrel, hdy⟩ := hyp y hy
        exact ⟨⟨y, hysW y hy, hrel, rfl⟩, (hdataHolds_enc x (hysW y hy) hd).mpr hdy⟩
  have hconcAll (c : Concept) (hc : c ∈ p.allConcepts)
      (hind : ∀ ind ∈ c.individuals, ind ∈ p.allIndividuals) (x : i.Object) :
      holds i' x (enc.encodeConcept c) ↔ holds i x c := by
    have ⟨h1, h2, h3⟩ := mem_allConcepts_subs hv hc
    exact hholds_iff c hind h1 h2 h3
      (fun u y hy => hW_sub_raw u y (mem_collectWitnesses_sub_rawWitnesses i p u hc y hy)) x
  have hrootInd : ∀ ind ∈ p.root.individuals, ind ∈ p.allIndividuals := fun ind h => by
    simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append]
    left; left; left; left; left; left; left; left; left; exact h
  refine ⟨i', ?_, x₀, (hconcAll p.root (List.mem_cons_self ..) hrootInd x₀).mpr hx₀⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- tbox
    intro q' hq' x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    have hsubC : q.sub ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; left; left; exact ⟨q, hq, by simp⟩
    have hsupC : q.sup ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; left; left; exact ⟨q, hq, by simp⟩
    have hsubI : ∀ ind ∈ q.sub.individuals, ind ∈ p.allIndividuals := fun ind h => by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; left; left; right; exact ⟨q, hq, .inl h⟩
    have hsupI : ∀ ind ∈ q.sup.individuals, ind ∈ p.allIndividuals := fun ind h => by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; left; left; right; exact ⟨q, hq, .inr h⟩
    exact (hconcAll q.sup hsupC hsupI x).mpr (hm.tbox q hq x ((hconcAll q.sub hsubC hsubI x).mp hx))
  · exact hm.rules
  · intro c hc x y hp
    exact hm.chains c hc x y ((objPath_eq_of_objProps (i₁ := i') (i₂ := i) rfl (fun _ _ _ => Iff.rfl) c.body x y).mp hp)
  · exact hm.reflexive
  · exact hm.irreflexive
  · exact hm.asymmetric
  · exact hm.disjoint
  · -- subData
    intro rs hrs x z hz
    have hr1 : rs.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have hr2 : rs.2 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have ⟨ht1, hb1⟩ := hv.hdprops rs.1 hr1
    have ⟨ht2, hb2⟩ := hv.hdprops rs.2 hr2
    simp only [i', ht1, hb1, ht2, hb2, ↓reduceIte] at hz ⊢
    obtain ⟨y, hyW, hrel, rfl⟩ := hz
    exact ⟨y, hyW, hm.subData rs hrs x y hrel, rfl⟩
  · -- disjointData
    intro rs hrs x z ⟨h1, h2⟩
    have hr1 : rs.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have hr2 : rs.2 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rs, hrs, by simp⟩
    have ⟨ht1, hb1⟩ := hv.hdprops rs.1 hr1
    have ⟨ht2, hb2⟩ := hv.hdprops rs.2 hr2
    simp only [i', ht1, hb1, ht2, hb2, ↓reduceIte] at h1 h2
    obtain ⟨y1, hy1W, hr1', rfl⟩ := h1
    obtain ⟨y2, hy2W, hr2', heq⟩ := h2
    have hpeq : φ x y1 = φ x y2 := by
      have := congrArg Rat.num (Value.number.inj (Option.some.inj heq))
      simp at this; omega
    have hyEq := hφ_inj x y1 hy1W y2 hy2W hpeq
    subst hyEq
    exact hm.disjointData rs hrs x y1 ⟨hr1', hr2'⟩
  · -- funcData
    intro r hr x z1 z2 h1 h2
    have hdp : r ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append]
      left; left; left; right; exact hr
    have ⟨ht, hb⟩ := hv.hdprops r hdp
    simp only [i', ht, hb, ↓reduceIte] at h1 h2
    obtain ⟨y1, _, hr1, rfl⟩ := h1
    obtain ⟨y2, _, hr2, rfl⟩ := h2
    rw [hm.funcData r hr x y1 y2 hr1 hr2]
  · -- dataRanges (encoded original ranges + domRanges)
    intro rd' hrd' x z hz
    rcases List.mem_append.mp hrd' with h1 | h2
    · obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp h1
      have hdp : rd.1 ∈ p.allDataProps := by
        simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
        left; left; left; left; left; left; right; exact ⟨rd, hrd, rfl⟩
      have hd : ∀ a ∈ atomsOfDataRange rd.2, a ∈ enc.atoms := fun a ha => by
        rw [hv.hatoms]
        simp only [Problem.allDataAtoms, Problem.allDataRanges, List.mem_eraseDups, List.mem_flatMap,
          List.mem_append, List.mem_map]
        exact ⟨rd.2, .inr ⟨rd, hrd, rfl⟩, ha⟩
      have ⟨ht, hb⟩ := hv.hdprops rd.1 hdp
      simp only [i', ht, hb, ↓reduceIte] at hz
      obtain ⟨y, hyW, hrel, rfl⟩ := hz
      exact (hdataHolds_enc x hyW hd).mpr (hm.dataRanges rd hrd x y hrel)
    · obtain ⟨dp, hdp, rfl⟩ := List.mem_map.mp h2
      have ⟨ht, hb⟩ := hv.hdprops dp hdp
      simp only [i', ht, hb, ↓reduceIte] at hz
      obtain ⟨y, hyW, _, rfl⟩ := hz
      exact (dataHolds_allSlotsDR_iff i' _ enc.totalSlots).mpr ⟨φ x y, hφ_bound x y hyW, rfl⟩
  · -- keys
    intro k' hk' x y hx hy hnx hny ho hd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    have hclsC : k.cls ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]
      right; left; right; exact ⟨k, hk, rfl⟩
    have hclsI : ∀ ind ∈ k.cls.individuals, ind ∈ p.allIndividuals := fun ind h => by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; left; right; exact ⟨k, hk, h⟩
    refine hm.keys k hk x y ((hconcAll k.cls hclsC hclsI x).mp hx)
      ((hconcAll k.cls hclsC hclsI y).mp hy) (hnamed_imp_i x hnx) (hnamed_imp_i y hny)
      (fun r hr => by
        obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
        exact ⟨z, hnamed_imp_i z hnz, hxz, hyz⟩)
      (fun dp hdp => ?_)
    have hdk : hasDataKeys = true := by
      simp only [hasDataKeys, Bool.not_eq_true']
      cases hall : p.keys.all (fun k0 => k0.dataProps.isEmpty)
      · rfl
      · have hem := List.all_eq_true.mp hall k hk
        cases hks : k.dataProps with
        | nil => rw [hks] at hdp; cases hdp
        | cons _ _ => rw [hks] at hem; cases hem
    have hdpAll : dp ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; right; exact ⟨k, hk, hdp⟩
    have ⟨ht, hb⟩ := hv.hdprops dp hdpAll
    obtain ⟨z, hzx, hzy⟩ := hd dp hdp
    simp only [i', ht, hb, ↓reduceIte] at hzx hzy
    obtain ⟨u1, hu1W, hrx, rfl⟩ := hzx
    obtain ⟨u2, hu2W, hry, heq⟩ := hzy
    have hphiEq := hφ_named_eq hdk hnx hny
    have hWEq := hW_named_eq hdk hnx hny
    have hu2W' : u2 ∈ W x := hWEq ▸ hu2W
    have hvalEq : φ x u1 = φ x u2 := by
      have h1 := congrArg Rat.num (Value.number.inj (Option.some.inj heq))
      simp only [Int.ofNat_eq_natCast, Rat.ofInt_num] at h1
      have h2 : φ x u1 = φ y u2 := by omega
      rw [hphiEq] at h2 ⊢
      exact h2
    have huEq := hφ_inj x u1 hu1W u2 hu2W' hvalEq
    subst huEq
    exact ⟨u1, hrx, hry⟩
  · -- classAssertions
    intro ac' hac'
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp hac'
    have hcaC : ac.2 ∈ p.allConcepts := by
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]
      right; right; exact ⟨ac, hac, rfl⟩
    have hcaI : ∀ ind ∈ ac.2.individuals, ind ∈ p.allIndividuals := fun ind h => by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; right; exact ⟨ac, hac, List.mem_cons_of_mem _ h⟩
    have haI : ac.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; left; right; exact ⟨ac, hac, List.mem_cons_self ..⟩
    change holds i' (ind' ac.1) (enc.encodeConcept ac.2)
    rw [hind'_eq ac.1 haI]
    exact (hconcAll ac.2 hcaC hcaI _).mpr (hm.classAssertions ac hac)
  · -- objAssertions
    intro rab hrab
    have ha1 : rab.2.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rab, hrab, by simp⟩
    have ha2 : rab.2.2 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; left; right; exact ⟨rab, hrab, by simp⟩
    change i.objectProperties rab.1 (ind' rab.2.1) (ind' rab.2.2)
    rw [hind'_eq _ ha1, hind'_eq _ ha2]; exact hm.objAssertions rab hrab
  · -- negObjAssertions
    intro rab hrab
    have ha1 : rab.2.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rab, hrab, by simp⟩
    have ha2 : rab.2.2 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; left; right; exact ⟨rab, hrab, by simp⟩
    change ¬ i.objectProperties rab.1 (ind' rab.2.1) (ind' rab.2.2)
    rw [hind'_eq _ ha1, hind'_eq _ ha2]; exact hm.negObjAssertions rab hrab
  · -- sameInds
    intro ab hab
    have ha1 : ab.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; right; exact ⟨ab, hab, by simp⟩
    have ha2 : ab.2 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; left; right; exact ⟨ab, hab, by simp⟩
    change ind' ab.1 = ind' ab.2
    rw [hind'_eq _ ha1, hind'_eq _ ha2]; exact hm.sameInds ab hab
  · -- diffInds
    intro ab hab
    have ha1 : ab.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; right; exact ⟨ab, hab, by simp⟩
    have ha2 : ab.2 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      left; left; right; exact ⟨ab, hab, by simp⟩
    change ind' ab.1 ≠ ind' ab.2
    rw [hind'_eq _ ha1, hind'_eq _ ha2]; exact hm.diffInds ab hab
  · -- dataAssertions
    intro ral' hral'
    obtain ⟨ral, hral, rfl⟩ := List.mem_map.mp hral'
    have hdp : ral.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; right; exact ⟨ral, hral, rfl⟩
    have haI : ral.2.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; right; exact ⟨ral, hral, rfl⟩
    have hl : ral.2.2 ∈ enc.lits := by
      rw [hv.hlits]
      simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_map]
      left; right; exact ⟨ral, hral, rfl⟩
    have ⟨ht, hb⟩ := hv.hdprops ral.1 hdp
    obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv hl
    have horig := hm.dataAssertions ral hral
    rw [source.literal _ hl v hdl] at horig
    simp only [i', ht, hb, ↓reduceIte, WiderEncoding.encodeLiteral, hdl, decodeLiteral_natLit,
      hind'_eq _ haI]
    exact ⟨source.value v, hW_lit _ v hvMem, horig, by rw [hφ_lit _ v hvMem]⟩
  · -- negDataAssertions
    intro ral' hral'
    obtain ⟨ral, hral, rfl⟩ := List.mem_map.mp hral'
    have hdp : ral.1 ∈ p.allDataProps := by
      simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]
      right; exact ⟨ral, hral, rfl⟩
    have haI : ral.2.1 ∈ p.allIndividuals := by
      simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_map]
      right; exact ⟨ral, hral, rfl⟩
    have hl : ral.2.2 ∈ enc.lits := by
      rw [hv.hlits]
      simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_map]
      right; exact ⟨ral, hral, rfl⟩
    have ⟨ht, hb⟩ := hv.hdprops ral.1 hdp
    obtain ⟨v, hvMem, hdl⟩ := decodeLiteral_mem_litVals hv hl
    have horig := hm.negDataAssertions ral hral
    rw [source.literal _ hl v hdl] at horig
    simp only [i', ht, hb, ↓reduceIte, WiderEncoding.encodeLiteral, hdl, decodeLiteral_natLit,
      hind'_eq _ haI]
    rintro ⟨y, hyW, hrel, heq⟩
    have hpeq : φ (i.individuals ral.2.1) y = idxOfList enc.litVals v := by
      have := congrArg Rat.num (Value.number.inj (Option.some.inj heq))
      simp at this; omega
    have hyEq := hφ_inj _ y hyW (source.value v) (hW_lit _ v hvMem)
      (hpeq.trans (hφ_lit _ v hvMem).symm)
    subst hyEq
    exact horig hrel

/-! ### 6. Equisatisfiability theorem and composed verified decision adapter -/

private def standardSource {p : Problem} {enc : WiderEncoding} (hv : ValidEncoding p enc)
    (i : Interpretation datatypeMap) : enc.Source i where
  value := i.embedValue
  injective := i.embedValue_injective
  literal l _ v hl := i.lexicalAgreement l v hl
  evalLiteral v _ _ hd := evalWiderDataRange_iff (validEncoding_dataRange_wider hv hd) i v
  coverSmall hadm hlt ha y hy := sampleWiderCell_complete_of_lt hadm hlt ha i y hy

private theorem encodeWiderData_sat_mpr {p : Problem} {enc : WiderEncoding}
    (hv : ValidEncoding p enc) (hsat : p.Sat) : (enc.encodeProblem p).Sat := by
  obtain ⟨i, hm, x₀, hx₀⟩ := hsat
  exact encodeWiderData_sat_of_source hv i (standardSource hv i) hm hx₀

theorem WiderEncoding.encode_of_source {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) {dm : DatatypeMap}
    (i : Interpretation dm) (source : enc.Source i)
    (hm : p.Models i) {x : i.Object} (hx : holds i x p.root) : (enc.encodeProblem p).Sat :=
  encodeWiderData_sat_of_source (buildWiderEncoding_valid h) i source hm hx

theorem WiderEncoding.atom_admitted {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) {a : DataRange} (ha : a ∈ enc.atoms) :
    isWiderExactAtom a = true :=
  validEncoding_atoms_wider (buildWiderEncoding_valid h) a ha

theorem WiderEncoding.literal_decoded {p : Problem} {enc : WiderEncoding}
    (h : buildWiderEncoding p = some enc) {v : Value} (hv : v ∈ enc.litVals) :
    ∃ l ∈ enc.lits, decodeLiteral l = some v :=
  (mem_litVals_iff (buildWiderEncoding_valid h) v).mp hv

theorem encodeWiderData_sat_iff {p p' : Problem} (h : encodeWiderData p = some p') :
    p'.Sat ↔ p.Sat := by
  simp only [encodeWiderData, Option.map_eq_some_iff] at h
  obtain ⟨enc, henc, rfl⟩ := h
  have hv := buildWiderEncoding_valid henc
  exact ⟨encodeWiderData_sat_mp hv, encodeWiderData_sat_mpr hv⟩

theorem intIntervalDR_isSROIQD (lo hi : Nat) : (intIntervalDR lo hi).isSROIQD = true := by
  simp only [intIntervalDR, DataRange.isSROIQD, isExactAtomicDataRange, isOrderIntFacet,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨by decide, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩
  · simp [isNumericFacetBound, decodeLiteral_natLit]
  · simp [isNumericFacetBound, decodeLiteral_natLit]

theorem intIntervalsDR_isSROIQD (ivs : List (Nat × Nat)) : (intIntervalsDR ivs).isSROIQD = true := by
  induction ivs with
  | nil => decide
  | cons p rest ih =>
    cases rest with
    | nil => exact intIntervalDR_isSROIQD p.1 p.2
    | cons q qs =>
      simp only [intIntervalsDR, DataRange.isSROIQD_union, Bool.and_eq_true]
      exact ⟨intIntervalDR_isSROIQD p.1 p.2, ih⟩

theorem allSlotsDR_isSROIQD (totalSlots : Nat) : (allSlotsDR totalSlots).isSROIQD = true := by
  unfold allSlotsDR
  split
  · decide
  · exact intIntervalDR_isSROIQD 0 (totalSlots - 1)

theorem encodeDataRange_isSROIQD (enc : WiderEncoding) (d : DataRange) :
    (enc.encodeDataRange d).isSROIQD = true :=
  intIntervalsDR_isSROIQD _

theorem encodeLiteral_isSome (enc : WiderEncoding) (l : Literal) :
    (decodeLiteral (enc.encodeLiteral l)).isSome = true := by
  unfold WiderEncoding.encodeLiteral
  cases decodeLiteral l <;> simp [decodeLiteral_natLit]

/-- Exact wider-data problem decision pipeline (shared by `decideRankedWithWiderDataRanges?`
and `decideRealProblem?`). -/
def decideWiderProblem? (p : Problem) : Option Bool :=
  (lowerTopData? p.lowerBottom).bind fun p1 =>
    (encodeWiderData p1).bind fun q =>
      let lowered := q.lowerAllTopRoleAxioms
      (findRank lowered.rules lowered.chains).bind fun rank =>
        if h : lowered.isSROIQDWithTop rank = true then
          Option.some (decideSROIQDWithTopBool h)
        else none

theorem decideWiderProblem_iff {p : Problem} {b : Bool}
    (h : decideWiderProblem? p = Option.some b) :
    b = true ↔ p.Sat := by
  simp only [decideWiderProblem?, Option.bind_eq_some_iff] at h
  obtain ⟨p1, hp1, q, hq, rank, _, hb⟩ := h
  split at hb
  · rename_i hadmit
    cases hb
    exact (decideSROIQDWithTopBool_iff hadmit).trans
      (q.lowerAllTopRoleAxioms_sat_iff.trans
        ((encodeWiderData_sat_iff hq).trans
          ((lowerTopData_sat_iff hp1).trans p.lowerBottom_sat_iff)))
  · contradiction

/-- Unified verified fuel-free decision adapter extending `decideWithTopRoleAxioms?`
with exact wider OWL 2 DL datatype and facet solving (general decimal/rational/real
order facets, string hierarchy, length facets on strings/PlainLiteral/anyURI/
hexBinary/base64Binary, `dateTime`/`dateTimeStamp`, and `HasKey` over wider data
properties). Takes a zero-overhead fast path when the lowered problem is already
in `isSROIQDWithTop`, and falls back to `decideWiderProblem?` otherwise. -/
def decideRankedWithWiderDataRanges? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    if p.root = .top ∧ p.checkSimpleWithTop = true then
      let fast :=
        let q := p.lowerAllTopRoleAxioms
        (findRank q.rules q.chains).bind fun rank =>
          if h : q.isSROIQDWithTop rank = true then
            Option.some (decideSROIQDWithTopBool h)
          else none
      fast <|> decideWiderProblem? p
    else none

theorem decideRankedWithWiderDataRanges_iff {o : Ontology} {b : Bool}
    (h : decideRankedWithWiderDataRanges? o = Option.some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideRankedWithWiderDataRanges?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, hrest⟩ := h
  split at hrest
  · rename_i hroot
    let fast :=
      let q := p.lowerAllTopRoleAxioms
      (findRank q.rules q.chains).bind fun rank =>
        if h : q.isSROIQDWithTop rank = true then
          Option.some (decideSROIQDWithTopBool h)
        else none
    cases hfast : fast with
    | some bf =>
      have hbf : bf = b := by simpa [fast, hfast] using hrest
      subst hbf
      simp only [fast, Option.bind_eq_some_iff] at hfast
      obtain ⟨rank, _, hb⟩ := hfast
      split at hb
      · rename_i hadmit
        cases hb
        exact (decideSROIQDWithTopBool_iff hadmit).trans
          (p.lowerAllTopRoleAxioms_sat_iff.trans
            ((Normalize.normalizeWithDefs_sat_iff hnorm).trans
              (satisfiable_iff_sat p hroot.1)).symm)
      · contradiction
    | none =>
      have hw : decideWiderProblem? p = Option.some b := by simpa [fast, hfast] using hrest
      exact (decideWiderProblem_iff hw).trans
        ((Normalize.normalizeWithDefs_sat_iff hnorm).trans
          (satisfiable_iff_sat p hroot.1)).symm
  · contradiction

/-- Try the ranked solver, universal grounding, then certified object-role bounds. -/
def decideWithWiderDataRanges? (o : Ontology) : Option Bool :=
  decideRankedWithWiderDataRanges? o <|> OWLUniversal.decideUniversalOntology? o <|>
    ObjectRoleBounds.decideObjectHierarchy? o

theorem decideWithWiderDataRanges_iff {o : Ontology} {b : Bool}
    (h : decideWithWiderDataRanges? o = some b) : b = true ↔ Satisfiable datatypeMap o := by
  cases hr : decideRankedWithWiderDataRanges? o with
  | none =>
    cases hu : OWLUniversal.decideUniversalOntology? o with
    | none => exact ObjectRoleBounds.decideObjectHierarchy_iff (by simpa [decideWithWiderDataRanges?, hr, hu] using h)
    | some v =>
      have he : v = b := by simpa [decideWithWiderDataRanges?, hr, hu] using h
      exact he ▸ OWLUniversal.decideUniversalOntology_iff hu
  | some br =>
    have he : br = b := by simpa [decideWithWiderDataRanges?, hr] using h
    subst br
    exact decideRankedWithWiderDataRanges_iff hr

theorem decideWithWiderDataRanges_unsat_iff {o : Ontology} {b : Bool}
    (h : decideWithWiderDataRanges? o = Option.some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideWithWiderDataRanges_iff h]
  cases b <;> simp

theorem decideWithWiderDataRanges_extends_topRoleAxioms {o : Ontology} {b : Bool}
    (h : decideWithTopRoleAxioms? o = Option.some b) :
    decideWithWiderDataRanges? o = Option.some b := by
  simp only [decideWithTopRoleAxioms?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, hrest⟩ := h
  split at hrest
  · rename_i hroot
    simp only [Option.bind_eq_some_iff] at hrest
    obtain ⟨rank, hrank, hb⟩ := hrest
    split at hb
    · rename_i hadmit
      cases hb
      dsimp only at hroot
      simp [decideWithWiderDataRanges?, decideRankedWithWiderDataRanges?, hnorm, hroot, hrank, hadmit]
    · contradiction
  · contradiction

#print axioms decodeLiteral_natLit
#print axioms dataHolds_intIntervalDR_iff
#print axioms encodeWiderData_sat_iff
#print axioms decideWithWiderDataRanges_iff
#print axioms decideWithWiderDataRanges_unsat_iff
#print axioms decideWithWiderDataRanges_extends_topRoleAxioms

end Sabrina.OWL2.SROIQD.Termination.WiderData
