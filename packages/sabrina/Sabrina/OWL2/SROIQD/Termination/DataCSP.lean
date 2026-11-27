import Sabrina.OWL2.SROIQD.Termination.DataRangeExact
import Sabrina.OWL2.SROIQD.CoreCompleteness
import Std.Data.HashSet.Lemmas

/-!
Exact concrete-datatype constraint satisfaction solver (`DataCSP`) for `SROIQ(D)`.

Supports local and multi-root systems with:
- `dataSome`, `dataAll`, `dataValue` (positive and negative), `dataMin`, `dataMax`
- `subData` (`SubDataPropertyOf`), `disjointData` (`DisjointDataProperties`)
- `funcData` (`FunctionalDataProperty`), `dataRanges` (`DataPropertyRange`)
- `dataAssertions`, `negDataAssertions`
- `keyDisjoint` (disjoint data-property constraints across named roots for mixed `HasKey`)

Both soundness (`solveDataCSP_sound`) and completeness (`solveDataCSP_complete`)
are kernel-verified without fuel approximations.
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.OWL2.Datatypes

/-! ### 1. Compound `DataRange` evaluation over `Value` -/

def evalDataRange : DataRange → Value → Bool
  | .complement r, v => !evalDataRange r v
  | .intersection a b, v => evalDataRange a v && evalDataRange b v
  | .union a b, v => evalDataRange a v || evalDataRange b v
  | a, v => evalAtom a v

theorem evalDataRange_iff {d : DataRange} (hd : d.isSROIQD = true)
    (i : Interpretation datatypeMap) (v : Value) :
    evalDataRange d v = true ↔ dataHolds i (i.embedValue v) d := by
  induction d with
  | complement r ih =>
    simp only [evalDataRange, Bool.not_eq_true', Bool.eq_false_iff, dataHolds]
    exact not_congr (ih hd)
  | intersection a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalDataRange, Bool.and_eq_true, dataHolds]
    exact and_congr (iha ha) (ihb hb)
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hd
    simp only [evalDataRange, Bool.or_eq_true, dataHolds]
    exact or_congr (iha ha) (ihb hb)
  | datatype _ | restriction _ _ | oneOf _ =>
    exact evalAtom_iff hd i v

theorem evalDataRange_eq_evalOnPartition {atoms pos neg : List DataRange}
    (hpos : ∀ a ∈ pos, isExactAtomicDataRange a = true)
    (hneg : ∀ a ∈ neg, isExactAtomicDataRange a = true)
    (hpart : (pos, neg) ∈ prunedExactPartitions atoms)
    {v : Value} (hv : evalPartition pos neg v = true)
    {d : DataRange} (hd : d.isSROIQD = true)
    (hsub : ∀ a ∈ atomsOfDataRange d, a ∈ atoms) :
    evalDataRange d v = evalOnPartition pos d := by
  let i₀ := (SROIQDModel.mk ⟨0, [], []⟩ [] [] []).toInterpretation
  have hpartHolds : dataHolds i₀ (i₀.embedValue v) (partitionRange pos neg) :=
    (evalPartition_iff hpos hneg i₀ v).mp hv
  have h1 := evalDataRange_iff hd i₀ v
  have h2 := evalOnPartition_iff_pruned hpart hpartHolds hsub
  cases h3 : evalDataRange d v <;> cases h4 : evalOnPartition pos d
  · rfl
  · exfalso
    have hh := h2.mp h4
    have ht := h1.mpr hh
    rw [h3] at ht; cases ht
  · exfalso
    have hh := h1.mp h3
    have ht := h2.mpr hh
    rw [h4] at ht; cases ht
  · rfl

/-! ### 2. Reflexive-transitive `subData` closure (`subDataStar`) -/

def subDataStep (subData : List (IRI × IRI)) (cur : List IRI) : List IRI :=
  (cur ++ subData.filterMap fun (r, t) => if cur.contains r then some t else none).eraseDups

theorem mem_subDataStep_of_mem {subData : List (IRI × IRI)} {cur : List IRI} {x : IRI}
    (hx : x ∈ cur) : x ∈ subDataStep subData cur :=
  List.mem_eraseDups.mpr (List.mem_append_left _ hx)

def subDataUniverse (subData : List (IRI × IRI)) (dp : IRI) : List IRI :=
  (dp :: subData.map Prod.snd).eraseDups

theorem subDataStep_subset_universe {subData : List (IRI × IRI)} {dp : IRI} {cur : List IRI}
    (hsub : ∀ x ∈ cur, x ∈ subDataUniverse subData dp) :
    ∀ x ∈ subDataStep subData cur, x ∈ subDataUniverse subData dp := by
  intro x hx
  rcases List.mem_append.mp (List.mem_eraseDups.mp hx) with h1 | h2
  · exact hsub x h1
  · obtain ⟨⟨r, t⟩, hrt, hif⟩ := List.mem_filterMap.mp h2
    simp at hif
    rw [← hif.2]
    exact List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_map_of_mem hrt))

def subDataLoop (subData : List (IRI × IRI)) : Nat → List IRI → List IRI
  | 0, cur => cur
  | n + 1, cur =>
    let next := subDataStep subData cur
    if next.all (cur.contains ·) then cur
    else subDataLoop subData n next

def subDataStar (subData : List (IRI × IRI)) (dp : IRI) : List IRI :=
  subDataLoop subData (subDataUniverse subData dp).length [dp]

theorem mem_subDataLoop_of_mem (subData : List (IRI × IRI)) (n : Nat) (cur : List IRI)
    {x : IRI} (hx : x ∈ cur) : x ∈ subDataLoop subData n cur := by
  induction n generalizing cur with
  | zero => exact hx
  | succ n ih =>
    simp only [subDataLoop]
    split
    · exact hx
    · exact ih (subDataStep subData cur) (mem_subDataStep_of_mem hx)

theorem self_mem_subDataStar (subData : List (IRI × IRI)) (dp : IRI) :
    dp ∈ subDataStar subData dp :=
  mem_subDataLoop_of_mem subData _ [dp] (List.mem_singleton_self _)

theorem subDataLoop_sound {i : Interpretation datatypeMap} {subData : List (IRI × IRI)}
    {x : i.Object} {y : i.Data}
    (hm : ∀ rs ∈ subData, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y) :
    ∀ (n : Nat) (cur : List IRI),
      (∀ r ∈ cur, i.dataProperties r x y) →
      ∀ r ∈ subDataLoop subData n cur, i.dataProperties r x y
  | 0, cur, hcur => hcur
  | n + 1, cur, hcur => by
    simp only [subDataLoop]
    split
    · exact hcur
    · apply subDataLoop_sound hm n (subDataStep subData cur)
      intro r hr
      rcases List.mem_append.mp (List.mem_eraseDups.mp hr) with h1 | h2
      · exact hcur r h1
      · obtain ⟨⟨r₀, t₀⟩, hrt, hif⟩ := List.mem_filterMap.mp h2
        simp at hif
        exact hif.2 ▸ hm (r₀, t₀) hrt (hcur r₀ hif.1)

theorem subDataStar_sound {i : Interpretation datatypeMap} {subData : List (IRI × IRI)}
    {dp : IRI} {x : i.Object} {y : i.Data}
    (hm : ∀ rs ∈ subData, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y)
    (hdp : i.dataProperties dp x y) :
    ∀ dp' ∈ subDataStar subData dp, i.dataProperties dp' x y :=
  subDataLoop_sound hm _ [dp] (fun _ hr => (List.mem_singleton.mp hr) ▸ hdp)

private theorem subDataStep_length_gt_of_not_all {subData : List (IRI × IRI)} {cur : List IRI}
    (hnd : cur.Nodup)
    (hnot : (subDataStep subData cur).all (cur.contains ·) = false) :
    cur.length < (subDataStep subData cur).length := by
  have hsub : ∀ x ∈ cur, x ∈ subDataStep subData cur := fun _ hx => mem_subDataStep_of_mem hx
  have hex : ∀ (xs : List IRI), xs.all (cur.contains ·) = false → ∃ w ∈ xs, w ∉ cur := by
    intro xs hxs
    induction xs with
    | nil => cases hxs
    | cons a tail ih =>
      rw [List.all_cons] at hxs
      cases hca : cur.contains a with
      | false =>
        exact ⟨a, List.mem_cons_self .., fun hm => by
          rw [List.contains_iff_mem.mpr hm] at hca; cases hca⟩
      | true =>
        rw [hca, Bool.true_and] at hxs
        obtain ⟨w, hw, hwn⟩ := ih hxs
        exact ⟨w, List.mem_cons_of_mem _ hw, hwn⟩
  obtain ⟨w, hw, hwn⟩ := hex (subDataStep subData cur) hnot
  have hsub2 : ∀ x ∈ w :: cur, x ∈ subDataStep subData cur := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hw
    · exact hsub x hx'
  have hnd2 : (w :: cur).Nodup := List.nodup_cons.mpr ⟨hwn, hnd⟩
  have hle2 := hnd2.length_le_of_subset hsub2
  simp at hle2
  omega

theorem subDataLoop_closed (subData : List (IRI × IRI)) (dp : IRI) :
    ∀ (n : Nat) (cur : List IRI),
      cur.Nodup →
      (∀ x ∈ cur, x ∈ subDataUniverse subData dp) →
      (subDataUniverse subData dp).length - cur.length ≤ n →
      ∀ (r t : IRI), (r, t) ∈ subData →
        r ∈ subDataLoop subData n cur → t ∈ subDataLoop subData n cur
  | 0, cur, hnd, hsub, hrem => by
    simp only [subDataLoop]
    intro r t hrt _
    have htU : t ∈ subDataUniverse subData dp :=
      List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_map_of_mem hrt))
    by_cases htc : t ∈ cur
    · exact htc
    · have hnd2 : (t :: cur).Nodup := List.nodup_cons.mpr ⟨htc, hnd⟩
      have hsub2 : ∀ x ∈ t :: cur, x ∈ subDataUniverse subData dp := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact htU
        · exact hsub x hx'
      have hle2 := hnd2.length_le_of_subset hsub2
      simp at hle2
      omega
  | n + 1, cur, hnd, hsub, hrem => by
    simp only [subDataLoop]
    split
    · rename_i hall
      intro r t hrt hr
      have htStep : t ∈ subDataStep subData cur := by
        refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
        refine List.mem_filterMap.mpr ⟨(r, t), hrt, ?_⟩
        dsimp only
        rw [List.contains_iff_mem.mpr hr]
        rfl
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hall t htStep)
    · rename_i hnot
      have hnot' : (subDataStep subData cur).all (cur.contains ·) = false :=
        Bool.eq_false_iff.mpr hnot
      have hlt := subDataStep_length_gt_of_not_all hnd hnot'
      have hndNext : (subDataStep subData cur).Nodup := nodup_eraseDups_list _
      have hsubNext := subDataStep_subset_universe hsub
      exact subDataLoop_closed subData dp n (subDataStep subData cur)
        hndNext hsubNext (by omega)

theorem subDataStar_closed (subData : List (IRI × IRI)) (dp : IRI)
    {r t : IRI} (hrt : (r, t) ∈ subData) (hr : r ∈ subDataStar subData dp) :
    t ∈ subDataStar subData dp := by
  refine subDataLoop_closed subData dp (subDataUniverse subData dp).length [dp]
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact List.mem_eraseDups.mpr (List.mem_cons_self ..))
    (by omega) r t hrt hr

/-! ### 3. Concrete Data CSP representation and solver -/

structure DataLower where
  subj : Nat
  dp : IRI
  range : DataRange
  count : Nat
  deriving DecidableEq, Repr

structure DataUpper where
  subj : Nat
  dp : IRI
  range : DataRange
  bound : Nat
  deriving DecidableEq, Repr

structure DataCSP where
  subData : List (IRI × IRI) := []
  disjointData : List (IRI × IRI) := []
  keyDisjoint : List (Nat × Nat × IRI) := []
  lowers : List DataLower := []
  uppers : List DataUpper := []
  deriving DecidableEq, Repr

def DataCSP.isSROIQD (csp : DataCSP) : Bool :=
  csp.lowers.all (fun l => l.range.isSROIQD) &&
  csp.uppers.all (fun u => u.range.isSROIQD)

structure DataCSP.Realizes (csp : DataCSP) (i : Interpretation datatypeMap)
    (env : Nat → i.Object) : Prop where
  subData : ∀ rs ∈ csp.subData, ∀ s y,
    i.dataProperties rs.1 (env s) y → i.dataProperties rs.2 (env s) y
  disjointData : ∀ rs ∈ csp.disjointData, ∀ s y,
    ¬ (i.dataProperties rs.1 (env s) y ∧ i.dataProperties rs.2 (env s) y)
  keyDisjoint : ∀ kd ∈ csp.keyDisjoint, ∀ y,
    ¬ (i.dataProperties kd.2.2 (env kd.1) y ∧ i.dataProperties kd.2.2 (env kd.2.1) y)
  lowers : ∀ l ∈ csp.lowers,
    AtLeast l.count (fun y => i.dataProperties l.dp (env l.subj) y ∧ dataHolds i y l.range)
  uppers : ∀ u ∈ csp.uppers,
    ¬ AtLeast (u.bound + 1) (fun y => i.dataProperties u.dp (env u.subj) y ∧ dataHolds i y u.range)

def DataCSP.totalDemand (csp : DataCSP) : Nat :=
  (csp.lowers.map DataLower.count).sum

def DataCSP.atoms (csp : DataCSP) : List DataRange :=
  ((csp.lowers.map DataLower.range ++ csp.uppers.map DataUpper.range).eraseDups.flatMap
    atomsOfDataRange).eraseDups

theorem DataCSP.atoms_nodup (csp : DataCSP) : csp.atoms.Nodup :=
  nodup_eraseDups_list _

theorem DataCSP.atoms_exact {csp : DataCSP} (h : csp.isSROIQD = true) :
    ∀ a ∈ csp.atoms, isExactAtomicDataRange a = true := by
  obtain ⟨hl, hu⟩ := Bool.and_eq_true_iff.mp h
  intro a ha
  obtain ⟨d, hd, had⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ha)
  rcases List.mem_append.mp (List.mem_eraseDups.mp hd) with h1 | h2
  · obtain ⟨l, hlMem, rfl⟩ := List.mem_map.mp h1
    exact atomsOfDataRange_exact (List.all_eq_true.mp hl l hlMem) a had
  · obtain ⟨u, huMem, rfl⟩ := List.mem_map.mp h2
    exact atomsOfDataRange_exact (List.all_eq_true.mp hu u huMem) a had

def DataCSP.pool (csp : DataCSP) : List Value :=
  let K := csp.totalDemand + 1
  ((prunedExactPartitions csp.atoms).flatMap fun pq => samplePartition K pq.1 pq.2).eraseDups

theorem DataCSP.pool_nodup (csp : DataCSP) : csp.pool.Nodup :=
  nodup_eraseDups_list _

abbrev DataEdge := IRI × Nat × Value

def hasDataEdge (edges : List DataEdge) (dp : IRI) (s : Nat) (v : Value) : Bool :=
  edges.contains (dp, s, v)

def qualPoolValues (pool : List Value) (edges : List DataEdge)
    (s : Nat) (dp : IRI) (d : DataRange) : List Value :=
  pool.filter fun v => hasDataEdge edges dp s v && evalDataRange d v

def checkDataAdmissible (pool : List Value) (subData : List (IRI × IRI))
    (disjointData : List (IRI × IRI)) (keyDisjoint : List (Nat × Nat × IRI))
    (uppers : List DataUpper) (edges : List DataEdge) : Bool :=
  (edges.all fun (_, _, v) => pool.contains v) &&
  (subData.all fun (r, t) =>
    edges.all fun (dp, s, v) => !(dp == r) || hasDataEdge edges t s v) &&
  (disjointData.all fun (r, t) =>
    edges.all fun (dp, s, v) => !(dp == r && hasDataEdge edges t s v)) &&
  (keyDisjoint.all fun (s₁, s₂, dp) =>
    edges.all fun (dp', s, v) => !(dp' == dp && s == s₁ && hasDataEdge edges dp s₂ v)) &&
  (uppers.all fun u =>
    decide ((qualPoolValues pool edges u.subj u.dp u.range).length ≤ u.bound))

private def checkUppersIndexed (pool : List Value) (uppers : List DataUpper)
    (edges : List DataEdge) : Bool :=
  let occupied := Std.HashSet.ofList (edges.map fun (dp, subj, _) => (dp, subj))
  uppers.all fun u =>
    !occupied.contains (u.dp, u.subj) ||
      decide ((qualPoolValues pool edges u.subj u.dp u.range).length ≤ u.bound)

private theorem checkUppersIndexed_eq (pool : List Value) (uppers : List DataUpper)
    (edges : List DataEdge) :
    checkUppersIndexed pool uppers edges = uppers.all (fun u =>
      decide ((qualPoolValues pool edges u.subj u.dp u.range).length ≤ u.bound)) := by
  unfold checkUppersIndexed
  apply List.all_congr rfl
  intro u
  simp only [Std.HashSet.contains_ofList]
  cases h : (edges.map fun (dp, subj, _) => (dp, subj)).contains (u.dp, u.subj) with
  | true => simp
  | false =>
    have hempty : qualPoolValues pool edges u.subj u.dp u.range = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro v _ hval
      have hv : (u.dp, u.subj, v) ∈ edges :=
        List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hval).1
      have hseen : (u.dp, u.subj) ∈ edges.map (fun (dp, subj, _) => (dp, subj)) :=
        List.mem_map_of_mem hv
      exact Bool.eq_false_iff.mp h (List.contains_iff_mem.mpr hseen)
    simp [hempty]

private def checkDataAdmissibleIndexed (pool : List Value) (subData : List (IRI × IRI))
    (disjointData : List (IRI × IRI)) (keyDisjoint : List (Nat × Nat × IRI))
    (uppers : List DataUpper) (edges : List DataEdge) : Bool :=
  (edges.all fun (_, _, v) => pool.contains v) &&
  (subData.all fun (r, t) =>
    edges.all fun (dp, s, v) => !(dp == r) || hasDataEdge edges t s v) &&
  (disjointData.all fun (r, t) =>
    edges.all fun (dp, s, v) => !(dp == r && hasDataEdge edges t s v)) &&
  (keyDisjoint.all fun (s₁, s₂, dp) =>
    edges.all fun (dp', s, v) => !(dp' == dp && s == s₁ && hasDataEdge edges dp s₂ v)) &&
  checkUppersIndexed pool uppers edges

@[csimp] private theorem checkDataAdmissible_eq_indexed :
    checkDataAdmissible = checkDataAdmissibleIndexed := by
  funext pool subData disjointData keyDisjoint uppers edges
  simp only [checkDataAdmissible, checkDataAdmissibleIndexed, checkUppersIndexed_eq]

def addSubDataStar (subData : List (IRI × IRI)) (dp : IRI) (s : Nat) (v : Value)
    (edges : List DataEdge) : List DataEdge :=
  ((subDataStar subData dp).map (fun dp' => (dp', s, v)) ++ edges).eraseDups

def pickForLower (subData : List (IRI × IRI)) (subj : Nat) (dp : IRI) :
    Nat → List Value → List DataEdge →
    (List DataEdge → Option (List DataEdge)) → Option (List DataEdge)
  | 0, _, edges, cont => cont edges
  | _ + 1, [], _, _ => none
  | k + 1, v :: vs, edges, cont =>
    match pickForLower subData subj dp k vs (addSubDataStar subData dp subj v edges) cont with
    | some sol => some sol
    | none => pickForLower subData subj dp (k + 1) vs edges cont

def solveLowers (pool : List Value) (subData : List (IRI × IRI))
    (disjointData : List (IRI × IRI)) (keyDisjoint : List (Nat × Nat × IRI))
    (uppers : List DataUpper) :
    List DataLower → List DataEdge → Option (List DataEdge)
  | [], edges =>
    if checkDataAdmissible pool subData disjointData keyDisjoint uppers edges then
      some edges
    else none
  | L :: rest, edges =>
    if !checkDataAdmissible pool subData disjointData keyDisjoint uppers edges then none
    else
      let haveCnt := (qualPoolValues pool edges L.subj L.dp L.range).length
      let need := L.count - haveCnt
      let cands := pool.filter fun v => !hasDataEdge edges L.dp L.subj v && evalDataRange L.range v
      pickForLower subData L.subj L.dp need cands edges
        (solveLowers pool subData disjointData keyDisjoint uppers rest)

private def literalWitness (csp : DataCSP) : List DataEdge :=
  (csp.lowers.flatMap fun lower =>
    match lower.count, lower.range with
    | 1, .oneOf [literal] =>
      match decodeLiteral literal with
      | some value =>
        (subDataStar csp.subData lower.dp).map fun dp => (dp, lower.subj, value)
      | none => []
    | _, _ => []).eraseDups

def solveDataCSP (csp : DataCSP) : Option (List DataEdge) :=
  if csp.lowers.isEmpty then some []
  else
    let pool := csp.pool
    let edges := literalWitness csp
    if checkDataAdmissible pool csp.subData csp.disjointData csp.keyDisjoint csp.uppers edges &&
        csp.lowers.all (fun lower =>
          decide (lower.count ≤ (qualPoolValues pool edges lower.subj lower.dp lower.range).length)) then
      some edges
    else solveLowers pool csp.subData csp.disjointData csp.keyDisjoint csp.uppers csp.lowers []

/-! ### 4. Soundness of `solveDataCSP` -/

theorem mem_addSubDataStar {subData : List (IRI × IRI)} {dp : IRI} {s : Nat} {v : Value}
    {edges : List DataEdge} {e : DataEdge} :
    e ∈ addSubDataStar subData dp s v edges ↔
      (∃ dp' ∈ subDataStar subData dp, e = (dp', s, v)) ∨ e ∈ edges := by
  simp only [addSubDataStar, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact or_congr ⟨fun ⟨dp', h, he⟩ => ⟨dp', h, he.symm⟩,
                  fun ⟨dp', h, he⟩ => ⟨dp', h, he.symm⟩⟩ Iff.rfl

theorem subset_addSubDataStar (subData : List (IRI × IRI)) (dp : IRI) (s : Nat) (v : Value)
    (edges : List DataEdge) :
    ∀ e ∈ edges, e ∈ addSubDataStar subData dp s v edges :=
  fun _ he => mem_addSubDataStar.mpr (.inr he)

theorem self_mem_addSubDataStar (subData : List (IRI × IRI)) (dp : IRI) (s : Nat) (v : Value)
    (edges : List DataEdge) :
    (dp, s, v) ∈ addSubDataStar subData dp s v edges :=
  mem_addSubDataStar.mpr (.inl ⟨dp, self_mem_subDataStar subData dp, rfl⟩)

theorem qualPoolValues_subset_of_subset (pool : List Value)
    {edges₁ edges₂ : List DataEdge} (hsub : ∀ e ∈ edges₁, e ∈ edges₂)
    (s : Nat) (dp : IRI) (d : DataRange) :
    ∀ v ∈ qualPoolValues pool edges₁ s dp d, v ∈ qualPoolValues pool edges₂ s dp d := by
  intro v hv
  obtain ⟨hp, hcond⟩ := List.mem_filter.mp hv
  obtain ⟨he, hd⟩ := Bool.and_eq_true_iff.mp hcond
  have he' : hasDataEdge edges₂ dp s v = true :=
    List.contains_iff_mem.mpr (hsub _ (List.contains_iff_mem.mp he))
  exact List.mem_filter.mpr ⟨hp, Bool.and_eq_true_iff.mpr ⟨he', hd⟩⟩

private theorem nodup_append_of_disjoint {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ x ∈ xs, x ∉ ys) :
    (xs ++ ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons a tail ih =>
    obtain ⟨hna, hndTail⟩ := List.nodup_cons.mp hx
    refine List.nodup_cons.mpr ⟨?_, ih hndTail (fun x hx' => hd x (List.mem_cons_of_mem _ hx'))⟩
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hna h1
    · exact hd a (List.mem_cons_self ..) h2

theorem pickForLower_spec {subData : List (IRI × IRI)} {subj : Nat} {dp : IRI}
    {P : List DataEdge → Prop} :
    ∀ (k : Nat) (cands : List Value) (edges : List DataEdge)
      (cont : List DataEdge → Option (List DataEdge))
      (sol : List DataEdge),
      (∀ e' s', cont e' = some s' → (∀ e ∈ e', e ∈ s') ∧ P s') →
      pickForLower subData subj dp k cands edges cont = some sol →
      (∀ e ∈ edges, e ∈ sol) ∧ P sol ∧
      ∃ chosen : List Value, chosen.Sublist cands ∧ chosen.length = k ∧
        ∀ v ∈ chosen, (dp, subj, v) ∈ sol
  | 0, cands, edges, cont, sol, hcont, hpick => by
    simp only [pickForLower] at hpick
    obtain ⟨hsub, hp⟩ := hcont edges sol hpick
    exact ⟨hsub, hp, [], List.nil_sublist cands, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | _ + 1, [], _, _, _, _, hpick => by cases hpick
  | k + 1, v :: vs, edges, cont, sol, hcont, hpick => by
    simp only [pickForLower] at hpick
    split at hpick
    · rename_i sol' h1
      cases hpick
      obtain ⟨hsub1, hp1, chosen, hchSub, hchLen, hchMem⟩ :=
        pickForLower_spec k vs (addSubDataStar subData dp subj v edges) cont sol hcont h1
      refine ⟨fun e he => hsub1 e (subset_addSubDataStar _ _ _ _ _ e he), hp1,
        v :: chosen, List.Sublist.cons_cons v hchSub, by simp [hchLen], ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hsub1 _ (self_mem_addSubDataStar _ _ _ _ _)
      · exact hchMem w hw'
    · obtain ⟨hsub2, hp2, chosen, hchSub, hchLen, hchMem⟩ :=
        pickForLower_spec (k + 1) vs edges cont sol hcont hpick
      exact ⟨hsub2, hp2, chosen, List.Sublist.cons v hchSub, hchLen, hchMem⟩

theorem solveLowers_spec (pool : List Value) (subData : List (IRI × IRI))
    (disjointData : List (IRI × IRI)) (keyDisjoint : List (Nat × Nat × IRI))
    (uppers : List DataUpper) (hpnd : pool.Nodup) :
    ∀ (lowers : List DataLower) (edges sol : List DataEdge),
      solveLowers pool subData disjointData keyDisjoint uppers lowers edges = some sol →
      (∀ e ∈ edges, e ∈ sol) ∧
      checkDataAdmissible pool subData disjointData keyDisjoint uppers sol = true ∧
      (∀ L ∈ lowers, L.count ≤ (qualPoolValues pool sol L.subj L.dp L.range).length)
  | [], edges, sol, hsol => by
    simp only [solveLowers] at hsol
    split at hsol
    · rename_i hadm
      cases hsol
      exact ⟨fun _ h => h, hadm, fun _ h => (List.not_mem_nil h).elim⟩
    · cases hsol
  | L :: rest, edges, sol, hsol => by
    simp only [solveLowers] at hsol
    split at hsol
    · cases hsol
    · let P (s : List DataEdge) : Prop :=
        checkDataAdmissible pool subData disjointData keyDisjoint uppers s = true ∧
        ∀ L' ∈ rest, L'.count ≤ (qualPoolValues pool s L'.subj L'.dp L'.range).length
      have hcont : ∀ e' s',
          solveLowers pool subData disjointData keyDisjoint uppers rest e' = some s' →
          (∀ e ∈ e', e ∈ s') ∧ P s' := by
        intro e' s' hs'
        obtain ⟨h1, h2, h3⟩ := solveLowers_spec pool subData disjointData keyDisjoint uppers hpnd rest e' s' hs'
        exact ⟨h1, h2, h3⟩
      obtain ⟨hsub, ⟨hadm, hrest⟩, chosen, hchSub, hchLen, hchMem⟩ :=
        pickForLower_spec
          (L.count - (qualPoolValues pool edges L.subj L.dp L.range).length)
          (pool.filter fun v => !hasDataEdge edges L.dp L.subj v && evalDataRange L.range v)
          edges
          (solveLowers pool subData disjointData keyDisjoint uppers rest)
          sol hcont hsol
      refine ⟨hsub, hadm, ?_⟩
      intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · have holdNodup : (qualPoolValues pool edges L'.subj L'.dp L'.range).Nodup :=
          List.filter_sublist.nodup hpnd
        have hchNodup : chosen.Nodup :=
          hchSub.nodup (List.filter_sublist.nodup hpnd)
        have hdisj : ∀ v ∈ chosen, v ∉ qualPoolValues pool edges L'.subj L'.dp L'.range := by
          intro v hv hold
          have hcand := hchSub.subset hv
          obtain ⟨_, hc⟩ := List.mem_filter.mp hcand
          obtain ⟨hnotEdge, _⟩ := Bool.and_eq_true_iff.mp hc
          obtain ⟨_, ho⟩ := List.mem_filter.mp hold
          obtain ⟨hhasEdge, _⟩ := Bool.and_eq_true_iff.mp ho
          rw [hhasEdge] at hnotEdge; cases hnotEdge
        have hcombNodup : (chosen ++ qualPoolValues pool edges L'.subj L'.dp L'.range).Nodup :=
          nodup_append_of_disjoint hchNodup holdNodup hdisj
        have hcombSub : ∀ v ∈ chosen ++ qualPoolValues pool edges L'.subj L'.dp L'.range,
            v ∈ qualPoolValues pool sol L'.subj L'.dp L'.range := by
          intro v hv
          rcases List.mem_append.mp hv with h1 | h2
          · have hcand := hchSub.subset h1
            obtain ⟨hvp, hc⟩ := List.mem_filter.mp hcand
            obtain ⟨_, hd⟩ := Bool.and_eq_true_iff.mp hc
            have hedgeSol := hchMem v h1
            exact List.mem_filter.mpr ⟨hvp, Bool.and_eq_true_iff.mpr
              ⟨List.contains_iff_mem.mpr hedgeSol, hd⟩⟩
          · exact qualPoolValues_subset_of_subset pool hsub L'.subj L'.dp L'.range v h2
        have hle := hcombNodup.length_le_of_subset hcombSub
        rw [List.length_append, hchLen] at hle
        omega
      · exact hrest L' hL'

theorem solveDataCSP_sound {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) :
    checkDataAdmissible csp.pool csp.subData csp.disjointData csp.keyDisjoint csp.uppers sol = true ∧
    (∀ L ∈ csp.lowers, L.count ≤ (qualPoolValues csp.pool sol L.subj L.dp L.range).length) := by
  simp only [solveDataCSP] at hsol
  split at hsol
  · rename_i hempty
    obtain rfl := Option.some.inj hsol
    have noValues : csp.pool.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
    simp [List.isEmpty_iff.mp hempty, checkDataAdmissible, qualPoolValues, hasDataEdge, noValues]
  · split at hsol
    · rename_i hvalid
      obtain rfl := (Option.some.inj hsol).symm
      have ⟨hadm, hlower⟩ := Bool.and_eq_true_iff.mp hvalid
      exact ⟨hadm, fun lower hmem => of_decide_eq_true (List.all_eq_true.mp hlower lower hmem)⟩
    · obtain ⟨_, hadm, hlow⟩ := solveLowers_spec csp.pool csp.subData csp.disjointData
        csp.keyDisjoint csp.uppers csp.pool_nodup csp.lowers [] sol hsol
      exact ⟨hadm, hlow⟩

/-- Any interpretation `i` whose data-property edges on the subjects of `csp`
agree with `sol` satisfies `csp.Realizes i env`. -/
theorem solveDataCSP_realizes {csp : DataCSP} {sol : List DataEdge}
    (hcsp : csp.isSROIQD = true) (hsol : solveDataCSP csp = some sol)
    (i : Interpretation datatypeMap) (env : Nat → i.Object)
    (hedges : ∀ (dp : IRI) (s : Nat) (y : i.Data),
      (dp ∈ csp.subData.map Prod.fst ∨ dp ∈ csp.subData.map Prod.snd ∨
       dp ∈ csp.disjointData.map Prod.fst ∨ dp ∈ csp.disjointData.map Prod.snd ∨
       dp ∈ csp.keyDisjoint.map (fun q => q.2.2) ∨
       dp ∈ csp.lowers.map DataLower.dp ∨ dp ∈ csp.uppers.map DataUpper.dp) →
      (i.dataProperties dp (env s) y ↔ ∃ v : Value, y = i.embedValue v ∧ (dp, s, v) ∈ sol)) :
    csp.Realizes i env := by
  obtain ⟨hadm, hlow⟩ := solveDataCSP_sound hsol
  obtain ⟨hlSROIQD, huSROIQD⟩ := Bool.and_eq_true_iff.mp hcsp
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨⟨hpool, hsubD⟩, hdisjD⟩, hkeyD⟩, hupD⟩ := hadm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨r, t⟩ hrt s y hry
    have hrIn : r ∈ csp.subData.map Prod.fst := List.mem_map_of_mem hrt
    have htIn : t ∈ csp.subData.map Prod.snd := List.mem_map_of_mem hrt
    obtain ⟨v, rfl, hrv⟩ := (hedges r s y (.inl hrIn)).mp hry
    have hstep := hsubD (r, t) hrt (r, s, v) hrv
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, hasDataEdge,
      List.contains_iff_mem] at hstep
    exact (hedges t s (i.embedValue v) (.inr (.inl htIn))).mpr ⟨v, rfl, hstep⟩
  · intro ⟨r, t⟩ hrt s y ⟨hry, hty⟩
    have hrIn : r ∈ csp.disjointData.map Prod.fst := List.mem_map_of_mem hrt
    have htIn : t ∈ csp.disjointData.map Prod.snd := List.mem_map_of_mem hrt
    obtain ⟨v₁, hy₁, hrv⟩ := (hedges r s y (.inr (.inr (.inl hrIn)))).mp hry
    obtain ⟨v₂, hy₂, htv⟩ := (hedges t s y (.inr (.inr (.inr (.inl htIn))))).mp hty
    have hveq : v₁ = v₂ := i.embedValue_injective (hy₁.symm.trans hy₂)
    subst hveq
    have hstep := hdisjD (r, t) hrt (r, s, v₁) hrv
    have hhas : hasDataEdge sol t s v₁ = true := List.contains_iff_mem.mpr htv
    simp [hhas] at hstep
  · intro ⟨s₁, s₂, dp⟩ hkd y ⟨hy₁, hy₂⟩
    have hdpIn : dp ∈ csp.keyDisjoint.map (fun q => q.2.2) := List.mem_map_of_mem hkd
    obtain ⟨v₁, he₁, h₁⟩ := (hedges dp s₁ y (.inr (.inr (.inr (.inr (.inl hdpIn)))))).mp hy₁
    obtain ⟨v₂, he₂, h₂⟩ := (hedges dp s₂ y (.inr (.inr (.inr (.inr (.inl hdpIn)))))).mp hy₂
    have hveq : v₁ = v₂ := i.embedValue_injective (he₁.symm.trans he₂)
    subst hveq
    have hstep := hkeyD (s₁, s₂, dp) hkd (dp, s₁, v₁) h₁
    have hhas : hasDataEdge sol dp s₂ v₁ = true := List.contains_iff_mem.mpr h₂
    simp [hhas] at hstep
  · intro l hl
    have hlen := hlow l hl
    let embed : Value → i.Data := i.embedValue
    let qs := qualPoolValues csp.pool sol l.subj l.dp l.range
    have hqnd : qs.Nodup := List.filter_sublist.nodup csp.pool_nodup
    have hdpIn : l.dp ∈ csp.lowers.map DataLower.dp := List.mem_map_of_mem hl
    have hdOk : l.range.isSROIQD = true := List.all_eq_true.mp hlSROIQD l hl
    refine ⟨(qs.take l.count).map embed,
      (List.length_map embed).trans (List.length_take_of_le hlen),
      nodup_map_inj i.embedValue_injective ((List.take_sublist ..).nodup hqnd), ?_⟩
    intro y hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    have hv' := List.mem_of_mem_take hv
    obtain ⟨_, hcond⟩ := List.mem_filter.mp hv'
    obtain ⟨he, hd⟩ := Bool.and_eq_true_iff.mp hcond
    exact ⟨(hedges l.dp l.subj (i.embedValue v)
        (.inr (.inr (.inr (.inr (.inr (.inl hdpIn))))))).mpr
        ⟨v, rfl, List.contains_iff_mem.mp he⟩,
      (evalDataRange_iff hdOk i v).mp hd⟩
  · intro u hu ⟨ys, hlen, hnd, hq⟩
    have hbound := hupD u hu
    let embed : Value → i.Data := i.embedValue
    have hdpIn : u.dp ∈ csp.uppers.map DataUpper.dp := List.mem_map_of_mem hu
    have hdOk : u.range.isSROIQD = true := List.all_eq_true.mp huSROIQD u hu
    let qs := qualPoolValues csp.pool sol u.subj u.dp u.range
    have hsub : ∀ y ∈ ys, y ∈ qs.map embed := by
      intro y hy
      obtain ⟨hdpY, hdY⟩ := hq y hy
      obtain ⟨v, rfl, hvSol⟩ := (hedges u.dp u.subj y
        (.inr (.inr (.inr (.inr (.inr (.inr hdpIn))))))).mp hdpY
      have hvPool : v ∈ csp.pool := List.contains_iff_mem.mp (hpool (u.dp, u.subj, v) hvSol)
      have hvEval : evalDataRange u.range v = true := (evalDataRange_iff hdOk i v).mpr hdY
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hvPool, Bool.and_eq_true_iff.mpr
        ⟨List.contains_iff_mem.mpr hvSol, hvEval⟩⟩)
    have hle := hnd.length_le_of_subset hsub
    have hmapLen : (qs.map embed).length = (qualPoolValues csp.pool sol u.subj u.dp u.range).length :=
      List.length_map embed
    omega

/-! ### 5. Completeness of `solveDataCSP` -/

def targetDiff (pool : List Value) (target edges : List DataEdge)
    (s : Nat) (dp : IRI) (d : DataRange) : List Value :=
  pool.filter fun v => hasDataEdge target dp s v && !hasDataEdge edges dp s v && evalDataRange d v

theorem targetDiff_sublist_cands (pool : List Value) (target edges : List DataEdge)
    (s : Nat) (dp : IRI) (d : DataRange) :
    (targetDiff pool target edges s dp d).Sublist
      (pool.filter fun v => !hasDataEdge edges dp s v && evalDataRange d v) := by
  have haux : ∀ (xs : List Value) (p q : Value → Bool),
      (∀ v, p v = true → q v = true) → (xs.filter p).Sublist (xs.filter q) := by
    intro xs p q hpq
    induction xs with
    | nil => exact List.Sublist.slnil
    | cons a tail ih =>
      simp only [List.filter]
      cases hp : p a with
      | false =>
        cases hq : q a
        · exact ih
        · exact List.Sublist.cons a ih
      | true =>
        rw [hpq a hp]
        exact List.Sublist.cons_cons a ih
  exact haux pool _ _ fun v hv => by
    obtain ⟨⟨_, hne⟩, hd⟩ := Bool.and_eq_true_iff.mp hv |>.imp_left Bool.and_eq_true_iff.mp
    exact Bool.and_eq_true_iff.mpr ⟨hne, hd⟩

theorem qualPoolValues_target_length_eq (pool : List Value)
    {target edges : List DataEdge} (hsub : ∀ e ∈ edges, e ∈ target)
    (s : Nat) (dp : IRI) (d : DataRange) :
    (qualPoolValues pool target s dp d).length =
      (targetDiff pool target edges s dp d).length +
      (qualPoolValues pool edges s dp d).length := by
  unfold qualPoolValues targetDiff
  induction pool with
  | nil => rfl
  | cons v vs ih =>
    have himp : hasDataEdge edges dp s v = true → hasDataEdge target dp s v = true :=
      fun h => List.contains_iff_mem.mpr (hsub _ (List.contains_iff_mem.mp h))
    simp only [List.filter]
    cases he : hasDataEdge edges dp s v with
    | false =>
      cases ht : hasDataEdge target dp s v <;> cases hd : evalDataRange d v <;>
        simp [ih] <;> omega
    | true =>
      rw [himp he]
      cases hd : evalDataRange d v <;> simp [ih] <;> omega

def foldAddStar (subData : List (IRI × IRI)) (subj : Nat) (dp : IRI) :
    List Value → List DataEdge → List DataEdge
  | [], edges => edges
  | v :: vs, edges => foldAddStar subData subj dp vs (addSubDataStar subData dp subj v edges)

theorem pickForLower_isSome_of_sublist (subData : List (IRI × IRI)) (subj : Nat) (dp : IRI)
    {chosen cands : List Value} (hsub : chosen.Sublist cands)
    (edges : List DataEdge) (cont : List DataEdge → Option (List DataEdge))
    (hcont : (cont (foldAddStar subData subj dp chosen edges)).isSome = true) :
    (pickForLower subData subj dp chosen.length cands edges cont).isSome = true := by
  induction hsub generalizing edges with
  | slnil => exact hcont
  | @cons l₁ l₂ a _ ih =>
    cases l₁ with
    | nil => exact hcont
    | cons w ws =>
      simp only [List.length_cons, pickForLower]
      split
      · rfl
      · exact ih edges hcont
  | cons_cons a _ ih =>
    simp only [List.length_cons, pickForLower, foldAddStar] at hcont ⊢
    split
    · rfl
    · rename_i hnone
      have his := ih (addSubDataStar subData dp subj a edges) hcont
      rw [hnone] at his; cases his

def EdgesSubClosed (subData : List (IRI × IRI)) (edges : List DataEdge) : Prop :=
  ∀ r t, (r, t) ∈ subData → ∀ s v, (r, s, v) ∈ edges → (t, s, v) ∈ edges

theorem addSubDataStar_subClosed {subData : List (IRI × IRI)} {dp : IRI} {s : Nat} {v : Value}
    {edges : List DataEdge} (hclosed : EdgesSubClosed subData edges) :
    EdgesSubClosed subData (addSubDataStar subData dp s v edges) := by
  intro r t hrt s' v' hmem
  rcases mem_addSubDataStar.mp hmem with ⟨dp', hdp', heq⟩ | hold
  · obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    exact mem_addSubDataStar.mpr (.inl ⟨t, subDataStar_closed subData dp hrt hdp', rfl⟩)
  · exact mem_addSubDataStar.mpr (.inr (hclosed r t hrt s' v' hold))

theorem addSubDataStar_subset_of_closed {subData : List (IRI × IRI)} {dp : IRI} {s : Nat} {v : Value}
    {edges target : List DataEdge} (hsub : ∀ e ∈ edges, e ∈ target)
    (htClosed : EdgesSubClosed subData target)
    (hseed : (dp, s, v) ∈ target) :
    ∀ e ∈ addSubDataStar subData dp s v edges, e ∈ target := by
  intro e he
  rcases mem_addSubDataStar.mp he with ⟨dp', hdp', rfl⟩ | hold
  · have hloop : ∀ (n : Nat) (cur : List IRI),
        (∀ r ∈ cur, (r, s, v) ∈ target) →
        ∀ r ∈ subDataLoop subData n cur, (r, s, v) ∈ target := by
      intro n
      induction n with
      | zero => intro _ h; exact h
      | succ n ih =>
        intro cur hcur
        simp only [subDataLoop]
        split
        · exact hcur
        · refine ih (subDataStep subData cur) fun r hr => ?_
          rcases List.mem_append.mp (List.mem_eraseDups.mp hr) with h1 | h2
          · exact hcur r h1
          · obtain ⟨⟨r₀, t₀⟩, hrt, hif⟩ := List.mem_filterMap.mp h2
            simp at hif
            exact hif.2 ▸ htClosed r₀ t₀ hrt s v (hcur r₀ hif.1)
    exact hloop _ [dp] (fun r hr => (List.mem_singleton.mp hr) ▸ hseed) dp' hdp'
  · exact hsub e hold

theorem foldAddStar_preserves {subData : List (IRI × IRI)} {subj : Nat} {dp : IRI}
    {target : List DataEdge} (htClosed : EdgesSubClosed subData target) :
    ∀ (chosen : List Value) (edges : List DataEdge),
      (∀ v ∈ chosen, (dp, subj, v) ∈ target) →
      (∀ e ∈ edges, e ∈ target) →
      EdgesSubClosed subData edges →
      (∀ e ∈ foldAddStar subData subj dp chosen edges, e ∈ target) ∧
      EdgesSubClosed subData (foldAddStar subData subj dp chosen edges)
  | [], _edges, _, hsub, hcl => ⟨hsub, hcl⟩
  | v :: vs, edges, hch, hsub, hcl =>
    foldAddStar_preserves htClosed vs (addSubDataStar subData dp subj v edges)
      (fun w hw => hch w (List.mem_cons_of_mem _ hw))
      (addSubDataStar_subset_of_closed hsub htClosed (hch v (List.mem_cons_self ..)))
      (addSubDataStar_subClosed hcl)

theorem checkDataAdmissible_of_subset {pool : List Value} {subData : List (IRI × IRI)}
    {disjointData : List (IRI × IRI)} {keyDisjoint : List (Nat × Nat × IRI)}
    {uppers : List DataUpper} {edges target : List DataEdge}
    (hpnd : pool.Nodup)
    (hadmT : checkDataAdmissible pool subData disjointData keyDisjoint uppers target = true)
    (hsub : ∀ e ∈ edges, e ∈ target)
    (hclosed : EdgesSubClosed subData edges) :
    checkDataAdmissible pool subData disjointData keyDisjoint uppers edges = true := by
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hadmT ⊢
  obtain ⟨⟨⟨⟨hpool, _⟩, hdisj⟩, hkey⟩, hup⟩ := hadmT
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro e he; exact hpool e (hsub e he)
  · intro ⟨r, t⟩ hrt ⟨dp, s, v⟩ he
    by_cases hdp : dp = r
    · subst hdp
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, hasDataEdge,
        List.contains_iff_mem]
      exact hclosed dp t hrt s v he
    · simp [beq_false_of_ne hdp]
  · intro ⟨r, t⟩ hrt ⟨dp, s, v⟩ he
    have ht := hdisj (r, t) hrt (dp, s, v) (hsub _ he)
    by_cases hdp : dp = r
    · subst hdp
      cases hte : hasDataEdge edges t s v with
      | false => simp
      | true =>
        have htt : hasDataEdge target t s v = true :=
          List.contains_iff_mem.mpr (hsub _ (List.contains_iff_mem.mp hte))
        simp [htt] at ht
    · simp [beq_false_of_ne hdp]
  · intro ⟨s₁, s₂, dp⟩ hkd ⟨dp', s, v⟩ he
    have ht := hkey (s₁, s₂, dp) hkd (dp', s, v) (hsub _ he)
    by_cases hcond : dp' = dp ∧ s = s₁
    · rcases hcond with ⟨rfl, rfl⟩
      cases h2 : hasDataEdge edges dp' s₂ v with
      | false => simp
      | true =>
        have htt : hasDataEdge target dp' s₂ v = true :=
          List.contains_iff_mem.mpr (hsub _ (List.contains_iff_mem.mp h2))
        simp [htt] at ht
    · cases h1 : (dp' == dp && s == s₁) with
      | false => rfl
      | true =>
        obtain ⟨hd1, hs1⟩ := Bool.and_eq_true_iff.mp h1
        exact (hcond ⟨beq_iff_eq.mp hd1, beq_iff_eq.mp hs1⟩).elim
  · intro u hu
    have hsubQ := qualPoolValues_subset_of_subset pool hsub u.subj u.dp u.range
    have hle : (qualPoolValues pool edges u.subj u.dp u.range).length ≤
        (qualPoolValues pool target u.subj u.dp u.range).length :=
      (List.filter_sublist.nodup hpnd).length_le_of_subset hsubQ
    have htu := hup u hu
    omega

theorem solveLowers_isSome_of_target {pool : List Value} {subData : List (IRI × IRI)}
    {disjointData : List (IRI × IRI)} {keyDisjoint : List (Nat × Nat × IRI)}
    {uppers : List DataUpper} {target : List DataEdge}
    (hpnd : pool.Nodup)
    (hadmT : checkDataAdmissible pool subData disjointData keyDisjoint uppers target = true)
    (htClosed : EdgesSubClosed subData target) :
    ∀ (lowers : List DataLower) (edges : List DataEdge),
      (∀ L ∈ lowers, L.count ≤ (qualPoolValues pool target L.subj L.dp L.range).length) →
      (∀ e ∈ edges, e ∈ target) →
      EdgesSubClosed subData edges →
      (solveLowers pool subData disjointData keyDisjoint uppers lowers edges).isSome = true
  | [], edges, _, hsub, hcl => by
    simp only [solveLowers, checkDataAdmissible_of_subset hpnd hadmT hsub hcl, ↓reduceIte]
    rfl
  | L :: rest, edges, hlow, hsub, hcl => by
    have hadmE := checkDataAdmissible_of_subset hpnd hadmT hsub hcl
    simp only [solveLowers, hadmE, Bool.not_true]
    have hlenEq := qualPoolValues_target_length_eq pool hsub L.subj L.dp L.range
    have hL := hlow L (List.mem_cons_self ..)
    have hneedLe : L.count - (qualPoolValues pool edges L.subj L.dp L.range).length ≤
        (targetDiff pool target edges L.subj L.dp L.range).length := by omega
    let need := L.count - (qualPoolValues pool edges L.subj L.dp L.range).length
    let diff := targetDiff pool target edges L.subj L.dp L.range
    let chosen := diff.take need
    have hchLen : chosen.length = L.count - (qualPoolValues pool edges L.subj L.dp L.range).length :=
      List.length_take_of_le hneedLe
    have hchSub : chosen.Sublist (pool.filter fun v => !hasDataEdge edges L.dp L.subj v && evalDataRange L.range v) :=
      (List.take_sublist need diff).trans (targetDiff_sublist_cands pool target edges L.subj L.dp L.range)
    have hchTarget : ∀ v ∈ chosen, (L.dp, L.subj, v) ∈ target := by
      intro v hv
      have hvd := List.mem_of_mem_take hv
      obtain ⟨_, hc⟩ := List.mem_filter.mp hvd
      obtain ⟨⟨ht, _⟩, _⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left Bool.and_eq_true_iff.mp
      exact List.contains_iff_mem.mp ht
    obtain ⟨hsub', hcl'⟩ := foldAddStar_preserves htClosed chosen edges hchTarget hsub hcl
    have hcont := solveLowers_isSome_of_target hpnd hadmT htClosed rest
      (foldAddStar subData L.subj L.dp chosen edges)
      (fun L' hL' => hlow L' (List.mem_cons_of_mem _ hL'))
      hsub' hcl'
    change (pickForLower subData L.subj L.dp
      (L.count - (qualPoolValues pool edges L.subj L.dp L.range).length)
      (pool.filter fun v => !hasDataEdge edges L.dp L.subj v && evalDataRange L.range v)
      edges (solveLowers pool subData disjointData keyDisjoint uppers rest)).isSome = true
    rw [← hchLen]
    exact pickForLower_isSome_of_sublist subData L.subj L.dp hchSub edges _ hcont

/-! ### 6. Witness projection into `csp.pool` and `solveDataCSP_complete` -/

private def dedupClassical {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: xs =>
    let rest := dedupClassical xs
    if a ∈ rest then rest else a :: rest

private theorem mem_dedupClassical {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    x ∈ dedupClassical xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    simp only [dedupClassical]
    split
    · rename_i hm
      simp only [ih, List.mem_cons]
      exact ⟨fun h => .inr h, fun h => h.elim (fun he => ih.mp (he ▸ hm)) id⟩
    · simp only [List.mem_cons, ih]

private theorem dedupClassical_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (dedupClassical xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tail ih =>
    simp only [dedupClassical]
    split
    · exact ih
    · rename_i hnot
      exact List.nodup_cons.mpr ⟨hnot, ih⟩

private theorem dedupClassical_length_le {α : Type} [DecidableEq α] (xs : List α) :
    (dedupClassical xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a tail ih =>
    simp only [dedupClassical]
    split <;> simp <;> omega

private theorem collectLowerWitnesses {i : Interpretation datatypeMap} {env : Nat → i.Object}
    (ls : List DataLower)
    (hlow : ∀ l ∈ ls, AtLeast l.count (fun y => i.dataProperties l.dp (env l.subj) y ∧ dataHolds i y l.range)) :
    ∃ W : List i.Data,
      W.Nodup ∧
      W.length ≤ (ls.map DataLower.count).sum ∧
      ∀ l ∈ ls, ∃ xs : List i.Data,
        xs.length = l.count ∧ xs.Nodup ∧
        (∀ y ∈ xs, y ∈ W) ∧
        (∀ y ∈ xs, i.dataProperties l.dp (env l.subj) y ∧ dataHolds i y l.range) := by
  classical
  induction ls with
  | nil =>
    exact ⟨[], List.nodup_nil, Nat.le_refl 0, fun _ h => (List.not_mem_nil h).elim⟩
  | cons L rest ih =>
    obtain ⟨W_rest, hndR, hlenR, hwitR⟩ := ih (fun l hl => hlow l (List.mem_cons_of_mem _ hl))
    obtain ⟨xs_L, hlenL, hndL, hqL⟩ := hlow L (List.mem_cons_self ..)
    have hlenW : (dedupClassical (xs_L ++ W_rest)).length ≤ ((L :: rest).map DataLower.count).sum := by
      have h1 := dedupClassical_length_le (xs_L ++ W_rest)
      rw [List.length_append, hlenL] at h1
      simp only [List.map_cons, List.sum_cons]
      omega
    refine ⟨dedupClassical (xs_L ++ W_rest), dedupClassical_nodup _, hlenW, ?_⟩
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · refine ⟨xs_L, hlenL, hndL, fun y hy => ?_, hqL⟩
      exact (mem_dedupClassical _ _).mpr (List.mem_append_left _ hy)
    · obtain ⟨xs, h1, h2, h3, h4⟩ := hwitR l hl'
      refine ⟨xs, h1, h2, fun y hy => ?_, h4⟩
      exact (mem_dedupClassical _ _).mpr (List.mem_append_right _ (h3 y hy))

private def nthVal : List Value → Nat → Value
  | [], _ => .boolean false
  | v :: _, 0 => v
  | _ :: vs, n + 1 => nthVal vs n

private theorem nthVal_mem {vs : List Value} {k : Nat} (hk : k < vs.length) :
    nthVal vs k ∈ vs := by
  induction vs generalizing k with
  | nil => simp at hk
  | cons v tail ih =>
    cases k with
    | zero => exact List.mem_cons_self ..
    | succ k =>
      exact List.mem_cons_of_mem _ (ih (Nat.lt_of_succ_lt_succ hk))

private theorem nthVal_inj {vs : List Value} (hnd : vs.Nodup) {k₁ k₂ : Nat}
    (h₁ : k₁ < vs.length) (h₂ : k₂ < vs.length)
    (heq : nthVal vs k₁ = nthVal vs k₂) : k₁ = k₂ := by
  induction vs generalizing k₁ k₂ with
  | nil => simp at h₁
  | cons v tail ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    cases k₁ with
    | zero =>
      cases k₂ with
      | zero => rfl
      | succ k₂ =>
        simp only [nthVal] at heq
        exact (hnot (heq ▸ nthVal_mem (Nat.lt_of_succ_lt_succ h₂))).elim
    | succ k₁ =>
      cases k₂ with
      | zero =>
        simp only [nthVal] at heq
        exact (hnot (heq.symm ▸ nthVal_mem (Nat.lt_of_succ_lt_succ h₁))).elim
      | succ k₂ =>
        exact congrArg Nat.succ (ih hnd' (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂) heq)

private def indexIn {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | a :: as, x => if x = a then 0 else indexIn as x + 1

private theorem indexIn_lt_of_mem {α : Type} [DecidableEq α] {xs : List α} {x : α}
    (hx : x ∈ xs) : indexIn xs x < xs.length := by
  induction xs with
  | nil => cases hx
  | cons a tail ih =>
    simp only [indexIn, List.length_cons]
    by_cases h : x = a
    · simp [h]
    · simp only [h, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact (h rfl).elim
      · exact Nat.succ_lt_succ (ih hx')

private theorem indexIn_inj {α : Type} [DecidableEq α] {xs : List α} {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (heq : indexIn xs x = indexIn xs y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a tail ih =>
    simp only [indexIn] at heq
    by_cases hxa : x = a <;> by_cases hya : y = a
    · exact hxa.trans hya.symm
    · simp [hxa, hya] at heq
    · simp [hxa, hya] at heq
    · simp only [hxa, hya, ↓reduceIte] at heq
      have hx' : x ∈ tail := (List.mem_cons.mp hx).resolve_left hxa
      have hy' : y ∈ tail := (List.mem_cons.mp hy).resolve_left hya
      exact ih hx' hy' (Nat.succ.inj heq)

private theorem find?_eq_some_of_unique {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (ha : a ∈ xs) (hpa : p a = true)
    (huniq : ∀ b ∈ xs, p b = true → b = a) :
    xs.find? p = some a := by
  induction xs with
  | nil => cases ha
  | cons x tail ih =>
    simp only [List.find?]
    cases hpx : p x with
    | true => rw [huniq x (List.mem_cons_self ..) hpx]
    | false =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [hpa] at hpx; cases hpx
      · exact ih ha' (fun b hb hpb => huniq b (List.mem_cons_of_mem _ hb) hpb)

theorem solveDataCSP_complete {csp : DataCSP} (hcsp : csp.isSROIQD = true)
    {i : Interpretation datatypeMap} {env : Nat → i.Object}
    (hreal : csp.Realizes i env) :
    (solveDataCSP csp).isSome = true := by
  classical
  obtain ⟨hlSROIQD, huSROIQD⟩ := Bool.and_eq_true_iff.mp hcsp
  obtain ⟨W, hWnd, hWlen, hWwit⟩ := collectLowerWitnesses csp.lowers hreal.lowers
  let K := csp.totalDemand + 1
  have hWltK : W.length < K := by
    change W.length < csp.totalDemand + 1
    unfold DataCSP.totalDemand
    omega
  let partPred (y : i.Data) (pq : List DataRange × List DataRange) : Bool :=
    decide (dataHolds i y (partitionRange pq.1 pq.2))
  let W_part (pq : List DataRange × List DataRange) : List i.Data :=
    W.filter (fun y => partPred y pq)
  let S_part (pq : List DataRange × List DataRange) : List Value :=
    samplePartition K pq.1 pq.2
  have hpartExact (pq : List DataRange × List DataRange)
      (hpq : pq ∈ prunedExactPartitions csp.atoms) :
      (∀ a ∈ pq.1, isExactAtomicDataRange a = true) ∧
      (∀ a ∈ pq.2, isExactAtomicDataRange a = true) := by
    obtain ⟨hp, hn, _⟩ := mem_prunedExactPartitions_sub hpq
    exact ⟨fun a ha => csp.atoms_exact hcsp a (hp a ha),
           fun a ha => csp.atoms_exact hcsp a (hn a ha)⟩
  have hWpartLeSpart (pq : List DataRange × List DataRange)
      (hpq : pq ∈ prunedExactPartitions csp.atoms) :
      (W_part pq).length ≤ (S_part pq).length := by
    obtain ⟨hposE, hnegE⟩ := hpartExact pq hpq
    have hWpNd : (W_part pq).Nodup := List.filter_sublist.nodup hWnd
    have hWpLeW : (W_part pq).length ≤ W.length :=
      hWpNd.length_le_of_subset fun y hy => (List.mem_filter.mp hy).1
    by_cases hlt : (S_part pq).length < K
    · let embed : Value → i.Data := i.embedValue
      have hsub : ∀ y ∈ W_part pq, y ∈ (S_part pq).map embed := by
        intro y hy
        have hholds : dataHolds i y (partitionRange pq.1 pq.2) :=
          of_decide_eq_true (List.mem_filter.mp hy).2
        obtain ⟨v, hv, rfl⟩ := samplePartition_complete_of_lt hposE hnegE hlt i y hholds
        exact List.mem_map_of_mem hv
      have h1 := hWpNd.length_le_of_subset hsub
      have h2 : ((S_part pq).map embed).length = (S_part pq).length := List.length_map embed
      omega
    · omega
  let findPart (y : i.Data) : List DataRange × List DataRange :=
    ((prunedExactPartitions csp.atoms).find? (partPred y)).getD ([], [])
  have hfindPart_eq (y : i.Data) (pq : List DataRange × List DataRange)
      (hpq : pq ∈ prunedExactPartitions csp.atoms)
      (hholds : dataHolds i y (partitionRange pq.1 pq.2)) :
      findPart y = pq := by
    have hfind : (prunedExactPartitions csp.atoms).find? (partPred y) = some pq :=
      find?_eq_some_of_unique hpq (decide_eq_true hholds) fun pq' hpq' hp' =>
        prunedExactPartitions_unique hpq' hpq (of_decide_eq_true hp') hholds
    simp [findPart, hfind]
  let phi (y : i.Data) : Value :=
    let pq := findPart y
    nthVal (S_part pq) (indexIn (W_part pq) y)
  have hphi_spec (y : i.Data) (hy : y ∈ W) :
      phi y ∈ csp.pool ∧
      (findPart y) ∈ prunedExactPartitions csp.atoms ∧
      dataHolds i y (partitionRange (findPart y).1 (findPart y).2) ∧
      dataHolds i (i.embedValue (phi y)) (partitionRange (findPart y).1 (findPart y).2) ∧
      evalPartition (findPart y).1 (findPart y).2 (phi y) = true := by
    obtain ⟨pq, hpq, hholds⟩ := exists_prunedExactPartition i y (csp.atoms_exact hcsp)
    have hfp : findPart y = pq := hfindPart_eq y pq hpq hholds
    obtain ⟨hposE, hnegE⟩ := hpartExact pq hpq
    have hyWp : y ∈ W_part pq :=
      List.mem_filter.mpr ⟨hy, decide_eq_true hholds⟩
    have hidxLt : indexIn (W_part pq) y < (S_part pq).length :=
      Nat.lt_of_lt_of_le (indexIn_lt_of_mem hyWp) (hWpartLeSpart pq hpq)
    have hphiMemS : phi y ∈ S_part pq := by
      change nthVal (S_part (findPart y)) (indexIn (W_part (findPart y)) y) ∈ S_part pq
      rw [hfp]
      exact nthVal_mem hidxLt
    have hphiPool : phi y ∈ csp.pool :=
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨pq, hpq, hphiMemS⟩)
    have hphiHolds : dataHolds i (i.embedValue (phi y)) (partitionRange pq.1 pq.2) :=
      samplePartition_sound hposE hnegE hphiMemS i
    have hphiEval : evalPartition pq.1 pq.2 (phi y) = true :=
      (evalPartition_iff hposE hnegE i (phi y)).mpr hphiHolds
    rw [hfp]
    exact ⟨hphiPool, hpq, hholds, hphiHolds, hphiEval⟩
  have hphi_inj (y₁ y₂ : i.Data) (hy₁ : y₁ ∈ W) (hy₂ : y₂ ∈ W)
      (heq : phi y₁ = phi y₂) : y₁ = y₂ := by
    obtain ⟨_, hpq₁, hh₁, hphiH₁, _⟩ := hphi_spec y₁ hy₁
    obtain ⟨_, hpq₂, hh₂, hphiH₂, _⟩ := hphi_spec y₂ hy₂
    have hphiH₂' : dataHolds i (i.embedValue (phi y₁)) (partitionRange (findPart y₂).1 (findPart y₂).2) := by
      rw [heq]; exact hphiH₂
    have hpqEq : findPart y₁ = findPart y₂ :=
      prunedExactPartitions_unique hpq₁ hpq₂ hphiH₁ hphiH₂'
    have hh₂' : dataHolds i y₂ (partitionRange (findPart y₁).1 (findPart y₁).2) := by
      rw [hpqEq]; exact hh₂
    let pq := findPart y₁
    have hy₁Wp : y₁ ∈ W_part pq :=
      List.mem_filter.mpr ⟨hy₁, decide_eq_true hh₁⟩
    have hy₂Wp : y₂ ∈ W_part pq :=
      List.mem_filter.mpr ⟨hy₂, decide_eq_true hh₂'⟩
    have hidx₁ : indexIn (W_part pq) y₁ < (S_part pq).length :=
      Nat.lt_of_lt_of_le (indexIn_lt_of_mem hy₁Wp) (hWpartLeSpart pq hpq₁)
    have hidx₂ : indexIn (W_part pq) y₂ < (S_part pq).length :=
      Nat.lt_of_lt_of_le (indexIn_lt_of_mem hy₂Wp) (hWpartLeSpart pq hpq₁)
    have hnthEq : nthVal (S_part pq) (indexIn (W_part pq) y₁) =
        nthVal (S_part pq) (indexIn (W_part pq) y₂) := by
      change phi y₁ = nthVal (S_part pq) (indexIn (W_part pq) y₂)
      rw [heq]
      change nthVal (S_part (findPart y₂)) (indexIn (W_part (findPart y₂)) y₂) = _
      rw [← hpqEq]
    have hidxEq : indexIn (W_part pq) y₁ = indexIn (W_part pq) y₂ :=
      nthVal_inj (samplePartition_nodup K pq.1 pq.2) hidx₁ hidx₂ hnthEq
    exact indexIn_inj hy₁Wp hy₂Wp hidxEq
  have hphi_eval_iff (y : i.Data) (hy : y ∈ W) (d : DataRange)
      (hd : d.isSROIQD = true) (hsub : ∀ a ∈ atomsOfDataRange d, a ∈ csp.atoms) :
      evalDataRange d (phi y) = true ↔ dataHolds i y d := by
    obtain ⟨_, hpq, hh, _, hphiEval⟩ := hphi_spec y hy
    obtain ⟨hposE, hnegE⟩ := hpartExact (findPart y) hpq
    rw [evalDataRange_eq_evalOnPartition hposE hnegE hpq hphiEval hd hsub]
    exact evalOnPartition_iff_pruned hpq hh hsub
  -- Build target edges from W and hreal.dataProperties
  let target : List DataEdge :=
    ((csp.lowers.flatMap fun L =>
      (W.filter fun y => decide (i.dataProperties L.dp (env L.subj) y)).flatMap fun y =>
        (subDataStar csp.subData L.dp).map fun dp' => (dp', L.subj, phi y))).eraseDups
  have htarget_origin (dp : IRI) (s : Nat) (v : Value)
      (hmem : (dp, s, v) ∈ target) :
      v ∈ csp.pool ∧ ∃ y ∈ W, phi y = v ∧ i.dataProperties dp (env s) y := by
    obtain ⟨L, hL, h1⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hmem)
    obtain ⟨y, hyF, h2⟩ := List.mem_flatMap.mp h1
    obtain ⟨hyW, hdpL⟩ := List.mem_filter.mp hyF
    obtain ⟨dp', hdp', heq⟩ := List.mem_map.mp h2
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    exact ⟨(hphi_spec y hyW).1, y, hyW, rfl,
      subDataStar_sound (fun rs hrs => hreal.subData rs hrs L.subj y)
        (of_decide_eq_true hdpL) dp' hdp'⟩
  have htClosed : EdgesSubClosed csp.subData target := by
    intro r t hrt s v hmem
    obtain ⟨L, hL, h1⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hmem)
    obtain ⟨y, hyF, h2⟩ := List.mem_flatMap.mp h1
    obtain ⟨dp', hdp', heq⟩ := List.mem_map.mp h2
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    refine List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨L, hL,
      List.mem_flatMap.mpr ⟨y, hyF, List.mem_map.mpr ⟨t,
        subDataStar_closed csp.subData L.dp hrt hdp', rfl⟩⟩⟩)
  have hadmT : checkDataAdmissible csp.pool csp.subData csp.disjointData
      csp.keyDisjoint csp.uppers target = true := by
    simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro ⟨dp, s, v⟩ hmem
      exact List.contains_iff_mem.mpr (htarget_origin dp s v hmem).1
    · intro ⟨r, t⟩ hrt ⟨dp, s, v⟩ hmem
      by_cases hdp : dp = r
      · subst hdp
        simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, hasDataEdge,
          List.contains_iff_mem]
        exact htClosed dp t hrt s v hmem
      · simp [beq_false_of_ne hdp]
    · intro ⟨r, t⟩ hrt ⟨dp, s, v⟩ hmem
      by_cases hdp : dp = r
      · subst hdp
        cases hte : hasDataEdge target t s v with
        | false => simp
        | true =>
          obtain ⟨_, y₁, hy₁W, hphi₁, hdp₁⟩ := htarget_origin dp s v hmem
          obtain ⟨_, y₂, hy₂W, hphi₂, hdp₂⟩ := htarget_origin t s v (List.contains_iff_mem.mp hte)
          have hyeq : y₁ = y₂ := hphi_inj y₁ y₂ hy₁W hy₂W (hphi₁.trans hphi₂.symm)
          subst hyeq
          exact (hreal.disjointData (dp, t) hrt s y₁ ⟨hdp₁, hdp₂⟩).elim
      · simp [beq_false_of_ne hdp]
    · intro ⟨s₁, s₂, dp⟩ hkd ⟨dp', s, v⟩ hmem
      by_cases hcond : dp' = dp ∧ s = s₁
      · rcases hcond with ⟨rfl, rfl⟩
        cases h2 : hasDataEdge target dp' s₂ v with
        | false => simp
        | true =>
          obtain ⟨_, y₁, hy₁W, hphi₁, hdp₁⟩ := htarget_origin dp' s v hmem
          obtain ⟨_, y₂, hy₂W, hphi₂, hdp₂⟩ := htarget_origin dp' s₂ v (List.contains_iff_mem.mp h2)
          have hyeq : y₁ = y₂ := hphi_inj y₁ y₂ hy₁W hy₂W (hphi₁.trans hphi₂.symm)
          subst hyeq
          exact (hreal.keyDisjoint (s, s₂, dp') hkd y₁ ⟨hdp₁, hdp₂⟩).elim
      · cases h1 : (dp' == dp && s == s₁) with
        | false => rfl
        | true =>
          obtain ⟨hd1, hs1⟩ := Bool.and_eq_true_iff.mp h1
          exact (hcond ⟨beq_iff_eq.mp hd1, beq_iff_eq.mp hs1⟩).elim
    · intro u hu
      have hdOk : u.range.isSROIQD = true := List.all_eq_true.mp huSROIQD u hu
      have hdSub : ∀ a ∈ atomsOfDataRange u.range, a ∈ csp.atoms := fun a ha =>
        List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨u.range,
          List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_map_of_mem hu)), ha⟩)
      let qs := qualPoolValues csp.pool target u.subj u.dp u.range
      by_cases hle : qs.length ≤ u.bound
      · exact hle
      · exfalso
        have hgt : u.bound + 1 ≤ qs.length := by omega
        -- Pull back `qs.take (u.bound + 1)` to `W` via `W.filter`
        let pre : List i.Data := W.filter fun y =>
          (qs.take (u.bound + 1)).contains (phi y)
        have hpreNd : pre.Nodup := List.filter_sublist.nodup hWnd
        have htakeSubPre : ∀ v ∈ qs.take (u.bound + 1), v ∈ pre.map phi := by
          intro v hv
          have hvQ := List.mem_of_mem_take hv
          obtain ⟨_, hc⟩ := List.mem_filter.mp hvQ
          obtain ⟨he, _⟩ := Bool.and_eq_true_iff.mp hc
          obtain ⟨_, y, hyW, rfl, _⟩ := htarget_origin u.dp u.subj v (List.contains_iff_mem.mp he)
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hyW, List.contains_iff_mem.mpr hv⟩)
        have htakeNd : (qs.take (u.bound + 1)).Nodup :=
          (List.take_sublist ..).nodup (List.filter_sublist.nodup csp.pool_nodup)
        have hlenLe := htakeNd.length_le_of_subset htakeSubPre
        rw [List.length_take_of_le hgt, List.length_map] at hlenLe
        have hpreQual : ∀ y ∈ pre, i.dataProperties u.dp (env u.subj) y ∧ dataHolds i y u.range := by
          intro y hy
          obtain ⟨hyW, hcon⟩ := List.mem_filter.mp hy
          have hvQ := List.mem_of_mem_take (List.contains_iff_mem.mp hcon)
          obtain ⟨_, hc⟩ := List.mem_filter.mp hvQ
          obtain ⟨he, hd⟩ := Bool.and_eq_true_iff.mp hc
          obtain ⟨_, y', hy'W, hphiEq, hdpY'⟩ := htarget_origin u.dp u.subj (phi y) (List.contains_iff_mem.mp he)
          have hyeq : y' = y := hphi_inj y' y hy'W hyW hphiEq
          subst hyeq
          exact ⟨hdpY', (hphi_eval_iff y' hy'W u.range hdOk hdSub).mp hd⟩
        exact hreal.uppers u hu ⟨pre.take (u.bound + 1),
          List.length_take_of_le hlenLe,
          (List.take_sublist ..).nodup hpreNd,
          fun y hy => hpreQual y (List.mem_of_mem_take hy)⟩
  have hlowT : ∀ L ∈ csp.lowers,
      L.count ≤ (qualPoolValues csp.pool target L.subj L.dp L.range).length := by
    intro L hL
    have hdOk : L.range.isSROIQD = true := List.all_eq_true.mp hlSROIQD L hL
    have hdSub : ∀ a ∈ atomsOfDataRange L.range, a ∈ csp.atoms := fun a ha =>
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨L.range,
        List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map_of_mem hL)), ha⟩)
    obtain ⟨xs, hxsLen, hxsNd, hxsW, hxsQ⟩ := hWwit L hL
    have hmapNd : (xs.map phi).Nodup := by
      have haux : ∀ (l : List i.Data), l.Nodup → (∀ y ∈ l, y ∈ W) → (l.map phi).Nodup := by
        intro l hnd hsubW
        induction l with
        | nil => exact List.nodup_nil
        | cons a tail ih =>
          obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
          refine List.nodup_cons.mpr ⟨?_, ih hnd' (fun y hy => hsubW y (List.mem_cons_of_mem _ hy))⟩
          intro hm
          obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
          have hab := hphi_inj b a (hsubW b (List.mem_cons_of_mem _ hb))
            (hsubW a (List.mem_cons_self ..)) heq
          exact hna (hab ▸ hb)
      exact haux xs hxsNd hxsW
    have hmapSub : ∀ v ∈ xs.map phi,
        v ∈ qualPoolValues csp.pool target L.subj L.dp L.range := by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      have hyW := hxsW y hy
      obtain ⟨hdpY, hdY⟩ := hxsQ y hy
      have hphiPool := (hphi_spec y hyW).1
      have hmemT : (L.dp, L.subj, phi y) ∈ target :=
        List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨L, hL,
          List.mem_flatMap.mpr ⟨y, List.mem_filter.mpr ⟨hyW, decide_eq_true hdpY⟩,
            List.mem_map.mpr ⟨L.dp, self_mem_subDataStar csp.subData L.dp, rfl⟩⟩⟩)
      have heval : evalDataRange L.range (phi y) = true :=
        (hphi_eval_iff y hyW L.range hdOk hdSub).mpr hdY
      exact List.mem_filter.mpr ⟨hphiPool, Bool.and_eq_true_iff.mpr
        ⟨List.contains_iff_mem.mpr hmemT, heval⟩⟩
    have hle := hmapNd.length_le_of_subset hmapSub
    rw [List.length_map, hxsLen] at hle
    exact hle
  unfold solveDataCSP
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact solveLowers_isSome_of_target csp.pool_nodup hadmT htClosed csp.lowers []
        hlowT (fun _ h => (List.not_mem_nil h).elim)
        (fun _ _ _ _ _ h => (List.not_mem_nil h).elim)

theorem solveDataCSP_none_unsat {csp : DataCSP} (hcsp : csp.isSROIQD = true)
    (hnone : solveDataCSP csp = none)
    {i : Interpretation datatypeMap} {env : Nat → i.Object} :
    ¬ csp.Realizes i env := by
  intro hreal
  have his := solveDataCSP_complete hcsp hreal
  rw [hnone] at his
  cases his

#print axioms solveDataCSP_sound
#print axioms solveDataCSP_realizes
#print axioms solveDataCSP_complete
#print axioms solveDataCSP_none_unsat

end Sabrina.OWL2.SROIQD.Termination

/-! ### 7. Bridge from `SROIQ(D)` concepts and `Problem` to `DataCSP` -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.OWL2.Datatypes
open Sabrina.RoleChains (Rank checkRegular)

def Concept.isSROIQD : Concept → Bool
  | .top | .bottom => true
  | .lit a _ => isCoreClassIRI a
  | .nom _ _ => true
  | .self r _ => isCoreObjPropIRI r.1
  | .conj a b | .disj a b => a.isSROIQD && b.isSROIQD
  | .some r c | .all r c | .min _ r c | .max _ r c => isCoreObjPropIRI r.1 && c.isSROIQD
  | .dataSome dp d | .dataAll dp d | .dataMin _ dp d | .dataMax _ dp d =>
    isCoreDataPropIRI dp && d.isSROIQD
  | .dataValue dp l _ =>
    isCoreDataPropIRI dp && (decodeLiteral l).isSome

theorem Concept.isSROIQD_dual (c : Concept) : c.dual.isSROIQD = c.isSROIQD := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQD]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQD]
  | _ => simp_all [Concept.dual, Concept.isSROIQD]

namespace Termination

def conceptToLower (s : Nat) : Concept → Option DataLower
  | .dataSome dp d => some ⟨s, dp, d, 1⟩
  | .dataMin n dp d => some ⟨s, dp, d, n⟩
  | .dataValue dp l true => some ⟨s, dp, .oneOf [l], 1⟩
  | _ => none

def conceptToUpper (s : Nat) : Concept → Option DataUpper
  | .dataAll dp d => some ⟨s, dp, .complement d, 0⟩
  | .dataMax n dp d => some ⟨s, dp, d, n⟩
  | .dataValue dp l false => some ⟨s, dp, .oneOf [l], 0⟩
  | _ => none

def mkSubjectsDataCSP (p : Problem) (subjLabels : List (Nat × List Concept))
    (keyDisjoint : List (Nat × Nat × IRI)) : DataCSP where
  subData := p.subData
  disjointData := p.disjointData
  keyDisjoint := keyDisjoint
  lowers := subjLabels.flatMap fun (s, ls) => ls.filterMap (conceptToLower s)
  uppers := subjLabels.flatMap fun (s, ls) =>
    ls.filterMap (conceptToUpper s) ++
    p.dataRanges.map (fun (dp, d) => ⟨s, dp, .complement d, 0⟩) ++
    p.funcData.map (fun dp => ⟨s, dp, .datatype literalDatatype, 1⟩)

theorem mkSubjectsDataCSP_isSROIQD {p : Problem}
    {subjLabels : List (Nat × List Concept)} {keyDisjoint : List (Nat × Nat × IRI)}
    (hdr : ∀ rd ∈ p.dataRanges, rd.2.isSROIQD = true)
    (hls : ∀ sl ∈ subjLabels, ∀ c ∈ sl.2, c.isSROIQD = true) :
    (mkSubjectsDataCSP p subjLabels keyDisjoint).isSROIQD = true := by
  simp only [DataCSP.isSROIQD, mkSubjectsDataCSP, Bool.and_eq_true, List.all_eq_true,
    List.mem_flatMap, List.mem_append, List.mem_filterMap, List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro l ⟨⟨s, ls⟩, hsl, c, hc, hcl⟩
    have hcOk := hls (s, ls) hsl c hc
    cases c <;> simp [conceptToLower] at hcl
    · subst hcl; exact (Bool.and_eq_true_iff.mp hcOk).2
    · rename_i dp lit sign
      cases sign <;> simp at hcl
      subst hcl
      have hlit := (Bool.and_eq_true_iff.mp hcOk).2
      simp [DataRange.isSROIQD, isExactAtomicDataRange, hlit]
    · subst hcl; exact (Bool.and_eq_true_iff.mp hcOk).2
  · rintro u ⟨⟨s, ls⟩, hsl, hcase⟩
    rcases hcase with (⟨c, hc, hcu⟩ | ⟨⟨dp, d⟩, hrd, rfl⟩) | ⟨dp, _, rfl⟩
    · have hcOk := hls (s, ls) hsl c hc
      cases c <;> simp [conceptToUpper] at hcu
      · subst hcu; exact (Bool.and_eq_true_iff.mp hcOk).2
      · rename_i dp lit sign
        cases sign <;> simp at hcu
        subst hcu
        have hlit := (Bool.and_eq_true_iff.mp hcOk).2
        simp [DataRange.isSROIQD, isExactAtomicDataRange, hlit]
      · subst hcu; exact (Bool.and_eq_true_iff.mp hcOk).2
    · exact hdr (dp, d) hrd
    · rfl

theorem mkSubjectsDataCSP_realizes_of_models {p : Problem}
    {subjLabels : List (Nat × List Concept)} {keyDisjoint : List (Nat × Nat × IRI)}
    {i : Interpretation datatypeMap} {env : Nat → i.Object}
    (hm : p.Models i)
    (hlabels : ∀ sl ∈ subjLabels, ∀ c ∈ sl.2, holds i (env sl.1) c)
    (hkd : ∀ kd ∈ keyDisjoint, ∀ y, ¬ (i.dataProperties kd.2.2 (env kd.1) y ∧ i.dataProperties kd.2.2 (env kd.2.1) y)) :
    (mkSubjectsDataCSP p subjLabels keyDisjoint).Realizes i env := by
  refine ⟨fun rs hrs s y h => hm.subData rs hrs (env s) y h,
    fun rs hrs s y h => hm.disjointData rs hrs (env s) y h,
    hkd, ?_, ?_⟩
  · intro l hl
    obtain ⟨⟨s, ls⟩, hsl, hfm⟩ := List.mem_flatMap.mp hl
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.mp hfm
    have hhold := hlabels (s, ls) hsl c hc
    cases c <;> simp [conceptToLower] at hcl
    · subst hcl
      obtain ⟨y, hy, hd⟩ := hhold
      exact ⟨[y], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun z hz => (List.mem_singleton.mp hz) ▸ ⟨hy, hd⟩⟩
    · rename_i dp lit sign
      cases sign <;> simp at hcl
      subst hcl
      exact ⟨[i.literalValue lit], rfl,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun z hz => (List.mem_singleton.mp hz) ▸ ⟨hhold, lit, List.mem_singleton_self _, rfl⟩⟩
    · subst hcl
      exact hhold
  · intro u hu
    obtain ⟨⟨s, ls⟩, hsl, hcase⟩ := List.mem_flatMap.mp hu
    simp only [List.mem_append, List.mem_filterMap, List.mem_map] at hcase
    rcases hcase with (⟨c, hc, hcu⟩ | ⟨⟨dp, d⟩, hrd, rfl⟩) | ⟨dp, hfd, rfl⟩
    · have hhold := hlabels (s, ls) hsl c hc
      cases c <;> simp [conceptToUpper] at hcu
      · subst hcu
        rintro ⟨ys, hlen, _, hq⟩
        cases ys with
        | nil => simp at hlen
        | cons y _ =>
          obtain ⟨hy, hnotd⟩ := hq y (List.mem_cons_self ..)
          exact hnotd (hhold y hy)
      · rename_i dp lit sign
        cases sign <;> simp at hcu
        subst hcu
        rintro ⟨ys, hlen, _, hq⟩
        cases ys with
        | nil => simp at hlen
        | cons y _ =>
          obtain ⟨hy, l', hl', rfl⟩ := hq y (List.mem_cons_self ..)
          rw [List.mem_singleton.mp hl'] at hy
          exact hhold hy
      · subst hcu
        exact hhold
    · rintro ⟨ys, hlen, _, hq⟩
      cases ys with
      | nil => simp at hlen
      | cons y _ =>
        obtain ⟨hy, hnotd⟩ := hq y (List.mem_cons_self ..)
        exact hnotd (hm.dataRanges (dp, d) hrd (env s) y hy)
    · rintro ⟨ys, hlen, hnd, hq⟩
      cases ys with
      | nil => simp at hlen
      | cons y₁ tail =>
        cases tail with
        | nil => simp at hlen
        | cons y₂ _ =>
          have h1 := (hq y₁ (List.mem_cons_self ..)).1
          have h2 := (hq y₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
          have heq := hm.funcData dp hfd (env s) y₁ y₂ h1 h2
          exact (List.nodup_cons.mp hnd).1 (heq ▸ List.mem_cons_self ..)

/-- Semantic data-edge relation induced by a solved `List DataEdge`. -/
def solEdge (sol : List DataEdge) (i : Interpretation datatypeMap)
    (dp : IRI) (s : Nat) (y : i.Data) : Prop :=
  ∃ v : Value, y = i.embedValue v ∧ (dp, s, v) ∈ sol

theorem solEdge_subData {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) (i : Interpretation datatypeMap)
    {r t : IRI} (hrt : (r, t) ∈ csp.subData) (s : Nat) (y : i.Data)
    (h : solEdge sol i r s y) : solEdge sol i t s y := by
  obtain ⟨hadm, _⟩ := solveDataCSP_sound hsol
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true] at hadm
  obtain ⟨⟨⟨⟨_, hsubD⟩, _⟩, _⟩, _⟩ := hadm
  obtain ⟨v, rfl, hrv⟩ := h
  have hstep := hsubD (r, t) hrt (r, s, v) hrv
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, hasDataEdge,
    List.contains_iff_mem] at hstep
  exact ⟨v, rfl, hstep⟩

theorem solEdge_disjointData {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) (i : Interpretation datatypeMap)
    {r t : IRI} (hrt : (r, t) ∈ csp.disjointData) (s : Nat) (y : i.Data) :
    ¬ (solEdge sol i r s y ∧ solEdge sol i t s y) := by
  rintro ⟨⟨v₁, hy₁, h₁⟩, ⟨v₂, hy₂, h₂⟩⟩
  have hveq : v₁ = v₂ := i.embedValue_injective (hy₁.symm.trans hy₂)
  subst hveq
  obtain ⟨hadm, _⟩ := solveDataCSP_sound hsol
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true] at hadm
  obtain ⟨⟨⟨_, hdisjD⟩, _⟩, _⟩ := hadm
  have hstep := hdisjD (r, t) hrt (r, s, v₁) h₁
  have hhas : hasDataEdge sol t s v₁ = true := List.contains_iff_mem.mpr h₂
  simp [hhas] at hstep

theorem solEdge_keyDisjoint {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) (i : Interpretation datatypeMap)
    {s₁ s₂ : Nat} {dp : IRI} (hkd : (s₁, s₂, dp) ∈ csp.keyDisjoint) (y : i.Data) :
    ¬ (solEdge sol i dp s₁ y ∧ solEdge sol i dp s₂ y) := by
  rintro ⟨⟨v₁, hy₁, h₁⟩, ⟨v₂, hy₂, h₂⟩⟩
  have hveq : v₁ = v₂ := i.embedValue_injective (hy₁.symm.trans hy₂)
  subst hveq
  obtain ⟨hadm, _⟩ := solveDataCSP_sound hsol
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true] at hadm
  obtain ⟨⟨_, hkeyD⟩, _⟩ := hadm
  have hstep := hkeyD (s₁, s₂, dp) hkd (dp, s₁, v₁) h₁
  have hhas : hasDataEdge sol dp s₂ v₁ = true := List.contains_iff_mem.mpr h₂
  simp [hhas] at hstep

theorem solEdge_lower_atLeast {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) (i : Interpretation datatypeMap)
    {l : DataLower} (hl : l ∈ csp.lowers) (hdOk : l.range.isSROIQD = true) :
    AtLeast l.count (fun y => solEdge sol i l.dp l.subj y ∧ dataHolds i y l.range) := by
  obtain ⟨_, hlow⟩ := solveDataCSP_sound hsol
  have hlen := hlow l hl
  let embed : Value → i.Data := i.embedValue
  let qs := qualPoolValues csp.pool sol l.subj l.dp l.range
  have hqnd : qs.Nodup := List.filter_sublist.nodup csp.pool_nodup
  refine ⟨(qs.take l.count).map embed,
    (List.length_map embed).trans (List.length_take_of_le hlen),
    nodup_map_inj i.embedValue_injective ((List.take_sublist ..).nodup hqnd), ?_⟩
  intro y hy
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  have hv' := List.mem_of_mem_take hv
  obtain ⟨_, hcond⟩ := List.mem_filter.mp hv'
  obtain ⟨he, hd⟩ := Bool.and_eq_true_iff.mp hcond
  exact ⟨⟨v, rfl, List.contains_iff_mem.mp he⟩, (evalDataRange_iff hdOk i v).mp hd⟩

theorem solEdge_upper_not_atLeast {csp : DataCSP} {sol : List DataEdge}
    (hsol : solveDataCSP csp = some sol) (i : Interpretation datatypeMap)
    {u : DataUpper} (hu : u ∈ csp.uppers) (hdOk : u.range.isSROIQD = true) :
    ¬ AtLeast (u.bound + 1) (fun y => solEdge sol i u.dp u.subj y ∧ dataHolds i y u.range) := by
  rintro ⟨ys, hlen, hnd, hq⟩
  obtain ⟨hadm, _⟩ := solveDataCSP_sound hsol
  simp only [checkDataAdmissible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨⟨hpool, _⟩, _⟩, _⟩, hupD⟩ := hadm
  have hbound := hupD u hu
  let embed : Value → i.Data := i.embedValue
  let qs := qualPoolValues csp.pool sol u.subj u.dp u.range
  have hsub : ∀ y ∈ ys, y ∈ qs.map embed := by
    intro y hy
    obtain ⟨⟨v, rfl, hvSol⟩, hdY⟩ := hq y hy
    have hvPool : v ∈ csp.pool := List.contains_iff_mem.mp (hpool (u.dp, u.subj, v) hvSol)
    have hvEval : evalDataRange u.range v = true := (evalDataRange_iff hdOk i v).mpr hdY
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hvPool, Bool.and_eq_true_iff.mpr
      ⟨List.contains_iff_mem.mpr hvSol, hvEval⟩⟩)
  have hle := hnd.length_le_of_subset hsub
  have hmapLen : (qs.map embed).length = (qualPoolValues csp.pool sol u.subj u.dp u.range).length :=
    List.length_map embed
  omega

theorem solEdge_dataRanges {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} {d : DataRange} (hrd : (dp, d) ∈ p.dataRanges) (hdOk : d.isSROIQD = true)
    (y : i.Data) (hy : solEdge sol i dp s y) : dataHolds i y d := by
  have hu : ⟨s, dp, .complement d, 0⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).uppers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨(s, ls), hsl, .inl (.inr ⟨(dp, d), hrd, rfl⟩)⟩
  have hnot := solEdge_upper_not_atLeast hsol i hu hdOk
  apply Classical.byContradiction
  intro hnd
  exact hnot ⟨[y], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun z hz => (List.mem_singleton.mp hz) ▸ ⟨hy, hnd⟩⟩

theorem solEdge_funcData {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} (hfd : dp ∈ p.funcData)
    (y₁ y₂ : i.Data) (h₁ : solEdge sol i dp s y₁) (h₂ : solEdge sol i dp s y₂) :
    y₁ = y₂ := by
  have hu : ⟨s, dp, .datatype literalDatatype, 1⟩ ∈
      (mkSubjectsDataCSP p subjLabels keyDisjoint).uppers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨(s, ls), hsl, .inr ⟨dp, hfd, rfl⟩⟩
  have hnot := solEdge_upper_not_atLeast hsol i hu rfl
  exact (atMostOne_iff (fun y => solEdge sol i dp s y ∧ dataHolds i y (.datatype literalDatatype))).mp
    hnot y₁ y₂ ⟨h₁, i.literalDatatypeExt y₁⟩ ⟨h₂, i.literalDatatypeExt y₂⟩

theorem solEdge_holds_dataSome {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} {d : DataRange} (hc : .dataSome dp d ∈ ls) (hdOk : d.isSROIQD = true) :
    ∃ y : i.Data, solEdge sol i dp s y ∧ dataHolds i y d := by
  have hl : ⟨s, dp, d, 1⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).lowers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .dataSome dp d, hc, rfl⟩
  obtain ⟨ys, hlen, _, hq⟩ := solEdge_lower_atLeast hsol i hl hdOk
  cases ys with
  | nil => simp at hlen
  | cons y _ => exact ⟨y, hq y (List.mem_cons_self ..)⟩

theorem solEdge_holds_dataAll {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} {d : DataRange} (hc : .dataAll dp d ∈ ls) (hdOk : d.isSROIQD = true) :
    ∀ y : i.Data, solEdge sol i dp s y → dataHolds i y d := by
  have hu : ⟨s, dp, .complement d, 0⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).uppers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_append, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .inl (.inl ⟨.dataAll dp d, hc, rfl⟩)⟩
  have hnot := solEdge_upper_not_atLeast hsol i hu hdOk
  intro y hy
  apply Classical.byContradiction
  intro hnd
  exact hnot ⟨[y], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun z hz => (List.mem_singleton.mp hz) ▸ ⟨hy, hnd⟩⟩

theorem solEdge_holds_dataValue_true {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} {l : Literal} (hc : .dataValue dp l true ∈ ls)
    (hlOk : (decodeLiteral l).isSome = true) :
    solEdge sol i dp s (i.literalValue l) := by
  have hl : ⟨s, dp, .oneOf [l], 1⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).lowers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .dataValue dp l true, hc, rfl⟩
  have hdOk : (DataRange.oneOf [l]).isSROIQD = true := by
    simp [DataRange.isSROIQD, isExactAtomicDataRange, hlOk]
  obtain ⟨ys, hlen, _, hq⟩ := solEdge_lower_atLeast hsol i hl hdOk
  cases ys with
  | nil => simp at hlen
  | cons y _ =>
    obtain ⟨hy, l', hl', heq⟩ := hq y (List.mem_cons_self ..)
    rw [List.mem_singleton.mp hl'] at heq
    exact heq ▸ hy

theorem solEdge_holds_dataValue_false {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {dp : IRI} {l : Literal} (hc : .dataValue dp l false ∈ ls)
    (hlOk : (decodeLiteral l).isSome = true) :
    ¬ solEdge sol i dp s (i.literalValue l) := by
  have hu : ⟨s, dp, .oneOf [l], 0⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).uppers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_append, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .inl (.inl ⟨.dataValue dp l false, hc, rfl⟩)⟩
  have hdOk : (DataRange.oneOf [l]).isSROIQD = true := by
    simp [DataRange.isSROIQD, isExactAtomicDataRange, hlOk]
  have hnot := solEdge_upper_not_atLeast hsol i hu hdOk
  intro hy
  exact hnot ⟨[i.literalValue l], rfl, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun z hz => (List.mem_singleton.mp hz) ▸ ⟨hy, l, List.mem_singleton_self _, rfl⟩⟩

theorem solEdge_holds_dataMin {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {n : Nat} {dp : IRI} {d : DataRange} (hc : .dataMin n dp d ∈ ls) (hdOk : d.isSROIQD = true) :
    AtLeast n (fun y => solEdge sol i dp s y ∧ dataHolds i y d) := by
  have hl : ⟨s, dp, d, n⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).lowers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .dataMin n dp d, hc, rfl⟩
  exact solEdge_lower_atLeast hsol i hl hdOk

theorem solEdge_holds_dataMax {p : Problem} {subjLabels : List (Nat × List Concept)}
    {keyDisjoint : List (Nat × Nat × IRI)} {sol : List DataEdge}
    (hsol : solveDataCSP (mkSubjectsDataCSP p subjLabels keyDisjoint) = some sol)
    (i : Interpretation datatypeMap)
    {s : Nat} {ls : List Concept} (hsl : (s, ls) ∈ subjLabels)
    {n : Nat} {dp : IRI} {d : DataRange} (hc : .dataMax n dp d ∈ ls) (hdOk : d.isSROIQD = true) :
    ¬ AtLeast (n + 1) (fun y => solEdge sol i dp s y ∧ dataHolds i y d) := by
  have hu : ⟨s, dp, d, n⟩ ∈ (mkSubjectsDataCSP p subjLabels keyDisjoint).uppers := by
    simp only [mkSubjectsDataCSP, List.mem_flatMap, List.mem_append, List.mem_filterMap]
    exact ⟨(s, ls), hsl, .inl (.inl ⟨.dataMax n dp d, hc, rfl⟩)⟩
  exact solEdge_upper_not_atLeast hsol i hu hdOk

end Termination
end Sabrina.OWL2.SROIQD
