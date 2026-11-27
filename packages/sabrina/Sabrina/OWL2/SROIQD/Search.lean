import Sabrina.OWL2.SROIQD.Branch

/-! Unified SROIQ(D) tableau transitions, mixed object+data HasKey merging,
    data property hierarchy & disjointness, datatype-range clash closure,
    finite model witness completion, and kernel-verified consistency/entailment
    checkers. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole InclusionVerdict)
open Sabrina.RoleChains (Graph)
open Sabrina.OWL2.Datatypes (Value FloatVal DateTimeVal datatypeMap decodeLiteral samplePattern)
open Sabrina.OWL2.DataRanges (compile compileSolvedRange SolvedRange)

structure Transition (p : Problem) (s : Branch) where
  branches : List Branch
  preserves : s.Sat p → ∃ t ∈ branches, t.Sat p

private def deterministic {p : Problem} {s : Branch} (t : Branch)
    (h : s.Sat p → t.Sat p) : Transition p s :=
  ⟨[t], fun hs => ⟨t, List.mem_singleton.mpr rfl, h hs⟩⟩

private def close {p : Problem} {s : Branch} (h : ¬ s.Sat p) : Transition p s :=
  ⟨[], fun hs => (h hs).elim⟩

private def add {p : Problem} {s : Branch} (x : Nat) (c : Concept)
    (h : ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env x) c) : Transition p s :=
  deterministic (s.add x c) fun ⟨i, hm, env, hs⟩ =>
    ⟨i, hm, env, Branch.add_realizes hs (h i env hm hs)⟩

private def select {p : Problem} {s : Branch} (x : Nat) (a b : Concept)
    (h : ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env x) a ∨ holds i (env x) b) : Transition p s :=
  ⟨[s.add x a, s.add x b], fun ⟨i, hm, env, hs⟩ => by
    rcases h i env hm hs with ha | hb
    · exact ⟨s.add x a, by simp, i, hm, env, Branch.add_realizes hs ha⟩
    · exact ⟨s.add x b, by simp, i, hm, env, Branch.add_realizes hs hb⟩⟩

private def addEdge {p : Problem} {s : Branch} (r : OrientedRole) (x y : Nat)
    (h : ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holdsOriented i r (env x) (env y)) : Transition p s :=
  deterministic (s.addOriented r x y) fun ⟨i, hm, env, hs⟩ =>
    ⟨i, hm, env, Branch.addOriented_realizes hs (h i env hm hs)⟩

private def inequalityClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.unequal.attach.findSome? fun ⟨⟨x, y⟩, h⟩ =>
    if he : x = y then some (close fun ⟨_, _, env, hs⟩ => hs.unequal x y h (congrArg env he))
    else none

private def labelClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    if hc : c = .bottom then
      some (close fun ⟨i, _, env, hs⟩ => by
        have he := hs.labels x c h
        rw [hc] at he; exact he)
    else if hd : s.known x c.dual then
      some (close fun ⟨i, _, env, hs⟩ =>
        (holds_dual i (env x) c).mp (Branch.known_sound hs hd) (hs.labels x c h))
    else none

private def negEdgeClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.negEdges.attach.findSome? fun ⟨⟨r, x, y⟩, h⟩ =>
    if he : s.edge (r, false) x y then
      some (close fun ⟨_, _, _, hs⟩ => hs.negEdges r x y h (Branch.edge_sound hs he))
    else none

private def nominalMerge (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    match c with
    | .nom (.named a) true =>
      s.noms.attach.findSome? fun ⟨⟨b, y⟩, hn⟩ =>
        if hab : a = b then
          if hxy : x ≠ y then
            let keep := min x y
            let drop := max x y
            some (deterministic (s.merge keep drop) fun ⟨i, hm, env, hs⟩ => by
              have hx : env x = i.individuals (.named a) := hs.labels x (.nom (.named a) true) h
              have hy : env y = i.individuals (.named a) := hab ▸ hs.noms b y hn
              have heq : env keep = env drop := by
                by_cases hle : x ≤ y
                · simp only [keep, drop, Nat.min_eq_left hle, Nat.max_eq_right hle]
                  exact hx.trans hy.symm
                · have hlt : y ≤ x := Nat.le_of_not_le hle
                  simp only [keep, drop, Nat.min_eq_right hlt, Nat.max_eq_left hlt]
                  exact hy.trans hx.symm
              exact ⟨i, hm, env, Branch.merge_realizes hs heq⟩)
          else none
        else none
    | .nom (.named a) false =>
      s.noms.attach.findSome? fun ⟨⟨b, y⟩, hn⟩ =>
        if hab : a = b then
          if hxy : x = y then
            some (close fun ⟨i, _, env, hs⟩ => by
              have hx : env x ≠ i.individuals (.named a) := hs.labels x (.nom (.named a) false) h
              have hy : env x = i.individuals (.named a) := hxy ▸ hab ▸ hs.noms b y hn
              exact hx hy)
          else none
        else none
    | .nom (.anonymous doc lid) true =>
      s.anons.attach.findSome? fun ⟨⟨k, y⟩, hn⟩ =>
        if hab : (doc, lid) = k then
          if hxy : x ≠ y then
            let keep := min x y
            let drop := max x y
            some (deterministic (s.merge keep drop) fun ⟨i, hm, env, hs⟩ => by
              have hx : env x = i.individuals (.anonymous doc lid) := hs.labels x (.nom (.anonymous doc lid) true) h
              have hy : env y = i.individuals (.anonymous doc lid) := by
                have hk := hs.anons k y hn
                rw [← hab] at hk; exact hk
              have heq : env keep = env drop := by
                by_cases hle : x ≤ y
                · simp only [keep, drop, Nat.min_eq_left hle, Nat.max_eq_right hle]
                  exact hx.trans hy.symm
                · have hlt : y ≤ x := Nat.le_of_not_le hle
                  simp only [keep, drop, Nat.min_eq_right hlt, Nat.max_eq_left hlt]
                  exact hy.trans hx.symm
              exact ⟨i, hm, env, Branch.merge_realizes hs heq⟩)
          else none
        else none
    | .nom (.anonymous doc lid) false =>
      s.anons.attach.findSome? fun ⟨⟨k, y⟩, hn⟩ =>
        if hab : (doc, lid) = k then
          if hxy : x = y then
            some (close fun ⟨i, _, env, hs⟩ => by
              have hx : env x ≠ i.individuals (.anonymous doc lid) := hs.labels x (.nom (.anonymous doc lid) false) h
              have hy : env x = i.individuals (.anonymous doc lid) := by
                have hk := hxy ▸ hs.anons k y hn
                rw [← hab] at hk; exact hk
              exact hx hy)
          else none
        else none
    | _ => none

private def selfSteps (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    match c with
    | .self r true =>
      if s.edge r x x then none
      else some (addEdge r x x fun _ _ _ hs => hs.labels x (.self r true) h)
    | .self r false =>
      if he : s.edge r x x then
        some (close fun ⟨_, _, _, hs⟩ => hs.labels x (.self r false) h (Branch.edge_sound hs he))
      else none
    | _ => none

private def roleCharSteps (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  (p.chars.irreflexive.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x =>
      if he : s.edge (r, false) x x then
        some (close fun ⟨_, hm, _, hs⟩ => hm.irreflexive r hr _ (Branch.edge_sound hs he))
      else none) <|>
  (p.chars.asymmetric.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hxy : s.edge (r, false) x y then
        if hyx : s.edge (r, false) y x then
          some (close fun ⟨_, hm, _, hs⟩ =>
            hm.asymmetric r hr _ _ (Branch.edge_sound hs hxy) (Branch.edge_sound hs hyx))
        else none
      else none) <|>
  (p.chars.disjoint.attach.findSome? fun ⟨(r, t), hd⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hr : s.edge r x y then
        if ht : s.edge t x y then
          some (close fun ⟨_, hm, _, hs⟩ =>
            hm.disjoint (r, t) hd _ _ ⟨Branch.edge_sound hs hr, Branch.edge_sound hs ht⟩)
        else none
      else none) <|>
  (p.chars.reflexive.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x =>
      if s.edge (r, false) x x then none
      else some (addEdge (r, false) x x fun _ _ hm _ => hm.reflexive r hr _))

/-- Intersect a data range with all universal data constraints on `(x, dp)`. -/
private def combineDataRange (s : Branch) (x : Nat) (dp : IRI) (d : DataRange) : DataRange :=
  let cs := s.dataConstraints.filterMap fun (y, r, e) =>
    if y == x && r == dp then some e else none
  cs.foldl DataRange.intersection d

private theorem combineDataRange_sound {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {x : Nat} {dp : IRI} {d : DataRange} {y : i.Data}
    (hs : s.Realizes i env) (hedge : i.dataProperties dp (env x) y)
    (hd : dataHolds i y d) : dataHolds i y (combineDataRange s x dp d) := by
  unfold combineDataRange
  have hfold : ∀ (cs : List DataRange) (acc : DataRange),
      (∀ e ∈ cs, dataHolds i y e) → dataHolds i y acc →
      dataHolds i y (cs.foldl DataRange.intersection acc) := by
    intro cs
    induction cs with
    | nil => intro acc _ hacc; exact hacc
    | cons e tail ih =>
      intro acc hall hacc
      exact ih (.intersection acc e)
        (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
        ⟨hacc, hall e (List.mem_cons_self ..)⟩
  refine hfold _ d ?_ hd
  intro e he
  obtain ⟨⟨a, r, e'⟩, hmem, hif⟩ := List.mem_filterMap.mp he
  cases hcond : (a == x && r == dp) with
  | false => simp [hcond] at hif
  | true =>
    simp only [hcond, ↓reduceIte, Option.some.injEq] at hif
    subst hif
    obtain ⟨hx, hr⟩ := Bool.and_eq_true_iff.mp hcond
    have hx' := beq_iff_eq.mp hx
    have hr' := beq_iff_eq.mp hr
    subst hx' hr'
    exact hs.dataConstraints a r e' hmem y hedge

private def dataClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  -- 1. Positive / negative data edge clash
  (s.dataEdges.attach.findSome? fun ⟨⟨dp, x, v⟩, h⟩ =>
    if hn : s.negDataEdges.contains (dp, x, v) then
      some (close fun ⟨_, _, _, hs⟩ =>
        hs.negDataEdges dp x v (List.contains_iff_mem.mp hn) (hs.dataEdges dp x v h))
    else none) <|>
  -- 2. Disjoint data property clash on observed data edges
  (p.disjointData.attach.findSome? fun ⟨⟨r, t⟩, hrt⟩ =>
    s.dataEdges.attach.findSome? fun ⟨⟨dp, x, v⟩, he⟩ =>
      if h1 : dp = r then
        if h2 : s.dataEdges.contains (t, x, v) then
          some (close fun ⟨_, hm, env, hs⟩ =>
            hm.disjointData (r, t) hrt (env x) _
              ⟨h1 ▸ hs.dataEdges dp x v he, hs.dataEdges t x v (List.contains_iff_mem.mp h2)⟩)
        else none
      else none) <|>
  -- 3. Functional data property clash on distinct values
  (p.funcData.attach.findSome? fun ⟨dp, hdp⟩ =>
    s.dataEdges.attach.findSome? fun ⟨⟨dp1, x1, v1⟩, h1⟩ =>
      if hdp1 : dp1 = dp then
        s.dataEdges.attach.findSome? fun ⟨⟨dp2, x2, v2⟩, h2⟩ =>
          if hdp2 : dp2 = dp ∧ x2 = x1 ∧ v1 ≠ v2 then
            some (close fun ⟨i, hm, env, hs⟩ => by
              have e1 := hdp1 ▸ hs.dataEdges dp1 x1 v1 h1
              have e2 := hdp2.2.1 ▸ hdp2.1 ▸ hs.dataEdges dp2 x2 v2 h2
              exact hdp2.2.2 (i.embedValue_injective (hm.funcData dp hdp (env x1) _ _ e1 e2)))
          else none
      else none) <|>
  -- 4. Data constraint violation on a data edge
  (s.dataConstraints.attach.findSome? fun ⟨⟨x, dp, d⟩, hc⟩ =>
    match hcomp : compile d with
    | none => none
    | some comp =>
      s.dataEdges.attach.findSome? fun ⟨⟨dp', x', v⟩, he⟩ =>
        if hmatch : dp' = dp ∧ x' = x then
          if hfail : comp.holds v = false then
            some (close fun ⟨i, _, _, hs⟩ => by
              have hedge := hmatch.2 ▸ hmatch.1 ▸ hs.dataEdges dp' x' v he
              have hdata := hs.dataConstraints x dp d hc _ hedge
              have htrue := (comp.holds_iff i v).mpr hdata
              rw [hfail] at htrue; cases htrue)
          else none
        else none) <|>
  -- 5. dataMax violation on distinct observed data edges
  (s.labels.attach.findSome? fun ⟨⟨x, c⟩, hl⟩ =>
    match c with
    | .dataMax n dp d =>
      match hcomp : compile d with
      | none => none
      | some comp =>
        let vals := (s.dataEdges.filterMap fun (r, y, v) =>
          if r == dp && y == x && comp.holds v then some v else none).eraseDups
        if hlen : n + 1 ≤ vals.length then
          some (close fun ⟨i, _, env, hs⟩ => by
            have hmax := hs.labels x (.dataMax n dp d) hl
            apply hmax
            let takeVals : List Value := vals.take (n + 1)
            let embed : Value → i.Data := i.embedValue
            have hndv : takeVals.Nodup := (List.take_sublist ..).nodup (nodup_eraseDups_list _)
            refine ⟨takeVals.map embed, by simp [takeVals, Nat.min_eq_left hlen],
              nodup_map_inj i.embedValue_injective hndv, ?_⟩
            · intro z hz
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
              have hv' := List.mem_eraseDups.mp (List.mem_of_mem_take hv)
              obtain ⟨⟨r, y, v'⟩, hmem, hif⟩ := List.mem_filterMap.mp hv'
              cases hcond : (r == dp && y == x && comp.holds v') with
              | false => simp [hcond] at hif
              | true =>
                simp only [hcond, ↓reduceIte, Option.some.injEq] at hif
                subst hif
                obtain ⟨⟨hr, hy⟩, hch⟩ := Bool.and_eq_true_iff.mp hcond |>.imp_left Bool.and_eq_true_iff.mp
                have hr' := beq_iff_eq.mp hr
                have hy' := beq_iff_eq.mp hy
                subst hr' hy'
                exact ⟨hs.dataEdges r y v' hmem, (comp.holds_iff i v').mp hch⟩)
        else none
    | _ => none) <|>
  -- 6. dataSome / dataMin emptiness, finite-domain exhaustion, or functional conflict
  (s.labels.attach.findSome? fun ⟨⟨x, c⟩, hl⟩ =>
    match c with
    | .dataSome dp d =>
      let comb := combineDataRange s x dp d
      (match hsr : compileSolvedRange comb with
      | none => none
      | some sr =>
        if hemp : sr.isEmpty = true then
          some (close fun ⟨i, _, _, hs⟩ => by
            obtain ⟨y, hy, hd⟩ := hs.labels x (.dataSome dp d) hl
            exact sr.isEmpty_sound hemp i y (combineDataRange_sound hs hy hd))
        else match hfin : sr.finiteValues? with
        | some vs =>
          if hexh : vs.all (fun v => s.negDataEdges.contains (dp, x, v)) = true then
            some (close fun ⟨i, _, _, hs⟩ => by
              obtain ⟨y, hy, hd⟩ := hs.labels x (.dataSome dp d) hl
              obtain ⟨v, hv, rfl⟩ := sr.finiteValues?_sound hfin i y (combineDataRange_sound hs hy hd)
              have hneg := List.all_eq_true.mp hexh v hv
              exact hs.negDataEdges dp x v (List.contains_iff_mem.mp hneg) hy)
          else none
        | none => none) <|>
      (if hfunc : dp ∈ p.funcData then
        match hcomp : compile d with
        | none => none
        | some comp =>
          s.dataEdges.attach.findSome? fun ⟨⟨dp', x', v⟩, he⟩ =>
            if hmatch : dp' = dp ∧ x' = x then
              if hfail : comp.holds v = false then
                some (close fun ⟨i, hm, env, hs⟩ => by
                  obtain ⟨y, hy, hd⟩ := hs.labels x (.dataSome dp d) hl
                  have hedge := hmatch.2 ▸ hmatch.1 ▸ hs.dataEdges dp' x' v he
                  have hyEq : y = i.embedValue v := hm.funcData dp hfunc (env x) y _ hy hedge
                  subst hyEq
                  have htrue := (comp.holds_iff i v).mpr hd
                  rw [hfail] at htrue; cases htrue)
              else none
            else none
      else none)
    | .dataMin (n + 1) dp d =>
      let comb := combineDataRange s x dp d
      (match hsr : compileSolvedRange comb with
      | none => none
      | some sr =>
        if hemp : sr.isEmpty = true then
          some (close fun ⟨i, _, _, hs⟩ => by
            obtain ⟨xs, hlen, _, hq⟩ := hs.labels x (.dataMin (n + 1) dp d) hl
            cases xs with
            | nil => simp at hlen
            | cons y _ =>
              have ⟨hy, hd⟩ := hq y (List.mem_cons_self ..)
              exact sr.isEmpty_sound hemp i y (combineDataRange_sound hs hy hd))
        else match hfin : sr.finiteValues? with
        | some vs =>
          let avail := vs.filter (fun v => !s.negDataEdges.contains (dp, x, v))
          if hlt : avail.length < n + 1 then
            some (close fun ⟨i, _, _, hs⟩ => by
              obtain ⟨xs, hlen, hnd, hq⟩ := hs.labels x (.dataMin (n + 1) dp d) hl
              let embed : Value → i.Data := i.embedValue
              have hsub : ∀ y ∈ xs, y ∈ avail.map embed := fun y hy => by
                have ⟨hedge, hd⟩ := hq y hy
                obtain ⟨v, hv, rfl⟩ := sr.finiteValues?_sound hfin i y (combineDataRange_sound hs hedge hd)
                refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hv, ?_⟩)
                cases hneg : s.negDataEdges.contains (dp, x, v)
                · rfl
                · exact (hs.negDataEdges dp x v (List.contains_iff_mem.mp hneg) hedge).elim
              have hle := hnd.length_le_of_subset hsub
              rw [hlen, List.length_map] at hle
              omega)
          else none
        | none => none) <|>
      (if hfunc : dp ∈ p.funcData then
        if hgt : n + 1 ≥ 2 then
          some (close fun ⟨i, hm, env, hs⟩ => by
            obtain ⟨xs, hlen, hnd, hq⟩ := hs.labels x (.dataMin (n + 1) dp d) hl
            cases xs with
            | nil => simp at hlen
            | cons y1 rest =>
              cases rest with
              | nil => simp at hlen; omega
              | cons y2 _ =>
                have h1 := (hq y1 (List.mem_cons_self ..)).1
                have h2 := (hq y2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
                have heq := hm.funcData dp hfunc (env x) y1 y2 h1 h2
                exact (List.nodup_cons.mp hnd).1 (heq ▸ List.mem_cons_self ..))
        else match hcomp : compile d with
        | none => none
        | some comp =>
          s.dataEdges.attach.findSome? fun ⟨⟨dp', x', v⟩, he⟩ =>
            if hmatch : dp' = dp ∧ x' = x then
              if hfail : comp.holds v = false then
                some (close fun ⟨i, hm, env, hs⟩ => by
                  obtain ⟨xs, hlen, _, hq⟩ := hs.labels x (.dataMin (n + 1) dp d) hl
                  cases xs with
                  | nil => simp at hlen
                  | cons y _ =>
                    have ⟨hy, hd⟩ := hq y (List.mem_cons_self ..)
                    have hedge := hmatch.2 ▸ hmatch.1 ▸ hs.dataEdges dp' x' v he
                    have hyEq : y = i.embedValue v := hm.funcData dp hfunc (env x) y _ hy hedge
                    subst hyEq
                    have htrue := (comp.holds_iff i v).mpr hd
                    rw [hfail] at htrue; cases htrue)
              else none
            else none
      else none)
    | _ => none)

private def dataSteps (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  -- 1. Extract dataValue labels into dataEdges / negDataEdges
  (s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    match c with
    | .dataValue dp l true =>
      match hdl : decodeLiteral l with
      | none => none
      | some v =>
        if s.dataEdges.contains (dp, x, v) then none
        else some (deterministic (s.addDataEdge dp x v) fun ⟨i, hm, env, hs⟩ => by
          have hv : i.dataProperties dp (env x) (i.literalValue l) := hs.labels x (.dataValue dp l true) h
          rw [i.lexicalAgreement l v hdl] at hv
          exact ⟨i, hm, env, Branch.addDataEdge_realizes hs hv⟩)
    | .dataValue dp l false =>
      match hdl : decodeLiteral l with
      | none => none
      | some v =>
        if s.negDataEdges.contains (dp, x, v) then none
        else some (deterministic (s.addNegDataEdge dp x v) fun ⟨i, hm, env, hs⟩ => by
          have hv : ¬ i.dataProperties dp (env x) (i.literalValue l) := hs.labels x (.dataValue dp l false) h
          rw [i.lexicalAgreement l v hdl] at hv
          exact ⟨i, hm, env, Branch.addNegDataEdge_realizes hs hv⟩)
    | .dataAll dp d =>
      if s.dataConstraints.contains (x, dp, d) then none
      else some (deterministic (s.addDataConstraint x dp d) fun ⟨i, hm, env, hs⟩ =>
        ⟨i, hm, env, Branch.addDataConstraint_realizes hs (hs.labels x (.dataAll dp d) h)⟩)
    | _ => none) <|>
  -- 2. Propagate global DataPropertyRange axioms to all active nodes
  (p.dataRanges.attach.findSome? fun ⟨⟨dp, d⟩, hdr⟩ =>
    nodes.findSome? fun x =>
      if s.dataConstraints.contains (x, dp, d) then none
      else some (deterministic (s.addDataConstraint x dp d) fun ⟨i, hm, env, hs⟩ =>
        ⟨i, hm, env, Branch.addDataConstraint_realizes hs (hm.dataRanges (dp, d) hdr (env x))⟩)) <|>
  -- 3. Propagate SubDataPropertyOf along observed data edges
  (p.subData.attach.findSome? fun ⟨⟨r, t⟩, hrt⟩ =>
    s.dataEdges.attach.findSome? fun ⟨⟨dp, x, v⟩, he⟩ =>
      if h1 : dp = r then
        if s.dataEdges.contains (t, x, v) then none
        else some (deterministic (s.addDataEdge t x v) fun ⟨i, hm, env, hs⟩ =>
          ⟨i, hm, env, Branch.addDataEdge_realizes hs
            (hm.subData (r, t) hrt (env x) _ (h1 ▸ hs.dataEdges dp x v he))⟩)
      else none) <|>
  -- 4. Propagate universal dataConstraints downward along SubDataPropertyOf
  (p.subData.attach.findSome? fun ⟨⟨r, t⟩, hrt⟩ =>
    s.dataConstraints.attach.findSome? fun ⟨⟨x, dp, d⟩, hc⟩ =>
      if h1 : dp = t then
        if s.dataConstraints.contains (x, r, d) then none
        else some (deterministic (s.addDataConstraint x r d) fun ⟨i, hm, env, hs⟩ =>
          ⟨i, hm, env, Branch.addDataConstraint_realizes hs fun y hy =>
            hs.dataConstraints x dp d hc y (h1 ▸ hm.subData (r, t) hrt (env x) y hy)⟩)
      else none)

/-- Mixed object + data `HasKey` merge rule: if two distinct named nodes `x` and `y`
    satisfy `k.cls` and agree on a named filler for every `r ∈ k.objProps` and a
    decoded value for every `dp ∈ k.dataProps`, merge `max x y` into `min x y`.
    Anonymous individuals (`s.anons`) are intentionally excluded per OWL 2 Direct Semantics. -/
private def keyMerge (p : Problem) (s : Branch) : Option (Transition p s) :=
  p.keys.attach.findSome? fun ⟨k, hk⟩ =>
    s.noms.attach.findSome? fun ⟨⟨a, x⟩, hx⟩ =>
      if hkx : s.known x k.cls then
        s.noms.attach.findSome? fun ⟨⟨b, y⟩, hy⟩ =>
          if hxy : x ≠ y then
            if hky : s.known y k.cls then
              let objOk := k.objProps.all fun r =>
                s.noms.any fun (_, z) => s.edge r x z && s.edge r y z
              let dataOk := k.dataProps.all fun dp =>
                s.dataEdges.any fun (r, n, v) =>
                  r == dp && n == x && s.dataEdges.contains (dp, y, v)
              if hok : objOk = true ∧ dataOk = true then
                let keep := min x y
                let drop := max x y
                some (deterministic (s.merge keep drop) fun ⟨i, hm, env, hs⟩ => by
                  have hnx : i.named (env x) := hs.noms a x hx ▸ i.namedIndividual a
                  have hny : i.named (env y) := hs.noms b y hy ▸ i.namedIndividual b
                  have ho : ∀ r ∈ k.objProps, ∃ z, i.named z ∧
                      holdsOriented i r (env x) z ∧ holdsOriented i r (env y) z := by
                    intro r hr
                    have h1 := List.all_eq_true.mp hok.1 r hr
                    obtain ⟨⟨c, z⟩, hz, hboth⟩ := List.any_eq_true.mp h1
                    obtain ⟨hxz, hyz⟩ := Bool.and_eq_true_iff.mp hboth
                    exact ⟨env z, hs.noms c z hz ▸ i.namedIndividual c,
                      Branch.edge_sound hs hxz, Branch.edge_sound hs hyz⟩
                  have hd : ∀ dp ∈ k.dataProps, ∃ z,
                      i.dataProperties dp (env x) z ∧ i.dataProperties dp (env y) z := by
                    intro dp hdp
                    have h1 := List.all_eq_true.mp hok.2 dp hdp
                    obtain ⟨⟨r, n, v⟩, hmem, hcond⟩ := List.any_eq_true.mp h1
                    obtain ⟨⟨hr, hn⟩, hcy⟩ := Bool.and_eq_true_iff.mp hcond |>.imp_left Bool.and_eq_true_iff.mp
                    have hr' := beq_iff_eq.mp hr
                    have hn' := beq_iff_eq.mp hn
                    subst hr' hn'
                    exact ⟨i.embedValue v, hs.dataEdges r n v hmem,
                      hs.dataEdges r y v (List.contains_iff_mem.mp hcy)⟩
                  have heqxy : env x = env y :=
                    hm.keys k hk (env x) (env y) (Branch.known_sound hs hkx)
                      (Branch.known_sound hs hky) hnx hny ho hd
                  have heq : env keep = env drop := by
                    by_cases hle : x ≤ y
                    · simp only [keep, drop, Nat.min_eq_left hle, Nat.max_eq_right hle]; exact heqxy
                    · have hlt : y ≤ x := Nat.le_of_not_le hle
                      simp only [keep, drop, Nat.min_eq_right hlt, Nat.max_eq_left hlt]; exact heqxy.symm
                  exact ⟨i, hm, env, Branch.merge_realizes hs heq⟩)
              else none
            else none
          else none
      else none

private def hierarchy (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  p.rules.attach.findSome? fun ⟨(r, t), h⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hs : s.edge r x y then
        if s.edge t x y then none
        else some (addEdge t x y fun _ env hm he => hm.rules (r, t) h (env x) (env y) (Branch.edge_sound he hs))
      else none

private def chains (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  p.chains.attach.findSome? fun ⟨c, hc⟩ =>
    nodes.findSome? fun x =>
      (s.targets x c.body).attach.findSome? fun ⟨y, hy⟩ =>
        if s.edge (c.head, false) x y then none
        else some (addEdge (c.head, false) x y fun _ env hm hs =>
          hm.chains c hc (env x) (env y) (Branch.targets_sound hs hy))

private def localLabels (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .conj a b =>
      if !s.known x a then some (add x a fun _ _ _ hs => (hs.labels x (.conj a b) h).1)
      else if !s.known x b then some (add x b fun _ _ _ hs => (hs.labels x (.conj a b) h).2)
      else none
    | .all r c =>
      nodes.findSome? fun y =>
        if he : s.edge r x y then
          if s.known y c then none
          else some (add y c fun _ env _ hs => hs.labels x (.all r c) h (env y) (Branch.edge_sound hs he))
        else none
    | _ => none

private def deterministicGCI (p : Problem) (s : Branch) (nodes : List Nat)
    (absorb : Bool := false) :
    Option (Transition p s) :=
  nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if s.known x q.sup then none
    else if hp : (q.sub.triggeringPremises (s.known x) absorb).isSome then
      let support := (q.sub.triggeringPremises (s.known x) absorb).get hp
      some (add x q.sup
        (fun i env hm hs => hm.tbox q hq (env x) (support.property.2 i (env x)
          (fun c hc => Branch.known_sound hs (support.property.1 c hc)))))
    else none

private def disjunctions (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .disj a b =>
      if s.known x a || s.known x b then none
      else if ha : s.known x a.dual then
        some (add x b fun i env _ hs =>
          (hs.labels x (.disj a b) h).resolve_left ((holds_dual i (env x) a).mp (Branch.known_sound hs ha)))
      else if hb : s.known x b.dual then
        some (add x a fun i env _ hs =>
          (hs.labels x (.disj a b) h).resolve_right ((holds_dual i (env x) b).mp (Branch.known_sound hs hb)))
      else some (select x a b fun _ _ _ hs => hs.labels x (.disj a b) h)
    | _ => none

private def splitClass {p : Problem} {s : Branch} (x : Nat) (a : Concept) : Transition p s :=
  select x a a.dual fun i env _ _ => by
    classical
    rcases Classical.em (holds i (env x) a) with h | h
    · exact Or.inl h
    · exact Or.inr ((holds_dual i (env x) a).mpr h)

private def undecidedGCI (p : Problem) (s : Branch) (nodes : List Nat)
    (deferAbsorbed : Bool := false) :
    Option (Transition p s) :=
  nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if s.known x q.sup || s.known x q.sub.dual ||
        (deferAbsorbed && q.sub.absorptionPremises.isSome) then none
    else some (select x q.sub.dual q.sup (fun i env hm _ => by
      classical
      rcases Classical.em (holds i (env x) q.sub) with ha | ha
      · exact Or.inr (hm.tbox q hq (env x) ha)
      · exact Or.inl ((holds_dual i (env x) q.sub).mpr ha)))

private def qualifiers (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  s.labels.findSome? fun (x, c) =>
    match c with
    | .max _ r body =>
      nodes.findSome? fun y =>
        if s.edge r x y && !(s.known y body || s.known y body.dual) then
          some (splitClass y body)
        else none
    | _ => none

private def mergeChoices {p : Problem} {s : Branch} {x n : Nat} {r : OrientedRole} {c : Concept}
    (label : (x, .max n r c) ∈ s.labels) (nodes : List Nat)
    (hlen : nodes.length = n + 1) (hn : nodes.Nodup)
    (qualified : ∀ y ∈ nodes, s.edge r x y = true ∧ s.known y c = true) :
    Transition p s :=
  let pairs := (distinctPairs nodes).filter fun (a, b) => decide (a < b)
  ⟨pairs.map (fun (a, b) => s.merge a b), fun hs => by
    obtain ⟨i, hm, env, h⟩ := hs
    have he (y : Nat) (hy : y ∈ nodes) : holdsOriented i r (env x) (env y) ∧ holds i (env y) c :=
      ⟨Branch.edge_sound h (qualified y hy).1, Branch.known_sound h (qualified y hy).2⟩
    obtain ⟨a, ha, b, hb, hab, heq⟩ :=
      exists_equal_witnesses hlen hn he (h.labels x (.max n r c) label)
    have takePair (a b : Nat) (ha : a ∈ nodes) (hb : b ∈ nodes) (hlt : a < b)
        (he : env a = env b) : ∃ t ∈ pairs.map (fun (a, b) => s.merge a b), t.Sat p := by
      have hp : (a, b) ∈ pairs := List.mem_filter.mpr
        ⟨mem_distinctPairs.mpr ⟨ha, hb, Nat.ne_of_lt hlt⟩, decide_eq_true hlt⟩
      exact ⟨s.merge a b, List.mem_map.mpr ⟨(a, b), hp, rfl⟩, i, hm, env,
        Branch.merge_realizes h he⟩
    exact (Nat.lt_or_gt_of_ne hab).elim (fun hlt => takePair a b ha hb hlt heq)
      (fun hlt => takePair b a hb ha hlt heq.symm)⟩

private def upperBounds (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .max n r body =>
      let qualified := s.nodes.filter fun y => s.edge r x y && s.known y body
      if hn : n + 1 ≤ qualified.length then
        let ys := qualified.take (n + 1)
        some (mergeChoices h ys (List.length_take_of_le hn)
          ((List.take_sublist ..).nodup (List.filter_sublist.nodup s.nodes_nodup))
          (fun _ hy => Bool.and_eq_true_iff.mp ((List.mem_filter.mp (List.mem_of_mem_take hy)).2)))
      else none
    | _ => none

private def witnesses (p : Problem) (s : Branch) (nodes : List Nat) (maxNodes : Nat) :
    Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    if s.expanded.contains (x, c) then none
    else match c with
    | .some r body =>
      if nodes.any (fun y => s.edge r x y && s.known y body) then none
      else some (deterministic (s.allocate x r body (.some r body) 1 false)
        fun ⟨i, hm, env, hs⟩ => by
          obtain ⟨y, hy⟩ := hs.labels x (.some r body) h
          obtain ⟨env', hh⟩ := Branch.allocate_sound hs (mark := .some r body) 1 false [y] rfl
            (by simp) (by simpa) (Branch.label_support h)
          exact ⟨i, hm, env', hh⟩)
    | .min (n + 1) r body =>
      if n + 1 > maxNodes then none else
      some (deterministic (s.allocate x r body (.min (n + 1) r body) (n + 1) true)
        fun ⟨i, hm, env, hs⟩ => by
          obtain ⟨values, hln, hnd, hq⟩ := hs.labels x (.min (n + 1) r body) h
          obtain ⟨env', hh⟩ := Branch.allocate_sound hs (mark := .min (n + 1) r body)
            (n + 1) true values hln (fun _ => hnd) hq (Branch.label_support h)
          exact ⟨i, hm, env', hh⟩)
    | _ => none

def next (p : Problem) (s : Branch) (maxNodes : Nat) (deferAbsorbed : Bool := false) :
    Option (Transition p s) :=
  let nodes := s.nodes
  inequalityClash p s <|> labelClash p s <|> negEdgeClash p s <|> dataClash p s <|>
    nominalMerge p s <|> keyMerge p s <|> selfSteps p s <|>
    roleCharSteps p s nodes <|> dataSteps p s nodes <|> localLabels p s nodes <|>
    hierarchy p s nodes <|> chains p s nodes <|> deterministicGCI p s nodes deferAbsorbed <|>
    disjunctions p s <|> upperBounds p s <|> witnesses p s nodes maxNodes <|>
    qualifiers p s nodes <|> undecidedGCI p s nodes deferAbsorbed

/-- Untrusted witness generator for data existential/cardinality labels during
    finite model proposal. All proposed models are verified by `checkModel`. -/
private def candidateValues (sr : SolvedRange r) (count : Nat) : List Value :=
  match sr.finiteValues? with
  | some vs => vs
  | none =>
    match sr with
    | .finite f => f.values
    | .intInterval iv =>
      let base : Int := match iv.bounds.lower, iv.bounds.upper with
        | some lo, _ => lo
        | none, some hi => hi - Int.ofNat count
        | none, none => 0
      (List.range (count + 8)).map fun k => Value.integer (base + Int.ofNat k)
    | .ratInterval rv =>
      let base : Int := match rv.bounds.lower, rv.bounds.upper with
        | some b, _ => b.1.num / b.1.den + 1
        | none, some b => b.1.num / b.1.den - Int.ofNat count - 1
        | none, none => 0
      (List.range (count + 8)).map fun k => Value.integer (base + Int.ofNat k)
    | .stringInterval sv =>
      let lo := sv.bounds.minLen
      (List.range (count + 8)).map fun k =>
        let ch := Char.ofNat (97 + (k % 26))
        Value.string (String.ofList (List.replicate lo ch ++ if k < 26 then [] else [Char.ofNat (48 + k / 26)]))

private def closeSubDataEdges {n : Nat} (subData : List (IRI × IRI))
    (edges : List (IRI × Fin n × Value)) : List (IRI × Fin n × Value) := Id.run do
  let mut acc := edges.eraseDups
  let mut changed := true
  let mut iter := 0
  while changed && iter < subData.length + 2 do
    changed := false
    iter := iter + 1
    let mut additions : List (IRI × Fin n × Value) := []
    for (r, t) in subData do
      for (dp, w, v) in acc do
        if dp == r && !acc.contains (t, w, v) && !additions.contains (t, w, v) then
          additions := (t, w, v) :: additions
          changed := true
    acc := additions ++ acc
  return acc.eraseDups

private def extractDataRangeHints : DataRange → List Value
  | .datatype _ => []
  | .complement r => extractDataRangeHints r
  | .intersection a b | .union a b => extractDataRangeHints a ++ extractDataRangeHints b
  | .oneOf ls => ls.filterMap decodeLiteral
  | .restriction _ fs =>
    fs.flatMap fun f =>
      let bVal := match decodeLiteral f.bound with
        | some (.number q) =>
          [Value.number q, Value.number (q + 1), Value.number (q - 1),
           Value.number (q + mkRat 1 2), Value.number (q - mkRat 1 2)]
        | some (.float (.finite q)) =>
          [Value.float (.finite q), Value.float (.finite (q + 1)), Value.float (.finite (q - 1))]
        | some (.double (.finite q)) =>
          [Value.double (.finite q), Value.double (.finite (q + 1)), Value.double (.finite (q - 1))]
        | some (.dateTime dt) =>
          [Value.dateTime dt,
           Value.dateTime { dt with epochSeconds := dt.epochSeconds + 1 },
           Value.dateTime { dt with epochSeconds := dt.epochSeconds - 1 }]
        | some v => [v]
        | none => []
      let patVal := if f.name == "http://www.w3.org/2001/XMLSchema#pattern" then
          match samplePattern f.bound.lexical with
          | some s => [Value.string s, Value.anyURI s]
          | none => []
        else if f.name == "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange" then
          let tag := if f.bound.lexical == "*" || f.bound.lexical.isEmpty then "en" else f.bound.lexical.toLower
          [Value.plainLiteral "a" tag, Value.plainLiteral "item" tag]
        else []
      bVal ++ patVal

/-- Broad candidate pool covering all 33 OWL 2 DL datatype families (`xsd:float`,
    `xsd:double`, `xsd:dateTime`, `xsd:dateTimeStamp`, `xsd:hexBinary`,
    `xsd:base64Binary`, `xsd:anyURI`, `rdf:XMLLiteral`, `rdf:PlainLiteral`,
    string subtypes, `xsd:pattern`, `rdf:langRange`, numeric, and boolean) for
    untrusted finite-model witness proposal (always checked by `checkModel`). -/
private def fallbackCandidates (d : DataRange) (count : Nat) : List Value :=
  let hints := extractDataRangeHints d
  let ks := List.range (count + 4)
  let ints := ks.map fun k => Value.integer (Int.ofNat k)
  let strs := [Value.string "en", Value.string "a", Value.string "item", Value.string ""] ++
    ks.map (fun k => Value.string s!"a{k}")
  let langs := ks.map (fun k => Value.plainLiteral s!"a{k}" "en") ++
    [Value.plainLiteral "a" "en-us", Value.plainLiteral "a" "fr"]
  let floats := ks.map (fun k => Value.float (.finite (Rat.ofInt (Int.ofNat k + 1)))) ++
    [Value.float .posZero, Value.float .negZero]
  let doubles := ks.map (fun k => Value.double (.finite (Rat.ofInt (Int.ofNat k + 1)))) ++
    [Value.double .posZero, Value.double .negZero]
  let dts := ks.map (fun k => Value.dateTime ⟨Rat.ofInt (Int.ofNat k * 3600), some 0⟩) ++
    ks.map (fun k => Value.dateTime ⟨Rat.ofInt (Int.ofNat k * 3600), none⟩)
  let bins := ks.map (fun k => Value.hexBinary (List.replicate k (UInt8.ofNat (k + 1)))) ++
    ks.map (fun k => Value.base64Binary (List.replicate k (UInt8.ofNat (k + 1))))
  let uris := ks.map (fun k => Value.anyURI s!"http://example.org/{k}")
  let xmls := ks.map (fun k => Value.xmlLiteral s!"<x{k}></x{k}>")
  let bools := [Value.boolean false, Value.boolean true]
  (hints ++ ints ++ strs ++ langs ++ floats ++ doubles ++ dts ++ bins ++ uris ++ xmls ++ bools).eraseDups

private def completeDataEdges (p : Problem) (s : Branch)
    (index : Nat → Option (Fin (s.nodes.length - 1 + 1))) :
    List (IRI × Fin (s.nodes.length - 1 + 1) × Value) := Id.run do
  let mut edges := s.dataEdges.filterMap fun (dp, x, v) => (index x).map (dp, ·, v)
  for (x, c) in s.labels do
    let some wx := index x | continue
    let req : Option (IRI × DataRange × Nat) := match c with
      | .dataSome dp d => some (dp, d, 1)
      | .dataMin (n + 1) dp d => some (dp, d, n + 1)
      | _ => none
    let some (dp, d, need) := req | continue
    let comb := combineDataRange s x dp d
    let some comp := compile comb | continue
    let existing := (edges.filterMap fun (r, w, v) =>
      if r == dp && w == wx && comp.holds v then some v else none).eraseDups
    if existing.length >= need then continue
    let mut added := existing.length
    let srCands := match compileSolvedRange comb with
      | some sr => candidateValues sr (need + 4)
      | none => []
    for v in srCands do
      if added >= need then break
      if comp.holds v && !s.negDataEdges.contains (dp, x, v) &&
         !edges.contains (dp, wx, v) then
        edges := (dp, wx, v) :: edges
        added := added + 1
    if added < need then
      for v in fallbackCandidates comb (need + 4) do
        if added >= need then break
        if comp.holds v && !s.negDataEdges.contains (dp, x, v) &&
           !edges.contains (dp, wx, v) then
          edges := (dp, wx, v) :: edges
          added := added + 1
  return closeSubDataEdges p.subData edges

private def toModel (p : Problem) (s : Branch) : SROIQDModel :=
  let nodes := s.nodes
  let additional := nodes.length - 1
  let index := fun a =>
    let n := nodes.idxOf a
    if h : n < additional + 1 then some (⟨n, h⟩ : Fin (additional + 1)) else none
  let g : Graph :=
    ⟨additional,
     s.labels.filterMap fun
      | (n, .lit c true) => (index n).map (c, ·)
      | _ => none,
     s.edges.filterMap fun (r, a, b) => do
      return (r, ← index a, ← index b)⟩
  ⟨g,
   s.noms.filterMap fun (a, n) => (index n).map (a, ·),
   s.anons.filterMap fun (k, n) => (index n).map (k, ·),
   completeDataEdges p s index⟩

/-- Compute the label set of a node for pairwise/subset blocking. -/
private def nodeLabels (s : Branch) (x : Nat) : List Concept :=
  (s.labels.filterMap fun (n, c) => if n == x then some c else none).eraseDups

private def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private def pairEdgeRoles (s : Branch) (x y : Nat) : List IRI :=
  (s.edges.filterMap fun (r, a, b) => if a == x && b == y then some r else none).eraseDups

private def isFixedNode (s : Branch) (x : Nat) : Bool :=
  (s.noms.any fun (_, n) => n == x) || (s.anons.any fun (_, n) => n == x)

/-- Find a pairwise blocker `y' < y` for a non-fixed edge `(x, y)` (Horrocks-Sattler
    pairwise blocking: matching labels on `x`/`x'` and `y`/`y'`, matching forward/backward
    roles, and matching data constraints on `y`/`y'`). -/
private def pairwiseBlocker (s : Branch) (y : Nat) : Option Nat := Id.run do
  if isFixedNode s y then return none
  let ly := nodeLabels s y
  let dcy := (s.dataConstraints.filterMap fun (n, dp, d) => if n == y then some (dp, d) else none).eraseDups
  let parents := (s.edges.filterMap fun (_, x, b) => if b == y && x < y then some x else none).eraseDups
  for x in parents do
    let lx := nodeLabels s x
    let fwd := pairEdgeRoles s x y
    let bwd := pairEdgeRoles s y x
    for y' in s.nodes do
      if y' >= y || isFixedNode s y' then continue
      if !sameSet ly (nodeLabels s y') then continue
      let dcy' := (s.dataConstraints.filterMap fun (n, dp, d) => if n == y' then some (dp, d) else none).eraseDups
      if !sameSet dcy dcy' then continue
      let parents' := (s.edges.filterMap fun (_, x', b') => if b' == y' && x' < y' then some x' else none).eraseDups
      for x' in parents' do
        if sameSet lx (nodeLabels s x') &&
           sameSet fwd (pairEdgeRoles s x' y') &&
           sameSet bwd (pairEdgeRoles s y' x') then
          return some y'
  return none

/-- Find an earlier node `y' < y` whose labels and data constraints are a superset
    of `y`'s (for cyclic leaf quotienting, including root `0` for inverse-functional cycles). -/
private def subsetBlocker (s : Branch) (y : Nat) : Option Nat := Id.run do
  if isFixedNode s y then return none
  let ly := nodeLabels s y
  let dcy := (s.dataConstraints.filterMap fun (n, dp, d) => if n == y then some (dp, d) else none).eraseDups
  for y' in s.nodes do
    if y' >= y || isFixedNode s y' then continue
    let ly' := nodeLabels s y'
    if ly.all (ly'.contains ·) then
      let dcy' := (s.dataConstraints.filterMap fun (n, dp, d) => if n == y' then some (dp, d) else none).eraseDups
      if dcy.all (dcy'.contains ·) then return some y'
  return none

/-- Apply a blocking redirect map `redirect` (dropping redirected nodes and rewiring
    all incident edges to their blockers) to propose a compact finite model. -/
private def buildQuotientModel (p : Problem) (s : Branch) (redirects : List (Nat × Nat)) : Option SROIQDModel :=
  if redirects.isEmpty then none
  else
    let remap (n : Nat) : Nat := (redirects.lookup n).getD n
    let kept := s.nodes.filter fun n => (redirects.lookup n).isNone
    if kept.isEmpty then none
    else
      let additional := kept.length - 1
      let index := fun a =>
        let n := kept.idxOf (remap a)
        if h : n < additional + 1 then some (⟨n, h⟩ : Fin (additional + 1)) else none
      let g : Graph :=
        ⟨additional,
         (s.labels.filterMap fun
          | (n, .lit c true) => if (redirects.lookup n).isNone then (index n).map (c, ·) else none
          | _ => none).eraseDups,
         (s.edges.filterMap fun (r, a, b) => do
            return (r, ← index (remap a), ← index (remap b))).eraseDups⟩
      let noms := (s.noms.filterMap fun (a, n) => (index (remap n)).map (a, ·)).eraseDups
      let anons := (s.anons.filterMap fun (k, n) => (index (remap n)).map (k, ·)).eraseDups
      let sQuot : Branch := { s with
        labels := s.labels.filter fun (n, _) => (redirects.lookup n).isNone
        dataEdges := s.dataEdges.filter fun (_, n, _) => (redirects.lookup n).isNone
        negDataEdges := s.negDataEdges.filter fun (_, n, _) => (redirects.lookup n).isNone
        dataConstraints := s.dataConstraints.filter fun (n, _, _) => (redirects.lookup n).isNone }
      let dEdges := Id.run do
        let mut edges := sQuot.dataEdges.filterMap fun (dp, x, v) => (index x).map (dp, ·, v)
        for (x, c) in sQuot.labels do
          let some wx := index x | continue
          let req : Option (IRI × DataRange × Nat) := match c with
            | .dataSome dp d => some (dp, d, 1)
            | .dataMin (n + 1) dp d => some (dp, d, n + 1)
            | _ => none
          let some (dp, d, need) := req | continue
          let comb := combineDataRange sQuot x dp d
          let some comp := compile comb | continue
          let existing := (edges.filterMap fun (r, w, v) =>
            if r == dp && w == wx && comp.holds v then some v else none).eraseDups
          if existing.length >= need then continue
          let mut added := existing.length
          let srCands := match compileSolvedRange comb with
            | some sr => candidateValues sr (need + 4)
            | none => []
          for v in srCands do
            if added >= need then break
            if comp.holds v && !sQuot.negDataEdges.contains (dp, x, v) &&
               !edges.contains (dp, wx, v) then
              edges := (dp, wx, v) :: edges
              added := added + 1
          if added < need then
            for v in fallbackCandidates comb (need + 4) do
              if added >= need then break
              if comp.holds v && !sQuot.negDataEdges.contains (dp, x, v) &&
                 !edges.contains (dp, wx, v) then
                edges := (dp, wx, v) :: edges
                added := added + 1
        return closeSubDataEdges p.subData edges
      some ⟨g, noms, anons, dEdges⟩

/-- Propose finite quotient models via pairwise blocking and cyclic leaf blocking.
    Every returned model is verified by `checkModel` before acceptance. -/
private def toBlockedModels (p : Problem) (s : Branch) : List SROIQDModel :=
  let pairRedirs := s.nodes.filterMap fun y => (pairwiseBlocker s y).map (y, ·)
  let leafRedirs := s.nodes.filterMap fun y =>
    if s.edges.any (fun (_, a, b) => a == y && b > y) then none
    else (subsetBlocker s y).map (y, ·)
  ([buildQuotientModel p s pairRedirs, buildQuotientModel p s leafRedirs]).filterMap id

structure Limits where
  worlds : Nat := 16
  depth : Nat := 256
  visits : Nat := 20000

/-- Convert the default allowance for additional live worlds into the absolute
    cap used by search and certificate replay. Initialization assigns a world
    to the query root and to each named and anonymous individual. -/
def Limits.forProblem (p : Problem) (extra : Limits := {}) : Limits :=
  { extra with worlds := 1 + p.nominals.length + p.anons.length + extra.worlds }

inductive Evidence where
  | model (model : SROIQDModel)
  | refutation (depth : Nat)

def Evidence.isModel : Evidence → Bool
  | .model _ => true
  | .refutation _ => false

def checkClosed (p : Problem) (maxNodes : Nat) : Nat → Branch → Bool
  | 0, _ => false
  | depth + 1, s =>
    match next p s maxNodes with
    | none => false
    | some t => t.branches.all (checkClosed p maxNodes depth)

theorem checkClosed_sound {p : Problem} {maxNodes depth : Nat} {s : Branch}
    (h : checkClosed p maxNodes depth s = true) : ¬ s.Sat p := by
  induction depth generalizing s with
  | zero => cases h
  | succ n ih =>
    intro hs
    simp only [checkClosed] at h
    split at h
    · contradiction
    · rename_i t _
      obtain ⟨u, hu, hmodel⟩ := t.preserves hs
      exact ih (List.all_eq_true.mp h u hu) hmodel

private def provedClash {p : Problem} (s : Branch) (clash : NodeClash p) :
    Option { _c : NodeClash p // ¬ s.Sat p } :=
  if h : clash.premises.all (s.known clash.node) then
    some ⟨clash, fun ⟨i, hm, env, hs⟩ =>
      clash.sound i hm (env clash.node) fun c hc =>
        Branch.known_sound hs (List.all_eq_true.mp h c hc)⟩
  else none

private def explainLocalLabel (p : Problem) (s : Branch) (x : Nat) (c : Concept) :
    Option (LocalLabelRule p) :=
  (s.labels.findSome? fun (y, label) =>
    if x != y then none
    else match label with
    | .conj a b =>
      if h : c = a then
        some (.unary x [.conj a b] c fun _ _ _ hp => h.symm ▸ (hp (.conj a b) (by simp)).1)
      else if h : c = b then
        some (.unary x [.conj a b] c fun _ _ _ hp => h.symm ▸ (hp (.conj a b) (by simp)).2)
      else none
    | .disj a b =>
      if h : c = b ∧ s.known x a.dual = true then
        some (.unary x [.disj a b, a.dual] c fun i _ z hp => h.1.symm ▸
          (hp (.disj a b) (by simp)).resolve_left ((holds_dual i z a).mp (hp a.dual (by simp))))
      else if h : c = a ∧ s.known x b.dual = true then
        some (.unary x [.disj a b, b.dual] c fun i _ z hp => h.1.symm ▸
          (hp (.disj a b) (by simp)).resolve_right ((holds_dual i z b).mp (hp b.dual (by simp))))
      else none
    | _ => none) <|>
  (p.tbox.attach.findSome? fun ⟨q, hq⟩ => do
    if h : c = q.sup then
      let support ← q.sub.triggeringPremises (s.known x)
      return .unary x support.val c fun i hm z hp => h.symm ▸ hm.tbox q hq z (support.property.2 i z hp)
    else none)

private def explainLocalChoice (p : Problem) (s : Branch) (x : Nat) (a b : Concept) :
    Option (LocalLabelRule p) :=
  if b == a.dual then some (.split p x a)
  else if s.known x (.disj a b) then
    some (.binary x [.disj a b] a b fun _ _ _ hp => hp (.disj a b) (by simp))
  else p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if q.sub.dual == a && q.sup == b then some (.gci x q hq) else none

/-- Explain closures only when the conflict contains a label newly introduced
    at the head of the child branch. More involved transitions keep their
    ordinary refutation without a reusable dependency set. -/
private def probeClash {p : Problem} (s : Branch) (children : List Branch)
    (clashes : List (Option (NodeClash p))) : Option (NodeClash p) := do
  let newLabel := fun (child : Branch) (clash : NodeClash p) => do
    let (x, c) ← child.labels.head?
    if x == clash.node && !s.known x c && clash.premises.contains c then some c else none
  match children, clashes with
  | [], [] =>
    s.labels.findSome? fun (x, c) =>
      if c == .bottom then some (.bottom p x)
      else if s.known x c.dual then some (.dual p x c)
      else none
  | [child], [some clash] =>
    let c ← newLabel child clash
    let rule ← explainLocalLabel p s clash.node c
    rule.resolve clashes
  | [left, right], [some a, some b] =>
    if a.node != b.node then none else
      let first ← newLabel left a
      let second ← newLabel right b
      let rule ← explainLocalChoice p s a.node first second
      rule.resolve clashes
  | _, _ => none

private inductive ProbeVerdict (p : Problem) (s : Branch) where
  | model (witness : SROIQDModel)
  | closed (depth : Nat) (clash : Option (NodeClash p)) (refutes : ¬ s.Sat p)
  | unknown

private inductive ProbeBranches (p : Problem) (s : Branch) (xs : List Branch) where
  | model (witness : SROIQDModel)
  | jump (depth : Nat) (clash : { _c : NodeClash p // ¬ s.Sat p })
  | closed (depth : Nat) (clashes : List (Option (NodeClash p)))
      (refutes : ∀ b ∈ xs, ¬ b.Sat p)
  | unknown

private def probeBranches {p : Problem} (s : Branch)
    (visit : (b : Branch) → Option Nat → ProbeVerdict p b × Option Nat) :
    (xs : List Branch) → Option Nat → ProbeBranches p s xs × Option Nat
  | [], fuel => (.closed 0 [] (fun _ h => nomatch h), fuel)
  | b :: bs, fuel =>
    let (answer, fuel) := visit b fuel
    match answer with
    | .model m => (.model m, fuel)
    | .closed depth clue refutes =>
      if let some jump := clue.bind (provedClash s) then
        (.jump depth jump, fuel)
      else
        let (tail, fuel) := probeBranches s visit bs fuel
        match tail with
        | .model m => (.model m, fuel)
        | .jump d jump => (.jump d jump, fuel)
        | .closed d clues refutesTail =>
          (.closed (max depth d) (clue :: clues) (fun branch h => by
            rcases List.mem_cons.mp h with rfl | h
            · exact refutes
            · exact refutesTail branch h), fuel)
        | .unknown => (.unknown, fuel)
    | .unknown =>
      if fuel == some 0 then (.unknown, fuel)
      else
        let (tail, fuel) := probeBranches s visit bs fuel
        match tail with
        | .model m => (.model m, fuel)
        | .jump d jump => (.jump d jump, fuel)
        | .closed .. | .unknown => (.unknown, fuel)

private def tryBranchModel (p : Problem) (s : Branch) : Option SROIQDModel :=
  let m := toModel p s
  if checkModel p m then some m else (toBlockedModels p s).find? (checkModel p)

private def probe (p : Problem) (maxNodes : Nat) (searchModels : Bool) :
    Nat → (s : Branch) → Option Nat → ProbeVerdict p s × Option Nat
  | 0, _, fuel => (.unknown, fuel)
  | _ + 1, _, some 0 => (.unknown, some 0)
  | depth + 1, s, fuel => Id.run do
    let fuel := fuel.map (· - 1)
    if searchModels && s.nodes.length > maxNodes then return (.unknown, fuel)
    let step := next p s maxNodes (deferAbsorbed := true)
    -- The model checker tests every original GCI. An inactive antecedent
    -- needs a split only if the candidate model cannot discharge it.
    if step.isNone && searchModels then
      if let some m := tryBranchModel p s then return (.model m, fuel)
    let some t := step <|> undecidedGCI p s s.nodes | return (.unknown, fuel)
    let tryEarlyModel := match t.branches with
      | [] => false
      | [u] => u.nodes.length > s.nodes.length
      | _ => true
    if searchModels && step.isSome && tryEarlyModel then
      if let some m := tryBranchModel p s then return (.model m, fuel)
    let (result, remaining) := probeBranches s (probe p maxNodes searchModels depth) t.branches fuel
    match result with
    | .model m => return (.model m, remaining)
    | .unknown => return (.unknown, remaining)
    | .jump d clash => return (.closed (d + 1) (some clash.val) clash.property, remaining)
    | .closed d clashes refutes =>
      let learned := probeClash s t.branches clashes
      return (.closed (d + 1) learned (fun hs => by
        obtain ⟨b, hb, hsat⟩ := t.preserves hs
        exact refutes b hb hsat), remaining)

def checkEvidence (p : Problem) (maxNodes : Nat) : Evidence → Bool
  | .model m => checkModel p m
  | .refutation d =>
    match initial p with
    | some s =>
      match (probe p maxNodes false d s none).1 with
      | .closed .. => true
      | _ => checkClosed p maxNodes d s
    | none => false

def evidenceClaim (p : Problem) (e : Evidence) : Prop :=
  if e.isModel then p.Sat else ¬ p.Sat

theorem checkEvidence_sound {p : Problem} {maxNodes : Nat} {e : Evidence}
    (h : checkEvidence p maxNodes e = true) : evidenceClaim p e := by
  cases e with
  | model m => exact checkModel_sound h
  | refutation depth =>
    simp only [checkEvidence] at h
    cases hi : initial p with
    | none => simp [hi] at h
    | some s =>
      simp only [hi] at h
      split at h
      · exact fun hp => ‹¬ s.Sat p› (initial_sat hi hp)
      · exact fun hp => checkClosed_sound h (initial_sat hi hp)

def propose (p : Problem) (limits : Limits) : Option Evidence :=
  match initial p with
  | none => none
  | some s =>
    match (probe p limits.worlds true limits.depth s (some limits.visits)).1 with
    | .model m => some (.model m)
    | .closed depth .. => some (.refutation depth)
    | .unknown => none

/-- Certified ontology consistency over OWL 2 Direct Semantics (`datatypeMap`). -/
def checkConsistency (p : Problem) (maxNodes : Nat) (e : Evidence) : Bool :=
  p.checkSimple && (p.root == .top) && checkEvidence p maxNodes e

theorem checkConsistency_sound {p : Problem} {maxNodes : Nat} {e : Evidence}
    (h : checkConsistency p maxNodes e = true) :
    (∀ r ∈ p.simpleRoles, RoleChains.SimpleRoles.Simple p.rules p.chains r) ∧
      if e.isModel then Satisfiable datatypeMap p.toOntology
      else ¬ Satisfiable datatypeMap p.toOntology := by
  simp only [checkConsistency, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨hsim, hroot⟩, hev⟩
  refine ⟨Problem.checkSimple_iff.mp hsim, ?_⟩
  have hc := checkEvidence_sound hev
  rw [satisfiable_iff_sat p hroot]
  exact hc

structure InclusionEvidence where
  counterexample : Evidence
  inclusion : Evidence

def InclusionEvidence.verdict (e : InclusionEvidence) : InclusionVerdict :=
  match e.counterexample.isModel, e.inclusion.isModel with
  | false, true => .entailed
  | true, false => .refuted
  | true, true => .independent
  | false, false => .inconsistent

def counterProblem (p : Problem) (q : Inclusion) : Problem :=
  { p with root := .conj q.sub q.sup.dual }

def inclusionProblem (p : Problem) (q : Inclusion) : Problem :=
  { p with tbox := q :: p.tbox, root := .top }

def checkInclusion (p : Problem) (q : Inclusion) (maxNodes : Nat) (e : InclusionEvidence) : Bool :=
  q.sub.hasNoAnon && q.sup.hasNoAnon &&
  (inclusionProblem p q).checkSimple &&
  checkEvidence (counterProblem p q) maxNodes e.counterexample &&
  checkEvidence (inclusionProblem p q) maxNodes e.inclusion

def verdictClaim (p : Problem) (q : Inclusion) : InclusionVerdict → Prop
  | .entailed => Satisfiable datatypeMap p.toOntology ∧
      Entails datatypeMap p.toOntology [.subClassOf q.sub.toClassExpr q.sup.toClassExpr]
  | .refuted => Satisfiable datatypeMap p.toOntology ∧
      ¬ Satisfiable datatypeMap (inclusionProblem p q).toOntology
  | .independent => ¬ Entails datatypeMap p.toOntology [.subClassOf q.sub.toClassExpr q.sup.toClassExpr] ∧
      Satisfiable datatypeMap (inclusionProblem p q).toOntology
  | .inconsistent => ¬ Satisfiable datatypeMap p.toOntology

private theorem models_withRoot {i : Interpretation datatypeMap} {p : Problem} {r : Concept}
    (h : p.Models i) : ({ p with root := r } : Problem).Models i :=
  ⟨h.tbox, h.rules, h.chains, h.reflexive, h.irreflexive, h.asymmetric, h.disjoint,
   h.subData, h.disjointData, h.funcData, h.dataRanges, h.keys, h.classAssertions,
   h.objAssertions, h.negObjAssertions, h.sameInds, h.diffInds, h.dataAssertions,
   h.negDataAssertions⟩

private theorem models_of_withRoot {i : Interpretation datatypeMap} {p : Problem} {r : Concept}
    (h : ({ p with root := r } : Problem).Models i) : p.Models i :=
  ⟨h.tbox, h.rules, h.chains, h.reflexive, h.irreflexive, h.asymmetric, h.disjoint,
   h.subData, h.disjointData, h.funcData, h.dataRanges, h.keys, h.classAssertions,
   h.objAssertions, h.negObjAssertions, h.sameInds, h.diffInds, h.dataAssertions,
   h.negDataAssertions⟩

private theorem entails_subClass_iff (p : Problem) (q : Inclusion)
    (hsubNo : q.sub.hasNoAnon = true) (hsupNo : q.sup.hasNoAnon = true) :
    Entails datatypeMap p.toOntology [.subClassOf q.sub.toClassExpr q.sup.toClassExpr] ↔
      ¬ (counterProblem p q).Sat := by
  constructor
  · rintro h ⟨i, hm, x, hsub, hnd⟩
    have hi : models i p.toOntology :=
      satisfies_models ((satisfies_toOntology_iff i p).mpr (models_of_withRoot hm))
    obtain ⟨assign, ha⟩ := h i hi
    have hax := ha _ (List.mem_singleton_self _)
    have hax' : axiomHolds i (.subClassOf q.sub.toClassExpr q.sup.toClassExpr) := by
      intro y hy
      rw [toClassExpr_iff] at hy ⊢
      exact (holds_withAnonymous_of_noAnon i assign y q.sup hsupNo).mp
        ((toClassExpr_iff (i.withAnonymous assign) y q.sup).mp
          (hax y ((toClassExpr_iff (i.withAnonymous assign) y q.sub).mpr
            ((holds_withAnonymous_of_noAnon i assign y q.sub hsubNo).mpr hy))))
    have hsup := (toClassExpr_iff i x q.sup).mp (hax' x ((toClassExpr_iff i x q.sub).mpr hsub))
    exact (holds_dual i x q.sup).mp hnd hsup
  · intro hno i ⟨assign, hsat⟩
    let j := i.withAnonymous assign
    have hm : p.Models j := (satisfies_toOntology_iff j p).mp hsat
    refine ⟨assign, fun a ha => ?_⟩
    rw [List.mem_singleton.mp ha]
    intro x hx
    apply Classical.byContradiction
    intro hn
    exact hno ⟨j, models_withRoot hm, x, (toClassExpr_iff j x q.sub).mp hx,
      (holds_dual j x q.sup).mpr fun hs => hn ((toClassExpr_iff j x q.sup).mpr hs)⟩

theorem checkInclusion_sound {p : Problem} {q : Inclusion} {maxNodes : Nat} {e : InclusionEvidence}
    (h : checkInclusion p q maxNodes e = true) :
    verdictClaim p q e.verdict := by
  rcases e with ⟨a, b⟩
  simp only [checkInclusion, Bool.and_eq_true] at h
  have hsubNo := h.1.1.1.1
  have hsupNo := h.1.1.1.2
  have ha := checkEvidence_sound h.1.2
  have hb := checkEvidence_sound h.2
  have he := entails_subClass_iff p q hsubNo hsupNo
  have hqsat : Satisfiable datatypeMap (inclusionProblem p q).toOntology ↔ (inclusionProblem p q).Sat :=
    satisfiable_iff_sat (inclusionProblem p q) rfl
  cases hca : a.isModel <;> cases hcb : b.isModel <;>
    simp only [evidenceClaim, hca, hcb, Bool.false_eq_true, ↓reduceIte] at ha hb <;>
    simp only [InclusionEvidence.verdict, hca, hcb, verdictClaim]
  · intro ⟨i, assign, hsat⟩
    let j := i.withAnonymous assign
    have hm := (satisfies_toOntology_iff j p).mp hsat
    obtain ⟨x⟩ := j.objectNonempty
    apply hb
    refine ⟨j, ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩, x, trivial⟩
    intro ax hax y hy
    rcases List.mem_cons.mp hax with hEq | hax
    · rw [hEq] at hy ⊢
      apply Classical.byContradiction
      intro hneg
      exact ha ⟨j, models_withRoot hm, y, hy, (holds_dual j y q.sup).mpr hneg⟩
    · exact hm.tbox ax hax y hy
  · obtain ⟨i, hm, _, _⟩ := hb
    have hm' : p.Models i := ⟨fun ax hax => hm.tbox ax (List.mem_cons_of_mem _ hax),
      hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩
    exact ⟨⟨i, satisfies_models ((satisfies_toOntology_iff i p).mpr hm')⟩, he.mpr ha⟩
  · obtain ⟨i, hm, _⟩ := ha
    exact ⟨⟨i, satisfies_models ((satisfies_toOntology_iff i p).mpr (models_of_withRoot hm))⟩,
      fun hp => hb (hqsat.mp hp)⟩
  · exact ⟨fun hent => he.mp hent ha, hqsat.mpr hb⟩

end Sabrina.OWL2.SROIQD
