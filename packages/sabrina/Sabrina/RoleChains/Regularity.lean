import Sabrina.RoleChains.Semantics

namespace Sabrina.RoleChains

open Sabrina.ALC

abbrev Rank := String → Nat

private def lower (rank : Rank) (head : String) (r : OrientedRole) : Bool := decide (rank r.1 < rank head)

private def beginsWithHead (rank : Rank) (head : String) : List OrientedRole → Bool
  | [] => false
  | r :: rs => (r == (head, false)) && rs.all (lower rank head)

private def shapeOK (rank : Rank) (c : Chain) : Bool :=
  (c.body == [(c.head, false), (c.head, false)]) ||
    (c.body.all (lower rank c.head) ||
      (beginsWithHead rank c.head c.body || beginsWithHead rank c.head c.body.reverse))

def checkRegular (rank : Rank) (rules : RoleTheory) (chains : List Chain) : Bool :=
  rules.all (fun (r,s) => decide (rank r.1 ≤ rank s.1)) &&
  chains.all (fun c => decide (2 ≤ c.body.length) && shapeOK rank c)

/-- A sufficient rank witness for the nonbuiltin role-chain order. The rank of
    a converse is the rank of its base role. Simple inclusions never go down. -/
def Ranked (rank : Rank) (rules : RoleTheory) (chains : List Chain) : Prop :=
  (∀ r s : OrientedRole, (r,s) ∈ rules → rank r.1 ≤ rank s.1) ∧
  ∀ c ∈ chains, 2 ≤ c.body.length ∧
    (c.body = [(c.head, false), (c.head, false)] ∨
      (∀ r ∈ c.body, rank r.1 < rank c.head) ∨
      (∃ rest, c.body = (c.head, false) :: rest ∧ ∀ r ∈ rest, rank r.1 < rank c.head) ∨
      (∃ rest, c.body = rest ++ [(c.head, false)] ∧ ∀ r ∈ rest, rank r.1 < rank c.head))

private theorem beginsWithHead_sound {rank head word}
    (h : beginsWithHead rank head word = true) :
    ∃ rest, word = (head, false) :: rest ∧ ∀ r ∈ rest, rank r.1 < rank head := by
  cases word with
  | nil => simp [beginsWithHead] at h
  | cons r rest =>
    simp only [beginsWithHead, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, lower,
      decide_eq_true_eq] at h
    exact ⟨rest, by rw [h.1], h.2⟩

theorem checkRegular_sound {rank rules chains} (h : checkRegular rank rules chains = true) :
    Ranked rank rules chains := by
  simp only [checkRegular, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun r s hrs => h.1 (r,s) hrs, ?_⟩
  intro c hc
  obtain ⟨hlen, hshape⟩ := h.2 c hc
  refine ⟨hlen, ?_⟩
  simp only [shapeOK, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, lower, decide_eq_true_eq] at hshape
  rcases hshape with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (beginsWithHead_sound h)))
  · obtain ⟨tail, he, htail⟩ := beginsWithHead_sound h
    have hp := congrArg List.reverse he
    simp only [List.reverse_reverse, List.reverse_cons] at hp
    exact Or.inr (Or.inr (Or.inr
      ⟨tail.reverse, hp, fun r hr => htail r (List.mem_reverse.mp hr)⟩))

private theorem beginsWithHead_complete {rank head rest}
    (h : ∀ r ∈ rest, rank r.1 < rank head) :
    beginsWithHead rank head ((head, false) :: rest) = true := by
  simpa [beginsWithHead, lower, List.all_eq_true] using h

/-- The checker recognizes precisely the rank witnesses used by the
role-language construction. -/
theorem checkRegular_iff {rank rules chains} :
    checkRegular rank rules chains = true ↔ Ranked rank rules chains := by
  refine ⟨checkRegular_sound, fun ⟨hrules, hchains⟩ => ?_⟩
  simp only [checkRegular, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun rs h => hrules rs.1 rs.2 h, fun c hc => ?_⟩
  obtain ⟨hlen, hshape⟩ := hchains c hc
  refine ⟨hlen, ?_⟩
  simp only [shapeOK, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, lower, decide_eq_true_eq]
  rcases hshape with h | h | ⟨rs, he, h⟩ | ⟨rs, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (he.symm ▸ beginsWithHead_complete h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [he, List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact beginsWithHead_complete fun r hr => h r (List.mem_reverse.mp hr)

/-- Rank order is invariant under inverse and cannot conflict with any
    hierarchy consequence obtained by mirroring and closure. -/
theorem Ranked.respectsClosure {rank rules chains} (h : Ranked rank rules chains)
    {r s : OrientedRole} (hrs : (r,s) ∈ roleClosure rules) : rank r.1 ≤ rank s.1 := by
  apply ALCH.close_sound (R := fun a b : OrientedRole => rank a.1 ≤ rank b.1) _ Nat.le_trans hrs
  intro a b hab
  rcases List.mem_append.mp hab with hab | hab
  · exact h.1 a b hab
  · obtain ⟨⟨a',b'⟩, hm, he⟩ := List.mem_map.mp hab
    cases he
    exact h.1 a' b' hm

/-- The strict order induced by a checked rank has no reverse path in the
simple inclusion hierarchy, including inclusions obtained by inversion. -/
theorem Ranked.noReverseInclusion {rank rules chains} (h : Ranked rank rules chains)
    {r s : OrientedRole} (hlt : rank r.1 < rank s.1) : (s, r) ∉ roleClosure rules :=
  fun hr => Nat.not_le_of_lt hlt (h.respectsClosure hr)

private def lowerRoles (c : Chain) : List OrientedRole :=
  if c.body == [(c.head, false), (c.head, false)] then []
  else if c.body.head? == some (c.head, false) then c.body.drop 1
  else if c.body.getLast? == some (c.head, false) then c.body.dropLast
  else c.body

private def tableRank (table : List (String × Nat)) (r : String) : Nat :=
  (table.lookup r).getD 0

@[noinline] private def inferRankTable (rules : RoleTheory) (chains : List Chain) :
    List (String × Nat) :=
  let constraints := (rules.map fun (r,s) => (r.1,s.1,0)) ++
    chains.flatMap (fun c => (lowerRoles c).map (fun r => (r.1,c.head,1)))
  let names := (constraints.flatMap fun (r,s,_) => [r,s]).eraseDups
  let relax := fun (table : List (String × Nat)) =>
    constraints.foldl (fun table (r,s,w) =>
      let k := tableRank table r + w
      table.map fun (t,v) => (t, if t == s then max v k else v)) table
  names.foldl (fun table _ => relax table) (names.map fun r => (r,0))

/-- Find a potential rank witness with bounded relaxation. -/
def inferRank (rules : RoleTheory) (chains : List Chain) : Rank :=
  tableRank (inferRankTable rules chains)

/-- Validate the inferred rank using a single table for all role lookups. -/
def checkInferredRank (rules : RoleTheory) (chains : List Chain) : Bool :=
  let table := inferRankTable rules chains
  checkRegular (fun r => tableRank table r) rules chains

private def roleNames (rules : RoleTheory) (chains : List Chain) : List String :=
  ((rules.flatMap fun (r, s) => [r.1, s.1]) ++
    chains.flatMap (fun c => c.head :: c.bodyNames)).eraseDups

private def compressRank (names : List String) (rank : Rank) : Rank :=
  fun r => names.countP fun s => decide (rank s < rank r)

private theorem compressRank_mono {names : List String} {rank : Rank} {r s : String}
    (h : rank r ≤ rank s) : compressRank names rank r ≤ compressRank names rank s :=
  List.countP_mono_left (fun _ _ hx => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hx) h))

private theorem compressRank_strict {names : List String} {rank : Rank} {r s : String}
    (hr : r ∈ names) (h : rank r < rank s) :
    compressRank names rank r < compressRank names rank s := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem hr
  have hbefore := compressRank_mono (names := before) (Nat.le_of_lt h)
  have hafter := compressRank_mono (names := after) (Nat.le_of_lt h)
  simp [compressRank, List.countP_append, h] at hbefore hafter ⊢
  omega

private theorem compressRank_ranked {rank rules chains} (h : Ranked rank rules chains) :
    Ranked (compressRank (roleNames rules chains) rank) rules chains := by
  have strict {c : Chain} (hc : c ∈ chains) {r : OrientedRole} (hr : r ∈ c.body)
      (hlt : rank r.1 < rank c.head) :
      compressRank (roleNames rules chains) rank r.1 <
        compressRank (roleNames rules chains) rank c.head := by
    apply compressRank_strict _ hlt
    simp only [roleNames, List.mem_eraseDups, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_of_mem _ (List.mem_map_of_mem hr)⟩)
  refine ⟨fun r s hr => compressRank_mono (h.1 r s hr), fun c hc => ?_⟩
  obtain ⟨hlen, hshape⟩ := h.2 c hc
  refine ⟨hlen, ?_⟩
  rcases hshape with eq | lowerAll | ⟨rs, eq, lowerRest⟩ | ⟨rs, eq, lowerRest⟩
  · exact Or.inl eq
  · exact Or.inr (Or.inl fun r hr => strict hc hr (lowerAll r hr))
  · exact Or.inr (Or.inr (Or.inl ⟨rs, eq, fun r hr =>
      strict hc (eq.symm ▸ List.mem_cons_of_mem _ hr) (lowerRest r hr)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rs, eq, fun r hr =>
      strict hc (eq.symm ▸ List.mem_append_left _ hr) (lowerRest r hr)⟩))

private def rankTables (bound : Nat) : List String → List (List (String × Nat))
  | [] => [[]]
  | r :: rs =>
    let tails := rankTables bound rs
    (List.range (bound + 1)).flatMap fun k => tails.map ((r, k) :: ·)

private theorem map_mem_rankTables (bound : Nat) (rank : Rank) (names : List String)
    (h : ∀ n ∈ names, rank n ≤ bound) :
    names.map (fun n => (n, rank n)) ∈ rankTables bound names := by
  induction names with
  | nil => simp [rankTables]
  | cons r rs ih =>
    refine List.mem_flatMap.mpr ⟨rank r, List.mem_range.mpr (Nat.lt_succ_of_le
      (h r (List.mem_cons_self ..))), ?_⟩
    exact List.mem_map_of_mem (ih fun n hn => h n (List.mem_cons_of_mem _ hn))

private theorem tableRank_map {names : List String} {rank : Rank} {r : String}
    (h : r ∈ names) : tableRank (names.map fun n => (n, rank n)) r = rank r := by
  induction names with
  | nil => simp at h
  | cons n ns ih =>
    by_cases he : r = n
    · subst n; simp [tableRank]
    · have hb : (r == n) = false := by simpa using he
      simpa only [tableRank, List.map_cons, List.lookup_cons, hb] using
        ih ((List.mem_cons.mp h).resolve_left he)

private theorem rankTable_ranked {rules chains rank} (h : Ranked rank rules chains) :
    Ranked (tableRank ((roleNames rules chains).map fun n => (n, rank n))) rules chains := by
  have ruleMem {r s : OrientedRole} (hrs : (r,s) ∈ rules) :
      r.1 ∈ roleNames rules chains ∧ s.1 ∈ roleNames rules chains := by
    simp only [roleNames, List.mem_eraseDups, List.mem_append]
    exact ⟨Or.inl (List.mem_flatMap.mpr ⟨(r,s), hrs, by simp⟩),
      Or.inl (List.mem_flatMap.mpr ⟨(r,s), hrs, by simp⟩)⟩
  have chainMem {c : Chain} (hc : c ∈ chains) {r : String} (hr : r ∈ c.head :: c.bodyNames) :
      r ∈ roleNames rules chains := by
    simp only [roleNames, List.mem_eraseDups, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨c, hc, hr⟩)
  refine ⟨fun r s hr => ?_, fun c hc => ?_⟩
  · rw [tableRank_map (ruleMem hr).1, tableRank_map (ruleMem hr).2]
    exact h.1 r s hr
  · obtain ⟨hlen, hshape⟩ := h.2 c hc
    have lower {r : OrientedRole} (hr : r ∈ c.body) (hlt : rank r.1 < rank c.head) :
        tableRank ((roleNames rules chains).map fun n => (n, rank n)) r.1 <
          tableRank ((roleNames rules chains).map fun n => (n, rank n)) c.head := by
      rw [tableRank_map (chainMem hc (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))),
        tableRank_map (chainMem hc (List.mem_cons_self ..))]
      exact hlt
    refine ⟨hlen, ?_⟩
    rcases hshape with eq | lowerAll | ⟨rs, eq, lowerRest⟩ | ⟨rs, eq, lowerRest⟩
    · exact Or.inl eq
    · exact Or.inr (Or.inl fun r hr => lower hr (lowerAll r hr))
    · exact Or.inr (Or.inr (Or.inl ⟨rs, eq, fun r hr =>
        lower (eq.symm ▸ List.mem_cons_of_mem _ hr) (lowerRest r hr)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rs, eq, fun r hr =>
        lower (eq.symm ▸ List.mem_append_left _ hr) (lowerRest r hr)⟩))

/-- Complete search for a rank in the implemented regular chain fragment.
Use the inexpensive relaxation first. The finite fallback is exhaustive. -/
def findRank (rules : RoleTheory) (chains : List Chain) : Option Rank :=
  let table := inferRankTable rules chains
  let rank := fun r => tableRank table r
  if checkRegular rank rules chains then some rank
  else
    let names := roleNames rules chains
    ((rankTables names.length names).find? fun table =>
      checkRegular (tableRank table) rules chains).map tableRank

theorem findRank_sound {rules chains rank} (h : findRank rules chains = some rank) :
    Ranked rank rules chains := by
  simp only [findRank] at h
  split at h
  · next he =>
    cases h
    exact checkRegular_sound he
  · obtain ⟨table, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    have hc : checkRegular (tableRank table) rules chains = true :=
      List.find?_some (p := fun t => checkRegular (tableRank t) rules chains) ht
    exact checkRegular_sound hc

theorem findRank_complete {rules chains rank} (h : Ranked rank rules chains) :
    (findRank rules chains).isSome = true := by
  simp only [findRank]
  split
  · rfl
  · simp only [Option.isSome_map]
    apply List.find?_isSome.mpr
    let names := roleNames rules chains
    let small := compressRank names rank
    refine ⟨names.map (fun n => (n, small n)), ?_, ?_⟩
    · exact map_mem_rankTables names.length small names (fun _ _ => List.countP_le_length)
    · exact checkRegular_iff.mpr (rankTable_ranked (compressRank_ranked h))

theorem findRank_iff {rules chains} :
    (findRank rules chains).isSome = true ↔ ∃ rank, Ranked rank rules chains := by
  constructor
  · intro h
    obtain ⟨rank, hr⟩ := Option.isSome_iff_exists.mp h
    exact ⟨rank, findRank_sound hr⟩
  · rintro ⟨_, h⟩
    exact findRank_complete h

end Sabrina.RoleChains
