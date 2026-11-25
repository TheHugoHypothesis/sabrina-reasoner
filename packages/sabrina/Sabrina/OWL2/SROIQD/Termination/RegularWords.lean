import Sabrina.OWL2.SROIQD.Termination.StringLengthCells

/-! Capped enumeration of a regular language. Each state stores up to the
requested number of distinct accepted suffixes. The table only grows, and
completeness below the cap follows from the equations at its fixed point. -/

namespace Sabrina.OWL2.SROIQD.Termination.RegularWords

structure Machine (State Symbol : Type) where
  statePool : Unit → List State
  alphabet : List Symbol
  transition : State → Symbol → State
  final : State → Bool
  closed : ∀ s ∈ statePool (), ∀ a ∈ alphabet, transition s a ∈ statePool ()

def Machine.states (m : Machine State Symbol) : List State := m.statePool ()

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

def Machine.accepts (m : Machine State Symbol) (s : State) : List Symbol → Bool
  | [] => m.final s
  | a :: w => m.accepts (m.transition s a) w

abbrev Table (State Symbol : Type) := List (State × List (List Symbol))

private def Table.atState (t : Table State Symbol) (s : State) : List (List Symbol) :=
  ((t.lookup s).getD [])

private def Machine.extensions (m : Machine State Symbol) (t : Table State Symbol)
    (s : State) : List (List Symbol) :=
  (if m.final s then [[]] else []) ++ m.alphabet.flatMap fun a =>
    (t.atState (m.transition s a)).map (a :: ·)

private def Machine.expand (m : Machine State Symbol) (K : Nat)
    (t : Table State Symbol) (s : State) : List (List Symbol) :=
  ((t.atState s ++ m.extensions t s).eraseDups).take K

private theorem lookup_tabulate (f : State → List (List Symbol)) (ss : List State)
    {s : State} (hs : s ∈ ss) :
    ((ss.map fun s => (s, f s)).lookup s) = some (f s) := by
  induction ss with
  | nil => cases hs
  | cons a as ih =>
    by_cases h : s = a
    · subst a; simp
    · simp [List.lookup_cons, beq_false_of_ne h, ih ((List.mem_cons.mp hs).resolve_left h)]

private def Machine.grow (m : Machine State Symbol) (K : Nat) (t : Table State Symbol) :
    Table State Symbol :=
  m.states.map fun s => (s, m.expand K t s)

private theorem Machine.grow_at (m : Machine State Symbol) (K : Nat) (t : Table State Symbol)
    {s : State} (hs : s ∈ m.states) :
    (m.grow K t).atState s = m.expand K t s := by
  simp [Machine.grow, Table.atState, lookup_tabulate _ _ hs]

private def Machine.Valid (m : Machine State Symbol) (K : Nat)
    (t : Table State Symbol) : Prop :=
  ∀ s ∈ m.states,
    (t.atState s).Nodup ∧ (t.atState s).length ≤ K ∧
      ∀ w ∈ t.atState s, m.accepts s w = true ∧ ∀ a ∈ w, a ∈ m.alphabet

private theorem Machine.empty_valid (m : Machine State Symbol) (K : Nat) :
    m.Valid K [] := by
  simp [Machine.Valid, Table.atState]

private theorem Machine.mem_extensions (m : Machine State Symbol) {K : Nat} {t : Table State Symbol}
    (hv : m.Valid K t) {s : State} (hs : s ∈ m.states) {w : List Symbol}
    (hw : w ∈ m.extensions t s) : m.accepts s w = true ∧ ∀ a ∈ w, a ∈ m.alphabet := by
  rcases List.mem_append.mp hw with hw | hw
  · cases hf : m.final s <;> simp [hf] at hw
    subst w
    exact ⟨hf, by simp⟩
  · obtain ⟨a, ha, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hw
    obtain ⟨haccept, hm⟩ := (hv _ (m.closed _ hs _ ha)).2.2 v hv'
    exact ⟨haccept, fun b hb => (List.mem_cons.mp hb).elim (· ▸ ha) (hm b)⟩

private theorem Machine.grow_valid (m : Machine State Symbol) (K : Nat) (t : Table State Symbol)
    (hv : m.Valid K t) : m.Valid K (m.grow K t) := by
  intro s hs
  rw [m.grow_at K t hs]
  refine ⟨(List.take_sublist ..).nodup (nodup_eraseDups_list _), List.length_take_le .., ?_⟩
  intro w hw
  have he := List.mem_eraseDups.mp (List.mem_of_mem_take hw)
  rcases List.mem_append.mp he with h | h
  · exact (hv s hs).2.2 w h
  · exact m.mem_extensions hv hs h

private theorem take_eraseDups_append {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α)
    (hn : xs.Nodup) :
    ((xs ++ ys).eraseDups).take xs.length = xs := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [List.cons_append, List.eraseDups_cons, List.length_cons, List.take_succ_cons]
    have hkeep : as.filter (fun b => !(b == a)) = as := by
      apply List.filter_eq_self.mpr
      intro x hx
      have he := beq_false_of_ne (show x ≠ a from fun he => hn'.1 (he ▸ hx))
      simp [he]
    rw [List.filter_append, hkeep]
    exact congrArg (a :: ·) (ih _ hn'.2)

private theorem Machine.grow_preserves (m : Machine State Symbol) {K : Nat} {t : Table State Symbol}
    (hv : m.Valid K t) {s : State} (hs : s ∈ m.states) :
    ((m.grow K t).atState s).take (t.atState s).length = t.atState s := by
  rw [m.grow_at K t hs, Machine.expand, List.take_take, Nat.min_eq_left (hv s hs).2.1]
  exact take_eraseDups_append _ _ (hv s hs).1

private theorem Machine.grow_length (m : Machine State Symbol) {K : Nat} {t : Table State Symbol}
    (hv : m.Valid K t) {s : State} (hs : s ∈ m.states) :
    (t.atState s).length ≤ ((m.grow K t).atState s).length := by
  have he := congrArg List.length (m.grow_preserves hv hs)
  rw [List.length_take] at he
  omega

private def Machine.remaining (m : Machine State Symbol) (K : Nat) (t : Table State Symbol) : Nat :=
  (m.states.map fun s => K - (t.atState s).length).sum

private theorem sum_le_of_pointwise {α : Type} {as : List α} {f g : α → Nat}
    (hle : ∀ a ∈ as, f a ≤ g a) : (as.map f).sum ≤ (as.map g).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hle a (List.mem_cons_self ..)) (ih fun b hb => hle b (List.mem_cons_of_mem _ hb))

private theorem sum_lt_of_mem_lt {α : Type} {as : List α} {f g : α → Nat}
    (hle : ∀ a ∈ as, f a ≤ g a) (hlt : ∃ a ∈ as, f a < g a) :
    (as.map f).sum < (as.map g).sum := by
  induction as with
  | nil => simp at hlt
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨b, hb, h⟩ := hlt
    have htail x hx := hle x (List.mem_cons_of_mem _ hx)
    have hhead := hle a (List.mem_cons_self ..)
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Nat.add_lt_add_of_lt_of_le h (sum_le_of_pointwise htail)
    · exact Nat.add_lt_add_of_le_of_lt hhead (ih htail ⟨b, hb, h⟩)

private theorem Machine.remaining_decreases (m : Machine State Symbol) {K : Nat}
    {t : Table State Symbol} (hv : m.Valid K t)
    (h : m.states.any (fun s => (t.atState s).length < ((m.grow K t).atState s).length) = true) :
    m.remaining K (m.grow K t) < m.remaining K t := by
  refine sum_lt_of_mem_lt (fun s hs => ?_) ?_
  · have := m.grow_length hv hs
    omega
  · obtain ⟨s, hs, he⟩ := List.any_eq_true.mp h
    have hl := (m.grow_valid K t hv s hs).2.1
    have hlt := of_decide_eq_true he
    exact ⟨s, hs, by omega⟩

private def Machine.stable (m : Machine State Symbol) (K : Nat) (t : Table State Symbol) : Prop :=
  ∀ s ∈ m.states, (m.grow K t).atState s = t.atState s

private theorem Machine.stable_of_no_growth (m : Machine State Symbol) {K : Nat}
    {t : Table State Symbol} (hv : m.Valid K t)
    (h : ¬ m.states.any (fun s => (t.atState s).length < ((m.grow K t).atState s).length) = true) :
    m.stable K t := by
  intro s hs
  have he : ((m.grow K t).atState s).length ≤ (t.atState s).length := by
    apply Nat.le_of_not_gt
    intro hl
    exact h (List.any_eq_true.mpr ⟨s, hs, decide_eq_true hl⟩)
  simpa only [List.take_of_length_le he] using m.grow_preserves hv hs

private def Machine.saturate (m : Machine State Symbol) (K : Nat) (t : Table State Symbol)
    (hv : m.Valid K t) : { table : Table State Symbol // m.Valid K table ∧ m.stable K table } :=
  if h : m.states.any (fun s => (t.atState s).length < ((m.grow K t).atState s).length) = true
  then m.saturate K (m.grow K t) (m.grow_valid K t hv)
  else ⟨t, hv, m.stable_of_no_growth hv h⟩
termination_by m.remaining K t
decreasing_by exact m.remaining_decreases hv h

private theorem Machine.stable_extensions (m : Machine State Symbol) {K : Nat}
    {t : Table State Symbol} (ht : m.stable K t) {s : State} (hs : s ∈ m.states)
    (hshort : (t.atState s).length < K) {v : List Symbol}
    (h : v ∈ m.extensions t s) : v ∈ t.atState s := by
  have htake : t.atState s = (t.atState s ++ m.extensions t s).eraseDups := by
    have he := ht s hs
    rw [m.grow_at K t hs, Machine.expand] at he
    have hlen := congrArg List.length he
    rw [List.length_take] at hlen
    exact he.symm.trans (List.take_of_length_le (by omega))
  rw [htake]
  exact List.mem_eraseDups.mpr (List.mem_append_right _ h)

private theorem Machine.stable_complete (m : Machine State Symbol) {K : Nat}
    {t : Table State Symbol} (hv : m.Valid K t) (ht : m.stable K t)
    {w : List Symbol} {s : State} (hs : s ∈ m.states)
    (hshort : (t.atState s).length < K)
    (haccept : m.accepts s w = true) (hword : ∀ a ∈ w, a ∈ m.alphabet) :
    w ∈ t.atState s := by
  induction w generalizing s with
  | nil =>
    exact m.stable_extensions ht hs hshort (List.mem_append_left _ (by simpa [Machine.accepts] using haccept))
  | cons a w ih =>
    have ha := hword a (List.mem_cons_self ..)
    have hs' := m.closed s hs a ha
    have hfiber (u) (hu : u ∈ t.atState (m.transition s a)) :
        a :: u ∈ t.atState s :=
      m.stable_extensions ht hs hshort (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_map_of_mem hu⟩))
    have hnd : ((t.atState (m.transition s a)).map (a :: ·)).Nodup :=
      (hv _ hs').1.map (a :: ·) (fun _ _ hn he => hn (List.cons.inj he).2)
    have hlen := hnd.length_le_of_subset (fun _ hw =>
      let ⟨u, hu, he⟩ := List.mem_map.mp hw
      he ▸ hfiber u hu)
    rw [List.length_map] at hlen
    exact hfiber _ (ih hs' (Nat.lt_of_le_of_lt hlen hshort) haccept
      (fun b hb => hword b (List.mem_cons_of_mem _ hb)))

def Machine.sample (m : Machine State Symbol) (K : Nat) (s : State) : List (List Symbol) :=
  (m.saturate K [] (m.empty_valid K)).val.atState s

theorem Machine.sample_sound (m : Machine State Symbol) (K : Nat) {s : State}
    (hs : s ∈ m.states) :
    (m.sample K s).Nodup ∧ (m.sample K s).length ≤ K ∧
      ∀ w ∈ m.sample K s, m.accepts s w = true ∧ ∀ a ∈ w, a ∈ m.alphabet :=
  (m.saturate K [] (m.empty_valid K)).property.1 s hs

theorem Machine.sample_complete_of_lt (m : Machine State Symbol) (K : Nat) {s : State}
    (hs : s ∈ m.states) {w : List Symbol}
    (hshort : (m.sample K s).length < K) (haccept : m.accepts s w = true)
    (hword : ∀ a ∈ w, a ∈ m.alphabet) : w ∈ m.sample K s :=
  let result := m.saturate K [] (m.empty_valid K)
  m.stable_complete result.property.1 result.property.2 hs hshort haccept hword

private def Machine.extendStates (m : Machine State Symbol) (xs : List State) : List State :=
  (xs ++ xs.flatMap fun s => m.alphabet.map (m.transition s)).eraseDups

private theorem Machine.extendStates_mem (m : Machine State Symbol) (xs : List State)
    {s : State} (h : s ∈ xs) : s ∈ m.extendStates xs :=
  List.mem_eraseDups.mpr (List.mem_append_left _ h)

private theorem Machine.extendStates_next (m : Machine State Symbol) (xs : List State)
    {s : State} (hs : s ∈ xs) {a : Symbol} (ha : a ∈ m.alphabet) :
    m.transition s a ∈ m.extendStates xs :=
  List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨s, hs, List.mem_map_of_mem ha⟩))

private theorem Machine.extendStates_inside (m : Machine State Symbol) {xs : List State}
    (h : xs ⊆ m.states) : m.extendStates xs ⊆ m.states := by
  intro s hs
  rcases List.mem_append.mp (List.mem_eraseDups.mp hs) with hs | hs
  · exact h hs
  · obtain ⟨q, hq, hnext⟩ := List.mem_flatMap.mp hs
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hnext
    exact m.closed q (h hq) a ha

private theorem subset_of_no_growth {xs ys : List State}
    (hn : xs.Nodup) (hsub : xs ⊆ ys) (h : ys.length ≤ xs.length) : ys ⊆ xs := by
  intro a ha
  apply Classical.byContradiction
  intro hna
  have hn' : (a :: xs).Nodup := List.nodup_cons.mpr ⟨hna, hn⟩
  have hle := hn'.length_le_of_subset (fun s hs =>
    (List.mem_cons.mp hs).elim (fun he => he.symm ▸ ha) (fun hs => hsub hs))
  simp only [List.length_cons] at hle
  omega

private def Machine.closeStates (m : Machine State Symbol) (start : State)
    (nodes : List State) (hn : nodes.Nodup) (hin : nodes ⊆ m.states)
    (hstart : start ∈ nodes) :
    { xs : List State // start ∈ xs ∧
      ∀ s ∈ xs, ∀ a ∈ m.alphabet, m.transition s a ∈ xs } :=
  let next := m.extendStates nodes
  if h : nodes.length < next.length then
    m.closeStates start next (nodup_eraseDups_list _)
      (m.extendStates_inside hin) (m.extendStates_mem nodes hstart)
  else
    ⟨nodes, hstart, fun s hs a ha =>
      subset_of_no_growth hn (fun _ hmem => m.extendStates_mem nodes hmem)
        (Nat.le_of_not_gt h) (m.extendStates_next nodes hs ha)⟩
termination_by m.states.length - nodes.length
decreasing_by
  have hle := (nodup_eraseDups_list (nodes ++ nodes.flatMap fun s =>
    m.alphabet.map (m.transition s))).length_le_of_subset (m.extendStates_inside hin)
  change next.length ≤ m.states.length at hle
  change m.states.length - next.length < m.states.length - nodes.length
  omega

private def Machine.reachable (m : Machine State Symbol) (s : State) (hs : s ∈ m.states) :
    { r : Machine State Symbol // s ∈ r.states ∧ r.alphabet = m.alphabet ∧
      r.transition = m.transition ∧ r.final = m.final } :=
  let reach := m.closeStates s [s] (by simp) (by simp [hs]) (List.mem_singleton_self _)
  ⟨{ m with statePool := fun _ => reach.val, closed := reach.property.2 },
    reach.property.1, rfl, rfl, rfl⟩

private theorem Machine.accepts_of_same_graph (m r : Machine State Symbol)
    (hte : r.transition = m.transition) (hfin : r.final = m.final) (s : State) (w : List Symbol) :
    r.accepts s w = m.accepts s w := by
  induction w generalizing s with
  | nil => exact congrFun hfin s
  | cons a w ih => simp [Machine.accepts, hte, ih]

/-- Sampling starts with the reachable subgraph. The finite pool appears
in the termination proof and need not be materialized by the executable. -/
def Machine.sampleReachable (m : Machine State Symbol) (K : Nat) (s : State)
    (hs : s ∈ m.states) : List (List Symbol) :=
  let r := m.reachable s hs
  r.val.sample K s

theorem Machine.sampleReachable_sound (m : Machine State Symbol) (K : Nat) {s : State}
    (hs : s ∈ m.states) :
    (m.sampleReachable K s hs).Nodup ∧ (m.sampleReachable K s hs).length ≤ K ∧
      ∀ w ∈ m.sampleReachable K s hs, m.accepts s w = true ∧ ∀ a ∈ w, a ∈ m.alphabet := by
  let r := m.reachable s hs
  obtain ⟨hnd, hlen, hgood⟩ := r.val.sample_sound K r.property.1
  refine ⟨hnd, hlen, fun w hw => ?_⟩
  obtain ⟨ha, hmem⟩ := hgood w hw
  rw [m.accepts_of_same_graph r.val r.property.2.2.1 r.property.2.2.2] at ha
  exact ⟨ha, fun a ha => r.property.2.1 ▸ hmem a ha⟩

theorem Machine.sampleReachable_complete (m : Machine State Symbol) (K : Nat) {s : State}
    (hs : s ∈ m.states) {w : List Symbol} (hlt : (m.sampleReachable K s hs).length < K)
    (h : m.accepts s w = true) (ha : ∀ a ∈ w, a ∈ m.alphabet) :
    w ∈ m.sampleReachable K s hs := by
  let r := m.reachable s hs
  refine r.val.sample_complete_of_lt K r.property.1 hlt ?_ ?_
  · rw [m.accepts_of_same_graph r.val r.property.2.2.1 r.property.2.2.2]
    exact h
  · intro a hm
    exact r.property.2.1.symm ▸ ha a hm

#print axioms Machine.sample_sound
#print axioms Machine.sample_complete_of_lt

end Sabrina.OWL2.SROIQD.Termination.RegularWords
