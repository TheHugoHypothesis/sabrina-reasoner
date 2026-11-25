import Sabrina.ALC.Semantics

namespace Sabrina.ALC

/-- A row records the concepts true at one element, restricted to the input closure. -/
abbrev Row := List Concept

private def subformulas : Concept → List Concept
  | .top => [.top]
  | .atom name => [.atom name]
  | .neg c => .neg c :: subformulas c
  | .conj a b => .conj a b :: (subformulas a ++ subformulas b)
  | .some r c => .some r c :: subformulas c

private theorem self_mem_subformulas (c : Concept) : c ∈ subformulas c := by
  cases c <;> simp [subformulas]

private theorem subformulas_closed {c d : Concept} (h : d ∈ subformulas c) :
    subformulas d ⊆ subformulas c := by
  induction c with
  | top => simp [subformulas] at h; subst d; exact fun _ hm => hm
  | atom name => simp [subformulas] at h; subst d; exact fun _ hm => hm
  | neg c ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ hm => hm
    · intro x hx
      exact List.mem_cons_of_mem _ (ih h hx)
  | conj a b iha ihb =>
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ hm => hm
    · intro x hx
      rcases List.mem_append.mp h with ha | hb
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iha ha hx))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihb hb hx))
  | some r c ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ hm => hm
    · intro x hx
      exact List.mem_cons_of_mem _ (ih h hx)

private def axiomForms (ax : Inclusion) : List Concept := subformulas ax.sub ++ subformulas ax.sup

/-- Subformulas of the query and both sides of every inclusion. -/
def closure (tbox : TBox) (root : Concept) : List Concept :=
  (subformulas root ++ tbox.flatMap axiomForms).eraseDups

theorem root_mem_closure (tbox : TBox) (root : Concept) : root ∈ closure tbox root := by
  exact List.mem_eraseDups.mpr (List.mem_append_left _ (self_mem_subformulas root))

theorem axiom_mem_closure {tbox : TBox} (root : Concept) {ax : Inclusion} (ha : ax ∈ tbox) :
    ax.sub ∈ closure tbox root ∧ ax.sup ∈ closure tbox root := by
  constructor
  · exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨ax, ha, List.mem_append_left _ (self_mem_subformulas ax.sub)⟩))
  · exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨ax, ha, List.mem_append_right _ (self_mem_subformulas ax.sup)⟩))

private theorem closure_closed {tbox : TBox} {root c : Concept} (hc : c ∈ closure tbox root) :
    subformulas c ⊆ closure tbox root := by
  intro d hd
  apply List.mem_eraseDups.mpr
  rcases List.mem_append.mp (List.mem_eraseDups.mp hc) with hr | ha
  · exact List.mem_append_left _ (subformulas_closed hr hd)
  · obtain ⟨ax, hax, hm⟩ := List.mem_flatMap.mp ha
    apply List.mem_append_right _
    apply List.mem_flatMap.mpr
    refine ⟨ax, hax, ?_⟩
    rcases List.mem_append.mp hm with hl | hr
    · exact List.mem_append_left _ (subformulas_closed hl hd)
    · exact List.mem_append_right _ (subformulas_closed hr hd)

theorem neg_mem_closure {tbox : TBox} {root c : Concept} (hc : .neg c ∈ closure tbox root) :
    c ∈ closure tbox root :=
  closure_closed hc (List.mem_cons_of_mem _ (self_mem_subformulas c))

theorem conj_mem_closure {tbox : TBox} {root a b : Concept} (hc : .conj a b ∈ closure tbox root) :
    a ∈ closure tbox root ∧ b ∈ closure tbox root :=
  ⟨closure_closed hc (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_subformulas a))),
   closure_closed hc (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem_subformulas b)))⟩

theorem some_mem_closure {tbox : TBox} {root c : Concept} {r : String}
    (hc : .some r c ∈ closure tbox root) : c ∈ closure tbox root :=
  closure_closed hc (List.mem_cons_of_mem _ (self_mem_subformulas c))

/-- Enumerate choices of which closure concepts belong to a row. -/
def rows : List Concept → List Row
  | [] => [[]]
  | c :: cs =>
    let rest := rows cs
    rest ++ rest.map (c :: ·)

theorem filter_mem_rows (cs : List Concept) (p : Concept → Bool) : cs.filter p ∈ rows cs := by
  induction cs with
  | nil => simp [rows]
  | cons c cs ih =>
    rw [List.filter_cons, rows]
    split
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
    · exact List.mem_append_left _ ih

/-- Boolean constraints on a row, including agreement on all global inclusions. -/
def coherent (row : Row) : Concept → Bool
  | .top => decide (.top ∈ row)
  | .neg c => decide ((.neg c ∈ row) ↔ c ∉ row)
  | .conj a b => decide ((.conj a b ∈ row) ↔ (a ∈ row ∧ b ∈ row))
  | .atom _ | .some _ _ => true

def localCheck (cs : List Concept) (tbox : TBox) (row : Row) : Bool :=
  cs.all (coherent row) && tbox.all (fun ax => decide (ax.sub ∈ row → ax.sup ∈ row))

def candidates (tbox : TBox) (root : Concept) : List Row :=
  let cs := closure tbox root
  (rows cs).filter (localCheck cs tbox)

/-- A role edge may only witness existential concepts that are true at its source. -/
def admitsEdge (cs : List Concept) (role : String) (src dst : Row) : Bool :=
  cs.all fun
    | .some r c => decide (role = r → c ∈ dst → .some r c ∈ src)
    | _ => true

theorem admitsEdge_iff {cs : List Concept} {r : String} {src dst : Row} :
    admitsEdge cs r src dst = true ↔ ∀ c, .some r c ∈ cs → c ∈ dst → .some r c ∈ src := by
  simp only [admitsEdge, List.all_eq_true]
  constructor
  · intro h c hc hd
    exact of_decide_eq_true (h _ hc) rfl hd
  · intro h c hc
    cases c with
    | some s c =>
      apply decide_eq_true
      intro hr hd
      subst s
      exact h c hc hd
    | _ => rfl

/-- Every existential in a row must have an admissible edge to a witness row. -/
def hasWitnesses (cs : List Concept) (pool : List Row) (row : Row)
    (edge : String → Row → Row → Bool := admitsEdge cs) : Bool :=
  cs.all fun
    | .some r c => !(decide (.some r c ∈ row)) ||
        pool.any (fun dst => decide (c ∈ dst) && edge r row dst)
    | _ => true

theorem hasWitnesses_iff {cs : List Concept} {pool : List Row} {row : Row}
    {edge : String → Row → Row → Bool} :
    hasWitnesses cs pool row edge = true ↔ ∀ r c, .some r c ∈ cs → .some r c ∈ row →
      ∃ dst ∈ pool, c ∈ dst ∧ edge r row dst = true := by
  simp only [hasWitnesses, List.all_eq_true]
  constructor
  · intro h r c hc hs
    have hw := h _ hc
    simpa [hs, List.any_eq_true, Bool.and_eq_true] using hw
  · intro h c hc
    cases c with
    | some r c =>
      by_cases hs : .some r c ∈ row
      · simpa [hs, List.any_eq_true, Bool.and_eq_true] using h r c hc hs
      · simp [hs]
    | _ => rfl

end Sabrina.ALC
