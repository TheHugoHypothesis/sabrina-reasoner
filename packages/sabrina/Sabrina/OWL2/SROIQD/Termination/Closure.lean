import Sabrina.OWL2.SROIQD.Search

/-! Finite alphabet for ordinary concept labels. The existing `Concept.dual`
is a semantic complement. Applying it to a data quantifier twice adds two
explicit complements to its range. The tableau uses duals at specific
rule premises, so it needs closure under those uses of duality. -/
namespace Sabrina.OWL2.SROIQD.Termination

/-- Collect a concept, its dual, and the same pair for every object subconcept. -/
def paired : Concept → List Concept
  | c@(.conj a b) | c@(.disj a b) => [c, c.dual] ++ paired a ++ paired b
  | c@(.some _ a) | c@(.all _ a) | c@(.min _ _ a) | c@(.max _ _ a) =>
    [c, c.dual] ++ paired a
  | c => [c, c.dual]

theorem self_mem_paired (c : Concept) : c ∈ paired c := by
  cases c <;> simp [paired]

theorem dual_mem_paired (c : Concept) : c.dual ∈ paired c := by
  cases c <;> simp [paired]

/-- Subconcepts and the extra label introduced when a qualified upper bound
splits on membership in its filler. Clashes only inspect labels. -/
def operands : Concept → List Concept
  | .conj a b | .disj a b => [a,b]
  | .some _ a | .all _ a | .min _ _ a => [a]
  | .max _ _ a => [a,a.dual]
  | _ => []

private theorem root_operands (c : Concept) {a : Concept}
    (h : a ∈ operands c ++ operands c.dual) : a = .bottom ∨ a ∈ paired c := by
  have ha := self_mem_paired
  have hd := dual_mem_paired
  cases c with
  | min n r body =>
    cases n <;> simp [operands, Concept.dual, paired] at h ⊢ <;> grind
  | dataMin n r range =>
    cases n <;> simp [operands, Concept.dual, paired] at h ⊢ <;> grind
  | _ =>
    simp [operands, Concept.dual, paired] at h ⊢ <;> grind

theorem paired_operands {c x a : Concept} (hx : x ∈ paired c) (ha : a ∈ operands x) :
    a = .bottom ∨ a ∈ paired c := by
  induction c with
  | conj l r il ir | disj l r il ir =>
    simp only [paired, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl) | hl) | hr
    · exact root_operands _ (List.mem_append_left _ ha)
    · exact root_operands _ (List.mem_append_right _ ha)
    · rcases il hl with h | h
      · exact .inl h
      · exact .inr (List.mem_append_left _ (List.mem_append_right _ h))
    · rcases ir hr with h | h
      · exact .inl h
      · exact .inr (List.mem_append_right _ h)
  | some _ b ih | all _ b ih | min _ _ b ih | max _ _ b ih =>
    simp only [paired, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | hb
    · exact root_operands _ (List.mem_append_left _ ha)
    · exact root_operands _ (List.mem_append_right _ ha)
    · rcases ih hb with h | h
      · exact .inl h
      · exact .inr (List.mem_append_right _ h)
  | _ =>
    simp only [paired, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact root_operands _ (List.mem_append_left _ ha)
    · exact root_operands _ (List.mem_append_right _ ha)

/-- Root and input concepts that can enter a branch without a parent label.
Initialization binds every ABox individual with a positive nominal. -/
def seeds (p : Problem) : List Concept :=
  p.root :: p.tbox.flatMap (fun q => [q.sub,q.sup]) ++
    p.classAssertions.map Prod.snd ++ p.keys.map KeyAxiom.cls ++
    p.allIndividuals.map (fun a => .nom a true)

def clos (p : Problem) : List Concept :=
  (.top :: .bottom :: (seeds p).flatMap paired).eraseDups

theorem clos_nodup (p : Problem) : (clos p).Nodup := nodup_eraseDups_list _

theorem bottom_mem_clos (p : Problem) : Concept.bottom ∈ clos p := by simp [clos]

theorem paired_subset_clos {p : Problem} {c : Concept} (h : c ∈ seeds p) :
    paired c ⊆ clos p := by
  intro d hd
  simp only [clos, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
  exact .inr (.inr ⟨c,h,hd⟩)

theorem seed_mem_clos {p : Problem} {c : Concept} (h : c ∈ seeds p) :
    c ∈ clos p := paired_subset_clos h (self_mem_paired c)

theorem seed_dual_mem_clos {p : Problem} {c : Concept} (h : c ∈ seeds p) :
    c.dual ∈ clos p := paired_subset_clos h (dual_mem_paired c)

theorem clos_operands {p : Problem} {c d : Concept} (hc : c ∈ clos p)
    (hd : d ∈ operands c) : d ∈ clos p := by
  simp only [clos, List.mem_eraseDups, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | ⟨a,ha,hc⟩
  · simp [operands] at hd
  · simp [operands] at hd
  · rcases paired_operands hc hd with rfl | h
    · exact bottom_mem_clos p
    · exact paired_subset_clos ha h

/-- Enumerate a label set once in the fixed alphabet order. -/
def labelSet (p : Problem) (s : Branch) (x : Nat) : List Concept :=
  (clos p).filter fun c => s.labels.contains (x,c)

/-- All subsets, represented in the order of the alphabet. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | c :: cs =>
    let rest := subsets cs
    rest ++ rest.map (c :: ·)

theorem filter_mem_subsets {α : Type} (keep : α → Bool) (cs : List α) :
    cs.filter keep ∈ subsets cs := by
  induction cs with
  | nil => simp [subsets]
  | cons c cs ih =>
    cases h : keep c
    · exact List.mem_append_left _ (by simpa [h] using ih)
    · exact List.mem_append_right _ (List.mem_map.mpr
        ⟨cs.filter keep,ih,by simp [h]⟩)

theorem subsets_length {α : Type} (cs : List α) : (subsets cs).length = 2 ^ cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

theorem label_set_bound (p : Problem) :
    ∃ rows : List (List Concept), rows.length = 2 ^ (clos p).length ∧
      ∀ (s : Branch) (x : Nat), labelSet p s x ∈ rows :=
  ⟨subsets (clos p),subsets_length _,fun _ _ => filter_mem_subsets _ _⟩

private def doubleComplements (d : DataRange) : Nat → DataRange
  | 0 => d
  | n + 1 => .complement (.complement (doubleComplements d n))

private theorem size_le_doubleComplements (d : DataRange) (n : Nat) :
    n ≤ sizeOf (doubleComplements d n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => simp [doubleComplements]; omega

private theorem mem_size_bound {α : Type} {f : α → Nat} {cs : List α} {a : α}
    (h : a ∈ cs) : f a ≤ (cs.map f).foldr max 0 := by
  induction cs with
  | nil => contradiction
  | cons b cs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

/-- Literal closure under arbitrary iterations of the existing dual is
impossible even for one data existential. The rule alphabet uses only the
dual occurrences that the calculus can actually produce. -/
theorem no_raw_dual_closure (cs : List Concept) (r : IRI) (d : DataRange)
    (h : .dataSome r d ∈ cs) :
    ¬ (∀ c ∈ cs, c.dual ∈ cs) := by
  intro hdual
  have all (n : Nat) : .dataSome r (doubleComplements d n) ∈ cs := by
    induction n with
    | zero => exact h
    | succ n ih =>
      exact hdual _ (hdual _ ih)
  let f : Concept → Nat := fun c =>
    match c with
    | .dataSome _ range => sizeOf range
    | _ => 0
  let n := (cs.map f).foldr max 0 + 1
  have hb := mem_size_bound (f := f) (all n)
  have hn := size_le_doubleComplements d n
  change sizeOf (doubleComplements d n) ≤ (cs.map f).foldr max 0 at hb
  omega

#print axioms clos_operands
#print axioms label_set_bound
#print axioms no_raw_dual_closure

end Sabrina.OWL2.SROIQD.Termination
