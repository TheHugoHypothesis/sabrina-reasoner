import Sabrina.OWL2.SROIQD.Termination.Closure

/-! Label preservation for the existing rule selector. The proof inspects
the constructors that each rule returns. Satisfiability preservation alone
does not constrain the syntax of a transition's children. -/
namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole)

def LabelsWithin (p : Problem) (s : Branch) : Prop :=
  ∀ {x c}, (x,c) ∈ s.labels → c ∈ clos p

private theorem add_within {p : Problem} {s : Branch} {x : Nat} {c : Concept}
    (hs : LabelsWithin p s) (hc : c ∈ clos p) : LabelsWithin p (s.add x c) := by
  unfold Branch.add
  split
  · exact hs
  · intro y d hd
    rcases List.mem_cons.mp hd with h | h
    · exact (Prod.mk.inj h).2 ▸ hc
    · exact hs h

private theorem merge_within {p : Problem} {s : Branch} {x y : Nat}
    (hs : LabelsWithin p s) : LabelsWithin p (s.merge x y) := by
  intro a c h
  simp only [Branch.merge, List.mem_eraseDups] at h
  obtain ⟨⟨n,d⟩,hd,he⟩ := List.mem_map.mp h
  exact (Prod.mk.inj he).2 ▸ hs hd

private theorem allocate_within {p : Problem} {s : Branch} {x : Nat} {r : OrientedRole}
    {body mark : Concept} {count : Nat} {distinct : Bool}
    (hs : LabelsWithin p s) (hbody : body ∈ clos p) :
    LabelsWithin p (s.allocate x r body mark count distinct) := by
  intro a c h
  simp only [Branch.allocate, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨_,_,he⟩ := List.mem_map.mp h
    exact (Prod.mk.inj he).2 ▸ hbody
  · exact hs h

private theorem add_oriented_within {p : Problem} {s : Branch} {r : OrientedRole}
    {x y : Nat} (hs : LabelsWithin p s) : LabelsWithin p (s.addOriented r x y) := by
  unfold Branch.addOriented
  split <;> unfold Branch.addEdge <;> split <;> exact fun h => hs h

private structure ChildrenWithin {p : Problem} {s : Branch} (t : Transition p s) : Prop where
  all : ∀ b ∈ t.branches, LabelsWithin p b

private structure OptionsWithin {p : Problem} {s : Branch}
    (o : Option (Transition p s)) : Prop where
  children : ∀ t, o = some t → ChildrenWithin t

private theorem within_none {p : Problem} {s : Branch} :
    OptionsWithin (p := p) (s := s) none := by
  constructor
  intro _ he
  contradiction

private theorem within_some {p : Problem} {s : Branch} {t : Transition p s}
    (h : ChildrenWithin t) : OptionsWithin (some t) := by
  constructor
  intro u he
  cases he
  exact h

private theorem within_choice {p : Problem} {s : Branch}
    {a b : Option (Transition p s)} (ha : OptionsWithin a) (hb : OptionsWithin b) :
    OptionsWithin (a <|> b) := by
  cases a
  · exact hb
  · exact ha

private theorem within_find {p : Problem} {s : Branch} {α : Type} {xs : List α}
    {f : α → Option (Transition p s)} (h : ∀ x ∈ xs, OptionsWithin (f x)) :
    OptionsWithin (xs.findSome? f) := by
  constructor
  intro t ht
  obtain ⟨pre,x,post,he,hx,_⟩ := List.findSome?_eq_some_iff.mp ht
  exact (h x (he ▸ List.mem_append_right _ (List.mem_cons_self ..))).children t hx

private theorem no_children {p : Problem} {s : Branch} {t : Transition p s}
    (h : t.branches = []) : ChildrenWithin t := by
  constructor
  simp [h]

private theorem one_child {p : Problem} {s : Branch} {t : Transition p s} {b : Branch}
    (h : t.branches = [b]) (hb : LabelsWithin p b) :
    ChildrenWithin t := by
  constructor
  intro c hc
  obtain rfl := List.mem_singleton.mp (h ▸ hc)
  exact hb

private theorem two_children {p : Problem} {s : Branch} {t : Transition p s}
    {a b : Branch} (h : t.branches = [a,b]) (ha : LabelsWithin p a) (hb : LabelsWithin p b) :
    ChildrenWithin t := by
  constructor
  intro c hc
  rw [h] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ha
  · obtain rfl := List.mem_singleton.mp hc
    exact hb

private theorem merge_children {p : Problem} {s : Branch} {t : Transition p s}
    {pairs : List (Nat × Nat)}
    (h : t.branches = pairs.map (fun (a,b) => s.merge a b)) (hs : LabelsWithin p s) :
    ChildrenWithin t := by
  constructor
  intro b hb
  rw [h] at hb
  obtain ⟨⟨_,_⟩,_,rfl⟩ := List.mem_map.mp hb
  exact merge_within hs

-- These are proof-local references to the selectors used by the imported
-- definition of next. No private selector is part of the public interface.
private def searchName (id : Lean.Name) : Lean.Name :=
  (Lean.Name.mkNum `_private.Sabrina.OWL2.SROIQD.Search 0) ++
    `Sabrina.OWL2.SROIQD ++ id

local macro "rule% " n:ident : term => pure (Lean.mkIdent (searchName n.getId))

local macro "unfold_rule " n:ident : tactic =>
  `(tactic| unfold $(Lean.mkIdent (searchName n.getId)):ident)

local macro "option_cases" : tactic =>
  `(tactic| repeat' first
    | exact within_none
    | apply within_choice
    | (apply within_find; intro _ _)
    | apply within_some
    | split
    | (dsimp only; split))

private theorem inequality_within (p : Problem) (s : Branch) :
    OptionsWithin ((rule% inequalityClash) p s) := by
  unfold_rule inequalityClash
  option_cases
  (apply no_children; rfl)

private theorem label_clash_within (p : Problem) (s : Branch) :
    OptionsWithin ((rule% labelClash) p s) := by
  unfold_rule labelClash
  option_cases
  all_goals (apply no_children; rfl)

private theorem neg_edge_within (p : Problem) (s : Branch) :
    OptionsWithin ((rule% negEdgeClash) p s) := by
  unfold_rule negEdgeClash
  option_cases
  (apply no_children; rfl)

private theorem nominal_within {p : Problem} {s : Branch} (hs : LabelsWithin p s) :
    OptionsWithin ((rule% nominalMerge) p s) := by
  unfold_rule nominalMerge
  option_cases
  all_goals first
    | (apply no_children; rfl)
    | (apply one_child <;> first | rfl | exact merge_within hs)

private theorem self_within {p : Problem} {s : Branch} (hs : LabelsWithin p s) :
    OptionsWithin ((rule% selfSteps) p s) := by
  unfold_rule selfSteps
  option_cases
  all_goals first
    | (apply no_children; rfl)
    | (apply one_child <;> first | rfl | exact add_oriented_within hs)

private theorem hierarchy_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% hierarchy) p s nodes) := by
  unfold_rule hierarchy
  option_cases
  apply one_child
  · rfl
  · exact add_oriented_within hs

private theorem chains_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% chains) p s nodes) := by
  unfold_rule chains
  option_cases
  apply one_child
  · rfl
  · exact add_oriented_within hs

private theorem data_clash_within (p : Problem) (s : Branch) :
    OptionsWithin ((rule% dataClash) p s) := by
  unfold_rule dataClash
  option_cases
  all_goals apply no_children <;> rfl

private theorem key_within {p : Problem} {s : Branch} (hs : LabelsWithin p s) :
    OptionsWithin ((rule% keyMerge) p s) := by
  unfold_rule keyMerge
  option_cases
  apply one_child
  · rfl
  · exact merge_within hs

private theorem role_chars_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% roleCharSteps) p s nodes) := by
  unfold_rule roleCharSteps
  option_cases
  all_goals first
    | (apply no_children; rfl)
    | (apply one_child <;> first | rfl | exact add_oriented_within hs)

private theorem data_steps_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% dataSteps) p s nodes) := by
  unfold_rule dataSteps
  option_cases
  all_goals
    apply one_child
    · rfl
    · first
      | unfold Branch.addDataEdge; split <;> exact fun h => hs h
      | unfold Branch.addNegDataEdge; split <;> exact fun h => hs h
      | unfold Branch.addDataConstraint; split <;> exact fun h => hs h

private theorem upper_bounds_within {p : Problem} {s : Branch} (hs : LabelsWithin p s) :
    OptionsWithin ((rule% upperBounds) p s) := by
  unfold_rule upperBounds
  apply within_find
  rintro ⟨⟨x,c⟩,hc⟩ _
  cases c <;> try exact within_none
  dsimp only
  split
  case isFalse => exact within_none
  apply within_some
  apply merge_children
  · rfl
  · exact hs

private theorem sub_seed {p : Problem} {q : Inclusion} (h : q ∈ p.tbox) : q.sub ∈ seeds p := by
  have hm : q.sub ∈ p.tbox.flatMap (fun e => [e.sub,e.sup]) :=
    List.mem_flatMap.mpr ⟨q,h,by simp⟩
  simp [seeds, hm]

private theorem sup_seed {p : Problem} {q : Inclusion} (h : q ∈ p.tbox) : q.sup ∈ seeds p := by
  have hm : q.sup ∈ p.tbox.flatMap (fun e => [e.sub,e.sup]) :=
    List.mem_flatMap.mpr ⟨q,h,by simp⟩
  simp [seeds, hm]

private theorem label_operand {p : Problem} {s : Branch} {x : Nat} {c d : Concept}
    (hs : LabelsWithin p s) (hc : (x,c) ∈ s.labels) (hd : d ∈ operands c) :
    d ∈ clos p :=
  clos_operands (hs hc) hd

local macro "from_operand " hs:ident parent:term : tactic =>
  `(tactic| (apply label_operand $hs:ident (c := $parent)
             <;> first | assumption | (simp [operands]; done)))

private theorem local_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% localLabels) p s nodes) := by
  unfold_rule localLabels
  option_cases
  all_goals
    apply one_child
    · rfl
    · apply add_within hs
      first | from_operand hs (.conj _ _) | from_operand hs (.all _ _)

private theorem deterministic_gci_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% deterministicGCI) p s nodes) := by
  unfold_rule deterministicGCI
  apply within_find
  intro x _
  apply within_find
  rintro ⟨q,hq⟩ _
  option_cases
  apply one_child
  · rfl
  · apply add_within hs
    exact seed_mem_clos (sup_seed (by assumption))

private theorem undecided_gci_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% undecidedGCI) p s nodes) := by
  unfold_rule undecidedGCI
  apply within_find
  intro x _
  apply within_find
  rintro ⟨q,hq⟩ _
  option_cases
  apply two_children
  · rfl
  · apply add_within hs
    exact seed_dual_mem_clos (sub_seed (by assumption))
  · apply add_within hs
    exact seed_mem_clos (sup_seed (by assumption))

private theorem disjunctions_within {p : Problem} {s : Branch} (hs : LabelsWithin p s) :
    OptionsWithin ((rule% disjunctions) p s) := by
  unfold_rule disjunctions
  option_cases
  all_goals
    first
    | (apply one_child <;> first | rfl | apply add_within hs)
    | (apply two_children <;> first | rfl | apply add_within hs)
  all_goals from_operand hs (.disj _ _)

private theorem witnesses_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) (maxNodes : Nat) :
    OptionsWithin ((rule% witnesses) p s nodes maxNodes) := by
  unfold_rule witnesses
  option_cases
  all_goals
    apply one_child
    · rfl
    · apply allocate_within hs
      first | from_operand hs (.some _ _) | from_operand hs (.min _ _ _)

private theorem qualifiers_within {p : Problem} {s : Branch} (hs : LabelsWithin p s)
    (nodes : List Nat) : OptionsWithin ((rule% qualifiers) p s nodes) := by
  unfold_rule qualifiers
  apply within_find
  intro label hm
  option_cases
  apply two_children
  · rfl
  · apply add_within hs
    from_operand hs (.max _ _ _)
  · apply add_within hs
    from_operand hs (.max _ _ _)

/-- Every child returned by the actual selector preserves the finite label
alphabet, independently of the selector's allocation limit. -/
theorem next_preserves_closure {p : Problem} {s : Branch} {maxNodes : Nat}
    (hs : LabelsWithin p s) {t : Transition p s} (hnext : next p s maxNodes = some t) :
    ∀ b ∈ t.branches, LabelsWithin p b := by
  have h : OptionsWithin (next p s maxNodes) := by
    unfold next
    dsimp only
    refine within_choice (inequality_within p s) ?_
    refine within_choice (label_clash_within p s) ?_
    refine within_choice (neg_edge_within p s) ?_
    refine within_choice (data_clash_within p s) ?_
    refine within_choice (nominal_within hs) ?_
    refine within_choice (key_within hs) ?_
    refine within_choice (self_within hs) ?_
    refine within_choice (role_chars_within hs s.nodes) ?_
    refine within_choice (data_steps_within hs s.nodes) ?_
    refine within_choice (local_within hs s.nodes) ?_
    refine within_choice (hierarchy_within hs s.nodes) ?_
    refine within_choice (chains_within hs s.nodes) ?_
    refine within_choice (deterministic_gci_within hs s.nodes) ?_
    refine within_choice (disjunctions_within hs) ?_
    refine within_choice (upper_bounds_within hs) ?_
    refine within_choice (witnesses_within hs s.nodes maxNodes) ?_
    exact within_choice (qualifiers_within hs s.nodes) (undecided_gci_within hs s.nodes)
  exact (h.children t hnext).all

private theorem zipIdx_mem {α : Type} {xs : List α} {k n : Nat} {x : α}
    (h : (x,n) ∈ xs.zipIdx k) : x ∈ xs :=
  List.mem_of_getElem (List.mem_zipIdx h).2.2.symm

private theorem named_mem_individuals {p : Problem} {a : IRI} (h : a ∈ p.nominals) :
    .named a ∈ p.allIndividuals := by
  obtain ⟨i,hi,he⟩ := List.mem_filterMap.mp h
  cases i <;> simp_all

private theorem anonymous_mem_individuals {p : Problem} {a : String × String} (h : a ∈ p.anons) :
    .anonymous a.1 a.2 ∈ p.allIndividuals := by
  obtain ⟨i,hi,he⟩ := List.mem_filterMap.mp h
  cases i <;> simp_all
  subst a
  exact hi

private theorem nominal_in_clos {p : Problem} {i : Individual} (h : i ∈ p.allIndividuals) :
    .nom i true ∈ clos p := by
  have hm : .nom i true ∈ p.allIndividuals.map (fun a => Concept.nom a true) :=
    List.mem_map_of_mem h
  exact seed_mem_clos (by simp [seeds, hm])

private theorem class_in_clos {p : Problem} {i : Individual} {c : Concept}
    (h : (i,c) ∈ p.classAssertions) : c ∈ clos p := by
  have hm : c ∈ p.classAssertions.map Prod.snd := List.mem_map_of_mem h
  exact seed_mem_clos (by simp [seeds, hm])

private theorem same_ind_in_clos {p : Problem} {a b : Individual}
    (h : (a,b) ∈ p.sameInds) : .nom b true ∈ clos p := by
  apply nominal_in_clos
  have hm : b ∈ p.sameInds.flatMap (fun (x,y) => [x,y]) :=
    List.mem_flatMap.mpr ⟨(a,b),h,by simp⟩
  simp [Problem.allIndividuals, hm]

local macro "init_helper% " n:ident : term =>
  pure (Lean.mkIdent ((Lean.Name.mkNum `_private.Sabrina.OWL2.SROIQD.Branch 0) ++
    `Sabrina.OWL2.SROIQD ++ n.getId))

theorem initial_labels_within {p : Problem} {s : Branch}
    (h : initial p = some s) : LabelsWithin p s := by
  simp only [initial, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ca,hca,same,hsame,_,_,_,_,_,_,_,_,_,_,rfl⟩ := h
  intro x c hc
  simp only [List.mem_cons, List.mem_append] at hc
  rcases hc with (((he | hn) | ha) | hclass) | hsameLabel
  · obtain rfl := (Prod.mk.inj he).2
    exact seed_mem_clos (by simp [seeds])
  · obtain ⟨⟨a,_⟩,ha,he⟩ := List.mem_map.mp hn
    rw [← (Prod.mk.inj he).2]
    exact nominal_in_clos (named_mem_individuals (zipIdx_mem ha))
  · obtain ⟨⟨a,_⟩,ha,he⟩ := List.mem_map.mp ha
    rw [← (Prod.mk.inj he).2]
    exact nominal_in_clos (anonymous_mem_individuals (zipIdx_mem ha))
  · obtain ⟨⟨i,d⟩,hi,hd⟩ := (init_helper% mapM_mem_iff) hca hclass
    obtain ⟨_,_,he⟩ := Option.map_eq_some_iff.mp hd
    rw [← (Prod.mk.inj he).2]
    exact class_in_clos hi
  · obtain ⟨⟨a,b⟩,hi,hd⟩ := (init_helper% mapM_mem_iff) hsame hsameLabel
    obtain ⟨_,_,he⟩ := Option.map_eq_some_iff.mp hd
    rw [← (Prod.mk.inj he).2]
    exact same_ind_in_clos hi

inductive Reachable (p : Problem) : Branch → Prop where
  | initial {s} : SROIQD.initial p = some s → Reachable p s
  | step {s b} {n} {t : Transition p s} : Reachable p s →
      next p s n = some t → b ∈ t.branches → Reachable p b

theorem reachable_labels {p : Problem} {s : Branch} (h : Reachable p s) :
    LabelsWithin p s := by
  induction h with
  | initial hi => exact fun h => initial_labels_within hi h
  | step _ ht hb ih => exact fun h => next_preserves_closure ih ht _ hb h

theorem mem_labelSet_iff {p : Problem} {s : Branch} (h : LabelsWithin p s)
    (x : Nat) (c : Concept) : c ∈ labelSet p s x ↔ (x,c) ∈ s.labels := by
  simp only [labelSet, List.mem_filter, List.contains_iff_mem]
  exact ⟨And.right, fun hc => ⟨h hc,hc⟩⟩

#print axioms initial_labels_within
#print axioms next_preserves_closure
#print axioms reachable_labels
#print axioms mem_labelSet_iff

end Sabrina.OWL2.SROIQD.Termination
