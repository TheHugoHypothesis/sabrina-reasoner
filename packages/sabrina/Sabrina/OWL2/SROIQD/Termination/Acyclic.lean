import Sabrina.OWL2.DecisionProcedure
import Sabrina.OWL2.SROIQD.Termination.Closure

/-! A depth-limited input fragment with propositional GCIs and at most one
named class assertion. The assertion can have nested existential and
universal restrictions in either direction. Type elimination supplies a
finite, explicitly saturated branch for the existing decision interface. -/

namespace Sabrina.OWL2.SROIQD.Termination.Acyclic

open Sabrina.ALC (OrientedRole converse)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.OWL2.DecisionProcedure
open Sabrina.OWL2.Normalize (DatatypeDefs normalizeWithDefs)

def isLocal : Concept → Bool
  | .top | .bottom => true
  | .lit a _ => isCoreClassIRI a
  | .conj a b | .disj a b => isLocal a && isLocal b
  | _ => false

private theorem local_core {c : Concept} (h : isLocal c = true) : c.isCore = true := by
  induction c <;> simp_all [isLocal, Concept.isCore]

/-- The universal GCIs cannot generate role successors. All modal obligations
occur in a single optional named assertion of the ordinary noncounting core.
The construction has no RBox, data axioms, individual equalities or keys. -/
structure Input where
  tbox : List Inclusion
  anchor : Option (IRI × Concept)
  localTBox : ∀ q ∈ tbox, isLocal q.sub = true ∧ isLocal q.sup = true
  coreAnchor : ∀ a ∈ anchor, a.2.isCore = true

def Input.problem (input : Input) : Problem :=
  { tbox := input.tbox
    classAssertions := input.anchor.toList.map (fun (a,c) => (.named a,c)) }

def Input.goal (input : Input) : Concept :=
  input.anchor.elim .top Prod.snd

private theorem core_ordinary {c : Concept} (h : c.isCore = true) :
    c.isOrdinary = true := by
  induction c <;> simp_all [Concept.isCore, Concept.isOrdinary]

theorem problem_ordinary (input : Input) : input.problem.isOrdinary = true := by
  simp only [Problem.isOrdinary, Input.problem, Concept.isOrdinary, List.all_nil,
    Bool.and_eq_true, List.all_eq_true, true_and, and_true]
  refine ⟨?_,?_⟩
  · intro q hq
    exact ⟨core_ordinary (local_core (input.localTBox q hq).1),
      core_ordinary (local_core (input.localTBox q hq).2)⟩
  · intro q hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    exact core_ordinary (input.coreAnchor a (by simpa using ha))

abbrev Row := List Concept

/-- Only the stored labels used in this fragment are included; the datatype
and nominal syntax remains in the common SROIQ(D) closure. -/
def concepts (input : Input) : List Concept :=
  (clos input.problem).filter Concept.isCore

private theorem mem_concepts (input : Input) {c : Concept} (h : c ∈ clos input.problem)
    (hc : c.isCore = true) : c ∈ concepts input :=
  List.mem_filter.mpr ⟨h,hc⟩

private theorem top_mem (input : Input) : Concept.top ∈ concepts input :=
  mem_concepts input (by simp [clos]) rfl

private theorem tbox_side {input : Input} {q : Inclusion} (h : q ∈ input.tbox) :
    q.sub ∈ concepts input ∧ q.sub.dual ∈ concepts input ∧ q.sup ∈ concepts input := by
  have hm (c : Concept) (hc : c ∈ [q.sub,q.sup]) : c ∈ seeds input.problem := by
    have he : c ∈ input.tbox.flatMap (fun e => [e.sub,e.sup]) :=
      List.mem_flatMap.mpr ⟨q,h,hc⟩
    simp [seeds,Input.problem,he]
  have hcore := input.localTBox q h
  have hsub := hm q.sub (by simp)
  have hsup := hm q.sup (by simp)
  exact ⟨mem_concepts input (seed_mem_clos hsub) (local_core hcore.1),
    mem_concepts input (seed_dual_mem_clos hsub) (by rw [Concept.isCore_dual]; exact local_core hcore.1),
    mem_concepts input (seed_mem_clos hsup) (local_core hcore.2)⟩

private theorem goal_mem (input : Input) : input.goal ∈ concepts input := by
  cases h : input.anchor with
  | none => simpa [Input.goal,h] using top_mem input
  | some pair =>
    have hcore := input.coreAnchor pair (by simp [h])
    have hmem : pair.2 ∈ seeds input.problem := by simp [seeds,Input.problem,h]
    simpa [Input.goal,h] using mem_concepts input (seed_mem_clos hmem) hcore

private theorem child_mem {input : Input} {c d : Concept} (hc : c ∈ concepts input)
    (hd : d ∈ operands c) : d ∈ concepts input := by
  have ⟨hc,hcore⟩ := List.mem_filter.mp hc
  apply mem_concepts input (clos_operands hc hd)
  cases c <;> simp_all [Concept.isCore, operands]
  all_goals rcases hd with rfl | rfl <;> first | exact hcore.1 | exact hcore.2

private theorem subset_of_subsets {α : Type} {xs ys : List α}
    (h : ys ∈ subsets xs) : ys ⊆ xs := by
  induction xs generalizing ys with
  | nil => obtain rfl := List.mem_singleton.mp h; exact List.nil_subset _
  | cons x xs ih =>
    rcases List.mem_append.mp h with h | h
    · exact fun _ ha => List.mem_cons_of_mem _ (ih h ha)
    · obtain ⟨rest,hm,rfl⟩ := List.mem_map.mp h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hm ha)

private def coherent (row : Row) : Concept → Bool
  | .bottom => false
  | .lit a b => !(row.contains (.lit a (!b)))
  | .conj a b => row.contains a && row.contains b
  | .disj a b => row.contains a || row.contains b
  | _ => true

private def localCheck (input : Input) (row : Row) : Bool :=
  row.contains .top && row.all (coherent row) &&
    input.tbox.all (fun q => row.contains q.sub.dual || row.contains q.sup)

private def candidates (input : Input) : List Row :=
  (subsets (concepts input)).filter (localCheck input)

private def propagates (r : OrientedRole) (src dst : Row) : Bool :=
  src.all fun
    | .all s body => s != r || dst.contains body
    | _ => true

private theorem propagates_iff {r : OrientedRole} {src dst : Row} :
    propagates r src dst = true ↔ ∀ c, .all r c ∈ src → c ∈ dst := by
  simp only [propagates, List.all_eq_true]
  constructor
  · intro h c hc
    simpa [List.contains_iff_mem] using h (.all r c) hc
  · intro h a ha
    cases a <;> try rfl
    rename_i s c
    by_cases hs : s = r
    · subst s
      simpa [List.contains_iff_mem] using h c ha
    · simp [hs]

private def permits (r : OrientedRole) (src dst : Row) : Bool :=
  propagates r src dst && propagates (converse r) dst src

private theorem permits_flip (r : OrientedRole) (src dst : Row) :
    permits (converse r) dst src = permits r src dst := by
  have hr : converse (converse r) = r := by cases r <;> simp [converse]
  simp only [permits, hr, Bool.and_comm]

private def hasWitnesses (pool : List Row) (row : Row) : Bool :=
  row.all fun
    | .some r c => pool.any (fun dst => permits r row dst && dst.contains c)
    | _ => true

private theorem hasWitnesses_iff {pool : List Row} {row : Row} :
    hasWitnesses pool row = true ↔ ∀ r c, .some r c ∈ row →
      ∃ dst ∈ pool, permits r row dst = true ∧ c ∈ dst := by
  simp only [hasWitnesses, List.all_eq_true]
  constructor
  · intro h r c hc
    simpa [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] using h (.some r c) hc
  · intro h a ha
    cases a <;> try rfl
    rename_i r body
    simpa [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] using h r body ha

private def prune (pool : List Row) : List Row := pool.filter (hasWitnesses pool)

private theorem prune_sublist (pool : List Row) : (prune pool).Sublist pool := List.filter_sublist

/-- The finite pool strictly shrinks at each recursive call. The threshold
below is the mathematical progress test, independent of budgets or fuel. -/
private def stabilize (pool : List Row) : List Row :=
  if _h : (prune pool).length < pool.length then stabilize (prune pool) else pool
termination_by pool.length

private theorem stabilize_subset (pool : List Row) : stabilize pool ⊆ pool := by
  rw [stabilize]
  split
  · exact fun _ h => (prune_sublist pool).subset (stabilize_subset (prune pool) h)
  · exact fun _ h => h
termination_by pool.length

private theorem stabilize_fixed (pool : List Row) :
    prune (stabilize pool) = stabilize pool := by
  rw [stabilize]
  split
  · exact stabilize_fixed (prune pool)
  · rename_i hn
    apply (prune_sublist pool).eq_of_length
    have := (prune_sublist pool).length_le
    omega
termination_by pool.length

private def survivors (input : Input) : List Row := stabilize (candidates input)

private theorem survivor_concepts {input : Input} {row : Row} (hr : row ∈ survivors input) :
    row ⊆ concepts input :=
  subset_of_subsets (List.mem_filter.mp (stabilize_subset _ hr)).1

private theorem survivor_local {input : Input} {row : Row} (hr : row ∈ survivors input) :
    localCheck input row = true :=
  (List.mem_filter.mp (stabilize_subset _ hr)).2

private theorem survivor_witness {input : Input} {row : Row} (hr : row ∈ survivors input) :
    hasWitnesses (survivors input) row = true := by
  have hf := stabilize_fixed (candidates input)
  have hp : row ∈ prune (survivors input) := hf.symm ▸ hr
  exact (List.mem_filter.mp hp).2

private noncomputable def realized (input : Input) (i : Interpretation datatypeMap)
    (x : i.Object) : Row := by
  classical
  exact (concepts input).filter (fun c => decide (holds i x c))

private theorem mem_realized {input : Input} {i : Interpretation datatypeMap} {x : i.Object}
    {c : Concept} : c ∈ realized input i x ↔ c ∈ concepts input ∧ holds i x c := by
  classical
  simp [realized, List.mem_filter]

private theorem realized_local {input : Input} {i : Interpretation datatypeMap}
    (hm : input.problem.Models i) (x : i.Object) : localCheck input (realized input i x) = true := by
  classical
  simp only [localCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true]
  refine ⟨⟨mem_realized.mpr ⟨top_mem input, trivial⟩, ?_⟩, ?_⟩
  · intro c hc
    have ⟨hc,hh⟩ := mem_realized.mp hc
    cases c with
    | bottom => exact hh.elim
    | lit a b =>
      have hn : (.lit a (!b) : Concept) ∉ realized input i x :=
        fun hbad => (holds_dual i x (.lit a b)).mp (mem_realized.mp hbad).2 hh
      simp [coherent, hn]
    | conj a b =>
      simp only [coherent, Bool.and_eq_true, List.contains_iff_mem]
      exact ⟨mem_realized.mpr ⟨child_mem hc (by simp [operands]),hh.1⟩,
        mem_realized.mpr ⟨child_mem hc (by simp [operands]),hh.2⟩⟩
    | disj a b =>
      simp only [coherent, Bool.or_eq_true, List.contains_iff_mem]
      rcases hh with ha | hb
      · exact .inl (mem_realized.mpr ⟨child_mem hc (by simp [operands]),ha⟩)
      · exact .inr (mem_realized.mpr ⟨child_mem hc (by simp [operands]),hb⟩)
    | _ => rfl
  · intro q hq
    obtain ⟨_,hdual,hsup⟩ := tbox_side hq
    simp only [Bool.or_eq_true, List.contains_iff_mem]
    by_cases hsub : holds i x q.sub
    · exact .inr (mem_realized.mpr ⟨hsup,hm.tbox q hq x hsub⟩)
    · exact .inl (mem_realized.mpr ⟨hdual,(holds_dual i x q.sub).mpr hsub⟩)

private theorem realized_candidate {input : Input} {i : Interpretation datatypeMap}
    (hm : input.problem.Models i) (x : i.Object) : realized input i x ∈ candidates input := by
  classical
  apply List.mem_filter.mpr
  exact ⟨filter_mem_subsets _ _, realized_local hm x⟩

private theorem holds_flip {i : Interpretation datatypeMap} {r : OrientedRole} {x y : i.Object} :
    holdsOriented i r x y → holdsOriented i (converse r) y x := by
  rcases r with ⟨r,_ | _⟩ <;> exact id

private theorem realized_propagates (input : Input) {i : Interpretation datatypeMap}
    {x y : i.Object} {r : OrientedRole} (he : holdsOriented i r x y) :
    propagates r (realized input i x) (realized input i y) = true := by
  apply propagates_iff.mpr
  intro c hc
  obtain ⟨hcc, h⟩ := mem_realized.mp hc
  exact mem_realized.mpr ⟨child_mem hcc (by simp [operands]),h y he⟩

private theorem realized_prunes {input : Input} {i : Interpretation datatypeMap}
    {pool : List Row} (hpool : ∀ x : i.Object, realized input i x ∈ pool) (x : i.Object) :
    realized input i x ∈ prune pool := by
  refine List.mem_filter.mpr ⟨hpool x, hasWitnesses_iff.mpr ?_⟩
  intro r c hc
  obtain ⟨hcc,y,hr,hy⟩ := mem_realized.mp hc
  exact ⟨_,hpool y,Bool.and_eq_true_iff.mpr
    ⟨realized_propagates input hr,realized_propagates input (holds_flip hr)⟩,
    mem_realized.mpr ⟨child_mem hcc (by simp [operands]),hy⟩⟩

private theorem realized_stabilizes {input : Input} {i : Interpretation datatypeMap}
    (pool : List Row) (hpool : ∀ x : i.Object, realized input i x ∈ pool) (x : i.Object) :
    realized input i x ∈ stabilize pool := by
  rw [stabilize]
  split
  · exact realized_stabilizes (prune pool) (realized_prunes hpool) x
  · exact hpool x
termination_by pool.length

private def pick (input : Input) : Option Row :=
  (survivors input).find? (fun row => row.contains input.goal)

private theorem pick_mem {input : Input} {row : Row} (h : pick input = some row) :
    row ∈ survivors input ∧ input.goal ∈ row :=
  ⟨List.mem_of_find?_eq_some h,
    List.contains_iff_mem.mp (List.find?_some (p := fun (r : Row) => r.contains input.goal) h)⟩

private theorem pick_complete {input : Input} (hs : input.problem.Sat) :
    ∃ row, pick input = some row := by
  obtain ⟨i,hm,root,_⟩ := hs
  have hex : ∃ x, holds i x input.goal := by
    cases h : input.anchor with
    | none => exact ⟨root, by simp [Input.goal,h,holds]⟩
    | some ac =>
      refine ⟨i.individuals (.named ac.1), ?_⟩
      simpa [Input.goal,h] using
        hm.classAssertions (.named ac.1,ac.2) (by simp [Input.problem,h])
  obtain ⟨x,hx⟩ := hex
  have hs := realized_stabilizes (candidates input) (realized_candidate hm) x
  have hg := mem_realized.mpr ⟨goal_mem input,hx⟩
  cases hp : pick input with
  | some row => exact ⟨row,rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp hp _ hs
    rw [List.contains_iff_mem.mpr hg] at hnone
    contradiction

private def table (input : Input) (first : Row) : List (Row × Nat) :=
  (first :: survivors input).zipIdx

private theorem table_first (input : Input) (first : Row) :
    (first,0) ∈ table input first := by simp [table, List.zipIdx]

private theorem table_row {input : Input} {first row : Row} {x : Nat}
    (hf : first ∈ survivors input) (h : (row,x) ∈ table input first) :
    row ∈ survivors input := by
  have hr : row ∈ first :: survivors input :=
    List.mem_of_getElem (List.mem_zipIdx h).2.2.symm
  exact (List.mem_cons.mp hr).elim (· ▸ hf) id

private theorem table_index {input : Input} {first row other : Row} {x : Nat}
    (h : (row,x) ∈ table input first) (h' : (other,x) ∈ table input first) :
    row = other :=
  (List.mem_zipIdx h).2.2.trans (List.mem_zipIdx h').2.2.symm

private theorem table_reaches {input : Input} {first row : Row}
    (h : row ∈ survivors input) : ∃ x, (row,x) ∈ table input first := by
  have hmem : row ∈ (table input first).map Prod.fst := by
    simp [table, List.mem_cons, h]
  obtain ⟨⟨r,x⟩,hm,rfl⟩ := List.mem_map.mp hmem
  exact ⟨x,hm⟩

private def conceptRole : Concept → Option IRI
  | .all r _ | .some r _ => some r.1
  | _ => none

private def roleNames (input : Input) : List IRI :=
  (concepts input).filterMap conceptRole

private theorem some_role {input : Input} {row : Row} {r : OrientedRole} {c : Concept}
    (hr : row ∈ survivors input) (hc : .some r c ∈ row) : r.1 ∈ roleNames input :=
  List.mem_filterMap.mpr ⟨.some r c,survivor_concepts hr hc,rfl⟩

private theorem ordinary_role {input : Input} {r : IRI} (hr : r ∈ roleNames input) :
    isCoreObjPropIRI r = true := by
  obtain ⟨c,hc,he⟩ := List.mem_filterMap.mp hr
  obtain ⟨_,h⟩ := List.mem_filter.mp hc
  cases c <;> simp_all [conceptRole, Concept.isCore]

private def materialize (input : Input) (first : Row) : Branch :=
  let ts := table input first
  { labels := ts.flatMap fun (row,x) => row.map (x, ·)
    edges := (roleNames input).flatMap fun r =>
      ts.flatMap fun (src,x) =>
        (ts.filter fun (dst,_) => permits (r,false) src dst).map fun (_,y) => (r,x,y)
    noms := input.anchor.toList.map (fun a => (a.1,0)) }

private theorem label_iff {input : Input} {first : Row} {x : Nat} {c : Concept} :
    (x,c) ∈ (materialize input first).labels ↔
      ∃ row, (row,x) ∈ table input first ∧ c ∈ row := by
  simp only [materialize, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨row,n⟩,hr,d,hd,he⟩
    cases he
    exact ⟨row,hr,hd⟩
  · rintro ⟨row,hr,hc⟩
    exact ⟨(row,x),hr,c,hc,rfl⟩

private theorem stored_edge_iff {input : Input} {first : Row} {r : IRI} {x y : Nat} :
    (r,x,y) ∈ (materialize input first).edges ↔
      r ∈ roleNames input ∧ ∃ src dst, (src,x) ∈ table input first ∧
        (dst,y) ∈ table input first ∧ permits (r,false) src dst = true := by
  simp only [materialize, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨s,hs,⟨src,n⟩,hn,⟨dst,k⟩,⟨hk,hp⟩,he⟩
    cases he
    exact ⟨hs,src,dst,hn,hk,hp⟩
  · rintro ⟨hr,src,dst,hs,hd,hp⟩
    exact ⟨r,hr,(src,x),hs,(dst,y),⟨hd,hp⟩,rfl⟩

private theorem edge_iff {input : Input} {first : Row} {r : OrientedRole} {x y : Nat} :
    (materialize input first).edge r x y = true ↔
      r.1 ∈ roleNames input ∧ ∃ src dst, (src,x) ∈ table input first ∧
        (dst,y) ∈ table input first ∧ permits r src dst = true := by
  rcases r with ⟨r,_ | _⟩
  · change List.contains _ (r,x,y) = true ↔ _
    rw [List.contains_iff_mem]
    exact stored_edge_iff
  · change List.contains _ (r,y,x) = true ↔ _
    rw [List.contains_iff_mem, stored_edge_iff]
    constructor
    · rintro ⟨hr,dst,src,hd,hs,hp⟩
      exact ⟨hr,src,dst,hs,hd,(permits_flip (r,false) dst src).trans hp⟩
    · rintro ⟨hr,src,dst,hs,hd,hp⟩
      exact ⟨hr,dst,src,hd,hs,(permits_flip (r,false) dst src).symm.trans hp⟩

private theorem table_of_support {input : Input} {first : Row} {x : Nat}
    (h : x ∈ (materialize input first).support) : ∃ row, (row,x) ∈ table input first := by
  let b := materialize input first
  change x ∈ (b.labels.map Prod.fst ++ b.edges.flatMap (fun (_,a,c) => [a,c])) ++
    ([] : List Nat) ++ [] ++ b.noms.map Prod.snd ++ [] ++ [] ++ [] ++ [] at h
  simp only [List.append_nil, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨⟨_,c⟩,hm,rfl⟩ := List.mem_map.mp h
    obtain ⟨row,hr,_⟩ := label_iff.mp hm
    exact ⟨row,hr⟩
  · obtain ⟨⟨r,a,c⟩,he,hx⟩ := List.mem_flatMap.mp h
    obtain ⟨_,src,dst,hs,hd,_⟩ := stored_edge_iff.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨src,hs⟩
    · exact ⟨dst,hd⟩
  · obtain ⟨_,hm,rfl⟩ := List.mem_map.mp h
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hm
    exact ⟨first,table_first input first⟩

private theorem row_top {input : Input} {row : Row} (h : row ∈ survivors input) :
    .top ∈ row :=
  List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (survivor_local h)).1).1

private theorem row_coherent {input : Input} {row : Row} {c : Concept}
    (hr : row ∈ survivors input) (hc : c ∈ row) : coherent row c = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (survivor_local hr)).1).2 c hc

private theorem label_core {input : Input} {first : Row}
    (hf : first ∈ survivors input) {x : Nat} {c : Concept}
    (h : (x,c) ∈ (materialize input first).labels) : c.isCore = true := by
  obtain ⟨row,ht,hc⟩ := label_iff.mp h
  exact (List.mem_filter.mp (survivor_concepts (table_row hf ht) hc)).2

private theorem open_clash_free {input : Input} {first : Row} (hf : first ∈ survivors input) :
    (materialize input first).CoreClashFree := by
  constructor
  · intro x h
    obtain ⟨row,ht,hc⟩ := label_iff.mp h
    have hcheck := row_coherent (table_row hf ht) hc
    contradiction
  · intro x a ha hn
    obtain ⟨pos,hp,hp'⟩ := label_iff.mp ha
    obtain ⟨neg,hn,hn'⟩ := label_iff.mp hn
    obtain rfl := table_index hp hn
    have hb := row_coherent (table_row hf hp) hp'
    simp [coherent, hn'] at hb

private theorem table_top {input : Input} {first row : Row} {x : Nat}
    (hf : first ∈ survivors input) (hr : (row,x) ∈ table input first) :
    (x,.top) ∈ (materialize input first).labels :=
  label_iff.mpr ⟨row,hr,row_top (table_row hf hr)⟩

private theorem anchor_index {input : Input} {first : Row} {a : IRI} {c : Concept}
    (h : input.anchor = some (a,c)) (h0 : 0 ∈ (materialize input first).support) :
    ((materialize input first).indNode h0 (.named a)).val = 0 := by
  simp only [Branch.indNode]
  split
  · rename_i k hk
    change List.lookup a (input.anchor.toList.map (fun pair => (pair.1,0))) = some k at hk
    simpa [h] using hk.symm
  · rfl

private theorem open_saturated {input : Input} {first : Row}
    (hf : first ∈ survivors input) (hg : input.goal ∈ first) :
    (materialize input first).SROIQDSaturated input.problem := by
  constructor
  case root => exact table_top hf (table_first input first)
  case conj =>
    intro x a b hl
    obtain ⟨row,hr,hc⟩ := label_iff.mp hl
    have hc := row_coherent (table_row hf hr) hc
    simp only [coherent, Bool.and_eq_true, List.contains_iff_mem] at hc
    exact ⟨label_iff.mpr ⟨row,hr,hc.1⟩, label_iff.mpr ⟨row,hr,hc.2⟩⟩
  case disj =>
    intro x a b hl
    obtain ⟨row,hr,hc⟩ := label_iff.mp hl
    have hc := row_coherent (table_row hf hr) hc
    simp only [coherent, Bool.or_eq_true, List.contains_iff_mem] at hc
    exact hc.imp (fun ha => label_iff.mpr ⟨row,hr,ha⟩) (fun hb => label_iff.mpr ⟨row,hr,hb⟩)
  case some =>
    intro x r c hl
    obtain ⟨src,hx,hl⟩ := label_iff.mp hl
    have hm := table_row hf hx
    obtain ⟨dst,hd,hp,hc⟩ := hasWitnesses_iff.mp (survivor_witness hm) r c hl
    obtain ⟨y,hy⟩ := table_reaches (first := first) hd
    exact ⟨y,edge_iff.mpr ⟨some_role hm hl,src,dst,hx,hy,hp⟩,label_iff.mpr ⟨dst,hy,hc⟩⟩
  case all =>
    intro x r c hl y he
    obtain ⟨row,hr,hc⟩ := label_iff.mp hl
    obtain ⟨_,src,dst,hs,hd,hp⟩ := edge_iff.mp he
    obtain rfl := table_index hr hs
    exact label_iff.mpr ⟨dst,hd,propagates_iff.mp (Bool.and_eq_true_iff.mp hp).1 c hc⟩
  case tbox =>
    intro q hq x hx
    obtain ⟨row,hr⟩ := table_of_support hx
    have hq := List.all_eq_true.mp
      (Bool.and_eq_true_iff.mp (survivor_local (table_row hf hr))).2 q hq
    simp only [Bool.or_eq_true, List.contains_iff_mem] at hq
    exact hq.imp (fun hd => label_iff.mpr ⟨row,hr,hd⟩) (fun hs => label_iff.mpr ⟨row,hr,hs⟩)
  case classAssertions =>
    intro ac hac
    cases h : input.anchor with
    | none => simp [Input.problem,h] at hac
    | some pair =>
      rcases pair with ⟨a,c⟩
      have he : ac = (.named a,c) := by simpa [Input.problem,h] using hac
      subst ac
      simp only [anchor_index h]
      exact label_iff.mpr ⟨first,table_first input first,by simpa [Input.goal,h] using hg⟩
  all_goals first
    | (simp [Input.problem]; done)
    | (intros; have hc := label_core hf (by assumption); contradiction)

private theorem materialized_sat {input : Input} {first : Row}
    (hf : first ∈ survivors input) (hg : input.goal ∈ first) :
    (materialize input first).Sat input.problem := by
  let b := materialize input first
  have cf := open_clash_free hf
  have hs := open_saturated hf hg
  have h0 : 0 ∈ b.support := Branch.label_support hs.root
  let i := b.toSROIQDInterpretation h0
  let env (x : Nat) : i.Object := if hx : x ∈ b.support then ⟨x,hx⟩ else ⟨0,h0⟩
  have env_of_support {x : Nat} (hx : x ∈ b.support) : env x = ⟨x,hx⟩ := dite_eq_left hx
  refine ⟨i, ?_, env, ?_⟩
  · refine ⟨?_, ?_, hs.chains, hs.reflexive, hs.irreflexive, hs.asymmetric,
      hs.disjoint, hs.subData, hs.disjointData, hs.funcData, hs.dataRanges, hs.keys,
      ?_, hs.objAssertions, hs.negObjAssertions, hs.sameInds, hs.diffInds,
      hs.dataAssertions, hs.negDataAssertions⟩
    · intro q hq x hsub
      have ht := input.localTBox q hq
      rcases hs.tbox q hq x.val x.property with hdual | hsup
      · exact ((sroiqd_saturated_holds_pair cf hs (core_ordinary (local_core ht.1))).2
          x hdual hsub).elim
      · exact sroiqd_saturated_holds cf hs x (core_ordinary (local_core ht.2)) hsup
    · simp [Input.problem]
    · intro ac hac
      have hl := hs.classAssertions ac hac
      exact sroiqd_saturated_holds cf hs (b.indNode h0 ac.1) (core_ordinary (label_core hf hl)) hl
  · constructor
    case labels =>
      intro x c hl
      rw [env_of_support (Branch.label_support hl)]
      exact sroiqd_saturated_holds cf hs _ (core_ordinary (label_core hf hl)) hl
    case edges =>
      intro r x y he
      obtain ⟨hr,src,dst,hx,hy,_⟩ := stored_edge_iff.mp he
      rw [env_of_support (Branch.label_support (table_top hf hx)),
          env_of_support (Branch.label_support (table_top hf hy))]
      have hord := ordinary_role hr
      simp only [isCoreObjPropIRI, Bool.and_eq_true, bne_iff_ne] at hord
      change (if r = topObjectProperty then True else if r = bottomObjectProperty
        then False else (r,x,y) ∈ b.edges)
      simpa [hord.1,hord.2] using he
    case noms =>
      intro a x hn
      cases h : input.anchor with
      | none => simp [materialize,h] at hn
      | some pair =>
        rcases pair with ⟨n,c⟩
        have he : a = n ∧ x = 0 := by simpa [materialize,h] using hn
        rcases he with ⟨rfl,rfl⟩
        apply Subtype.ext
        rw [env_of_support h0]
        exact (anchor_index h h0).symm
    all_goals simp [materialize]

private def branchDecEq : DecidableEq Branch := fun a b => by
  cases a
  cases b
  simp only [Branch.mk.injEq]
  infer_instance

private def openRules {p : Problem} (leaf : Branch) (model : leaf.Sat p)
    (clashFree : leaf.CoreClashFree) (saturated : leaf.SROIQDSaturated p) :
    TerminatingRuleSet p := by
  letI := branchDecEq
  exact {
    measure := fun s => if s = leaf then 0 else 1
    step := fun s => if s = leaf then none else
      some ⟨[leaf], fun _ => ⟨leaf,List.mem_singleton_self _,model⟩⟩
    decreases := by
      intro s t ht b hb
      split at ht
      · contradiction
      · rename_i hne
        cases ht
        obtain rfl := List.mem_singleton.mp hb
        simp [hne]
    fair := by
      intro s hs
      split at hs
      · rename_i he
        subst s
        exact ⟨clashFree,saturated⟩
      · contradiction }

private def closedRules {p : Problem} (refuted : ∀ s : Branch, ¬ s.Sat p) :
    TerminatingRuleSet p where
  measure := fun _ => 0
  step s := some ⟨[], fun hs => (refuted s hs).elim⟩
  decreases := by intro s t ht b hb; cases ht; contradiction
  fair := by intro s hs; contradiction

/-- Run finite type elimination, then expose its result through the existing
transition interface. A successful result redirects to its canonical branch
in one step. This preserves existence of a model, as required by
`Transition`, even when the source branch contains other assertions. -/
def terminatingRules (input : Input) : TerminatingRuleSet input.problem :=
  match h : pick input with
  | some first =>
    let hm := pick_mem h
    openRules (materialize input first) (materialized_sat hm.1 hm.2)
      (open_clash_free hm.1) (open_saturated hm.1 hm.2)
  | none => closedRules fun _ hs => by
    obtain ⟨i,hm,_⟩ := hs
    obtain ⟨x⟩ := i.objectNonempty
    obtain ⟨row,hrow⟩ := pick_complete (input := input) ⟨i,hm,x,True.intro⟩
    rw [h] at hrow
    contradiction

/-- Every selected leaf stores `⊤` at each of its supported nodes. -/
theorem terminal_top (input : Input) (s : Branch)
    (h : (terminatingRules input).step s = none) :
    ∀ x ∈ s.support, (x,.top) ∈ s.labels := by
  unfold terminatingRules at h
  split at h
  · rename_i row hp
    have he : s = materialize input row := by
      unfold openRules at h
      dsimp only at h
      split at h <;> first | assumption | contradiction
    subst s
    intro x hx
    obtain ⟨r,hr⟩ := table_of_support hx
    exact table_top (pick_mem hp).1 hr
  · contradiction

theorem decide_ontology_iff {o : Ontology} {defs : DatatypeDefs} {input : Input} {s : Branch}
    (hnorm : normalizeWithDefs o = some (defs,input.problem))
    (hinit : initial input.problem = some s) :
    ((∃ openB, decideBranch (terminatingRules input) s = .sat openB) ↔ Satisfiable datatypeMap o) ∧
    ((∃ d, decideBranch (terminatingRules input) s = .unsat d) ↔ ¬ Satisfiable datatypeMap o) :=
  decideBranch_ontology_iff (terminatingRules input) hnorm rfl (problem_ordinary input) hinit

private theorem core_no_individuals {c : Concept} (hc : c.isCore = true) :
    c.individuals = [] := by
  induction c <;> simp_all [Concept.isCore, Concept.individuals]

theorem initial_exists (input : Input) : ∃ s, initial input.problem = some s := by
  have ht : input.tbox.flatMap (fun q => q.sub.individuals ++ q.sup.individuals) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    have hc := input.localTBox q hq
    simp [core_no_individuals (local_core hc.1), core_no_individuals (local_core hc.2)]
  cases h : input.anchor with
  | none =>
    simp [initial, Problem.nominals, Problem.anons, Problem.allIndividuals,
      Concept.individuals, Input.problem, h, ht]
  | some ac =>
    rcases ac with ⟨a,c⟩
    have hc := core_no_individuals (input.coreAnchor (a,c) (by simp [h]))
    simp [initial, Problem.nominals, Problem.anons, Problem.allIndividuals,
      Concept.individuals, Input.problem, h, ht, hc]
    have lookup : List.lookup a ([(a,1)] : List (IRI × Nat)) = some 1 := List.lookup_cons_self
    refine ⟨{labels := [(0,.top),(1,.nom (.named a) true),(1,c)], noms := [(a,1)]}, ?_⟩
    change (((List.lookup a ([(a,1)] : List (IRI × Nat))).map (·,c)).bind
      (fun ac => some [ac])).bind (fun labels =>
      some ({ labels := (0,.top) :: (1,.nom (.named a) true) :: labels
              noms := [(a,1)] } : Branch)) = _
    rw [lookup]
    rfl

private theorem initial_isSome (input : Input) : (initial input.problem).isSome = true := by
  obtain ⟨s,hs⟩ := initial_exists input
  simp [hs]

private def start (input : Input) : Branch :=
  (initial input.problem).get (initial_isSome input)

private theorem initial_start (input : Input) : initial input.problem = some (start input) :=
  (Option.some_get (initial_isSome input)).symm

/-- Total entry point for a bounded-depth normalized problem. -/
def run (input : Input) : TableauDecision :=
  decideBranch (terminatingRules input) (start input)

theorem run_ontology_iff {o : Ontology} {defs : DatatypeDefs} {input : Input}
    (hnorm : normalizeWithDefs o = some (defs,input.problem)) :
    ((∃ openB, run input = .sat openB) ↔ Satisfiable datatypeMap o) ∧
    ((∃ d, run input = .unsat d) ↔ ¬ Satisfiable datatypeMap o) :=
  decide_ontology_iff hnorm (initial_start input)

section Regression

private def topConjunction : Input where
  tbox := []
  anchor := some ("urn:sabrina:termination:anchor",.conj .top .top)
  localTBox := by simp
  coreAnchor := by
    intro a h
    have ha := Option.mem_def.mp h
    injection ha with e
    subst a
    rfl

private def inverseContradiction : Input where
  tbox := []
  anchor := some ("urn:sabrina:termination:anchor",
    .some ("urn:sabrina:termination:edge",false) (.all ("urn:sabrina:termination:edge",true) .bottom))
  localTBox := by simp
  coreAnchor := by
    intro a h
    have ha := Option.mem_def.mp h
    injection ha with e
    subst a
    decide

private def topConjunctionOntology : Ontology := topConjunction.problem.toOntology.reverse
private def inverseContradictionOntology : Ontology := inverseContradiction.problem.toOntology.reverse

#guard (match run topConjunction with | .sat _ => true | .unsat _ => false)

private theorem top_conjunction_pick : (pick topConjunction).isSome = true := by decide +kernel

private theorem inverse_contradiction_decides :
    (match run inverseContradiction with | .sat _ => false | .unsat _ => true) = true := by decide +kernel

theorem top_conjunction_satisfiable : Satisfiable datatypeMap topConjunctionOntology := by
  have hp := top_conjunction_pick
  cases h : pick topConjunction with
  | none => simp [h] at hp
  | some row =>
    obtain ⟨hm,hg⟩ := pick_mem h
    apply (Normalize.normalizeWithDefs_sat_iff (o := topConjunctionOntology) (defs := [])
      (p := topConjunction.problem) rfl).mpr
    apply (satisfiable_iff_sat topConjunction.problem rfl).mpr
    exact sroiqd_saturated_sat (problem_ordinary topConjunction)
      (open_clash_free hm) (open_saturated hm hg)

theorem inverse_contradiction_unsatisfiable :
    ¬ Satisfiable datatypeMap inverseContradictionOntology := by
  apply (run_ontology_iff (o := inverseContradictionOntology) (input := inverseContradiction) rfl).2.mp
  have h := inverse_contradiction_decides
  cases e : run inverseContradiction <;> simp_all

end Regression

end Sabrina.OWL2.SROIQD.Termination.Acyclic

namespace Sabrina.OWL2.SROIQD

/-- Propositional GCIs with at most one named class assertion in ordinary ALCI.
All modality is confined to the finite-depth assertion. The remaining
normalized problem fields, including the query root, have default values. -/
def Problem.isBoundedDepth (p : Problem) : Prop :=
  ∃ input : Termination.Acyclic.Input, input.problem = p

theorem Problem.boundedDepth_hasRuleSet {p : Problem} (h : p.isBoundedDepth) :
    Nonempty (Sabrina.OWL2.DecisionProcedure.TerminatingRuleSet p) := by
  obtain ⟨input,rfl⟩ := h
  exact ⟨Termination.Acyclic.terminatingRules input⟩

#print axioms Termination.Acyclic.terminatingRules
#print axioms Termination.Acyclic.terminal_top
#print axioms Termination.Acyclic.decide_ontology_iff
#print axioms Termination.Acyclic.run_ontology_iff
#print axioms Termination.Acyclic.top_conjunction_satisfiable
#print axioms Termination.Acyclic.inverse_contradiction_unsatisfiable
#print axioms Problem.boundedDepth_hasRuleSet

end Sabrina.OWL2.SROIQD
