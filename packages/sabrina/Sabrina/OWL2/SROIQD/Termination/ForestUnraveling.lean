import Sabrina.OWL2.SROIQD.Termination.BlockedForest

/-!
Infinite forest-unraveling model construction and dual Truth Lemma for full
cyclic `SROIQ` (including nominals, ABoxes, regular role chains, inverse roles,
qualified number restrictions, and object `HasKey` axioms).
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse holdsRole)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)
open Sabrina.RoleChains (Rank PathRegex)
open Sabrina.RoleChains.SimpleRoles (Simple)
open Sabrina.RoleChains.TransitivePaths (WordPath converse_converse)
open Sabrina.RoleChains.RankedPaths (Generated complete normalize)

namespace BlockedForest

variable {b : BlockedForest}

/-! ### Unraveled forest paths -/

def walkTail (b : BlockedForest) (start : b.Node) : List b.Node → b.Node
  | [] => start
  | c :: _ => b.target c

inductive Walk (b : BlockedForest) (start : b.Node) : List b.Node → Prop where
  | root : b.isRoot start = true → Walk b start []
  | step {xs c} : Walk b start xs → b.Child (b.walkTail start xs) c → Walk b start (c :: xs)

structure Path (b : BlockedForest) where
  start : b.Node
  steps : List b.Node
  valid : b.Walk start steps

namespace Path

theorem ext {x y : b.Path} (hs : x.start = y.start) (hl : x.steps = y.steps) : x = y := by
  cases x; cases y; cases hs; cases hl; rfl

def root (b : BlockedForest) (r : b.Node) (hr : b.isRoot r = true) : b.Path :=
  ⟨r, [], .root hr⟩

def root0 (b : BlockedForest) : b.Path :=
  root b 0 b.root0

def tailNode (x : b.Path) : b.Node := b.walkTail x.start x.steps

def extend (x : b.Path) (c : b.Node) (hc : b.Child x.tailNode c) : b.Path :=
  ⟨x.start, c :: x.steps, .step x.valid hc⟩

theorem valid_cons {start : b.Node} {xs : List b.Node} {c : b.Node}
    (h : b.Walk start (c :: xs)) :
    b.Walk start xs ∧ b.Child (b.walkTail start xs) c := by
  cases h with
  | step hs hc => exact ⟨hs, hc⟩

theorem start_isRoot (x : b.Path) : b.isRoot x.start = true := by
  cases x with
  | mk s xs h =>
    induction h with
    | root hr => exact hr
    | step _ _ ih => exact ih

theorem tail_unblocked (hw : b.BlockingValid) (x : b.Path) : b.Unblocked x.tailNode := by
  cases x with
  | mk s xs h =>
    induction h with
    | root hr => exact root_unblocked hw hr
    | step _ hc ih => exact child_target_unblocked hw ih hc

theorem steps_nil_iff_tail_root (hw : b.BlockingValid) (x : b.Path) :
    x.steps = [] ↔ b.isRoot x.tailNode = true := by
  cases hx : x.steps with
  | nil =>
    simp only [tailNode, hx, walkTail, true_iff]
    exact x.start_isRoot
  | cons c rest =>
    simp only [tailNode, hx, walkTail, reduceCtorEq, false_iff]
    have hc := (valid_cons (hx ▸ x.valid)).2
    have hf := target_not_root hw hc.1
    simp [hf]

theorem extend_injective (x : b.Path) {c d : b.Node}
    {hc : b.Child x.tailNode c} {hd : b.Child x.tailNode d}
    (h : x.extend c hc = x.extend d hd) : c = d :=
  (List.cons.inj (congrArg Path.steps h)).1

/-- Canonical path ending at any unblocked node `x`. -/
def canonical (b : BlockedForest) (hw : b.BlockingValid) (x : b.Node)
    (hu : b.Unblocked x) : {p : b.Path // p.tailNode = x} :=
  if hr : b.isRoot x = true then
    ⟨Path.root b x hr, rfl⟩
  else
    have hnr : b.isRoot x = false := Bool.eq_false_iff.mpr hr
    have hch : b.Child (b.parent x) x := ⟨hnr, rfl⟩
    have hpu : b.Unblocked (b.parent x) := unblocked_ancestor hu (.parent hch)
    let p := canonical b hw (b.parent x) hpu
    ⟨p.val.extend x (p.property.symm ▸ hch), by
      change b.target x = x
      exact target_of_unblocked hu⟩
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr hr)

theorem canonical_tailNode (hw : b.BlockingValid) (x : b.Node) (hu : b.Unblocked x) :
    (canonical b hw x hu).val.tailNode = x :=
  (canonical b hw x hu).property

theorem canonical_root (hw : b.BlockingValid) {x : b.Node} (hu : b.Unblocked x)
    (hr : b.isRoot x = true) :
    (canonical b hw x hu).val = Path.root b x hr := by
  unfold canonical
  rw [dite_eq_left hr]

theorem canonical_child (hw : b.BlockingValid) {x y : b.Node}
    (hux : b.Unblocked x) (huy : b.Unblocked y) (hc : b.Child x y) :
    ∃ (hch : b.Child (canonical b hw x hux).val.tailNode y),
      (canonical b hw y huy).val = (canonical b hw x hux).val.extend y hch := by
  have hnr : ¬ (b.isRoot y = true) := by simp [hc.1]
  have hpar := hc.2
  refine ⟨(canonical_tailNode hw x hux).symm ▸ hc, ?_⟩
  have hunfold : (canonical b hw y huy).val =
      (canonical b hw (b.parent y) (unblocked_ancestor huy (.parent ⟨hc.1, rfl⟩))).val.extend y
        ((canonical_tailNode hw (b.parent y) _).symm ▸ ⟨hc.1, rfl⟩) := by
    rw [canonical, dite_eq_right hnr]
  rw [hunfold]
  apply Path.ext
  · change (canonical b hw (b.parent y) _).val.start = (canonical b hw x hux).val.start
    cases hpar; rfl
  · change y :: (canonical b hw (b.parent y) _).val.steps = y :: (canonical b hw x hux).val.steps
    cases hpar; rfl

end Path

/-! ### Base graph of the forest unraveling -/

def Base (b : BlockedForest) (r : OrientedRole) (x y : b.Path) : Prop :=
  (y = x ∧ r.1 ∈ b.loops x.tailNode) ∨
  (x.steps = [] ∧ y.steps = [] ∧ b.RootEdge r x.start y.start) ∨
  (∃ c, y.start = x.start ∧ y.steps = c :: x.steps ∧ b.Down r c) ∨
  (∃ c, x.start = y.start ∧ x.steps = c :: y.steps ∧ b.Down (converse r) c) ∨
  (x.steps ≠ [] ∧ y.steps = [] ∧ (r, y.start) ∈ b.toRoot x.tailNode) ∨
  (x.steps = [] ∧ y.steps ≠ [] ∧ (converse r, x.start) ∈ b.toRoot y.tailNode)

theorem base_flip {r : OrientedRole} {x y : b.Path}
    (he : b.Base r x y) : b.Base (converse r) y x := by
  rcases he with ⟨rfl, h⟩ | ⟨hx, hy, h⟩ | ⟨c, hs, hl, hd⟩ | ⟨c, hs, hl, hd⟩ |
    ⟨hx, hy, htr⟩ | ⟨hx, hy, htr⟩
  · exact .inl ⟨rfl, by rcases r with ⟨_, _ | _⟩ <;> exact h⟩
  · exact .inr (.inl ⟨hy, hx, (rootEdge_converse b r x.start y.start).mpr h⟩)
  · exact .inr (.inr (.inr (.inl ⟨c, hs, hl, by simpa only [converse_converse] using hd⟩)))
  · exact .inr (.inr (.inl ⟨c, hs, hl, hd⟩))
  · exact .inr (.inr (.inr (.inr (.inr ⟨hy, hx, by simpa only [converse_converse] using htr⟩))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨hy, hx, htr⟩))))

theorem base_loop_iff (r : OrientedRole) (x : b.Path) :
    b.Base r x x ↔ b.Edge r x.tailNode x.tailNode := by
  rw [edge_loop_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨c, _, hl, _⟩ | ⟨c, _, hl, _⟩ | ⟨hx, hx', _⟩ | ⟨hx, hx', _⟩)
    · exact h
    · exfalso
      rcases r with ⟨rn, _ | _⟩
      · exact (b.rootEdges_valid _ h).2.2 rfl
      · exact (b.rootEdges_valid _ h).2.2 rfl
    · have hlen := congrArg List.length hl; simp at hlen
    · have hlen := congrArg List.length hl; simp at hlen
    · exact (hx hx').elim
    · exact (hx' hx).elim
  · exact fun h => .inl ⟨rfl, h⟩

private theorem base_edge_and_match (hw : b.BlockingValid) {r : OrientedRole} {x y : b.Path}
    (he : b.Base r x y) :
    ∃ n, b.Edge r x.tailNode n ∧
      (∀ c, c ∈ b.labels n ↔ c ∈ b.labels y.tailNode) ∧
      (∀ g, g ∈ b.guardLabels n ↔ g ∈ b.guardLabels y.tailNode) := by
  rcases he with ⟨heq, h⟩ | ⟨hx, hy, h⟩ | ⟨c, hs, hl, hd⟩ | ⟨c, hs, hl, hd⟩ |
    ⟨_, hy, htr⟩ | ⟨hx, _, htr⟩
  · cases heq
    exact ⟨x.tailNode, (edge_loop_iff b r _).mpr h, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
    have hyt : y.tailNode = y.start := by simp [Path.tailNode, hy, walkTail]
    refine ⟨y.tailNode, ?_, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    rw [hxt, hyt]
    exact .inr (.inl ⟨x.start_isRoot, y.start_isRoot, h⟩)
  · have hc : b.Child x.tailNode c := by
      have hv := (Path.valid_cons (hl ▸ y.valid)).2
      simpa only [Path.tailNode, hs] using hv
    have hyt : y.tailNode = b.target c := by simp [Path.tailNode, hl, walkTail]
    rw [hyt]
    exact ⟨c, (edge_child_iff hc).mpr hd, (target_match hw).labels, (target_match hw).guards⟩
  · have hc : b.Child y.tailNode c := by
      have hv := (Path.valid_cons (hl ▸ x.valid)).2
      simpa only [Path.tailNode, hs] using hv
    have hxt : x.tailNode = b.target c := by simp [Path.tailNode, hl, walkTail]
    have htch : b.Child (b.parent (b.target c)) (b.target c) :=
      ⟨target_not_root hw hc.1, rfl⟩
    have hdown : b.Down (converse r) (b.target c) := ((target_match hw).roles (converse r)).mp hd
    have hedge : b.Edge r x.tailNode (b.parent x.tailNode) := by
      rw [hxt]
      exact .inr (.inr (.inr (.inl ⟨htch, hdown⟩)))
    refine ⟨b.parent x.tailNode, hedge, ?_, ?_⟩
    · intro d
      rw [hxt, ← hc.2]
      exact ((target_match hw).parentLabels d).symm
    · intro g
      rw [hxt, ← hc.2]
      exact ((target_match hw).parentGuards g).symm
  · have hyt : y.tailNode = y.start := by simp [Path.tailNode, hy, walkTail]
    refine ⟨y.tailNode, ?_, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    rw [hyt]
    exact .inr (.inr (.inr (.inr (.inl htr))))
  · have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
    refine ⟨y.tailNode, ?_, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    rw [hxt]
    exact .inr (.inr (.inr (.inr (.inr htr))))

theorem base_guard_step {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {r : OrientedRole} {x y : b.Path} (he : b.Base r x y)
    {g k : Guard} (hg : g ∈ b.guardLabels x.tailNode) (hk : k ∈ g.advance r) :
    k ∈ b.guardLabels y.tailNode := by
  obtain ⟨n, hedge, _, hguards⟩ := base_edge_and_match hs.blocking he
  exact (hguards k).mp (hs.guardStep x.tailNode n r hedge g hg k hk)

/-! ### Unraveled OWL 2 Direct Semantics interpretation -/

def baseInterpretation (b : BlockedForest) : Sabrina.ALC.Interpretation where
  Domain := b.Path
  nonempty := ⟨Path.root0 b⟩
  atom a x := .lit a true ∈ b.labels x.tailNode
  role r x y := b.Base (r, false) x y

theorem base_holdsRole_iff (r : OrientedRole) (x y : b.Path) :
    holdsRole b.baseInterpretation r x y ↔ b.Base r x y := by
  rcases r with ⟨r, _ | _⟩
  · rfl
  · exact ⟨fun h => base_flip (r := (r, false)) h, fun h => base_flip (r := (r, true)) h⟩

theorem base_modelsRoles {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p) :
    Sabrina.ALC.modelsRoles b.baseInterpretation p.rules := by
  intro r s hrs x y hxy
  have hb : b.Base r x y := (base_holdsRole_iff r x y).mp hxy
  apply (base_holdsRole_iff s x y).mpr
  rcases hb with ⟨rfl, h⟩ | ⟨hx, hy, h⟩ | ⟨c, hst, hl, hd⟩ | ⟨c, hst, hl, hd⟩ |
    ⟨hx, hy, htr⟩ | ⟨hx, hy, htr⟩
  · exact .inl ⟨rfl, (edge_loop_iff b s _).mp (hs.rules (r, s) hrs _ _ ((edge_loop_iff b r _).mpr h))⟩
  · have hne : x.start ≠ y.start := by
      rcases r with ⟨rn, _ | _⟩
      · exact (b.rootEdges_valid _ h).2.2
      · exact Ne.symm (b.rootEdges_valid _ h).2.2
    have hre := (edge_root_iff x.start_isRoot y.start_isRoot hne).mp
      (hs.rules (r, s) hrs _ _ ((edge_root_iff x.start_isRoot y.start_isRoot hne).mpr h))
    exact .inr (.inl ⟨hx, hy, hre⟩)
  · have hc : b.Child x.tailNode c := by
      have hv := (Path.valid_cons (hl ▸ y.valid)).2
      simpa only [Path.tailNode, hst] using hv
    have hd' := (edge_child_iff hc).mp (hs.rules (r, s) hrs _ _ ((edge_child_iff hc).mpr hd))
    exact .inr (.inr (.inl ⟨c, hst, hl, hd'⟩))
  · have hc : b.Child y.tailNode c := by
      have hv := (Path.valid_cons (hl ▸ x.valid)).2
      simpa only [Path.tailNode, hst] using hv
    have h1 : b.Edge r c y.tailNode := (b.edge_converse r c y.tailNode).mp ((edge_child_iff hc).mpr hd)
    have h2 : b.Edge s c y.tailNode := hs.rules (r, s) hrs _ _ h1
    have h3 : b.Edge (converse s) y.tailNode c := (b.edge_converse s c y.tailNode).mpr h2
    exact .inr (.inr (.inr (.inl ⟨c, hst, hl, (edge_child_iff hc).mp h3⟩)))
  · have ⟨h1, h2, h3⟩ := b.toRoot_valid x.tailNode _ htr
    have htr' := (edge_toRoot_iff h1 h2 h3).mp
      (hs.rules (r, s) hrs _ _ ((edge_toRoot_iff h1 h2 h3).mpr htr))
    exact .inr (.inr (.inr (.inr (.inl ⟨hx, hy, htr'⟩))))
  · have ⟨h1, h2, h3⟩ := b.toRoot_valid y.tailNode _ htr
    have hre : b.Edge r x.start y.tailNode :=
      (b.edge_converse r x.start y.tailNode).mp ((edge_toRoot_iff h1 h2 h3).mpr htr)
    have hse : b.Edge s x.start y.tailNode := hs.rules (r, s) hrs _ _ hre
    have hse' : b.Edge (converse s) y.tailNode x.start := (b.edge_converse s x.start y.tailNode).mpr hse
    exact .inr (.inr (.inr (.inr (.inr ⟨hx, hy, (edge_toRoot_iff h1 h2 h3).mp hse'⟩))))

private noncomputable def fallbackNamedPath (b : BlockedForest) : b.Path :=
  match h : b.noms with
  | [] => Path.root0 b
  | (_, r) :: _ => Path.root b r (b.noms_valid _ (h ▸ List.mem_cons_self ..))

private noncomputable def evalIndividual (b : BlockedForest) (ind : Individual) : b.Path := by
  classical
  exact if h : ∃ r, b.BoundTo ind r then
    Path.root b (Classical.choose h) (Classical.choose_spec h).isRoot
  else
    fallbackNamedPath b

private theorem evalIndividual_eq_of_bound {b : BlockedForest} {p : Problem}
    (hb : b.BindingsValid p) {ind : Individual} {r : b.Node} (h : b.BoundTo ind r) :
    evalIndividual b ind = Path.root b r h.isRoot := by
  classical
  unfold evalIndividual
  rw [dite_eq_left ⟨r, h⟩]
  have heq : Classical.choose (⟨r, h⟩ : ∃ x, b.BoundTo ind x) = r :=
    hb.ind_unique (Classical.choose_spec (⟨r, h⟩ : ∃ x, b.BoundTo ind x)) h
  exact Path.ext heq rfl

private def namedPath (b : BlockedForest) (x : b.Path) : Prop :=
  if b.noms.isEmpty then x = Path.root0 b
  else x.steps = [] ∧ b.isNamedRoot x.start = true

private theorem namedPath_individual (b : BlockedForest) (a : IRI) :
    namedPath b (evalIndividual b (.named a)) := by
  classical
  by_cases hex : ∃ r, b.BoundTo (.named a) r
  · have heval : evalIndividual b (.named a) =
        Path.root b (Classical.choose hex) (Classical.choose_spec hex).isRoot := by
      unfold evalIndividual; rw [dite_eq_left hex]
    rw [heval]
    have hspec : (a, Classical.choose hex) ∈ b.noms := Classical.choose_spec hex
    unfold namedPath
    cases hn : b.noms with
    | nil => rw [hn] at hspec; cases hspec
    | cons hd tl =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Path.root, true_and]
      unfold isNamedRoot
      exact List.any_eq_true.mpr ⟨(a, Classical.choose hex), hspec, beq_self_eq_true _⟩
  · have heval : evalIndividual b (.named a) = fallbackNamedPath b := by
      unfold evalIndividual; rw [dite_eq_right hex]
    rw [heval]
    unfold namedPath
    cases hn : b.noms with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte]
      unfold fallbackNamedPath
      split
      · rfl
      · rename_i heq; rw [hn] at heq; cases heq
    | cons hd tl =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      have hfb : fallbackNamedPath b = Path.root b hd.2 (b.noms_valid hd (hn ▸ List.mem_cons_self ..)) := by
        unfold fallbackNamedPath
        split
        · rename_i heq; rw [hn] at heq; cases heq
        · rename_i a₀ r₀ tl' heq
          rw [hn] at heq
          cases heq
          rfl
      rw [hfb]
      refine ⟨rfl, ?_⟩
      unfold isNamedRoot
      exact List.any_eq_true.mpr ⟨hd, hn ▸ List.mem_cons_self .., beq_self_eq_true _⟩

def pathSubjLabels (b : BlockedForest) (x : b.Path) : List (Nat × List Concept) :=
  if x.steps.isEmpty then b.rootSubjects else [(x.tailNode.val, b.labels x.tailNode)]

def pathKeyDisjoint (b : BlockedForest) (x : b.Path) : List (Nat × Nat × IRI) :=
  if x.steps.isEmpty then b.keyDisjoint.map (fun (r₁, r₂, dp) => (r₁.val, r₂.val, dp)) else []

def pathCSP (b : BlockedForest) (p : Problem) (x : b.Path) : DataCSP :=
  mkSubjectsDataCSP p (b.pathSubjLabels x) (b.pathKeyDisjoint x)

def pathSol (b : BlockedForest) (p : Problem) (x : b.Path) : List DataEdge :=
  (solveDataCSP (b.pathCSP p x)).getD []

theorem pathSubjLabels_mem (b : BlockedForest) (x : b.Path) :
    (x.tailNode.val, b.labels x.tailNode) ∈ b.pathSubjLabels x := by
  unfold pathSubjLabels
  cases hx : x.steps with
  | nil =>
    simp only [List.isEmpty_nil, ↓reduceIte, Path.tailNode, hx, walkTail]
    exact mem_rootSubjects_of_isRoot x.start_isRoot
  | cons _ _ =>
    simp [List.isEmpty_cons]

theorem pathCSP_eq_rootDataCSP (b : BlockedForest) (p : Problem) {x : b.Path}
    (hx : x.steps = []) : b.pathCSP p x = b.rootDataCSP p := by
  simp [pathCSP, pathSubjLabels, pathKeyDisjoint, hx, rootDataCSP]

theorem pathSol_eq_rootSol (b : BlockedForest) (p : Problem) {x y : b.Path}
    (hx : x.steps = []) (hy : y.steps = []) : b.pathSol p x = b.pathSol p y := by
  simp [pathSol, pathCSP_eq_rootDataCSP b p hx, pathCSP_eq_rootDataCSP b p hy]

theorem pathCSP_solve {p : Problem} (cf : b.BlockedClashFree p) (hw : b.BlockingValid)
    (x : b.Path) :
    solveDataCSP (mkSubjectsDataCSP p (b.pathSubjLabels x) (b.pathKeyDisjoint x)) =
      some (b.pathSol p x) := by
  change solveDataCSP (b.pathCSP p x) = some (b.pathSol p x)
  have his : (solveDataCSP (b.pathCSP p x)).isSome = true := by
    cases hx : x.steps with
    | nil =>
      rw [pathCSP_eq_rootDataCSP b p hx]
      exact cf.rootData
    | cons c rest =>
      have hnr : b.isRoot x.tailNode = false := by
        cases hr : b.isRoot x.tailNode with
        | false => rfl
        | true =>
          have hnil := (Path.steps_nil_iff_tail_root hw x).mpr hr
          rw [hx] at hnil; cases hnil
      simpa [pathCSP, pathSubjLabels, pathKeyDisjoint, hx, nodeDataCSP] using
        cf.nodeData x.tailNode (x.tail_unblocked hw) hnr
  unfold pathSol
  cases h : solveDataCSP (b.pathCSP p x) with
  | none => rw [h] at his; cases his
  | some s => rfl

noncomputable abbrev toUnraveledInterpretation (b : BlockedForest) (p : Problem) :
    Interpretation datatypeMap where
  Object := b.Path
  objectNonempty := ⟨Path.root0 b⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes a x :=
    if a = thing then True
    else if a = nothing then False
    else .lit a true ∈ b.labels x.tailNode
  objectProperties r x y :=
    if r = topObjectProperty then True
    else if r = bottomObjectProperty then False
    else (complete b.baseInterpretation p.rules p.chains).role r x y
  dataProperties r x y :=
    if r = topDataProperty then True
    else if r = bottomDataProperty then False
    else ∃ v : Value, y = some v ∧ (r, x.tailNode.val, v) ∈ b.pathSol p x
  individuals := evalIndividual b
  datatypes t y := t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = y
  literalValue := decodeLiteral
  lexicalAgreement := fun _ _ h => h
  named := namedPath b
  namedIndividual := namedPath_individual b
  thingExt := by simp
  nothingExt := by
    have h : nothing ≠ thing := by decide
    intro x; simp [h]
  topObjectExt := by simp
  bottomObjectExt := by
    have h : bottomObjectProperty ≠ topObjectProperty := by decide
    intro x y; simp [h]
  topDataExt := by simp
  bottomDataExt := by
    have h : bottomDataProperty ≠ topDataProperty := by decide
    intro x y; simp [h]
  literalDatatypeExt := by simp
  datatypeAgreement := by
    intro t ht y
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp [hn]
    exact Iff.rfl

private theorem coreObj_ne {r : IRI} (hr : isCoreObjPropIRI r = true) :
    r ≠ topObjectProperty ∧ r ≠ bottomObjectProperty := by
  simp only [isCoreObjPropIRI, Bool.and_eq_true, bne_iff_ne] at hr; exact hr

private theorem coreClass_ne {a : IRI} (ha : isCoreClassIRI a = true) :
    a ≠ thing ∧ a ≠ nothing := by
  simp only [isCoreClassIRI, Bool.and_eq_true, bne_iff_ne] at ha; exact ha

private theorem coreData_ne {dp : IRI} (h : isCoreDataPropIRI dp = true) :
    dp ≠ topDataProperty ∧ dp ≠ bottomDataProperty := by
  simp only [isCoreDataPropIRI, Bool.and_eq_true, bne_iff_ne] at h; exact h

theorem unraveled_data_iff (p : Problem) {dp : IRI} (hdp : isCoreDataPropIRI dp = true)
    (x : b.Path) (y : (b.toUnraveledInterpretation p).Data) :
    (b.toUnraveledInterpretation p).dataProperties dp x y ↔
      solEdge (b.pathSol p x) (b.toUnraveledInterpretation p) dp x.tailNode.val y := by
  have ⟨h1, h2⟩ := coreData_ne hdp
  simp only [toUnraveledInterpretation, solEdge, h1, h2, ↓reduceIte]
  exact Iff.rfl

theorem unraveled_role_iff (p : Problem) (r : OrientedRole)
    (hr : isCoreObjPropIRI r.1 = true) (x y : b.Path) :
    holdsOriented (b.toUnraveledInterpretation p) r x y ↔
      holdsRole (complete b.baseInterpretation p.rules p.chains) r x y := by
  have ⟨h1, h2⟩ := coreObj_ne hr
  rcases r with ⟨r, _ | _⟩ <;> simp [holdsOriented, holdsRole, h1, h2]

theorem base_implies_unraveled {p : Problem} {r : OrientedRole}
    (hr : isCoreObjPropIRI r.1 = true) {x y : b.Path} (he : b.Base r x y) :
    holdsOriented (b.toUnraveledInterpretation p) r x y := by
  apply (unraveled_role_iff p r hr x y).mpr
  apply (Sabrina.RoleChains.RankedPaths.holdsRole_complete _ _ _ _ _ _).mpr
  refine ⟨[r], (Sabrina.RoleChains.RankedPaths.generated_closed _ _).letter r, ?_⟩
  exact ⟨y, (base_holdsRole_iff r x y).mpr he, rfl⟩

private theorem simple_role_localizes {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole}
    (hr : isCoreObjPropIRI r.1 = true) (hsim : Simple p.rules p.chains r) (x y : b.Path) :
    holdsOriented (b.toUnraveledInterpretation p) r x y ↔ b.Base r x y := by
  constructor
  · intro h
    obtain ⟨word, hw, hpath⟩ := (Sabrina.RoleChains.RankedPaths.holdsRole_complete
      _ _ _ _ _ _).mp ((unraveled_role_iff p r hr x y).mp h)
    obtain ⟨s, rfl, below⟩ := Sabrina.RoleChains.SimpleRoles.generated_simple
      (Sabrina.RoleChains.checkRegular_sound hi.regular) hw hsim
    obtain ⟨z, hxz, hzy⟩ := hpath
    change z = y at hzy
    subst z
    apply (base_holdsRole_iff r x y).mp
    rcases below with he | hbelow
    · exact he ▸ hxz
    · exact Sabrina.ALC.modelsClosure (base_modelsRoles hs) s r hbelow x y hxz
  · exact base_implies_unraveled hr

private theorem universal_label {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} {c : Concept}
    (hr : isCoreObjPropIRI r.1 = true) {x y : b.Path}
    (hl : .all r c ∈ b.labels x.tailNode)
    (he : holdsOriented (b.toUnraveledInterpretation p) r x y) :
    c ∈ b.labels y.tailNode := by
  obtain ⟨w, hgw, hwp⟩ := (Sabrina.RoleChains.RankedPaths.holdsRole_complete
    _ _ _ _ _ _).mp ((unraveled_role_iff p r hr x y).mp he)
  have hg0 : (⟨roleLanguage rank p r, c⟩ : Guard) ∈ b.guardLabels x.tailNode :=
    hs.guardStart x.tailNode (x.tail_unblocked hs.blocking) r c hl
  have hacc : (roleLanguage rank p r).Matches w :=
    ((roleLanguage rank p r).accepts_iff w).mp ((roleLanguage_accepts hi.regular r w).mpr hgw)
  have walkGuard : ∀ (w : List OrientedRole) (u v : b.Path) (g : Guard),
      g ∈ b.guardLabels u.tailNode → g.state.Matches w →
      WordPath b.baseInterpretation w u v → g.filler ∈ b.labels v.tailNode := by
    intro w
    induction w with
    | nil =>
      intro u v g hg hm hwp
      change u = v at hwp
      subst hwp
      exact hs.guardAccept u.tailNode g hg (g.state.nullable_iff.mpr hm)
    | cons step rest ih =>
      intro u v g hg hm hwp
      obtain ⟨z, hstep, hrest⟩ := hwp
      obtain ⟨nextState, hderiv, hmatch⟩ := (PathRegex.matches_derivative g.state step rest).mp hm
      let nextG : Guard := ⟨nextState, g.filler⟩
      have hmem : nextG ∈ g.advance step := List.mem_map.mpr ⟨nextState, hderiv, rfl⟩
      have hg' : nextG ∈ b.guardLabels z.tailNode :=
        base_guard_step hs ((base_holdsRole_iff step u z).mp hstep) hg hmem
      exact ih z v nextG hg' hmatch hrest
  exact walkGuard w x y ⟨roleLanguage rank p r, c⟩ hg0 hacc hwp

/-! ### Lifting lower bounds and reflecting upper bounds -/

private theorem lift_from_root {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {x : b.Path} (hx : x.steps = []) {r : OrientedRole} {y : b.Node}
    (huy : b.Unblocked y) (he : b.Edge r x.start y) :
    b.Base r x (Path.canonical b hs.blocking y huy).val := by
  have hxr : b.isRoot x.start = true := x.start_isRoot
  have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
  have hux : b.Unblocked x.start := root_unblocked hs.blocking hxr
  rcases he with ⟨rfl, hloop⟩ | ⟨_, hyr, hre⟩ | ⟨hch, hd⟩ | ⟨hch, _⟩ | htr | htr
  · have hcan := Path.canonical_root hs.blocking huy hxr
    have heq : (Path.canonical b hs.blocking x.start huy).val = x :=
      hcan.trans (Path.ext rfl hx.symm)
    rw [heq]
    exact .inl ⟨rfl, by simpa [hxt] using hloop⟩
  · rw [Path.canonical_root hs.blocking huy hyr]
    exact .inr (.inl ⟨hx, rfl, hre⟩)
  · obtain ⟨hch', hcan⟩ := Path.canonical_child hs.blocking hux huy hch
    have hpx : (Path.canonical b hs.blocking x.start hux).val = x :=
      (Path.canonical_root hs.blocking hux hxr).trans (Path.ext rfl hx.symm)
    rw [hcan]
    refine .inr (.inr (.inl ⟨y, ?_, ?_, hd⟩))
    · simp [Path.extend, hpx]
    · simp [Path.extend, hpx]
  · rw [hch.1] at hxr; cases hxr
  · have hnr := (b.toRoot_valid x.start _ htr).1; rw [hnr] at hxr; cases hxr
  · have hnr := (b.toRoot_valid y _ htr).1
    have hsteps : (Path.canonical b hs.blocking y huy).val.steps ≠ [] := by
      intro hnil
      have hr := (Path.steps_nil_iff_tail_root hs.blocking _).mp hnil
      rw [Path.canonical_tailNode] at hr
      rw [hnr] at hr; cases hr
    refine .inr (.inr (.inr (.inr (.inr ⟨hx, hsteps, ?_⟩))))
    rwa [Path.canonical_tailNode]

private theorem lift_blockable_neighbor (hw : b.BlockingValid) {x : b.Path}
    {c₀ : b.Node} {rest : List b.Node} (hx : x.steps = c₀ :: rest)
    {r : OrientedRole} {y : b.Node} (he : b.Edge r x.tailNode y) :
    ∃ z : b.Path, b.Base r x z ∧ (∀ d, d ∈ b.labels y ↔ d ∈ b.labels z.tailNode) ∧
      ((z = x ∧ y = x.tailNode) ∨
       (z.steps = y :: x.steps ∧ b.Child x.tailNode y) ∨
       (z.start = x.start ∧ z.steps = rest ∧ y = b.parent x.tailNode) ∨
       (z.steps = [] ∧ z.start = y ∧ b.isRoot y = true ∧ b.parent x.tailNode ≠ y)) := by
  have hc₀ := (Path.valid_cons (hx ▸ x.valid)).2
  have hxt : x.tailNode = b.target c₀ := by simp [Path.tailNode, hx, walkTail]
  have hnr : b.isRoot x.tailNode = false := hxt ▸ target_not_root hw hc₀.1
  rcases he with ⟨rfl, hloop⟩ | ⟨hxr, _, _⟩ | ⟨hch, hd⟩ | ⟨hch, hd⟩ | htr | htr
  · exact ⟨x, .inl ⟨rfl, hloop⟩, fun _ => Iff.rfl, .inl ⟨rfl, rfl⟩⟩
  · rw [hnr] at hxr; cases hxr
  · refine ⟨x.extend y hch, .inr (.inr (.inl ⟨y, rfl, rfl, hd⟩)), ?_, .inr (.inl ⟨rfl, hch⟩)⟩
    intro d
    change d ∈ b.labels y ↔ d ∈ b.labels (b.target y)
    exact (target_match hw).labels d
  · let z : b.Path := ⟨x.start, rest, (Path.valid_cons (hx ▸ x.valid)).1⟩
    have hdown : b.Down (converse r) c₀ := by
      have h1 : b.Down (converse r) (b.target c₀) := hxt ▸ hd
      exact ((target_match hw).roles (converse r)).mpr h1
    refine ⟨z, .inr (.inr (.inr (.inl ⟨c₀, rfl, hx, hdown⟩))), ?_, .inr (.inr (.inl ⟨rfl, rfl, hch.2.symm⟩))⟩
    intro d
    have hpar : b.parent c₀ = z.tailNode := hc₀.2
    rw [← hch.2, hxt, ← hpar]
    exact ((target_match hw).parentLabels d).symm
  · have ⟨_, hyr, hnp⟩ := b.toRoot_valid x.tailNode _ htr
    refine ⟨Path.root b y hyr, .inr (.inr (.inr (.inr (.inl ⟨by simp [hx], rfl, htr⟩)))),
      fun _ => Iff.rfl, .inr (.inr (.inr ⟨rfl, rfl, hyr, hnp⟩))⟩
  · have h1 := (b.toRoot_valid y _ htr).2.1
    rw [hnr] at h1; cases h1

private theorem minimum_holds {rank : Rank} {p : Problem}
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} {c : Concept}
    (hr : isCoreObjPropIRI r.1 = true)
    (hc : ∀ x : b.Path, c ∈ b.labels x.tailNode → holds (b.toUnraveledInterpretation p) x c)
    {n : Nat} {x : b.Path} (hl : .min n r c ∈ b.labels x.tailNode) :
    AtLeast n (fun y => holdsOriented (b.toUnraveledInterpretation p) r x y ∧
      holds (b.toUnraveledInterpretation p) y c) := by
  obtain ⟨ys, hlen, hnd, hspec⟩ := hs.min x.tailNode (x.tail_unblocked hs.blocking) n r c hl
  cases hx : x.steps with
  | nil =>
    have hxr : b.isRoot x.tailNode = true := (Path.steps_nil_iff_tail_root hs.blocking x).mp hx
    have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
    have hsub : ∀ y ∈ ys, ∃ z : b.Path, z.tailNode = y ∧ b.Base r x z ∧ c ∈ b.labels z.tailNode := by
      intro y hy
      obtain ⟨hunb, hedge, hlab⟩ := hspec y hy
      have huy := hunb hxr
      refine ⟨(Path.canonical b hs.blocking y huy).val, Path.canonical_tailNode hs.blocking y huy,
        lift_from_root hs hx huy (hxt ▸ hedge), ?_⟩
      rwa [Path.canonical_tailNode]
    classical
    let lift (y : b.Node) : b.Path :=
      if h : y ∈ ys then Classical.choose (hsub y h) else Path.root0 b
    have hlift_spec (y : b.Node) (hy : y ∈ ys) :
        (lift y).tailNode = y ∧ b.Base r x (lift y) ∧ c ∈ b.labels (lift y).tailNode := by
      simp only [lift, hy, ↓reduceDIte]
      exact Classical.choose_spec (hsub y hy)
    refine ⟨ys.map lift, by simp [hlen], ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact hnd.imp_of_mem fun ha hb hne heq => hne <|
        (hlift_spec _ ha).1.symm.trans ((congrArg Path.tailNode heq).trans (hlift_spec _ hb).1)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have ⟨_, hbase, hlab⟩ := hlift_spec y hy
      exact ⟨base_implies_unraveled hr hbase, hc _ hlab⟩
  | cons c₀ rest =>
    have hsub : ∀ y ∈ ys, ∃ z : b.Path, b.Base r x z ∧ c ∈ b.labels z.tailNode ∧
        ((z = x ∧ y = x.tailNode) ∨
         (z.steps = y :: x.steps ∧ b.Child x.tailNode y) ∨
         (z.start = x.start ∧ z.steps = rest ∧ y = b.parent x.tailNode) ∨
         (z.steps = [] ∧ z.start = y ∧ b.isRoot y = true ∧ b.parent x.tailNode ≠ y)) := by
      intro y hy
      obtain ⟨_, hedge, hlab⟩ := hspec y hy
      obtain ⟨z, hbase, hml, hshape⟩ := lift_blockable_neighbor hs.blocking hx hedge
      exact ⟨z, hbase, (hml c).mp hlab, hshape⟩
    classical
    let lift (y : b.Node) : b.Path :=
      if h : y ∈ ys then Classical.choose (hsub y h) else Path.root0 b
    have hlift (y : b.Node) (hy : y ∈ ys) :
        b.Base r x (lift y) ∧ c ∈ b.labels (lift y).tailNode ∧
        ((lift y = x ∧ y = x.tailNode) ∨
         ((lift y).steps = y :: x.steps ∧ b.Child x.tailNode y) ∨
         ((lift y).start = x.start ∧ (lift y).steps = rest ∧ y = b.parent x.tailNode) ∨
         ((lift y).steps = [] ∧ (lift y).start = y ∧ b.isRoot y = true ∧ b.parent x.tailNode ≠ y)) := by
      simp only [lift, hy, ↓reduceDIte]
      exact Classical.choose_spec (hsub y hy)
    refine ⟨ys.map lift, by simp [hlen], ?_, ?_⟩
    · apply List.pairwise_map.mpr
      refine hnd.imp_of_mem fun ha hb hne heq => ?_
      have h1 := (hlift _ ha).2.2
      have h2 := (hlift _ hb).2.2
      rw [heq] at h1
      rcases h1 with ⟨hz1, hy1⟩ | ⟨hs1, _⟩ | ⟨hst1, hs1, hy1⟩ | ⟨hs1, hst1, _, hnp1⟩ <;>
        rcases h2 with ⟨hz2, hy2⟩ | ⟨hs2, _⟩ | ⟨hst2, hs2, hy2⟩ | ⟨hs2, hst2, _, hnp2⟩
      all_goals first
        | exact hne (hy1.trans hy2.symm)
        | exact hne (List.cons.inj (hs1.symm.trans hs2)).1
        | exact hne (hst1.symm.trans hst2)
        | (have hlen := congrArg List.length (hs1.symm.trans hs2); simp [hx] at hlen; (try omega); done)
        | (have hlen := congrArg List.length ((congrArg Path.steps hz1).symm.trans hs2); simp [hx] at hlen; (try omega); done)
        | (have hlen := congrArg List.length (hs1.symm.trans (congrArg Path.steps hz2)); simp [hx] at hlen; (try omega); done)
        | (have hnil : rest = [] := hs1.symm.trans hs2
           have hc₀ := (Path.valid_cons (hx ▸ x.valid)).2
           have hxt : x.tailNode = b.target c₀ := by simp [Path.tailNode, hx, walkTail]
           have hpar_c₀ : b.parent c₀ = x.start := by
             have := hc₀.2; simpa [walkTail, hnil] using this
           have hpar_eq : b.parent x.tailNode = x.start := by
             cases hblk : b.blockedBy c₀ with
             | none => rw [hxt, target, hblk, Option.getD_none, hpar_c₀]
             | some anc =>
               exfalso
               have ⟨hanc, hnr, _⟩ := hs.blocking.blocker c₀ anc hblk
               have hpar_root : b.isRoot (b.parent c₀) = true := hpar_c₀ ▸ x.start_isRoot
               have hch' : b.Child (b.parent c₀) c₀ := ⟨hc₀.1, rfl⟩
               rcases (Anc.child_iff hch').mp hanc with rfl | hanc'
               · rw [hnr] at hpar_root; cases hpar_root
               · have hf := hanc'.not_root_right; rw [hpar_root] at hf; cases hf
           exact hnp2 (hpar_eq.trans (hst1.symm.trans hst2)))
        | (have hnil : rest = [] := hs2.symm.trans hs1
           have hc₀ := (Path.valid_cons (hx ▸ x.valid)).2
           have hxt : x.tailNode = b.target c₀ := by simp [Path.tailNode, hx, walkTail]
           have hpar_c₀ : b.parent c₀ = x.start := by
             have := hc₀.2; simpa [walkTail, hnil] using this
           have hpar_eq : b.parent x.tailNode = x.start := by
             cases hblk : b.blockedBy c₀ with
             | none => rw [hxt, target, hblk, Option.getD_none, hpar_c₀]
             | some anc =>
               exfalso
               have ⟨hanc, hnr, _⟩ := hs.blocking.blocker c₀ anc hblk
               have hpar_root : b.isRoot (b.parent c₀) = true := hpar_c₀ ▸ x.start_isRoot
               have hch' : b.Child (b.parent c₀) c₀ := ⟨hc₀.1, rfl⟩
               rcases (Anc.child_iff hch').mp hanc with rfl | hanc'
               · rw [hnr] at hpar_root; cases hpar_root
               · have hf := hanc'.not_root_right; rw [hpar_root] at hf; cases hf
           exact hnp1 (hpar_eq.trans (hst2.symm.trans hst1)))
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have ⟨hbase, hlab, _⟩ := hlift y hy
      exact ⟨base_implies_unraveled hr hbase, hc _ hlab⟩

private theorem maximum_holds {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} {c : Concept}
    (hr : isCoreObjPropIRI r.1 = true) (hsim : Simple p.rules p.chains r)
    (hdual : ∀ x : b.Path, c.dual ∈ b.labels x.tailNode → ¬ holds (b.toUnraveledInterpretation p) x c)
    {n : Nat} {x : b.Path} (hl : .max n r c ∈ b.labels x.tailNode) :
    ¬ AtLeast (n + 1) (fun y => holdsOriented (b.toUnraveledInterpretation p) r x y ∧
      holds (b.toUnraveledInterpretation p) y c) := by
  rintro ⟨ys, hlen, hnd, hspec⟩
  have hbase_mem : ∀ y ∈ ys, b.Base r x y ∧ c ∈ b.labels y.tailNode := by
    intro y hy
    obtain ⟨he, hcy⟩ := hspec y hy
    have hbase := (simple_role_localizes hi hs hr hsim x y).mp he
    obtain ⟨m, hedge, hml, _⟩ := base_edge_and_match hs.blocking hbase
    have hsplit := hs.maxQual x.tailNode (x.tail_unblocked hs.blocking) n r c hl m hedge
    refine ⟨hbase, ?_⟩
    rcases hsplit with hpos | hneg
    · exact (hml c).mp hpos
    · exact (hdual y ((hml c.dual).mp hneg) hcy).elim
  apply hs.maxBound x.tailNode (x.tail_unblocked hs.blocking) n r c hl
  cases hx : x.steps with
  | nil =>
    have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
    let proj (y : b.Path) : b.Node :=
      match y.steps with
      | [] => y.start
      | d :: _ => d
    have hproj_prop : ∀ y ∈ ys,
        (b.isRoot (proj y) = true ∨ b.Child x.tailNode (proj y)) ∧
        b.Edge r x.tailNode (proj y) ∧ c ∈ b.labels (proj y) ∧
        ((y.steps = [] ∧ proj y = y.start) ∨ (y.steps = [proj y] ∧ y.start = x.start)) := by
      intro y hy
      obtain ⟨hbase, hcy⟩ := hbase_mem y hy
      rcases hbase with ⟨heq, hloop⟩ | ⟨_, hy', hre⟩ | ⟨d, hst, hl', hd⟩ | ⟨_, _, hl', _⟩ |
        ⟨hxn, _, _⟩ | ⟨_, _, htr⟩
      · cases heq
        refine ⟨.inl (by simp [proj, hx, x.start_isRoot]), ?_, ?_, .inl ⟨hx, by simp [proj, hx]⟩⟩
        · simpa [proj, hx, hxt] using (edge_loop_iff b r x.tailNode).mpr hloop
        · simpa [proj, hx, hxt] using hcy
      · refine ⟨.inl (by simp [proj, hy', y.start_isRoot]), ?_, ?_, .inl ⟨hy', by simp [proj, hy']⟩⟩
        · simp only [proj, hy', hxt]
          exact .inr (.inl ⟨x.start_isRoot, y.start_isRoot, hre⟩)
        · simpa [proj, hy', Path.tailNode, walkTail] using hcy
      · have hch : b.Child x.tailNode d := by
          have hv := (Path.valid_cons (hl' ▸ y.valid)).2
          simpa only [Path.tailNode, hst] using hv
        have hyt : y.tailNode = b.target d := by simp [Path.tailNode, hl', walkTail]
        refine ⟨.inr (by simpa [proj, hl'] using hch), ?_, ?_, .inr ⟨by simp [proj, hl', hx], hst⟩⟩
        · simpa [proj, hl'] using (edge_child_iff hch).mpr hd
        · simp only [proj, hl']
          exact ((target_match hs.blocking).labels c).mpr (hyt ▸ hcy)
      · rw [hx] at hl'; cases hl'
      · exact (hxn hx).elim
      · exfalso
        have ⟨hnr, _, hnp⟩ := b.toRoot_valid y.tailNode _ htr
        have hedge : b.Edge r x.start y.tailNode := .inr (.inr (.inr (.inr (.inr htr))))
        exact hs.nnEliminated x.start x.start_isRoot n r c (hxt ▸ hl)
          y.tailNode (y.tail_unblocked hs.blocking) hnr hnp hedge hcy
    refine ⟨ys.map proj, by simp [hlen], ?_, ?_⟩
    · apply List.pairwise_map.mpr
      refine hnd.imp_of_mem fun {pa pb} ha hb hne heq => ?_
      have h1 := (hproj_prop pa ha).2.2.2
      have h2 := (hproj_prop pb hb).2.2.2
      have hr1 := (hproj_prop pa ha).1
      have hr2 := (hproj_prop pb hb).1
      rcases h1 with ⟨hs1, hp1⟩ | ⟨hs1, hst1⟩ <;> rcases h2 with ⟨hs2, hp2⟩ | ⟨hs2, hst2⟩
      · exact hne (Path.ext (hp1.symm.trans (heq.trans hp2)) (hs1.trans hs2.symm))
      · rcases hr1 with h1r | h1c
        · have h2f : b.isRoot (proj pb) = false := (Path.valid_cons (hs2 ▸ pb.valid)).2.1
          rw [heq, h2f] at h1r; cases h1r
        · rw [hp1] at h1c; have := h1c.1; rw [pa.start_isRoot] at this; cases this
      · rcases hr2 with h2r | h2c
        · have h1f : b.isRoot (proj pa) = false := (Path.valid_cons (hs1 ▸ pa.valid)).2.1
          rw [← heq, h1f] at h2r; cases h2r
        · rw [hp2] at h2c; have := h2c.1; rw [pb.start_isRoot] at this; cases this
      · exact hne (Path.ext (hst1.trans hst2.symm) (by rw [hs1, hs2, heq]))
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have ⟨hor, hedge, hlab, _⟩ := hproj_prop y hy
      exact ⟨fun _ => hor, hedge, hlab⟩
  | cons c₀ rest =>
    have hxn : x.steps ≠ [] := by simp [hx]
    have hxf : b.isRoot x.tailNode = false := by
      have hc₀ := (Path.valid_cons (hx ▸ x.valid)).2
      simpa [Path.tailNode, hx, walkTail] using target_not_root hs.blocking hc₀.1
    have hmap : ∀ y ∈ ys, ∃ m : b.Node,
        b.Edge r x.tailNode m ∧ c ∈ b.labels m ∧
        ((y = x ∧ m = x.tailNode) ∨
         (y.start = x.start ∧ y.steps = m :: x.steps ∧ b.Child x.tailNode m) ∨
         (y.start = x.start ∧ y.steps = rest ∧ m = b.parent x.tailNode ∧ b.Child m x.tailNode) ∨
         (y.steps = [] ∧ y.start = m ∧ b.isRoot m = true ∧ b.parent x.tailNode ≠ m)) := by
      intro y hy
      obtain ⟨hbase, hcy⟩ := hbase_mem y hy
      rcases hbase with ⟨heq, hloop⟩ | ⟨hx', _, _⟩ | ⟨d, hst, hl', hd⟩ | ⟨d, hst, hl', hd⟩ |
        ⟨_, hy', htr⟩ | ⟨hx', _, _⟩
      · cases heq
        exact ⟨x.tailNode, (edge_loop_iff b r _).mpr hloop, hcy, .inl ⟨rfl, rfl⟩⟩
      · exact (hxn hx').elim
      · have hch : b.Child x.tailNode d := by
          have hv := (Path.valid_cons (hl' ▸ y.valid)).2
          simpa only [Path.tailNode, hst] using hv
        have hyt : y.tailNode = b.target d := by simp [Path.tailNode, hl', walkTail]
        exact ⟨d, (edge_child_iff hch).mpr hd, ((target_match hs.blocking).labels c).mpr (hyt ▸ hcy),
          .inr (.inl ⟨hst, hl', hch⟩)⟩
      · have hst' : y.start = x.start := hst.symm
        have hsteps : d = c₀ ∧ y.steps = rest := List.cons.inj (hl'.symm.trans hx)
        have hc₀ := (Path.valid_cons (hx ▸ x.valid)).2
        have hxt : x.tailNode = b.target c₀ := by simp [Path.tailNode, hx, walkTail]
        have hch : b.Child (b.parent x.tailNode) x.tailNode := ⟨hxf, rfl⟩
        have hdown : b.Down (converse r) x.tailNode := by
          rw [hxt]
          exact ((target_match hs.blocking).roles (converse r)).mp (hsteps.1 ▸ hd)
        have hlab : c ∈ b.labels (b.parent x.tailNode) := by
          have hpar : b.parent c₀ = y.tailNode := by
            have := hc₀.2
            simpa [Path.tailNode, hst', hsteps.2] using this
          rw [hxt]
          exact ((target_match hs.blocking).parentLabels c).mp (hpar.symm ▸ hcy)
        exact ⟨b.parent x.tailNode, .inr (.inr (.inr (.inl ⟨hch, hdown⟩))), hlab,
          .inr (.inr (.inl ⟨hst', hsteps.2, rfl, hch⟩))⟩
      · have ⟨_, hyr, hnp⟩ := b.toRoot_valid x.tailNode _ htr
        have hyt : y.tailNode = y.start := by simp [Path.tailNode, hy', walkTail]
        exact ⟨y.start, .inr (.inr (.inr (.inr (.inl htr)))), hyt ▸ hcy,
          .inr (.inr (.inr ⟨hy', rfl, hyr, hnp⟩))⟩
      · exact (hxn hx').elim
    classical
    let proj (y : b.Path) : b.Node :=
      if h : y ∈ ys then Classical.choose (hmap y h) else 0
    have hproj (y : b.Path) (hy : y ∈ ys) :
        b.Edge r x.tailNode (proj y) ∧ c ∈ b.labels (proj y) ∧
        ((y = x ∧ proj y = x.tailNode) ∨
         (y.start = x.start ∧ y.steps = proj y :: x.steps ∧ b.Child x.tailNode (proj y)) ∨
         (y.start = x.start ∧ y.steps = rest ∧ proj y = b.parent x.tailNode ∧ b.Child (proj y) x.tailNode) ∨
         (y.steps = [] ∧ y.start = proj y ∧ b.isRoot (proj y) = true ∧ b.parent x.tailNode ≠ proj y)) := by
      simp only [proj, hy, ↓reduceDIte]
      exact Classical.choose_spec (hmap y hy)
    refine ⟨ys.map proj, by simp [hlen], ?_, ?_⟩
    · apply List.pairwise_map.mpr
      refine hnd.imp_of_mem fun ha hb hne heq => ?_
      have h1 := (hproj _ ha).2.2
      have h2 := (hproj _ hb).2.2
      rw [heq] at h1
      rcases h1 with ⟨hy1, hm1⟩ | ⟨hst1, hs1, hc1⟩ | ⟨hst1, hs1, hm1, hc1⟩ | ⟨hs1, hst1, hr1, hnp1⟩ <;>
        rcases h2 with ⟨hy2, hm2⟩ | ⟨hst2, hs2, hc2⟩ | ⟨hst2, hs2, hm2, hc2⟩ | ⟨hs2, hst2, hr2, hnp2⟩
      all_goals first
        | exact hne (hy1.trans hy2.symm)
        | exact hne (Path.ext (hst1.trans hst2.symm) (by rw [hs1, hs2, heq]))
        | exact hne (Path.ext (hst1.trans hst2.symm) (hs1.trans hs2.symm))
        | exact Nat.lt_irrefl _ (hm1 ▸ child_lt hc2)
        | exact Nat.lt_irrefl _ (hm2 ▸ child_lt hc1)
        | exact Nat.lt_asymm (child_lt hc1) (child_lt hc2)
        | exact hnp2 hm1.symm
        | exact hnp1 hm2.symm
        | (rw [hm1, hxf] at hr2; cases hr2)
        | (rw [hm2, hxf] at hr1; cases hr1)
        | (have := hc1.1; rw [hr2] at this; cases this)
        | (have := hc2.1; rw [hr1] at this; cases this)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have ⟨hedge, hlab, _⟩ := hproj y hy
      exact ⟨fun hr' => (by rw [hxf] at hr'; cases hr'), hedge, hlab⟩

/-! ### Dual Truth Lemma and `SROIQ(D)` Model Construction -/

theorem sroiq_unraveled_holds_pair {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    (cf : b.BlockedClashFree p) (hs : b.BlockedSaturated rank p) {c : Concept}
    (hc : c.isSROIQD = true)
    (counted : ∀ r ∈ c.countedRoles, Simple p.rules p.chains r)
    (inds : ∀ ind ∈ c.individuals, ∃ r, b.BoundTo ind r) :
    (∀ x : b.Path, c ∈ b.labels x.tailNode → holds (b.toUnraveledInterpretation p) x c) ∧
    (∀ x : b.Path, c.dual ∈ b.labels x.tailNode → ¬ holds (b.toUnraveledInterpretation p) x c) := by
  have hu (x : b.Path) : b.Unblocked x.tailNode := x.tail_unblocked hs.blocking
  induction c with
  | top =>
    exact ⟨fun _ _ => trivial, fun x hl _ => cf.bottom x.tailNode hl⟩
  | bottom =>
    exact ⟨fun x hl => (cf.bottom x.tailNode hl).elim, fun _ _ h => h⟩
  | lit a sign =>
    have ⟨hn₁, hn₂⟩ := coreClass_ne hc
    cases sign with
    | false =>
      refine ⟨fun x hl hp => ?_, fun x hl hn => ?_⟩
      · exact cf.literal _ a (by simpa [holds, toUnraveledInterpretation, hn₁, hn₂] using hp) hl
      · dsimp [Concept.dual] at hl
        exact hn (by simpa [holds, toUnraveledInterpretation, hn₁, hn₂] using hl)
    | true =>
      refine ⟨fun x hl => ?_, fun x hl hp => ?_⟩
      · simpa [holds, toUnraveledInterpretation, hn₁, hn₂] using hl
      · dsimp [Concept.dual] at hl
        exact cf.literal _ a (by simpa [holds, toUnraveledInterpretation, hn₁, hn₂] using hp) hl
  | nom ind sign =>
    obtain ⟨r, hbound⟩ := inds ind (by simp [Concept.individuals])
    have heval : evalIndividual b ind = Path.root b r hbound.isRoot :=
      evalIndividual_eq_of_bound hs.bindings hbound
    have pos_case (x : b.Path) (hl : .nom ind true ∈ b.labels x.tailNode) :
        x = evalIndividual b ind := by
      have hxt : x.tailNode = r := hs.nomPos x.tailNode (hu x) ind r hl hbound
      have hnil : x.steps = [] :=
        (Path.steps_nil_iff_tail_root hs.blocking x).mpr (hxt.symm ▸ hbound.isRoot)
      have hst : x.start = r := by simpa [Path.tailNode, hnil, walkTail] using hxt
      exact (Path.ext hst hnil).trans heval.symm
    have neg_case (x : b.Path) (hl : .nom ind false ∈ b.labels x.tailNode) :
        x ≠ evalIndividual b ind := by
      intro heq
      rw [heval] at heq
      have hxt : x.tailNode = r := by rw [heq]; rfl
      exact cf.nomNeg x.tailNode ind hl (hxt.symm ▸ hbound)
    cases sign with
    | true =>
      exact ⟨fun x hl => pos_case x hl, fun x hl hp => neg_case x hl hp⟩
    | false =>
      exact ⟨fun x hl => neg_case x hl, fun x hl hn => hn (pos_case x hl)⟩
  | self r sign =>
    have hr : isCoreObjPropIRI r.1 = true := hc
    have hsim := counted r (by simp [Concept.countedRoles])
    have eq (x : b.Path) := (simple_role_localizes hi hs hr hsim x x).trans (base_loop_iff r x)
    cases sign with
    | false => exact ⟨fun x hl he => cf.selfNeg _ r hl ((eq x).mp he),
        fun x hl hn => hn ((eq x).mpr (hs.selfPos _ (hu x) r hl))⟩
    | true => exact ⟨fun x hl => (eq x).mpr (hs.selfPos _ (hu x) r hl),
        fun x hl he => cf.selfNeg _ r hl ((eq x).mp he)⟩
  | conj a c ia ic =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have ⟨pa, na⟩ := ia hc.1 (fun r hr => counted r (List.mem_append_left _ hr))
      (fun ind hi => inds ind (List.mem_append_left _ hi))
    have ⟨pc, nc⟩ := ic hc.2 (fun r hr => counted r (List.mem_append_right _ hr))
      (fun ind hi => inds ind (List.mem_append_right _ hi))
    refine ⟨fun x hl => ?_, fun x hl ⟨ha, hc⟩ => ?_⟩
    · obtain ⟨ha, hc⟩ := hs.conj _ (hu x) a c hl
      exact ⟨pa x ha, pc x hc⟩
    · exact (hs.disj _ (hu x) a.dual c.dual hl).elim (fun h => na x h ha) (fun h => nc x h hc)
  | disj a c ia ic =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have ⟨pa, na⟩ := ia hc.1 (fun r hr => counted r (List.mem_append_left _ hr))
      (fun ind hi => inds ind (List.mem_append_left _ hi))
    have ⟨pc, nc⟩ := ic hc.2 (fun r hr => counted r (List.mem_append_right _ hr))
      (fun ind hi => inds ind (List.mem_append_right _ hi))
    refine ⟨fun x hl => ?_, fun x hl hv => ?_⟩
    · exact (hs.disj _ (hu x) a c hl).imp (pa x) (pc x)
    · obtain ⟨ha, hc⟩ := hs.conj _ (hu x) a.dual c.dual hl
      exact hv.elim (na x ha) (nc x hc)
  | some r c ih =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have ⟨pc, nc⟩ := ih hc.2 counted inds
    refine ⟨fun x hl => ?_, fun x hl ⟨y, he, hy⟩ => ?_⟩
    · obtain ⟨v, hunb, hv, hfill⟩ := hs.some _ (hu x) r c hl
      cases hx : x.steps with
      | nil =>
        have hxr : b.isRoot x.tailNode = true := (Path.steps_nil_iff_tail_root hs.blocking x).mp hx
        have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
        have huv := hunb hxr
        have hbase := lift_from_root hs hx huv (hxt ▸ hv)
        refine ⟨(Path.canonical b hs.blocking v huv).val, base_implies_unraveled hc.1 hbase,
          pc _ ?_⟩
        rwa [Path.canonical_tailNode]
      | cons c₀ rest =>
        obtain ⟨z, hbase, hml, _⟩ := lift_blockable_neighbor hs.blocking hx hv
        exact ⟨z, base_implies_unraveled hc.1 hbase, pc z ((hml c).mp hfill)⟩
    · exact nc y (universal_label hi hs hc.1 hl he) hy
  | all r c ih =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have ⟨pc, nc⟩ := ih hc.2 counted inds
    refine ⟨fun x hl y he => pc y (universal_label hi hs hc.1 hl he), fun x hl ha => ?_⟩
    obtain ⟨v, hunb, hv, hd⟩ := hs.some _ (hu x) r c.dual hl
    cases hx : x.steps with
    | nil =>
      have hxr : b.isRoot x.tailNode = true := (Path.steps_nil_iff_tail_root hs.blocking x).mp hx
      have hxt : x.tailNode = x.start := by simp [Path.tailNode, hx, walkTail]
      have huv := hunb hxr
      have hbase := lift_from_root hs hx huv (hxt ▸ hv)
      exact nc _ (by rwa [Path.canonical_tailNode]) (ha _ (base_implies_unraveled hc.1 hbase))
    | cons c₀ rest =>
      obtain ⟨z, hbase, hml, _⟩ := lift_blockable_neighbor hs.blocking hx hv
      exact nc z ((hml c.dual).mp hd) (ha z (base_implies_unraveled hc.1 hbase))
  | min n r c ih =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have hsim := counted r (List.mem_cons_self ..)
    have ⟨pc, nc⟩ := ih hc.2 (fun s hm => counted s (List.mem_cons_of_mem _ hm)) inds
    refine ⟨fun x hl => minimum_holds hs hc.1 pc hl, fun x hl => ?_⟩
    cases n with
    | zero =>
      exact (cf.bottom _ (hs.conj _ (hu x) .bottom (.min 0 r c) hl).1).elim
    | succ m => exact maximum_holds hi hs hc.1 hsim nc hl
  | max n r c ih =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have hsim := counted r (List.mem_cons_self ..)
    have ⟨pc, nc⟩ := ih hc.2 (fun s hm => counted s (List.mem_cons_of_mem _ hm)) inds
    refine ⟨fun x hl => maximum_holds hi hs hc.1 hsim nc hl, fun x hl hn => ?_⟩
    exact hn (minimum_holds hs hc.1 pc hl)
  | dataSome dp d =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    refine ⟨fun x hl => ?_, fun x hl ⟨y, hy, hd⟩ => ?_⟩
    · obtain ⟨y, hy, hd⟩ := solEdge_holds_dataSome (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
      exact ⟨y, (b.unraveled_data_iff p hc.1 x y).mpr hy, hd⟩
    · have hnot := solEdge_holds_dataAll (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
        y ((b.unraveled_data_iff p hc.1 x y).mp hy)
      exact hnot hd
  | dataAll dp d =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    refine ⟨fun x hl y hy => ?_, fun x hl hall => ?_⟩
    · exact solEdge_holds_dataAll (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
        y ((b.unraveled_data_iff p hc.1 x y).mp hy)
    · obtain ⟨y, hy, hnot⟩ := solEdge_holds_dataSome (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
      exact hnot (hall y ((b.unraveled_data_iff p hc.1 x y).mpr hy))
  | dataValue dp l sign =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    cases sign with
    | true =>
      refine ⟨fun x hl => ?_, fun x hl hp => ?_⟩
      · exact (b.unraveled_data_iff p hc.1 x _).mpr
          (solEdge_holds_dataValue_true (b.pathCSP_solve cf hs.blocking x)
            (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2)
      · exact solEdge_holds_dataValue_false (b.pathCSP_solve cf hs.blocking x)
          (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
          ((b.unraveled_data_iff p hc.1 x _).mp hp)
    | false =>
      refine ⟨fun x hl hp => ?_, fun x hl hn => ?_⟩
      · exact solEdge_holds_dataValue_false (b.pathCSP_solve cf hs.blocking x)
          (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
          ((b.unraveled_data_iff p hc.1 x _).mp hp)
      · exact hn ((b.unraveled_data_iff p hc.1 x _).mpr
          (solEdge_holds_dataValue_true (b.pathCSP_solve cf hs.blocking x)
            (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2))
  | dataMin n dp d =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have hpred (x : b.Path) :
        (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧
          dataHolds (b.toUnraveledInterpretation p) y d) =
        (fun y => solEdge (b.pathSol p x) (b.toUnraveledInterpretation p) dp x.tailNode.val y ∧
          dataHolds (b.toUnraveledInterpretation p) y d) := by
      ext y; exact and_congr_left' (b.unraveled_data_iff p hc.1 x y)
    refine ⟨fun x hl => ?_, fun x hl => ?_⟩
    · change AtLeast n (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧ _)
      rw [hpred x]
      exact solEdge_holds_dataMin (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
    · cases n with
      | zero =>
        exact (cf.bottom _ (hs.conj _ (hu x) .bottom (.dataMin 0 dp d) hl).1).elim
      | succ m =>
        change ¬ AtLeast (m + 1) (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧ _)
        rw [hpred x]
        exact solEdge_holds_dataMax (b.pathCSP_solve cf hs.blocking x)
          (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
  | dataMax n dp d =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    have hpred (x : b.Path) :
        (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧
          dataHolds (b.toUnraveledInterpretation p) y d) =
        (fun y => solEdge (b.pathSol p x) (b.toUnraveledInterpretation p) dp x.tailNode.val y ∧
          dataHolds (b.toUnraveledInterpretation p) y d) := by
      ext y; exact and_congr_left' (b.unraveled_data_iff p hc.1 x y)
    refine ⟨fun x hl => ?_, fun x hl hn => ?_⟩
    · change ¬ AtLeast (n + 1) (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧ _)
      rw [hpred x]
      exact solEdge_holds_dataMax (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2
    · apply hn
      change AtLeast (n + 1) (fun y => (b.toUnraveledInterpretation p).dataProperties dp x y ∧ _)
      rw [hpred x]
      exact solEdge_holds_dataMin (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hl hc.2

private theorem bound_of_allIndividuals {p : Problem} (hb : b.BindingsValid p)
    {ind : Individual} (h : ind ∈ p.allIndividuals) : ∃ r, b.BoundTo ind r := by
  cases ind with
  | named a =>
    have hm : a ∈ p.nominals := List.mem_filterMap.mpr ⟨.named a, h, rfl⟩
    exact hb.nomComplete a hm
  | anonymous doc lid =>
    have hm : (doc, lid) ∈ p.anons := List.mem_filterMap.mpr ⟨.anonymous doc lid, h, rfl⟩
    exact hb.anonComplete (doc, lid) hm

private theorem simple_for {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    {r : OrientedRole} (hr : r ∈ p.simpleRoles) : Simple p.rules p.chains r :=
  Problem.checkSimple_iff.mp hi.simple r hr

private theorem chain_path {p : Problem} {body : List OrientedRole}
    (ho : ∀ r ∈ body, isCoreObjPropIRI r.1 = true) (x y : b.Path) :
    objPath (b.toUnraveledInterpretation p) body x y ↔
      Sabrina.RoleChains.TransitivePaths.WordPath (complete b.baseInterpretation p.rules p.chains) body x y := by
  induction body generalizing x with
  | nil => rfl
  | cons r rs ih =>
    have h := unraveled_role_iff (b := b) p r (ho r (List.mem_cons_self ..))
    constructor <;> rintro ⟨z, he, ht⟩
    · exact ⟨z, (h x z).mp he, (ih (fun s hs => ho s (List.mem_cons_of_mem _ hs)) z).mp ht⟩
    · exact ⟨z, (h x z).mpr he, (ih (fun s hs => ho s (List.mem_cons_of_mem _ hs)) z).mpr ht⟩

private theorem base_pair_template (hw : b.BlockingValid) {r₁ r₂ : OrientedRole} {x y : b.Path}
    (h1 : b.Base r₁ x y) (h2 : b.Base r₂ x y) :
    ∃ a c : b.Node, b.Edge r₁ a c ∧ b.Edge r₂ a c := by
  have hchild_not_toRoot : ∀ {u v : b.Path} {c : b.Node} {r : OrientedRole},
      v.start = u.start → v.steps = c :: u.steps → u.steps = [] →
      (r, u.start) ∈ b.toRoot v.tailNode → False := by
    intro u v c r hst hs hu ht
    have hch : b.Child u.start c := by
      have hv := (Path.valid_cons (hs ▸ v.valid)).2
      simpa only [hst, hu, walkTail] using hv
    have hunb : b.blockedBy c = none := (child_of_root_unblocked hw u.start_isRoot hch).1
    have hvt : v.tailNode = c := by
      simp [Path.tailNode, hs, walkTail, target, hunb]
    exact (b.toRoot_valid v.tailNode _ ht).2.2 (by rw [hvt, hch.2])
  rcases h1 with ⟨heq1, hl1⟩ | ⟨hx1, hy1, hr1⟩ | ⟨c1, hst1, hs1, hd1⟩ | ⟨c1, hst1, hs1, hd1⟩ |
    ⟨hx1, hy1, ht1⟩ | ⟨hx1, hy1, ht1⟩ <;>
    rcases h2 with ⟨heq2, hl2⟩ | ⟨hx2, hy2, hr2⟩ | ⟨c2, hst2, hs2, hd2⟩ | ⟨c2, hst2, hs2, hd2⟩ |
      ⟨hx2, hy2, ht2⟩ | ⟨hx2, hy2, ht2⟩
  all_goals first
    | (cases heq1; exact ⟨x.tailNode, x.tailNode, (edge_loop_iff b r₁ _).mpr hl1, (edge_loop_iff b r₂ _).mpr hl2⟩)
    | exact ⟨x.start, y.start, .inr (.inl ⟨x.start_isRoot, y.start_isRoot, hr1⟩),
        .inr (.inl ⟨x.start_isRoot, y.start_isRoot, hr2⟩)⟩
    | (obtain rfl := (List.cons.inj (hs1.symm.trans hs2)).1
       have hch : b.Child x.tailNode c1 := by
         have hv := (Path.valid_cons (hs1 ▸ y.valid)).2
         simpa only [Path.tailNode, hst1] using hv
       exact ⟨x.tailNode, c1, (edge_child_iff hch).mpr hd1, (edge_child_iff hch).mpr hd2⟩)
    | (obtain rfl := (List.cons.inj (hs1.symm.trans hs2)).1
       have hch : b.Child y.tailNode c1 := by
         have hv := (Path.valid_cons (hs1 ▸ x.valid)).2
         simpa only [Path.tailNode, hst1] using hv
       exact ⟨c1, y.tailNode,
         (b.edge_converse r₁ c1 y.tailNode).mp ((edge_child_iff hch).mpr hd1),
         (b.edge_converse r₂ c1 y.tailNode).mp ((edge_child_iff hch).mpr hd2)⟩)
    | exact ⟨x.tailNode, y.start, .inr (.inr (.inr (.inr (.inl ht1)))), .inr (.inr (.inr (.inr (.inl ht2))))⟩
    | exact ⟨x.start, y.tailNode, .inr (.inr (.inr (.inr (.inr ht1)))), .inr (.inr (.inr (.inr (.inr ht2))))⟩
    | (exfalso; first
        | exact hx1 hx2
        | exact hy1 hy2
        | exact hx2 hx1
        | exact hy2 hy1
        | (cases heq1; exact hx2 hy2)
        | (cases heq1; exact hy2 hx2)
        | (cases heq2; exact hx1 hy1)
        | (cases heq2; exact hy1 hx1)
        | (rw [hy2] at hs1; cases hs1)
        | (rw [hx2] at hs1; cases hs1)
        | (rw [hy1] at hs2; cases hs2)
        | (rw [hx1] at hs2; cases hs2)
        | exact hchild_not_toRoot hst1 hs1 hx2 ht2
        | exact hchild_not_toRoot hst1 hs1 hy2 ht2
        | exact hchild_not_toRoot hst2 hs2 hx1 ht1
        | exact hchild_not_toRoot hst2 hs2 hy1 ht1
        | (cases heq1; have := congrArg List.length hs2; simp at this)
        | (cases heq2; have := congrArg List.length hs1; simp at this)
        | (have h1 := congrArg List.length hs1; have h2 := congrArg List.length hs2; simp at h1 h2; omega)
        | (cases heq1; rcases r₂ with ⟨_, _ | _⟩ <;> exact (b.rootEdges_valid _ hr2).2.2 rfl)
        | (cases heq2; rcases r₁ with ⟨_, _ | _⟩ <;> exact (b.rootEdges_valid _ hr1).2.2 rfl))

theorem sroiq_unraveled_models {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    (cf : b.BlockedClashFree p) (hs : b.BlockedSaturated rank p) :
    p.Models (b.toUnraveledInterpretation p) := by
  have allIndBound : ∀ ind ∈ p.allIndividuals, ∃ r, b.BoundTo ind r :=
    fun ind h => bound_of_allIndividuals hs.bindings h
  constructor
  case tbox =>
    intro q hq x hsub
    obtain ⟨hsubSyn, hsupSyn⟩ := hi.tbox q hq
    have indSub : ∀ ind ∈ q.sub.individuals, ∃ r, b.BoundTo ind r := fun ind h =>
      allIndBound ind (by
        have hm : ind ∈ p.tbox.flatMap (fun a => a.sub.individuals ++ a.sup.individuals) :=
          List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ h⟩
        simp [Problem.allIndividuals, hm])
    have indSup : ∀ ind ∈ q.sup.individuals, ∃ r, b.BoundTo ind r := fun ind h =>
      allIndBound ind (by
        have hm : ind ∈ p.tbox.flatMap (fun a => a.sub.individuals ++ a.sup.individuals) :=
          List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ h⟩
        simp [Problem.allIndividuals, hm])
    have cntSub : ∀ r ∈ q.sub.countedRoles, Simple p.rules p.chains r := fun r hr =>
      simple_for hi (by
        have hm : r ∈ p.tbox.flatMap (fun a => a.sub.countedRoles ++ a.sup.countedRoles) :=
          List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ hr⟩
        simp [Problem.simpleRoles, hm])
    have cntSup : ∀ r ∈ q.sup.countedRoles, Simple p.rules p.chains r := fun r hr =>
      simple_for hi (by
        have hm : r ∈ p.tbox.flatMap (fun a => a.sub.countedRoles ++ a.sup.countedRoles) :=
          List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ hr⟩
        simp [Problem.simpleRoles, hm])
    rcases hs.tbox q hq x.tailNode (x.tail_unblocked hs.blocking) with hd | hp
    · exact ((sroiq_unraveled_holds_pair hi cf hs hsubSyn cntSub indSub).2 x hd hsub).elim
    · exact (sroiq_unraveled_holds_pair hi cf hs hsupSyn cntSup indSup).1 x hp
  case rules =>
    intro q hq x y hxy
    obtain ⟨hr1, hr2⟩ := hi.rules q hq
    apply (unraveled_role_iff p q.2 hr2 x y).mpr
    exact Sabrina.RoleChains.RankedPaths.complete_roles b.baseInterpretation p.rules p.chains q.1 q.2 hq x y
      ((unraveled_role_iff p q.1 hr1 x y).mp hxy)
  case chains =>
    intro c hc x y hxy
    obtain ⟨hr, hbody⟩ := hi.chains c hc
    apply (unraveled_role_iff p (c.head, false) hr x y).mpr
    exact Sabrina.RoleChains.RankedPaths.complete_chains b.baseInterpretation p.rules p.chains c hc x y
      ((chain_path (fun r hr => hbody r.1 (List.mem_map_of_mem hr)) x y).mp hxy)
  case reflexive =>
    intro r hr x
    exact base_implies_unraveled (hi.reflexive r hr)
      ((base_loop_iff (r, false) x).mpr (hs.reflexive r hr _))
  case irreflexive =>
    intro r hr x he
    have hsim : Simple p.rules p.chains (r, false) := simple_for hi (by simp [Problem.simpleRoles, hr])
    have hbase := (simple_role_localizes hi hs (hi.irreflexive r hr) hsim x x).mp he
    exact cf.irreflexive r hr _ ((base_loop_iff (r, false) x).mp hbase)
  case asymmetric =>
    intro r hr x y hxy hyx
    have hsim : Simple p.rules p.chains (r, false) := simple_for hi (by simp [Problem.simpleRoles, hr])
    have h1 := (simple_role_localizes hi hs (hi.asymmetric r hr) hsim x y).mp hxy
    have h2 := base_flip (r := (r, false)) ((simple_role_localizes hi hs (hi.asymmetric r hr) hsim y x).mp hyx)
    obtain ⟨a, c, he1, he2⟩ := base_pair_template hs.blocking h1 h2
    exact cf.asymmetric r hr a c he1 ((b.edge_converse (r, false) c a).mp he2)
  case disjoint =>
    intro q hq x y ⟨he, he'⟩
    obtain ⟨h1, h2⟩ := hi.disjoint q hq
    have mem (r : OrientedRole) (hr : r ∈ [q.1, q.2]) : r ∈ p.simpleRoles := by
      have hm : r ∈ p.chars.disjoint.flatMap (fun (s, t) => [s, t]) :=
        List.mem_flatMap.mpr ⟨q, hq, hr⟩
      simp [Problem.simpleRoles, hm]
    have hb1 := (simple_role_localizes hi hs h1 (simple_for hi (mem q.1 (by simp))) x y).mp he
    have hb2 := (simple_role_localizes hi hs h2 (simple_for hi (mem q.2 (by simp))) x y).mp he'
    obtain ⟨a, c, he1, he2⟩ := base_pair_template hs.blocking hb1 hb2
    exact cf.disjoint q hq a c ⟨he1, he2⟩
  case classAssertions =>
    intro ac hac
    have hsyn := hi.classAssertions ac hac
    have hbound : ∃ r, b.BoundTo ac.1 r := allIndBound ac.1 (by
      have hm : ac.1 ∈ p.classAssertions.flatMap (fun (a, c) => a :: c.individuals) :=
        List.mem_flatMap.mpr ⟨ac, hac, List.mem_cons_self ..⟩
      simp [Problem.allIndividuals, hm])
    obtain ⟨r, hr⟩ := hbound
    have heval := evalIndividual_eq_of_bound hs.bindings hr
    have hlab : ac.2 ∈ b.labels r := hs.classAssertions ac hac r hr
    have hcnt : ∀ s ∈ ac.2.countedRoles, Simple p.rules p.chains s := fun s hs' =>
      simple_for hi (by
        have hm : s ∈ p.classAssertions.flatMap (fun (_, c) => c.countedRoles) :=
          List.mem_flatMap.mpr ⟨ac, hac, hs'⟩
        simp [Problem.simpleRoles, hm])
    have hinds : ∀ ind ∈ ac.2.individuals, ∃ r', b.BoundTo ind r' := fun ind hind =>
      allIndBound ind (by
        have hm : ind ∈ p.classAssertions.flatMap (fun (a, c) => a :: c.individuals) :=
          List.mem_flatMap.mpr ⟨ac, hac, List.mem_cons_of_mem _ hind⟩
        simp [Problem.allIndividuals, hm])
    change holds (b.toUnraveledInterpretation p) (evalIndividual b ac.1) ac.2
    rw [heval]
    exact (sroiq_unraveled_holds_pair hi cf hs hsyn hcnt hinds).1 (Path.root b r hr.isRoot) hlab
  case objAssertions =>
    intro rab hrab
    obtain ⟨r1, h1⟩ := allIndBound rab.2.1 (by
      have hm : rab.2.1 ∈ p.objAssertions.flatMap (fun (_, a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨rab, hrab, by simp⟩
      simp [Problem.allIndividuals, hm])
    obtain ⟨r2, h2⟩ := allIndBound rab.2.2 (by
      have hm : rab.2.2 ∈ p.objAssertions.flatMap (fun (_, a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨rab, hrab, by simp⟩
      simp [Problem.allIndividuals, hm])
    have he1 := evalIndividual_eq_of_bound hs.bindings h1
    have he2 := evalIndividual_eq_of_bound hs.bindings h2
    have hedge : b.Edge (rab.1, false) r1 r2 := hs.objAssertions rab hrab r1 r2 h1 h2
    have hbase : b.Base (rab.1, false) (Path.root b r1 h1.isRoot) (Path.root b r2 h2.isRoot) := by
      by_cases heq : r1 = r2
      · subst heq
        exact .inl ⟨rfl, (edge_loop_iff b (rab.1, false) r1).mp hedge⟩
      · exact .inr (.inl ⟨rfl, rfl, (edge_root_iff h1.isRoot h2.isRoot heq).mp hedge⟩)
    change holdsOriented (b.toUnraveledInterpretation p) (rab.1, false)
      (evalIndividual b rab.2.1) (evalIndividual b rab.2.2)
    rw [he1, he2]
    exact base_implies_unraveled (hi.objAssertions rab hrab) hbase
  case negObjAssertions =>
    intro rab hrab hhold
    obtain ⟨r1, h1⟩ := allIndBound rab.2.1 (by
      have hm : rab.2.1 ∈ p.negObjAssertions.flatMap (fun (_, a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨rab, hrab, by simp⟩
      simp [Problem.allIndividuals, hm])
    obtain ⟨r2, h2⟩ := allIndBound rab.2.2 (by
      have hm : rab.2.2 ∈ p.negObjAssertions.flatMap (fun (_, a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨rab, hrab, by simp⟩
      simp [Problem.allIndividuals, hm])
    have he1 := evalIndividual_eq_of_bound hs.bindings h1
    have he2 := evalIndividual_eq_of_bound hs.bindings h2
    have hall : .all (rab.1, false) (.nom rab.2.2 false) ∈ b.labels r1 :=
      hs.negObjAssertions rab hrab r1 h1
    have hhold' : holdsOriented (b.toUnraveledInterpretation p) (rab.1, false)
        (Path.root b r1 h1.isRoot) (Path.root b r2 h2.isRoot) := by
      change (b.toUnraveledInterpretation p).objectProperties rab.1
        (Path.root b r1 h1.isRoot) (Path.root b r2 h2.isRoot)
      rw [← he1, ← he2]
      exact hhold
    have hnom : .nom rab.2.2 false ∈ b.labels r2 :=
      universal_label hi hs (hi.negObjAssertions rab hrab) hall hhold'
    exact cf.nomNeg r2 rab.2.2 hnom h2
  case sameInds =>
    intro ab hab
    obtain ⟨r1, h1⟩ := allIndBound ab.1 (by
      have hm : ab.1 ∈ p.sameInds.flatMap (fun (a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨ab, hab, by simp⟩
      simp [Problem.allIndividuals, hm])
    obtain ⟨r2, h2⟩ := allIndBound ab.2 (by
      have hm : ab.2 ∈ p.sameInds.flatMap (fun (a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨ab, hab, by simp⟩
      simp [Problem.allIndividuals, hm])
    have heq := hs.sameInds ab hab r1 r2 h1 h2
    change evalIndividual b ab.1 = evalIndividual b ab.2
    rw [evalIndividual_eq_of_bound hs.bindings h1, evalIndividual_eq_of_bound hs.bindings h2]
    subst heq; rfl
  case diffInds =>
    intro ab hab heq
    obtain ⟨r1, h1⟩ := allIndBound ab.1 (by
      have hm : ab.1 ∈ p.diffInds.flatMap (fun (a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨ab, hab, by simp⟩
      simp [Problem.allIndividuals, hm])
    obtain ⟨r2, h2⟩ := allIndBound ab.2 (by
      have hm : ab.2 ∈ p.diffInds.flatMap (fun (a, b) => [a, b]) :=
        List.mem_flatMap.mpr ⟨ab, hab, by simp⟩
      simp [Problem.allIndividuals, hm])
    have he1 := evalIndividual_eq_of_bound hs.bindings h1
    have he2 := evalIndividual_eq_of_bound hs.bindings h2
    have hrt : r1 = r2 := congrArg Path.start (he1.symm.trans (heq.trans he2))
    exact cf.nomNeg r1 ab.2 (hs.diffInds ab hab r1 h1) (hrt.symm ▸ h2)
  case keys =>
    intro k hk x y hkx hky hnx hny hobj hdata
    obtain ⟨hclsSyn, hobjCore, hdataCore⟩ := hi.keys k hk
    unfold toUnraveledInterpretation namedPath at hnx hny
    cases hnoms : b.noms with
    | nil =>
      simp only [hnoms, List.isEmpty_nil, ↓reduceIte] at hnx hny
      exact hnx.trans hny.symm
    | cons hd tl =>
      simp only [hnoms, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hnx hny
      obtain ⟨hxnil, hxnamed⟩ := hnx
      obtain ⟨hynil, hynamed⟩ := hny
      have hxnamed' : b.isNamedRoot x.start = true := by simpa [hnoms] using hxnamed
      have hynamed' : b.isNamedRoot y.start = true := by simpa [hnoms] using hynamed
      have hxt : x.tailNode = x.start := by simp [Path.tailNode, hxnil, walkTail]
      have hyt : y.tailNode = y.start := by simp [Path.tailNode, hynil, walkTail]
      have hcnt : ∀ r ∈ k.cls.countedRoles, Simple p.rules p.chains r := fun r hr =>
        simple_for hi (by
          have hm : r ∈ p.keys.flatMap (fun a => a.cls.countedRoles) :=
            List.mem_flatMap.mpr ⟨k, hk, hr⟩
          simp [Problem.simpleRoles, hm])
      have hinds : ∀ ind ∈ k.cls.individuals, ∃ r', b.BoundTo ind r' := fun ind hind =>
        allIndBound ind (by
          have hm : ind ∈ p.keys.flatMap (fun a => a.cls.individuals) :=
            List.mem_flatMap.mpr ⟨k, hk, hind⟩
          simp [Problem.allIndividuals, hm])
      have hpair := sroiq_unraveled_holds_pair hi cf hs hclsSyn hcnt hinds
      have hclx : k.cls ∈ b.labels x.start := by
        rcases hs.keyCls k hk x.start hxnamed' with hpos | hneg
        · exact hpos
        · exact (hpair.2 x (hxt.symm ▸ hneg) hkx).elim
      have hcly : k.cls ∈ b.labels y.start := by
        rcases hs.keyCls k hk y.start hynamed' with hpos | hneg
        · exact hpos
        · exact (hpair.2 y (hyt.symm ▸ hneg) hky).elim
      have hobjMatch : ∀ r ∈ k.objProps, ∃ z, b.isNamedRoot z = true ∧
          b.Edge r x.start z ∧ b.Edge r y.start z := by
        intro r hr
        obtain ⟨z, hnz, hxz, hyz⟩ := hobj r hr
        unfold toUnraveledInterpretation namedPath at hnz
        simp only [hnoms, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hnz
        obtain ⟨hznil, hznamed⟩ := hnz
        have hznamed' : b.isNamedRoot z.start = true := by simpa [hnoms] using hznamed
        obtain ⟨⟨a, z₀⟩, haz, hzbeq⟩ := List.any_eq_true.mp hznamed'
        have hzEq : z₀ = z.start := beq_iff_eq.mp hzbeq
        have haz' : (a, z.start) ∈ b.noms := hzEq ▸ haz
        have hzt : z.tailNode = z.start := by simp [Path.tailNode, hznil, walkTail]
        have hexz : b.Edge r x.start z.start := by
          rcases hs.keyObjSplit k hk r hr x.start hxnamed' a z.start haz' with hed | hall
          · exact hed
          · exfalso
            have hnom : .nom (.named a) false ∈ b.labels z.tailNode :=
              universal_label hi hs (r := r) (hobjCore r hr) (hxt.symm ▸ hall) hxz
            exact cf.nomNeg z.start (.named a) (hzt ▸ hnom) haz'
        have heyz : b.Edge r y.start z.start := by
          rcases hs.keyObjSplit k hk r hr y.start hynamed' a z.start haz' with hed | hall
          · exact hed
          · exfalso
            have hnom : .nom (.named a) false ∈ b.labels z.tailNode :=
              universal_label hi hs (r := r) (hobjCore r hr) (hyt.symm ▸ hall) hyz
            exact cf.nomNeg z.start (.named a) (hzt ▸ hnom) haz'
        exact ⟨z.start, hznamed', hexz, heyz⟩
      rcases hs.keyMerge k hk x.start y.start hxnamed' hynamed' hclx hcly hobjMatch with
          hstartEq | ⟨dp, hdp, hkd⟩
      · exact Path.ext hstartEq (hxnil.trans hynil.symm)
      · exfalso
        obtain ⟨z, hxz, hyz⟩ := hdata dp hdp
        have hdpCore := hdataCore dp hdp
        have hxz' := (b.unraveled_data_iff p hdpCore x z).mp hxz
        have hyz' := (b.unraveled_data_iff p hdpCore y z).mp hyz
        rw [hxt] at hxz'
        rw [hyt, ← b.pathSol_eq_rootSol p hxnil hynil] at hyz'
        have hkd' : (x.start.val, y.start.val, dp) ∈ (b.pathCSP p x).keyDisjoint := by
          simp only [pathCSP, mkSubjectsDataCSP, pathKeyDisjoint, hxnil, List.isEmpty_nil,
            ↓reduceIte, List.mem_map]
          exact ⟨(x.start, y.start, dp), hkd, rfl⟩
        exact solEdge_keyDisjoint (b.pathCSP_solve cf hs.blocking x)
          (b.toUnraveledInterpretation p) hkd' z ⟨hxz', hyz'⟩
  case subData =>
    intro rs hrs x y hxy
    obtain ⟨hr1, hr2⟩ := hi.subData rs hrs
    exact (b.unraveled_data_iff p hr2 x y).mpr
      (solEdge_subData (b.pathCSP_solve cf hs.blocking x)
        (b.toUnraveledInterpretation p) hrs x.tailNode.val y
        ((b.unraveled_data_iff p hr1 x y).mp hxy))
  case disjointData =>
    intro rs hrs x y ⟨h1, h2⟩
    obtain ⟨hr1, hr2⟩ := hi.disjointData rs hrs
    exact solEdge_disjointData (b.pathCSP_solve cf hs.blocking x)
      (b.toUnraveledInterpretation p) hrs x.tailNode.val y
      ⟨(b.unraveled_data_iff p hr1 x y).mp h1, (b.unraveled_data_iff p hr2 x y).mp h2⟩
  case funcData =>
    intro dp hfd x y₁ y₂ h₁ h₂
    have hdp := hi.funcData dp hfd
    exact solEdge_funcData (b.pathCSP_solve cf hs.blocking x)
      (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hfd y₁ y₂
      ((b.unraveled_data_iff p hdp x y₁).mp h₁)
      ((b.unraveled_data_iff p hdp x y₂).mp h₂)
  case dataRanges =>
    intro rd hrd x y hxy
    obtain ⟨hdp, hd⟩ := hi.dataRanges rd hrd
    exact solEdge_dataRanges (b.pathCSP_solve cf hs.blocking x)
      (b.toUnraveledInterpretation p) (b.pathSubjLabels_mem x) hrd hd y
      ((b.unraveled_data_iff p hdp x y).mp hxy)
  case dataAssertions =>
    intro dal hdal
    obtain ⟨hdp, hlit⟩ := hi.dataAssertions dal hdal
    obtain ⟨r, hr⟩ := allIndBound dal.2.1 (by
      have hm : dal.2.1 ∈ p.dataAssertions.map (fun (_, a, _) => a) :=
        List.mem_map.mpr ⟨dal, hdal, rfl⟩
      simp [Problem.allIndividuals, hm])
    have heval := evalIndividual_eq_of_bound hs.bindings hr
    have hlab : .dataValue dal.1 dal.2.2 true ∈ b.labels r := hs.dataAssertions dal hdal r hr
    have hsyn : (Concept.dataValue dal.1 dal.2.2 true).isSROIQD = true :=
      Bool.and_eq_true_iff.mpr ⟨hdp, hlit⟩
    change holds (b.toUnraveledInterpretation p) (evalIndividual b dal.2.1)
      (.dataValue dal.1 dal.2.2 true)
    rw [heval]
    exact (sroiq_unraveled_holds_pair hi cf hs hsyn
      (by simp [Concept.countedRoles]) (by simp [Concept.individuals])).1
      (Path.root b r hr.isRoot) hlab
  case negDataAssertions =>
    intro dal hdal
    obtain ⟨hdp, hlit⟩ := hi.negDataAssertions dal hdal
    obtain ⟨r, hr⟩ := allIndBound dal.2.1 (by
      have hm : dal.2.1 ∈ p.negDataAssertions.map (fun (_, a, _) => a) :=
        List.mem_map.mpr ⟨dal, hdal, rfl⟩
      simp [Problem.allIndividuals, hm])
    have heval := evalIndividual_eq_of_bound hs.bindings hr
    have hlab : .dataValue dal.1 dal.2.2 false ∈ b.labels r := hs.negDataAssertions dal hdal r hr
    have hsyn : (Concept.dataValue dal.1 dal.2.2 false).isSROIQD = true :=
      Bool.and_eq_true_iff.mpr ⟨hdp, hlit⟩
    change holds (b.toUnraveledInterpretation p) (evalIndividual b dal.2.1)
      (.dataValue dal.1 dal.2.2 false)
    rw [heval]
    exact (sroiq_unraveled_holds_pair hi cf hs hsyn
      (by simp [Concept.countedRoles]) (by simp [Concept.individuals])).1
      (Path.root b r hr.isRoot) hlab

end BlockedForest

/-- Full `SROIQ(D)` model construction from an open, saturated blocked forest. -/
theorem sroiqd_blocked_saturated_sat {rank : Rank} {p : Problem} {b : BlockedForest}
    (hsroiqd : p.isSROIQD rank = true) (hcf : b.BlockedClashFree p)
    (hsat : b.BlockedSaturated rank p) : p.Sat := by
  have hi := p.sroiqdInput hsroiqd
  have hcnt : ∀ r ∈ p.root.countedRoles, Simple p.rules p.chains r := fun r hr =>
    BlockedForest.simple_for hi (by simp [Problem.simpleRoles, hr])
  have hinds : ∀ ind ∈ p.root.individuals, ∃ r, b.BoundTo ind r := fun ind hind =>
    BlockedForest.bound_of_allIndividuals hsat.bindings (by simp [Problem.allIndividuals, hind])
  refine ⟨b.toUnraveledInterpretation p, b.sroiq_unraveled_models hi hcf hsat,
    BlockedForest.Path.root0 b, ?_⟩
  exact (b.sroiq_unraveled_holds_pair hi hcf hsat hi.root hcnt hinds).1
    (BlockedForest.Path.root0 b) hsat.root

/-- Object-only `SROIQ` model construction from an open, saturated blocked forest. -/
theorem sroiq_blocked_saturated_sat {rank : Rank} {p : Problem} {b : BlockedForest}
    (hsroiq : p.isSROIQ rank = true) (hcf : b.BlockedClashFree p)
    (hsat : b.BlockedSaturated rank p) : p.Sat :=
  sroiqd_blocked_saturated_sat (p.isSROIQ_implies_isSROIQD hsroiq) hcf hsat

#print axioms sroiqd_blocked_saturated_sat
#print axioms sroiq_blocked_saturated_sat

end Sabrina.OWL2.SROIQD.Termination
