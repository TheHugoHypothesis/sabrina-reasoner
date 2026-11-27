import Std.Data.HashSet
import Std.Data.HashMap
import Std.Data.DHashMap
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

private def addMany {p : Problem} {s : Branch}
    (items : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 }) : Transition p s :=
  let newLabels := items.map Subtype.val
  deterministic { s with labels := newLabels ++ s.labels }
    fun ⟨i, hm, env, hs⟩ =>
      ⟨i, hm, env,
        ⟨fun x c hmem =>
          (List.mem_append.mp hmem).elim
            (fun hnew => by
              obtain ⟨⟨⟨x', c'⟩, hpf⟩, _, heq⟩ := List.mem_map.mp hnew
              cases heq; exact hpf i env hm hs)
            (hs.labels x c),
         hs.edges, hs.negEdges, hs.unequal, hs.noms, hs.anons, hs.dataEdges, hs.negDataEdges, hs.dataConstraints⟩⟩

private def addManyEdges {p : Problem} {s : Branch}
    (items : List { e : OrientedRole × Nat × Nat // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holdsOriented i e.1 (env e.2.1) (env e.2.2) }) : Transition p s :=
  let newEdges := items.map fun ⟨(r, x, y), _⟩ => if r.2 then (r.1, y, x) else (r.1, x, y)
  deterministic { s with edges := newEdges ++ s.edges }
    fun ⟨i, hm, env, hs⟩ =>
      ⟨i, hm, env,
        ⟨hs.labels,
         fun r x y hmem =>
          (List.mem_append.mp hmem).elim
            (fun hnew => by
              obtain ⟨⟨⟨⟨rn, dir⟩, a, b⟩, hpf⟩, _, heq⟩ := List.mem_map.mp hnew
              cases dir with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
                rcases heq with ⟨rfl, rfl, rfl⟩
                exact hpf i env hm hs
              | true =>
                simp only [↓reduceIte, Prod.mk.injEq] at heq
                rcases heq with ⟨rfl, rfl, rfl⟩
                exact hpf i env hm hs)
            (hs.edges r x y),
         hs.negEdges, hs.unequal, hs.noms, hs.anons, hs.dataEdges, hs.negDataEdges, hs.dataConstraints⟩⟩

private def addManyDataConstraints {p : Problem} {s : Branch}
    (items : List { item : Nat × IRI × DataRange // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → ∀ y, i.dataProperties item.2.1 (env item.1) y → dataHolds i y item.2.2 }) :
    Transition p s :=
  let newDCs := items.map Subtype.val
  deterministic { s with dataConstraints := newDCs ++ s.dataConstraints }
    fun ⟨i, hm, env, hs⟩ =>
      ⟨i, hm, env,
        ⟨hs.labels, hs.edges, hs.negEdges, hs.unequal, hs.noms, hs.anons, hs.dataEdges, hs.negDataEdges,
         fun x dp d hmem =>
          (List.mem_append.mp hmem).elim
            (fun hnew => by
              obtain ⟨⟨⟨x', dp', d'⟩, hpf⟩, _, heq⟩ := List.mem_map.mp hnew
              cases heq; exact hpf i env hm hs)
            (hs.dataConstraints x dp d)⟩⟩

private def addManyDataEdges {p : Problem} {s : Branch}
    (items : List { item : IRI × Nat × Value // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → i.dataProperties item.1 (env item.2.1) (i.embedValue item.2.2) }) :
    Transition p s :=
  let newDEs := items.map Subtype.val
  deterministic { s with dataEdges := newDEs ++ s.dataEdges }
    fun ⟨i, hm, env, hs⟩ =>
      ⟨i, hm, env,
        ⟨hs.labels, hs.edges, hs.negEdges, hs.unequal, hs.noms, hs.anons,
         fun dp x v hmem =>
          (List.mem_append.mp hmem).elim
            (fun hnew => by
              obtain ⟨⟨⟨dp', x', v'⟩, hpf⟩, _, heq⟩ := List.mem_map.mp hnew
              cases heq; exact hpf i env hm hs)
            (hs.dataEdges dp x v),
         hs.negDataEdges, hs.dataConstraints⟩⟩

private def allocateManySome {p : Problem} {s : Branch}
    (items : List { item : Nat × OrientedRole × Concept // (item.1, .some item.2.1 item.2.2) ∈ s.labels }) :
    Transition p s :=
  deterministic (s.allocateManySome (items.map Subtype.val)) fun ⟨i, hm, env, hs⟩ =>
    let ⟨env', hh⟩ := Branch.allocateManySome_sound hs (items.map Subtype.val) fun item hmem => by
      obtain ⟨⟨it, hpf⟩, _, rfl⟩ := List.mem_map.mp hmem
      exact hpf
    ⟨i, hm, env', hh⟩

private def indKey : Individual → String × String
  | .named a => ("", a)
  | .anonymous d l => (d, l)

private def hashDataRange : DataRange → UInt64
  | .datatype s => mixHash 1 (hash s)
  | .complement d => mixHash 2 (hashDataRange d)
  | .intersection a b => mixHash 3 (mixHash (hashDataRange a) (hashDataRange b))
  | .union a b => mixHash 4 (mixHash (hashDataRange a) (hashDataRange b))
  | .oneOf ls => mixHash 5 (ls.foldl (fun h l => mixHash h (mixHash (hash l.lexical) (hash l.datatype))) 7)
  | .restriction t fs => mixHash 6 (mixHash (hash t) (fs.foldl (fun h f => mixHash h (mixHash (hash f.name) (hash f.bound.lexical))) 11))

private def hashConcept : Concept → UInt64
  | .top => 1
  | .bottom => 2
  | .lit s b => mixHash 3 (mixHash (hash s) (hash b))
  | .nom a b => mixHash 4 (mixHash (hash (indKey a)) (hash b))
  | .self r b => mixHash 5 (mixHash (hash r) (hash b))
  | .conj a b => mixHash 6 (mixHash (hashConcept a) (hashConcept b))
  | .disj a b => mixHash 7 (mixHash (hashConcept a) (hashConcept b))
  | .some r c => mixHash 8 (mixHash (hash r) (hashConcept c))
  | .all r c => mixHash 9 (mixHash (hash r) (hashConcept c))
  | .min n r c => mixHash 10 (mixHash (hash n) (mixHash (hash r) (hashConcept c)))
  | .max n r c => mixHash 11 (mixHash (hash n) (mixHash (hash r) (hashConcept c)))
  | .dataSome r d => mixHash 12 (mixHash (hash r) (hashDataRange d))
  | .dataAll r d => mixHash 13 (mixHash (hash r) (hashDataRange d))
  | .dataValue r l b => mixHash 14 (mixHash (hash r) (mixHash (hash l.lexical) (mixHash (hash l.datatype) (hash b))))
  | .dataMin n r d => mixHash 15 (mixHash (hash n) (mixHash (hash r) (hashDataRange d)))
  | .dataMax n r d => mixHash 16 (mixHash (hash n) (mixHash (hash r) (hashDataRange d)))

private local instance : Hashable DataRange := ⟨hashDataRange⟩
private local instance : Hashable Concept := ⟨hashConcept⟩
private local instance : LawfulHashable DataRange := ⟨fun _ _ h => by rw [beq_iff_eq.mp h]⟩
private local instance : LawfulHashable Concept := ⟨fun _ _ h => by rw [beq_iff_eq.mp h]⟩

private theorem Branch.add_edges_eq (s : Branch) (x : Nat) (c : Concept) :
    (s.add x c).edges = s.edges := by
  unfold Branch.add
  split <;> rfl

private theorem holdsOriented_of_edge_mem {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} (hs : s.Realizes i env) {r : OrientedRole} {x y : Nat}
    (h : (if r.2 then (r.1, y, x) else (r.1, x, y)) ∈ s.edges) :
    holdsOriented i r (env x) (env y) := by
  rcases r with ⟨rn, _ | _⟩
  · exact hs.edges rn x y h
  · exact hs.edges rn y x h

private structure LabelStore (labels : List (Nat × Concept)) where
  map : Std.HashSet (Nat × Concept)
  sound : ∀ xc, map.contains xc = true → xc ∈ labels

private def LabelStore.addAll {labels : List (Nat × Concept)}
    (init : Std.HashSet (Nat × Concept))
    (hinit : ∀ y, init.contains y = true → y ∈ labels) :
    (rem : List (Nat × Concept)) → (∀ x ∈ rem, x ∈ labels) → LabelStore labels
  | [], _ => ⟨init, hinit⟩
  | x :: xs, hsub =>
    LabelStore.addAll (init.insert x)
      (fun y hy => by
        rw [Std.HashSet.contains_insert] at hy
        rcases Bool.or_eq_true_iff.mp hy with heq | hmem
        · exact (beq_iff_eq.mp heq) ▸ hsub x (List.mem_cons_self ..)
        · exact hinit y hmem)
      xs (fun z hz => hsub z (List.mem_cons_of_mem _ hz))

private def LabelStore.build (labels : List (Nat × Concept)) : LabelStore labels :=
  LabelStore.addAll (Std.HashSet.emptyWithCapacity labels.length)
    (fun _ h => by simp at h) labels (fun _ hx => hx)

private def LabelStore.extend {oldLabels newLabels : List (Nat × Concept)}
    (st : LabelStore oldLabels) (added : List (Nat × Concept))
    (hOld : ∀ xc ∈ oldLabels, xc ∈ newLabels)
    (hAdded : ∀ xc ∈ added, xc ∈ newLabels) : LabelStore newLabels :=
  LabelStore.addAll st.map (fun y hy => hOld y (st.sound y hy)) added hAdded

private def LabelStore.mem? {labels : List (Nat × Concept)} (st : LabelStore labels)
    (xc : Nat × Concept) : Option (PLift (xc ∈ labels)) :=
  if h : st.map.contains xc then some ⟨st.sound xc h⟩ else none

private def LabelStore.knownProof {s : Branch} (st : LabelStore s.labels) (x : Nat) :
    (c : Concept) → Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object), s.Realizes i env → holds i (env x) c))
  | .top => some ⟨fun _ _ _ => trivial⟩
  | c => (st.mem? (x, c)).map fun ⟨h⟩ => ⟨fun _ _ hs => hs.labels x c h⟩

private def LabelStore.fastKnown {labels : List (Nat × Concept)} (st : LabelStore labels) (x : Nat) :
    Concept → Bool
  | .top => true
  | c => st.map.contains (x, c)

private structure EdgeIndex (edges : List (IRI × Nat × Nat)) where
  edgeMap : Std.DHashMap (IRI × Nat × Nat) (fun e => PLift (e ∈ edges))
  outAdj : Std.HashMap (IRI × Nat) (List Nat)
  inAdj : Std.HashMap (IRI × Nat) (List Nat)
  inEdgesByTarget : Std.HashMap Nat (List (OrientedRole × Nat))
  edgesByRole : Std.HashMap IRI (List (Nat × Nat))
  roleSources : Std.HashMap OrientedRole (List Nat)
  edgeNodes : Array Nat

private def EdgeIndex.adj {edges : List (IRI × Nat × Nat)} (eidx : EdgeIndex edges)
    (r : OrientedRole) (x : Nat) : List Nat :=
  if r.2 then eidx.inAdj.getD (r.1, x) [] else eidx.outAdj.getD (r.1, x) []

private def EdgeIndex.edgeProof {s : Branch} (eidx : EdgeIndex s.edges) (r : OrientedRole) (x y : Nat) :
    Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object), s.Realizes i env → holdsOriented i r (env x) (env y))) :=
  (eidx.edgeMap.get? (if r.2 then (r.1, y, x) else (r.1, x, y))).map fun ⟨h⟩ =>
    ⟨fun _ _ hs => holdsOriented_of_edge_mem hs h⟩

private def buildEdgeIndex (edges : List (IRI × Nat × Nat)) : EdgeIndex edges := Id.run do
  let mut nodeSet : Std.HashSet Nat := {}
  let mut edgeNodes : Array Nat := #[]
  let mut edgeMap : Std.DHashMap (IRI × Nat × Nat) (fun e => PLift (e ∈ edges)) := {}
  let mut outAdj : Std.HashMap (IRI × Nat) (List Nat) := {}
  let mut inAdj : Std.HashMap (IRI × Nat) (List Nat) := {}
  let mut inEdgesByTarget : Std.HashMap Nat (List (OrientedRole × Nat)) := {}
  let mut edgesByRole : Std.HashMap IRI (List (Nat × Nat)) := {}
  let mut roleSources : Std.HashMap OrientedRole (List Nat) := {}
  for ⟨(r, x, y), hmem⟩ in edges.attach do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; edgeNodes := edgeNodes.push x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; edgeNodes := edgeNodes.push y
    if !edgeMap.contains (r, x, y) then
      edgeMap := edgeMap.insert (r, x, y) ⟨hmem⟩
      outAdj := outAdj.insert (r, x) (y :: outAdj.getD (r, x) [])
      inAdj := inAdj.insert (r, y) (x :: inAdj.getD (r, y) [])
      inEdgesByTarget := inEdgesByTarget.insert y (((r, false), x) :: inEdgesByTarget.getD y [])
      inEdgesByTarget := inEdgesByTarget.insert x (((r, true), y) :: inEdgesByTarget.getD x [])
      edgesByRole := edgesByRole.insert r ((x, y) :: edgesByRole.getD r [])
      roleSources := roleSources.insert (r, false) (x :: roleSources.getD (r, false) [])
      roleSources := roleSources.insert (r, true) (y :: roleSources.getD (r, true) [])
  return { edgeMap, outAdj, inAdj, inEdgesByTarget, edgesByRole, roleSources, edgeNodes }

private structure BranchIndex (s : Branch) where
  nodes : List Nat
  labels : LabelStore s.labels
  expandedSet : Std.HashSet (Nat × Concept)
  eidx : EdgeIndex s.edges
  someLabelNodes : Std.HashMap OrientedRole (List Nat)
  classNodes : Std.HashMap IRI (List Nat)
  nomNodes : Std.HashMap (String × String) (List Nat)
  nomBinding : Std.HashMap IRI (List Nat)
  anonBinding : Std.HashMap (String × String) (List Nat)
  dataSources : Std.HashMap IRI (List Nat)
  dataTouchNodes : Std.HashMap IRI (List Nat)
  dataByPropNode : Std.HashMap (IRI × Nat) (List Value)
  dataEdgesByPropNode : Std.HashMap (IRI × Nat) (List { d : IRI × Nat × Value // d ∈ s.dataEdges })
  dataConstraintByNodeProp : Std.HashMap (Nat × IRI) (List DataRange)
  dataCardLabels : List (Nat × Concept)
  hasSelfLabel : Bool

private def buildBranchIndexWith (s : Branch) (edgeIdx? : Option (EdgeIndex s.edges) := none) : BranchIndex s := Id.run do
  let labels := LabelStore.build s.labels
  let mut nodeSet : Std.HashSet Nat := {}
  let mut nodeArr : Array Nat := #[]
  let mut seenLabel : Std.HashSet (Nat × Concept) := {}
  let mut expandedSet : Std.HashSet (Nat × Concept) := {}
  let mut classNodes : Std.HashMap IRI (List Nat) := {}
  let mut nomNodes : Std.HashMap (String × String) (List Nat) := {}
  let mut someLabelNodes : Std.HashMap OrientedRole (List Nat) := {}
  let mut dataTouchNodes : Std.HashMap IRI (List Nat) := {}
  let mut dataCardLabels : List (Nat × Concept) := []
  let mut hasSelfLabel := false
  for p in s.expanded do
    expandedSet := expandedSet.insert p
  for (x, c) in s.labels do
    if !nodeSet.contains x then
      nodeSet := nodeSet.insert x
      nodeArr := nodeArr.push x
    if !seenLabel.contains (x, c) then
      seenLabel := seenLabel.insert (x, c)
      match c with
      | .lit cls true => classNodes := classNodes.insert cls (x :: classNodes.getD cls [])
      | .nom ind true =>
        let k := indKey ind
        nomNodes := nomNodes.insert k (x :: nomNodes.getD k [])
      | .some r _ => someLabelNodes := someLabelNodes.insert r (x :: someLabelNodes.getD r [])
      | .self _ _ => hasSelfLabel := true
      | .dataSome dp _ | .dataMin _ dp _ =>
        dataCardLabels := (x, c) :: dataCardLabels
        dataTouchNodes := dataTouchNodes.insert dp (x :: dataTouchNodes.getD dp [])
      | .dataMax _ _ _ => dataCardLabels := (x, c) :: dataCardLabels
      | _ => pure ()
  let eidx := match edgeIdx? with
    | some e => e
    | none => buildEdgeIndex s.edges
  for n in eidx.edgeNodes do
    if !nodeSet.contains n then nodeSet := nodeSet.insert n; nodeArr := nodeArr.push n
  for (_, x, y) in s.negEdges do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; nodeArr := nodeArr.push y
  for (x, y) in s.unequal do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; nodeArr := nodeArr.push y
  let mut nomBinding : Std.HashMap IRI (List Nat) := {}
  for (a, x) in s.noms do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    nomBinding := nomBinding.insert a (x :: nomBinding.getD a [])
  let mut anonBinding : Std.HashMap (String × String) (List Nat) := {}
  for (k, x) in s.anons do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    anonBinding := anonBinding.insert k (x :: anonBinding.getD k [])
  let mut dataSources : Std.HashMap IRI (List Nat) := {}
  let mut dataByPropNode : Std.HashMap (IRI × Nat) (List Value) := {}
  let mut dataEdgesByPropNode : Std.HashMap (IRI × Nat) (List { d : IRI × Nat × Value // d ∈ s.dataEdges }) := {}
  for ⟨(dp, x, v), hmem⟩ in s.dataEdges.attach do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    dataSources := dataSources.insert dp (x :: dataSources.getD dp [])
    dataTouchNodes := dataTouchNodes.insert dp (x :: dataTouchNodes.getD dp [])
    dataByPropNode := dataByPropNode.insert (dp, x) (v :: dataByPropNode.getD (dp, x) [])
    dataEdgesByPropNode := dataEdgesByPropNode.insert (dp, x) (⟨(dp, x, v), hmem⟩ :: dataEdgesByPropNode.getD (dp, x) [])
  for (_, x, _) in s.negDataEdges do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
  let mut dataConstraintByNodeProp : Std.HashMap (Nat × IRI) (List DataRange) := {}
  for (x, dp, d) in s.dataConstraints do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodeArr := nodeArr.push x
    dataConstraintByNodeProp := dataConstraintByNodeProp.insert (x, dp) (d :: dataConstraintByNodeProp.getD (x, dp) [])
  return {
    nodes := nodeArr.toList
    labels, expandedSet, eidx,
    someLabelNodes, classNodes, nomNodes,
    nomBinding, anonBinding, dataSources, dataTouchNodes, dataByPropNode, dataEdgesByPropNode,
    dataConstraintByNodeProp, dataCardLabels, hasSelfLabel
  }

private def buildBranchIndex (s : Branch) : BranchIndex s := buildBranchIndexWith s none

private inductive AnchorKey where
  | cls (c : IRI)
  | role (r : OrientedRole)
  | nom (k : String × String)
  | data (dp : IRI)

private def gciAnchorKey : Concept → Option AnchorKey
  | .nom a true => some (.nom (indKey a))
  | .lit c true => some (.cls c)
  | .some r _ => some (.role r)
  | .dataSome dp _ => some (.data dp)
  | .conj a b => gciAnchorKey a <|> gciAnchorKey b
  | _ => none

private structure StaticIndex (p : Problem) where
  disjMap : Std.HashMap IRI (List { pr : IRI × Inclusion // pr.2 ∈ p.tbox })
  tboxBySup : Std.HashMap Concept (List { q : Inclusion // q ∈ p.tbox })
  topAllGCIs : List { pr : Inclusion × OrientedRole × Concept // pr.1 ∈ p.tbox ∧ pr.1.sub = .top ∧ pr.1.sup = .all pr.2.1 pr.2.2 }
  topMaxGCIs : List { pr : Inclusion × Nat × OrientedRole × Concept // pr.1 ∈ p.tbox ∧ pr.1.sub = .top ∧ pr.1.sup = .max pr.2.1 pr.2.2.1 pr.2.2.2 }
  topOtherGCIs : List { q : Inclusion // q ∈ p.tbox ∧ q.sub = .top }
  classGCIs : Std.HashMap IRI (List { q : Inclusion // q ∈ p.tbox })
  roleGCIs : Std.HashMap OrientedRole (List { q : Inclusion // q ∈ p.tbox })
  nomGCIs : Std.HashMap (String × String) (List { q : Inclusion // q ∈ p.tbox })
  dataGCIs : Std.HashMap IRI (List { q : Inclusion // q ∈ p.tbox })
  unanchoredGCIs : List { q : Inclusion // q ∈ p.tbox }

private def buildStaticIndex (p : Problem) : StaticIndex p := Id.run do
  let mut disjMap : Std.HashMap IRI (List { pr : IRI × Inclusion // pr.2 ∈ p.tbox }) := {}
  let mut tboxBySup : Std.HashMap Concept (List { q : Inclusion // q ∈ p.tbox }) := {}
  let mut topAllGCIs : List { pr : Inclusion × OrientedRole × Concept // pr.1 ∈ p.tbox ∧ pr.1.sub = .top ∧ pr.1.sup = .all pr.2.1 pr.2.2 } := []
  let mut topMaxGCIs : List { pr : Inclusion × Nat × OrientedRole × Concept // pr.1 ∈ p.tbox ∧ pr.1.sub = .top ∧ pr.1.sup = .max pr.2.1 pr.2.2.1 pr.2.2.2 } := []
  let mut topOtherGCIs : List { q : Inclusion // q ∈ p.tbox ∧ q.sub = .top } := []
  let mut classGCIs : Std.HashMap IRI (List { q : Inclusion // q ∈ p.tbox }) := {}
  let mut roleGCIs : Std.HashMap OrientedRole (List { q : Inclusion // q ∈ p.tbox }) := {}
  let mut nomGCIs : Std.HashMap (String × String) (List { q : Inclusion // q ∈ p.tbox }) := {}
  let mut dataGCIs : Std.HashMap IRI (List { q : Inclusion // q ∈ p.tbox }) := {}
  let mut unanchoredGCIs : List { q : Inclusion // q ∈ p.tbox } := []
  for ⟨q, hq⟩ in p.tbox.attach do
    tboxBySup := tboxBySup.insert q.sup (⟨q, hq⟩ :: tboxBySup.getD q.sup [])
    if q.sup == .bottom then
      match q.sub with
      | .conj (.lit a true) (.lit b true) =>
        disjMap := disjMap.insert a (⟨(b, q), hq⟩ :: disjMap.getD a [])
        disjMap := disjMap.insert b (⟨(a, q), hq⟩ :: disjMap.getD b [])
      | _ => pure ()
    if hsub : q.sub = .top then
      match hsup : q.sup with
      | .all r body => topAllGCIs := ⟨(q, r, body), hq, hsub, hsup⟩ :: topAllGCIs
      | .max n r body => topMaxGCIs := ⟨(q, n, r, body), hq, hsub, hsup⟩ :: topMaxGCIs
      | _ => topOtherGCIs := ⟨q, hq, hsub⟩ :: topOtherGCIs
    else
      match gciAnchorKey q.sub with
      | some (.cls c) => classGCIs := classGCIs.insert c (⟨q, hq⟩ :: classGCIs.getD c [])
      | some (.role r) => roleGCIs := roleGCIs.insert r (⟨q, hq⟩ :: roleGCIs.getD r [])
      | some (.nom k) => nomGCIs := nomGCIs.insert k (⟨q, hq⟩ :: nomGCIs.getD k [])
      | some (.data dp) => dataGCIs := dataGCIs.insert dp (⟨q, hq⟩ :: dataGCIs.getD dp [])
      | none => unanchoredGCIs := ⟨q, hq⟩ :: unanchoredGCIs
  return { disjMap, tboxBySup, topAllGCIs, topMaxGCIs, topOtherGCIs,
           classGCIs, roleGCIs, nomGCIs, dataGCIs, unanchoredGCIs }

private def BranchIndex.fastKnown {s : Branch} (idx : BranchIndex s) (x : Nat) : Concept → Bool :=
  idx.labels.fastKnown x

private def BranchIndex.knownProof {s : Branch} (idx : BranchIndex s) (x : Nat) (c : Concept) :
    Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object), s.Realizes i env → holds i (env x) c)) :=
  idx.labels.knownProof x c

private def BranchIndex.fastEdge {s : Branch} (idx : BranchIndex s) (r : OrientedRole) (x y : Nat) : Bool :=
  if r.2 then idx.eidx.edgeMap.contains (r.1, y, x) else idx.eidx.edgeMap.contains (r.1, x, y)

private def BranchIndex.edgeProof {s : Branch} (idx : BranchIndex s) (r : OrientedRole) (x y : Nat) :
    Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object), s.Realizes i env → holdsOriented i r (env x) (env y))) :=
  idx.eidx.edgeProof r x y

private def BranchIndex.adj {s : Branch} (idx : BranchIndex s) (r : OrientedRole) (x : Nat) : List Nat :=
  idx.eidx.adj r x

private def fastNodeCount (s : Branch) : Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  for n in s.support do
    seen := seen.insert n
  return seen.size

private def inequalityClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.unequal.attach.findSome? fun ⟨⟨x, y⟩, h⟩ =>
    if he : x = y then some (close fun ⟨_, _, env, hs⟩ => hs.unequal x y h (congrArg env he))
    else none

private def labelClash (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    if hc : c = .bottom then
      some (close fun ⟨i, _, env, hs⟩ => by
        have he := hs.labels x c h
        rw [hc] at he; exact he)
    else match idx.knownProof x c.dual with
      | some ⟨hd⟩ =>
        some (close fun ⟨i, _, env, hs⟩ =>
          (holds_dual i (env x) c).mp (hd i env hs) (hs.labels x c h))
      | none => none

private def negEdgeClash (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  s.negEdges.attach.findSome? fun ⟨⟨r, x, y⟩, h⟩ =>
    match idx.edgeProof (r, false) x y with
    | some ⟨he⟩ =>
      some (close fun ⟨i, _, env, hs⟩ => hs.negEdges r x y h (he i env hs))
    | none => none

private def nominalMergeIndexed (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    match c with
    | .nom (.named a) true =>
      if (idx.nomBinding.getD a []).any (· != x) then
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
      else none
    | .nom (.named a) false =>
      if (idx.nomBinding.getD a []).contains x then
        s.noms.attach.findSome? fun ⟨⟨b, y⟩, hn⟩ =>
          if hab : a = b then
            if hxy : x = y then
              some (close fun ⟨i, _, env, hs⟩ => by
                have hx : env x ≠ i.individuals (.named a) := hs.labels x (.nom (.named a) false) h
                have hy : env x = i.individuals (.named a) := hxy ▸ hab ▸ hs.noms b y hn
                exact hx hy)
            else none
          else none
      else none
    | .nom (.anonymous doc lid) true =>
      if (idx.anonBinding.getD (doc, lid) []).any (· != x) then
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
      else none
    | .nom (.anonymous doc lid) false =>
      if (idx.anonBinding.getD (doc, lid) []).contains x then
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
      else none
    | _ => none

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

private def roleCharSteps (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  (p.chars.irreflexive.attach.findSome? fun ⟨r, hr⟩ =>
    (idx.eidx.edgesByRole.getD r []).findSome? fun (x, y) =>
      if x == y then
        match idx.edgeProof (r, false) x x with
        | some ⟨he⟩ =>
          some (close fun ⟨i, hm, env, hs⟩ => hm.irreflexive r hr _ (he i env hs))
        | none => none
      else none) <|>
  (p.chars.asymmetric.attach.findSome? fun ⟨r, hr⟩ =>
    (idx.eidx.edgesByRole.getD r []).findSome? fun (x, y) =>
      match idx.edgeProof (r, false) x y, idx.edgeProof (r, false) y x with
      | some ⟨hxy⟩, some ⟨hyx⟩ =>
        some (close fun ⟨i, hm, env, hs⟩ =>
          hm.asymmetric r hr _ _ (hxy i env hs) (hyx i env hs))
      | _, _ => none) <|>
  (p.chars.disjoint.attach.findSome? fun ⟨(r, t), hd⟩ =>
    (idx.eidx.edgesByRole.getD r.1 []).findSome? fun (u, v) =>
      let x := if r.2 then v else u
      let y := if r.2 then u else v
      match idx.edgeProof r x y, idx.edgeProof t x y with
      | some ⟨hr⟩, some ⟨ht⟩ =>
        some (close fun ⟨i, hm, env, hs⟩ =>
          hm.disjoint (r, t) hd _ _ ⟨hr i env hs, ht i env hs⟩)
      | _, _ => none) <|>
  (p.chars.reflexive.attach.findSome? fun ⟨r, hr⟩ =>
    idx.nodes.findSome? fun x =>
      if idx.eidx.edgeMap.contains (r, x, x) then none
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

private def dataClashIndexed (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  let maybeNeg := !s.negDataEdges.isEmpty && !s.dataEdges.isEmpty
  let maybeDisj := !p.disjointData.isEmpty && !s.dataEdges.isEmpty
  let maybeFunc := !s.dataEdges.isEmpty && p.funcData.any fun dp =>
    (idx.dataSources.getD dp []).any fun x => ((idx.dataByPropNode.getD (dp, x) []).eraseDups).length ≥ 2
  let maybeRange := !s.dataEdges.isEmpty && !s.dataConstraints.isEmpty && (Id.run do
    let mut cache : Std.HashMap DataRange (Option (Value → Bool)) := {}
    for (x, dp, d) in s.dataConstraints do
      let vals := idx.dataByPropNode.getD (dp, x) []
      if vals.isEmpty then continue
      let pred? ← match cache[d]? with
        | some c? => pure c?
        | none =>
          let c? := (compile d).map (·.holds)
          cache := cache.insert d c?
          pure c?
      if let some pred := pred? then
        if vals.any (fun v => !pred v) then return true
    return false)
  let maybeCard := !idx.dataCardLabels.isEmpty && (Id.run do
    let mut srCache : Std.HashMap DataRange (Bool × Option Nat) := {}
    let mut funcSet : Std.HashSet IRI := {}
    for dp in p.funcData do funcSet := funcSet.insert dp
    for (x, c) in idx.dataCardLabels do
      match c with
      | .dataMax n dp _ =>
        if (idx.dataByPropNode.getD (dp, x) []).length ≥ n + 1 then return true
      | .dataSome dp d =>
        if funcSet.contains dp && !(idx.dataByPropNode.getD (dp, x) []).isEmpty then return true
        let cs := idx.dataConstraintByNodeProp.getD (x, dp) []
        let comb := cs.foldl DataRange.intersection d
        let (isEmp, finSz?) ← match srCache[comb]? with
          | some info => pure info
          | none =>
            let info := match compileSolvedRange comb with
              | none => (false, none)
              | some sr => (sr.isEmpty, sr.finiteValues?.map List.length)
            srCache := srCache.insert comb info
            pure info
        if isEmp then return true
        if let some sz := finSz? then
          if sz == 0 || !s.negDataEdges.isEmpty then return true
      | .dataMin (n + 1) dp d =>
        if funcSet.contains dp && (n + 1 ≥ 2 || !(idx.dataByPropNode.getD (dp, x) []).isEmpty) then return true
        let cs := idx.dataConstraintByNodeProp.getD (x, dp) []
        let comb := cs.foldl DataRange.intersection d
        let (isEmp, finSz?) ← match srCache[comb]? with
          | some info => pure info
          | none =>
            let info := match compileSolvedRange comb with
              | none => (false, none)
              | some sr => (sr.isEmpty, sr.finiteValues?.map List.length)
            srCache := srCache.insert comb info
            pure info
        if isEmp then return true
        if let some sz := finSz? then
          if sz < n + 1 || !s.negDataEdges.isEmpty then return true
      | _ => pure ()
    return false)
  if maybeNeg || maybeDisj || maybeFunc || maybeRange || maybeCard then
    dataClash p s
  else none

private def dataSteps (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
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
  -- 2. Lazily propagate DataPropertyRange axioms in ONE batch to nodes that actually touch `dp`
  (Id.run do
    let mut items : List { item : Nat × IRI × DataRange // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
        p.Models i → s.Realizes i env → ∀ y, i.dataProperties item.2.1 (env item.1) y → dataHolds i y item.2.2 } := []
    let mut seen : Std.HashSet (Nat × IRI) := {}
    for ⟨⟨dp, d⟩, hdr⟩ in p.dataRanges.attach do
      for x in idx.dataTouchNodes.getD dp [] do
        if !(idx.dataConstraintByNodeProp.getD (x, dp) []).contains d && !seen.contains (x, dp) then
          if !s.dataConstraints.contains (x, dp, d) then
            seen := seen.insert (x, dp)
            items := ⟨(x, dp, d), fun _ env hm _ => hm.dataRanges (dp, d) hdr (env x)⟩ :: items
    if items.isEmpty then return none else return some (addManyDataConstraints items)) <|>
  -- 3. Propagate SubDataPropertyOf along observed data edges in ONE batch
  (Id.run do
    let mut items : List { item : IRI × Nat × Value // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
        p.Models i → s.Realizes i env → i.dataProperties item.1 (env item.2.1) (i.embedValue item.2.2) } := []
    for ⟨⟨r, t⟩, hrt⟩ in p.subData.attach do
      if !(idx.dataSources.getD r []).isEmpty then
        for ⟨⟨dp, x, v⟩, he⟩ in s.dataEdges.attach do
          if h1 : dp = r then
            if !(idx.dataByPropNode.getD (t, x) []).contains v && !s.dataEdges.contains (t, x, v) then
              items := ⟨(t, x, v), fun _ env hm hs =>
                hm.subData (r, t) hrt (env x) _ (h1 ▸ hs.dataEdges dp x v he)⟩ :: items
    if items.isEmpty then return none else return some (addManyDataEdges items)) <|>
  -- 4. Propagate universal dataConstraints downward along SubDataPropertyOf in ONE batch
  (Id.run do
    let mut items : List { item : Nat × IRI × DataRange // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
        p.Models i → s.Realizes i env → ∀ y, i.dataProperties item.2.1 (env item.1) y → dataHolds i y item.2.2 } := []
    for ⟨⟨r, t⟩, hrt⟩ in p.subData.attach do
      for ⟨⟨x, dp, d⟩, hc⟩ in s.dataConstraints.attach do
        if h1 : dp = t then
          if !(idx.dataConstraintByNodeProp.getD (x, r) []).contains d && !s.dataConstraints.contains (x, r, d) then
            items := ⟨(x, r, d), fun _ env hm hs y hy =>
              hs.dataConstraints x dp d hc y (h1 ▸ hm.subData (r, t) hrt (env x) y hy)⟩ :: items
    if items.isEmpty then return none else return some (addManyDataConstraints items))

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

private def keyMergeIndexed (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  if p.keys.isEmpty then none
  else p.keys.attach.findSome? fun ⟨k, _⟩ =>
    let matchingNoms := s.noms.filter fun (_, x) => idx.fastKnown x k.cls
    if matchingNoms.length < 2 then none
    else keyMerge p s

private def isTriggered (s : Branch) (x : Nat) : Concept → Bool
  | .top => true
  | .bottom => false
  | .lit a true => s.known x (.lit a true)
  | .nom a true => s.known x (.nom a true)
  | .self r true => s.known x (.self r true) || s.edge r x x
  | .dataValue dp l true => s.known x (.dataValue dp l true)
  | .conj a b => isTriggered s x a && isTriggered s x b
  | .disj a b => isTriggered s x a || isTriggered s x b
  | .some r body =>
    s.known x (.some r body) ||
    s.edges.any fun (rn, a, b) =>
      rn == r.1 && (if r.2 then b == x && isTriggered s a body else a == x && isTriggered s b body)
  | .dataSome dp d =>
    s.known x (.dataSome dp d) ||
    s.dataEdges.any fun (r, y, v) =>
      r == dp && y == x &&
      (d == .datatype literalDatatype ||
        match compile d with | some comp => comp.holds v | none => false)
  | c => s.known x c

private theorem isTriggered_sound {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} (hs : s.Realizes i env) {x : Nat} {c : Concept}
    (ht : isTriggered s x c = true) : holds i (env x) c := by
  induction c generalizing x with
  | top => trivial
  | bottom => simp [isTriggered] at ht
  | lit a b =>
    cases b <;> exact Branch.known_sound hs ht
  | nom a b =>
    cases b <;> exact Branch.known_sound hs ht
  | self r b =>
    cases b with
    | false => exact Branch.known_sound hs ht
    | true =>
      rcases Bool.or_eq_true_iff.mp ht with hk | he
      · exact Branch.known_sound hs hk
      · exact Branch.edge_sound hs he
  | dataValue dp l b =>
    cases b <;> exact Branch.known_sound hs ht
  | conj a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp ht
    exact ⟨iha ha, ihb hb⟩
  | disj a b iha ihb =>
    rcases Bool.or_eq_true_iff.mp ht with ha | hb
    · exact Or.inl (iha ha)
    · exact Or.inr (ihb hb)
  | some r body ih =>
    rcases Bool.or_eq_true_iff.mp ht with hk | hany
    · exact Branch.known_sound hs hk
    · obtain ⟨⟨rn, a, b⟩, hmem, hcond⟩ := List.any_eq_true.mp hany
      obtain ⟨hrn, hdir⟩ := Bool.and_eq_true_iff.mp hcond
      have hrn' := beq_iff_eq.mp hrn
      subst hrn'
      rcases r with ⟨rn, _ | _⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hdir
        obtain ⟨rfl, hbody⟩ := hdir
        exact ⟨env b, hs.edges rn a b hmem, ih hbody⟩
      · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hdir
        obtain ⟨rfl, hbody⟩ := hdir
        exact ⟨env a, hs.edges rn a b hmem, ih hbody⟩
  | dataSome dp d =>
    rcases Bool.or_eq_true_iff.mp ht with hk | hany
    · exact Branch.known_sound hs hk
    · obtain ⟨⟨r, y, v⟩, hmem, hcond⟩ := List.any_eq_true.mp hany
      obtain ⟨⟨hr, hy⟩, hdok⟩ := Bool.and_eq_true_iff.mp hcond |>.imp_left Bool.and_eq_true_iff.mp
      have hr' := beq_iff_eq.mp hr
      have hy' := beq_iff_eq.mp hy
      subst hr' hy'
      refine ⟨i.embedValue v, hs.dataEdges r y v hmem, ?_⟩
      rcases Bool.or_eq_true_iff.mp hdok with hlit | hcomp
      · have hdeq := beq_iff_eq.mp hlit
        subst hdeq
        exact i.literalDatatypeExt _
      · cases hc : compile d with
        | none => simp [hc] at hcomp
        | some comp =>
          rw [hc] at hcomp
          exact (comp.holds_iff i v).mp hcomp
  | _ => exact Branch.known_sound hs ht

private def isTriggeredProof {s : Branch} (idx : BranchIndex s) (x : Nat) :
    (c : Concept) → Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      s.Realizes i env → holds i (env x) c))
  | .top => some ⟨fun _ _ _ => trivial⟩
  | .bottom => none
  | .lit a true => idx.knownProof x (.lit a true)
  | .nom a true => idx.knownProof x (.nom a true)
  | .self r true =>
    match idx.knownProof x (.self r true) with
    | some hp => some hp
    | none => (idx.edgeProof r x x).map fun ⟨he⟩ => ⟨he⟩
  | .dataValue dp l true => idx.knownProof x (.dataValue dp l true)
  | .conj a b =>
    match isTriggeredProof idx x a, isTriggeredProof idx x b with
    | some ⟨ha⟩, some ⟨hb⟩ => some ⟨fun i env hs => ⟨ha i env hs, hb i env hs⟩⟩
    | _, _ => none
  | .disj a b =>
    match isTriggeredProof idx x a with
    | some ⟨ha⟩ => some ⟨fun i env hs => Or.inl (ha i env hs)⟩
    | none => (isTriggeredProof idx x b).map fun ⟨hb⟩ => ⟨fun i env hs => Or.inr (hb i env hs)⟩
  | .some r body =>
    idx.knownProof x (.some r body) <|>
    (idx.adj r x).findSome? fun y =>
      match idx.edgeProof r x y, isTriggeredProof idx y body with
      | some ⟨he⟩, some ⟨hb⟩ => some ⟨fun i env hs => ⟨env y, he i env hs, hb i env hs⟩⟩
      | _, _ => none
  | .dataSome dp d =>
    idx.knownProof x (.dataSome dp d) <|>
    (idx.dataEdgesByPropNode.getD (dp, x) []).findSome? fun ⟨(r, y, v), hmem⟩ =>
      if hr : r = dp ∧ y = x then
        if hlit : d = .datatype literalDatatype then
          some ⟨fun i _ hs => ⟨i.embedValue v, hr.2 ▸ hr.1 ▸ hs.dataEdges r y v hmem,
            hlit ▸ i.literalDatatypeExt _⟩⟩
        else match compile d with
          | none => none
          | some comp =>
            if hok : comp.holds v = true then
              some ⟨fun i _ hs => ⟨i.embedValue v, hr.2 ▸ hr.1 ▸ hs.dataEdges r y v hmem,
                (comp.holds_iff i v).mp hok⟩⟩
            else none
      else none
  | c => idx.knownProof x c

private def hierarchy (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) := Id.run do
  let mut added : Std.HashSet (OrientedRole × Nat × Nat) := {}
  let mut items : List { e : OrientedRole × Nat × Nat // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holdsOriented i e.1 (env e.2.1) (env e.2.2) } := []
  for ⟨(r, t), h⟩ in p.rules.attach do
    for (u, v) in idx.eidx.edgesByRole.getD r.1 [] do
      let x := if r.2 then v else u
      let y := if r.2 then u else v
      if !idx.fastEdge t x y && !added.contains (t, x, y) then
        if let some ⟨he⟩ := idx.edgeProof r x y then
          added := added.insert (t, x, y)
          items := ⟨(t, x, y), fun i env hm hs => hm.rules (r, t) h (env x) (env y) (he i env hs)⟩ :: items
  if items.isEmpty then return none else return some (addManyEdges items)

private def walkIdxTargetsProof {s : Branch} (idx : BranchIndex s) (x : Nat) :
    (rs : List OrientedRole) →
    List { y : Nat // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      s.Realizes i env → objPath i rs (env x) (env y) }
  | [] => [⟨x, fun _ _ _ => rfl⟩]
  | r :: rs =>
    (idx.adj r x).flatMap fun y =>
      match idx.edgeProof r x y with
      | none => []
      | some ⟨he⟩ =>
        (walkIdxTargetsProof idx y rs).map fun ⟨z, hz⟩ =>
          ⟨z, fun i env hs => ⟨env y, he i env hs, hz i env hs⟩⟩

private def chains (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) := Id.run do
  let mut added : Std.HashSet (IRI × Nat × Nat) := {}
  let mut items : List { e : OrientedRole × Nat × Nat // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holdsOriented i e.1 (env e.2.1) (env e.2.2) } := []
  for ⟨c, hc⟩ in p.chains.attach do
    match hbody : c.body with
    | [] =>
      for x in idx.nodes do
        if !idx.eidx.edgeMap.contains (c.head, x, x) && !added.contains (c.head, x, x) then
          added := added.insert (c.head, x, x)
          items := ⟨((c.head, false), x, x), fun _ env hm _ =>
            hm.chains c hc (env x) (env x) (by rw [hbody]; rfl)⟩ :: items
    | r0 :: rs =>
      for (u, v) in idx.eidx.edgesByRole.getD r0.1 [] do
        let x := if r0.2 then v else u
        let mid := if r0.2 then u else v
        if let some ⟨h0⟩ := idx.edgeProof r0 x mid then
          for ⟨y, hy⟩ in walkIdxTargetsProof idx mid rs do
            if !idx.eidx.edgeMap.contains (c.head, x, y) && !added.contains (c.head, x, y) then
              added := added.insert (c.head, x, y)
              items := ⟨((c.head, false), x, y), fun i env hm hs =>
                hm.chains c hc (env x) (env y) (by rw [hbody]; exact ⟨env mid, h0 i env hs, hy i env hs⟩)⟩ :: items
  if items.isEmpty then return none else return some (addManyEdges items)

private def collectConjLeaves (c : Concept) :
    List { d : Concept // ∀ (i : Interpretation datatypeMap) (w : i.Object), holds i w c → holds i w d } :=
  match c with
  | .conj a b =>
    (collectConjLeaves a).map (fun ⟨d, hd⟩ => ⟨d, fun i w h => hd i w h.1⟩) ++
    (collectConjLeaves b).map (fun ⟨d, hd⟩ => ⟨d, fun i w h => hd i w h.2⟩)
  | .top => []
  | other => [⟨other, fun _ _ h => h⟩]

private def addManySame {p : Problem} {s : Branch}
    (items : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 }) :
    { t : Transition p s // ∀ b ∈ t.branches, b.edges = s.edges } :=
  ⟨addMany items, fun b hb => by
    simp only [addMany, deterministic, List.mem_singleton] at hb
    subst hb; rfl⟩

private def selectSame {p : Problem} {s : Branch} (x : Nat) (a b : Concept)
    (h : ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env x) a ∨ holds i (env x) b) :
    { t : Transition p s // ∀ u ∈ t.branches, u.edges = s.edges } :=
  ⟨select x a b h, fun u hu => by
    simp only [select, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact Branch.add_edges_eq ..⟩

private def localLabels (p : Problem) (s : Branch) (idx : BranchIndex s) :
    Option { t : Transition p s // ∀ b ∈ t.branches, b.edges = s.edges } := Id.run do
  let mut added : Std.HashSet (Nat × Concept) := {}
  let mut items : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  for ⟨(x, c), h⟩ in s.labels.attach do
    match hc : c with
    | .conj a b =>
      for ⟨d, hd⟩ in collectConjLeaves (.conj a b) do
        if !idx.fastKnown x d && !added.contains (x, d) then
          added := added.insert (x, d)
          items := ⟨(x, d), fun i env _ hs => hd i (env x) (hs.labels x (.conj a b) (hc ▸ h))⟩ :: items
    | .all r body =>
      for y in idx.adj r x do
        if !idx.fastKnown y body && !added.contains (y, body) then
          if let some ⟨he⟩ := idx.edgeProof r x y then
            added := added.insert (y, body)
            items := ⟨(y, body), fun i env _ hs => hs.labels x (.all r body) (hc ▸ h) (env y) (he i env hs)⟩ :: items
    | _ => pure ()
  if items.isEmpty then return none else return some (addManySame items)

private def deterministicGCI (p : Problem) (st : StaticIndex p) (s : Branch) (idx : BranchIndex s)
    (absorb : Bool := false) :
    Option { t : Transition p s // ∀ b ∈ t.branches, b.edges = s.edges } := Id.run do
  let mut added : Std.HashSet (Nat × Concept) := {}
  let mut items : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  if absorb then
    for ⟨(q, r, body), hq, hsub, hsup⟩ in st.topAllGCIs do
      for (u, v) in idx.eidx.edgesByRole.getD r.1 [] do
        let x := if r.2 then v else u
        let y := if r.2 then u else v
        if !idx.fastKnown y body && !added.contains (y, body) then
          if let some ⟨he⟩ := idx.edgeProof r x y then
            added := added.insert (y, body)
            items := ⟨(y, body), fun i env hm hs => by
              have hAll := hm.tbox q hq (env x) (hsub ▸ trivial)
              rw [hsup] at hAll
              exact hAll (env y) (he i env hs)⟩ :: items
    for ⟨(q, n, r, _body), hq, hsub, _hsup⟩ in st.topMaxGCIs do
      for x in idx.eidx.roleSources.getD r [] do
        if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
          if (idx.adj r x).length ≥ n + 1 then
            added := added.insert (x, q.sup)
            items := ⟨(x, q.sup), fun i env hm _ => hm.tbox q hq (env x) (hsub ▸ trivial)⟩ :: items
    for ⟨q, hq, hsub⟩ in st.topOtherGCIs do
      for x in idx.nodes do
        if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
          added := added.insert (x, q.sup)
          items := ⟨(x, q.sup), fun i env hm _ => hm.tbox q hq (env x) (hsub ▸ trivial)⟩ :: items
    for (cls, cands) in idx.classNodes do
      for ⟨q, hq⟩ in st.classGCIs.getD cls [] do
        for x in cands do
          if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
            if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
              added := added.insert (x, q.sup)
              items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
    for (r, cands) in idx.eidx.roleSources do
      for ⟨q, hq⟩ in st.roleGCIs.getD r [] do
        for x in cands do
          if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
            if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
              added := added.insert (x, q.sup)
              items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
    for (r, cands) in idx.someLabelNodes do
      for ⟨q, hq⟩ in st.roleGCIs.getD r [] do
        for x in cands do
          if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
            if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
              added := added.insert (x, q.sup)
              items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
    for (k, cands) in idx.nomNodes do
      for ⟨q, hq⟩ in st.nomGCIs.getD k [] do
        for x in cands do
          if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
            if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
              added := added.insert (x, q.sup)
              items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
    for (dp, cands) in idx.dataTouchNodes do
      for ⟨q, hq⟩ in st.dataGCIs.getD dp [] do
        for x in cands do
          if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
            if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
              added := added.insert (x, q.sup)
              items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
    for ⟨q, hq⟩ in st.unanchoredGCIs do
      for x in idx.nodes do
        if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
          if let some ⟨ht⟩ := isTriggeredProof idx x q.sub then
            added := added.insert (x, q.sup)
            items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: items
  else
    for ⟨q, hq⟩ in p.tbox.attach do
      for x in idx.nodes do
        if !idx.fastKnown x q.sup && !added.contains (x, q.sup) then
          if hp : (q.sub.triggeringPremises (s.known x) false).isSome then
            let support := (q.sub.triggeringPremises (s.known x) false).get hp
            added := added.insert (x, q.sup)
            items := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x)
              (support.property.2 i (env x) (fun c hc => Branch.known_sound hs (support.property.1 c hc)))⟩ :: items
  if items.isEmpty then return none else return some (addManySame items)

private def disjAlreadyKnown {s : Branch} (idx : BranchIndex s) (x : Nat) : Concept → Bool
  | .disj a b => disjAlreadyKnown idx x a || disjAlreadyKnown idx x b
  | c => idx.fastKnown x c

private def disjAlreadyKnownSmall (s : Branch) (x : Nat) : Concept → Bool
  | .disj a b => disjAlreadyKnownSmall s x a || disjAlreadyKnownSmall s x b
  | c => s.known x c

private def disjunctions (p : Problem) (st : StaticIndex p) (s : Branch) (idx : BranchIndex s) :
    Option { t : Transition p s // ∀ b ∈ t.branches, b.edges = s.edges } := Id.run do
  let mut added : Std.HashSet (Nat × Concept) := {}
  let mut unitItems : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  let refutesLit (x : Nat) (cls : IRI) :
      Option { _u : Unit // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
        p.Models i → s.Realizes i env → ¬ holds i (env x) (.lit cls true) } :=
    (st.disjMap.getD cls []).findSome? fun ⟨(other, q), hq⟩ =>
      match idx.knownProof x (.lit other true) with
      | some ⟨hkn⟩ =>
        if hsup : q.sup = .bottom then
          if hsub1 : q.sub = .conj (.lit cls true) (.lit other true) then
            some ⟨(), fun i env hm hs hcls => by
              have hbot := hm.tbox q hq (env x) (hsub1 ▸ ⟨hcls, hkn i env hs⟩)
              rw [hsup] at hbot; exact hbot⟩
          else if hsub2 : q.sub = .conj (.lit other true) (.lit cls true) then
            some ⟨(), fun i env hm hs hcls => by
              have hbot := hm.tbox q hq (env x) (hsub2 ▸ ⟨hkn i env hs, hcls⟩)
              rw [hsup] at hbot; exact hbot⟩
          else none
        else none
      | none => none
  for ⟨(x, c), h⟩ in s.labels.attach do
    match hc : c with
    | .disj a b =>
      if disjAlreadyKnown idx x a || disjAlreadyKnown idx x b then continue
      match idx.knownProof x a.dual with
      | some ⟨ha⟩ =>
        if !added.contains (x, b) then
          added := added.insert (x, b)
          unitItems := ⟨(x, b), fun i env _ hs =>
            (hs.labels x (.disj a b) (hc ▸ h)).resolve_left
              ((holds_dual i (env x) a).mp (ha i env hs))⟩ :: unitItems
      | none =>
        match idx.knownProof x b.dual with
        | some ⟨hb⟩ =>
          if !added.contains (x, a) then
            added := added.insert (x, a)
            unitItems := ⟨(x, a), fun i env _ hs =>
              (hs.labels x (.disj a b) (hc ▸ h)).resolve_right
                ((holds_dual i (env x) b).mp (hb i env hs))⟩ :: unitItems
        | none =>
          match haLit : a, hbLit : b with
          | .lit clsA true, _ =>
            if let some ⟨_, hnotA⟩ := refutesLit x clsA then
              if !added.contains (x, b) then
                added := added.insert (x, b)
                unitItems := ⟨(x, b), fun i env hm hs =>
                  (hs.labels x (.disj a b) (hc ▸ h)).resolve_left (haLit ▸ hnotA i env hm hs)⟩ :: unitItems
            else match hbLit2 : b with
            | .lit clsB true =>
              if let some ⟨_, hnotB⟩ := refutesLit x clsB then
                if !added.contains (x, a) then
                  added := added.insert (x, a)
                  unitItems := ⟨(x, a), fun i env hm hs =>
                    (hs.labels x (.disj a b) (hc ▸ h)).resolve_right (hbLit2 ▸ hnotB i env hm hs)⟩ :: unitItems
            | _ => pure ()
          | _, .lit clsB true =>
            if let some ⟨_, hnotB⟩ := refutesLit x clsB then
              if !added.contains (x, a) then
                added := added.insert (x, a)
                unitItems := ⟨(x, a), fun i env hm hs =>
                  (hs.labels x (.disj a b) (hc ▸ h)).resolve_right (hbLit ▸ hnotB i env hm hs)⟩ :: unitItems
          | _, _ => pure ()
    | _ => pure ()
  if !unitItems.isEmpty then
    return some (addManySame unitItems)
  return s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .disj a b =>
      if disjAlreadyKnown idx x a || disjAlreadyKnown idx x b then none
      else some (selectSame x a b fun _ _ _ hs => hs.labels x (.disj a b) h)
    | _ => none

private def splitClass {p : Problem} {s : Branch} (x : Nat) (a : Concept) : Transition p s :=
  select x a a.dual fun i env _ _ => by
    classical
    rcases Classical.em (holds i (env x) a) with h | h
    · exact Or.inl h
    · exact Or.inr ((holds_dual i (env x) a).mpr h)

private def splitClassSame {p : Problem} {s : Branch} (x : Nat) (a : Concept) :
    { t : Transition p s // ∀ u ∈ t.branches, u.edges = s.edges } :=
  selectSame x a a.dual fun i env _ _ => by
    classical
    rcases Classical.em (holds i (env x) a) with h | h
    · exact Or.inl h
    · exact Or.inr ((holds_dual i (env x) a).mpr h)

private def undecidedGCI (p : Problem) (s : Branch) (idx : BranchIndex s)
    (deferAbsorbed : Bool := false) :
    Option { t : Transition p s // ∀ u ∈ t.branches, u.edges = s.edges } :=
  p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if deferAbsorbed && (q.sub.isDeferrable || q.sub.absorptionPremises.isSome || q.sub.nominalGuard?.isSome) then none
    else idx.nodes.findSome? fun x =>
      if idx.fastKnown x q.sup || idx.fastKnown x q.sub.dual then none
      else some (selectSame x q.sub.dual q.sup (fun i env hm _ => by
        classical
        rcases Classical.em (holds i (env x) q.sub) with ha | ha
        · exact Or.inr (hm.tbox q hq (env x) ha)
        · exact Or.inl ((holds_dual i (env x) q.sub).mpr ha)))

private def undecidedGCIFallback (p : Problem) (s : Branch) (nodes : List Nat) :
    Option (Transition p s) :=
  nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if s.known x q.sup || s.known x q.sub.dual then none
    else
      match hng : q.sub.nominalGuard? with
      | some (inds, rest) =>
        let matched : Option { a : Individual // a ∈ inds ∧ s.known x (.nom a true) = true } :=
          inds.attach.findSome? fun ⟨a, ha⟩ =>
            if hnom : s.known x (.nom a true) then some ⟨a, ha, hnom⟩ else none
        match matched with
        | some ⟨a, ha, hnom⟩ =>
          if s.known x rest.dual then none
          else some (select x rest.dual q.sup (fun i env hm hs => by
            classical
            rcases Classical.em (holds i (env x) rest) with hr | hr
            · exact Or.inr (hm.tbox q hq (env x)
                (Concept.nominalGuard?_sound hng i (env x) ha (Branch.known_sound hs hnom) hr))
            · exact Or.inl ((holds_dual i (env x) rest).mpr hr)))
        | none =>
          some (select x q.sub.dual q.sup (fun i env hm _ => by
            classical
            rcases Classical.em (holds i (env x) q.sub) with ha | ha
            · exact Or.inr (hm.tbox q hq (env x) ha)
            · exact Or.inl ((holds_dual i (env x) q.sub).mpr ha)))
      | none =>
        some (select x q.sub.dual q.sup (fun i env hm _ => by
          classical
          rcases Classical.em (holds i (env x) q.sub) with ha | ha
          · exact Or.inr (hm.tbox q hq (env x) ha)
          · exact Or.inl ((holds_dual i (env x) q.sub).mpr ha)))

private def qualifiers (p : Problem) (s : Branch) (idx : BranchIndex s) :
    Option { t : Transition p s // ∀ u ∈ t.branches, u.edges = s.edges } :=
  s.labels.findSome? fun (x, c) =>
    match c with
    | .max _ r body =>
      (idx.adj r x).findSome? fun y =>
        if !(idx.fastKnown y body || idx.fastKnown y body.dual) then
          some (splitClassSame y body)
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

private def upperBounds (p : Problem) (s : Branch) (idx : BranchIndex s) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .max n r body =>
      let adjQual := (idx.adj r x).filter fun y => idx.fastKnown y body
      if adjQual.length < n + 1 then none
      else
        let qualified := s.nodes.filter fun y => s.edge r x y && s.known y body
        if hn : n + 1 ≤ qualified.length then
          let ys := qualified.take (n + 1)
          some (mergeChoices h ys (List.length_take_of_le hn)
            ((List.take_sublist ..).nodup (List.filter_sublist.nodup s.nodes_nodup))
            (fun _ hy => Bool.and_eq_true_iff.mp ((List.mem_filter.mp (List.mem_of_mem_take hy)).2)))
        else none
    | _ => none

private def witnesses (p : Problem) (s : Branch) (idx : BranchIndex s) (maxNodes : Nat) :
    Option (Transition p s) := Id.run do
  let budget := if maxNodes ≥ idx.nodes.length then maxNodes - idx.nodes.length else 0
  let mut someItems : List { item : Nat × OrientedRole × Concept // (item.1, .some item.2.1 item.2.2) ∈ s.labels } := []
  let mut seenSome : Std.HashSet (Nat × Concept) := {}
  for ⟨(x, c), h⟩ in s.labels.attach do
    if idx.expandedSet.contains (x, c) then continue
    match hc : c with
    | .some r body =>
      if !(idx.adj r x).any (fun y => idx.fastKnown y body) && !seenSome.contains (x, c) then
        if someItems.length < max 1 budget then
          seenSome := seenSome.insert (x, c)
          someItems := ⟨(x, r, body), hc ▸ h⟩ :: someItems
    | _ => pure ()
  if !someItems.isEmpty then
    return some (allocateManySome someItems)
  return s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    if idx.expandedSet.contains (x, c) then none
    else match c with
    | .min (n + 1) r body =>
      if n + 1 > maxNodes then none else
      some (deterministic (s.allocate x r body (.min (n + 1) r body) (n + 1) true)
        fun ⟨i, hm, env, hs⟩ => by
          obtain ⟨values, hln, hnd, hq⟩ := hs.labels x (.min (n + 1) r body) h
          obtain ⟨env', hh⟩ := Branch.allocate_sound hs (mark := .min (n + 1) r body)
            (n + 1) true values hln (fun _ => hnd) hq (Branch.label_support h)
          exact ⟨i, hm, env', hh⟩)
    | _ => none

private def nextSmall (p : Problem) (s : Branch) (maxNodes : Nat) (deferAbsorbed : Bool := false) :
    Option (Transition p s) :=
  let nodes := s.nodes
  inequalityClash p s <|>
  (s.labels.attach.findSome? fun ⟨⟨x, c⟩, h⟩ =>
    if hc : c = .bottom then
      some (close fun ⟨_, _, _, hs⟩ => by have he := hs.labels x c h; rw [hc] at he; exact he)
    else if hd : s.known x c.dual then
      some (close fun ⟨i, _, env, hs⟩ =>
        (holds_dual i (env x) c).mp (Branch.known_sound hs hd) (hs.labels x c h))
    else none) <|>
  (s.negEdges.attach.findSome? fun ⟨⟨r, x, y⟩, h⟩ =>
    if he : s.edge (r, false) x y then
      some (close fun ⟨_, _, _, hs⟩ => hs.negEdges r x y h (Branch.edge_sound hs he))
    else none) <|>
  dataClash p s <|> nominalMerge p s <|> keyMerge p s <|> selfSteps p s <|>
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
      else some (addEdge (r, false) x x fun _ _ hm _ => hm.reflexive r hr _)) <|>
  (s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
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
  (p.dataRanges.attach.findSome? fun ⟨⟨dp, d⟩, hdr⟩ =>
    nodes.findSome? fun x =>
      if s.dataConstraints.contains (x, dp, d) then none
      else some (deterministic (s.addDataConstraint x dp d) fun ⟨i, hm, env, hs⟩ =>
        ⟨i, hm, env, Branch.addDataConstraint_realizes hs (hm.dataRanges (dp, d) hdr (env x))⟩)) <|>
  (p.subData.attach.findSome? fun ⟨⟨r, t⟩, hrt⟩ =>
    s.dataEdges.attach.findSome? fun ⟨⟨dp, x, v⟩, he⟩ =>
      if h1 : dp = r then
        if s.dataEdges.contains (t, x, v) then none
        else some (deterministic (s.addDataEdge t x v) fun ⟨i, hm, env, hs⟩ =>
          ⟨i, hm, env, Branch.addDataEdge_realizes hs
            (hm.subData (r, t) hrt (env x) _ (h1 ▸ hs.dataEdges dp x v he))⟩)
      else none) <|>
  (p.subData.attach.findSome? fun ⟨⟨r, t⟩, hrt⟩ =>
    s.dataConstraints.attach.findSome? fun ⟨⟨x, dp, d⟩, hc⟩ =>
      if h1 : dp = t then
        if s.dataConstraints.contains (x, r, d) then none
        else some (deterministic (s.addDataConstraint x r d) fun ⟨i, hm, env, hs⟩ =>
          ⟨i, hm, env, Branch.addDataConstraint_realizes hs fun y hy =>
            hs.dataConstraints x dp d hc y (h1 ▸ hm.subData (r, t) hrt (env x) y hy)⟩)
      else none) <|>
  (s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .conj a b =>
      if !s.known x a then some (add x a fun _ _ _ hs => (hs.labels x (.conj a b) h).1)
      else if !s.known x b then some (add x b fun _ _ _ hs => (hs.labels x (.conj a b) h).2)
      else none
    | .all r body =>
      nodes.findSome? fun y =>
        if he : s.edge r x y then
          if s.known y body then none
          else some (add y body fun _ env _ hs => hs.labels x (.all r body) h (env y) (Branch.edge_sound hs he))
        else none
    | _ => none) <|>
  (p.rules.attach.findSome? fun ⟨(r, t), h⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hs : s.edge r x y then
        if s.edge t x y then none
        else some (addEdge t x y fun _ env hm he => hm.rules (r, t) h (env x) (env y) (Branch.edge_sound he hs))
      else none) <|>
  (p.chains.attach.findSome? fun ⟨c, hc⟩ =>
    nodes.findSome? fun x =>
      (s.targets x c.body).attach.findSome? fun ⟨y, hy⟩ =>
        if s.edge (c.head, false) x y then none
        else some (addEdge (c.head, false) x y fun _ env hm hs =>
          hm.chains c hc (env x) (env y) (Branch.targets_sound hs hy))) <|>
  (nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if s.known x q.sup then none
    else if deferAbsorbed then
      if ht : isTriggered s x q.sub then
        some (add x q.sup fun _ env hm hs => hm.tbox q hq (env x) (isTriggered_sound hs ht))
      else none
    else if hp : (q.sub.triggeringPremises (s.known x) false).isSome then
      let support := (q.sub.triggeringPremises (s.known x) false).get hp
      some (add x q.sup fun i env hm hs => hm.tbox q hq (env x)
        (support.property.2 i (env x) fun c hc => Branch.known_sound hs (support.property.1 c hc)))
    else none) <|>
  (s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .disj a b =>
      if disjAlreadyKnownSmall s x a || disjAlreadyKnownSmall s x b then none
      else if ha : s.known x a.dual then
        some (add x b fun i env _ hs =>
          (hs.labels x (.disj a b) h).resolve_left ((holds_dual i (env x) a).mp (Branch.known_sound hs ha)))
      else if hb : s.known x b.dual then
        some (add x a fun i env _ hs =>
          (hs.labels x (.disj a b) h).resolve_right ((holds_dual i (env x) b).mp (Branch.known_sound hs hb)))
      else some (select x a b fun _ _ _ hs => hs.labels x (.disj a b) h)
    | _ => none) <|>
  (s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
    match c with
    | .max n r body =>
      let qualified := s.nodes.filter fun y => s.edge r x y && s.known y body
      if hn : n + 1 ≤ qualified.length then
        let ys := qualified.take (n + 1)
        some (mergeChoices h ys (List.length_take_of_le hn)
          ((List.take_sublist ..).nodup (List.filter_sublist.nodup s.nodes_nodup))
          (fun _ hy => Bool.and_eq_true_iff.mp ((List.mem_filter.mp (List.mem_of_mem_take hy)).2)))
      else none
    | _ => none) <|>
  (s.labels.attach.findSome? fun ⟨(x, c), h⟩ =>
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
    | _ => none) <|>
  (s.labels.findSome? fun (x, c) =>
    match c with
    | .max _ r body =>
      nodes.findSome? fun y =>
        if s.edge r x y && !(s.known y body || s.known y body.dual) then some (splitClass y body)
        else none
    | _ => none) <|>
  (nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if s.known x q.sup || s.known x q.sub.dual ||
        (deferAbsorbed && (q.sub.isDeferrable || q.sub.absorptionPremises.isSome || q.sub.nominalGuard?.isSome)) then none
    else some (select x q.sub.dual q.sup fun i env hm _ => by
      classical
      rcases Classical.em (holds i (env x) q.sub) with ha | ha
      · exact Or.inr (hm.tbox q hq (env x) ha)
      · exact Or.inl ((holds_dual i (env x) q.sub).mpr ha)))

private def isSpecialConcept : Concept → Bool
  | .nom _ _ | .self _ _ | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _ | .dataMin _ _ _ | .dataMax _ _ _ => true
  | _ => false

private def disjAlreadyKnownStore {labels : List (Nat × Concept)} (st : LabelStore labels) (x : Nat) :
    Concept → Bool
  | .disj a b => disjAlreadyKnownStore st x a || disjAlreadyKnownStore st x b
  | c => st.fastKnown x c

private structure DeltaCache (s : Branch) where
  labels : LabelStore s.labels
  eidx : EdgeIndex s.edges
  openDisjs : List (Nat × Concept × Concept)
  disjsByNode : Std.HashMap Nat (List (Concept × Concept))
  dirtyLabels : List (Nat × Concept)
  nodeCount : Nat

private def buildDeltaCache (s : Branch) (labels : LabelStore s.labels) (eidx : EdgeIndex s.edges)
    (nodeCount : Nat) : DeltaCache s := Id.run do
  let mut openDisjs : List (Nat × Concept × Concept) := []
  let mut disjsByNode : Std.HashMap Nat (List (Concept × Concept)) := {}
  for (x, c) in s.labels do
    match c with
    | .disj a b =>
      if !disjAlreadyKnownStore labels x a && !disjAlreadyKnownStore labels x b then
        openDisjs := (x, a, b) :: openDisjs
        disjsByNode := disjsByNode.insert x ((a, b) :: disjsByNode.getD x [])
    | _ => pure ()
  return { labels, eidx, openDisjs := openDisjs.reverse, disjsByNode, dirtyLabels := [], nodeCount }

private def isTriggeredDelta {s : Branch} (labels : LabelStore s.labels) (eidx : EdgeIndex s.edges)
    (x : Nat) : (c : Concept) →
    Option (PLift (∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      s.Realizes i env → holds i (env x) c))
  | .top => some ⟨fun _ _ _ => trivial⟩
  | .bottom => none
  | .lit a true => labels.knownProof x (.lit a true)
  | .nom a true => labels.knownProof x (.nom a true)
  | .self r true =>
    match labels.knownProof x (.self r true) with
    | some hp => some hp
    | none => (eidx.edgeProof r x x).map fun ⟨he⟩ => ⟨he⟩
  | .dataValue dp l true => labels.knownProof x (.dataValue dp l true)
  | .conj a b =>
    match isTriggeredDelta labels eidx x a, isTriggeredDelta labels eidx x b with
    | some ⟨ha⟩, some ⟨hb⟩ => some ⟨fun i env hs => ⟨ha i env hs, hb i env hs⟩⟩
    | _, _ => none
  | .disj a b =>
    match isTriggeredDelta labels eidx x a with
    | some ⟨ha⟩ => some ⟨fun i env hs => Or.inl (ha i env hs)⟩
    | none => (isTriggeredDelta labels eidx x b).map fun ⟨hb⟩ => ⟨fun i env hs => Or.inr (hb i env hs)⟩
  | .some r body =>
    labels.knownProof x (.some r body) <|>
    (eidx.adj r x).findSome? fun y =>
      match eidx.edgeProof r x y, isTriggeredDelta labels eidx y body with
      | some ⟨he⟩, some ⟨hb⟩ => some ⟨fun i env hs => ⟨env y, he i env hs, hb i env hs⟩⟩
      | _, _ => none
  | c => labels.knownProof x c

private theorem Branch.mem_add_of_mem {s : Branch} {x : Nat} {c : Concept} {xc : Nat × Concept}
    (h : xc ∈ s.labels) : xc ∈ (s.add x c).labels := by
  unfold Branch.add
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

private theorem Branch.mem_add_self {s : Branch} {x : Nat} {c : Concept} (hne : c ≠ .top) :
    (x, c) ∈ (s.add x c).labels := by
  unfold Branch.add
  split
  · rename_i hk
    cases c with
    | top => exact (hne rfl).elim
    | _ => exact List.contains_iff_mem.mp hk
  · exact List.mem_cons_self ..

private inductive DeltaStep (p : Problem) (s : Branch) where
  | closed (t : Transition p s)
  | pushed1 (t : Transition p s) (child : Branch) (added : List (Nat × Concept))
      (hBr : t.branches = [child])
      (hOld : ∀ xc ∈ s.labels, xc ∈ child.labels)
      (hAdded : ∀ xc ∈ added, xc ∈ child.labels)
      (hEdges : child.edges = s.edges)
      (openDisjs' : List (Nat × Concept × Concept))
  | pushed2 (t : Transition p s) (left right : Branch) (addedL addedR : List (Nat × Concept))
      (hBr : t.branches = [left, right])
      (hOldL : ∀ xc ∈ s.labels, xc ∈ left.labels)
      (hAddedL : ∀ xc ∈ addedL, xc ∈ left.labels)
      (hEdgesL : left.edges = s.edges)
      (hOldR : ∀ xc ∈ s.labels, xc ∈ right.labels)
      (hAddedR : ∀ xc ∈ addedR, xc ∈ right.labels)
      (hEdgesR : right.edges = s.edges)
      (openDisjs' : List (Nat × Concept × Concept))
  | fallback

private def addManyDelta {p : Problem} {s : Branch}
    (items : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 })
    (openDisjs' : List (Nat × Concept × Concept)) : DeltaStep p s :=
  .pushed1 (addMany items) { s with labels := items.map Subtype.val ++ s.labels }
    (items.map Subtype.val) rfl
    (fun _ hx => List.mem_append_right _ hx)
    (fun _ hx => List.mem_append_left _ hx)
    rfl openDisjs'

private def selectDelta {p : Problem} {s : Branch} (x : Nat) (a b : Concept)
    (ha : a ≠ .top) (hb : b ≠ .top)
    (h : ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env x) a ∨ holds i (env x) b)
    (openDisjs' : List (Nat × Concept × Concept)) : DeltaStep p s :=
  .pushed2 (select x a b h) (s.add x a) (s.add x b) [(x, a)] [(x, b)] rfl
    (fun _ hx => Branch.mem_add_of_mem hx)
    (fun _ hx => (List.mem_singleton.mp hx) ▸ Branch.mem_add_self ha)
    (Branch.add_edges_eq ..)
    (fun _ hx => Branch.mem_add_of_mem hx)
    (fun _ hx => (List.mem_singleton.mp hx) ▸ Branch.mem_add_self hb)
    (Branch.add_edges_eq ..)
    openDisjs'

private def popOpenDisj {labels : List (Nat × Concept)} (st : LabelStore labels) :
    List (Nat × Concept × Concept) →
    Option ((Nat × Concept × Concept) × List (Nat × Concept × Concept))
  | [] => none
  | (x, a, b) :: rest =>
    if disjAlreadyKnownStore st x a || disjAlreadyKnownStore st x b then
      popOpenDisj st rest
    else some ((x, a, b), rest)

private def nextDelta (p : Problem) (st : StaticIndex p) (s : Branch) (cache : DeltaCache s) :
    DeltaStep p s := Id.run do
  -- D1: labelClash on newly added dirty labels
  for (x, c) in cache.dirtyLabels do
    if hc : c = .bottom then
      if let some ⟨hmem⟩ := cache.labels.mem? (x, c) then
        return .closed (close fun ⟨_, _, _, hs⟩ => by have h := hs.labels x c hmem; rw [hc] at h; exact h)
    else
      if let some ⟨hd⟩ := cache.labels.knownProof x c.dual then
        if let some ⟨hmem⟩ := cache.labels.mem? (x, c) then
          return .closed (close fun ⟨i, _, env, hs⟩ =>
            (holds_dual i (env x) c).mp (hd i env hs) (hs.labels x c hmem))
  -- D2: localLabels on dirty labels
  let mut added : Std.HashSet (Nat × Concept) := {}
  let mut localItems : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  for (x, c) in cache.dirtyLabels do
    match hc : c with
    | .conj a b =>
      if let some ⟨hmem⟩ := cache.labels.mem? (x, c) then
        for ⟨d, hd⟩ in collectConjLeaves (.conj a b) do
          if !cache.labels.fastKnown x d && !added.contains (x, d) then
            added := added.insert (x, d)
            localItems := ⟨(x, d), fun i env _ hs => hd i (env x) (hs.labels x (.conj a b) (hc ▸ hmem))⟩ :: localItems
    | .all r body =>
      if let some ⟨hmem⟩ := cache.labels.mem? (x, c) then
        for y in cache.eidx.adj r x do
          if !cache.labels.fastKnown y body && !added.contains (y, body) then
            if let some ⟨he⟩ := cache.eidx.edgeProof r x y then
              added := added.insert (y, body)
              localItems := ⟨(y, body), fun i env _ hs => hs.labels x (.all r body) (hc ▸ hmem) (env y) (he i env hs)⟩ :: localItems
    | _ => pure ()
  if !localItems.isEmpty then
    return addManyDelta localItems cache.openDisjs
  -- D3: deterministicGCI on dirty labels & incoming role neighbors
  let mut dirtyNodeSet : Std.HashSet Nat := {}
  let mut dirtyNodes : Array Nat := #[]
  for (x, _) in cache.dirtyLabels do
    if !dirtyNodeSet.contains x then
      dirtyNodeSet := dirtyNodeSet.insert x
      dirtyNodes := dirtyNodes.push x
  let mut gciAdded : Std.HashSet (Nat × Concept) := {}
  let mut gciItems : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  for (x, c) in cache.dirtyLabels do
    match c with
    | .lit cls true =>
      for ⟨q, hq⟩ in st.classGCIs.getD cls [] do
        if !cache.labels.fastKnown x q.sup && !gciAdded.contains (x, q.sup) then
          if let some ⟨ht⟩ := isTriggeredDelta cache.labels cache.eidx x q.sub then
            gciAdded := gciAdded.insert (x, q.sup)
            gciItems := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: gciItems
    | .some r _ =>
      for ⟨q, hq⟩ in st.roleGCIs.getD r [] do
        if !cache.labels.fastKnown x q.sup && !gciAdded.contains (x, q.sup) then
          if let some ⟨ht⟩ := isTriggeredDelta cache.labels cache.eidx x q.sub then
            gciAdded := gciAdded.insert (x, q.sup)
            gciItems := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: gciItems
    | _ => pure ()
  for y in dirtyNodes do
    for (r, x) in cache.eidx.inEdgesByTarget.getD y [] do
      for ⟨q, hq⟩ in st.roleGCIs.getD r [] do
        if !cache.labels.fastKnown x q.sup && !gciAdded.contains (x, q.sup) then
          if let some ⟨ht⟩ := isTriggeredDelta cache.labels cache.eidx x q.sub then
            gciAdded := gciAdded.insert (x, q.sup)
            gciItems := ⟨(x, q.sup), fun i env hm hs => hm.tbox q hq (env x) (ht i env hs)⟩ :: gciItems
    for ⟨q, hq⟩ in st.unanchoredGCIs do
      if !cache.labels.fastKnown y q.sup && !gciAdded.contains (y, q.sup) then
        if let some ⟨ht⟩ := isTriggeredDelta cache.labels cache.eidx y q.sub then
          gciAdded := gciAdded.insert (y, q.sup)
          gciItems := ⟨(y, q.sup), fun i env hm hs => hm.tbox q hq (env y) (ht i env hs)⟩ :: gciItems
  if !gciItems.isEmpty then
    return addManyDelta gciItems cache.openDisjs
  -- D4: unit propagation on dirtyNodes' disjunctions only
  let mut unitAdded : Std.HashSet (Nat × Concept) := {}
  let mut unitItems : List { xc : Nat × Concept // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
      p.Models i → s.Realizes i env → holds i (env xc.1) xc.2 } := []
  let refutesLit (x : Nat) (cls : IRI) :
      Option { _u : Unit // ∀ (i : Interpretation datatypeMap) (env : Nat → i.Object),
        p.Models i → s.Realizes i env → ¬ holds i (env x) (.lit cls true) } :=
    (st.disjMap.getD cls []).findSome? fun ⟨(other, q), hq⟩ =>
      match cache.labels.knownProof x (.lit other true) with
      | some ⟨hkn⟩ =>
        if hsup : q.sup = .bottom then
          if hsub1 : q.sub = .conj (.lit cls true) (.lit other true) then
            some ⟨(), fun i env hm hs hcls => by
              have hbot := hm.tbox q hq (env x) (hsub1 ▸ ⟨hcls, hkn i env hs⟩)
              rw [hsup] at hbot; exact hbot⟩
          else if hsub2 : q.sub = .conj (.lit other true) (.lit cls true) then
            some ⟨(), fun i env hm hs hcls => by
              have hbot := hm.tbox q hq (env x) (hsub2 ▸ ⟨hkn i env hs, hcls⟩)
              rw [hsup] at hbot; exact hbot⟩
          else none
        else none
      | none => none
  for x in dirtyNodes do
    for (a, b) in cache.disjsByNode.getD x [] do
      if disjAlreadyKnownStore cache.labels x a || disjAlreadyKnownStore cache.labels x b then continue
      let some ⟨hmem⟩ := cache.labels.mem? (x, .disj a b) | continue
      match cache.labels.knownProof x a.dual with
      | some ⟨ha⟩ =>
        if !unitAdded.contains (x, b) then
          unitAdded := unitAdded.insert (x, b)
          unitItems := ⟨(x, b), fun i env _ hs =>
            (hs.labels x (.disj a b) hmem).resolve_left
              ((holds_dual i (env x) a).mp (ha i env hs))⟩ :: unitItems
      | none =>
        match cache.labels.knownProof x b.dual with
        | some ⟨hb⟩ =>
          if !unitAdded.contains (x, a) then
            unitAdded := unitAdded.insert (x, a)
            unitItems := ⟨(x, a), fun i env _ hs =>
              (hs.labels x (.disj a b) hmem).resolve_right
                ((holds_dual i (env x) b).mp (hb i env hs))⟩ :: unitItems
        | none =>
          match haLit : a, hbLit : b with
          | .lit clsA true, _ =>
            if let some ⟨_, hnotA⟩ := refutesLit x clsA then
              if !unitAdded.contains (x, b) then
                unitAdded := unitAdded.insert (x, b)
                unitItems := ⟨(x, b), fun i env hm hs =>
                  (hs.labels x (.disj a b) hmem).resolve_left (haLit ▸ hnotA i env hm hs)⟩ :: unitItems
            else match hbLit2 : b with
            | .lit clsB true =>
              if let some ⟨_, hnotB⟩ := refutesLit x clsB then
                if !unitAdded.contains (x, a) then
                  unitAdded := unitAdded.insert (x, a)
                  unitItems := ⟨(x, a), fun i env hm hs =>
                    (hs.labels x (.disj a b) hmem).resolve_right (hbLit2 ▸ hnotB i env hm hs)⟩ :: unitItems
            | _ => pure ()
          | _, .lit clsB true =>
            if let some ⟨_, hnotB⟩ := refutesLit x clsB then
              if !unitAdded.contains (x, a) then
                unitAdded := unitAdded.insert (x, a)
                unitItems := ⟨(x, a), fun i env hm hs =>
                  (hs.labels x (.disj a b) hmem).resolve_right (hbLit ▸ hnotB i env hm hs)⟩ :: unitItems
          | _, _ => pure ()
  if !unitItems.isEmpty then
    return addManyDelta unitItems cache.openDisjs
  -- D5: pop the next unresolved disjunction and split
  match popOpenDisj cache.labels cache.openDisjs with
  | some ((x, a, b), rest) =>
    if ha : a ≠ .top then
      if hb : b ≠ .top then
        if let some ⟨hmem⟩ := cache.labels.mem? (x, .disj a b) then
          return selectDelta x a b ha hb (fun _ _ _ hs => hs.labels x (.disj a b) hmem) rest
    return .fallback
  | none => return .fallback

private inductive NextStep (p : Problem) (s : Branch) where
  | sameEdges (t : Transition p s) (he : ∀ b ∈ t.branches, b.edges = s.edges)
      (eidx : EdgeIndex s.edges) (edgesSat : Bool) (nodeCount : Nat)
  | enterDelta (cache : DeltaCache s) (step : DeltaStep p s)
  | changedEdges (t : Transition p s) (nodeCount : Nat)
  | done (nodeCount : Nat)

private def nextWith (p : Problem) (st : StaticIndex p) (s : Branch) (maxNodes : Nat)
    (deferAbsorbed : Bool := false) (edgeCache : Option (EdgeIndex s.edges × Bool) := none) :
    NextStep p s :=
  let (eidx, edgesSat) := match edgeCache with
    | some pair => pair
    | none => (buildEdgeIndex s.edges, false)
  let idx := buildBranchIndexWith s (some eidx)
  let nodeCount := idx.nodes.length
  match inequalityClash p s <|> labelClash p s idx <|> negEdgeClash p s idx <|> dataClashIndexed p s idx <|>
        nominalMergeIndexed p s idx <|> keyMergeIndexed p s idx <|>
        (if idx.hasSelfLabel then selfSteps p s else none) with
  | some t => .changedEdges t nodeCount
  | none =>
    match (if !edgesSat then roleCharSteps p s idx else none) <|> dataSteps p s idx with
    | some t => .changedEdges t nodeCount
    | none =>
      match localLabels p s idx with
      | some ⟨t, he⟩ => .sameEdges t he eidx edgesSat nodeCount
      | none =>
        match (if !edgesSat then hierarchy p s idx <|> chains p s idx else none) with
        | some t => .changedEdges t nodeCount
        | none =>
          match deterministicGCI p st s idx deferAbsorbed with
          | some ⟨t, he⟩ => .sameEdges t he eidx true nodeCount
          | none =>
            match disjunctions p st s idx with
            | some ⟨t, he⟩ =>
              if t.branches.length == 2 then
                let dcache := buildDeltaCache s idx.labels eidx nodeCount
                match nextDelta p st s dcache with
                | .fallback => .sameEdges t he eidx true nodeCount
                | ds => .enterDelta dcache ds
              else
                .sameEdges t he eidx true nodeCount
            | none =>
              match upperBounds p s idx <|> witnesses p s idx maxNodes with
              | some t => .changedEdges t nodeCount
              | none =>
                match qualifiers p s idx <|> undecidedGCI p s idx deferAbsorbed with
                | some ⟨t, he⟩ => .sameEdges t he eidx true nodeCount
                | none => .done nodeCount

def next (p : Problem) (s : Branch) (maxNodes : Nat) (deferAbsorbed : Bool := false) :
    Option (Transition p s) :=
  if s.labels.length ≤ 16 && p.tbox.length ≤ 16 && s.edges.length ≤ 16 &&
     p.rules.length ≤ 16 && p.chains.length ≤ 16 then
    nextSmall p s maxNodes deferAbsorbed
  else
    match nextWith p (buildStaticIndex p) s maxNodes deferAbsorbed none with
    | .sameEdges t .. | .changedEdges t .. => some t
    | .enterDelta _ (.closed t) | .enterDelta _ (.pushed1 t ..) | .enterDelta _ (.pushed2 t ..) => some t
    | .enterDelta _ .fallback | .done _ => none

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

private def completeDataEdges {n : Nat} (p : Problem) (s : Branch)
    (index : Nat → Option (Fin n)) :
    List (IRI × Fin n × Value) := Id.run do
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
  let nodes := (buildBranchIndex s).nodes
  let additional := nodes.length - 1
  let nodeIdxMap : Std.HashMap Nat (Fin (additional + 1)) := Id.run do
    let mut m : Std.HashMap Nat (Fin (additional + 1)) := {}
    let mut k := 0
    for a in nodes do
      if h : k < additional + 1 then
        m := m.insert a ⟨k, h⟩
      k := k + 1
    return m
  let index := fun a => nodeIdxMap[a]?
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
  let idx := buildBranchIndex s
  if idx.nodes.length > 256 then []
  else
    let pairRedirs := idx.nodes.filterMap fun y => (pairwiseBlocker s y).map (y, ·)
    let leafRedirs := idx.nodes.filterMap fun y =>
      if s.edges.any (fun (_, a, b) => a == y && b > y) then none
      else (subsetBlocker s y).map (y, ·)
    ([buildQuotientModel p s pairRedirs, buildQuotientModel p s leafRedirs]).filterMap id

structure Limits where
  worlds : Nat := 16
  depth : Nat := 256
  visits : Nat := 20000

/-- Convert the default allowance for additional live worlds into the absolute
    cap used by search and certificate replay. Initialization assigns a world
    to the query root and to each named and anonymous individual; scale
    witness/depth/visit budgets proportionally so larger ABoxes do not stall
    before existential witnesses on named individuals are allocated. -/
def Limits.forProblem (p : Problem) (extra : Limits := {}) : Limits :=
  let nInds := 1 + p.nominals.length + p.anons.length
  { worlds := nInds + max extra.worlds (nInds * 2 + 64)
    depth := max extra.depth (nInds * 4 + 512)
    visits := max extra.visits (nInds * 16 + 20000) }

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

private def explainLocalLabel (p : Problem) (st : StaticIndex p) (s : Branch) (x : Nat) (c : Concept) :
    Option (LocalLabelRule p) :=
  (s.labels.findSome? fun (y, label) =>
    if x != y then none
    else match label with
    | .conj a b =>
      (collectConjLeaves (.conj a b)).findSome? fun ⟨d, hd⟩ =>
        if h : c = d then
          some (.unary x [.conj a b] c fun i _ z hp =>
            h.symm ▸ hd i z (hp (.conj a b) (by simp)))
        else none
    | .disj a b =>
      if h : c = b ∧ s.known x a.dual = true then
        some (.unary x [.disj a b, a.dual] c fun i _ z hp => h.1.symm ▸
          (hp (.disj a b) (by simp)).resolve_left ((holds_dual i z a).mp (hp a.dual (by simp))))
      else if h : c = a ∧ s.known x b.dual = true then
        some (.unary x [.disj a b, b.dual] c fun i _ z hp => h.1.symm ▸
          (hp (.disj a b) (by simp)).resolve_right ((holds_dual i z b).mp (hp b.dual (by simp))))
      else if hcb : c = b then
        match haLit : a with
        | .lit clsA true =>
          (st.disjMap.getD clsA []).findSome? fun ⟨(other, q), hq⟩ =>
            if s.known x (.lit other true) then
              if hsup : q.sup = .bottom then
                if hsub1 : q.sub = .conj (.lit clsA true) (.lit other true) then
                  some (.unary x [.disj a b, .lit other true] c fun i hm z hp => by
                    rw [hcb]
                    refine (hp (.disj a b) (by simp)).resolve_left fun ha => ?_
                    rw [haLit] at ha
                    have hbot := hm.tbox q hq z (hsub1 ▸ ⟨ha, hp (.lit other true) (by simp)⟩)
                    rw [hsup] at hbot; exact hbot)
                else if hsub2 : q.sub = .conj (.lit other true) (.lit clsA true) then
                  some (.unary x [.disj a b, .lit other true] c fun i hm z hp => by
                    rw [hcb]
                    refine (hp (.disj a b) (by simp)).resolve_left fun ha => ?_
                    rw [haLit] at ha
                    have hbot := hm.tbox q hq z (hsub2 ▸ ⟨hp (.lit other true) (by simp), ha⟩)
                    rw [hsup] at hbot; exact hbot)
                else none
              else none
            else none
        | _ => none
      else if hca : c = a then
        match hbLit : b with
        | .lit clsB true =>
          (st.disjMap.getD clsB []).findSome? fun ⟨(other, q), hq⟩ =>
            if s.known x (.lit other true) then
              if hsup : q.sup = .bottom then
                if hsub1 : q.sub = .conj (.lit clsB true) (.lit other true) then
                  some (.unary x [.disj a b, .lit other true] c fun i hm z hp => by
                    rw [hca]
                    refine (hp (.disj a b) (by simp)).resolve_right fun hb => ?_
                    rw [hbLit] at hb
                    have hbot := hm.tbox q hq z (hsub1 ▸ ⟨hb, hp (.lit other true) (by simp)⟩)
                    rw [hsup] at hbot; exact hbot)
                else if hsub2 : q.sub = .conj (.lit other true) (.lit clsB true) then
                  some (.unary x [.disj a b, .lit other true] c fun i hm z hp => by
                    rw [hca]
                    refine (hp (.disj a b) (by simp)).resolve_right fun hb => ?_
                    rw [hbLit] at hb
                    have hbot := hm.tbox q hq z (hsub2 ▸ ⟨hp (.lit other true) (by simp), hb⟩)
                    rw [hsup] at hbot; exact hbot)
                else none
              else none
            else none
        | _ => none
      else none
    | _ => none) <|>
  ((st.tboxBySup.getD c []).findSome? fun ⟨q, hq⟩ =>
    if h : c = q.sup then
      match q.sub.triggeringPremises (s.known x) with
      | some support =>
        some (.unary x support.val c fun i hm z hp => h.symm ▸ hm.tbox q hq z (support.property.2 i z hp))
      | none =>
        match hng : q.sub.nominalGuard? with
        | none => none
        | some (inds, rest) =>
          inds.attach.findSome? fun ⟨a, ha⟩ =>
            if s.known x (.nom a true) then
              if htop : rest = .top then
                some (.unary x [.nom a true] c fun i hm z hp =>
                  h.symm ▸ hm.tbox q hq z
                    (Concept.nominalGuard?_sound hng i z ha (hp (.nom a true) (by simp)) (htop ▸ trivial)))
              else if s.known x rest then
                some (.unary x [.nom a true, rest] c fun i hm z hp =>
                  h.symm ▸ hm.tbox q hq z
                    (Concept.nominalGuard?_sound hng i z ha
                      (hp (.nom a true) (by simp)) (hp rest (by simp))))
              else match rest.triggeringPremises (s.known x) with
              | some supR =>
                some (.unary x (.nom a true :: supR.val) c fun i hm z hp =>
                  h.symm ▸ hm.tbox q hq z
                    (Concept.nominalGuard?_sound hng i z ha
                      (hp (.nom a true) (List.mem_cons_self ..))
                      (supR.property.2 i z fun d hd => hp d (List.mem_cons_of_mem _ hd))))
              | none => none
            else none
    else none)

private def explainLocalChoice (p : Problem) (s : Branch) (x : Nat) (a b : Concept) :
    Option (LocalLabelRule p) :=
  if b == a.dual then some (.split p x a)
  else if s.known x (.disj a b) then
    some (.binary x [.disj a b] a b fun _ _ _ hp => hp (.disj a b) (by simp))
  else p.tbox.attach.findSome? fun ⟨q, hq⟩ =>
    if q.sub.dual == a && q.sup == b then some (.gci x q hq)
    else
      match hng : q.sub.nominalGuard? with
      | some (inds, rest) =>
        if haEq : rest.dual = a then
          if hbEq : q.sup = b then
            inds.attach.findSome? fun ⟨ind, hind⟩ =>
              if s.known x (.nom ind true) then
                some (.binary x [.nom ind true] a b fun i hm z hp => by
                  subst haEq; subst hbEq
                  classical
                  rcases Classical.em (holds i z rest) with hr | hr
                  · exact Or.inr (hm.tbox q hq z
                      (Concept.nominalGuard?_sound hng i z hind (hp (.nom ind true) (by simp)) hr))
                  · exact Or.inl ((holds_dual i z rest).mpr hr))
              else none
          else none
        else none
      | none => none

/-- Resolve a `NodeClash` backward through all labels newly introduced at the head of a
    single (possibly batched) child branch. Every label in a batched `addMany` transition
    is derived directly from `s`, so resolving against each newly added premise on
    `clash.node` preserves full dependency-directed backjumping through batched steps. -/
private def resolveBatchClash {p : Problem} (st : StaticIndex p) (s child : Branch) (clash : NodeClash p) :
    Option (NodeClash p) := Id.run do
  let addedCount := child.labels.length - s.labels.length
  let newLabels := child.labels.take addedCount
  let mut cur := clash
  let mut resolvedAny := false
  for (x, c) in newLabels do
    if x == cur.node && !s.known x c && cur.premises.contains c then
      match explainLocalLabel p st s cur.node c with
      | some rule =>
        match rule.resolve [some cur] with
        | some nextClash =>
          cur := nextClash
          resolvedAny := true
        | none => return none
      | none => return none
  if resolvedAny then return some cur else return none

/-- Explain closures when the conflict contains labels newly introduced at the head of
    the child branch (including batched `addMany` transitions). More involved transitions
    keep their ordinary refutation without a reusable dependency set. -/
private def probeClash {p : Problem} (st : StaticIndex p) (s : Branch) (children : List Branch)
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
    resolveBatchClash st s child clash
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

private def probeBranches {p : Problem} (s : Branch) :
    (xs : List Branch) →
    ((b : Branch) → b ∈ xs → Option Nat → ProbeVerdict p b × Option Nat) →
    Option Nat → ProbeBranches p s xs × Option Nat
  | [], _, fuel => (.closed 0 [] (fun _ h => nomatch h), fuel)
  | b :: bs, visit, fuel =>
    let (answer, fuel) := visit b (List.mem_cons_self ..) fuel
    match answer with
    | .model m => (.model m, fuel)
    | .closed depth clue refutes =>
      if let some jump := clue.bind (provedClash s) then
        (.jump depth jump, fuel)
      else
        let (tail, fuel) := probeBranches s bs (fun b' hb' f => visit b' (List.mem_cons_of_mem _ hb') f) fuel
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
        let (tail, fuel) := probeBranches s bs (fun b' hb' f => visit b' (List.mem_cons_of_mem _ hb') f) fuel
        match tail with
        | .model m => (.model m, fuel)
        | .jump d jump => (.jump d jump, fuel)
        | .closed .. | .unknown => (.unknown, fuel)

private def isTriggeredCanon (labelSet : Std.HashSet (Nat × Concept))
    (outAdj inAdj : Std.HashMap (IRI × Nat) (List Nat))
    (edgeSet : Std.HashSet (IRI × Nat × Nat))
    (dataByPropNode : Std.HashMap (IRI × Nat) (List Value))
    (x : Nat) : Concept → Bool
  | .top => true
  | .bottom => false
  | .lit a true => labelSet.contains (x, .lit a true)
  | .nom a true => labelSet.contains (x, .nom a true)
  | .self r true =>
    labelSet.contains (x, .self r true) ||
    (if r.2 then edgeSet.contains (r.1, x, x) else edgeSet.contains (r.1, x, x))
  | .dataValue dp l true => labelSet.contains (x, .dataValue dp l true)
  | .conj a b =>
    isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x a &&
    isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x b
  | .disj a b =>
    isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x a ||
    isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x b
  | .some r body =>
    labelSet.contains (x, .some r body) ||
    (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []).any fun y =>
      isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode y body
  | .dataSome dp d =>
    labelSet.contains (x, .dataSome dp d) ||
    (dataByPropNode.getD (dp, x) []).any fun v =>
      d == .datatype literalDatatype ||
      match compile d with | some comp => comp.holds v | none => false
  | c => labelSet.contains (x, c)

private def walkCanonTargets (outAdj inAdj : Std.HashMap (IRI × Nat) (List Nat))
    (x : Nat) : List OrientedRole → List Nat
  | [] => [x]
  | r :: rs =>
    (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []).flatMap fun y =>
      walkCanonTargets outAdj inAdj y rs

private def disjKnownCanon (labelSet : Std.HashSet (Nat × Concept)) (x : Nat) : Concept → Bool
  | .disj a b => disjKnownCanon labelSet x a || disjKnownCanon labelSet x b
  | .top => true
  | c => labelSet.contains (x, c)

/-- Precompute told class ancestors `A ⊑* B` from `p.tbox` for inherited disjointness
    lookahead inside `tryCanonicalModel`. -/
private def buildClassAncestors (p : Problem) : Std.HashMap IRI (List IRI) := Id.run do
  let mut direct : Std.HashMap IRI (List IRI) := {}
  for q in p.tbox do
    match q.sub, q.sup with
    | .lit a true, .lit b true =>
      direct := direct.insert a (b :: direct.getD a [])
    | .lit a true, .conj b c =>
      for ⟨d, _⟩ in collectConjLeaves (.conj b c) do
        match d with
        | .lit b' true => direct := direct.insert a (b' :: direct.getD a [])
        | _ => pure ()
    | _, _ => pure ()
  let mut anc : Std.HashMap IRI (List IRI) := {}
  for (root, _) in direct do
    let mut visited : Std.HashSet IRI := {}
    let mut stack : List IRI := [root]
    let mut out : List IRI := []
    while !stack.isEmpty do
      match stack with
      | [] => break
      | cur :: rest =>
        stack := rest
        if !visited.contains cur then
          visited := visited.insert cur
          out := cur :: out
          for sup in direct.getD cur [] do
            if !visited.contains sup then stack := sup :: stack
    anc := anc.insert root out
  return anc

private def hasNegOrAll : Concept → Bool
  | .lit _ false | .nom _ false | .all .. | .max .. | .self _ false
  | .dataAll .. | .dataMax .. | .dataValue _ _ false => true
  | .conj a b | .disj a b => hasNegOrAll a || hasNegOrAll b
  | .some _ b | .min _ _ b => hasNegOrAll b
  | _ => false

private partial def holdsInCanonState
    (lSet : Std.HashSet (Nat × Concept))
    (oAdj iAdj : Std.HashMap (IRI × Nat) (List Nat))
    (eSet : Std.HashSet (IRI × Nat × Nat))
    (dByPN : Std.HashMap (IRI × Nat) (List Value))
    (x : Nat) : Concept → Bool
  | .top => true
  | .bottom => false
  | .lit cls true => lSet.contains (x, .lit cls true)
  | .lit cls false => !lSet.contains (x, .lit cls true)
  | .nom ind true => lSet.contains (x, .nom ind true)
  | .nom ind false => !lSet.contains (x, .nom ind true)
  | .self r true => eSet.contains (r.1, x, x)
  | .self r false => !eSet.contains (r.1, x, x)
  | .conj a b =>
    holdsInCanonState lSet oAdj iAdj eSet dByPN x a &&
    holdsInCanonState lSet oAdj iAdj eSet dByPN x b
  | .disj a b =>
    holdsInCanonState lSet oAdj iAdj eSet dByPN x a ||
    holdsInCanonState lSet oAdj iAdj eSet dByPN x b
  | .some r body =>
    (if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []).any fun y =>
      holdsInCanonState lSet oAdj iAdj eSet dByPN y body
  | .all r body =>
    (if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []).all fun y =>
      holdsInCanonState lSet oAdj iAdj eSet dByPN y body
  | .min n r body =>
    ((if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []).filter fun y =>
      holdsInCanonState lSet oAdj iAdj eSet dByPN y body).length ≥ n
  | .max n r body =>
    ((if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []).filter fun y =>
      holdsInCanonState lSet oAdj iAdj eSet dByPN y body).length ≤ n
  | c => isTriggeredCanon lSet oAdj iAdj eSet dByPN x c

/-- Single attempt of untrusted canonical-witness-reuse finite model proposal,
    respecting `banned` disjunction choices from earlier conflict-driven attempts.
    Returns `.ok m` if `checkModel p m = true`, or `.error newlyBanned` on clash. -/
private def tryCanonicalModelAttempt (p : Problem) (st : StaticIndex p)
    (ancestors : Std.HashMap IRI (List IRI)) (s : Branch)
    (banned : Std.HashSet (Nat × Concept)) :
    Except (List (Nat × Concept)) {m : SROIQDModel // checkModel p m = true} := Id.run do
  -- Identify roles whose superproperties have an inverse upper-bound restriction
  -- (cannot share one witness across distinct sources) or forward functional restriction
  -- (must reuse an existing filler on the same source rather than creating a second one).
  let mut invFuncRoles : Std.HashSet OrientedRole := {}
  let mut funcSuper : Std.HashMap OrientedRole (List OrientedRole) := {}
  let mut funcRoles : Std.HashSet OrientedRole := {}
  let negLHSGCIs := p.tbox.filter fun q => hasNegOrAll q.sub
  for q in p.tbox do
    for ⟨d, _⟩ in collectConjLeaves q.sup do
      match d with
      | .max _ r _ =>
        invFuncRoles := invFuncRoles.insert (r.1, !r.2)
        funcRoles := funcRoles.insert r
        funcSuper := funcSuper.insert r (r :: funcSuper.getD r [])
      | _ => pure ()
  -- Close `invFuncRoles` and `funcRoles` backward along `p.rules` (if `s ⊑ t` and `t` is bounded, `s` is too)
  let mut rfChanged := true
  let mut rfIter := 0
  while rfChanged && rfIter < p.rules.length + 2 do
    rfChanged := false
    rfIter := rfIter + 1
    for (r, t) in p.rules do
      if invFuncRoles.contains t && !invFuncRoles.contains r then
        invFuncRoles := invFuncRoles.insert r
        rfChanged := true
      let tFlip : OrientedRole := (t.1, !t.2)
      let rFlip : OrientedRole := (r.1, !r.2)
      if invFuncRoles.contains tFlip && !invFuncRoles.contains rFlip then
        invFuncRoles := invFuncRoles.insert rFlip
        rfChanged := true
      if funcRoles.contains t then
        if !funcRoles.contains r then
          funcRoles := funcRoles.insert r
          rfChanged := true
        for fs in funcSuper.getD t [] do
          if !(funcSuper.getD r []).contains fs then
            funcSuper := funcSuper.insert r (fs :: funcSuper.getD r [])
            rfChanged := true
      if funcRoles.contains tFlip then
        if !funcRoles.contains rFlip then
          funcRoles := funcRoles.insert rFlip
          rfChanged := true
        for fs in funcSuper.getD tFlip [] do
          if !(funcSuper.getD rFlip []).contains fs then
            funcSuper := funcSuper.insert rFlip (fs :: funcSuper.getD rFlip [])
            rfChanged := true
  let mut irreflAsym : Std.HashSet IRI := {}
  for r in p.chars.irreflexive do irreflAsym := irreflAsym.insert r
  for r in p.chars.asymmetric do irreflAsym := irreflAsym.insert r
  -- Initialize mutable canonical state from `s`
  let mut nodeSet : Std.HashSet Nat := {}
  let mut nodes : Array Nat := #[]
  let mut maxNode : Nat := 0
  let mut labelSet : Std.HashSet (Nat × Concept) := {}
  let mut labelsByNode : Std.HashMap Nat (List Concept) := {}
  let mut classNodes : Std.HashMap IRI (List Nat) := {}
  let mut nomNodes : Std.HashMap (String × String) (List Nat) := {}
  let mut someLabels : Array (Nat × OrientedRole × Concept) := #[]
  let mut minLabels : Array (Nat × Nat × OrientedRole × Concept) := #[]
  let mut allLabels : Std.HashMap (OrientedRole × Nat) (List Concept) := {}
  let mut disjLabels : Array (Nat × Concept × Concept) := #[]
  let mut edgeSet : Std.HashSet (IRI × Nat × Nat) := {}
  let mut outAdj : Std.HashMap (IRI × Nat) (List Nat) := {}
  let mut inAdj : Std.HashMap (IRI × Nat) (List Nat) := {}
  let mut edgesByRole : Std.HashMap IRI (List (Nat × Nat)) := {}
  let mut roleSources : Std.HashMap OrientedRole (List Nat) := {}
  let mut dataByPropNode : Std.HashMap (IRI × Nat) (List Value) := {}
  let mut dataTouchNodes : Std.HashMap IRI (List Nat) := {}
  let mut dataEdges := s.dataEdges
  let mut negDataEdges := s.negDataEdges
  let mut dataConstraints := s.dataConstraints
  let mut dataConstraintSet : Std.HashSet (Nat × IRI × DataRange) := {}
  for dc in s.dataConstraints do dataConstraintSet := dataConstraintSet.insert dc
  for (dp, x, v) in s.dataEdges do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
    dataByPropNode := dataByPropNode.insert (dp, x) (v :: dataByPropNode.getD (dp, x) [])
    dataTouchNodes := dataTouchNodes.insert dp (x :: dataTouchNodes.getD dp [])
  for (_, x) in s.noms do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
  for (_, x) in s.anons do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
  for (x, y) in s.unequal do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; nodes := nodes.push y; if y > maxNode then maxNode := y
  for (_, x, y) in s.negEdges do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; nodes := nodes.push y; if y > maxNode then maxNode := y
  for (r, x, y) in s.edges do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
    if !nodeSet.contains y then nodeSet := nodeSet.insert y; nodes := nodes.push y; if y > maxNode then maxNode := y
    if !edgeSet.contains (r, x, y) then
      edgeSet := edgeSet.insert (r, x, y)
      outAdj := outAdj.insert (r, x) (y :: outAdj.getD (r, x) [])
      inAdj := inAdj.insert (r, y) (x :: inAdj.getD (r, y) [])
      edgesByRole := edgesByRole.insert r ((x, y) :: edgesByRole.getD r [])
      roleSources := roleSources.insert (r, false) (x :: roleSources.getD (r, false) [])
      roleSources := roleSources.insert (r, true) (y :: roleSources.getD (r, true) [])
  let mut pendingLabels : Array (Nat × Concept) := #[]
  for (x, c) in s.labels do
    if !nodeSet.contains x then nodeSet := nodeSet.insert x; nodes := nodes.push x; if x > maxNode then maxNode := x
    pendingLabels := pendingLabels.push (x, c)
  let mut nextNode := maxNode + 1
  let origNodes := nodes.size
  let maxNewNodes := max 512 (origNodes * 4)
  let mut canonWit1 : Std.HashMap (OrientedRole × Concept × List Concept) Nat := {}
  let mut canonWit2 : Std.HashMap (OrientedRole × Concept × List Concept) Nat := {}
  let mut nodeChoices : Std.HashMap Nat (List Concept) := {}
  let mut clashNodes : Std.HashSet Nat := {}
  let mut clashed := false
  let mut edgesChanged := true
  let mut labelsChanged := true
  let rec flattenDisj : Concept → List Concept
    | .disj a b => flattenDisj a ++ flattenDisj b
    | .bottom => []
    | c => [c]
  -- Helper: check if adding `cand` to node `x` causes an immediate local contradiction
  -- (including superclass closure, `isTriggeredCanon` GCIs, inherited binary disjointness, and unit propagation)
  let localSafe (lSet : Std.HashSet (Nat × Concept)) (lByNode : Std.HashMap Nat (List Concept))
      (oAdj iAdj : Std.HashMap (IRI × Nat) (List Nat)) (eSet : Std.HashSet (IRI × Nat × Nat))
      (dByPN : Std.HashMap (IRI × Nat) (List Value))
      (x : Nat) (cand : Concept) : Bool := Id.run do
    if banned.contains (x, cand) then return false
    let mut loc : Std.HashSet Concept := {}
    let mut nodeDisjs : List (Concept × Concept) := []
    for c in lByNode.getD x [] do
      loc := loc.insert c
      match c with
      | .disj a b => nodeDisjs := (a, b) :: nodeDisjs
      | _ => pure ()
    let rec trigLoc (locSet : Std.HashSet Concept) : Concept → Bool
      | .top => true
      | .bottom => false
      | .conj a b => trigLoc locSet a && trigLoc locSet b
      | .disj a b => trigLoc locSet a || trigLoc locSet b
      | .some r body =>
        locSet.contains (.some r body) ||
        (if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []).any fun y =>
          isTriggeredCanon lSet oAdj iAdj eSet dByPN y body
      | c => locSet.contains c
    let refuted (locSet : Std.HashSet Concept) : Concept → Bool
      | .bottom => true
      | .lit cls true =>
        let ancs := ancestors.getD cls [cls]
        ancs.any fun a =>
          locSet.contains (.lit a false) ||
          (st.disjMap.getD a []).any fun ⟨(other, _), _⟩ => locSet.contains (.lit other true)
      | c => locSet.contains c.dual
    let mut work : List Concept := [cand]
    let mut steps := 0
    while !work.isEmpty && steps < 64 do
      steps := steps + 1
      let mut nextWork : List Concept := []
      for c in work do
        for ⟨d, _⟩ in collectConjLeaves c do
          if d == .bottom then return false
          if loc.contains d.dual then return false
          if !loc.contains d then
            loc := loc.insert d
            match d with
            | .disj a b => nodeDisjs := (a, b) :: nodeDisjs
            | .lit cls true =>
              for ⟨(other, _), _⟩ in st.disjMap.getD cls [] do
                if loc.contains (.lit other true) then return false
              for ⟨q, _⟩ in st.classGCIs.getD cls [] do
                if !loc.contains q.sup && trigLoc loc q.sub then
                  nextWork := q.sup :: nextWork
            | .nom _ true =>
              if !lSet.contains (x, d) then return false
            | .all r body =>
              let nbs := if r.2 then iAdj.getD (r.1, x) [] else oAdj.getD (r.1, x) []
              if nbs.any (fun y => lSet.contains (y, body.dual)) then return false
            | _ => pure ()
      if nextWork.isEmpty then
        -- Unit-propagate node `x`'s disjunctions inside `loc`
        for (a, b) in nodeDisjs do
          let knownA := (flattenDisj a).any (loc.contains ·)
          let knownB := (flattenDisj b).any (loc.contains ·)
          if knownA || knownB then continue
          let refA := (flattenDisj a).all (refuted loc)
          let refB := (flattenDisj b).all (refuted loc)
          if refA && refB then return false
          else if refA && !loc.contains b then nextWork := b :: nextWork
          else if refB && !loc.contains a then nextWork := a :: nextWork
      work := nextWork
    return true
  let failClash (nc : Std.HashMap Nat (List Concept)) (cns : Std.HashSet Nat) : List (Nat × Concept) := Id.run do
    let mut out : List (Nat × Concept) := []
    for x in cns do
      for c in nc.getD x [] do
        out := (x, c) :: out
    if out.isEmpty then
      for (x, cs) in nc do
        if let some c := cs.head? then
          out := (x, c) :: out
    return out
  for _round in [:512] do
    if clashed then return .error (failClash nodeChoices clashNodes)
    -- 1. Drain pendingLabels (unpacking conjunctions and indexing)
    let mut pIdx := 0
    while h : pIdx < pendingLabels.size do
      let (x, c) := pendingLabels[pIdx]
      pIdx := pIdx + 1
      if c == .top || labelSet.contains (x, c) then continue
      labelSet := labelSet.insert (x, c)
      labelsByNode := labelsByNode.insert x (c :: labelsByNode.getD x [])
      labelsChanged := true
      for ⟨d, _⟩ in collectConjLeaves c do
        if d == .bottom then
          clashed := true; clashNodes := clashNodes.insert x; continue
        if labelSet.contains (x, d.dual) then
          clashed := true; clashNodes := clashNodes.insert x; continue
        let isNew := d == c || !labelSet.contains (x, d)
        if isNew then
          if d != c then
            labelSet := labelSet.insert (x, d)
            labelsByNode := labelsByNode.insert x (d :: labelsByNode.getD x [])
          match d with
          | .lit cls true =>
            classNodes := classNodes.insert cls (x :: classNodes.getD cls [])
            for ⟨(other, _), _⟩ in st.disjMap.getD cls [] do
              if labelSet.contains (x, .lit other true) then
                clashed := true; clashNodes := clashNodes.insert x
          | .nom ind true =>
            let k := indKey ind
            nomNodes := nomNodes.insert k (x :: nomNodes.getD k [])
          | .some r body => someLabels := someLabels.push (x, r, body)
          | .min (n + 1) r body => minLabels := minLabels.push (x, n + 1, r, body)
          | .all r body =>
            allLabels := allLabels.insert (r, x) (body :: allLabels.getD (r, x) [])
            for y in (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []) do
              if !labelSet.contains (y, body) then
                pendingLabels := pendingLabels.push (y, body)
          | .disj a b => disjLabels := disjLabels.push (x, a, b)
          | .self r true =>
            let rn := r.1
            if !edgeSet.contains (rn, x, x) then
              edgeSet := edgeSet.insert (rn, x, x)
              outAdj := outAdj.insert (rn, x) (x :: outAdj.getD (rn, x) [])
              inAdj := inAdj.insert (rn, x) (x :: inAdj.getD (rn, x) [])
              edgesByRole := edgesByRole.insert rn ((x, x) :: edgesByRole.getD rn [])
              roleSources := roleSources.insert (rn, false) (x :: roleSources.getD (rn, false) [])
              roleSources := roleSources.insert (rn, true) (x :: roleSources.getD (rn, true) [])
              edgesChanged := true
          | .dataAll dp dr =>
            if !dataConstraintSet.contains (x, dp, dr) then
              dataConstraintSet := dataConstraintSet.insert (x, dp, dr)
              dataConstraints := (x, dp, dr) :: dataConstraints
          | .dataSome dp _ | .dataMin _ dp _ =>
            dataTouchNodes := dataTouchNodes.insert dp (x :: dataTouchNodes.getD dp [])
          | .dataValue dp l true =>
            if let some v := decodeLiteral l then
              if !(dataByPropNode.getD (dp, x) []).contains v then
                dataEdges := (dp, x, v) :: dataEdges
                dataByPropNode := dataByPropNode.insert (dp, x) (v :: dataByPropNode.getD (dp, x) [])
                dataTouchNodes := dataTouchNodes.insert dp (x :: dataTouchNodes.getD dp [])
          | .dataValue dp l false =>
            if let some v := decodeLiteral l then
              if !negDataEdges.contains (dp, x, v) then
                negDataEdges := (dp, x, v) :: negDataEdges
          | _ => pure ()
    pendingLabels := #[]
    if clashed then return .error (failClash nodeChoices clashNodes)
    -- 2. Close edges under reflexive, rules, and chains when edges changed
    if edgesChanged then
      edgesChanged := false
      let mut eLoop := true
      let mut eIter := 0
      while eLoop && eIter < 16 do
        eLoop := false
        eIter := eIter + 1
        let mut newEdges : Array (IRI × Nat × Nat) := #[]
        for r in p.chars.reflexive do
          for x in nodes do
            if !edgeSet.contains (r, x, x) then newEdges := newEdges.push (r, x, x)
        for (r, t) in p.rules do
          for (u, v) in edgesByRole.getD r.1 [] do
            let x := if r.2 then v else u
            let y := if r.2 then u else v
            let (rn, a, b) := if t.2 then (t.1, y, x) else (t.1, x, y)
            if !edgeSet.contains (rn, a, b) then newEdges := newEdges.push (rn, a, b)
        for c in p.chains do
          match c.body with
          | [] =>
            for x in nodes do
              if !edgeSet.contains (c.head, x, x) then newEdges := newEdges.push (c.head, x, x)
          | r0 :: rs =>
            for (u, v) in edgesByRole.getD r0.1 [] do
              let x := if r0.2 then v else u
              let mid := if r0.2 then u else v
              for y in walkCanonTargets outAdj inAdj mid rs do
                if !edgeSet.contains (c.head, x, y) then newEdges := newEdges.push (c.head, x, y)
        for (rn, a, b) in newEdges do
          if !edgeSet.contains (rn, a, b) then
            edgeSet := edgeSet.insert (rn, a, b)
            outAdj := outAdj.insert (rn, a) (b :: outAdj.getD (rn, a) [])
            inAdj := inAdj.insert (rn, b) (a :: inAdj.getD (rn, b) [])
            edgesByRole := edgesByRole.insert rn ((a, b) :: edgesByRole.getD rn [])
            roleSources := roleSources.insert (rn, false) (a :: roleSources.getD (rn, false) [])
            roleSources := roleSources.insert (rn, true) (b :: roleSources.getD (rn, true) [])
            eLoop := true
            for body in allLabels.getD ((rn, false), a) [] do
              if !labelSet.contains (b, body) then pendingLabels := pendingLabels.push (b, body)
            for body in allLabels.getD ((rn, true), b) [] do
              if !labelSet.contains (a, body) then pendingLabels := pendingLabels.push (a, body)
      if !pendingLabels.isEmpty then continue
    -- 3. Deterministic GCI pass
    if labelsChanged then
      labelsChanged := false
      for ⟨(_, r, body), _, _, _⟩ in st.topAllGCIs do
        for (u, v) in edgesByRole.getD r.1 [] do
          let y := if r.2 then u else v
          if !labelSet.contains (y, body) then pendingLabels := pendingLabels.push (y, body)
      for ⟨(q, n, r, _), _, _, _⟩ in st.topMaxGCIs do
        for x in roleSources.getD r [] do
          if !labelSet.contains (x, q.sup) then
            let deg := (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []).length
            if deg ≥ n + 1 then pendingLabels := pendingLabels.push (x, q.sup)
      for ⟨q, _, _⟩ in st.topOtherGCIs do
        for x in nodes do
          if !labelSet.contains (x, q.sup) then pendingLabels := pendingLabels.push (x, q.sup)
      for (cls, cands) in classNodes do
        for ⟨q, _⟩ in st.classGCIs.getD cls [] do
          for x in cands do
            if !labelSet.contains (x, q.sup) then
              if isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x q.sub then
                pendingLabels := pendingLabels.push (x, q.sup)
      for (r, cands) in roleSources do
        for ⟨q, _⟩ in st.roleGCIs.getD r [] do
          for x in cands do
            if !labelSet.contains (x, q.sup) then
              if isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x q.sub then
                pendingLabels := pendingLabels.push (x, q.sup)
      for (k, cands) in nomNodes do
        for ⟨q, _⟩ in st.nomGCIs.getD k [] do
          for x in cands do
            if !labelSet.contains (x, q.sup) then
              if isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x q.sub then
                pendingLabels := pendingLabels.push (x, q.sup)
      for (dp, cands) in dataTouchNodes do
        for ⟨q, _⟩ in st.dataGCIs.getD dp [] do
          for x in cands do
            if !labelSet.contains (x, q.sup) then
              if isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x q.sub then
                pendingLabels := pendingLabels.push (x, q.sup)
      for ⟨q, _⟩ in st.unanchoredGCIs do
        for x in nodes do
          if !labelSet.contains (x, q.sup) then
            if isTriggeredCanon labelSet outAdj inAdj edgeSet dataByPropNode x q.sub then
              pendingLabels := pendingLabels.push (x, q.sup)
      if !pendingLabels.isEmpty then continue
    -- 4. Resolve open disjunctions (unit propagation first, then at most one local-safe choice per node)
    let mut pickedDisj := false
    let mut pickedNodes : Std.HashSet Nat := {}
    for (x, a, b) in disjLabels do
      if disjKnownCanon labelSet x a || disjKnownCanon labelSet x b then continue
      if labelSet.contains (x, a.dual) then
        pendingLabels := pendingLabels.push (x, b); pickedDisj := true
      else if labelSet.contains (x, b.dual) then
        pendingLabels := pendingLabels.push (x, a); pickedDisj := true
      else
        let mut unitDone := false
        match a with
        | .lit clsA true =>
          if (st.disjMap.getD clsA []).any fun ⟨(other, _), _⟩ => labelSet.contains (x, .lit other true) then
            pendingLabels := pendingLabels.push (x, b); pickedDisj := true; unitDone := true
        | _ => pure ()
        if !unitDone then
          match b with
          | .lit clsB true =>
            if (st.disjMap.getD clsB []).any fun ⟨(other, _), _⟩ => labelSet.contains (x, .lit other true) then
              pendingLabels := pendingLabels.push (x, a); pickedDisj := true; unitDone := true
          | _ => pure ()
        if !unitDone && !pickedNodes.contains x then
          let alts := flattenDisj (.disj a b)
          match alts.find? (localSafe labelSet labelsByNode outAdj inAdj edgeSet dataByPropNode x) with
          | some chosen =>
            pickedNodes := pickedNodes.insert x
            nodeChoices := nodeChoices.insert x (chosen :: nodeChoices.getD x [])
            pendingLabels := pendingLabels.push (x, chosen); pickedDisj := true
          | none =>
            clashed := true; clashNodes := clashNodes.insert x
    if clashed then return .error (failClash nodeChoices clashNodes)
    if pickedDisj then continue
    -- 5. Canonical witness allocation (reusing one witness per `(r, body, allLabels(r, x))`!)
    let mut addedWit := false
    for (x, r, body) in someLabels do
      let adj := if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []
      if adj.any (fun y => body == .top || disjKnownCanon labelSet y body) then continue
      let mut w : Nat := 0
      let mut reuseExisting := false
      -- If `r` has a functional superproperty `fs` and `x` already has an `fs`-neighbor `y`,
      -- reuse `y` (adding `body` and edge `r`) rather than violating `≤1 fs`.
      if funcRoles.contains r then
        for fs in funcSuper.getD r [] do
          let fAdj := if fs.2 then inAdj.getD (fs.1, x) [] else outAdj.getD (fs.1, x) []
          if let some y := fAdj.head? then
            w := y; reuseExisting := true; break
      if reuseExisting then
        pendingLabels := pendingLabels.push (w, body)
      else
        let needFresh := invFuncRoles.contains r
        let wKey := (r, body, (allLabels.getD (r, x) []).eraseDups)
        if !needFresh then
          match canonWit1[wKey]? with
          | some w1 =>
            let asymBad := irreflAsym.contains r.1 &&
              (w1 == x || (if r.2 then edgeSet.contains (r.1, x, w1) else edgeSet.contains (r.1, w1, x)))
            if !asymBad then
              w := w1
            else
              match canonWit2[wKey]? with
              | some w2 => w := w2
              | none =>
                if nodes.size ≥ origNodes + maxNewNodes then return .error []
                w := nextNode; nextNode := nextNode + 1
                nodes := nodes.push w; nodeSet := nodeSet.insert w
                canonWit2 := canonWit2.insert wKey w
                pendingLabels := pendingLabels.push (w, body)
          | none =>
            if nodes.size ≥ origNodes + maxNewNodes then return .error []
            w := nextNode; nextNode := nextNode + 1
            nodes := nodes.push w; nodeSet := nodeSet.insert w
            canonWit1 := canonWit1.insert wKey w
            pendingLabels := pendingLabels.push (w, body)
        else
          if nodes.size ≥ origNodes + maxNewNodes then return .error []
          w := nextNode; nextNode := nextNode + 1
          nodes := nodes.push w; nodeSet := nodeSet.insert w
          pendingLabels := pendingLabels.push (w, body)
      let (rn, a, b) := if r.2 then (r.1, w, x) else (r.1, x, w)
      if !edgeSet.contains (rn, a, b) then
        edgeSet := edgeSet.insert (rn, a, b)
        outAdj := outAdj.insert (rn, a) (b :: outAdj.getD (rn, a) [])
        inAdj := inAdj.insert (rn, b) (a :: inAdj.getD (rn, b) [])
        edgesByRole := edgesByRole.insert rn ((a, b) :: edgesByRole.getD rn [])
        roleSources := roleSources.insert (rn, false) (a :: roleSources.getD (rn, false) [])
        roleSources := roleSources.insert (rn, true) (b :: roleSources.getD (rn, true) [])
        edgesChanged := true
        addedWit := true
        for bd in allLabels.getD ((rn, false), a) [] do
          if !labelSet.contains (b, bd) then pendingLabels := pendingLabels.push (b, bd)
        for bd in allLabels.getD ((rn, true), b) [] do
          if !labelSet.contains (a, bd) then pendingLabels := pendingLabels.push (a, bd)
    for (x, need, r, body) in minLabels do
      let adj := if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []
      let haveCount := (adj.filter (fun y => body == .top || disjKnownCanon labelSet y body)).length
      if haveCount ≥ need then continue
      for _ in [:need - haveCount] do
        let mut w : Nat := 0
        let mut reuseExisting := false
        if need == 1 && funcRoles.contains r then
          for fs in funcSuper.getD r [] do
            let fAdj := if fs.2 then inAdj.getD (fs.1, x) [] else outAdj.getD (fs.1, x) []
            if let some y := fAdj.head? then
              w := y; reuseExisting := true; break
        if !reuseExisting then
          if nodes.size ≥ origNodes + maxNewNodes then return .error []
          w := nextNode; nextNode := nextNode + 1
          nodes := nodes.push w; nodeSet := nodeSet.insert w
        pendingLabels := pendingLabels.push (w, body)
        let (rn, a, b) := if r.2 then (r.1, w, x) else (r.1, x, w)
        if !edgeSet.contains (rn, a, b) then
          edgeSet := edgeSet.insert (rn, a, b)
          outAdj := outAdj.insert (rn, a) (b :: outAdj.getD (rn, a) [])
          inAdj := inAdj.insert (rn, b) (a :: inAdj.getD (rn, b) [])
          edgesByRole := edgesByRole.insert rn ((a, b) :: edgesByRole.getD rn [])
          roleSources := roleSources.insert (rn, false) (a :: roleSources.getD (rn, false) [])
          roleSources := roleSources.insert (rn, true) (b :: roleSources.getD (rn, true) [])
          edgesChanged := true
          addedWit := true
          for bd in allLabels.getD ((rn, false), a) [] do
            if !labelSet.contains (b, bd) then pendingLabels := pendingLabels.push (b, bd)
          for bd in allLabels.getD ((rn, true), b) [] do
            if !labelSet.contains (a, bd) then pendingLabels := pendingLabels.push (a, bd)
    if !addedWit && pendingLabels.isEmpty && !edgesChanged && !labelsChanged then
      let mut addedNegGCI := false
      for q in negLHSGCIs do
        for x in nodes do
          let disjC := Concept.disj q.sup q.sub.dual
          if !labelSet.contains (x, q.sup) && !labelSet.contains (x, disjC) &&
              holdsInCanonState labelSet outAdj inAdj edgeSet dataByPropNode x q.sub &&
              !holdsInCanonState labelSet outAdj inAdj edgeSet dataByPropNode x q.sup then
            pendingLabels := pendingLabels.push (x, disjC)
            addedNegGCI := true
      if !addedNegGCI then
        break
  if clashed || !pendingLabels.isEmpty then return .error (failClash nodeChoices clashNodes)
  -- Propagate DataPropertyRange constraints to any node touching dp before completeDataEdges
  for (dp, dr) in p.dataRanges do
    for x in dataTouchNodes.getD dp [] do
      if !dataConstraintSet.contains (x, dp, dr) then
        dataConstraintSet := dataConstraintSet.insert (x, dp, dr)
        dataConstraints := (x, dp, dr) :: dataConstraints
  -- Convert canonical state to SROIQDModel and verify with kernel-verified `checkModel`!
  let nodeList := nodes.toList
  if nodeList.isEmpty then return .error []
  let additional := nodeList.length - 1
  let mut nodeIdxMap : Std.HashMap Nat (Fin (additional + 1)) := {}
  let mut k := 0
  for a in nodeList do
    if h : k < additional + 1 then
      nodeIdxMap := nodeIdxMap.insert a ⟨k, h⟩
    k := k + 1
  let index := fun a => nodeIdxMap[a]?
  let mut atoms : List (IRI × Fin (additional + 1)) := []
  for (cls, xs) in classNodes do
    for x in xs do
      if let some wx := index x then
        atoms := (cls, wx) :: atoms
  let mut edgesList : List (IRI × Fin (additional + 1) × Fin (additional + 1)) := []
  for (rn, pairs) in edgesByRole do
    for (a, b) in pairs do
      if let some wa := index a then
        if let some wb := index b then
          edgesList := (rn, wa, wb) :: edgesList
  let mut allLabelList : List (Nat × Concept) := []
  for (x, cs) in labelsByNode do
    for c in cs do
      match c with
      | .dataSome .. | .dataMin .. => allLabelList := (x, c) :: allLabelList
      | _ => pure ()
  let sCanon : Branch := {
    labels := allLabelList
    edges := []
    negEdges := []
    unequal := []
    expanded := []
    noms := s.noms
    anons := s.anons
    dataEdges := dataEdges
    negDataEdges := negDataEdges
    dataConstraints := dataConstraints
  }
  let g : Graph := ⟨additional, atoms, edgesList⟩
  let m : SROIQDModel :=
    ⟨g,
     s.noms.filterMap fun (a, n) => (index n).map (a, ·),
     s.anons.filterMap fun (a, n) => (index n).map (a, ·),
     completeDataEdges p sCanon index⟩
  if h : checkModel p m = true then return .ok ⟨m, h⟩ else return .error []

/-- Untrusted canonical-witness-reuse finite model proposer (anywhere blocking by `(r, body, allLabels)`
    with conflict-driven disjunction choice restarts). Every returned model is verified by
    `checkModel p m` (`checkModel_sound`) before acceptance. -/
private def tryCanonicalModel (p : Problem) (st : StaticIndex p) (s : Branch) :
    Option {m : SROIQDModel // checkModel p m = true} := Id.run do
  let ancestors := buildClassAncestors p
  let mut banned : Std.HashSet (Nat × Concept) := {}
  for _attempt in [:6] do
    match tryCanonicalModelAttempt p st ancestors s banned with
    | .ok m => return some m
    | .error newBans =>
      if newBans.isEmpty then return none
      let mut addedAny := false
      for b in newBans do
        if !banned.contains b then
          banned := banned.insert b
          addedAny := true
      if !addedAny then return none
  return none

/-- Try a checked model of `p` with a separate seed world for each requested concept.
    The seeds guide model construction. Callers can harvest the classes and
    counterexamples actually present in the checked model. -/
def proposeSeededCanonicalModel (p : Problem) (concepts : List Concept) :
    Option {m : SROIQDModel // checkModel p m = true} := do
  let s ← initial p
  let firstSeed := 1 + s.noms.length + s.anons.length
  let seeds := (concepts.zipIdx firstSeed).map fun (c, x) => (x, c)
  tryCanonicalModel p (buildStaticIndex p) { s with labels := s.labels ++ seeds }

private def tryBranchModel (p : Problem) (s : Branch) : Option SROIQDModel :=
  let m := toModel p s
  if checkModel p m then some m
  else (toBlockedModels p s).find? (checkModel p)

private def advanceDeltaCache {s b : Branch} (cache : DeltaCache s) (added : List (Nat × Concept))
    (hOld : ∀ xc ∈ s.labels, xc ∈ b.labels) (hAdded : ∀ xc ∈ added, xc ∈ b.labels)
    (hEdges : b.edges = s.edges) (openDisjs' : List (Nat × Concept × Concept)) :
    Option (DeltaCache b) :=
  if added.any (fun (_, c) => isSpecialConcept c) then none
  else
    let labels' := cache.labels.extend added hOld hAdded
    let (openDisjs'', disjsByNode') := added.foldl (fun (od, dbn) (x, c) =>
      match c with
      | .disj a d => ((x, a, d) :: od, dbn.insert x ((a, d) :: dbn.getD x []))
      | _ => (od, dbn)) (openDisjs', cache.disjsByNode)
    some {
      labels := labels'
      eidx := hEdges.symm ▸ cache.eidx
      openDisjs := openDisjs''
      disjsByNode := disjsByNode'
      dirtyLabels := added
      nodeCount := cache.nodeCount
    }

private def probeLoop (p : Problem) (st : StaticIndex p) (maxNodes : Nat) (searchModels : Bool) :
    Nat → (s : Branch) → Option Nat → Option (EdgeIndex s.edges × Bool) → Option (DeltaCache s) →
    ProbeVerdict p s × Option Nat
  | 0, _, fuel, _, _ => (.unknown, fuel)
  | _ + 1, _, some 0, _, _ => (.unknown, some 0)
  | depth + 1, s, fuel, edgeCache, deltaCache? => Id.run do
    let fuel := fuel.map (· - 1)
    let runDelta (cache : DeltaCache s) (ds : DeltaStep p s) : Option (ProbeVerdict p s × Option Nat) :=
      match ds with
      | .fallback => none
      | .closed t =>
        let (result, remaining) := probeBranches s t.branches
          (fun b _ f => probeLoop p st maxNodes searchModels depth b f none none) fuel
        match result with
        | .model m => some (.model m, remaining)
        | .unknown => some (.unknown, remaining)
        | .jump d clash => some (.closed (d + 1) (some clash.val) clash.property, remaining)
        | .closed d clashes refutes =>
          let learned := probeClash st s t.branches clashes
          some (.closed (d + 1) learned (fun hs => by
            obtain ⟨b, hb, hsat⟩ := t.preserves hs
            exact refutes b hb hsat), remaining)
      | .pushed1 t child added hBr hOld hAdded hEdges openDisjs' =>
        let childDelta := advanceDeltaCache cache added hOld hAdded hEdges openDisjs'
        let childEdge := some (hEdges.symm ▸ cache.eidx, true)
        let (ans, remaining) := probeLoop p st maxNodes searchModels depth child fuel childEdge childDelta
        match ans with
        | .model m => some (.model m, remaining)
        | .unknown => some (.unknown, remaining)
        | .closed d clue refutes =>
          if let some jump := clue.bind (provedClash s) then
            some (.closed (d + 1) (some jump.val) jump.property, remaining)
          else
            let learned := probeClash st s [child] [clue]
            some (.closed (d + 1) learned (fun hs => by
              obtain ⟨b, hb, hsat⟩ := t.preserves hs
              rw [hBr, List.mem_singleton] at hb
              exact refutes (hb ▸ hsat)), remaining)
      | .pushed2 t left right addedL addedR hBr hOldL hAddedL hEdgesL hOldR hAddedR hEdgesR openDisjs' =>
        let dL := advanceDeltaCache cache addedL hOldL hAddedL hEdgesL openDisjs'
        let eL := some (hEdgesL.symm ▸ cache.eidx, true)
        let (ansL, rem1) := probeLoop p st maxNodes searchModels depth left fuel eL dL
        match ansL with
        | .model m => some (.model m, rem1)
        | .closed dL' clueL refL =>
          if let some jump := clueL.bind (provedClash s) then
            some (.closed (dL' + 1) (some jump.val) jump.property, rem1)
          else
            let dR := advanceDeltaCache cache addedR hOldR hAddedR hEdgesR openDisjs'
            let eR := some (hEdgesR.symm ▸ cache.eidx, true)
            let (ansR, rem2) := probeLoop p st maxNodes searchModels depth right rem1 eR dR
            match ansR with
            | .model m => some (.model m, rem2)
            | .unknown => some (.unknown, rem2)
            | .closed dR' clueR refR =>
              if let some jump := clueR.bind (provedClash s) then
                some (.closed (dR' + 1) (some jump.val) jump.property, rem2)
              else
                let learned := probeClash st s [left, right] [clueL, clueR]
                some (.closed (max dL' dR' + 1) learned (fun hs => by
                  obtain ⟨b, hb, hsat⟩ := t.preserves hs
                  rw [hBr] at hb
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
                  rcases hb with rfl | rfl
                  · exact refL hsat
                  · exact refR hsat), rem2)
        | .unknown =>
          if rem1 == some 0 then some (.unknown, rem1)
          else
            let dR := advanceDeltaCache cache addedR hOldR hAddedR hEdgesR openDisjs'
            let eR := some (hEdgesR.symm ▸ cache.eidx, true)
            let (ansR, rem2) := probeLoop p st maxNodes searchModels depth right rem1 eR dR
            match ansR with
            | .model m => some (.model m, rem2)
            | .closed dR' clueR _ =>
              if let some jump := clueR.bind (provedClash s) then
                some (.closed (dR' + 1) (some jump.val) jump.property, rem2)
              else some (.unknown, rem2)
            | .unknown => some (.unknown, rem2)
    if let some dcache := deltaCache? then
      if searchModels && dcache.nodeCount > maxNodes then return (.unknown, fuel)
      if let some ans := runDelta dcache (nextDelta p st s dcache) then
        return ans
    let isSmall := s.labels.length ≤ 16 && p.tbox.length ≤ 16 && s.edges.length ≤ 16 &&
      p.rules.length ≤ 16 && p.chains.length ≤ 16
    let stepRes : NextStep p s :=
      if isSmall then
        match nextSmall p s maxNodes (deferAbsorbed := true) with
        | some t => .changedEdges t (fastNodeCount s)
        | none => .done (fastNodeCount s)
      else
        nextWith p st s maxNodes (deferAbsorbed := true) edgeCache
    let curNodes := match stepRes with
      | .sameEdges _ _ _ _ n | .changedEdges _ n | .done n => n
      | .enterDelta c _ => c.nodeCount
    if searchModels && curNodes > maxNodes then
      return (.unknown, fuel)
    match stepRes with
    | .done _ =>
      if searchModels then
        if let some m := tryBranchModel p s then return (.model m, fuel)
      let some t := undecidedGCIFallback p s (buildBranchIndex s).nodes | return (.unknown, fuel)
      let (result, remaining) := probeBranches s t.branches
        (fun b _ f => probeLoop p st maxNodes searchModels depth b f none none) fuel
      match result with
      | .model m => return (.model m, remaining)
      | .unknown => return (.unknown, remaining)
      | .jump d clash => return (.closed (d + 1) (some clash.val) clash.property, remaining)
      | .closed d clashes refutes =>
        let learned := probeClash st s t.branches clashes
        return (.closed (d + 1) learned (fun hs => by
          obtain ⟨b, hb, hsat⟩ := t.preserves hs
          exact refutes b hb hsat), remaining)
    | .enterDelta dcache ds =>
      match runDelta dcache ds with
      | some ans => return ans
      | none => return (.unknown, fuel)
    | .sameEdges t he eidx edgesSat _ =>
      let (result, remaining) := probeBranches s t.branches
        (fun b hb f => probeLoop p st maxNodes searchModels depth b f (some ((he b hb).symm ▸ eidx, edgesSat)) none) fuel
      match result with
      | .model m => return (.model m, remaining)
      | .unknown => return (.unknown, remaining)
      | .jump d clash => return (.closed (d + 1) (some clash.val) clash.property, remaining)
      | .closed d clashes refutes =>
        let learned := probeClash st s t.branches clashes
        return (.closed (d + 1) learned (fun hs => by
          obtain ⟨b, hb, hsat⟩ := t.preserves hs
          exact refutes b hb hsat), remaining)
    | .changedEdges t _ =>
      let tryEarlyModel := searchModels && match t.branches with
        | [u] =>
          u.expanded.length > s.expanded.length &&
          let nextNodes := fastNodeCount u
          nextNodes > curNodes && (curNodes ≤ 32 || curNodes % 16 == 0)
        | _ => false
      if tryEarlyModel then
        if let some m := tryBranchModel p s then return (.model m, fuel)
      let (result, remaining) := probeBranches s t.branches
        (fun b _ f => probeLoop p st maxNodes searchModels depth b f none none) fuel
      match result with
      | .model m => return (.model m, remaining)
      | .unknown => return (.unknown, remaining)
      | .jump d clash => return (.closed (d + 1) (some clash.val) clash.property, remaining)
      | .closed d clashes refutes =>
        let learned := probeClash st s t.branches clashes
        return (.closed (d + 1) learned (fun hs => by
          obtain ⟨b, hb, hsat⟩ := t.preserves hs
          exact refutes b hb hsat), remaining)

private def probe (p : Problem) (maxNodes : Nat) (searchModels : Bool)
    (depth : Nat) (s : Branch) (fuel : Option Nat) : ProbeVerdict p s × Option Nat :=
  let st := buildStaticIndex p
  if searchModels && (p.tbox.length > 16 || p.rules.length > 16 || s.labels.length > 16) then
    match tryCanonicalModel p st s with
    | some m => (.model m.val, fuel)
    | none => probeLoop p st maxNodes searchModels depth s fuel none none
  else
    probeLoop p st maxNodes searchModels depth s fuel none none

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
