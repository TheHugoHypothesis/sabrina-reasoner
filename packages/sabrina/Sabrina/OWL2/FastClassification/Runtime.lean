import Sabrina.OWL2.FastClassification.EL
import Sabrina.OWL2.FastCB
import Sabrina.OWL2.FastLocality

/-! Parallel runtime classification and realization using checked SROIQ(D) models and locality modules. -/

namespace Sabrina.OWL2.FastClassification

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Profile
open Sabrina.OWL2.FastLocality
open Sabrina.OWL2.EL
open Sabrina.OWL2.Classification
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.Normalize
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

private def canHarvestStandardModel (p : Problem) : Bool :=
  !p.allDataProps.any (fun dp => dp == topDataProperty || dp == bottomDataProperty) &&
  !p.allDataAtoms.any (fun
    | .datatype t | .restriction t _ => t == owlReal
    | _ => false)

private def checkTableauRolesOkFast (p : Problem) : Bool :=
  let closed := Sabrina.ALC.roleClosure p.rules
  p.simpleRoles.all (fun r => (RoleChains.SimpleRoles.firstComposite closed p.chains r).isNone) &&
  RoleChains.checkInferredRank p.rules p.chains

/-- Propose and kernel-verify (`checkModel`) a finite `SROIQDModel` for `o` when `o`
    is inside the standard `datatypeMap` tableau fragment (reused across classification,
    realization, and materialization to soundly prune non-entailed candidates in O(1)). -/
def proposeVerifiedModel (o : Ontology) : Option (SROIQDModel × Problem) :=
  match normalizeWithDefs o with
  | none => none
  | some (_, p) =>
    if canHarvestStandardModel p && checkTableauRolesOkFast p && p.root == .top then
      let limits := Limits.forProblem p
      match propose p limits with
      | some (.model m) => if checkModel p m then some (m, p) else none
      | _ => none
    else none

private def checkELRegular (elAxs : List ELAxiom) : Bool := Id.run do
  let mut rules : Sabrina.ALC.RoleTheory := []
  let mut chains : List RoleChains.Chain := []
  for ax in elAxs do
    match ax with
    | .roleSub r s => rules := ⟨(r, false), (s, false)⟩ :: rules
    | .roleChain r1 r2 s => chains := RoleChains.Chain.named [r1, r2] s :: chains
    | _ => pure ()
  return RoleChains.checkInferredRank rules chains

/-- Fast parallel compact $\mathcal{EL}^{++}$ classifier for 100k–350k class ontologies:
    returns `FastEL.CompactELHierarchy` without materializing flat `List (IRI × IRI)`
    subsumption pairs. -/
def classifyOntologyCompactELRuntime (o : Ontology)
    (decls : List FunctionalSyntax.EntityDecl := []) (numWorkers : Nat := 8) :
    Option FastEL.CompactELHierarchy :=
  let namedClasses := collectNamedClasses o decls
  let fp := profileOntology o
  if fp.leastFragment == .el then
    match normalizeEL o with
    | some elAxs =>
      if checkELRegular elAxs then
        FastEL.classifyFastEL elAxs namedClasses numWorkers
      else none
    | none => none
  else none

private def spawnChunks {α β : Type} (chunk : Nat) (f : α → β) :
    Nat → List α → List (Task (List β))
  | 0, xs => [Task.pure (xs.map f)]
  | _ + 1, [] => []
  | workers + 1, x :: xs =>
    let (front, rest) := (x :: xs).splitAt chunk
    Task.spawn (fun () => front.map f) :: spawnChunks chunk f workers rest

private theorem spawnChunks_get {α β : Type} (chunk : Nat) (f : α → β)
    (workers : Nat) (xs : List α) :
    (spawnChunks chunk f workers xs).flatMap Task.get = xs.map f := by
  induction workers generalizing xs with
  | zero => simp [spawnChunks]
  | succ workers ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [spawnChunks, List.splitAt_eq, List.flatMap_cons, Task.spawn, ih]
      rw [← List.map_append, List.take_append_drop]

def mapIndependent {α β : Type} (workers : Nat) (f : α → β) (xs : List α) : List β :=
  if workers ≤ 1 || xs.length ≤ 1 then xs.map f
  else
    let count := min workers xs.length
    let chunk := (xs.length + count - 1) / count
    (spawnChunks chunk f count xs).flatMap Task.get

theorem mapIndependent_eq {α β : Type} (workers : Nat) (f : α → β) (xs : List α) :
    mapIndependent workers f xs = xs.map f := by
  unfold mapIndependent
  split
  · rfl
  · apply spawnChunks_get

/-- A relaxation used to try subsumption counterexamples in a separate component. -/
def counterWithoutIndividuals (p : Problem) : Problem :=
  { p with
    tbox := p.tbox.filter fun q => q.sub.individuals.isEmpty && q.sup.individuals.isEmpty
    keys := []
    classAssertions := []
    objAssertions := []
    negObjAssertions := []
    sameInds := []
    diffInds := []
    dataAssertions := []
    negDataAssertions := [] }

private theorem counterWithoutIndividuals_sat {p : Problem} (h : p.Sat) :
    (counterWithoutIndividuals p).Sat := by
  obtain ⟨i, hi, hroot⟩ := h
  refine ⟨i, ⟨?_, hi.rules, hi.chains, hi.reflexive, hi.irreflexive, hi.asymmetric,
    hi.disjoint, hi.subData, hi.disjointData, hi.funcData, hi.dataRanges,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hroot⟩
  · intro q hq
    exact hi.tbox q (List.mem_filter.mp hq).1
  all_goals simp [counterWithoutIndividuals]

def appendModelComponent (base component : SROIQDModel) : SROIQDModel :=
  let additional := base.graph.additionalWorlds + component.graph.additionalWorlds + 1
  let left (x : base.graph.World) : Fin (additional + 1) := ⟨x.val, by have := x.isLt; omega⟩
  let right (x : component.graph.World) : Fin (additional + 1) :=
    ⟨base.graph.additionalWorlds + 1 + x.val, by have := x.isLt; omega⟩
  let atoms := (base.graph.atoms.map fun (c, x) => (c, left x)) ++
    (component.graph.atoms.map fun (c, x) => (c, right x))
  let edges := (base.graph.edges.map fun (r, x, y) => (r, left x, left y)) ++
    (component.graph.edges.map fun (r, x, y) => (r, right x, right y))
  let data := (base.dataEdges.map fun (r, x, v) => (r, left x, v)) ++
    (component.dataEdges.map fun (r, x, v) => (r, right x, v))
  ⟨⟨additional, atoms, edges⟩, base.nominals.map (Prod.map id left),
    base.anons.map (Prod.map id left), data⟩

private def groupListChunks {α : Type} (chunkSize : Nat) (xs : List α) : List (List α) :=
  let arr := xs.toArray
  if chunkSize == 0 || arr.isEmpty then []
  else
    (List.range ((arr.size + chunkSize - 1) / chunkSize)).map fun i =>
      (arr.extract (i * chunkSize) ((i + 1) * chunkSize)).toList

/-- Simplify a concept evaluated on a disjoint `right` component of `appendModelComponent base comp`,
    where every named/anonymous individual lives in `base` (`left` worlds), so `.nom _ true` is
    always false (`.bottom`) and `.nom _ false` is always true (`.top`). -/
def simplifyNomRight : Concept → Concept
  | .nom _ true => .bottom
  | .nom _ false => .top
  | .conj a b =>
    let a' := simplifyNomRight a
    let b' := simplifyNomRight b
    if a' == .bottom || b' == .bottom then .bottom
    else if a' == .top then b'
    else if b' == .top then a'
    else .conj a' b'
  | .disj a b =>
    let a' := simplifyNomRight a
    let b' := simplifyNomRight b
    if a' == .top || b' == .top then .top
    else if a' == .bottom then b'
    else if b' == .bottom then a'
    else .disj a' b'
  | .some r b =>
    let b' := simplifyNomRight b
    if b' == .bottom then .bottom else .some r b'
  | .all r b =>
    let b' := simplifyNomRight b
    if b' == .top then .top else .all r b'
  | .min (n + 1) r b =>
    let b' := simplifyNomRight b
    if b' == .bottom then .bottom else .min (n + 1) r b'
  | .max n r b =>
    let b' := simplifyNomRight b
    if b' == .bottom then .top else .max n r b'
  | c => c

/-- Extract the non-vacuous nominal-bearing TBox checks that must hold on any disjoint
    `right` component appended onto a verified `base` model of `p`. -/
def extractNomRightChecks (p : Problem) : Option (List (Concept × Concept)) :=
  if !p.keys.isEmpty || !canHarvestStandardModel p then none
  else
    let hasTopObj : Concept → Bool := fun c =>
      let rec go : Concept → Bool
        | .some r b | .all r b | .min _ r b | .max _ r b => r.1 == topObjectProperty || go b
        | .self r _ => r.1 == topObjectProperty
        | .conj a b | .disj a b => go a || go b
        | _ => false
      go c
    if p.tbox.any (fun q => hasTopObj q.sub || hasTopObj q.sup) ||
        p.rules.any (fun (r, s) => r.1 == topObjectProperty || s.1 == topObjectProperty) then
      none
    else
      let checks := p.tbox.filterMap fun q =>
        if q.sub.individuals.isEmpty && q.sup.individuals.isEmpty then none
        else
          let sub' := simplifyNomRight q.sub
          let sup' := simplifyNomRight q.sup
          if sub' == .bottom || sup' == .top then none
          else some (sub', sup')
      some checks

/-- Verify that every non-vacuous nominal-bearing TBox GCI of `p` holds on every world
    of a disjoint `component` (in O(|checks| × |component.worlds|) instead of re-checking `base`). -/
def checkNomRightOnComponent (checks : List (Concept × Concept)) (comp : SROIQDModel) : Bool :=
  if checks.isEmpty then true
  else
    let worlds := comp.graph.worlds
    checks.all fun (sub', sup') =>
      worlds.all fun w =>
        match eval? comp w sub' with
        | some true => eval? comp w sup' == some true
        | some false => true
        | none => false

/-- Verify TBox components appended onto a base ABox model. When `nomRightChecks?` is
    available (no `HasKey`, no `owl:topObjectProperty`), checks only the non-vacuous
    nominal GCIs on each component's worlds in O(|comp.worlds|); otherwise falls back
    to merged `checkModel p (appendModelComponent base comp)`. -/
def checkComponentBatches (p : Problem) (base : SROIQDModel) (comps : List SROIQDModel)
    (numWorkers : Nat) : List SROIQDModel :=
  match extractNomRightChecks p with
  | some checks =>
    comps.filter (checkNomRightOnComponent checks)
  | none =>
    let chunks := groupListChunks 4 comps
    (mapIndependent numWorkers (fun grp =>
      let combined := grp.foldl appendModelComponent base
      if checkModel p combined then [combined]
      else grp.filterMap fun c =>
        let m := appendModelComponent base c
        if checkModel p m then some m else none) chunks).flatten

/-- Context for fast disjoint-component TBox reasoning on large ABox ontologies. -/
structure TBoxFastCtx where
  tboxOnt : Ontology
  tboxIdx : LocalityIndex
  nomChecks : List (Concept × Concept)

private def exprHasIndiv : ClassExpr → Bool
  | .oneOf _ | .objectValue _ _ => true
  | .complement c | .objectSome _ c | .objectAll _ c | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => exprHasIndiv c
  | .intersection a b | .union a b => exprHasIndiv a || exprHasIndiv b
  | _ => false

private def isNomOrKeyAxiomFast : Axiom → Bool
  | .subClassOf a b => exprHasIndiv a || exprHasIndiv b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs => cs.any exprHasIndiv
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c => exprHasIndiv c
  | .hasKey .. => true
  | _ => false

private def isABoxAxiomFast : Axiom → Bool
  | .classAssertion .. | .objectAssertion .. | .negativeObjectAssertion ..
  | .dataAssertion .. | .negativeDataAssertion .. | .sameIndividuals .. | .differentIndividuals .. => true
  | _ => false

def buildTBoxFastCtx (o : Ontology) (p : Problem) : Option TBoxFastCtx := do
  if p.classAssertions.length < 64 then none
  let checks ← extractNomRightChecks p
  let tboxOnt := o.filter fun ax => !isABoxAxiomFast ax && !isNomOrKeyAxiomFast ax
  if tboxOnt.length + 64 > o.length then none
  return { tboxOnt := tboxOnt, tboxIdx := LocalityIndex.build tboxOnt, nomChecks := checks }

/-- Try to decide `o ⊨ SubObjectPropertyOf(r, s)` via the small ⊥-local module of `tboxOnlyOnt ⊆ o`:
    - UNSAT on `modT` proves `o ⊨ r ⊑ s` by monotonicity (`modT ⊆ o`).
    - SAT with a verified model `comp` passing `checkNomRightOnComponent` proves `o ⊭ r ⊑ s`
      via disjoint union `I_base ⊕ I_⊥(comp) ⊨ o` (fresh witness individuals live in `comp`). -/
def tryDecideSubObjPropViaTBox (tctx : TBoxFastCtx) (r s : IRI) : Option Bool := do
  let ax := Axiom.subObjectProperty (.named r) (.named s)
  let (modT, _) := extractBotModuleWithIndex tctx.tboxIdx tctx.tboxOnt (axiomSig ax)
  let freshA := "urn:sabrina:subprop_a"
  let freshB := "urn:sabrina:subprop_b"
  let cntOnt := Axiom.objectAssertion (.named r) (.named freshA) (.named freshB) ::
    Axiom.negativeObjectAssertion (.named s) (.named freshA) (.named freshB) :: modT
  let (_, pCnt) ← normalizeWithDefs cntOnt
  if !canHarvestStandardModel pCnt || !checkTableauRolesOkFast pCnt then none
  else
    let limits := Limits.forProblem pCnt
    match propose pCnt limits with
    | some (.refutation d) =>
      if pCnt.checkSimple && checkEvidence pCnt limits.worlds (.refutation d) then some true
      else none
    | some (.model comp) =>
      if pCnt.checkSimple && checkModel pCnt comp && checkNomRightOnComponent tctx.nomChecks comp then
        some false
      else none
    | none => none

/-- Try to decide `o ⊨ a ⊑ b` using the small ⊥-local module of `tboxOnlyOnt ⊆ o`:
    - UNSAT on `modT` transfers to `o` immediately by monotonicity (`modT ⊆ o`).
    - SAT with a verified model `comp` of `modT` that passes `checkNomRightOnComponent`
      transfers to `o` via disjoint union `I_base ⊕ I_⊥(comp) ⊨ o`. -/
private def tryDecideSubViaTBox (tctx : TBoxFastCtx) (a b : IRI) :
    Option (Bool × Option (SROIQDModel × List IRI)) := do
  let (modT, sigT) := extractBotModuleWithIndex tctx.tboxIdx tctx.tboxOnt
    (axiomSig (.subClassOf (.named a) (.named b)))
  let (defs, pT) ← normalizeWithDefs modT
  match queryToInclusions defs (.subClassOf (.named a) (.named b)) with
  | some [q] =>
    let cnt := counterProblem pT q
    if !canHarvestStandardModel cnt || !checkTableauRolesOkFast cnt then none
    else
      let limits := Limits.forProblem cnt
      match propose cnt limits with
      | some (.refutation d) =>
        if cnt.checkSimple && checkEvidence cnt limits.worlds (.refutation d) then
          some (true, none)
        else none
      | some (.model comp) =>
        if cnt.checkSimple && checkModel cnt comp && checkNomRightOnComponent tctx.nomChecks comp then
          some (false, some (comp, sigT.cls))
        else none
      | none => none
  | _ => none

/-- Refutations of the relaxed problem transfer to the original problem. A model
    can only settle the query after the original problem checks the combined graph. -/
private def decideCounterWithComponent (p : Problem) (base : SROIQDModel) :
    Option (PSum (¬ p.Sat) {m : SROIQDModel // checkModel p m = true}) := do
  let core := counterWithoutIndividuals p
  let limits : Limits := { worlds := 32, depth := 64, visits := 64 }
  match ← propose core limits with
  | .model component =>
    let model := appendModelComponent base component
    if h : checkModel p model = true then return .inr ⟨model, h⟩ else none
  | .refutation depth =>
    if h : checkEvidence core limits.worlds (.refutation depth) = true then
      return .inl fun hp => checkEvidence_sound h (counterWithoutIndividuals_sat hp)
    else none

/-- Decide `mod ⊨ a ⊑ b` while also returning the kernel-verified finite countermodel `m`
    whenever satisfiability of `a ∧ ¬b` is certified by `SROIQD.propose` + `checkEvidence`. -/
private def decideSubWithModel (mod : Ontology) (a b : IRI)
    (baseModel? : Option SROIQDModel := none) : Option (Bool × Option SROIQDModel) :=
  let tryFast : Option (Bool × Option SROIQDModel) :=
    match normalizeWithDefs mod with
    | some (defs, p) =>
      match queryToInclusions defs (.subClassOf (.named a) (.named b)) with
      | some [q] =>
        let cnt := counterProblem p q
        if canHarvestStandardModel cnt && checkTableauRolesOkFast cnt then
          let component? := baseModel?.bind fun base =>
            if cnt.classAssertions.length < 64 then none else decideCounterWithComponent cnt base
          match component? with
          | some (.inl _) => some (true, none)
          | some (.inr m) => some (false, some m.val)
          | none =>
            let limits := Limits.forProblem cnt
            match propose cnt limits with
            | some ev =>
              if cnt.checkSimple && checkEvidence cnt limits.worlds ev then
                match ev with
                | .model m => some (false, some m)
                | .refutation _ => some (true, none)
              else none
            | none => none
        else none
      | _ => none
    | none => none
  match tryFast with
  | some ans => some ans
  | none => (decidesSubsumption fastConsistencyCheck mod a b).map (·, none)

/-- Extract per-class possible-subsumer sets from a kernel-verified finite model `m`
    of a valid ⊥-local module `(mod, σ)` (or of the full ontology when `sigClasses = namedClasses`).
    Every entry `(c, poss)` certifies:
    1. `c` holds at some world of `m` (hence `c` is satisfiable in `o`), and
    2. every `b ∈ namedClasses` with `b ≠ owl:Thing` and `b ∉ poss` is separated from `c`
       at some world of `m`'s canonical ⊥-extension (hence `o ⊭ c ⊑ b`). -/
private def summarizeModel (m : SROIQDModel) (sigClasses : List IRI)
    (namedClassSet : Std.HashSet IRI) : List (IRI × List IRI) := Id.run do
  let n := m.graph.additionalWorlds + 1
  if n == 0 then return []
  let midx := ModelIndex.build m
  let sigSet : Std.HashSet IRI := sigClasses.foldl (fun s c => s.insert c) {}
  -- Pre-index active signature classes per world in O(|m.graph.atoms|)
  let mut worldAtoms : Array (List IRI) := Array.replicate n []
  let mut activeClasses : Array IRI := #[]
  let mut seenCls : Std.HashSet IRI := {}
  for (c, w) in m.graph.atoms do
    if c != thing && c != nothing && namedClassSet.contains c && sigSet.contains c then
      worldAtoms := worldAtoms.modify w.val (c :: ·)
      if !seenCls.contains c then
        seenCls := seenCls.insert c
        activeClasses := activeClasses.push c
  let mut out : Array (IRI × List IRI) := #[]
  for c in activeClasses do
    match midx.atomWorlds.getD c [] with
    | [] => pure ()
    | w0 :: wsRest =>
      let cand0 := worldAtoms[w0.val]!
      let cand := if wsRest.isEmpty then cand0
        else cand0.filter fun b => wsRest.all fun w => midx.atomSet.contains (b, w)
      out := out.push (c, cand)
  if namedClassSet.contains thing then
    match m.graph.worlds with
    | [] => pure ()
    | w0 :: wsRest =>
      let cand0 := worldAtoms[w0.val]!
      let cand := if wsRest.isEmpty then cand0
        else cand0.filter fun b => wsRest.all fun w => midx.atomSet.contains (b, w)
      out := out.push (thing, cand)
  return out.toList

/-- Known-Possible Subsumer classification state (Glimm et al. JAIR 2012):
    maintains exact known subsumers/subsumes adjacency sets (`knownSups`, `knownSubs`)
    plus monotonically shrinking verified-model possible-subsumer sets (`possSups`),
    avoiding `O(|C|²)` pair enumeration and `O(|C|³)` closure scans. -/
private structure KPState where
  knownSups : Std.HashMap IRI (Std.HashSet IRI) := {}
  knownSubs : Std.HashMap IRI (Std.HashSet IRI) := {}
  possSups : Std.HashMap IRI (Option (List IRI)) := {}
  knownFalse : Std.HashSet (IRI × IRI) := {}
  satSet : Std.HashSet IRI := {}
  unsatSet : Std.HashSet IRI := {}

private def KPState.init (o : Ontology) (namedClasses : List IRI)
    (namedClassSet : Std.HashSet IRI)
    (cbSubs : List (IRI × IRI) := []) (cbUnsats : List IRI := []) : KPState := Id.run do
  let mut toldAdj : Std.HashMap IRI (List IRI) := {}
  for ax in o do
    match ax with
    | .subClassOf (.named a) (.named b) =>
      if a != b then toldAdj := toldAdj.insert a (b :: toldAdj.getD a [])
    | .equivalentClasses cs =>
      for c1 in cs do
        if let .named a := c1 then
          for c2 in cs do
            if let .named b := c2 then
              if a != b then toldAdj := toldAdj.insert a (b :: toldAdj.getD a [])
    | _ => pure ()
  for (a, b) in cbSubs do
    if a != b then toldAdj := toldAdj.insert a (b :: toldAdj.getD a [])
  let hasThing := namedClassSet.contains thing
  let mut kSups : Std.HashMap IRI (Std.HashSet IRI) := {}
  let mut kSubs : Std.HashMap IRI (Std.HashSet IRI) := {}
  for a in namedClasses do
    let mut vis : Std.HashSet IRI := ({} : Std.HashSet IRI).insert a
    let mut stk : List IRI := [a]
    while !stk.isEmpty do
      let u := stk.head!
      stk := stk.tail!
      for v in toldAdj.getD u [] do
        if !vis.contains v then
          vis := vis.insert v
          stk := v :: stk
    let mut supsA : Std.HashSet IRI := ({} : Std.HashSet IRI).insert a
    if hasThing then supsA := supsA.insert thing
    for v in vis do
      if namedClassSet.contains v then
        supsA := supsA.insert v
    kSups := kSups.insert a supsA
    for b in supsA do
      kSubs := kSubs.insert b ((kSubs.getD b {}).insert a)
  let mut sat0 : Std.HashSet IRI := {}
  let mut unsat0 : Std.HashSet IRI := {}
  if hasThing then sat0 := sat0.insert thing
  if namedClassSet.contains nothing then unsat0 := unsat0.insert nothing
  for u in cbUnsats do
    if namedClassSet.contains u then
      unsat0 := unsat0.insert u
      for x in kSubs.getD u {} do
        unsat0 := unsat0.insert x
  return { knownSups := kSups, knownSubs := kSubs, satSet := sat0, unsatSet := unsat0 }

private def KPState.markSat (c : IRI) (st : KPState) : KPState := Id.run do
  if st.satSet.contains c then return st
  let mut sat := st.satSet.insert c
  for d in st.knownSups.getD c {} do
    sat := sat.insert d
  return { st with satSet := sat }

private def KPState.markUnsat (c : IRI) (st : KPState) : KPState := Id.run do
  let mut unsat := st.unsatSet.insert c
  for x in st.knownSubs.getD c {} do
    unsat := unsat.insert x
  return { st with unsatSet := unsat }

private def KPState.mergeSummary (summary : List (IRI × List IRI)) (st : KPState) : KPState := Id.run do
  let mut cur := st
  for (c, cand) in summary do
    cur := cur.markSat c
    let newPoss := match cur.possSups.getD c none with
      | none => some cand
      | some old =>
        if cand.length ≤ 16 then some (old.filter fun b => cand.contains b)
        else
          let cset : Std.HashSet IRI := cand.foldl (fun s x => s.insert x) {}
          some (old.filter fun b => cset.contains b)
    cur := { cur with possSups := cur.possSups.insert c newPoss }
  return cur

private def KPState.addTrue (a b : IRI) (st : KPState) : KPState := Id.run do
  if (st.knownSups.getD a {}).contains b then return st
  let supsB := (st.knownSups.getD b {}).insert b
  let subsA := (st.knownSubs.getD a {}).insert a
  let mut kSups := st.knownSups
  let mut kSubs := st.knownSubs
  for x in subsA do
    let mut sx := kSups.getD x {}
    for y in supsB do
      if !sx.contains y then
        sx := sx.insert y
        kSubs := kSubs.insert y ((kSubs.getD y {}).insert x)
    kSups := kSups.insert x sx
  return { st with knownSups := kSups, knownSubs := kSubs }

private def KPState.addFalse (a b : IRI) (st : KPState) : KPState :=
  match st.possSups.getD a none with
  | some ps => { st with possSups := st.possSups.insert a (some (ps.filter (· != b))) }
  | none => { st with knownFalse := st.knownFalse.insert (a, b) }

private def KPState.isPairDecided (st : KPState) (a b : IRI) : Bool :=
  (st.knownSups.getD a {}).contains b ||
  st.knownFalse.contains (a, b) ||
  match st.possSups.getD a none with
  | some ps => !ps.contains b
  | none => false

private def queryKPSat (idx : LocalityIndex) (o : Ontology) (namedClassSet : Std.HashSet IRI)
    (baseModel? : Option SROIQDModel) (tctx? : Option TBoxFastCtx) (c : IRI) :
    Option (Bool × List (IRI × List IRI)) :=
  match tctx?.bind (fun tctx => tryDecideSubViaTBox tctx c nothing) with
  | some (true, _) => some (true, [])
  | some (false, some (comp, sigCls)) => some (false, summarizeModel comp sigCls namedClassSet)
  | some (false, none) => some (false, [])
  | none =>
    let (mod, sig) := extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named c) (.named nothing)))
    (decideSubWithModel mod c nothing baseModel?).map fun (isUnsat, m?) =>
      if isUnsat then (true, [])
      else match m? with
        | some m => (false, summarizeModel m sig.cls namedClassSet)
        | none => (false, [])

private def queryKPSub (idx : LocalityIndex) (o : Ontology) (namedClassSet : Std.HashSet IRI)
    (baseModel? : Option SROIQDModel) (tctx? : Option TBoxFastCtx) (a b : IRI) :
    Option (Bool × List (IRI × List IRI)) :=
  match tctx?.bind (fun tctx => tryDecideSubViaTBox tctx a b) with
  | some (true, _) => some (true, [])
  | some (false, some (comp, sigCls)) => some (false, summarizeModel comp sigCls namedClassSet)
  | some (false, none) => some (false, [])
  | none =>
    let (mod, sig) := extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))
    (decideSubWithModel mod a b baseModel?).map fun (isSub, m?) =>
      if isSub then (true, [])
      else match m? with
        | some m => (false, summarizeModel m sig.cls namedClassSet)
        | none => (false, [])

private def sweepKPSat (satQuery : IRI → Option (Bool × List (IRI × List IRI))) :
    List IRI → KPState → Option KPState
  | [], st => some st
  | c :: rest, st =>
    if st.unsatSet.contains c || st.satSet.contains c then
      sweepKPSat satQuery rest st
    else
      (satQuery c).bind fun (isUnsat, summary) =>
        let st' := if isUnsat then st.markUnsat c
                   else (st.markSat c).mergeSummary summary
        sweepKPSat satQuery rest st'

private theorem sweepKPSat_append (satQuery : IRI → Option (Bool × List (IRI × List IRI)))
    (front rest : List IRI) (st : KPState) :
    sweepKPSat satQuery (front ++ rest) st =
      (sweepKPSat satQuery front st).bind (sweepKPSat satQuery rest) := by
  induction front generalizing st with
  | nil => simp [sweepKPSat]
  | cons c front ih =>
    simp only [List.cons_append, sweepKPSat]
    split
    · exact ih st
    · rw [Option.bind_assoc]
      apply Option.bind_congr
      rintro ⟨isUnsat, summary⟩ _
      exact ih _

private def lookupBatchAnswer {α β : Type} [BEq α]
    (query : α → β) (answers : List (α × β)) (key : α) : β :=
  match answers.lookup key with
  | some answer => answer
  | none => query key

private theorem lookupBatchAnswer_eq {α β : Type} [BEq α] [LawfulBEq α] (workers : Nat)
    (query : α → β) (gaps : List α) :
    lookupBatchAnswer query (mapIndependent workers (fun key => (key, query key)) gaps) = query := by
  funext key
  simp only [lookupBatchAnswer, mapIndependent_eq]
  split
  · rename_i ans hans
    obtain ⟨_, _, heq, _⟩ := List.lookup_eq_some_iff.mp hans
    have hm : (key, ans) ∈ gaps.map (fun k => (k, query k)) := by simp [heq]
    obtain ⟨_, _, h⟩ := List.mem_map.mp hm
    cases h; rfl
  · rfl

private def sweepKPSatBatched (workers chunkSize : Nat)
    (satQuery : IRI → Option (Bool × List (IRI × List IRI))) :
    Nat → List IRI → KPState → Option KPState
  | 0, rem, st => sweepKPSat satQuery rem st
  | _ + 1, [], st => some st
  | batches + 1, c :: rest, st => do
    let (batch, pending) := (c :: rest).splitAt chunkSize
    let gaps := batch.filter fun x => !st.unsatSet.contains x && !st.satSet.contains x
    -- Compute answers before passing the lookup closure to the sweep.
    let answers := mapIndependent workers (fun c => (c, satQuery c)) gaps
    let next ← sweepKPSat (lookupBatchAnswer satQuery answers) batch st
    sweepKPSatBatched workers chunkSize satQuery batches pending next

private theorem sweepKPSatBatched_eq (workers chunkSize : Nat)
    (satQuery : IRI → Option (Bool × List (IRI × List IRI)))
    (batches : Nat) (rem : List IRI) (st : KPState) :
    sweepKPSatBatched workers chunkSize satQuery batches rem st =
      sweepKPSat satQuery rem st := by
  induction batches generalizing rem st with
  | zero => rfl
  | succ batches ih =>
    cases rem with
    | nil => simp [sweepKPSatBatched, sweepKPSat]
    | cons c rest =>
      simp only [sweepKPSatBatched, List.splitAt_eq, lookupBatchAnswer_eq]
      conv =>
        rhs
        rw [← List.take_append_drop chunkSize (c :: rest), sweepKPSat_append]
      apply Option.bind_congr
      intro next _
      exact ih _ _

private def sweepKPSatParallel (workers : Nat)
    (satQuery : IRI → Option (Bool × List (IRI × List IRI)))
    (rem : List IRI) (st : KPState) : Option KPState :=
  if workers ≤ 1 then sweepKPSat satQuery rem st
  else
    let chunkSize := max (workers * 4) 32
    sweepKPSatBatched workers chunkSize satQuery ((rem.length + chunkSize - 1) / chunkSize) rem st

private theorem sweepKPSatParallel_eq (workers : Nat)
    (satQuery : IRI → Option (Bool × List (IRI × List IRI)))
    (rem : List IRI) (st : KPState) :
    sweepKPSatParallel workers satQuery rem st = sweepKPSat satQuery rem st := by
  unfold sweepKPSatParallel
  split
  · rfl
  · exact sweepKPSatBatched_eq ..

private def verifyKPPairs (query : IRI → IRI → Option (Bool × List (IRI × List IRI))) :
    List (IRI × IRI) → KPState → Option KPState
  | [], st => some st
  | (a, b) :: rest, st =>
    if st.isPairDecided a b then
      verifyKPPairs query rest st
    else
      (query a b).bind fun (isSub, summary) =>
        let st' := if isSub then st.addTrue a b
                   else (st.addFalse a b).mergeSummary summary
        verifyKPPairs query rest st'

private theorem verifyKPPairs_append (query : IRI → IRI → Option (Bool × List (IRI × List IRI)))
    (front rest : List (IRI × IRI)) (st : KPState) :
    verifyKPPairs query (front ++ rest) st =
      (verifyKPPairs query front st).bind (verifyKPPairs query rest) := by
  induction front generalizing st with
  | nil => simp [verifyKPPairs]
  | cons p front ih =>
    rcases p with ⟨a, b⟩
    simp only [List.cons_append, verifyKPPairs]
    split
    · exact ih st
    · rw [Option.bind_assoc]
      apply Option.bind_congr
      rintro ⟨isSub, summary⟩ _
      exact ih _

private def verifyKPPairsBatched (workers chunkSize : Nat)
    (query : IRI → IRI → Option (Bool × List (IRI × List IRI))) :
    Nat → List (IRI × IRI) → KPState → Option KPState
  | 0, pairs, st => verifyKPPairs query pairs st
  | _ + 1, [], st => some st
  | batches + 1, p :: rest, st => do
    let (batch, pending) := (p :: rest).splitAt chunkSize
    let gaps := batch.filter fun (a, b) => !st.isPairDecided a b
    let pairQuery := fun (p : IRI × IRI) => query p.1 p.2
    let answers := mapIndependent workers (fun p => (p, pairQuery p)) gaps
    let next ← verifyKPPairs (fun a b => lookupBatchAnswer pairQuery answers (a, b)) batch st
    verifyKPPairsBatched workers chunkSize query batches pending next

private theorem verifyKPPairsBatched_eq (workers chunkSize : Nat)
    (query : IRI → IRI → Option (Bool × List (IRI × List IRI)))
    (batches : Nat) (pairs : List (IRI × IRI)) (st : KPState) :
    verifyKPPairsBatched workers chunkSize query batches pairs st =
      verifyKPPairs query pairs st := by
  induction batches generalizing pairs st with
  | zero => rfl
  | succ batches ih =>
    cases pairs with
    | nil => simp [verifyKPPairsBatched, verifyKPPairs]
    | cons p rest =>
      simp only [verifyKPPairsBatched, List.splitAt_eq, lookupBatchAnswer_eq]
      conv =>
        rhs
        rw [← List.take_append_drop chunkSize (p :: rest), verifyKPPairs_append]
      apply Option.bind_congr
      intro next _
      exact ih _ _

private def verifyKPPairsParallel (workers : Nat)
    (query : IRI → IRI → Option (Bool × List (IRI × List IRI)))
    (pairs : List (IRI × IRI)) (st : KPState) : Option KPState :=
  if workers ≤ 1 then verifyKPPairs query pairs st
  else
    let chunkSize := max (workers * 4) 32
    verifyKPPairsBatched workers chunkSize query ((pairs.length + chunkSize - 1) / chunkSize) pairs st

private theorem verifyKPPairsParallel_eq (workers : Nat)
    (query : IRI → IRI → Option (Bool × List (IRI × List IRI)))
    (pairs : List (IRI × IRI)) (st : KPState) :
    verifyKPPairsParallel workers query pairs st = verifyKPPairs query pairs st := by
  unfold verifyKPPairsParallel
  split
  · rfl
  · exact verifyKPPairsBatched_eq ..

/-- Build the `ClassHierarchy` from the finalized `KPState` in `O(|C| · deg²)` without
    scanning `|C|²` pairs. -/
private def buildHierarchyFromKP (namedClasses : List IRI) (st : KPState) : ClassHierarchy := Id.run do
  let unsat := namedClasses.filter fun c => c == nothing || st.unsatSet.contains c
  let unsatSet : Std.HashSet IRI := unsat.foldl (fun s c => s.insert c) {}
  let satClasses := namedClasses.filter fun c => !unsatSet.contains c
  let mut subsArr : Array (IRI × IRI) := #[]
  for a in namedClasses do
    if unsatSet.contains a then
      for b in namedClasses do
        subsArr := subsArr.push (a, b)
    else
      let ks := st.knownSups.getD a {}
      for b in ks do
        subsArr := subsArr.push (a, b)
  let mut seenEq : Std.HashSet IRI := {}
  let mut eqGroups : Array (List IRI) := #[]
  for c in satClasses do
    if !seenEq.contains c then
      let ksC := st.knownSups.getD c {}
      let grp := ksC.toList.filter fun d =>
        !unsatSet.contains d && (st.knownSups.getD d {}).contains c
      let grp' := if grp.contains c then grp else c :: grp
      for d in grp' do
        seenEq := seenEq.insert d
      eqGroups := eqGroups.push grp'
  let mut dpArr : Array (IRI × List IRI) := #[]
  for c in satClasses do
    let ksC := st.knownSups.getD c {}
    let strictSups := ksC.toList.filter fun p =>
      p != c && !unsatSet.contains p && !(st.knownSups.getD p {}).contains c
    let direct := strictSups.filter fun p =>
      !strictSups.any fun mid =>
        mid != p && (st.knownSups.getD mid {}).contains p && !(st.knownSups.getD p {}).contains mid
    let parents := if direct.isEmpty then [thing] else direct
    dpArr := dpArr.push (c, parents)
  return {
    consistent := true
    classes := namedClasses
    unsatisfiable := unsat
    subsumptions := subsArr.toList
    equivalences := eqGroups.toList
    directParents := dpArr.toList
  }

/-- Sort classes leaves-first (fewest known subclasses first) so satisfiability checks on
    specific classes simultaneously certify all their superclasses via upward propagation
    and verified model harvesting. -/
private def orderLeavesFirst (namedClasses : List IRI) (st : KPState) : List IRI :=
  let arr := namedClasses.toArray.map fun c => ((st.knownSubs.getD c {}).size, c)
  let sorted := arr.qsort fun a b => a.1 < b.1
  sorted.toList.map Prod.snd

/-- Try to cover many classes in each checked model. When a verified base ABox model is
    available on a larger ABox, build lightweight TBox-only components via
    `counterWithoutIndividuals` and kernel-verify them appended onto the base model.
    A failed batch contributes no facts; the ordinary satisfiability sweep handles every
    uncovered class. -/
private def seedKPFromBatchModels (o : Ontology) (namedClasses : List IRI)
    (namedClassSet : Std.HashSet IRI) (numWorkers : Nat) (order : List IRI)
    (baseModel? : Option SROIQDModel) (st : KPState) : KPState :=
  if o.length > 10000 && baseModel?.isNone then st
  else
  let gaps := (order.filter fun c => !st.satSet.contains c && !st.unsatSet.contains c).toArray
  let batchSize := 64
  if gaps.size < batchSize then st
  else
    match normalizeWithDefs o with
    | none => st
    | some (_, p) =>
      if p.root != .top || !canHarvestStandardModel p || !checkTableauRolesOkFast p then st
      else
        let batches := List.range ((gaps.size + batchSize - 1) / batchSize)
        match baseModel? with
        | some base =>
          if p.classAssertions.length ≥ 64 then
            let core := counterWithoutIndividuals p
            let comps := (mapIndependent numWorkers (fun i =>
              let seed := (gaps.extract (i * batchSize) ((i + 1) * batchSize)).toList
              (proposeSeededCanonicalModel core (seed.map Concept.atom)).map Subtype.val) batches).filterMap id
            let verified := checkComponentBatches p base comps numWorkers
            let summaries := mapIndependent numWorkers (fun m =>
              summarizeModel m namedClasses namedClassSet) verified
            summaries.foldl (fun acc summary => acc.mergeSummary summary) st
          else
            let summaries := mapIndependent numWorkers (fun i =>
              let seed := (gaps.extract (i * batchSize) ((i + 1) * batchSize)).toList
              match proposeSeededCanonicalModel p (seed.map Concept.atom) with
              | some m => summarizeModel m.val namedClasses namedClassSet
              | none => []) batches
            summaries.foldl (fun acc summary => acc.mergeSummary summary) st
        | none =>
          let summaries := mapIndependent numWorkers (fun i =>
            let seed := (gaps.extract (i * batchSize) ((i + 1) * batchSize)).toList
            match proposeSeededCanonicalModel p (seed.map Concept.atom) with
            | some m => summarizeModel m.val namedClasses namedClassSet
            | none => []) batches
          summaries.foldl (fun acc summary => acc.mergeSummary summary) st

/-- Collect the exact remaining `(a, b)` candidates where `b ∈ P(a) \ K(a)` across all
    satisfiable named classes. -/
private def collectKPCandidates (namedClasses : List IRI) (st : KPState) : List (IRI × IRI) := Id.run do
  let mut out : Array (IRI × IRI) := #[]
  for a in namedClasses do
    if a != nothing && !st.unsatSet.contains a then
      let ps := (st.possSups.getD a none).getD namedClasses
      let ks := st.knownSups.getD a {}
      for b in ps do
        if b != a && b != thing && b != nothing && !st.unsatSet.contains b &&
            !ks.contains b && !st.knownFalse.contains (a, b) then
          out := out.push (a, b)
  return out.toList

private def classifyEnhancedRuntimeCore (o : Ontology) (namedClasses : List IRI)
    (numWorkers : Nat) (initModel? : Option SROIQDModel) : Option ClassHierarchy :=
  let idx := LocalityIndex.build o
  let consistent? : Option Bool :=
    if initModel?.isSome then some true
    else fastConsistencyCheck (extractBotModuleWithIndex idx o Sig.empty).1
  consistent?.bind fun consistent =>
    if !consistent then
      some {
        consistent := false
        classes := namedClasses
        unsatisfiable := namedClasses
        subsumptions := []
        equivalences := []
        directParents := []
      }
    else
      let namedClassSet : Std.HashSet IRI := namedClasses.foldl (fun s c => s.insert c) {}
      let (cb, cbPartialSummary) :=
        FastCB.runFastCBWithPartialModel o idx namedClasses namedClassSet numWorkers
      let st0 := (KPState.init o namedClasses namedClassSet cb.subs cb.unsats).mergeSummary cbPartialSummary
      let stInit := match initModel? with
        | some m0 => st0.mergeSummary (summarizeModel m0 namedClasses namedClassSet)
        | none => st0
      let satOrder := orderLeavesFirst namedClasses stInit
      let tctx? : Option TBoxFastCtx := match initModel? with
        | some _ => (normalizeWithDefs o).bind fun (_, p) => buildTBoxFastCtx o p
        | none => none
      let stSeeded := seedKPFromBatchModels o namedClasses namedClassSet numWorkers satOrder initModel? stInit
      (sweepKPSatParallel numWorkers
          (queryKPSat idx o namedClassSet initModel? tctx?) satOrder stSeeded).bind fun st1 =>
        let cands := collectKPCandidates namedClasses st1
        (verifyKPPairsParallel numWorkers
            (queryKPSub idx o namedClassSet initModel? tctx?) cands st1).map fun st2 =>
          buildHierarchyFromKP namedClasses st2

private def collectOutputClasses (o : Ontology) (decls : List FunctionalSyntax.EntityDecl)
    (auxiliaryClass? : Option IRI) : List IRI :=
  let classes := collectNamedClasses o decls
  match auxiliaryClass? with
  | none => classes
  | some aux => classes.filter (· != aux)

/-- Fast hybrid runtime TBox classifier reusing an optional already-verified full model `initModel?`.
    `auxiliaryClass?` restricts the output signature. Its axioms still participate in reasoning.
    1. Pure $\mathcal{EL}^{++}$ ontologies: parallel integer-interned single-model
       `FastEL.classifyFastELToHierarchy` (falling back to `classifyELSinglePass`
       only if built-in top/bottom object properties appear).
    2. General $\mathcal{SROIQ}(\mathcal{D})$ ontologies: pre-built `FastLocality.LocalityIndex`,
       told subsumers + transitive closure, initial verified-model seeding, parallel
       sat/unsat sweep with per-module countermodel harvesting, downward told-disjointness
       closure, and parallel Enhanced Traversal with per-pair countermodel harvesting. -/
def classifyOntologyFastWithModelRuntime (o : Ontology)
    (decls : List FunctionalSyntax.EntityDecl := [])
    (numWorkers : Nat := 8) (initModel? : Option SROIQDModel := none)
    (auxiliaryClass? : Option IRI := none) :
    Option ClassHierarchy :=
  let namedClasses := collectOutputClasses o decls auxiliaryClass?
  let fp := profileOntology o
  let enhanced := fun () =>
    let m0? := match initModel? with
      | some m => some m
      | none =>
        if o.length > 10000 && !o.any isABoxAxiomFast then none
        else (proposeVerifiedModel o).map Prod.fst
    classifyEnhancedRuntimeCore o namedClasses numWorkers m0?
  if fp.leastFragment == .el then
    match normalizeEL o with
    | some elAxs =>
      if checkELRegular elAxs then
        match FastEL.classifyFastELToHierarchy elAxs namedClasses numWorkers with
        | some h => some h
        | none =>
          match classifyELSinglePass elAxs namedClasses with
          | some h => some h
          | none => enhanced ()
      else enhanced ()
    | none => enhanced ()
  else
    if initModel?.isNone then
      match FastCB.classifyFastCB o namedClasses numWorkers with
      | some h => some h
      | none => enhanced ()
    else enhanced ()

def classifyOntologyFastRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := [])
    (numWorkers : Nat := 8) (auxiliaryClass? : Option IRI := none) :
    Option ClassHierarchy :=
  classifyOntologyFastWithModelRuntime o decls numWorkers none auxiliaryClass?

theorem classifyOntologyFastRuntime_nonEL_workers_eq (o : Ontology)
    (decls : List FunctionalSyntax.EntityDecl)
    (h : (profileOntology o).leastFragment ≠ .el) (workers : Nat)
    (auxiliaryClass? : Option IRI := none) :
    classifyOntologyFastRuntime o decls workers auxiliaryClass? =
      classifyOntologyFastRuntime o decls 1 auxiliaryClass? := by
  simp only [classifyOntologyFastRuntime, classifyOntologyFastWithModelRuntime,
    classifyEnhancedRuntimeCore, beq_iff_eq, h, ↓reduceIte,
    FastCB.classifyFastCB_workers_eq,
    FastCB.runFastCBWithPartialModel_workers_eq,
    seedKPFromBatchModels, checkComponentBatches, mapIndependent_eq,
    sweepKPSatParallel_eq, verifyKPPairsParallel_eq]

/-- Result of deterministic monotone positive ABox forward chaining:
    every type, object edge, and data value recorded is provably entailed by `o`. -/
structure PositiveABoxClosure where
  types : Std.HashMap IRI (Std.HashSet IRI) := {}
  edges : Std.HashSet (IRI × IRI × IRI) := {}
  data : Std.HashMap (IRI × IRI) (List Datatypes.Value) := {}

private def walkABoxChainTargets (outAdj inAdj : Std.HashMap (IRI × IRI) (List IRI))
    (x : IRI) : List Sabrina.ALC.OrientedRole → List IRI
  | [] => [x]
  | r :: rs =>
    (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []).flatMap fun y =>
      walkABoxChainTargets outAdj inAdj y rs

private def hasPosConclusion : Concept → Bool
  | .lit _ true | .all .. | .self _ true | .dataValue _ _ true => true
  | .conj a b => hasPosConclusion a || hasPosConclusion b
  | _ => false

private def collectPosLeaves : Concept → List Concept
  | .conj a b => collectPosLeaves a ++ collectPosLeaves b
  | c => [c]

private partial def posHoldsABox
    (types : Std.HashMap IRI (Std.HashSet IRI))
    (outAdj inAdj : Std.HashMap (IRI × IRI) (List IRI))
    (edgeSet : Std.HashSet (IRI × IRI × IRI))
    (dataMap : Std.HashMap (IRI × IRI) (List Datatypes.Value))
    (a : IRI) : Concept → Bool
  | .top => true
  | .lit cls true => (types.getD a {}).contains cls
  | .nom (.named j) true => j == a
  | .self r true => edgeSet.contains (r.1, a, a)
  | .conj c1 c2 =>
    posHoldsABox types outAdj inAdj edgeSet dataMap a c1 &&
    posHoldsABox types outAdj inAdj edgeSet dataMap a c2
  | .disj c1 c2 =>
    posHoldsABox types outAdj inAdj edgeSet dataMap a c1 ||
    posHoldsABox types outAdj inAdj edgeSet dataMap a c2
  | .some r body =>
    (if r.2 then inAdj.getD (r.1, a) [] else outAdj.getD (r.1, a) []).any fun b =>
      posHoldsABox types outAdj inAdj edgeSet dataMap b body
  | .min 0 _ _ => true
  | .min 1 r body =>
    (if r.2 then inAdj.getD (r.1, a) [] else outAdj.getD (r.1, a) []).any fun b =>
      posHoldsABox types outAdj inAdj edgeSet dataMap b body
  | .dataSome dp dr =>
    (dataMap.getD (dp, a) []).any fun v => SROIQD.Termination.evalDataRange dr v
  | .dataMin 0 _ _ => true
  | .dataMin 1 dp dr =>
    (dataMap.getD (dp, a) []).any fun v => SROIQD.Termination.evalDataRange dr v
  | .dataValue dp l true =>
    match Datatypes.decodeLiteral l with
    | some v => (dataMap.getD (dp, a) []).contains v
    | none => false
  | _ => false

/-- Deterministic monotone positive ABox closure over `p` and `superMap`:
    propagates asserted types, superclasses, object-property hierarchy/inverses/chains/reflexivity,
    data-property hierarchy, domains, ranges, universal restrictions along proved edges,
    defined-class equivalences, and anchored SWRL rules with zero closed-world assumptions. -/
def computePositiveABoxClosure (p : Problem) (superMap : Std.HashMap IRI (List IRI))
    (inds : List IRI) : PositiveABoxClosure := Id.run do
  let mut types : Std.HashMap IRI (Std.HashSet IRI) := {}
  let mut classInds : Std.HashMap IRI (List IRI) := {}
  let mut allOnInd : Std.HashMap (Sabrina.ALC.OrientedRole × IRI) (List Concept) := {}
  let mut edgeSet : Std.HashSet (IRI × IRI × IRI) := {}
  let mut outAdj : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut inAdj : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut byRole : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut roleSources : Std.HashMap Sabrina.ALC.OrientedRole (List IRI) := {}
  let mut roleSourceSet : Std.HashSet (Sabrina.ALC.OrientedRole × IRI) := {}
  let mut dataMap : Std.HashMap (IRI × IRI) (List Datatypes.Value) := {}
  let mut dataSources : Std.HashMap IRI (List IRI) := {}
  let mut dataSourceSet : Std.HashSet (IRI × IRI) := {}
  let mut pending : Array (IRI × Concept) := #[]
  let mut edgesChanged := false
  let mut dataChanged := false
  let mut factsChanged := false
  -- Pre-index positive-conclusion GCIs by LHS anchor
  let mut topAllByRole : Std.HashMap Sabrina.ALC.OrientedRole (List Concept) := {}
  let mut topOtherGCIs : Array Concept := #[]
  let mut classGCIs : Std.HashMap IRI (List Inclusion) := {}
  let mut roleGCIs : Std.HashMap Sabrina.ALC.OrientedRole (List Inclusion) := {}
  let mut nomGCIs : Std.HashMap IRI (List Inclusion) := {}
  let mut dataGCIs : Std.HashMap IRI (List Inclusion) := {}
  let mut unanchoredGCIs : Array Inclusion := #[]
  for q in p.tbox do
    if !hasPosConclusion q.sup then continue
    if q.sub == .top then
      for leaf in collectPosLeaves q.sup do
        match leaf with
        | .all r body =>
          if hasPosConclusion body then
            topAllByRole := topAllByRole.insert r (body :: topAllByRole.getD r [])
        | c =>
          if hasPosConclusion c then topOtherGCIs := topOtherGCIs.push c
    else
      let leaves := collectPosLeaves q.sub
      let mut anchored := false
      for l in leaves do
        if !anchored then
          match l with
          | .lit cls true =>
            classGCIs := classGCIs.insert cls (q :: classGCIs.getD cls [])
            anchored := true
          | _ => pure ()
      if !anchored then
        for l in leaves do
          if !anchored then
            match l with
            | .some r _ | .min 1 r _ =>
              roleGCIs := roleGCIs.insert r (q :: roleGCIs.getD r [])
              anchored := true
            | .nom (.named j) true =>
              nomGCIs := nomGCIs.insert j (q :: nomGCIs.getD j [])
              anchored := true
            | .dataSome dp _ | .dataMin 1 dp _ | .dataValue dp _ true =>
              dataGCIs := dataGCIs.insert dp (q :: dataGCIs.getD dp [])
              anchored := true
            | _ => pure ()
      if !anchored then
        unanchoredGCIs := unanchoredGCIs.push q
  -- Seed initial facts from p
  for (ia, c) in p.classAssertions do
    if let .named a := ia then
      pending := pending.push (a, c)
  for c in topOtherGCIs do
    for a in inds do
      pending := pending.push (a, c)
  let addEdge (es : Std.HashSet (IRI × IRI × IRI))
      (oa ia : Std.HashMap (IRI × IRI) (List IRI))
      (br : Std.HashMap IRI (List (IRI × IRI)))
      (rs : Std.HashMap Sabrina.ALC.OrientedRole (List IRI))
      (rss : Std.HashSet (Sabrina.ALC.OrientedRole × IRI))
      (r a b : IRI) :=
    if es.contains (r, a, b) then (es, oa, ia, br, rs, rss, false)
    else
      let (rs1, rss1) :=
        if rss.contains ((r, false), a) then (rs, rss)
        else (rs.insert (r, false) (a :: rs.getD (r, false) []), rss.insert ((r, false), a))
      let (rs2, rss2) :=
        if rss1.contains ((r, true), b) then (rs1, rss1)
        else (rs1.insert (r, true) (b :: rs1.getD (r, true) []), rss1.insert ((r, true), b))
      (es.insert (r, a, b),
       oa.insert (r, a) (b :: oa.getD (r, a) []),
       ia.insert (r, b) (a :: ia.getD (r, b) []),
       br.insert r ((a, b) :: br.getD r []),
       rs2, rss2, true)
  for (r, ia, ib) in p.objAssertions do
    if let (.named a, .named b) := (ia, ib) then
      let (es', oa', ia', br', rs', rss', ch) := addEdge edgeSet outAdj inAdj byRole roleSources roleSourceSet r a b
      edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'; roleSources := rs'; roleSourceSet := rss'
      if ch then edgesChanged := true
  for r in p.chars.reflexive do
    for a in inds do
      let (es', oa', ia', br', rs', rss', ch) := addEdge edgeSet outAdj inAdj byRole roleSources roleSourceSet r a a
      edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'; roleSources := rs'; roleSourceSet := rss'
      if ch then edgesChanged := true
  for (dp, ia, lit) in p.dataAssertions do
    if let (.named a, some v) := (ia, Datatypes.decodeLiteral lit) then
      let cur := dataMap.getD (dp, a) []
      if !cur.contains v then
        dataMap := dataMap.insert (dp, a) (v :: cur)
        dataChanged := true
        if !dataSourceSet.contains (dp, a) then
          dataSourceSet := dataSourceSet.insert (dp, a)
          dataSources := dataSources.insert dp (a :: dataSources.getD dp [])
  -- Close edges and fire topAllGCIs / allOnInd on newly added edges
  for _iter in [:24] do
    -- 1. Close edges under rules and chains
    if edgesChanged then
      edgesChanged := false
      let mut eLoop := true
      let mut eIter := 0
      while eLoop && eIter < 16 do
        eLoop := false
        eIter := eIter + 1
        let mut newEdges : Array (IRI × IRI × IRI) := #[]
        for (r, t) in p.rules do
          for (u, v) in byRole.getD r.1 [] do
            let (x, y) := if r.2 then (v, u) else (u, v)
            let (rn, a, b) := if t.2 then (t.1, y, x) else (t.1, x, y)
            if !edgeSet.contains (rn, a, b) then newEdges := newEdges.push (rn, a, b)
        for c in p.chains do
          match c.body with
          | [] =>
            for a in inds do
              if !edgeSet.contains (c.head, a, a) then newEdges := newEdges.push (c.head, a, a)
          | r0 :: rs =>
            for (u, v) in byRole.getD r0.1 [] do
              let (x, mid) := if r0.2 then (v, u) else (u, v)
              for y in walkABoxChainTargets outAdj inAdj mid rs do
                if !edgeSet.contains (c.head, x, y) then newEdges := newEdges.push (c.head, x, y)
        for (rn, a, b) in newEdges do
          let (es', oa', ia', br', rs', rss', ch) := addEdge edgeSet outAdj inAdj byRole roleSources roleSourceSet rn a b
          edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'; roleSources := rs'; roleSourceSet := rss'
          if ch then
            eLoop := true
            factsChanged := true
      -- Fire topAllByRole and allOnInd across edges
      for (r, bodies) in topAllByRole do
        for (u, v) in byRole.getD r.1 [] do
          let target := if r.2 then u else v
          for body in bodies do
            pending := pending.push (target, body)
      for ((r, a), bodies) in allOnInd do
        let nbs := if r.2 then inAdj.getD (r.1, a) [] else outAdj.getD (r.1, a) []
        for b in nbs do
          for body in bodies do
            pending := pending.push (b, body)
    -- 2. Close data under p.subData
    if dataChanged then
      dataChanged := false
      let mut dLoop := true
      let mut dIter := 0
      while dLoop && dIter < p.subData.length + 2 do
        dLoop := false
        dIter := dIter + 1
        let mut addD : Array (IRI × IRI × Datatypes.Value) := #[]
        for (r, t) in p.subData do
          for a in dataSources.getD r [] do
            let curT := dataMap.getD (t, a) []
            for v in dataMap.getD (r, a) [] do
              if !curT.contains v then
                addD := addD.push (t, a, v)
        for (t, a, v) in addD do
          let curT := dataMap.getD (t, a) []
          if !curT.contains v then
            dataMap := dataMap.insert (t, a) (v :: curT)
            if !dataSourceSet.contains (t, a) then
              dataSourceSet := dataSourceSet.insert (t, a)
              dataSources := dataSources.insert t (a :: dataSources.getD t [])
            dLoop := true
            factsChanged := true
    -- 3. Drain pending positive conclusions
    let mut pIdx := 0
    while h : pIdx < pending.size do
      let (a, c) := pending[pIdx]
      pIdx := pIdx + 1
      for leaf in collectPosLeaves c do
        match leaf with
        | .lit cls true =>
          let mut ta := types.getD a {}
          if !ta.contains cls then
            ta := ta.insert cls
            classInds := classInds.insert cls (a :: classInds.getD cls [])
            factsChanged := true
            for sup in superMap.getD cls [] do
              if !ta.contains sup then
                ta := ta.insert sup
                classInds := classInds.insert sup (a :: classInds.getD sup [])
            types := types.insert a ta
        | .all r body =>
          let curBodies := allOnInd.getD (r, a) []
          if hasPosConclusion body && !curBodies.contains body then
            allOnInd := allOnInd.insert (r, a) (body :: curBodies)
            let nbs := if r.2 then inAdj.getD (r.1, a) [] else outAdj.getD (r.1, a) []
            for b in nbs do
              pending := pending.push (b, body)
        | .self r true =>
          let (es', oa', ia', br', rs', rss', ch) := addEdge edgeSet outAdj inAdj byRole roleSources roleSourceSet r.1 a a
          edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'; roleSources := rs'; roleSourceSet := rss'
          if ch then edgesChanged := true; factsChanged := true
        | .dataValue dp l true =>
          if let some v := Datatypes.decodeLiteral l then
            let cur := dataMap.getD (dp, a) []
            if !cur.contains v then
              dataMap := dataMap.insert (dp, a) (v :: cur)
              if !dataSourceSet.contains (dp, a) then
                dataSourceSet := dataSourceSet.insert (dp, a)
                dataSources := dataSources.insert dp (a :: dataSources.getD dp [])
              dataChanged := true; factsChanged := true
        | _ => pure ()
    pending := #[]
    if edgesChanged || dataChanged then continue
    -- 4. Fire anchored positive-LHS GCIs
    let mut firedGCI := false
    for (cls, cands) in classInds do
      for q in classGCIs.getD cls [] do
        for a in cands do
          if posHoldsABox types outAdj inAdj edgeSet dataMap a q.sub then
            let already := match q.sup with
              | .lit supC true => (types.getD a {}).contains supC
              | _ => false
            if !already then
              pending := pending.push (a, q.sup)
              firedGCI := true
    for (r, cands) in roleSources do
      for q in roleGCIs.getD r [] do
        for a in cands do
          if posHoldsABox types outAdj inAdj edgeSet dataMap a q.sub then
            let already := match q.sup with
              | .lit supC true => (types.getD a {}).contains supC
              | _ => false
            if !already then
              pending := pending.push (a, q.sup)
              firedGCI := true
    for (j, qs) in nomGCIs do
      for q in qs do
        if posHoldsABox types outAdj inAdj edgeSet dataMap j q.sub then
          let already := match q.sup with
            | .lit supC true => (types.getD j {}).contains supC
            | _ => false
          if !already then
            pending := pending.push (j, q.sup)
            firedGCI := true
    for (dp, cands) in dataSources do
      for q in dataGCIs.getD dp [] do
        for a in cands do
          if posHoldsABox types outAdj inAdj edgeSet dataMap a q.sub then
            let already := match q.sup with
              | .lit supC true => (types.getD a {}).contains supC
              | _ => false
            if !already then
              pending := pending.push (a, q.sup)
              firedGCI := true
    for q in unanchoredGCIs do
      for a in inds do
        if posHoldsABox types outAdj inAdj edgeSet dataMap a q.sub then
          let already := match q.sup with
            | .lit supC true => (types.getD a {}).contains supC
            | _ => false
          if !already then
            pending := pending.push (a, q.sup)
            firedGCI := true
    if !firedGCI && !factsChanged then break
    factsChanged := false
  return { types := types, edges := edgeSet, data := dataMap }

/-- Pre-indexed ABox ego-neighborhood extractor (`o_ego ⊆ o`):
    any entailment proved on `o_ego` transfers to `o` by monotonicity of OWL 2 Direct Semantics. -/
structure ABoxEgoIndex where
  tboxAxioms : List Axiom
  aboxAxioms : Array (Axiom × List IRI)
  aboxByInd : Std.HashMap IRI (List Nat)
  indAdj : Std.HashMap IRI (List IRI)

private def isPureABoxAxiom : Axiom → Option (List IRI)
  | .classAssertion _ (.named a) => some [a]
  | .objectAssertion _ (.named a) (.named b) | .negativeObjectAssertion _ (.named a) (.named b) => some [a, b]
  | .dataAssertion _ (.named a) _ | .negativeDataAssertion _ (.named a) _ => some [a]
  | .sameIndividuals inds =>
    if inds.all (fun | .named _ => true | _ => false) then
      some (inds.filterMap fun | .named a => some a | _ => none)
    else none
  | .differentIndividuals inds =>
    if inds.all (fun | .named _ => true | _ => false) then
      some (inds.filterMap fun | .named a => some a | _ => none)
    else none
  | _ => none

def ABoxEgoIndex.build (o : Ontology) : ABoxEgoIndex := Id.run do
  let mut tbox : Array Axiom := #[]
  let mut abox : Array (Axiom × List IRI) := #[]
  let mut byInd : Std.HashMap IRI (List Nat) := {}
  let mut adj : Std.HashMap IRI (List IRI) := {}
  for ax in o do
    match isPureABoxAxiom ax with
    | none => tbox := tbox.push ax
    | some inds =>
      let idx := abox.size
      abox := abox.push (ax, inds)
      for a in inds do
        byInd := byInd.insert a (idx :: byInd.getD a [])
      match ax with
      | .objectAssertion _ (.named a) (.named b)
      | .negativeObjectAssertion _ (.named a) (.named b) =>
        if a != b then
          adj := adj.insert a (b :: adj.getD a [])
          adj := adj.insert b (a :: adj.getD b [])
      | .sameIndividuals _ =>
        for a in inds do
          for b in inds do
            if a != b then adj := adj.insert a (b :: adj.getD a [])
      | _ => pure ()
  return { tboxAxioms := tbox.toList, aboxAxioms := abox, aboxByInd := byInd, indAdj := adj }

/-- Extract a sound subset `o_ego ⊆ o` keeping the full TBox/RBox plus ABox assertions
    within a bounded 2-hop ego-neighborhood of `seedInds` (skipping expansion through
    high-degree hubs with > 16 neighbors so the subset stays small). -/
def ABoxEgoIndex.egoOntology (eidx : ABoxEgoIndex) (seedInds : List IRI) : Ontology := Id.run do
  let mut ego : Std.HashSet IRI := {}
  let mut hop1 : Array IRI := #[]
  for s in seedInds do
    if !ego.contains s then
      ego := ego.insert s
      hop1 := hop1.push s
  let mut hop2 : Array IRI := #[]
  for u in hop1 do
    let nbs := eidx.indAdj.getD u []
    if nbs.length ≤ 32 then
      for v in nbs do
        if !ego.contains v then
          ego := ego.insert v
          hop2 := hop2.push v
  for u in hop2 do
    let nbs := eidx.indAdj.getD u []
    if nbs.length ≤ 16 then
      for v in nbs do
        if !ego.contains v then
          ego := ego.insert v
  let mut seenAx : Std.HashSet Nat := {}
  let mut localAbox : Array Axiom := #[]
  for a in ego do
    for idx in eidx.aboxByInd.getD a [] do
      if !seenAx.contains idx then
        seenAx := seenAx.insert idx
        if let some (ax, inds) := eidx.aboxAxioms[idx]? then
          if inds.all (ego.contains ·) then
            localAbox := localAbox.push ax
  return eidx.tboxAxioms ++ localAbox.toList

/-- Fast hash-indexed direct-type computation (`O(|types|²)` with `O(1)` lookup). -/
def computeDirectTypesFast (types : List IRI) (subSet : Std.HashSet (IRI × IRI)) : List IRI :=
  let strictSub (a b : IRI) : Bool := subSet.contains (a, b) && !subSet.contains (b, a)
  types.filter fun c => !types.any fun moreSpec => strictSub moreSpec c

/-- Realize an ABox using the hierarchy and an optional kernel-verified full model `m?`:
    1. Deterministic positive ABox closure (`computePositiveABoxClosure`) derives all
       domain/range, superclass, role-chain, defined-class, universal, and SWRL entailments.
    2. Any class false at `m.indVal (.named ind)` in a kernel-verified model `m ⊨ o` is
       soundly pruned in O(1) without a tableau query (scanning only `worldAtoms[w]`).
    3. Multi-round soft negative countermodel refutation (`proposeSoftIndividualModel`)
       soundly prunes non-entailed disjunctive candidates across all individuals at once.
    4. Remaining candidates try a local 2-hop ego-neighborhood monotonicity fast path
       before falling back to full ⊥-local module verification in parallel. -/
def realizeFromHierarchyWithModelRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl)
    (hier : ClassHierarchy) (numWorkers : Nat := 8) (verifiedModel? : Option SROIQDModel := none)
    (auxiliaryClass? : Option IRI := none) (verifiedProblem? : Option Problem := none) :
    Option RealizationResult :=
  let namedClasses := collectOutputClasses o decls auxiliaryClass?
  let namedInds := collectNamedIndividuals o decls
  if !hier.consistent then
    some { consistent := false, individuals := namedInds, entries := [] }
  else
    let idx := LocalityIndex.build o
    let subSet := FastClassification.setOfPairs hier.subsumptions
    let superMap : Std.HashMap IRI (List IRI) := Id.run do
      let mut m : Std.HashMap IRI (List IRI) := {}
      for (a, b) in hier.subsumptions do
        m := m.insert a (b :: m.getD a [])
      return m
    let namedClassSet : Std.HashSet IRI := namedClasses.foldl (fun s c => s.insert c) {}
    let m? := match verifiedModel? with
      | some m => some m
      | none => (proposeVerifiedModel o).map Prod.fst
    let p? := match verifiedProblem? with
      | some p => some p
      | none => if m?.isSome then (normalizeWithDefs o).map Prod.snd else none
    let entailedByInd : Std.HashMap IRI (Std.HashSet IRI) :=
      match p? with
      | some p =>
        if canHarvestStandardModel p then
          (computePositiveABoxClosure p superMap namedInds).types
        else Id.run do
          let mut m : Std.HashMap IRI (Std.HashSet IRI) := {}
          for ax in o do
            if let .classAssertion (.named c) (.named ind) := ax then
              let mut s := (m.getD ind {}).insert c
              for sup in superMap.getD c [] do s := s.insert sup
              m := m.insert ind s
          return m
      | none => Id.run do
        let mut m : Std.HashMap IRI (Std.HashSet IRI) := {}
        for ax in o do
          if let .classAssertion (.named c) (.named ind) := ax then
            let mut s := (m.getD ind {}).insert c
            for sup in superMap.getD c [] do s := s.insert sup
            m := m.insert ind s
        return m
    let midx? : Option (Sigma fun m => ModelIndex m × Array (List IRI)) :=
      m?.map fun m =>
        let midx := ModelIndex.build m
        let worldAtoms : Array (List IRI) := Id.run do
          let mut arr : Array (List IRI) := Array.replicate (m.graph.additionalWorlds + 1) []
          for (c, w) in m.graph.atoms do
            if namedClassSet.contains c then
              arr := arr.modify w.val (c :: ·)
          return arr
        ⟨m, midx, worldAtoms⟩
    -- Multi-round soft negative countermodel refutation for residual candidates
    let residualByInd : Std.HashMap IRI (List IRI) :=
      match midx?, p? with
      | some ⟨_, midx, worldAtoms⟩, some p => Id.run do
        let mut resMap : Std.HashMap IRI (List IRI) := {}
        let mut totalRes := 0
        for ind in namedInds do
          let ent := entailedByInd.getD ind {}
          let w := midx.indVal (.named ind)
          let mut seen : Std.HashSet IRI := {}
          let mut cands : Array IRI := #[]
          for c in worldAtoms[w.val]! do
            if c != thing && !ent.contains c && !seen.contains c then
              seen := seen.insert c
              cands := cands.push c
          if !cands.isEmpty then
            resMap := resMap.insert ind cands.toList
            totalRes := totalRes + cands.size
        if totalRes ≥ 16 && canHarvestStandardModel p && checkTableauRolesOkFast p && p.root == .top then
          for _round in [:4] do
            let mut hints : Array (IRI × Concept) := #[]
            for ind in namedInds do
              match resMap.getD ind [] with
              | c :: _ => hints := hints.push (ind, .lit c false)
              | [] => pure ()
            if hints.isEmpty then break
            let negModels : List SROIQDModel :=
              match proposeSoftIndividualModel p hints.toList with
              | some ⟨mNeg, _⟩ => [mNeg]
              | none =>
                -- If full batch clashed beyond retry budget, split into chunks so isolated clashes don't block other individuals
                let chunks := groupListChunks 48 hints.toList
                (mapIndependent numWorkers (fun ch =>
                  (proposeSoftIndividualModel p ch).map Subtype.val) chunks).filterMap id
            if negModels.isEmpty then break
            let mut prunedAny := false
            for mNeg in negModels do
              let negIdx := ModelIndex.build mNeg
              for ind in namedInds do
                let cur := resMap.getD ind []
                if !cur.isEmpty then
                  let wn := negIdx.indVal (.named ind)
                  let kept := cur.filter fun c => negIdx.atomSet.contains (c, wn)
                  if kept.length < cur.length then
                    prunedAny := true
                    resMap := resMap.insert ind kept
            if !prunedAny then break
        return resMap
      | _, _ => {}
    let useEgo := namedInds.length ≥ 32
    let egoIdx? : Option ABoxEgoIndex := if useEgo then some (ABoxEgoIndex.build o) else none
    let realizeInd (ind : IRI) : Option IndividualTypes := do
      let mut entailed : Std.HashSet IRI := {}
      for c in entailedByInd.getD ind {} do
        if namedClassSet.contains c then
          entailed := entailed.insert c
      match midx? with
      | some ⟨_, midx, worldAtoms⟩ =>
        let candsToCheck := match p? with
          | some _ => residualByInd.getD ind []
          | none => worldAtoms[(midx.indVal (.named ind)).val]!
        let mut seenCand : Std.HashSet IRI := {}
        let mut types : Array IRI := #[]
        for c in entailed do
          if !seenCand.contains c then
            seenCand := seenCand.insert c
            types := types.push c
        for c in candsToCheck do
          if !seenCand.contains c then
            seenCand := seenCand.insert c
            if c == thing || entailed.contains c then
              types := types.push c
            else
              let seed := axiomSig (.classAssertion (.named c) (.named ind))
              let provedLocal := match egoIdx? with
                | some eidx =>
                  let egoMod := (extractBotModuleFast (eidx.egoOntology [ind]) seed).1
                  decidesInstance fastConsistencyCheck egoMod c ind == some true
                | none => false
              let isInst ←
                if provedLocal then pure true
                else
                  let mod := (extractBotModuleWithIndex idx o seed).1
                  decidesInstance fastConsistencyCheck mod c ind
              if isInst then
                types := types.push c
                entailed := entailed.insert c
                for sup in superMap.getD c [] do
                  if namedClassSet.contains sup then
                    entailed := entailed.insert sup
                    if !seenCand.contains sup then
                      seenCand := seenCand.insert sup
                      types := types.push sup
        let typeList := types.toList
        return { individual := ind, allTypes := typeList, directTypes := computeDirectTypesFast typeList subSet }
      | none =>
        let mut types : Array IRI := #[]
        for c in namedClasses do
          if c == thing || entailed.contains c then
            types := types.push c
          else
            let seed := axiomSig (.classAssertion (.named c) (.named ind))
            let mod := (extractBotModuleWithIndex idx o seed).1
            let isInst ← decidesInstance fastConsistencyCheck mod c ind
            if isInst then
              types := types.push c
              entailed := entailed.insert c
              for sup in superMap.getD c [] do
                if namedClassSet.contains sup then
                  entailed := entailed.insert sup
        let typeList := types.toList
        return { individual := ind, allTypes := typeList, directTypes := computeDirectTypesFast typeList subSet }
    let entries := if numWorkers ≤ 1 then namedInds.mapM realizeInd
      else (mapIndependent numWorkers realizeInd namedInds).mapM id
    entries.map fun entries =>
      { consistent := true, individuals := namedInds, entries }

/-- Realize an ABox using the hierarchy already computed for the same ontology. -/
def realizeFromHierarchyRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl)
    (hier : ClassHierarchy) (numWorkers : Nat := 8) : Option RealizationResult :=
  realizeFromHierarchyWithModelRuntime o decls hier numWorkers none

theorem realizeFromHierarchyRuntime_workers_eq (o : Ontology)
    (decls : List FunctionalSyntax.EntityDecl) (hier : ClassHierarchy) (workers : Nat) :
    realizeFromHierarchyRuntime o decls hier workers = realizeFromHierarchyRuntime o decls hier 1 := by
  simp only [realizeFromHierarchyRuntime, realizeFromHierarchyWithModelRuntime,
    mapIndependent_eq, List.mapM_map, Function.id_comp, ite_self]

/-- Fast hybrid runtime ABox realizer backed by `classifyOntologyFastRuntime`
    and cached locality indexing. -/
def realizeOntologyFastRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := [])
    (numWorkers : Nat := 8) (auxiliaryClass? : Option IRI := none) : Option RealizationResult :=
  let verified? := proposeVerifiedModel o
  let m0? := verified?.map Prod.fst
  let p0? := verified?.map Prod.snd
  (classifyOntologyFastWithModelRuntime o decls numWorkers m0? auxiliaryClass?).bind fun hier =>
    realizeFromHierarchyWithModelRuntime o decls hier numWorkers m0? auxiliaryClass? p0?

end Sabrina.OWL2.FastClassification
