import Sabrina.OWL2.SROIQD.Termination.ExtendedQueryDecision
import Sabrina.OWL2.StrictTyping
import Sabrina.OWL2.Profile
import Sabrina.OWL2.EL

/-! Certified OWL 2 DL Ontology Classification (complete named-class subsumption
    DAG, equivalence classes, unsatisfiable classes) and ABox Realization (all
    inferred types and most specific direct types per named individual).

    Proves kernel-checked soundness and completeness theorems
    (`classifyOntologyWith_sound_complete`, `realizeOntologyWith_sound_complete`,
    `classifyOntologyReal_sound_complete`, `realizeOntologyReal_sound_complete`)
    using strictly standard Lean core axioms. -/

namespace Sabrina.OWL2.Classification

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.StrictTyping
open Sabrina.OWL2.Profile
open Sabrina.OWL2.EL
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.ExactQuery
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

/-! ### 1. Named Class & Named Individual Extraction -/

private def dedupIRIs (xs : List IRI) : List IRI := Id.run do
  let mut seen : Std.HashSet IRI := {}
  let mut out : Array IRI := #[]
  for x in xs do
    if !seen.contains x then
      seen := seen.insert x
      out := out.push x
  return out.toList

/-- Collect all non-built-in named classes appearing in `o` or explicit `decls`. -/
def collectNamedClasses (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) : List IRI :=
  let fromOnt := (o.flatMap axiomClasses).filter fun c => c != thing && c != nothing
  let fromDecls := decls.filterMap fun d =>
    if d.kind == .cls && d.iri != thing && d.iri != nothing then some d.iri else none
  dedupIRIs (fromOnt ++ fromDecls)

private def indNamedIRIs : Individual → List IRI
  | .named i => [i]
  | .anonymous _ _ => []

private def classNamedIndIRIs : ClassExpr → List IRI
  | .named _ => []
  | .complement c => classNamedIndIRIs c
  | .intersection a b | .union a b => classNamedIndIRIs a ++ classNamedIndIRIs b
  | .oneOf inds => inds.flatMap indNamedIRIs
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c =>
    classNamedIndIRIs c
  | .objectValue _ a => indNamedIRIs a
  | _ => []

private def axiomNamedIndIRIs : Axiom → List IRI
  | .subClassOf a b => classNamedIndIRIs a ++ classNamedIndIRIs b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs => cs.flatMap classNamedIndIRIs
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c | .hasKey c _ _ =>
    classNamedIndIRIs c
  | .sameIndividuals inds | .differentIndividuals inds => inds.flatMap indNamedIRIs
  | .classAssertion c a => classNamedIndIRIs c ++ indNamedIRIs a
  | .objectAssertion _ a b | .negativeObjectAssertion _ a b => indNamedIRIs a ++ indNamedIRIs b
  | .dataAssertion _ a _ | .negativeDataAssertion _ a _ => indNamedIRIs a
  | _ => []

/-- Collect all named individuals appearing in `o` or explicit `decls`. -/
def collectNamedIndividuals (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) : List IRI :=
  let fromOnt := o.flatMap axiomNamedIndIRIs
  let fromDecls := decls.filterMap fun d =>
    if d.kind == .namedIndividual then some d.iri else none
  dedupIRIs (fromOnt ++ fromDecls)

/-! ### 2. Certified Classification Data Structures & Algorithm -/

structure ClassHierarchy where
  consistent : Bool
  classes : List IRI
  unsatisfiable : List IRI
  /-- All verified entailed pairs `(sub, sup)` among `classes`. -/
  subsumptions : List (IRI × IRI)
  /-- Equivalence classes of mutually subsuming satisfiable named classes. -/
  equivalences : List (List IRI)
  /-- Transitive-reduction direct superclasses for each named class. -/
  directParents : List (IRI × List IRI)
  deriving Repr

/-- Exact semantic check for `o ⊨ SubClassOf(a, b)` via any sound & complete
    consistency solver `solve`. -/
def decidesSubsumption (solve : Ontology → Option Bool) (o : Ontology) (a b : IRI) : Option Bool :=
  (solve (existsWitnessAxiom (.intersection (.named a) (.complement (.named b))) :: o)).map (!·)

theorem decidesSubsumption_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {a b : IRI} {res : Bool}
    (h : decidesSubsumption solve o a b = some res) :
    res = true ↔ Entails dm o [.subClassOf (.named a) (.named b)] := by
  simp only [decidesSubsumption, Option.map_eq_some_iff] at h
  obtain ⟨sat, hsat, rfl⟩ := h
  have hneg : negateQueryAxiom (.subClassOf (.named a) (.named b)) =
      some (existsWitnessAxiom (.intersection (.named a) (.complement (.named b)))) := rfl
  have hcnt := counterexample_sat_iff (dm := dm) o hneg
  cases sat with
  | false =>
    simp only [Bool.not_false, true_iff]
    exact Classical.byContradiction fun hne =>
      Bool.noConfusion ((hsolve hsat).mpr (hcnt.mpr hne))
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, false_iff]
    exact hcnt.mp ((hsolve hsat).mp rfl)

/-- Check `o ⊨ ClassAssertion(c, ind)` via any sound & complete consistency solver. -/
def decidesInstance (solve : Ontology → Option Bool) (o : Ontology) (c ind : IRI) : Option Bool :=
  (solve (.classAssertion (.complement (.named c)) (.named ind) :: o)).map (!·)

theorem decidesInstance_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {c ind : IRI} {res : Bool}
    (h : decidesInstance solve o c ind = some res) :
    res = true ↔ Entails dm o [.classAssertion (.named c) (.named ind)] := by
  simp only [decidesInstance, Option.map_eq_some_iff] at h
  obtain ⟨sat, hsat, rfl⟩ := h
  have hneg : negateQueryAxiom (.classAssertion (.named c) (.named ind)) =
      some (.classAssertion (.complement (.named c)) (.named ind)) := rfl
  have hcnt := counterexample_sat_iff (dm := dm) o hneg
  cases sat with
  | false =>
    simp only [Bool.not_false, true_iff]
    exact Classical.byContradiction fun hne =>
      Bool.noConfusion ((hsolve hsat).mpr (hcnt.mpr hne))
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, false_iff]
    exact hcnt.mp ((hsolve hsat).mp rfl)

private def filterMOption {α : Type} (p : α → Option Bool) : List α → Option (List α)
  | [] => some []
  | x :: xs =>
    (p x).bind fun b =>
      (filterMOption p xs).map fun rest => if b then x :: rest else rest

private theorem filterMOption_mem_iff {α : Type} {p : α → Option Bool} {P : α → Prop}
    (hp : ∀ {x b}, p x = some b → (b = true ↔ P x))
    {xs ys : List α} (h : filterMOption p xs = some ys) :
    ∀ x, x ∈ ys ↔ x ∈ xs ∧ P x := by
  induction xs generalizing ys with
  | nil =>
    simp only [filterMOption, Option.some.injEq] at h; subst h
    intro x; simp
  | cons a xs ih =>
    simp only [filterMOption, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rest, hrest, rfl⟩ := h
    have ih' := ih hrest
    intro x
    cases b with
    | true =>
      simp only [↓reduceIte, List.mem_cons, ih']
      have hPa : P a := (hp hb).mp rfl
      constructor
      · rintro (rfl | ⟨hx, hPx⟩)
        · exact ⟨Or.inl rfl, hPa⟩
        · exact ⟨Or.inr hx, hPx⟩
      · rintro ⟨rfl | hx, hPx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hPx⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, ih', List.mem_cons]
      have hnPa : ¬ P a := fun hP => Bool.noConfusion ((hp hb).mpr hP)
      constructor
      · rintro ⟨hx, hPx⟩; exact ⟨Or.inr hx, hPx⟩
      · rintro ⟨rfl | hx, hPx⟩
        · exact absurd hPx hnPa
        · exact ⟨hx, hPx⟩

private def computeEquivClasses (classes : List IRI) (subs : List (IRI × IRI)) : List (List IRI) :=
  let eqv (a b : IRI) : Bool := subs.contains (a, b) && subs.contains (b, a)
  let rec go (rem : List IRI) (seen : List IRI) : List (List IRI) :=
    match rem with
    | [] => []
    | c :: rest =>
      if seen.contains c then go rest seen
      else
        let grp := classes.filter (eqv c)
        grp :: go rest (grp ++ seen)
  go classes []

private def computeDirectParents (classes : List IRI) (subs : List (IRI × IRI)) : List (IRI × List IRI) :=
  let strictSub (a b : IRI) : Bool := subs.contains (a, b) && !subs.contains (b, a)
  classes.map fun c =>
    let strictSups := classes.filter (strictSub c)
    let direct := strictSups.filter fun p =>
      !strictSups.any fun mid => strictSub c mid && strictSub mid p
    let parents := if direct.isEmpty then [thing] else direct
    (c, parents)

/-- Certified full TBox classification with any exact consistency solver `solve`. -/
def classifyOntologyWith (solve : Ontology → Option Bool) (o : Ontology)
    (namedClasses : List IRI) : Option ClassHierarchy :=
  (solve o).bind fun consistent =>
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
      (filterMOption (fun c => decidesSubsumption solve o c nothing) namedClasses).bind fun unsat =>
        let allPairs := orderedPairs namedClasses
        (filterMOption (fun (a, b) => decidesSubsumption solve o a b) allPairs).map fun subs =>
          let satClasses := namedClasses.filter (!unsat.contains ·)
          {
            consistent := true
            classes := namedClasses
            unsatisfiable := unsat
            subsumptions := subs
            equivalences := computeEquivClasses satClasses subs
            directParents := computeDirectParents satClasses subs
          }

/-- Kernel-checked soundness and completeness theorem for `classifyOntologyWith`. -/
theorem classifyOntologyWith_sound_complete {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {namedClasses : List IRI} {h : ClassHierarchy}
    (hcls : classifyOntologyWith solve o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable dm o) ∧
    (h.consistent = true →
      Satisfiable dm o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm o [.subClassOf (.named a) (.named b)])) := by
  simp only [classifyOntologyWith, Option.bind_eq_some_iff] at hcls
  obtain ⟨cons, hcons, hrest⟩ := hcls
  cases cons with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest
    subst hrest
    exact ⟨fun _ hsat => Bool.noConfusion ((hsolve hcons).mpr hsat), fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hrest
    obtain ⟨unsat, hunsat, subs, hsubs, rfl⟩ := hrest
    refine ⟨(fun hc => by cases hc), fun _ => ⟨(hsolve hcons).mp rfl, ?_, ?_⟩⟩
    · exact filterMOption_mem_iff (fun h => decidesSubsumption_iff hsolve h) hunsat
    · intro a b
      have hm := filterMOption_mem_iff (P := fun p : IRI × IRI =>
          Entails dm o [.subClassOf (.named p.1) (.named p.2)])
        (fun {p b} hp => decidesSubsumption_iff hsolve hp) hsubs (a, b)
      simpa [mem_orderedPairs_iff, and_assoc] using hm

/-- Certified TBox classification under Dedekind-cut `realDatatypeMap`. -/
def classifyOntologyReal (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  classifyOntologyWith decideRealOntology? o namedClasses

theorem classifyOntologyReal_sound_complete {o : Ontology} {namedClasses : List IRI}
    {h : ClassHierarchy} (hcls : classifyOntologyReal o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable realDatatypeMap o) ∧
    (h.consistent = true →
      Satisfiable realDatatypeMap o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails realDatatypeMap o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails realDatatypeMap o [.subClassOf (.named a) (.named b)])) :=
  classifyOntologyWith_sound_complete decideRealOntology_iff hcls

/-! ### 3. Certified ABox Realization -/

structure IndividualTypes where
  individual : IRI
  allTypes : List IRI
  directTypes : List IRI
  deriving Repr

structure RealizationResult where
  consistent : Bool
  individuals : List IRI
  entries : List IndividualTypes
  deriving Repr

private def computeDirectTypes (types : List IRI) (subs : List (IRI × IRI)) : List IRI :=
  let strictSub (a b : IRI) : Bool := subs.contains (a, b) && !subs.contains (b, a)
  types.filter fun c => !types.any fun moreSpec => strictSub moreSpec c

private def mapMOption {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => (f x).bind fun y => (mapMOption f xs).map (y :: ·)

private theorem mapMOption_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : mapMOption f xs = some ys) :
    (∀ y ∈ ys, ∃ x ∈ xs, f x = some y) ∧ (∀ x ∈ xs, ∃ y ∈ ys, f x = some y) := by
  induction xs generalizing ys with
  | nil =>
    simp only [mapMOption, Option.some.injEq] at h; subst h
    exact ⟨(fun _ hy => by cases hy), (fun _ hx => by cases hx)⟩
  | cons a xs ih =>
    simp only [mapMOption, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rest, hrest, rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := ih hrest
    refine ⟨fun y hy => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨a, List.mem_cons_self .., hb⟩
      · obtain ⟨x, hx, hfx⟩ := ih1 y hy'; exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, List.mem_cons_self .., hb⟩
      · obtain ⟨y, hy, hfx⟩ := ih2 x hx'; exact ⟨y, List.mem_cons_of_mem _ hy, hfx⟩

/-- Certified ABox realization: for every named individual in `namedInds`, computes
    all entailed named classes from `namedClasses` and the minimal (most specific)
    direct types under the ontology's subsumption preorder. -/
def realizeOntologyWith (solve : Ontology → Option Bool) (o : Ontology)
    (namedClasses namedInds : List IRI) : Option RealizationResult :=
  (classifyOntologyWith solve o namedClasses).bind fun hier =>
    if !hier.consistent then
      some { consistent := false, individuals := namedInds, entries := [] }
    else
      (mapMOption (fun ind =>
        (filterMOption (fun c => decidesInstance solve o c ind) namedClasses).map fun ts =>
          { individual := ind
            allTypes := ts
            directTypes := computeDirectTypes ts hier.subsumptions }) namedInds).map fun entries =>
        { consistent := true, individuals := namedInds, entries := entries }

/-- Kernel-checked soundness and completeness theorem for `realizeOntologyWith`. -/
theorem realizeOntologyWith_sound_complete {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {namedClasses namedInds : List IRI} {r : RealizationResult}
    (hreal : realizeOntologyWith solve o namedClasses namedInds = some r) :
    (r.consistent = false → ¬ Satisfiable dm o) ∧
    (r.consistent = true →
      Satisfiable dm o ∧
      ∀ e ∈ r.entries,
        e.individual ∈ namedInds ∧
        (∀ c, c ∈ e.allTypes ↔ c ∈ namedClasses ∧ Entails dm o [.classAssertion (.named c) (.named e.individual)]) ∧
        (∀ c ∈ e.directTypes, c ∈ e.allTypes)) := by
  simp only [realizeOntologyWith, Option.bind_eq_some_iff] at hreal
  obtain ⟨hier, hcls, hrest⟩ := hreal
  have ⟨hunsatCls, hsatCls⟩ := classifyOntologyWith_sound_complete hsolve hcls
  cases hcon : hier.consistent with
  | false =>
    rw [hcon] at hrest
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest
    subst hrest
    exact ⟨fun _ => hunsatCls hcon, fun hc => by cases hc⟩
  | true =>
    rw [hcon] at hrest
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨entries, hentries, rfl⟩ := hrest
    refine ⟨(fun hc => by cases hc), fun _ => ⟨(hsatCls hcon).1, fun e he => ?_⟩⟩
    obtain ⟨ind, hind, hfe⟩ := (mapMOption_mem hentries).1 e he
    simp only [Option.map_eq_some_iff] at hfe
    obtain ⟨ts, hts, rfl⟩ := hfe
    refine ⟨hind, filterMOption_mem_iff (fun h => decidesInstance_iff hsolve h) hts, fun c hc => ?_⟩
    exact (List.mem_filter.mp hc).1

/-- Certified ABox realization under Dedekind-cut `realDatatypeMap`. -/
def realizeOntologyReal (o : Ontology) (namedClasses namedInds : List IRI) : Option RealizationResult :=
  realizeOntologyWith decideRealOntology? o namedClasses namedInds

theorem realizeOntologyReal_sound_complete {o : Ontology} {namedClasses namedInds : List IRI}
    {r : RealizationResult} (hreal : realizeOntologyReal o namedClasses namedInds = some r) :
    (r.consistent = false → ¬ Satisfiable realDatatypeMap o) ∧
    (r.consistent = true →
      Satisfiable realDatatypeMap o ∧
      ∀ e ∈ r.entries,
        e.individual ∈ namedInds ∧
        (∀ c, c ∈ e.allTypes ↔ c ∈ namedClasses ∧ Entails realDatatypeMap o [.classAssertion (.named c) (.named e.individual)]) ∧
        (∀ c ∈ e.directTypes, c ∈ e.allTypes)) :=
  realizeOntologyWith_sound_complete decideRealOntology_iff hreal

/-! ### 4. Fast Hybrid Runtime Classifier & Realizer (EL++ + Tableau + Exact SROIQ(D)) -/

private def hasWiderDataOrReal (p : SROIQD.Problem) : Bool :=
  p.allDataAtoms.any (fun
    | .datatype t | .restriction t _ => t == owlReal
    | _ => false) ||
  p.allDataAtoms.any SROIQD.Termination.WiderData.isOrderedExactAtom ||
  p.allDataAtoms.any SROIQD.Termination.WiderData.isStringFacetExtraAtom ||
  p.allDataProps.any (fun dp => dp == topDataProperty || dp == bottomDataProperty)

private def checkTableauRolesOk (p : SROIQD.Problem) : Bool :=
  let closed := Sabrina.ALC.roleClosure p.rules
  p.simpleRoles.all (fun r => (RoleChains.SimpleRoles.firstComposite closed p.chains r).isNone) &&
  RoleChains.checkRegular (RoleChains.inferRank p.rules p.chains) p.rules p.chains

private def tryTableauSat (p : SROIQD.Problem) : Option Bool :=
  if !hasWiderDataOrReal p && checkTableauRolesOk p then
    let limits : SROIQD.Limits := {}
    match SROIQD.propose p limits with
    | some ev =>
      if p.checkSimple && SROIQD.checkEvidence p limits.worlds ev then some ev.isModel else none
    | none => none
  else none

/-- Fast hybrid verified consistency solver:
    1. Polynomial `EL++` classifier when `o` is in `EL++`
    2. Direct `SROIQD.counterProblem` tableau fast path when the leading axiom is
       `existsWitnessAxiom e` (avoiding `owl:topObjectProperty` overhead!)
    3. Verified `SROIQ(D)` tableau (`propose` + `checkConsistency`) for standard OWL 2 DL
    4. Exact `decideRealOntology?` fallback for `owl:real`, wider datatypes, string facets,
       built-in data properties, or when bounded tableau search hits limits. -/
def fastConsistencyCheck (o : Ontology) : Option Bool :=
  match o with
  | .subClassOf (.named t) (.objectSome (.named top) e) :: base =>
    if t == thing && top == topObjectProperty then
      -- Fast path for `existsWitnessAxiom e :: base`: check `e ⊓ ¬⊥` at root via `counterProblem`
      let tryFast : Option Bool :=
        match Normalize.normalizeWithDefs base with
        | some (defs, p) =>
          match Normalize.queryToInclusions defs (.subClassOf e (.named nothing)) with
          | some [q] => tryTableauSat (SROIQD.counterProblem p q)
          | _ => none
        | none => none
      match tryFast with
      | some b => some b
      | none => decideRealOntology? o
    else
      fastConsistencyCheckPlain o
  | _ => fastConsistencyCheckPlain o
where
  fastConsistencyCheckPlain (ont : Ontology) : Option Bool :=
    let fp := profileOntology ont
    if fp.leastFragment == .el then
      match normalizeEL ont with
      | some elAxs =>
        match decideELConsistency elAxs with
        | some (.inl _) => some true
        | some (.inr _) => some false
        | none => decideRealOntology? ont
      | none => decideRealOntology? ont
    else
      match Normalize.normalizeWithDefs ont with
      | some (_, p) =>
        match tryTableauSat p with
        | some b => some b
        | none => decideRealOntology? ont
      | none => decideRealOntology? ont

def classifyOntologyRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) :
    Option ClassHierarchy :=
  let namedClasses := collectNamedClasses o decls
  classifyOntologyWith fastConsistencyCheck o namedClasses

def realizeOntologyRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) :
    Option RealizationResult :=
  let namedClasses := collectNamedClasses o decls
  let namedInds := collectNamedIndividuals o decls
  realizeOntologyWith fastConsistencyCheck o namedClasses namedInds

#print axioms classifyOntologyWith_sound_complete
#print axioms classifyOntologyReal_sound_complete
#print axioms realizeOntologyWith_sound_complete
#print axioms realizeOntologyReal_sound_complete

end Sabrina.OWL2.Classification
