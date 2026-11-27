import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastClassification.Runtime
import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.RDF.Serialize
import Sabrina.OWL2.StrictTyping

/-! Kernel-verified OWL 2 DL ontology materialization: computes entailed
    class hierarchies (`SubClassOf`, `EquivalentClasses`, unsatisfiable
    classes), object property hierarchies (`SubObjectPropertyOf`), ABox class
    realization (`ClassAssertion`), object property realization
    (`ObjectPropertyAssertion`), and individual equality (`SameIndividual`),
    and renders the materialized ontology to Functional-Style Syntax (`.ofn`),
    Turtle 1.1 (`.ttl`), or RDF/XML 1.1 (`.owl`).

    Proves `materializeWith_entailed` and `materializeReal_entailed`: every
    materialized inferred axiom is semantically entailed by the source ontology
    and contains no anonymous individuals, so appending inferred axioms to `o`
    preserves the exact class of models (`models i res.materializedOntology ↔ models i o`). -/

namespace Sabrina.OWL2.Materialize

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.Classification
open Sabrina.OWL2.RDF
open Sabrina.OWL2.RDF.OWLMapping
open Sabrina.OWL2.RDF.Serialize
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

/-! ### 1. Named Object Property Extraction & Generic Entailment Decider -/

private def dedupList {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => if xs.contains x then dedupList xs else x :: dedupList xs

private theorem dedupList_mem {α : Type} [BEq α] [LawfulBEq α] {x : α} {xs : List α} :
    x ∈ dedupList xs → x ∈ xs := by
  induction xs with
  | nil => intro h; cases h
  | cons a tl ih =>
    intro h
    simp only [dedupList] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | htl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih htl)

private def objPropNamedIRIs : ObjectProperty → List IRI
  | .named r | .inverse r => [r]

private def classNamedObjPropIRIs : ClassExpr → List IRI
  | .named _ => []
  | .complement c => classNamedObjPropIRIs c
  | .intersection a b | .union a b => classNamedObjPropIRIs a ++ classNamedObjPropIRIs b
  | .oneOf _ => []
  | .objectSome r c | .objectAll r c | .objectMin _ r c | .objectMax _ r c | .objectExact _ r c =>
    objPropNamedIRIs r ++ classNamedObjPropIRIs c
  | .objectValue r _ | .objectSelf r => objPropNamedIRIs r
  | _ => []

private def axiomNamedObjPropIRIs : Axiom → List IRI
  | .subClassOf a b => classNamedObjPropIRIs a ++ classNamedObjPropIRIs b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classNamedObjPropIRIs
  | .subObjectProperty r s | .inverseObjectProperties r s =>
    objPropNamedIRIs r ++ objPropNamedIRIs s
  | .subObjectPropertyChain rs s =>
    rs.flatMap objPropNamedIRIs ++ objPropNamedIRIs s
  | .equivalentObjectProperties rs | .disjointObjectProperties rs =>
    rs.flatMap objPropNamedIRIs
  | .objectPropertyDomain r c | .objectPropertyRange r c =>
    objPropNamedIRIs r ++ classNamedObjPropIRIs c
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .reflexiveObjectProperty r | .irreflexiveObjectProperty r
  | .symmetricObjectProperty r | .asymmetricObjectProperty r
  | .transitiveObjectProperty r => objPropNamedIRIs r
  | .dataPropertyDomain _ c => classNamedObjPropIRIs c
  | .hasKey c rs _ => classNamedObjPropIRIs c ++ rs.flatMap objPropNamedIRIs
  | .classAssertion c _ => classNamedObjPropIRIs c
  | .objectAssertion r _ _ | .negativeObjectAssertion r _ _ => objPropNamedIRIs r
  | _ => []

/-- Collect all non-built-in named object properties appearing in `o` or `decls`. -/
def collectNamedObjectProperties (o : Ontology) (decls : List EntityDecl := []) : List IRI :=
  let fromOnt := (o.flatMap axiomNamedObjPropIRIs).filter fun r =>
    r != topObjectProperty && r != bottomObjectProperty
  let fromDecls := decls.filterMap fun d =>
    if d.kind == .objectProperty && d.iri != topObjectProperty && d.iri != bottomObjectProperty
    then some d.iri else none
  dedupList (fromOnt ++ fromDecls)

private def anyBranchSat (solve : Ontology → Option Bool) (o : Ontology) :
    List Ontology → Option Bool
  | [] => some false
  | b :: rest =>
    match solve (b ++ o) with
    | some true => some true
    | some false => anyBranchSat solve o rest
    | none => none

private theorem anyBranchSat_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    (o : Ontology) (branches : List Ontology) {res : Bool}
    (h : anyBranchSat solve o branches = some res) :
    res = true ↔ ∃ b ∈ branches, Satisfiable dm (b ++ o) := by
  induction branches generalizing res with
  | nil =>
    simp only [anyBranchSat, Option.some.injEq] at h
    subst h; simp
  | cons hd tl ih =>
    simp only [anyBranchSat] at h
    cases hhd : solve (hd ++ o) with
    | none => simp [hhd] at h
    | some bhd =>
      cases bhd with
      | true =>
        simp only [hhd, Option.some.injEq] at h
        subst h
        exact ⟨fun _ => ⟨hd, List.mem_cons_self .., (hsolve hhd).mp rfl⟩, fun _ => rfl⟩
      | false =>
        simp only [hhd] at h
        have htl := ih h
        have hnot : ¬ Satisfiable dm (hd ++ o) := fun hs =>
          Bool.noConfusion ((hsolve hhd).mpr hs)
        constructor
        · intro hr
          obtain ⟨b, hb, hsat⟩ := htl.mp hr
          exact ⟨b, List.mem_cons_of_mem _ hb, hsat⟩
        · rintro ⟨b, hb, hsat⟩
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact absurd hsat hnot
          · exact htl.mpr ⟨b, hb', hsat⟩

/-- Exact entailment decision for any axiom form supported by `negateQueryBranches`. -/
def decidesAxiomEntails (solve : Ontology → Option Bool) (o : Ontology) (ax : Axiom) :
    Option Bool :=
  (negateQueryBranches o ax).bind fun branches =>
    (anyBranchSat solve o branches).map (!·)

theorem decidesAxiomEntails_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {ax : Axiom} {res : Bool}
    (h : decidesAxiomEntails solve o ax = some res) :
    res = true ↔ Entails dm o [ax] := by
  simp only [decidesAxiomEntails, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨branches, hneg, b, hb, rfl⟩ := h
  have hcnt := counterexample_branches_sat_iff (dm := dm) o hneg
  have hbs := anyBranchSat_iff hsolve o branches hb
  cases b with
  | false =>
    simp only [Bool.not_false, true_iff]
    exact Classical.byContradiction fun hne =>
      Bool.noConfusion (hbs.mpr (hcnt.mpr hne))
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, false_iff]
    exact hcnt.mp (hbs.mp rfl)

private def filterEntailedAxioms (solve : Ontology → Option Bool) (o : Ontology) :
    List Axiom → Option (List Axiom)
  | [] => some []
  | ax :: rest =>
    (decidesAxiomEntails solve o ax).bind fun b =>
      (filterEntailedAxioms solve o rest).map fun kept =>
        if b then ax :: kept else kept

private theorem filterEntailedAxioms_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {cands kept : List Axiom}
    (h : filterEntailedAxioms solve o cands = some kept) :
    ∀ a ∈ kept, a ∈ cands ∧ Entails dm o [a] := by
  induction cands generalizing kept with
  | nil =>
    simp only [filterEntailedAxioms, Option.some.injEq] at h
    subst h; intro a ha; cases ha
  | cons ax rest ih =>
    simp only [filterEntailedAxioms, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, restKept, hrest, rfl⟩ := h
    have ih' := ih hrest
    intro a ha
    cases b with
    | true =>
      simp only [↓reduceIte, List.mem_cons] at ha
      rcases ha with rfl | htl
      · exact ⟨List.mem_cons_self .., (decidesAxiomEntails_iff hsolve hb).mp rfl⟩
      · exact ⟨List.mem_cons_of_mem _ (ih' a htl).1, (ih' a htl).2⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ha
      exact ⟨List.mem_cons_of_mem _ (ih' a ha).1, (ih' a ha).2⟩

/-! ### 2. Materialization Options, Engine & Soundness/Equivalence Proofs -/

structure MaterializeOptions where
  includeAsserted : Bool := true
  includeDirectSubClass : Bool := true
  includeAllSubClass : Bool := false
  includeEquivalentClasses : Bool := true
  includeUnsatisfiable : Bool := true
  includeSubObjectProperties : Bool := true
  includeDirectTypes : Bool := true
  includeAllTypes : Bool := false
  includeObjectPropertyAssertions : Bool := true
  includeDataPropertyAssertions : Bool := true
  includeSameIndividuals : Bool := true
  deriving Repr

structure MaterializeResult where
  consistent : Bool
  assertedAxioms : Ontology
  inferredAxioms : Ontology
  materializedOntology : Ontology
  deriving Repr

private def unorderedPairs : List IRI → List (IRI × IRI)
  | [] => []
  | x :: xs => (xs.map fun y => (x, y)) ++ unorderedPairs xs

private def orderedDistinctPairs (xs : List IRI) : List (IRI × IRI) :=
  xs.flatMap fun a => (xs.filter (· != a)).map fun b => (a, b)

private theorem classHolds_named_equiv {dm : DatatypeMap} (o : Ontology) (cs : List IRI)
    (hsub : ∀ a ∈ cs, ∀ b ∈ cs, Entails dm o [.subClassOf (.named a) (.named b)]) :
    Entails dm o [.equivalentClasses (cs.map .named)] := by
  intro i hmod
  refine satisfies_models fun q hq => ?_
  simp only [List.mem_singleton] at hq
  subst hq
  intro ca hca cb hcb x
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hca
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hcb
  constructor
  · intro hx
    obtain ⟨assign, hs⟩ := hsub a ha b hb i hmod
    have h1 := hs _ (List.mem_singleton.mpr rfl) x
    exact h1 hx
  · intro hx
    obtain ⟨assign, hs⟩ := hsub b hb a ha i hmod
    have h1 := hs _ (List.mem_singleton.mpr rfl) x
    exact h1 hx

private theorem entails_to_axiomHolds_of_noAnon {dm : DatatypeMap} {o : Ontology} {a : Axiom}
    (hno : axiomAnonDocs a = []) (hent : Entails dm o [a])
    {i : Interpretation dm} {assign : String → String → i.Object}
    (hsat : satisfies (i.withAnonymous assign) o) :
    axiomHolds (i.withAnonymous assign) a := by
  obtain ⟨assign', hs'⟩ := hent i ⟨assign, hsat⟩
  have hholds : axiomHolds (i.withAnonymous assign') a := hs' a (List.mem_singleton.mpr rfl)
  exact (axiomHolds_withAnonymous_agree i (a1 := assign) (a2 := assign')
    (fun d hd => by simp [hno] at hd)).mpr hholds

private def materializedClassAxioms (hier : ClassHierarchy) (opts : MaterializeOptions) :
    List Axiom :=
  let subAxioms : List Axiom :=
    if opts.includeAllSubClass then
      hier.subsumptions.filterMap fun (a, b) =>
        if a == b then none else some (.subClassOf (.named a) (.named b))
    else if opts.includeDirectSubClass then
      hier.directParents.flatMap fun (a, ps) =>
        ps.filterMap fun b =>
          if hier.subsumptions.contains (a, b) then some (.subClassOf (.named a) (.named b))
          else none
    else []
  let eqAxioms : List Axiom :=
    if opts.includeEquivalentClasses then
      hier.equivalences.filterMap fun eq =>
        if eq.length ≥ 2 &&
            eq.all (fun a => eq.all (fun b => hier.subsumptions.contains (a, b))) then
          some (.equivalentClasses (eq.map .named))
        else none
    else []
  let unsatAxioms : List Axiom :=
    if opts.includeUnsatisfiable then
      hier.unsatisfiable.map fun c => .subClassOf (.named c) (.named nothing)
    else []
  subAxioms ++ eqAxioms ++ unsatAxioms

private def materializedTypeAxioms (real : RealizationResult) (opts : MaterializeOptions) :
    List Axiom :=
  if opts.includeAllTypes then
    real.entries.flatMap fun e =>
      e.allTypes.map fun c => .classAssertion (.named c) (.named e.individual)
  else if opts.includeDirectTypes then
    real.entries.flatMap fun e =>
      e.directTypes.map fun c => .classAssertion (.named c) (.named e.individual)
  else []

private def dataCandidateLiterals (o : Ontology) : List Literal :=
  (SWRL.collectKnownLiterals o).filter fun l => (Datatypes.decodeLiteral l).isSome

private def dataCandidateProperties (o : Ontology) (decls : List EntityDecl) : List IRI :=
  (StrictTyping.allDataProps decls o).eraseDups

private def dataAssertionCandidates (o : Ontology) (decls : List EntityDecl)
    (inds : List IRI) : List Axiom :=
  let lits := dataCandidateLiterals o
  (dataCandidateProperties o decls).flatMap fun p =>
    inds.flatMap fun ind => lits.map fun lit => .dataAssertion p (.named ind) lit

private theorem dataAssertionCandidates_noAnon {o : Ontology} {decls : List EntityDecl}
    {inds : List IRI} {a : Axiom} (h : a ∈ dataAssertionCandidates o decls inds) :
    axiomAnonDocs a = [] := by
  unfold dataAssertionCandidates at h
  obtain ⟨_, _, hs⟩ := List.mem_flatMap.mp h
  obtain ⟨_, _, hl⟩ := List.mem_flatMap.mp hs
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hl
  rfl

/-- Materialize entailed axioms for `o` using any sound & complete consistency solver `solve`. -/
def materializeWith (solve : Ontology → Option Bool) (o : Ontology)
    (decls : List EntityDecl := []) (opts : MaterializeOptions := {}) :
    Option MaterializeResult :=
  let namedClasses := collectNamedClasses o decls
  let namedInds := collectNamedIndividuals o decls
  let namedObjProps := collectNamedObjectProperties o decls
  (classifyOntologyWith solve o namedClasses).bind fun hier =>
    if !hier.consistent then
      some {
        consistent := false
        assertedAxioms := o
        inferredAxioms := []
        materializedOntology := if opts.includeAsserted then o else []
      }
    else
      (realizeOntologyWith solve o namedClasses namedInds).bind fun real =>
        if !real.consistent then
          some {
            consistent := false
            assertedAxioms := o
            inferredAxioms := []
            materializedOntology := if opts.includeAsserted then o else []
          }
        else
          let extraCands : List Axiom :=
            (if opts.includeSubObjectProperties then
              (orderedDistinctPairs namedObjProps).map fun (r, s) =>
                .subObjectProperty (.named r) (.named s)
            else []) ++
            (if opts.includeObjectPropertyAssertions then
              namedObjProps.flatMap fun r =>
                namedInds.flatMap fun a =>
                  namedInds.map fun b => .objectAssertion (.named r) (.named a) (.named b)
            else []) ++
            (if opts.includeSameIndividuals then
              (unorderedPairs namedInds).map fun (a, b) =>
                .sameIndividuals [.named a, .named b]
            else []) ++
            (if opts.includeDataPropertyAssertions then dataAssertionCandidates o decls namedInds else [])
          (filterEntailedAxioms solve o extraCands).map fun extraInferred =>
            let rawInferred :=
              materializedClassAxioms hier opts ++
              materializedTypeAxioms real opts ++
              extraInferred
            let deduped := dedupList rawInferred
            let freshInferred := deduped.filter fun ax => !o.contains ax
            let full := if opts.includeAsserted then o ++ freshInferred else freshInferred
            { consistent := true
              assertedAxioms := o
              inferredAxioms := freshInferred
              materializedOntology := full }

private theorem materializedClassAxioms_sound {dm : DatatypeMap} {o : Ontology}
    {namedClasses : List IRI} {hier : ClassHierarchy} (opts : MaterializeOptions)
    (hunsat : ∀ c, c ∈ hier.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm o [.subClassOf (.named c) (.named nothing)])
    (hsub : ∀ a b, (a, b) ∈ hier.subsumptions ↔ a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm o [.subClassOf (.named a) (.named b)]) :
    ∀ a ∈ materializedClassAxioms hier opts, Entails dm o [a] ∧ axiomAnonDocs a = [] := by
  intro a ha
  simp only [materializedClassAxioms, List.mem_append] at ha
  rcases ha with (h1 | h2) | h3
  · -- subAxioms
    split at h1
    · obtain ⟨⟨x, y⟩, hxy, hif⟩ := List.mem_filterMap.mp h1
      split at hif; · cases hif
      simp only [Option.some.injEq] at hif; subst hif
      exact ⟨(hsub x y).mp hxy |>.2.2, rfl⟩
    · split at h1
      · obtain ⟨⟨x, ps⟩, _, hbm⟩ := List.mem_flatMap.mp h1
        obtain ⟨y, _, hif⟩ := List.mem_filterMap.mp hbm
        split at hif; rotate_left; · cases hif
        rename_i hmem
        simp only [Option.some.injEq] at hif; subst hif
        exact ⟨(hsub x y).mp (List.contains_iff_mem.mp hmem) |>.2.2, rfl⟩
      · cases h1
  · -- eqAxioms
    split at h2
    · obtain ⟨eq, _, hif⟩ := List.mem_filterMap.mp h2
      split at hif; rotate_left; · cases hif
      rename_i hcond
      simp only [Option.some.injEq] at hif; subst hif
      have hpair : ∀ x ∈ eq, ∀ y ∈ eq, Entails dm o [.subClassOf (.named x) (.named y)] := by
        intro x hx y hy
        have h2' := (Bool.and_eq_true ..).mp hcond |>.2
        have hx' := List.all_eq_true.mp h2' x hx
        have hy' := List.all_eq_true.mp hx' y hy
        exact (hsub x y).mp (List.contains_iff_mem.mp hy') |>.2.2
      refine ⟨classHolds_named_equiv o eq hpair, ?_⟩
      simp only [axiomAnonDocs, List.flatMap_eq_nil_iff]
      intro c hc
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
      rfl
    · cases h2
  · -- unsatAxioms
    split at h3
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h3
      exact ⟨(hunsat c).mp hc |>.2, rfl⟩
    · cases h3

private theorem materializedTypeAxioms_sound {dm : DatatypeMap} {o : Ontology}
    {namedClasses : List IRI} {real : RealizationResult} (opts : MaterializeOptions)
    (hent : ∀ e ∈ real.entries,
      (∀ c, c ∈ e.allTypes ↔ c ∈ namedClasses ∧ Entails dm o [.classAssertion (.named c) (.named e.individual)]) ∧
      (∀ c ∈ e.directTypes, c ∈ e.allTypes)) :
    ∀ a ∈ materializedTypeAxioms real opts, Entails dm o [a] ∧ axiomAnonDocs a = [] := by
  intro a ha
  simp only [materializedTypeAxioms] at ha
  split at ha
  · obtain ⟨e, he, hc⟩ := List.mem_flatMap.mp ha
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc
    exact ⟨((hent e he).1 c).mp hcm |>.2, rfl⟩
  · split at ha
    · obtain ⟨e, he, hc⟩ := List.mem_flatMap.mp ha
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc
      exact ⟨((hent e he).1 c).mp ((hent e he).2 c hcm) |>.2, rfl⟩
    · cases ha

/-- Kernel-checked soundness and conservative model-equivalence theorem for
    `materializeWith`:
    1. If inconsistent, `o` is genuinely unsatisfiable.
    2. If consistent, `o` is satisfiable, every inferred axiom is semantically
       entailed by `o` (and anonymous-individual-free), and whenever asserted
       axioms are retained (`opts.includeAsserted = true`), the materialized
       ontology has the exact same models as `o`. -/
theorem materializeWith_entailed {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {decls : List EntityDecl} {opts : MaterializeOptions}
    {res : MaterializeResult}
    (hm : materializeWith solve o decls opts = some res) :
    (res.consistent = false → ¬ Satisfiable dm o) ∧
    (res.consistent = true →
      Satisfiable dm o ∧
      (∀ a ∈ res.inferredAxioms, Entails dm o [a] ∧ axiomAnonDocs a = []) ∧
      (opts.includeAsserted = true →
        ∀ i : Interpretation dm, models i res.materializedOntology ↔ models i o)) := by
  simp only [materializeWith, Option.bind_eq_some_iff] at hm
  obtain ⟨hier, hcls, hrest⟩ := hm
  have ⟨hunsatCls, hsatCls⟩ := classifyOntologyWith_sound_complete hsolve hcls
  cases hhc : hier.consistent with
  | false =>
    rw [hhc] at hrest
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest
    subst hrest
    exact ⟨fun _ => hunsatCls hhc, fun hc => by cases hc⟩
  | true =>
    rw [hhc] at hrest
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at hrest
    obtain ⟨real, hreal, hrest2⟩ := hrest
    have ⟨hunsatReal, hsatReal⟩ := realizeOntologyWith_sound_complete hsolve hreal
    cases hrc : real.consistent with
    | false =>
      rw [hrc] at hrest2
      simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest2
      subst hrest2
      exact ⟨fun _ => hunsatReal hrc, fun hc => by cases hc⟩
    | true =>
      rw [hrc] at hrest2
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest2
      obtain ⟨extraInferred, hextra, rfl⟩ := hrest2
      obtain ⟨hSat, hUnsat, hSub⟩ := hsatCls hhc
      obtain ⟨_, hEntReal⟩ := hsatReal hrc
      have hExtraSound := filterEntailedAxioms_sound hsolve hextra
      have hExtraNoAnon : ∀ a ∈ extraInferred, axiomAnonDocs a = [] := by
        intro a ha
        have hcand := (hExtraSound a ha).1
        simp only [List.mem_append] at hcand
        rcases hcand with ((h1 | h2) | h3) | h4
        · split at h1
          · obtain ⟨⟨r, s⟩, _, rfl⟩ := List.mem_map.mp h1; rfl
          · cases h1
        · split at h2
          · obtain ⟨r, _, h2a⟩ := List.mem_flatMap.mp h2
            obtain ⟨x, _, h2b⟩ := List.mem_flatMap.mp h2a
            obtain ⟨y, _, rfl⟩ := List.mem_map.mp h2b
            rfl
          · cases h2
        · split at h3
          · obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp h3; rfl
          · cases h3
        · split at h4
          · exact dataAssertionCandidates_noAnon h4
          · cases h4
      have hClsSound := materializedClassAxioms_sound opts hUnsat hSub
      have hTypSound := materializedTypeAxioms_sound opts (fun e he =>
        let h := hEntReal e he; ⟨h.2.1, h.2.2⟩)
      have hInfSound : ∀ a ∈ (dedupList (materializedClassAxioms hier opts ++
          materializedTypeAxioms real opts ++ extraInferred)).filter (fun ax => !o.contains ax),
          Entails dm o [a] ∧ axiomAnonDocs a = [] := by
        intro a ha
        have hmem := dedupList_mem (List.mem_filter.mp ha).1
        simp only [List.mem_append] at hmem
        rcases hmem with (h1 | h2) | h3
        · exact hClsSound a h1
        · exact hTypSound a h2
        · exact ⟨(hExtraSound a h3).2, hExtraNoAnon a h3⟩
      refine ⟨(fun hc => by cases hc), fun _ => ⟨hSat, hInfSound, fun hinc i => ?_⟩⟩
      simp only [hinc, ↓reduceIte]
      constructor
      · rintro ⟨assign, hsat⟩
        exact ⟨assign, fun a ha => hsat a (List.mem_append_left _ ha)⟩
      · rintro ⟨assign, hsat⟩
        refine ⟨assign, fun a ha => ?_⟩
        rcases List.mem_append.mp ha with ho | hi
        · exact hsat a ho
        · obtain ⟨hent, hno⟩ := hInfSound a hi
          exact entails_to_axiomHolds_of_noAnon hno hent hsat

/-- Certified materialization under Dedekind-cut `realDatatypeMap`. -/
def materializeReal (o : Ontology) (decls : List EntityDecl := [])
    (opts : MaterializeOptions := {}) : Option MaterializeResult :=
  materializeWith decideRealOntology? o decls opts

theorem materializeReal_entailed {o : Ontology} {decls : List EntityDecl}
    {opts : MaterializeOptions} {res : MaterializeResult}
    (hm : materializeReal o decls opts = some res) :
    (res.consistent = false → ¬ Satisfiable realDatatypeMap o) ∧
    (res.consistent = true →
      Satisfiable realDatatypeMap o ∧
      (∀ a ∈ res.inferredAxioms, Entails realDatatypeMap o [a] ∧ axiomAnonDocs a = []) ∧
      (opts.includeAsserted = true →
        ∀ i : Interpretation realDatatypeMap, models i res.materializedOntology ↔ models i o)) :=
  materializeWith_entailed decideRealOntology_iff hm

private def walkRoleChainTargets (outAdj inAdj : Std.HashMap (IRI × IRI) (List IRI))
    (x : IRI) : List Sabrina.ALC.OrientedRole → List IRI
  | [] => [x]
  | r :: rs =>
    (if r.2 then inAdj.getD (r.1, x) [] else outAdj.getD (r.1, x) []).flatMap fun y =>
      walkRoleChainTargets outAdj inAdj y rs

/-- Deterministic role-hierarchy, inverse, chain, and reflexivity closure over
    asserted named-individual `ObjectPropertyAssertion`s (every derived edge is
    provably entailed by `o` with zero tableau calls). -/
private def computeToldObjEdges (p : SROIQD.Problem) (inds : List IRI) :
    Std.HashSet (IRI × IRI × IRI) := Id.run do
  let mut edgeSet : Std.HashSet (IRI × IRI × IRI) := {}
  let mut outAdj : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut inAdj : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut byRole : Std.HashMap IRI (List (IRI × IRI)) := {}
  let addE (es : Std.HashSet (IRI × IRI × IRI)) (oa ia : Std.HashMap (IRI × IRI) (List IRI))
      (br : Std.HashMap IRI (List (IRI × IRI))) (r a b : IRI) :=
    if es.contains (r, a, b) then (es, oa, ia, br, false)
    else
      (es.insert (r, a, b),
       oa.insert (r, a) (b :: oa.getD (r, a) []),
       ia.insert (r, b) (a :: ia.getD (r, b) []),
       br.insert r ((a, b) :: br.getD r []),
       true)
  for (r, ia, ib) in p.objAssertions do
    match ia, ib with
    | .named a, .named b =>
      let (es', oa', ia', br', _) := addE edgeSet outAdj inAdj byRole r a b
      edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'
    | _, _ => pure ()
  for r in p.chars.reflexive do
    for a in inds do
      let (es', oa', ia', br', _) := addE edgeSet outAdj inAdj byRole r a a
      edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'
  let mut changed := true
  let mut iter := 0
  while changed && iter < 32 do
    changed := false
    iter := iter + 1
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
          for y in walkRoleChainTargets outAdj inAdj mid rs do
            if !edgeSet.contains (c.head, x, y) then newEdges := newEdges.push (c.head, x, y)
    for (rn, a, b) in newEdges do
      let (es', oa', ia', br', ch) := addE edgeSet outAdj inAdj byRole rn a b
      edgeSet := es'; outAdj := oa'; inAdj := ia'; byRole := br'
      if ch then changed := true
  return edgeSet

/-- Every recorded row lists the superproperties still possible at one edge of a
    previously unpopulated role. The edge comes from a checked model of `p` (or a
    checked TBox module component passing `checkNomRightOnComponent`). -/
private def roleWitnessSuperproperties (o : Ontology) (idx : FastLocality.LocalityIndex)
    (tctx? : Option FastClassification.TBoxFastCtx)
    (p : SROIQD.Problem) (baseModel : SROIQD.SROIQDModel)
    (base : SROIQD.ModelIndex baseModel) (props : List IRI) (numWorkers : Nat) :
    Std.HashMap IRI (Std.HashSet IRI) :=
  let missing := (props.filter fun r => (base.edgesByRole.getD r []).isEmpty).toArray
  let batchSize := 16
  let batches := List.range ((missing.size + batchSize - 1) / batchSize)
  let harvestFromModel (m : SROIQD.SROIQDModel) (roles : List IRI) : List (IRI × Std.HashSet IRI) :=
    let midx := SROIQD.ModelIndex.build m
    roles.filterMap fun r => do
      let (src, dst) ← (midx.edgesByRole.getD r []).head?
      let supers := props.foldl (fun (acc : Std.HashSet IRI) s =>
        if midx.edgeSet.contains (s, src, dst) then acc.insert s else acc) {}
      return (r, supers)
  -- Phase 1: fast batched witness seeding (16 roles per model)
  let phase1 : Std.HashMap IRI (Std.HashSet IRI) :=
    if p.classAssertions.length ≥ 64 then
      let core := FastClassification.counterWithoutIndividuals p
      let comps := (FastClassification.mapIndependent numWorkers (fun i =>
        let roles := (missing.extract (i * batchSize) ((i + 1) * batchSize)).toList
        let seeds := roles.map fun r => SROIQD.Concept.some (r, false) .top
        (SROIQD.proposeSeededCanonicalModel core seeds).map Subtype.val) batches).filterMap id
      let verified := FastClassification.checkComponentBatches p baseModel comps numWorkers
      let missingList := missing.toList
      let rows := FastClassification.mapIndependent numWorkers (fun m =>
        harvestFromModel m missingList) verified
      rows.foldl (fun acc batch => batch.foldl (fun acc (r, supers) =>
        match acc[r]? with
        | some prev => acc.insert r (prev.filter fun s => supers.contains s)
        | none => acc.insert r supers) acc) {}
    else
      let rows := FastClassification.mapIndependent numWorkers (fun i =>
        let roles := (missing.extract (i * batchSize) ((i + 1) * batchSize)).toList
        let seeds := roles.map fun r => SROIQD.Concept.some (r, false) .top
        match SROIQD.proposeSeededCanonicalModel p seeds with
        | none => []
        | some model => harvestFromModel model.val roles) batches
      rows.foldl (fun acc batch => batch.foldl (fun acc (r, supers) => acc.insert r supers) acc) {}
  -- Phase 2: per-role ⊥-local witness for any still-uncovered role so one failed batch
  -- never causes O(|props|) redundant SubObjectPropertyOf queries
  let stillMissing := missing.toList.filter fun r => !phase1.contains r
  if stillMissing.isEmpty then phase1
  else
    let singleRoleWitness (r : IRI) : Option (IRI × Std.HashSet IRI) :=
      let freshA := "urn:sabrina:rolewit_a"
      let freshB := "urn:sabrina:rolewit_b"
      let ax := Axiom.subObjectProperty (.named r) (.named r)
      let tryMod (mod : Ontology) (sigObjs : Option (List IRI)) (nomChecks? : Option (List (SROIQD.Concept × SROIQD.Concept))) :
          Option (IRI × Std.HashSet IRI) := do
        let cntOnt := Axiom.objectAssertion (.named r) (.named freshA) (.named freshB) :: mod
        let (_, pCnt) ← Normalize.normalizeWithDefs cntOnt
        let limits := SROIQD.Limits.forProblem pCnt
        match SROIQD.propose pCnt limits with
        | some (.model comp) =>
          let ok := pCnt.checkSimple && SROIQD.checkModel pCnt comp &&
            match nomChecks? with
            | some checks => FastClassification.checkNomRightOnComponent checks comp
            | none => true
          if !ok then none
          else
            let midx := SROIQD.ModelIndex.build comp
            let (src, dst) ← (midx.edgesByRole.getD r []).head?
            let sigSet? := sigObjs.map fun xs => xs.foldl (fun (s : Std.HashSet IRI) x => s.insert x) {}
            let supers := props.foldl (fun (acc : Std.HashSet IRI) s =>
              let inSig := match sigSet? with | some ss => ss.contains s | none => true
              if inSig && midx.edgeSet.contains (s, src, dst) then acc.insert s else acc) {}
            return (r, supers)
        | _ => none
      let viaTBox := tctx?.bind fun tctx =>
        let (modT, sigT) := FastLocality.extractBotModuleWithIndex tctx.tboxIdx tctx.tboxOnt (Profile.axiomSig ax)
        tryMod modT (some sigT.obj) (some tctx.nomChecks)
      match viaTBox with
      | some res => some res
      | none =>
        let (modFull, sigFull) := FastLocality.extractBotModuleWithIndex idx o (Profile.axiomSig ax)
        tryMod modFull (some sigFull.obj) none
    let extraRows := (FastClassification.mapIndependent numWorkers singleRoleWitness stillMissing).filterMap id
    extraRows.foldl (fun acc (r, supers) => acc.insert r supers) phase1

/-- Check extra entailments using sound & complete model-based pre-filtering
    (any assertion false in a kernel-verified model `m ⊨ o` cannot be entailed by `o`),
    deterministic positive ABox closure, local 2-hop ego-neighborhood monotonicity,
    and parallel ⊥-local module verification. -/
private def materializeExtraRuntime (o : Ontology) (decls : List EntityDecl) (props inds : List IRI)
    (hier : ClassHierarchy) (opts : MaterializeOptions)
    (verifiedModel? : Option (SROIQD.SROIQDModel × SROIQD.Problem) := none)
    (numWorkers : Nat := 8) : Option (List Axiom) := do
  let idx := FastLocality.LocalityIndex.build o
  let tctx? : Option FastClassification.TBoxFastCtx :=
    verifiedModel?.bind fun (_, p) => FastClassification.buildTBoxFastCtx o p
  let egoIdx? : Option FastClassification.ABoxEgoIndex :=
    if inds.length ≥ 32 then some (FastClassification.ABoxEgoIndex.build o) else none
  let axSeedInds : Axiom → List IRI
    | .objectAssertion _ (.named a) (.named b) => [a, b]
    | .dataAssertion _ (.named a) _ => [a]
    | .sameIndividuals is => is.filterMap fun | .named a => some a | _ => none
    | _ => []
  let checkAx (ax : Axiom) : Option (Option Axiom) := do
    match ax, tctx? with
    | .subObjectProperty (.named r) (.named s), some tctx =>
      if let some entailed := FastClassification.tryDecideSubObjPropViaTBox tctx r s then
        return if entailed then some ax else none
    | _, _ => pure ()
    let seed := Profile.axiomSig ax
    let provedLocal := match egoIdx?, axSeedInds ax with
      | some eidx, sInds@(_ :: _) =>
        let egoMod := (FastLocality.extractBotModuleFast (eidx.egoOntology sInds) seed).1
        decidesAxiomEntails fastConsistencyCheck egoMod ax == some true
      | _, _ => false
    if provedLocal then return some ax
    else
      let axioms := (FastLocality.extractBotModuleWithIndex idx o seed).1
      let entailed ← decidesAxiomEntails fastConsistencyCheck axioms ax
      return if entailed then some ax else none
  let checkBatch (cands : List Axiom) : Option (List Axiom) := do
    let results ← (FastClassification.mapIndependent numWorkers checkAx cands).mapM id
    return results.filterMap id
  let midx? : Option (Sigma fun m => SROIQD.Problem × SROIQD.ModelIndex m) :=
    verifiedModel?.map fun (m, p) => ⟨m, p, SROIQD.ModelIndex.build m⟩
  let posClosure? : Option FastClassification.PositiveABoxClosure :=
    if opts.includeObjectPropertyAssertions || opts.includeDataPropertyAssertions then
      match midx? with
      | some ⟨_, p, _⟩ =>
        let superMap : Std.HashMap IRI (List IRI) := Id.run do
          let mut m : Std.HashMap IRI (List IRI) := {}
          for (a, b) in hier.subsumptions do
            m := m.insert a (b :: m.getD a [])
          return m
        some (FastClassification.computePositiveABoxClosure p superMap inds)
      | none => none
    else none
  let mut inferred : Array Axiom := #[]
  if opts.includeSubObjectProperties then
    let mut toldSub : Std.HashSet (IRI × IRI) := {}
    if let some ⟨_, p, _⟩ := midx? then
      for (r, s) in Sabrina.ALC.roleClosure p.rules do
        if !r.2 && !s.2 && r.1 != s.1 then
          toldSub := toldSub.insert (r.1, s.1)
    let witnessSupers := match midx? with
      | some ⟨m, p, midx⟩ => roleWitnessSuperproperties o idx tctx? p m midx props numWorkers
      | none => {}
    let mut toCheck : Array Axiom := #[]
    for r in props do
      let possibleSupers := witnessSupers[r]?
      for s in props do
        if r != s then
          let ax := Axiom.subObjectProperty (.named r) (.named s)
          if toldSub.contains (r, s) then
            inferred := inferred.push ax
          else
            let refutedByModel := match possibleSupers, midx? with
              | some supers, _ => !supers.contains s
              | none, some ⟨_, _, midx⟩ =>
                (midx.edgesByRole.getD r []).any fun (u, v) => !midx.edgeSet.contains (s, u, v)
              | none, none => false
            if !refutedByModel then
              toCheck := toCheck.push ax
    let checked ← checkBatch toCheck.toList
    for ax in checked do inferred := inferred.push ax
  if opts.includeObjectPropertyAssertions then
    match midx? with
    | some ⟨m, p, midx⟩ =>
      let propSet : Std.HashSet IRI := props.foldl (fun s r => s.insert r) {}
      let toldEdges := match posClosure? with
        | some cl => cl.edges
        | none => computeToldObjEdges p inds
      let mut indsAtWorld : Std.HashMap Nat (List IRI) := {}
      for a in inds do
        let w := (midx.indVal (.named a)).val
        indsAtWorld := indsAtWorld.insert w (a :: indsAtWorld.getD w [])
      let mut seenEdge : Std.HashSet (IRI × IRI × IRI) := {}
      let mut toCheck : Array Axiom := #[]
      for (r, wa, wb) in m.graph.edges do
        if !propSet.contains r then continue
        let as := indsAtWorld.getD wa.val []
        if as.isEmpty then continue
        let bs := indsAtWorld.getD wb.val []
        if bs.isEmpty then continue
        for a in as do
          for b in bs do
            if !seenEdge.contains (r, a, b) then
              seenEdge := seenEdge.insert (r, a, b)
              let ax := Axiom.objectAssertion (.named r) (.named a) (.named b)
              if toldEdges.contains (r, a, b) then
                inferred := inferred.push ax
              else
                toCheck := toCheck.push ax
      let checked ← checkBatch toCheck.toList
      for ax in checked do inferred := inferred.push ax
    | none =>
      let mut toCheck : Array Axiom := #[]
      for r in props do
        for a in inds do
          for b in inds do
            toCheck := toCheck.push (.objectAssertion (.named r) (.named a) (.named b))
      let checked ← checkBatch toCheck.toList
      for ax in checked do inferred := inferred.push ax
  if opts.includeSameIndividuals then
    match midx? with
    | some ⟨_, _, midx⟩ =>
      let mut byWorld : Std.HashMap Nat (List IRI) := {}
      for a in inds do
        let w := (midx.indVal (.named a)).val
        byWorld := byWorld.insert w (a :: byWorld.getD w [])
      let mut toCheck : Array Axiom := #[]
      for (_, grp) in byWorld do
        let arr := grp.reverse.toArray
        if arr.size ≥ 2 then
          for h : i in [:arr.size] do
            for h' : j in [i + 1:arr.size] do
              toCheck := toCheck.push (.sameIndividuals [.named arr[i], .named arr[j]])
      let checked ← checkBatch toCheck.toList
      for ax in checked do inferred := inferred.push ax
    | none =>
      let individuals := inds.toArray
      let mut toCheck : Array Axiom := #[]
      for h : i in [:individuals.size] do
        for h' : j in [i + 1:individuals.size] do
          toCheck := toCheck.push (.sameIndividuals [.named individuals[i], .named individuals[j]])
      let checked ← checkBatch toCheck.toList
      for ax in checked do inferred := inferred.push ax
  if opts.includeDataPropertyAssertions then
    let lits := dataCandidateLiterals o
    if !lits.isEmpty then
      let dProps := dataCandidateProperties o decls
      let assertedSet : Std.HashSet (IRI × IRI × String × IRI) := Id.run do
        let mut s : Std.HashSet (IRI × IRI × String × IRI) := {}
        for ax in o do
          match ax with
          | .dataAssertion dp (.named ind) lit => s := s.insert (dp, ind, lit.lexical, lit.datatype)
          | _ => pure ()
        return s
      match midx? with
      | some ⟨_, _, midx⟩ =>
        let toldData : Std.HashMap (IRI × IRI) (List Datatypes.Value) :=
          match posClosure? with
          | some cl => cl.data
          | none => {}
        let decodedLits : List (Literal × Datatypes.Value) :=
          lits.filterMap fun l => (Datatypes.decodeLiteral l).map (l, ·)
        let mut toCheck : Array Axiom := #[]
        for dp in dProps do
          for ind in inds do
            let vals := midx.dataVals dp (midx.indVal (.named ind))
            if vals.isEmpty then continue
            let toldVals := toldData.getD (dp, ind) []
            for (lit, v) in decodedLits do
              if vals.contains v && !assertedSet.contains (dp, ind, lit.lexical, lit.datatype) then
                let ax := Axiom.dataAssertion dp (.named ind) lit
                if toldVals.contains v then
                  inferred := inferred.push ax
                else
                  toCheck := toCheck.push ax
        let checked ← checkBatch toCheck.toList
        for ax in checked do inferred := inferred.push ax
      | none =>
        let mut toCheck : Array Axiom := #[]
        for dp in dProps do
          for ind in inds do
            for lit in lits do
              if !assertedSet.contains (dp, ind, lit.lexical, lit.datatype) then
                toCheck := toCheck.push (.dataAssertion dp (.named ind) lit)
        let checked ← checkBatch toCheck.toList
        for ax in checked do inferred := inferred.push ax
  return inferred.toList

/-- Fast hybrid runtime materializer that reuses a single kernel-verified model
    and its hierarchy across classification, realization, and extra entailments. -/
def materializeOntologyRuntime (o : Ontology) (decls : List EntityDecl := [])
    (opts : MaterializeOptions := {}) (numWorkers : Nat := 8)
    (auxiliaryClass? : Option IRI := none) : Option MaterializeResult := do
  let verifiedModel? := FastClassification.proposeVerifiedModel o
  let m0? := verifiedModel?.map Prod.fst
  let p0? := verifiedModel?.map Prod.snd
  let hier ← FastClassification.classifyOntologyFastWithModelRuntime o decls numWorkers m0? auxiliaryClass?
  if !hier.consistent then
    return {
      consistent := false
      assertedAxioms := o
      inferredAxioms := []
      materializedOntology := if opts.includeAsserted then o else []
    }
  let real ← FastClassification.realizeFromHierarchyWithModelRuntime o decls hier numWorkers m0? auxiliaryClass? p0?
  let extraInferred ←
    if opts.includeSubObjectProperties || opts.includeObjectPropertyAssertions ||
        opts.includeSameIndividuals || opts.includeDataPropertyAssertions then do
      let props := if opts.includeSubObjectProperties || opts.includeObjectPropertyAssertions then
        collectNamedObjectProperties o decls else []
      materializeExtraRuntime o decls props real.individuals hier opts verifiedModel? numWorkers
    else pure []
  let rawInferred :=
    materializedClassAxioms hier opts ++ materializedTypeAxioms real opts ++ extraInferred
  let assertedByKey : Std.HashMap String (List Axiom) := Id.run do
    let mut m : Std.HashMap String (List Axiom) := {}
    for a in o do
      let k := renderAxiom a
      m := m.insert k (a :: m.getD k [])
    return m
  let mut seenByKey : Std.HashMap String (List Axiom) := {}
  let mut freshArr : Array Axiom := #[]
  for ax in rawInferred do
    let k := renderAxiom ax
    let inAsserted := (assertedByKey.getD k []).contains ax
    let inSeen := (seenByKey.getD k []).contains ax
    if !inAsserted && !inSeen then
      seenByKey := seenByKey.insert k (ax :: seenByKey.getD k [])
      freshArr := freshArr.push ax
  let freshInferred := freshArr.toList
  return {
    consistent := true
    assertedAxioms := o
    inferredAxioms := freshInferred
    materializedOntology := if opts.includeAsserted then o ++ freshInferred else freshInferred
  }

/-! ### 3. Output Formats & Serialization (`.ofn` / `.ttl` / `.owl`) -/

inductive OutputFormat where
  | ofn
  | ttl
  | rdfxml
  deriving DecidableEq, Repr

def OutputFormat.name : OutputFormat → String
  | .ofn => "ofn"
  | .ttl => "ttl"
  | .rdfxml => "rdfxml"

def OutputFormat.ofString? (s : String) : Option OutputFormat :=
  match s.toLower with
  | "ofn" | "fss" | "functional" => some .ofn
  | "ttl" | "turtle" => some .ttl
  | "owl" | "rdf" | "rdfxml" | "rdf/xml" | "xml" => some .rdfxml
  | _ => none

def OutputFormat.fromPath (path : String) : OutputFormat :=
  let low := path.toLower
  if low.endsWith ".ttl" || low.endsWith ".turtle" then .ttl
  else if low.endsWith ".owl" || low.endsWith ".rdf" || low.endsWith ".xml" then .rdfxml
  else .ofn

private def encodeAnnotSubject : AnnotationSubject → RDFTerm
  | .iri v => .iri v
  | .anonymous _ loc => .bnode loc

private def encodeAnnotValue : AnnotationValue → RDFTerm
  | .iri v => .iri v
  | .anonymous _ loc => .bnode loc
  | .literal l => .literal l.lexical l.datatype none

private def annotationAxiomTriple : AnnotationAxiom → RDFTriple
  | .assertion p s v => ⟨encodeAnnotSubject s, p, encodeAnnotValue v⟩
  | .subProperty sub sup => ⟨.iri sub, rdfsSubPropertyOf, .iri sup⟩
  | .domain p dom => ⟨.iri p, rdfsDomain, .iri dom⟩
  | .range p rng => ⟨.iri p, rdfsRange, .iri rng⟩

/-- Render a materialized ontology (with declarations, annotations, prefixes,
    optional ontology/version IRIs, and optional DL-Safe SWRL rules) into
    `.ofn`, `.ttl`, or `.owl` (RDF/XML). -/
def renderMaterialized (fmt : OutputFormat) (decls : List EntityDecl)
    (annots : List AnnotationAxiom) (ont : Ontology) (prefixes : PrefixMap := [])
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (rules : List SWRL.SWRLRule := []) : String :=
  match fmt with
  | .ofn =>
    renderDocumentOFN decls annots ont prefixes ontIRI verIRI [] rules
  | .ttl =>
    let baseGraph := encodeOntologyRDF decls ont ontIRI verIRI [] rules
    let fullGraph : RDFGraph := {
      triples := baseGraph.triples ++ annots.map annotationAxiomTriple
      prefixes := prefixes
    }
    renderTurtle fullGraph
  | .rdfxml =>
    let baseGraph := encodeOntologyRDF decls ont ontIRI verIRI [] rules
    let fullGraph : RDFGraph := {
      triples := baseGraph.triples ++ annots.map annotationAxiomTriple
      prefixes := prefixes
    }
    renderRDFXML fullGraph

end Sabrina.OWL2.Materialize
