import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastClassification
import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.RDF.Serialize

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
            else [])
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
        rcases hcand with (h1 | h2) | h3
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

/-- Check extra entailments in export order without allocating the candidate cross products. -/
private def materializeExtraRuntime (o : Ontology) (props inds : List IRI)
    (opts : MaterializeOptions) : Option (List Axiom) := do
  let idx := FastLocality.LocalityIndex.build o
  let emit (inferred : Array Axiom) (ax : Axiom) : Option (Array Axiom) := do
    let axioms := (FastLocality.extractBotModuleWithIndex idx o (Profile.axiomSig ax)).1
    let entailed ← decidesAxiomEntails fastConsistencyCheck axioms ax
    return if entailed then inferred.push ax else inferred
  let mut inferred := #[]
  if opts.includeSubObjectProperties then
    for r in props do
      for s in props do
        if r != s then
          inferred ← emit inferred (.subObjectProperty (.named r) (.named s))
  if opts.includeObjectPropertyAssertions then
    for r in props do
      for a in inds do
        for b in inds do
          inferred ← emit inferred (.objectAssertion (.named r) (.named a) (.named b))
  if opts.includeSameIndividuals then
    let individuals := inds.toArray
    for h : i in [:individuals.size] do
      for h' : j in [i + 1:individuals.size] do
        inferred ← emit inferred (.sameIndividuals [.named individuals[i], .named individuals[j]])
  return inferred.toList

/-- Fast hybrid runtime materializer that reuses its hierarchy during ABox realization. -/
def materializeOntologyRuntime (o : Ontology) (decls : List EntityDecl := [])
    (opts : MaterializeOptions := {}) : Option MaterializeResult := do
  let hier ← FastClassification.classifyOntologyFastRuntime o decls
  if !hier.consistent then
    return {
      consistent := false
      assertedAxioms := o
      inferredAxioms := []
      materializedOntology := if opts.includeAsserted then o else []
    }
  let real ← FastClassification.realizeFromHierarchyRuntime o decls hier
  let extraInferred ←
    if opts.includeSubObjectProperties || opts.includeObjectPropertyAssertions ||
        opts.includeSameIndividuals then do
      let props := if opts.includeSubObjectProperties || opts.includeObjectPropertyAssertions then
        collectNamedObjectProperties o decls else []
      materializeExtraRuntime o props real.individuals opts
    else pure []
  let rawInferred :=
    materializedClassAxioms hier opts ++ materializedTypeAxioms real opts ++ extraInferred
  let freshInferred := (dedupList rawInferred).filter fun ax => !o.contains ax
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
    and optional ontology/version IRIs) into `.ofn`, `.ttl`, or `.owl` (RDF/XML). -/
def renderMaterialized (fmt : OutputFormat) (decls : List EntityDecl)
    (annots : List AnnotationAxiom) (ont : Ontology) (prefixes : PrefixMap := [])
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none) : String :=
  match fmt with
  | .ofn =>
    renderDocumentOFN decls annots ont prefixes ontIRI verIRI []
  | .ttl =>
    let baseGraph := encodeOntologyRDF decls ont ontIRI verIRI []
    let fullGraph : RDFGraph := {
      triples := baseGraph.triples ++ annots.map annotationAxiomTriple
      prefixes := prefixes
    }
    renderTurtle fullGraph
  | .rdfxml =>
    let baseGraph := encodeOntologyRDF decls ont ontIRI verIRI []
    let fullGraph : RDFGraph := {
      triples := baseGraph.triples ++ annots.map annotationAxiomTriple
      prefixes := prefixes
    }
    renderRDFXML fullGraph

end Sabrina.OWL2.Materialize
