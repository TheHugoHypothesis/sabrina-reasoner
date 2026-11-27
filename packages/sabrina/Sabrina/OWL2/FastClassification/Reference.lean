import Sabrina.OWL2.FastClassification.Runtime

/-! Certified Enhanced Traversal classification and countermodel harvesting. -/

namespace Sabrina.OWL2.FastClassification

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Profile
open Sabrina.OWL2.FastLocality
open Sabrina.OWL2.EL
open Sabrina.OWL2.Classification
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.Normalize
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

private def orderedPairs (xs : List IRI) : List (IRI × IRI) :=
  xs.flatMap fun a => xs.map fun b => (a, b)

private theorem mem_orderedPairs_iff {xs : List IRI} {a b : IRI} :
    (a, b) ∈ orderedPairs xs ↔ a ∈ xs ∧ b ∈ xs := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, rfl⟩; exact ⟨hx, hy⟩
  · rintro ⟨ha, hb⟩; exact ⟨a, ha, b, hb, rfl, rfl⟩

/-! ### Semantic closure lemmas for subsumption and satisfiability -/

private theorem entails_sub_refl {dm : DatatypeMap} (o : Ontology) (a : IRI) :
    Entails dm o [.subClassOf (.named a) (.named a)] := by
  intro i _
  refine satisfies_models fun q hq => ?_
  simp only [List.mem_singleton] at hq; subst hq
  exact fun _ hx => hx

private theorem entails_sub_trans {dm : DatatypeMap} {o : Ontology} {a b c : IRI}
    (h1 : Entails dm o [.subClassOf (.named a) (.named b)])
    (h2 : Entails dm o [.subClassOf (.named b) (.named c)]) :
    Entails dm o [.subClassOf (.named a) (.named c)] := by
  intro i hmod
  obtain ⟨_, hs1⟩ := h1 i hmod
  obtain ⟨_, hs2⟩ := h2 i hmod
  have hab := hs1 _ (List.mem_singleton.mpr rfl)
  have hbc := hs2 _ (List.mem_singleton.mpr rfl)
  refine satisfies_models fun q hq => ?_
  simp only [List.mem_singleton] at hq; subst hq
  exact fun x hx => hbc x (hab x hx)

private theorem entails_sub_of_mem {dm : DatatypeMap} {o : Ontology} {a b : IRI}
    (hmem : .subClassOf (.named a) (.named b) ∈ o) :
    Entails dm o [.subClassOf (.named a) (.named b)] := by
  intro i ⟨assign, hsat⟩
  refine ⟨assign, fun q hq => ?_⟩
  simp only [List.mem_singleton] at hq; subst hq
  exact hsat _ hmem

private theorem entails_sub_of_equiv_mem {dm : DatatypeMap} {o : Ontology}
    {cs : List ClassExpr} {a b : IRI}
    (hmem : .equivalentClasses cs ∈ o)
    (ha : .named a ∈ cs) (hb : .named b ∈ cs) :
    Entails dm o [.subClassOf (.named a) (.named b)] := by
  intro i ⟨assign, hsat⟩
  refine ⟨assign, fun q hq => ?_⟩
  simp only [List.mem_singleton] at hq; subst hq
  intro x hx
  exact (hsat _ hmem (.named a) ha (.named b) hb x).mp hx

private theorem not_entails_upward {dm : DatatypeMap} {o : Ontology} {a b d : IRI}
    (hab : Entails dm o [.subClassOf (.named a) (.named b)])
    (hnad : ¬ Entails dm o [.subClassOf (.named a) (.named d)]) :
    ¬ Entails dm o [.subClassOf (.named b) (.named d)] :=
  fun hbd => hnad (entails_sub_trans hab hbd)

private theorem not_entails_downward {dm : DatatypeMap} {o : Ontology} {a b d : IRI}
    (hbd : Entails dm o [.subClassOf (.named b) (.named d)])
    (hnad : ¬ Entails dm o [.subClassOf (.named a) (.named d)]) :
    ¬ Entails dm o [.subClassOf (.named a) (.named b)] :=
  fun hab => hnad (entails_sub_trans hab hbd)

private theorem sat_upward {dm : DatatypeMap} {o : Ontology} {a b : IRI}
    (hab : Entails dm o [.subClassOf (.named a) (.named b)])
    (hsatA : ¬ Entails dm o [.subClassOf (.named a) (.named nothing)]) :
    ¬ Entails dm o [.subClassOf (.named b) (.named nothing)] :=
  not_entails_upward hab hsatA

private theorem unsat_downward {dm : DatatypeMap} {o : Ontology} {a b : IRI}
    (hab : Entails dm o [.subClassOf (.named a) (.named b)])
    (hunsatB : Entails dm o [.subClassOf (.named b) (.named nothing)]) :
    Entails dm o [.subClassOf (.named a) (.named nothing)] :=
  entails_sub_trans hab hunsatB

/-! ### Certified Enhanced Traversal with `FastLocality.LocalityIndex` -/

/-- Certified deduction cache maintained during Enhanced Traversal. -/
structure ClsCache where
  knownTrue : Std.HashSet (IRI × IRI) := {}
  knownFalse : Std.HashSet (IRI × IRI) := {}
  satSet : Std.HashSet IRI := {}
  unsatSet : Std.HashSet IRI := {}

/-- Soundness invariant for `ClsCache` relative to `(dm, o)`. -/
def ClsCache.Valid (dm : DatatypeMap) (o : Ontology) (st : ClsCache) : Prop :=
  (∀ p, st.knownTrue.contains p = true → Entails dm o [.subClassOf (.named p.1) (.named p.2)]) ∧
  (∀ p, st.knownFalse.contains p = true → ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)]) ∧
  (∀ c, st.satSet.contains c = true → ¬ Entails dm o [.subClassOf (.named c) (.named nothing)]) ∧
  (∀ c, st.unsatSet.contains c = true → Entails dm o [.subClassOf (.named c) (.named nothing)])

private theorem hashSet_contains_insert {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (s : Std.HashSet α) (a x : α) :
    (s.insert a).contains x = true ↔ x == a ∨ s.contains x = true := by
  simp only [Std.HashSet.contains_iff_mem, Std.HashSet.mem_insert, beq_iff_eq]
  exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
         fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩

private theorem ClsCache.valid_empty {dm : DatatypeMap} {o : Ontology} :
    ClsCache.Valid dm o {} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x hx <;> simp at hx

private theorem ClsCache.valid_insertTrue {dm : DatatypeMap} {o : Ontology} {st : ClsCache}
    (hv : st.Valid dm o) {p : IRI × IRI}
    (hp : Entails dm o [.subClassOf (.named p.1) (.named p.2)]) :
    ({ st with knownTrue := st.knownTrue.insert p }).Valid dm o := by
  refine ⟨fun q hq => ?_, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  rcases (hashSet_contains_insert st.knownTrue p q).mp hq with heq | hmem
  · have : q = p := beq_iff_eq.mp heq; subst this; exact hp
  · exact hv.1 q hmem

private theorem ClsCache.valid_insertFalse {dm : DatatypeMap} {o : Ontology} {st : ClsCache}
    (hv : st.Valid dm o) {p : IRI × IRI}
    (hp : ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)]) :
    ({ st with knownFalse := st.knownFalse.insert p }).Valid dm o := by
  refine ⟨hv.1, fun q hq => ?_, hv.2.2.1, hv.2.2.2⟩
  rcases (hashSet_contains_insert st.knownFalse p q).mp hq with heq | hmem
  · have : q = p := beq_iff_eq.mp heq; subst this; exact hp
  · exact hv.2.1 q hmem

private theorem ClsCache.valid_insertSat {dm : DatatypeMap} {o : Ontology} {st : ClsCache}
    (hv : st.Valid dm o) {c : IRI}
    (hc : ¬ Entails dm o [.subClassOf (.named c) (.named nothing)]) :
    ({ st with satSet := st.satSet.insert c }).Valid dm o := by
  refine ⟨hv.1, hv.2.1, fun q hq => ?_, hv.2.2.2⟩
  rcases (hashSet_contains_insert st.satSet c q).mp hq with heq | hmem
  · have : q = c := beq_iff_eq.mp heq; subst this; exact hc
  · exact hv.2.2.1 q hmem

private theorem ClsCache.valid_insertUnsat {dm : DatatypeMap} {o : Ontology} {st : ClsCache}
    (hv : st.Valid dm o) {c : IRI}
    (hc : Entails dm o [.subClassOf (.named c) (.named nothing)]) :
    ({ st with unsatSet := st.unsatSet.insert c }).Valid dm o := by
  refine ⟨hv.1, hv.2.1, hv.2.2.1, fun q hq => ?_⟩
  rcases (hashSet_contains_insert st.unsatSet c q).mp hq with heq | hmem
  · have : q = c := beq_iff_eq.mp heq; subst this; exact hc
  · exact hv.2.2.2 q hmem

/-- Seed reflexivity `(c, c)` into `knownTrue`. -/
private def seedReflexive (cs : List IRI) (st : ClsCache) : ClsCache :=
  cs.foldl (fun acc c => { acc with knownTrue := acc.knownTrue.insert (c, c) }) st

private theorem seedReflexive_valid {dm : DatatypeMap} {o : Ontology} (cs : List IRI) :
    ∀ st, st.Valid dm o → (seedReflexive cs st).Valid dm o := by
  induction cs with
  | nil => intro st hv; exact hv
  | cons c tl ih =>
    intro st hv
    exact ih _ (ClsCache.valid_insertTrue hv (entails_sub_refl o c))

private def seedEquivPairs (allCs : List ClassExpr) (st : ClsCache) : ClsCache :=
  allCs.foldl (fun s1 c1 =>
    match c1 with
    | .named a =>
      allCs.foldl (fun s2 c2 =>
        match c2 with
        | .named b => { s2 with knownTrue := s2.knownTrue.insert (a, b) }
        | _ => s2) s1
    | _ => s1) st

private theorem seedEquivPairs_valid {dm : DatatypeMap} {o : Ontology}
    {cs : List ClassExpr} (hmem : .equivalentClasses cs ∈ o) (st : ClsCache)
    (hv : st.Valid dm o) : (seedEquivPairs cs st).Valid dm o := by
  have inner : ∀ (a : IRI), ClassExpr.named a ∈ cs → ∀ (ys : List ClassExpr),
      (∀ y ∈ ys, y ∈ cs) → ∀ (s : ClsCache), s.Valid dm o →
      (ys.foldl (fun s2 c2 => match c2 with
        | ClassExpr.named b => { s2 with knownTrue := s2.knownTrue.insert (a, b) }
        | _ => s2) s).Valid dm o := by
    intro a ha ys
    induction ys with
    | nil => intro _ s hs; exact hs
    | cons y rest ih =>
      intro hsub s hs
      simp only [List.foldl_cons]
      cases y with
      | named b =>
        exact ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) _
          (ClsCache.valid_insertTrue hs (entails_sub_of_equiv_mem hmem ha (hsub _ (List.mem_cons_self ..))))
      | _ => exact ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) s hs
  have outer : ∀ (xs : List ClassExpr), (∀ x ∈ xs, x ∈ cs) → ∀ (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s1 c1 => match c1 with
        | ClassExpr.named a =>
          cs.foldl (fun s2 c2 => match c2 with
            | ClassExpr.named b => { s2 with knownTrue := s2.knownTrue.insert (a, b) }
            | _ => s2) s1
        | _ => s1) s).Valid dm o := by
    intro xs
    induction xs with
    | nil => intro _ s hs; exact hs
    | cons x rest ih =>
      intro hsub s hs
      simp only [List.foldl_cons]
      cases x with
      | named a =>
        exact ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) _
          (inner a (hsub _ (List.mem_cons_self ..)) cs (fun _ h => h) s hs)
      | _ => exact ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) s hs
  exact outer cs (fun _ h => h) st hv

/-- Seed syntactic told subsumptions (`SubClassOf` and `EquivalentClasses`) from `o`. -/
private def seedToldAxioms (xs : Ontology) (st : ClsCache) : ClsCache :=
  xs.foldl (fun acc ax =>
    match ax with
    | .subClassOf (.named a) (.named b) => { acc with knownTrue := acc.knownTrue.insert (a, b) }
    | .equivalentClasses cs => seedEquivPairs cs acc
    | _ => acc) st

private theorem seedToldAxioms_valid {dm : DatatypeMap} {o : Ontology} (xs : Ontology)
    (hsub : ∀ ax ∈ xs, ax ∈ o) :
    ∀ st, st.Valid dm o → (seedToldAxioms xs st).Valid dm o := by
  induction xs with
  | nil => intro st hv; exact hv
  | cons ax tl ih =>
    intro st hv
    simp only [seedToldAxioms, List.foldl_cons]
    have htl := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    have hmem : ax ∈ o := hsub ax (List.mem_cons_self ..)
    cases ax with
    | subClassOf c1 c2 =>
      cases c1 with
      | named a =>
        cases c2 with
        | named b => exact htl _ (ClsCache.valid_insertTrue hv (entails_sub_of_mem hmem))
        | _ => exact htl st hv
      | _ => exact htl st hv
    | equivalentClasses cs => exact htl _ (seedEquivPairs_valid hmem st hv)
    | _ => exact htl st hv

/-- Close `knownTrue` under transitivity over `namedClasses` (Floyd–Warshall over `HashSet`). -/
private def closeTransitive (namedClasses : List IRI) (st : ClsCache) : ClsCache :=
  namedClasses.foldl (fun s0 mid =>
    let preds := namedClasses.filter fun a => s0.knownTrue.contains (a, mid)
    let succs := namedClasses.filter fun b => s0.knownTrue.contains (mid, b)
    preds.foldl (fun s1 a =>
      succs.foldl (fun s2 b =>
        if s2.knownTrue.contains (a, mid) && s2.knownTrue.contains (mid, b) then
          { s2 with knownTrue := s2.knownTrue.insert (a, b) }
        else s2) s1) s0) st

private theorem closeTransitive_valid {dm : DatatypeMap} {o : Ontology}
    (namedClasses : List IRI) (st : ClsCache) (hv : st.Valid dm o) :
    (closeTransitive namedClasses st).Valid dm o := by
  have innerSucc : ∀ (mid a : IRI) (bs : List IRI) (s : ClsCache), s.Valid dm o →
      (bs.foldl (fun s2 b =>
        if s2.knownTrue.contains (a, mid) && s2.knownTrue.contains (mid, b) then
          { s2 with knownTrue := s2.knownTrue.insert (a, b) }
        else s2) s).Valid dm o := by
    intro mid a bs
    induction bs with
    | nil => intro s hs; exact hs
    | cons b tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      cases hcond : s.knownTrue.contains (a, mid) && s.knownTrue.contains (mid, b)
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih s hs
      · simp only [↓reduceIte]
        have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcond
        exact ih _ (ClsCache.valid_insertTrue hs (entails_sub_trans (hs.1 (a, mid) h1) (hs.1 (mid, b) h2)))
  have innerPred : ∀ (mid : IRI) (ps ss : List IRI) (s : ClsCache), s.Valid dm o →
      (ps.foldl (fun s1 a =>
        ss.foldl (fun s2 b =>
          if s2.knownTrue.contains (a, mid) && s2.knownTrue.contains (mid, b) then
            { s2 with knownTrue := s2.knownTrue.insert (a, b) }
          else s2) s1) s).Valid dm o := by
    intro mid ps ss
    induction ps with
    | nil => intro s hs; exact hs
    | cons a tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      exact ih _ (innerSucc mid a ss s hs)
  have outer : ∀ (ms : List IRI) (s : ClsCache), s.Valid dm o →
      (ms.foldl (fun s0 mid =>
        let preds := namedClasses.filter fun a => s0.knownTrue.contains (a, mid)
        let succs := namedClasses.filter fun b => s0.knownTrue.contains (mid, b)
        preds.foldl (fun s1 a =>
          succs.foldl (fun s2 b =>
            if s2.knownTrue.contains (a, mid) && s2.knownTrue.contains (mid, b) then
              { s2 with knownTrue := s2.knownTrue.insert (a, b) }
            else s2) s1) s0) s).Valid dm o := by
    intro ms
    induction ms with
    | nil => intro s hs; exact hs
    | cons mid tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      exact ih _ (innerPred mid _ _ s hs)
  exact outer namedClasses st hv

/-- Propagate newly proved `(a, b)` into `knownTrue` with eager transitive closure over `namedClasses`. -/
private def insertTrueAndClose (namedClasses : List IRI) (a b : IRI) (st : ClsCache) : ClsCache :=
  let s0 := { st with knownTrue := st.knownTrue.insert (a, b) }
  let preds := namedClasses.filter fun x => s0.knownTrue.contains (x, a)
  let succs := namedClasses.filter fun y => s0.knownTrue.contains (b, y)
  preds.foldl (fun s1 x =>
    succs.foldl (fun s2 y =>
      if s2.knownTrue.contains (x, a) && s2.knownTrue.contains (a, b) && s2.knownTrue.contains (b, y) then
        { s2 with knownTrue := s2.knownTrue.insert (x, y) }
      else s2) s1) s0

private theorem insertTrueAndClose_valid {dm : DatatypeMap} {o : Ontology}
    (namedClasses : List IRI) {a b : IRI} {st : ClsCache} (hv : st.Valid dm o)
    (hab : Entails dm o [.subClassOf (.named a) (.named b)]) :
    (insertTrueAndClose namedClasses a b st).Valid dm o := by
  have hs0 : ({ st with knownTrue := st.knownTrue.insert (a, b) }).Valid dm o :=
    ClsCache.valid_insertTrue hv hab
  have innerY : ∀ (x : IRI) (ys : List IRI) (s : ClsCache), s.Valid dm o →
      (ys.foldl (fun s2 y =>
        if s2.knownTrue.contains (x, a) && s2.knownTrue.contains (a, b) && s2.knownTrue.contains (b, y) then
          { s2 with knownTrue := s2.knownTrue.insert (x, y) }
        else s2) s).Valid dm o := by
    intro x ys
    induction ys with
    | nil => intro s hs; exact hs
    | cons y tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      cases hc : (s.knownTrue.contains (x, a) && s.knownTrue.contains (a, b) && s.knownTrue.contains (b, y))
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih s hs
      · simp only [↓reduceIte]
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨h1, h2⟩, h3⟩ := hc
        exact ih _ (ClsCache.valid_insertTrue hs
          (entails_sub_trans (entails_sub_trans (hs.1 (x, a) h1) (hs.1 (a, b) h2)) (hs.1 (b, y) h3)))
  have outerX : ∀ (xs ys : List IRI) (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s1 x =>
        ys.foldl (fun s2 y =>
          if s2.knownTrue.contains (x, a) && s2.knownTrue.contains (a, b) && s2.knownTrue.contains (b, y) then
            { s2 with knownTrue := s2.knownTrue.insert (x, y) }
          else s2) s1) s).Valid dm o := by
    intro xs ys
    induction xs with
    | nil => intro s hs; exact hs
    | cons x tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      exact ih _ (innerY x ys s hs)
  exact outerX _ _ _ hs0

/-- Propagate newly refuted `(a, b)` into `knownFalse` with Enhanced Traversal upward/downward closure:
    `a ⊑ x ∧ a ⋢ b → x ⋢ b` and `y ⊑ b ∧ a ⋢ b → a ⋢ y`. -/
private def insertFalseAndClose (namedClasses : List IRI) (a b : IRI) (st : ClsCache) : ClsCache :=
  let s0 := { st with knownFalse := st.knownFalse.insert (a, b) }
  let supsA := namedClasses.filter fun x => s0.knownTrue.contains (a, x)
  let subsB := namedClasses.filter fun y => s0.knownTrue.contains (y, b)
  let s1 := supsA.foldl (fun s x =>
    if s.knownTrue.contains (a, x) && s.knownFalse.contains (a, b) then
      { s with knownFalse := s.knownFalse.insert (x, b) }
    else s) s0
  subsB.foldl (fun s y =>
    if s.knownTrue.contains (y, b) && s.knownFalse.contains (a, b) then
      { s with knownFalse := s.knownFalse.insert (a, y) }
    else s) s1

private theorem insertFalseAndClose_valid {dm : DatatypeMap} {o : Ontology}
    (namedClasses : List IRI) {a b : IRI} {st : ClsCache} (hv : st.Valid dm o)
    (hnab : ¬ Entails dm o [.subClassOf (.named a) (.named b)]) :
    (insertFalseAndClose namedClasses a b st).Valid dm o := by
  have hs0 : ({ st with knownFalse := st.knownFalse.insert (a, b) }).Valid dm o :=
    ClsCache.valid_insertFalse hv hnab
  have step1 : ∀ (xs : List IRI) (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s x =>
        if s.knownTrue.contains (a, x) && s.knownFalse.contains (a, b) then
          { s with knownFalse := s.knownFalse.insert (x, b) }
        else s) s).Valid dm o := by
    intro xs
    induction xs with
    | nil => intro s hs; exact hs
    | cons x tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      cases hc : s.knownTrue.contains (a, x) && s.knownFalse.contains (a, b)
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih s hs
      · simp only [↓reduceIte]
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
        exact ih _ (ClsCache.valid_insertFalse hs (not_entails_upward (hs.1 _ h1) (hs.2.1 _ h2)))
  have step2 : ∀ (ys : List IRI) (s : ClsCache), s.Valid dm o →
      (ys.foldl (fun s y =>
        if s.knownTrue.contains (y, b) && s.knownFalse.contains (a, b) then
          { s with knownFalse := s.knownFalse.insert (a, y) }
        else s) s).Valid dm o := by
    intro ys
    induction ys with
    | nil => intro s hs; exact hs
    | cons y tl ih =>
      intro s hs
      simp only [List.foldl_cons]
      cases hc : s.knownTrue.contains (y, b) && s.knownFalse.contains (a, b)
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih s hs
      · simp only [↓reduceIte]
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
        exact ih _ (ClsCache.valid_insertFalse hs (not_entails_downward (hs.1 _ h1) (hs.2.1 _ h2)))
  exact step2 _ _ (step1 _ _ hs0)

private theorem not_entails_sub_of_disjoint_sub {dm : DatatypeMap} {o : Ontology}
    {cs : List ClassExpr} {a b x y : IRI}
    (hmem : .disjointClasses cs ∈ o)
    (hdisj : ∃ (i1 i2 : Nat), i1 ≠ i2 ∧ cs[i1]? = some (ClassExpr.named a) ∧ cs[i2]? = some (ClassExpr.named b))
    (hxa : Entails dm o [.subClassOf (.named x) (.named a)])
    (hyb : Entails dm o [.subClassOf (.named y) (.named b)])
    (hsatX : ¬ Entails dm o [.subClassOf (.named x) (.named nothing)]) :
    ¬ Entails dm o [.subClassOf (.named x) (.named y)] := by
  intro hxy
  have hxb : Entails dm o [.subClassOf (.named x) (.named b)] := entails_sub_trans hxy hyb
  apply hsatX
  intro i hmod
  obtain ⟨assign, hsat⟩ := hmod
  have hpw := hsat _ hmem
  obtain ⟨_, hsxa⟩ := hxa i ⟨assign, hsat⟩
  obtain ⟨_, hsxb⟩ := hxb i ⟨assign, hsat⟩
  have hsubA := hsxa _ (List.mem_singleton.mpr rfl)
  have hsubB := hsxb _ (List.mem_singleton.mpr rfl)
  have hdisjAB : ∀ z, ¬ (classHolds (i.withAnonymous assign) z (.named a) ∧
      classHolds (i.withAnonymous assign) z (.named b)) := by
    obtain ⟨i1, i2, hne, h1, h2⟩ := hdisj
    obtain ⟨hlt1, he1⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hlt2, he2⟩ := List.getElem?_eq_some_iff.mp h2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hp := List.pairwise_iff_getElem.mp hpw i1 i2 hlt1 hlt2 hlt
      rw [he1, he2] at hp; exact hp
    · have hp := List.pairwise_iff_getElem.mp hpw i2 i1 hlt2 hlt1 hgt
      rw [he1, he2] at hp
      exact fun z ⟨hza, hzb⟩ => hp z ⟨hzb, hza⟩
  refine ⟨assign, fun q hq => ?_⟩
  simp only [List.mem_singleton] at hq; subst hq
  intro z hzx
  exact absurd ⟨hsubA z hzx, hsubB z hzx⟩ (hdisjAB z)

/-- Seed `knownFalse` from told `DisjointClasses` axioms and propagate downward to all
    known subclasses (`x ⊑ a`, `y ⊑ b`, `a ⊥ b`, `sat(x)` ⇒ `x ⋢ y`). -/
private def seedDisjointFromList (namedClasses : List IRI) (cs : List ClassExpr) (st : ClsCache) : ClsCache :=
  let indexed := cs.zipIdx
  indexed.foldl (fun s1 (c1, i1) =>
    match c1 with
    | .named a =>
      let subsA := namedClasses.filter fun x => s1.knownTrue.contains (x, a) && s1.satSet.contains x
      if subsA.isEmpty then s1
      else
        indexed.foldl (fun s2 (c2, i2) =>
          match c2 with
          | .named b =>
            if i1 != i2 then
              let subsB := namedClasses.filter fun y => s2.knownTrue.contains (y, b)
              subsA.foldl (fun s3 x =>
                subsB.foldl (fun s4 y =>
                  if s4.knownTrue.contains (x, a) && s4.knownTrue.contains (y, b) && s4.satSet.contains x then
                    { s4 with knownFalse := s4.knownFalse.insert (x, y) }
                  else s4) s3) s2
            else s2
          | _ => s2) s1
    | _ => s1) st

private theorem mem_zipIdx_getElem? {α : Type} {xs : List α} {x : α} {k : Nat}
    (h : (x, k) ∈ xs.zipIdx) : xs[k]? = some x := by
  have go : ∀ (l : List α) (n : Nat), (x, k) ∈ l.zipIdx n → n ≤ k ∧ l[k - n]? = some x := by
    intro l
    induction l with
    | nil => intro n h; simp at h
    | cons hd tl ih =>
      intro n h
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | htl
      · simp
      · obtain ⟨hle, hget⟩ := ih (n + 1) htl
        have hpos : k - n = (k - (n + 1)) + 1 := by omega
        refine ⟨by omega, ?_⟩
        rw [hpos]
        simpa using hget
  have ⟨_, hget⟩ := go xs 0 h
  simpa using hget

private theorem seedDisjointFromList_valid {dm : DatatypeMap} {o : Ontology}
    (namedClasses : List IRI) {cs : List ClassExpr} (hmem : .disjointClasses cs ∈ o) (st : ClsCache)
    (hv : st.Valid dm o) : (seedDisjointFromList namedClasses cs st).Valid dm o := by
  have propPairs : ∀ (a b : IRI) (i1 i2 : Nat), i1 ≠ i2 →
      cs[i1]? = some (ClassExpr.named a) → cs[i2]? = some (ClassExpr.named b) →
      ∀ (xs ys : List IRI) (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s3 x =>
        ys.foldl (fun s4 y =>
          if s4.knownTrue.contains (x, a) && s4.knownTrue.contains (y, b) && s4.satSet.contains x then
            { s4 with knownFalse := s4.knownFalse.insert (x, y) }
          else s4) s3) s).Valid dm o := by
    intro a b i1 i2 hne hi1 hi2 xs ys
    have innerY : ∀ (x : IRI) (s : ClsCache), s.Valid dm o →
        (ys.foldl (fun s4 y =>
          if s4.knownTrue.contains (x, a) && s4.knownTrue.contains (y, b) && s4.satSet.contains x then
            { s4 with knownFalse := s4.knownFalse.insert (x, y) }
          else s4) s).Valid dm o := by
      intro x
      induction ys with
      | nil => intro s hs; exact hs
      | cons y tl ihy =>
        intro s hs
        simp only [List.foldl_cons]
        cases hc : (s.knownTrue.contains (x, a) && s.knownTrue.contains (y, b) && s.satSet.contains x)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihy s hs
        · simp only [↓reduceIte]
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hxa, hyb⟩, hsatX⟩ := hc
          exact ihy _ (ClsCache.valid_insertFalse hs
            (not_entails_sub_of_disjoint_sub hmem ⟨i1, i2, hne, hi1, hi2⟩
              (hs.1 _ hxa) (hs.1 _ hyb) (hs.2.2.1 _ hsatX)))
    induction xs with
    | nil => intro s hs; exact hs
    | cons x tl ihx =>
      intro s hs
      simp only [List.foldl_cons]
      exact ihx _ (innerY x s hs)
  have inner : ∀ (a : IRI) (i1 : Nat), cs[i1]? = some (ClassExpr.named a) →
      ∀ (subsA : List IRI) (ys : List (ClassExpr × Nat)), (∀ p ∈ ys, p ∈ cs.zipIdx) →
      ∀ (s : ClsCache), s.Valid dm o →
      (ys.foldl (fun s2 (c2, i2) =>
        match c2 with
        | ClassExpr.named b =>
          if i1 != i2 then
            let subsB := namedClasses.filter fun y => s2.knownTrue.contains (y, b)
            subsA.foldl (fun s3 x =>
              subsB.foldl (fun s4 y =>
                if s4.knownTrue.contains (x, a) && s4.knownTrue.contains (y, b) && s4.satSet.contains x then
                  { s4 with knownFalse := s4.knownFalse.insert (x, y) }
                else s4) s3) s2
          else s2
        | _ => s2) s).Valid dm o := by
    intro a i1 hi1 subsA ys
    induction ys with
    | nil => intro _ s hs; exact hs
    | cons p tl ih =>
      intro hsub s hs
      rcases p with ⟨c2, i2⟩
      simp only [List.foldl_cons]
      have htl := ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
      cases c2 with
      | named b =>
        cases hc : (i1 != i2)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact htl s hs
        · simp only [↓reduceIte]
          have hi2 : cs[i2]? = some (ClassExpr.named b) := mem_zipIdx_getElem? (hsub _ (List.mem_cons_self ..))
          exact htl _ (propPairs a b i1 i2 (bne_iff_ne.mp hc) hi1 hi2 subsA _ s hs)
      | _ => exact htl s hs
  have outer : ∀ (xs : List (ClassExpr × Nat)), (∀ p ∈ xs, p ∈ cs.zipIdx) →
      ∀ (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s1 (c1, i1) =>
        match c1 with
        | ClassExpr.named a =>
          let subsA := namedClasses.filter fun x => s1.knownTrue.contains (x, a) && s1.satSet.contains x
          if subsA.isEmpty then s1
          else
            cs.zipIdx.foldl (fun s2 (c2, i2) =>
              match c2 with
              | ClassExpr.named b =>
                if i1 != i2 then
                  let subsB := namedClasses.filter fun y => s2.knownTrue.contains (y, b)
                  subsA.foldl (fun s3 x =>
                    subsB.foldl (fun s4 y =>
                      if s4.knownTrue.contains (x, a) && s4.knownTrue.contains (y, b) && s4.satSet.contains x then
                        { s4 with knownFalse := s4.knownFalse.insert (x, y) }
                      else s4) s3) s2
                else s2
              | _ => s2) s1
        | _ => s1) s).Valid dm o := by
    intro xs
    induction xs with
    | nil => intro _ s hs; exact hs
    | cons p tl ih =>
      intro hsub s hs
      rcases p with ⟨c1, i1⟩
      simp only [List.foldl_cons]
      have htl := ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
      cases c1 with
      | named a =>
        dsimp only
        split
        · exact htl s hs
        · have hi1 : cs[i1]? = some (ClassExpr.named a) := mem_zipIdx_getElem? (hsub _ (List.mem_cons_self ..))
          exact htl _ (inner a i1 hi1 _ cs.zipIdx (fun _ h => h) s hs)
      | _ => exact htl s hs
  exact outer cs.zipIdx (fun _ h => h) st hv

private def seedToldDisjoint (namedClasses : List IRI) (xs : Ontology) (st : ClsCache) : ClsCache :=
  xs.foldl (fun acc ax =>
    match ax with
    | .disjointClasses cs => seedDisjointFromList namedClasses cs acc
    | _ => acc) st

private theorem seedToldDisjoint_valid {dm : DatatypeMap} {o : Ontology}
    (namedClasses : List IRI) (xs : Ontology) (hsub : ∀ ax ∈ xs, ax ∈ o) :
    ∀ st, st.Valid dm o → (seedToldDisjoint namedClasses xs st).Valid dm o := by
  induction xs with
  | nil => intro st hv; exact hv
  | cons ax tl ih =>
    intro st hv
    simp only [seedToldDisjoint, List.foldl_cons]
    have htl := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    have hmem : ax ∈ o := hsub ax (List.mem_cons_self ..)
    cases ax with
    | disjointClasses cs => exact htl _ (seedDisjointFromList_valid namedClasses hmem st hv)
    | _ => exact htl st hv

/-- Monotone sat/unsat sweep over `namedClasses` using cached `FastLocality.LocalityIndex`:
    skips classes already decided by `satSet`/`unsatSet`, propagates unsatisfiability
    downward to known subclasses (and adds `(u, d)` to `knownTrue`), and propagates
    satisfiability upward to known superclasses. -/
private def sweepSatUnsat (solve : Ontology → Option Bool) (idx : LocalityIndex)
    (o : Ontology) (allClasses : List IRI) :
    List IRI → ClsCache → Option (List IRI × ClsCache)
  | [], st => some ([], st)
  | c :: rest, st =>
    if st.unsatSet.contains c then
      (sweepSatUnsat solve idx o allClasses rest st).map fun (us, st') => (c :: us, st')
    else if st.satSet.contains c then
      sweepSatUnsat solve idx o allClasses rest st
    else
      let seed := axiomSig (.subClassOf (.named c) (.named nothing))
      let mod := (extractBotModuleWithIndex idx o seed).1
      (decidesSubsumption solve mod c nothing).bind fun isUnsat =>
        if isUnsat then
          let s1 := { st with unsatSet := st.unsatSet.insert c }
          let s2 := allClasses.foldl (fun s x =>
            if s.knownTrue.contains (x, c) && s.unsatSet.contains c then
              { s with unsatSet := s.unsatSet.insert x }
            else s) s1
          let s3 := allClasses.foldl (fun s d =>
            if s.unsatSet.contains c then
              { s with knownTrue := s.knownTrue.insert (c, d) }
            else s) s2
          (sweepSatUnsat solve idx o allClasses rest s3).map fun (us, st') => (c :: us, st')
        else
          let s1 := { st with satSet := st.satSet.insert c }
          let s2 := allClasses.foldl (fun s d =>
            if s.knownTrue.contains (c, d) && s.satSet.contains c then
              { s with satSet := s.satSet.insert d }
            else s) s1
          sweepSatUnsat solve idx o allClasses rest s2

private theorem sweepSatUnsat_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    (idx : LocalityIndex) (o : Ontology) (allClasses rem : List IRI) :
    ∀ st us st', st.Valid dm o →
      sweepSatUnsat solve idx o allClasses rem st = some (us, st') →
      st'.Valid dm o ∧
      (∀ c, c ∈ us ↔ c ∈ rem ∧ Entails dm o [.subClassOf (.named c) (.named nothing)]) := by
  induction rem with
  | nil =>
    intro st us st' hv h
    simp only [sweepSatUnsat, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, fun c => by simp⟩
  | cons c rest ih =>
    intro st us st' hv h
    simp only [sweepSatUnsat] at h
    cases hu : st.unsatSet.contains c
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : st.satSet.contains c
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at h
        obtain ⟨isUnsat, hdec, hrest⟩ := h
        have hmodEnt : Entails dm (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named c) (.named nothing)))).1
            [.subClassOf (.named c) (.named nothing)] ↔
            Entails dm o [.subClassOf (.named c) (.named nothing)] :=
          (extractBotModuleWithIndex_entails_iff idx o [.subClassOf (.named c) (.named nothing)]
            (axiomSig (.subClassOf (.named c) (.named nothing)))
            (fun q hq => by simp at hq; subst hq; exact Sig.Subset.refl _)).symm
        have hiff := (decidesSubsumption_iff hsolve hdec).trans hmodEnt
        cases isUnsat with
        | true =>
          simp only [↓reduceIte, Option.map_eq_some_iff] at hrest
          obtain ⟨⟨us1, st1⟩, hrec, heq⟩ := hrest
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hEntBot : Entails dm o [.subClassOf (.named c) (.named nothing)] := hiff.mp rfl
          have hv1 : ({ st with unsatSet := st.unsatSet.insert c }).Valid dm o :=
            ClsCache.valid_insertUnsat hv hEntBot
          have hv2 : ∀ (xs : List IRI) (s : ClsCache), s.Valid dm o →
              (xs.foldl (fun s x =>
                if s.knownTrue.contains (x, c) && s.unsatSet.contains c then
                  { s with unsatSet := s.unsatSet.insert x }
                else s) s).Valid dm o := by
            intro xs
            induction xs with
            | nil => intro s hvs; exact hvs
            | cons x tl ihx =>
              intro s hvs
              simp only [List.foldl_cons]
              cases hc : s.knownTrue.contains (x, c) && s.unsatSet.contains c
              · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihx s hvs
              · simp only [↓reduceIte]
                obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
                exact ihx _ (ClsCache.valid_insertUnsat hvs (unsat_downward (hvs.1 _ h1) (hvs.2.2.2 _ h2)))
          have hv3 : ∀ (ds : List IRI) (s : ClsCache), s.Valid dm o →
              (ds.foldl (fun s d =>
                if s.unsatSet.contains c then
                  { s with knownTrue := s.knownTrue.insert (c, d) }
                else s) s).Valid dm o := by
            intro ds
            induction ds with
            | nil => intro s hvs; exact hvs
            | cons d tl ihd =>
              intro s hvs
              simp only [List.foldl_cons]
              cases hc : s.unsatSet.contains c
              · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihd s hvs
              · simp only [↓reduceIte]
                exact ihd _ (ClsCache.valid_insertTrue hvs
                  (FastClassification.entails_sub_of_unsat (hvs.2.2.2 _ hc)))
          obtain ⟨hvFinal, hmem⟩ := ih _ us1 st1 (hv3 allClasses _ (hv2 allClasses _ hv1)) hrec
          refine ⟨hvFinal, fun x => ?_⟩
          simp only [List.mem_cons, hmem]
          constructor
          · rintro (rfl | ⟨hx, he⟩); exact ⟨Or.inl rfl, hEntBot⟩; exact ⟨Or.inr hx, he⟩
          · rintro ⟨rfl | hx, he⟩; exact Or.inl rfl; exact Or.inr ⟨hx, he⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hrest
          have hSatC : ¬ Entails dm o [.subClassOf (.named c) (.named nothing)] :=
            fun he => Bool.noConfusion (hiff.mpr he)
          have hv1 : ({ st with satSet := st.satSet.insert c }).Valid dm o :=
            ClsCache.valid_insertSat hv hSatC
          have hv2 : ∀ (ds : List IRI) (s : ClsCache), s.Valid dm o →
              (ds.foldl (fun s d =>
                if s.knownTrue.contains (c, d) && s.satSet.contains c then
                  { s with satSet := s.satSet.insert d }
                else s) s).Valid dm o := by
            intro ds
            induction ds with
            | nil => intro s hvs; exact hvs
            | cons d tl ihd =>
              intro s hvs
              simp only [List.foldl_cons]
              cases hc : s.knownTrue.contains (c, d) && s.satSet.contains c
              · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihd s hvs
              · simp only [↓reduceIte]
                obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
                exact ihd _ (ClsCache.valid_insertSat hvs (sat_upward (hvs.1 _ h1) (hvs.2.2.1 _ h2)))
          obtain ⟨hvFinal, hmem⟩ := ih _ us st' (hv2 allClasses _ hv1) hrest
          refine ⟨hvFinal, fun x => ?_⟩
          rw [hmem]
          constructor
          · rintro ⟨hx, he⟩; exact ⟨List.mem_cons_of_mem _ hx, he⟩
          · rintro ⟨hx, he⟩
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact absurd he hSatC
            · exact ⟨hx', he⟩
      · simp only [hs, ↓reduceIte] at h
        have hSatC := hv.2.2.1 c hs
        obtain ⟨hvFinal, hmem⟩ := ih st us st' hv h
        refine ⟨hvFinal, fun x => ?_⟩
        rw [hmem]
        constructor
        · rintro ⟨hx, he⟩; exact ⟨List.mem_cons_of_mem _ hx, he⟩
        · rintro ⟨hx, he⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact absurd he hSatC
          · exact ⟨hx', he⟩
    · simp only [hu, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨us1, st1⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hUnsatC := hv.2.2.2 c hu
      obtain ⟨hvFinal, hmem⟩ := ih st us1 st1 hv hrec
      refine ⟨hvFinal, fun x => ?_⟩
      simp only [List.mem_cons, hmem]
      constructor
      · rintro (rfl | ⟨hx, he⟩); exact ⟨Or.inl rfl, hUnsatC⟩; exact ⟨Or.inr hx, he⟩
      · rintro ⟨rfl | hx, he⟩; exact Or.inl rfl; exact Or.inr ⟨hx, he⟩

private def querySubsumption (solve : Ontology → Option Bool)
    (harvest : Ontology → IRI → IRI → List (IRI × IRI))
    (idx : LocalityIndex) (o : Ontology) (a b : IRI) : Option (Bool × List (IRI × IRI)) :=
  let mod := (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))).1
  (decidesSubsumption solve mod a b).map fun isSub =>
    (isSub, if isSub then [] else harvest mod a b)

private def hasTransitiveWitness (classes : List IRI) (st : ClsCache) (a b : IRI) : Bool :=
  classes.any fun mid => st.knownTrue.contains (a, mid) && st.knownTrue.contains (mid, b)

private def hasContrapositiveWitness (classes : List IRI) (st : ClsCache) (a b : IRI) : Bool :=
  classes.any fun mid =>
    (st.knownTrue.contains (mid, a) && st.knownFalse.contains (mid, b)) ||
    (st.knownTrue.contains (b, mid) && st.knownFalse.contains (a, mid))

/-- Enhanced Traversal over a list of candidate pairs `(a, b)`:
    1. Checks `knownTrue` / `knownFalse` in `O(1)`
    2. Checks transitive `knownTrue` witnesses (`a ⊑ mid ∧ mid ⊑ b`)
    3. Checks Enhanced Traversal contrapositive witnesses (`mid ⊑ a ∧ mid ⋢ b` or `b ⊑ mid ∧ a ⋢ mid`)
    4. Only queries `solve` on the per-pair ⊥-local module when still undecided, and eagerly
       propagates the result (plus any verified countermodel non-subsumptions from `harvest`). -/
private def traversePairs (query : IRI → IRI → Option (Bool × List (IRI × IRI)))
    (allClasses : List IRI) :
    List (IRI × IRI) → ClsCache → Option (List (IRI × IRI) × ClsCache)
  | [], st => some ([], st)
  | (a, b) :: rest, st =>
    if st.knownTrue.contains (a, b) then
      (traversePairs query allClasses rest st).map fun (ps, st') => ((a, b) :: ps, st')
    else if st.knownFalse.contains (a, b) then
      traversePairs query allClasses rest st
    else if hasTransitiveWitness allClasses st a b then
      let st1 := insertTrueAndClose allClasses a b st
      (traversePairs query allClasses rest st1).map fun (ps, st') => ((a, b) :: ps, st')
    else if hasContrapositiveWitness allClasses st a b then
      let st1 := insertFalseAndClose allClasses a b st
      traversePairs query allClasses rest st1
    else
      (query a b).bind fun (isSub, harvested) =>
        if isSub then
          let st1 := insertTrueAndClose allClasses a b st
          (traversePairs query allClasses rest st1).map fun (ps, st') => ((a, b) :: ps, st')
        else
          let st1 := insertFalseAndClose allClasses a b st
          let st2 := harvested.foldl (fun s p => { s with knownFalse := s.knownFalse.insert p }) st1
          traversePairs query allClasses rest st2

private theorem traversePairs_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    (idx : LocalityIndex) (o : Ontology)
    {harvest : Ontology → IRI → IRI → List (IRI × IRI)}
    (hharv : ∀ {mod a b p},
      (∃ seed σ, ValidBotModule o seed mod σ) →
      p ∈ harvest mod a b → ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)])
    (allClasses : List IRI) (rem : List (IRI × IRI)) :
    ∀ st ps st', st.Valid dm o →
      traversePairs (querySubsumption solve harvest idx o) allClasses rem st = some (ps, st') →
      st'.Valid dm o ∧
      (∀ p, p ∈ ps ↔ p ∈ rem ∧ Entails dm o [.subClassOf (.named p.1) (.named p.2)]) := by
  induction rem with
  | nil =>
    intro st ps st' hv h
    simp only [traversePairs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, fun p => by simp⟩
  | cons ab rest ih =>
    intro st ps st' hv h
    rcases ab with ⟨a, b⟩
    simp only [traversePairs, hasTransitiveWitness, hasContrapositiveWitness] at h
    cases ht : st.knownTrue.contains (a, b)
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      cases hf : st.knownFalse.contains (a, b)
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
        cases htr : allClasses.any fun mid => st.knownTrue.contains (a, mid) && st.knownTrue.contains (mid, b)
        · simp only [htr, Bool.false_eq_true, ↓reduceIte] at h
          cases hct : allClasses.any fun mid =>
              (st.knownTrue.contains (mid, a) && st.knownFalse.contains (mid, b)) ||
              (st.knownTrue.contains (b, mid) && st.knownFalse.contains (a, mid))
          · simp only [hct, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at h
            obtain ⟨⟨isSub, harvested⟩, hquery, hrest⟩ := h
            obtain ⟨answer, hdec, heq⟩ := Option.map_eq_some_iff.mp hquery
            have hanswer : answer = isSub := congrArg Prod.fst heq
            subst answer
            have hmodEnt : Entails dm (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))).1
                [.subClassOf (.named a) (.named b)] ↔
                Entails dm o [.subClassOf (.named a) (.named b)] :=
              (extractBotModuleWithIndex_entails_iff idx o [.subClassOf (.named a) (.named b)]
                (axiomSig (.subClassOf (.named a) (.named b)))
                (fun q hq => by simp at hq; subst hq; exact Sig.Subset.refl _)).symm
            have hiff := (decidesSubsumption_iff hsolve hdec).trans hmodEnt
            cases isSub with
            | true =>
              simp only [↓reduceIte, Option.map_eq_some_iff] at hrest
              obtain ⟨⟨ps1, st1⟩, hrec, heq⟩ := hrest
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              have hEnt : Entails dm o [.subClassOf (.named a) (.named b)] := hiff.mp rfl
              obtain ⟨hvF, hmem⟩ := ih _ ps1 st1 (insertTrueAndClose_valid allClasses hv hEnt) hrec
              refine ⟨hvF, fun p => ?_⟩
              simp only [List.mem_cons, hmem]
              constructor
              · rintro (rfl | ⟨hp, he⟩); exact ⟨Or.inl rfl, hEnt⟩; exact ⟨Or.inr hp, he⟩
              · rintro ⟨rfl | hp, he⟩; exact Or.inl rfl; exact Or.inr ⟨hp, he⟩
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at hrest
              have hNotEnt : ¬ Entails dm o [.subClassOf (.named a) (.named b)] :=
                fun he => Bool.noConfusion (hiff.mpr he)
              have hrepl := congrArg Prod.snd heq
              dsimp only [Bool.false_eq_true, ↓reduceIte] at hrepl
              subst harvested
              have hv1 := insertFalseAndClose_valid allClasses hv hNotEnt
              have hvb : ∃ seed σ, ValidBotModule o seed
                  (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))).1 σ :=
                ⟨axiomSig (.subClassOf (.named a) (.named b)),
                 (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))).2,
                 extractBotModuleWithIndex_valid idx o _⟩
              have hv2 : ∀ (hs : List (IRI × IRI)) (s : ClsCache), s.Valid dm o →
                  (∀ p ∈ hs, ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)]) →
                  (hs.foldl (fun s p => { s with knownFalse := s.knownFalse.insert p }) s).Valid dm o := by
                intro hs
                induction hs with
                | nil => intro s hvs _; exact hvs
                | cons p tl ihp =>
                  intro s hvs hall
                  simp only [List.foldl_cons]
                  exact ihp _ (ClsCache.valid_insertFalse hvs (hall p (List.mem_cons_self ..)))
                    (fun q hq => hall q (List.mem_cons_of_mem _ hq))
              have hv2' := hv2
                (harvest (extractBotModuleWithIndex idx o (axiomSig (.subClassOf (.named a) (.named b)))).1 a b)
                (insertFalseAndClose allClasses a b st) hv1
                (fun p hp => hharv hvb hp)
              obtain ⟨hvF, hmem⟩ := ih _ ps st' hv2' hrest
              refine ⟨hvF, fun p => ?_⟩
              rw [hmem]
              constructor
              · rintro ⟨hp, he⟩; exact ⟨List.mem_cons_of_mem _ hp, he⟩
              · rintro ⟨hp, he⟩
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact absurd he hNotEnt
                · exact ⟨hp', he⟩
          · simp only [hct, ↓reduceIte] at h
            obtain ⟨mid, _, hcond⟩ := List.any_eq_true.mp hct
            have hNotEnt : ¬ Entails dm o [.subClassOf (.named a) (.named b)] := by
              simp only [Bool.or_eq_true, Bool.and_eq_true] at hcond
              rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact not_entails_upward (hv.1 _ h1) (hv.2.1 _ h2)
              · exact not_entails_downward (hv.1 _ h1) (hv.2.1 _ h2)
            obtain ⟨hvF, hmem⟩ := ih _ ps st' (insertFalseAndClose_valid allClasses hv hNotEnt) h
            refine ⟨hvF, fun p => ?_⟩
            rw [hmem]
            constructor
            · rintro ⟨hp, he⟩; exact ⟨List.mem_cons_of_mem _ hp, he⟩
            · rintro ⟨hp, he⟩
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact absurd he hNotEnt
              · exact ⟨hp', he⟩
        · simp only [htr, ↓reduceIte, Option.map_eq_some_iff] at h
          obtain ⟨⟨ps1, st1⟩, hrec, heq⟩ := h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨mid, _, hcond⟩ := List.any_eq_true.mp htr
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcond
          have hEnt := entails_sub_trans (hv.1 _ h1) (hv.1 _ h2)
          obtain ⟨hvF, hmem⟩ := ih _ ps1 st1 (insertTrueAndClose_valid allClasses hv hEnt) hrec
          refine ⟨hvF, fun p => ?_⟩
          simp only [List.mem_cons, hmem]
          constructor
          · rintro (rfl | ⟨hp, he⟩); exact ⟨Or.inl rfl, hEnt⟩; exact ⟨Or.inr hp, he⟩
          · rintro ⟨rfl | hp, he⟩; exact Or.inl rfl; exact Or.inr ⟨hp, he⟩
      · simp only [hf, ↓reduceIte] at h
        have hNotEnt := hv.2.1 (a, b) hf
        obtain ⟨hvF, hmem⟩ := ih st ps st' hv h
        refine ⟨hvF, fun p => ?_⟩
        rw [hmem]
        constructor
        · rintro ⟨hp, he⟩; exact ⟨List.mem_cons_of_mem _ hp, he⟩
        · rintro ⟨hp, he⟩
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact absurd he hNotEnt
          · exact ⟨hp', he⟩
    · simp only [ht, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨ps1, st1⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hEnt := hv.1 (a, b) ht
      obtain ⟨hvF, hmem⟩ := ih st ps1 st1 hv hrec
      refine ⟨hvF, fun p => ?_⟩
      simp only [List.mem_cons, hmem]
      constructor
      · rintro (rfl | ⟨hp, he⟩); exact ⟨Or.inl rfl, hEnt⟩; exact ⟨Or.inr hp, he⟩
      · rintro ⟨rfl | hp, he⟩; exact Or.inl rfl; exact Or.inr ⟨hp, he⟩

private def classifyEnhancedCoreWith (solve : Ontology → Option Bool)
    (traverse : LocalityIndex → Ontology → List IRI → List (IRI × IRI) →
      ClsCache → Option (List (IRI × IRI) × ClsCache))
    (initHarvest : Ontology → List IRI → List (IRI × IRI))
    (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  let idx := LocalityIndex.build o
  let mod0 := (extractBotModuleWithIndex idx o Sig.empty).1
  (solve mod0).bind fun consistent =>
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
      let st0 := closeTransitive namedClasses
        (seedToldAxioms o (seedReflexive namedClasses {}))
      (sweepSatUnsat solve idx o namedClasses namedClasses st0).bind fun (unsat, st1) =>
        let st2 := seedToldDisjoint namedClasses o st1
        let st3 := (initHarvest o namedClasses).foldl
          (fun s p => { s with knownFalse := s.knownFalse.insert p }) st2
        let allPairs := orderedPairs namedClasses
        (traverse idx o namedClasses allPairs st3).map fun (subs, _) =>
          let satClasses := namedClasses.filter (!unsat.contains ·)
          let subSet := FastClassification.setOfPairs subs
          {
            consistent := true
            classes := namedClasses
            unsatisfiable := unsat
            subsumptions := subs
            equivalences := computeEquivClassesFast satClasses subSet
            directParents := computeDirectParentsFast satClasses subSet
          }

/-- Certified Enhanced Traversal classifier parameterized by an exact consistency
    solver and optional certified countermodel harvesters. -/
def classifyEnhancedCore (solve : Ontology → Option Bool)
    (initHarvest : Ontology → List IRI → List (IRI × IRI))
    (stepHarvest : Ontology → IRI → IRI → List (IRI × IRI))
    (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  classifyEnhancedCoreWith solve
    (fun idx base => traversePairs (querySubsumption solve stepHarvest idx base)) initHarvest o namedClasses

theorem classifyEnhancedCore_sound_complete {dm : DatatypeMap}
    {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {initHarvest : Ontology → List IRI → List (IRI × IRI)}
    {stepHarvest : Ontology → IRI → IRI → List (IRI × IRI)}
    (hinit : ∀ {o cs p}, p ∈ initHarvest o cs → ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)])
    (hstep : ∀ {o mod a b p},
      (∃ seed σ, ValidBotModule o seed mod σ) →
      p ∈ stepHarvest mod a b → ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)])
    {o : Ontology} {namedClasses : List IRI} {h : ClassHierarchy}
    (hcls : classifyEnhancedCore solve initHarvest stepHarvest o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable dm o) ∧
    (h.consistent = true →
      Satisfiable dm o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm o [.subClassOf (.named a) (.named b)])) := by
  unfold classifyEnhancedCore classifyEnhancedCoreWith at hcls
  dsimp only at hcls
  obtain ⟨cons, hcons, hrest⟩ := Option.bind_eq_some_iff.mp hcls
  have hsat0 : Satisfiable dm (extractBotModuleWithIndex (LocalityIndex.build o) o Sig.empty).1 ↔
      Satisfiable dm o := (extractBotModuleWithIndex_sat_iff _ o Sig.empty).symm
  cases cons with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    exact ⟨fun _ hs => Bool.noConfusion ((hsolve hcons).mpr (hsat0.mpr hs)), fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hrest
    obtain ⟨⟨unsat, st1⟩, hsweep, ⟨subs, stF⟩, htrav, rfl⟩ := hrest
    have hSatO : Satisfiable dm o := hsat0.mp ((hsolve hcons).mp rfl)
    have hv0 : (closeTransitive namedClasses (seedToldAxioms o (seedReflexive namedClasses {}))).Valid dm o :=
      closeTransitive_valid namedClasses _
        (seedToldAxioms_valid o (fun _ hx => hx) _ (seedReflexive_valid namedClasses {} ClsCache.valid_empty))
    obtain ⟨hv1, hunsat⟩ := sweepSatUnsat_sound hsolve _ o namedClasses namedClasses _ unsat st1 hv0 hsweep
    have hv2 : (seedToldDisjoint namedClasses o st1).Valid dm o :=
      seedToldDisjoint_valid namedClasses o (fun _ hx => hx) st1 hv1
    have hv3 : ∀ (hs : List (IRI × IRI)) (s : ClsCache), s.Valid dm o →
        (∀ p ∈ hs, ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)]) →
        (hs.foldl (fun s p => { s with knownFalse := s.knownFalse.insert p }) s).Valid dm o := by
      intro hs
      induction hs with
      | nil => intro s hvs _; exact hvs
      | cons p tl ihp =>
        intro s hvs hall
        simp only [List.foldl_cons]
        exact ihp _ (ClsCache.valid_insertFalse hvs (hall p (List.mem_cons_self ..)))
          (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    have hv3' := hv3 (initHarvest o namedClasses) _ hv2 (fun p hp => hinit hp)
    obtain ⟨_, hsubs⟩ := traversePairs_sound hsolve _ o (fun hvb hp => hstep hvb hp) namedClasses (orderedPairs namedClasses) _ subs stF hv3' htrav
    refine ⟨(fun hc => by cases hc), fun _ => ⟨hSatO, hunsat, fun a b => ?_⟩⟩
    have hm := hsubs (a, b)
    simpa [mem_orderedPairs_iff, and_assoc] using hm

/-- Certified Enhanced Traversal classifier for arbitrary `(dm, solve)` (no model harvester). -/
def classifyEnhancedWith (solve : Ontology → Option Bool) (o : Ontology)
    (namedClasses : List IRI) : Option ClassHierarchy :=
  classifyEnhancedCore solve (fun _ _ => []) (fun _ _ _ => []) o namedClasses

theorem classifyEnhancedWith_sound_complete {dm : DatatypeMap}
    {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {namedClasses : List IRI} {h : ClassHierarchy}
    (hcls : classifyEnhancedWith solve o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable dm o) ∧
    (h.consistent = true →
      Satisfiable dm o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm o [.subClassOf (.named a) (.named b)])) :=
  classifyEnhancedCore_sound_complete hsolve (fun hp => by cases hp) (fun _ hp => by cases hp) hcls

/-- Certified hybrid classifier under Dedekind-cut `realDatatypeMap`:
    uses single-pass polynomial $\mathcal{EL}^{++}$ (`classifyDirectEL`) whenever `o`
    is direct $\mathcal{EL}^{++}$, and falls back to `classifyEnhancedWith decideRealOntology?`
    for full expressive $\mathcal{SROIQ}(\mathcal{D})$. -/
def classifyEnhancedReal (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  match classifyDirectEL o namedClasses with
  | some h => some h
  | none => classifyEnhancedWith decideRealOntology? o namedClasses

theorem classifyEnhancedReal_sound_complete {o : Ontology} {namedClasses : List IRI}
    {h : ClassHierarchy} (hcls : classifyEnhancedReal o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable realDatatypeMap o) ∧
    (h.consistent = true →
      Satisfiable realDatatypeMap o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails realDatatypeMap o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails realDatatypeMap o [.subClassOf (.named a) (.named b)])) := by
  unfold classifyEnhancedReal at hcls
  cases hel : classifyDirectEL o namedClasses with
  | some h0 =>
    rw [hel] at hcls
    simp only [Option.some.injEq] at hcls; subst hcls
    exact classifyDirectEL_sound_complete hel
  | none =>
    rw [hel] at hcls
    exact classifyEnhancedWith_sound_complete decideRealOntology_iff hcls

/-! ### Certified `SROIQDModel` countermodel caching -/

private def checkModelCounterAt (m : SROIQDModel) (c d : IRI) : Bool :=
  m.graph.worlds.any fun w =>
    eval? m w (.conj (.atom c) (Concept.atom d).dual) == some true

/-- If `m` passes `checkModel p m = true`, then any `(c, d)` separated at some world
    of `m` immediately satisfies `counterProblem p ⟨.atom c, .atom d⟩`. -/
theorem checkModel_counter_of_checkModel {p : Problem} {m : SROIQDModel} {c d : IRI}
    (hm : checkModel p m = true)
    (hw : checkModelCounterAt m c d = true) :
    (counterProblem p ⟨.atom c, .atom d⟩).Sat := by
  have hchk : checkModel (counterProblem p ⟨.atom c, .atom d⟩) m = true := by
    unfold checkModel at hm ⊢
    simp only [Bool.and_eq_true] at hm ⊢
    exact ⟨hm.1, hw⟩
  exact checkModel_sound hchk

/-- Hash-indexed extraction of all `(c, d)` pairs among `namedClasses` refuted by a
    verified `SROIQDModel` `m` for `o` (zero additional tableau calls). -/
def harvestModelPairs (o : Ontology) (namedClasses : List IRI) (m : SROIQDModel) :
    List (IRI × IRI) :=
  match normalizeWithDefs o with
  | none => []
  | some (_, p) =>
    if p.root == .top && checkModel p m then
      m.separatedPairsFrom namedClasses namedClasses
    else []

theorem harvestModelPairs_sound {o : Ontology} {namedClasses : List IRI}
    {m : SROIQDModel} {pair : IRI × IRI}
    (hmem : pair ∈ harvestModelPairs o namedClasses m) :
    ¬ Entails datatypeMap o [.subClassOf (.named pair.1) (.named pair.2)] := by
  unfold harvestModelPairs at hmem
  cases hnorm : normalizeWithDefs o with
  | none => rw [hnorm] at hmem; cases hmem
  | some dp =>
    rcases dp with ⟨defs, p⟩
    rw [hnorm] at hmem
    cases hpm : (p.root == .top && checkModel p m) with
    | false => simp [hpm] at hmem
    | true =>
      simp only [hpm, ↓reduceIte] at hmem
      obtain ⟨_, hchk⟩ := Bool.and_eq_true_iff.mp hpm
      obtain ⟨hcT, hcN, hdT, hdN, hcnt⟩ := SROIQDModel.separatedPairsFrom_sound hmem
      have hsatCnt : (counterProblem p ⟨.atom pair.1, .atom pair.2⟩).Sat :=
        checkModel_counter_of_checkModel hchk hcnt
      have hq : queryToInclusions defs (.subClassOf (.named pair.1) (.named pair.2)) =
          some [⟨.atom pair.1, .atom pair.2⟩] := by
        simp [queryToInclusions, unfoldAxiom, unfoldClassExpr, rawQueryToInclusions,
          normClassExpr, beq_false_of_ne hcT, beq_false_of_ne hcN, beq_false_of_ne hdT, beq_false_of_ne hdN]
      have hnoAnon : ∀ q ∈ ([⟨.atom pair.1, .atom pair.2⟩] : List Inclusion),
          q.sub.hasNoAnon = true ∧ q.sup.hasNoAnon = true := by
        intro q hqm; simp at hqm; subst hqm; exact ⟨rfl, rfl⟩
      have hEntIff := (query_entails_iff_inclusions hnorm hq hnoAnon).1
      intro hent
      have hEntP := hEntIff.mp hent ⟨.atom pair.1, .atom pair.2⟩ (List.mem_singleton.mpr rfl)
      obtain ⟨i, hmodP, x0, hx0⟩ := hsatCnt
      have hmodP' : p.Models i := by cases hmodP; constructor <;> assumption
      have hsatPOnt : models i p.toOntology :=
        satisfies_models ((satisfies_toOntology_iff i p).mpr hmodP')
      obtain ⟨assign, hqSat⟩ := hEntP i hsatPOnt
      have hax := hqSat _ (List.mem_singleton.mpr rfl) x0
      simp only [counterProblem, SROIQD.holds, Concept.dual, Concept.toClassExpr, classHolds] at hx0 hax
      exact hx0.2 (hax hx0.1)

private def proposeInitModelPairs (o : Ontology) (namedClasses : List IRI) : List (IRI × IRI) :=
  match proposeVerifiedModel o with
  | some (m, _) => m.separatedPairsFrom namedClasses namedClasses
  | none => []

/-- Certified Enhanced Traversal + `SROIQDModel` countermodel seeding over `datatypeMap`. -/
def classifyEnhancedStd (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  match classifyDirectEL o namedClasses with
  | some h => some h
  | none =>
    classifyEnhancedCore SROIQD.Termination.WiderData.decideWithWiderDataRanges?
      proposeInitModelPairs (fun _ _ _ => []) o namedClasses

private theorem proposeInitModelPairs_sound {o : Ontology} {namedClasses : List IRI}
    {pair : IRI × IRI} (hp : pair ∈ proposeInitModelPairs o namedClasses) :
    ¬ Entails datatypeMap o [.subClassOf (.named pair.1) (.named pair.2)] := by
  unfold proposeInitModelPairs at hp
  cases hm : proposeVerifiedModel o with
  | none => simp [hm] at hp
  | some mp =>
    rcases mp with ⟨m, p'⟩
    simp only [hm] at hp
    unfold proposeVerifiedModel at hm
    cases hnorm : normalizeWithDefs o with
    | none => simp [hnorm] at hm
    | some dp =>
      rcases dp with ⟨defs, p⟩
      simp only [hnorm] at hm
      split at hm
      · rename_i hcond
        have hroot : p.root = .top := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2
        split at hm
        · rename_i m1 _
          split at hm
          · rename_i hchk
            simp only [Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            have hmem : pair ∈ harvestModelPairs o namedClasses m1 := by
              unfold harvestModelPairs
              simp [hnorm, hroot, hchk, hp]
            exact harvestModelPairs_sound hmem
          · cases hm
        · cases hm
      · cases hm

theorem classifyEnhancedStd_sound_complete {o : Ontology} {namedClasses : List IRI}
    {h : ClassHierarchy} (hcls : classifyEnhancedStd o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable datatypeMap o) ∧
    (h.consistent = true →
      Satisfiable datatypeMap o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails datatypeMap o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails datatypeMap o [.subClassOf (.named a) (.named b)])) := by
  unfold classifyEnhancedStd at hcls
  cases hel : classifyDirectEL o namedClasses with
  | some h0 =>
    rw [hel] at hcls; simp only [Option.some.injEq] at hcls; subst hcls
    exact classifyDirectEL_sound_complete hel
  | none =>
    rw [hel] at hcls
    exact classifyEnhancedCore_sound_complete decideWithWiderDataRanges_iff
      proposeInitModelPairs_sound (fun _ hp => by cases hp) hcls

end Sabrina.OWL2.FastClassification
