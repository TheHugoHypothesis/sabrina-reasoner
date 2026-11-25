import Std.Data.HashSet
import Std.Data.HashMap
import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastLocality
import Sabrina.OWL2.EL

/-! Kernel-verified fast OWL 2 DL ontology classification:
    1. **Single-pass polynomial $\mathcal{EL}^{++}$ classification** (`classifyELSinglePass`,
       `classifyDirectEL`): runs `EL.saturateEL` ONCE across all named classes, certifies
       each satisfiable class with a single canonical `ELModel` (`O(n)` model checks
       instead of `O(n²)`), and certifies entailed subsumptions via `EL.checkELProof`.
       Proved sound, complete, and terminating for arbitrary `DatatypeMap`.
    2. **Certified Enhanced Traversal with `FastLocality.LocalityIndex`**
       (`classifyEnhancedWith`, `classifyEnhancedReal`): pre-builds the inverted locality
       index once, seeds told subsumptions & transitive closure, performs monotone
       sat/unsat propagation and told disjointness pruning, runs Enhanced Traversal
       upward/downward non-subsumption closure over per-pair ⊥-local modules, and uses
       `O(1)` hash-set transitive reduction for `equivalences` and `directParents`.
    3. **Certified `SROIQDModel` countermodel caching** (`checkModel_counter_of_checkModel`,
       `harvestFullModelPairs_sound`, `classifyEnhancedWithModels`): every verified
       finite `SROIQDModel` refutes all `(c, d)` pairs it separates at any world with
       zero additional tableau calls.

    All proofs use zero `sorry` and strictly standard Lean 4 core axioms
    (`propext`, `Classical.choice`, `Quot.sound`). -/

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

/-! ### 1. Hash-Indexed Equivalence Classes & Direct Parents -/

/-- Hash-indexed equivalence class partitioning (`O(|C|²)` with `O(1)` pair lookup). -/
def computeEquivClassesFast (classes : List IRI) (subSet : Std.HashSet (IRI × IRI)) :
    List (List IRI) := Id.run do
  let mut seen : Std.HashSet IRI := {}
  let mut groups : List (List IRI) := []
  for c in classes do
    if !seen.contains c then
      let grp := classes.filter fun d => subSet.contains (c, d) && subSet.contains (d, c)
      for d in grp do
        seen := seen.insert d
      groups := grp :: groups
  return groups.reverse

/-- Hash-indexed transitive reduction (`directParents`) using `O(1)` subsumption lookup. -/
def computeDirectParentsFast (classes : List IRI) (subSet : Std.HashSet (IRI × IRI)) :
    List (IRI × List IRI) :=
  let strictSub (a b : IRI) : Bool := subSet.contains (a, b) && !subSet.contains (b, a)
  classes.map fun c =>
    let strictSups := classes.filter (strictSub c)
    let direct := strictSups.filter fun p =>
      !strictSups.any fun mid => strictSub c mid && strictSub mid p
    let parents := if direct.isEmpty then [thing] else direct
    (c, parents)

private def setOfPairs (ps : List (IRI × IRI)) : Std.HashSet (IRI × IRI) :=
  ps.foldl (fun s p => s.insert p) {}

private def orderedPairs (xs : List IRI) : List (IRI × IRI) :=
  xs.flatMap fun a => xs.map fun b => (a, b)

private theorem mem_orderedPairs_iff {xs : List IRI} {a b : IRI} :
    (a, b) ∈ orderedPairs xs ↔ a ∈ xs ∧ b ∈ xs := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, rfl⟩; exact ⟨hx, hy⟩
  · rintro ⟨ha, hb⟩; exact ⟨a, ha, b, hb, rfl, rfl⟩

/-! ### 2. Generic Semantic Closure Lemmas for Subsumption & Satisfiability -/

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

private theorem entails_sub_of_unsat {dm : DatatypeMap} {o : Ontology} {a b : IRI}
    (hbot : Entails dm o [.subClassOf (.named a) (.named nothing)]) :
    Entails dm o [.subClassOf (.named a) (.named b)] := by
  intro i hmod
  obtain ⟨assign, hs⟩ := hbot i hmod
  have h0 := hs _ (List.mem_singleton.mpr rfl)
  refine satisfies_models fun q hq => ?_
  simp only [List.mem_singleton] at hq; subst hq
  intro x hx
  exact absurd (h0 x hx) ((i.withAnonymous assign).nothingExt x)

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

private theorem not_entails_sub_of_disjoint_pairwise {dm : DatatypeMap} {o : Ontology}
    {cs : List ClassExpr} {a b : IRI}
    (hmem : .disjointClasses cs ∈ o)
    (hdisj : ∃ (i1 i2 : Nat), i1 ≠ i2 ∧ cs[i1]? = some (ClassExpr.named a) ∧ cs[i2]? = some (ClassExpr.named b))
    (hsatA : ¬ Entails dm o [.subClassOf (.named a) (.named nothing)]) :
    ¬ Entails dm o [.subClassOf (.named a) (.named b)] := by
  intro hab
  apply hsatA
  intro i hmod
  obtain ⟨assign, hsat⟩ := hmod
  have hpw := hsat _ hmem
  obtain ⟨_, hsab⟩ := hab i ⟨assign, hsat⟩
  have hsub := hsab _ (List.mem_singleton.mpr rfl)
  have hdisjAB : ∀ x, ¬ (classHolds (i.withAnonymous assign) x (.named a) ∧
      classHolds (i.withAnonymous assign) x (.named b)) := by
    obtain ⟨i1, i2, hne, h1, h2⟩ := hdisj
    obtain ⟨hlt1, he1⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hlt2, he2⟩ := List.getElem?_eq_some_iff.mp h2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hp := List.pairwise_iff_getElem.mp hpw i1 i2 hlt1 hlt2 hlt
      rw [he1, he2] at hp; exact hp
    · have hp := List.pairwise_iff_getElem.mp hpw i2 i1 hlt2 hlt1 hgt
      rw [he1, he2] at hp
      exact fun x ⟨hxa, hxb⟩ => hp x ⟨hxb, hxa⟩
  refine ⟨assign, fun q hq => ?_⟩
  simp only [List.mem_singleton] at hq; subst hq
  intro x hxa
  exact absurd ⟨hxa, hsub x hxa⟩ (hdisjAB x)

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

/-! ### 3. Single-Pass Polynomial EL++ Classification (Arbitrary `DatatypeMap`) -/

/-- Build an `Interpretation dm` (for ANY `dm : DatatypeMap`) from a checked `ELModel`. -/
def elModelToInterpretation (dm : DatatypeMap) (m : ELModel) (hne : m.nodes ≠ []) :
    Interpretation dm where
  Object := { u : IRI // u ∈ m.nodes }
  objectNonempty := match h : m.nodes with
    | [] => absurd h hne
    | x :: _ => ⟨⟨x, List.mem_cons_self ..⟩⟩
  Data := Option dm.Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := fun h => Option.some.inj h
  classes c x := m.hasCls c x.val = true
  objectProperties r x y := m.hasEdge r x.val y.val = true
  dataProperties p _ _ := p = topDataProperty
  individuals _ := match h : m.nodes with
    | [] => absurd h hne
    | x :: _ => ⟨x, List.mem_cons_self ..⟩
  datatypes r y :=
    if r = literalDatatype then True
    else match y with
      | some v => dm.valueSpace r v
      | none => False
  literalValue l := dm.lexicalValue l
  lexicalAgreement _ _ h := h
  named _ := True
  namedIndividual _ := trivial
  thingExt := fun x => by simp [ELModel.hasCls]
  nothingExt := fun x => by simp [ELModel.hasCls, thing, nothing]
  topObjectExt := fun x y => by simp [ELModel.hasEdge]
  bottomObjectExt := fun x y => by simp [ELModel.hasEdge, topObjectProperty, bottomObjectProperty]
  topDataExt := fun _ _ => rfl
  bottomDataExt := fun _ _ h => by simp [topDataProperty, bottomDataProperty] at h
  literalDatatypeExt := fun _ => by simp
  datatypeAgreement := fun r hr y => by
    have hne' : r ≠ literalDatatype := fun he => dm.literal_not_builtin (he ▸ hr)
    simp only [hne', ↓reduceIte]
    cases y with
    | none => simp
    | some v =>
      constructor
      · intro hv; exact ⟨v, hv, rfl⟩
      · rintro ⟨w, hw, heq⟩; cases heq; exact hw

theorem checkELModel_sound_with {dm : DatatypeMap} {axs : List ELAxiom} {m : ELModel}
    (hcheck : checkELModel axs m = true) :
    ∃ hne : m.nodes ≠ [], satisfies (elModelToInterpretation dm m hne) (elOntology axs) := by
  simp only [checkELModel, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hcheck
  obtain ⟨hne, hall⟩ := hcheck
  refine ⟨hne, fun ax hax => ?_⟩
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp hax
  have hchk := hall ea hea
  cases ea with
  | sub1 a b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
    intro x hx
    exact (hchk x.val x.property).elim
      (fun h => absurd hx (by simp [elModelToInterpretation, classHolds, h])) id
  | sub2 a1 a2 b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff] at hchk
    intro x ⟨h1, h2⟩
    rcases hchk x.val x.property with (h | h) | h
    · exact absurd h1 (by simp [elModelToInterpretation, classHolds, h])
    · exact absurd h2 (by simp [elModelToInterpretation, classHolds, h])
    · exact h
  | existR a r b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.any_eq_true, Bool.and_eq_true] at hchk
    intro x hx
    rcases hchk x.val x.property with hna | ⟨v, hv, hrv, hbv⟩
    · exact absurd hx (by simp [elModelToInterpretation, classHolds, hna])
    · exact ⟨⟨v, hv⟩, hrv, hbv⟩
  | existL r a b =>
    intro x ⟨y, hxy, hay⟩
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r = topObjectProperty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
      exact (hchk x.val x.property y.val y.property).elim
        (fun h => absurd hay (by simp [elModelToInterpretation, classHolds, h])) id
    · by_cases hb : r = bottomObjectProperty
      · subst hb; simp [elModelToInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
      · have hcond1 : (r == topObjectProperty) = false := beq_false_of_ne ht
        have hcond2 : (r == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem : (r, x.val, y.val) ∈ m.edges := by
          simp only [elModelToInterpretation, objectHolds, ELModel.hasEdge, hcond1, hcond2,
            Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        have hay' : m.hasCls a y.val = true := hay
        exact (hchk (r, x.val, y.val) hmem).elim
          (fun hnot => absurd (by simp [x.property, y.property, hay']) hnot) id
  | roleSub r s =>
    intro x y hxy
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r = topObjectProperty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true] at hchk
      exact hchk x.val x.property y.val y.property
    · by_cases hb : r = bottomObjectProperty
      · subst hb; simp [elModelToInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
      · have hcond1 : (r == topObjectProperty) = false := beq_false_of_ne ht
        have hcond2 : (r == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem : (r, x.val, y.val) ∈ m.edges := by
          simp only [elModelToInterpretation, objectHolds, ELModel.hasEdge, hcond1, hcond2,
            Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        exact (hchk (r, x.val, y.val) hmem).elim
          (fun hnot => absurd (by simp [x.property, y.property]) hnot) id
  | roleChain r1 r2 s =>
    intro x z ⟨y, hxy, w, hyw, hzw⟩
    subst hzw
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r1 = topObjectProperty ∨ r2 = topObjectProperty
    · have hcond : (r1 == topObjectProperty || r2 == topObjectProperty) = true := by
        rcases ht with rfl | rfl <;> simp
      simp only [hcond, ↓reduceIte, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
      rcases hchk x.val x.property y.val y.property with h | hall2
      · exact absurd hxy (by simp [elModelToInterpretation, objectHolds, h])
      · exact (hall2 w.val w.property).elim
          (fun h => absurd hyw (by simp [elModelToInterpretation, objectHolds, h])) id
    · have hnt1 : r1 ≠ topObjectProperty := fun h => ht (Or.inl h)
      have hnt2 : r2 ≠ topObjectProperty := fun h => ht (Or.inr h)
      by_cases hb : r1 = bottomObjectProperty ∨ r2 = bottomObjectProperty
      · rcases hb with rfl | rfl
        · simp [elModelToInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
        · simp [elModelToInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hyw
      · have hnb1 : r1 ≠ bottomObjectProperty := fun h => hb (Or.inl h)
        have hnb2 : r2 ≠ bottomObjectProperty := fun h => hb (Or.inr h)
        have hc1 : (r1 == topObjectProperty || r2 == topObjectProperty) = false := by
          simp [beq_false_of_ne hnt1, beq_false_of_ne hnt2]
        have hc2 : (r1 == bottomObjectProperty || r2 == bottomObjectProperty) = false := by
          simp [beq_false_of_ne hnb1, beq_false_of_ne hnb2]
        simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem1 : (r1, x.val, y.val) ∈ m.edges := by
          simp only [elModelToInterpretation, objectHolds, ELModel.hasEdge, beq_false_of_ne hnt1,
            beq_false_of_ne hnb1, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        have hmem2 : (r2, y.val, w.val) ∈ m.edges := by
          simp only [elModelToInterpretation, objectHolds, ELModel.hasEdge, beq_false_of_ne hnt2,
            beq_false_of_ne hnb2, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hyw
          exact hyw
        rcases hchk (r1, x.val, y.val) hmem1 with hnot1 | hall2
        · exact absurd (by simp [x.property, y.property]) hnot1
        · exact (hall2 (r2, y.val, w.val) hmem2).elim
            (fun hnot2 => absurd (by simp [w.property]) hnot2) id
  | roleRefl r =>
    simp only [ELModel.checkAxiom, List.all_eq_true] at hchk
    intro x; exact hchk x.val x.property

theorem checkELModel_counter_sub_with {dm : DatatypeMap} {axs : List ELAxiom}
    {m : ELModel} {a b u : IRI}
    (hcheck : checkELModel axs m = true)
    (hu : u ∈ m.nodes) (ha : m.hasCls a u = true) (hb : m.hasCls b u = false) :
    ¬ Entails dm (elOntology axs) [.subClassOf (.named a) (.named b)] := by
  obtain ⟨hne, hsat⟩ := checkELModel_sound_with (dm := dm) hcheck
  intro hent
  obtain ⟨_, hq⟩ := hent (elModelToInterpretation dm m hne) (satisfies_models hsat)
  have hsub := hq (.subClassOf (.named a) (.named b)) (List.mem_singleton_self _)
  have hb' : m.hasCls b u = true := hsub ⟨u, hu⟩ ha
  rw [hb] at hb'; exact Bool.false_ne_true hb'

private def certifyELRow (axs : List ELAxiom) (sat : ELSaturation)
    (a : IRI) (m : ELModel) : List IRI → Option (List (IRI × IRI))
  | [] => some []
  | b :: rest =>
    match sat.subProofs.get? (a, b) with
    | some pf =>
      if checkELProof axs pf (.sub a b) then
        (certifyELRow axs sat a m rest).map fun tl => (a, b) :: tl
      else none
    | none =>
      if !m.hasCls b a then
        certifyELRow axs sat a m rest
      else none

private theorem certifyELRow_sound {dm : DatatypeMap} {axs : List ELAxiom}
    {sat : ELSaturation} {a : IRI} {m : ELModel}
    (hm : checkELModel axs m = true) (ha_mem : a ∈ m.nodes) (ha_cls : m.hasCls a a = true)
    {bs : List IRI} {subs : List (IRI × IRI)}
    (h : certifyELRow axs sat a m bs = some subs) :
    ∀ x y, (x, y) ∈ subs ↔ x = a ∧ y ∈ bs ∧ Entails dm (elOntology axs) [.subClassOf (.named x) (.named y)] := by
  induction bs generalizing subs with
  | nil =>
    simp only [certifyELRow, Option.some.injEq] at h; subst h
    intro x y; simp
  | cons b rest ih =>
    simp only [certifyELRow] at h
    cases hget : sat.subProofs.get? (a, b) with
    | some pf =>
      rw [hget] at h
      cases hpf : checkELProof axs pf (.sub a b) with
      | false => simp [hpf] at h
      | true =>
        simp only [hpf, ↓reduceIte] at h
        obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp h
        have ih' := ih htl
        have hentAB : Entails dm (elOntology axs) [.subClassOf (.named a) (.named b)] :=
          checkELProof_entails_sub hpf
        intro x y
        simp only [List.mem_cons, Prod.mk.injEq, ih']
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, hy, hent⟩)
          · exact ⟨rfl, Or.inl rfl, hentAB⟩
          · exact ⟨rfl, Or.inr hy, hent⟩
        · rintro ⟨rfl, rfl | hy, hent⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, hy, hent⟩
    | none =>
      rw [hget] at h
      cases hnb : m.hasCls b a with
      | true => simp [hnb] at h
      | false =>
        simp only [hnb, Bool.not_false, ↓reduceIte] at h
        have hnotAB : ¬ Entails dm (elOntology axs) [.subClassOf (.named a) (.named b)] :=
          checkELModel_counter_sub_with hm ha_mem ha_cls hnb
        have ih' := ih h
        intro x y
        rw [ih']
        constructor
        · rintro ⟨rfl, hy, hent⟩; exact ⟨rfl, List.mem_cons_of_mem _ hy, hent⟩
        · rintro ⟨rfl, hy, hent⟩
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact absurd hent hnotAB
          · exact ⟨rfl, hy', hent⟩

private def certifyELClasses (axs : List ELAxiom) (sat : ELSaturation)
    (allClasses : List IRI) : List IRI → Option (List IRI × List (IRI × IRI))
  | [] => some ([], [])
  | a :: rest =>
    match sat.subProofs.get? (a, nothing) with
    | some pfBot =>
      if checkELProof axs pfBot (.sub a nothing) then
        (certifyELClasses axs sat allClasses rest).map fun (us, ss) =>
          (a :: us, allClasses.map (fun b => (a, b)) ++ ss)
      else none
    | none =>
      let m := sat.extractReachableModel a
      if checkELModel axs m && m.nodes.contains a && m.hasCls a a && !m.hasCls nothing a then
        (certifyELRow axs sat a m allClasses).bind fun row =>
          (certifyELClasses axs sat allClasses rest).map fun (us, ss) =>
            (us, row ++ ss)
      else none

private theorem certifyELClasses_sound {dm : DatatypeMap} {axs : List ELAxiom}
    {sat : ELSaturation} {allClasses rem : List IRI}
    {unsat : List IRI} {subs : List (IRI × IRI)}
    (h : certifyELClasses axs sat allClasses rem = some (unsat, subs)) :
    (∀ c, c ∈ unsat ↔ c ∈ rem ∧ Entails dm (elOntology axs) [.subClassOf (.named c) (.named nothing)]) ∧
    (∀ x y, (x, y) ∈ subs ↔ x ∈ rem ∧ y ∈ allClasses ∧ Entails dm (elOntology axs) [.subClassOf (.named x) (.named y)]) := by
  induction rem generalizing unsat subs with
  | nil =>
    simp only [certifyELClasses, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun c => by simp, fun x y => by simp⟩
  | cons a rest ih =>
    simp only [certifyELClasses] at h
    cases hbot : sat.subProofs.get? (a, nothing) with
    | some pfBot =>
      rw [hbot] at h
      cases hpf : checkELProof axs pfBot (.sub a nothing) with
      | false => simp [hpf] at h
      | true =>
        simp only [hpf, ↓reduceIte] at h
        obtain ⟨⟨us, ss⟩, hrec, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨ihu, ihs⟩ := ih hrec
        have hEntBot : Entails dm (elOntology axs) [.subClassOf (.named a) (.named nothing)] :=
          checkELProof_entails_sub hpf
        refine ⟨fun c => ?_, fun x y => ?_⟩
        · simp only [List.mem_cons, ihu]
          constructor
          · rintro (rfl | ⟨hc, he⟩)
            · exact ⟨Or.inl rfl, hEntBot⟩
            · exact ⟨Or.inr hc, he⟩
          · rintro ⟨rfl | hc, he⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hc, he⟩
        · simp only [List.mem_append, List.mem_map, Prod.mk.injEq, ihs, List.mem_cons]
          constructor
          · rintro (⟨b, hb, rfl, rfl⟩ | ⟨hx, hy, he⟩)
            · exact ⟨Or.inl rfl, hb, entails_sub_of_unsat hEntBot⟩
            · exact ⟨Or.inr hx, hy, he⟩
          · rintro ⟨rfl | hx, hy, he⟩
            · exact Or.inl ⟨y, hy, rfl, rfl⟩
            · exact Or.inr ⟨hx, hy, he⟩
    | none =>
      rw [hbot] at h
      cases hm : (checkELModel axs (sat.extractReachableModel a) &&
          (sat.extractReachableModel a).nodes.contains a &&
          (sat.extractReachableModel a).hasCls a a &&
          !(sat.extractReachableModel a).hasCls nothing a) with
      | false => dsimp only at h; rw [hm] at h; simp at h
      | true =>
        dsimp only at h; rw [hm] at h; simp only [↓reduceIte] at h
        simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hm
        obtain ⟨⟨⟨hmChk, haMem⟩, haCls⟩, hNotBot⟩ := hm
        obtain ⟨row, hrow, hrest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨us, ss⟩, hrec, heq⟩ := Option.map_eq_some_iff.mp hrest
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨ihu, ihs⟩ := ih hrec
        have hRow := certifyELRow_sound (dm := dm) hmChk haMem haCls hrow
        have hSatA : ¬ Entails dm (elOntology axs) [.subClassOf (.named a) (.named nothing)] :=
          checkELModel_counter_sub_with hmChk haMem haCls hNotBot
        refine ⟨fun c => ?_, fun x y => ?_⟩
        · rw [ihu]
          constructor
          · rintro ⟨hc, he⟩; exact ⟨List.mem_cons_of_mem _ hc, he⟩
          · rintro ⟨hc, he⟩
            rcases List.mem_cons.mp hc with rfl | hc'
            · exact absurd he hSatA
            · exact ⟨hc', he⟩
        · simp only [List.mem_append, hRow, ihs, List.mem_cons]
          constructor
          · rintro (⟨rfl, hy, he⟩ | ⟨hx, hy, he⟩)
            · exact ⟨Or.inl rfl, hy, he⟩
            · exact ⟨Or.inr hx, hy, he⟩
          · rintro ⟨rfl | hx, hy, he⟩
            · exact Or.inl ⟨rfl, hy, he⟩
            · exact Or.inr ⟨hx, hy, he⟩

/-- Single-pass polynomial $\mathcal{EL}^{++}$ classifier: runs `saturateEL` ONCE
    for all `namedClasses`, verifies `O(n)` canonical models + `ELProof`s, and computes
    hash-indexed `equivalences` and `directParents`. -/
def classifyELSinglePass (axs : List ELAxiom) (namedClasses : List IRI) :
    Option ClassHierarchy :=
  let sat := saturateEL axs namedClasses
  match sat.subProofs.get? (thing, nothing) with
  | some pf =>
    if checkELProof axs pf (.sub thing nothing) then
      some {
        consistent := false
        classes := namedClasses
        unsatisfiable := namedClasses
        subsumptions := []
        equivalences := []
        directParents := []
      }
    else none
  | none =>
    let m0 := sat.extractReachableModel thing
    if checkELModel axs m0 then
      (certifyELClasses axs sat namedClasses namedClasses).map fun (unsat, subs) =>
        let satClasses := namedClasses.filter (!unsat.contains ·)
        let subSet := setOfPairs subs
        {
          consistent := true
          classes := namedClasses
          unsatisfiable := unsat
          subsumptions := subs
          equivalences := computeEquivClassesFast satClasses subSet
          directParents := computeDirectParentsFast satClasses subSet
        }
    else none

/-- Kernel-checked soundness and completeness for single-pass polynomial $\mathcal{EL}^{++}$
    classification over arbitrary `DatatypeMap`. -/
theorem classifyELSinglePass_sound_complete {dm : DatatypeMap}
    {axs : List ELAxiom} {namedClasses : List IRI} {h : ClassHierarchy}
    (hcls : classifyELSinglePass axs namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable dm (elOntology axs)) ∧
    (h.consistent = true →
      Satisfiable dm (elOntology axs) ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm (elOntology axs) [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm (elOntology axs) [.subClassOf (.named a) (.named b)])) := by
  unfold classifyELSinglePass at hcls
  dsimp only at hcls
  cases htop : (saturateEL axs namedClasses).subProofs.get? (thing, nothing) with
  | some pf =>
    rw [htop] at hcls
    cases hpf : checkELProof axs pf (.sub thing nothing) with
    | false => simp [hpf] at hcls
    | true =>
      simp only [hpf, ↓reduceIte, Option.some.injEq] at hcls; subst hcls
      exact ⟨fun _ => checkELProof_inconsistent hpf, fun hc => by cases hc⟩
  | none =>
    rw [htop] at hcls
    cases hm0 : checkELModel axs ((saturateEL axs namedClasses).extractReachableModel thing) with
    | false => simp [hm0] at hcls
    | true =>
      simp only [hm0, ↓reduceIte] at hcls
      obtain ⟨⟨unsat, subs⟩, hcert, rfl⟩ := Option.map_eq_some_iff.mp hcls
      obtain ⟨hne, hsat0⟩ := checkELModel_sound_with (dm := dm) hm0
      obtain ⟨hunsat, hsubs⟩ := certifyELClasses_sound (dm := dm) hcert
      exact ⟨(fun hc => by cases hc), fun _ =>
        ⟨⟨elModelToInterpretation dm _ hne, satisfies_models hsat0⟩, hunsat, hsubs⟩⟩

/-! ### 4. Direct Zero-Aux EL++ Normalization Bridge (Exact Model Equivalence) -/

private def directELAxiom : Axiom → Option (List ELAxiom)
  | .subClassOf (.named a) (.named b) => some [.sub1 a b]
  | .subClassOf (.intersection (.named a1) (.named a2)) (.named b) => some [.sub2 a1 a2 b]
  | .subClassOf (.named a) (.objectSome (.named r) (.named b)) => some [.existR a r b]
  | .subClassOf (.objectSome (.named r) (.named a)) (.named b) => some [.existL r a b]
  | .equivalentClasses [.named a, .named b] => some [.sub1 a b, .sub1 b a]
  | .disjointClasses [.named a, .named b] => some [.sub2 a b nothing]
  | .subObjectProperty (.named r) (.named s) => some [.roleSub r s]
  | .equivalentObjectProperties [.named r, .named s] => some [.roleSub r s, .roleSub s r]
  | .transitiveObjectProperty (.named r) => some [.roleChain r r r]
  | .subObjectPropertyChain [.named r1, .named r2] (.named s) => some [.roleChain r1 r2 s]
  | .objectPropertyDomain (.named r) (.named c) => some [.existL r thing c]
  | .reflexiveObjectProperty (.named r) => some [.roleRefl r]
  | _ => none

private theorem directELAxiom_iff {dm : DatatypeMap} (i : Interpretation dm)
    {ax : Axiom} {eas : List ELAxiom} (h : directELAxiom ax = some eas) :
    axiomHolds i ax ↔ ∀ ea ∈ eas, axiomHolds i ea.toAxiom := by
  cases ax with
  | subClassOf c1 c2 =>
    cases c1 <;> cases c2 <;> simp [directELAxiom] at h
    case named.named a b => subst h; simp [ELAxiom.toAxiom]
    case named.objectSome a r f =>
      cases r <;> cases f <;> simp at h
      subst h; simp [ELAxiom.toAxiom]
    case intersection.named x y b =>
      cases x <;> cases y <;> simp at h
      subst h; simp [ELAxiom.toAxiom]
    case objectSome.named r f b =>
      cases r <;> cases f <;> simp at h
      subst h; simp [ELAxiom.toAxiom]
  | equivalentClasses cs =>
    match cs with
    | [.named a, .named b] =>
      simp only [directELAxiom, Option.some.injEq] at h; subst h
      constructor
      · intro heq ea hea
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hea
        rcases hea with rfl | rfl
        · exact fun x hx => (heq (.named a) (by simp) (.named b) (by simp) x).mp hx
        · exact fun x hx => (heq (.named b) (by simp) (.named a) (by simp) x).mp hx
      · intro hall c1 hc1 c2 hc2 x
        have hab := hall (.sub1 a b) (by simp) x
        have hba := hall (.sub1 b a) (by simp) x
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        · exact Iff.rfl
        · exact ⟨hab, hba⟩
        · exact ⟨hba, hab⟩
        · exact Iff.rfl
    | [] | [_] | _ :: _ :: _ :: _ | (.complement _ :: _) | (.intersection _ _ :: _)
    | (.union _ _ :: _) | (.oneOf _ :: _) | (.objectSome _ _ :: _) | (.objectAll _ _ :: _)
    | (.objectValue _ _ :: _) | (.objectSelf _ :: _) | (.objectMin _ _ _ :: _)
    | (.objectMax _ _ _ :: _) | (.objectExact _ _ _ :: _) | (.dataSome _ _ :: _)
    | (.dataAll _ _ :: _) | (.dataValue _ _ :: _) | (.dataMin _ _ _ :: _)
    | (.dataMax _ _ _ :: _) | (.dataExact _ _ _ :: _)
    | [.named _, .complement _] | [.named _, .intersection _ _] | [.named _, .union _ _]
    | [.named _, .oneOf _] | [.named _, .objectSome _ _] | [.named _, .objectAll _ _]
    | [.named _, .objectValue _ _] | [.named _, .objectSelf _] | [.named _, .objectMin _ _ _]
    | [.named _, .objectMax _ _ _] | [.named _, .objectExact _ _ _] | [.named _, .dataSome _ _]
    | [.named _, .dataAll _ _] | [.named _, .dataValue _ _] | [.named _, .dataMin _ _ _]
    | [.named _, .dataMax _ _ _] | [.named _, .dataExact _ _ _] =>
      simp [directELAxiom] at h
  | disjointClasses cs =>
    match cs with
    | [.named a, .named b] =>
      simp only [directELAxiom, Option.some.injEq] at h; subst h
      constructor
      · intro hdisj ea hea
        simp only [List.mem_singleton] at hea; subst hea
        intro x ⟨ha, hb⟩
        have hp := (List.pairwise_cons.mp hdisj).1 (.named b) (List.mem_singleton.mpr rfl) x
        exact absurd ⟨ha, hb⟩ hp
      · intro hall
        have hbot := hall (.sub2 a b nothing) (List.mem_singleton.mpr rfl)
        refine List.pairwise_cons.mpr ⟨fun c hc x ⟨ha, hb⟩ => ?_,
          List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil⟩
        rw [List.mem_singleton.mp hc] at hb
        exact i.nothingExt x (hbot x ⟨ha, hb⟩)
    | [] | [_] | _ :: _ :: _ :: _ | (.complement _ :: _) | (.intersection _ _ :: _)
    | (.union _ _ :: _) | (.oneOf _ :: _) | (.objectSome _ _ :: _) | (.objectAll _ _ :: _)
    | (.objectValue _ _ :: _) | (.objectSelf _ :: _) | (.objectMin _ _ _ :: _)
    | (.objectMax _ _ _ :: _) | (.objectExact _ _ _ :: _) | (.dataSome _ _ :: _)
    | (.dataAll _ _ :: _) | (.dataValue _ _ :: _) | (.dataMin _ _ _ :: _)
    | (.dataMax _ _ _ :: _) | (.dataExact _ _ _ :: _)
    | [.named _, .complement _] | [.named _, .intersection _ _] | [.named _, .union _ _]
    | [.named _, .oneOf _] | [.named _, .objectSome _ _] | [.named _, .objectAll _ _]
    | [.named _, .objectValue _ _] | [.named _, .objectSelf _] | [.named _, .objectMin _ _ _]
    | [.named _, .objectMax _ _ _] | [.named _, .objectExact _ _ _] | [.named _, .dataSome _ _]
    | [.named _, .dataAll _ _] | [.named _, .dataValue _ _] | [.named _, .dataMin _ _ _]
    | [.named _, .dataMax _ _ _] | [.named _, .dataExact _ _ _] =>
      simp [directELAxiom] at h
  | subObjectProperty r s =>
    cases r <;> cases s <;> simp [directELAxiom] at h
    subst h; simp [ELAxiom.toAxiom]
  | equivalentObjectProperties rs =>
    match rs with
    | [.named r, .named s] =>
      simp only [directELAxiom, Option.some.injEq] at h; subst h
      constructor
      · intro heq ea hea
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hea
        rcases hea with rfl | rfl
        · exact fun x y hxy => (heq (.named r) (by simp) (.named s) (by simp) x y).mp hxy
        · exact fun x y hxy => (heq (.named s) (by simp) (.named r) (by simp) x y).mp hxy
      · intro hall p1 hp1 p2 hp2 x y
        have hrs := hall (.roleSub r s) (by simp) x y
        have hsr := hall (.roleSub s r) (by simp) x y
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp1 hp2
        rcases hp1 with rfl | rfl <;> rcases hp2 with rfl | rfl
        · exact Iff.rfl
        · exact ⟨hrs, hsr⟩
        · exact ⟨hsr, hrs⟩
        · exact Iff.rfl
    | [] | [_] | _ :: _ :: _ :: _ | (.inverse _ :: _) | [.named _, .inverse _] =>
      simp [directELAxiom] at h
  | transitiveObjectProperty r =>
    cases r <;> simp [directELAxiom] at h
    subst h
    simp only [List.mem_singleton, forall_eq, ELAxiom.toAxiom, axiomHolds, objectHolds, rolePath]
    constructor
    · rintro htr x z ⟨y, hxy, w, hyw, rfl⟩; exact htr x y w hxy hyw
    · intro hch x y z hxy hyz; exact hch x z ⟨y, hxy, z, hyz, rfl⟩
  | subObjectPropertyChain rs s =>
    rcases rs with _ | ⟨r1, _ | ⟨r2, _ | _⟩⟩ <;> cases s <;> try simp [directELAxiom] at h
    cases r1 <;> cases r2 <;> simp at h
    subst h; simp [ELAxiom.toAxiom]
  | objectPropertyDomain r c =>
    cases r <;> cases c <;> simp [directELAxiom] at h
    subst h
    simp only [List.mem_singleton, forall_eq, ELAxiom.toAxiom, axiomHolds, objectHolds, classHolds]
    constructor
    · rintro hdom x ⟨y, hxy, _⟩; exact hdom x y hxy
    · intro hex x y hxy; exact hex x ⟨y, hxy, i.thingExt y⟩
  | reflexiveObjectProperty r =>
    cases r <;> simp [directELAxiom] at h
    subst h; simp [ELAxiom.toAxiom]
  | _ => simp [directELAxiom] at h

/-- Normalize a direct $\mathcal{EL}^{++}$ ontology with zero fresh auxiliary symbols. -/
def directELNormalize : Ontology → Option (List ELAxiom)
  | [] => some []
  | ax :: rest =>
    (directELAxiom ax).bind fun eas =>
      (directELNormalize rest).map fun tl => eas ++ tl

theorem directELNormalize_satisfies_iff {dm : DatatypeMap} (i : Interpretation dm)
    {o : Ontology} {axs : List ELAxiom} (h : directELNormalize o = some axs) :
    satisfies i o ↔ satisfies i (elOntology axs) := by
  induction o generalizing axs with
  | nil =>
    simp only [directELNormalize, Option.some.injEq] at h; subst h
    simp [satisfies, elOntology]
  | cons ax rest ih =>
    simp only [directELNormalize, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨eas, heas, tl, htl, rfl⟩ := h
    have ih' := ih htl
    have hax := directELAxiom_iff i heas
    simp only [satisfies, elOntology, List.map_append, List.mem_cons, List.mem_append,
      List.mem_map] at ih' ⊢
    constructor
    · intro hs a ha
      rcases ha with ⟨ea, hea, rfl⟩ | ⟨ea, hea, rfl⟩
      · exact hax.mp (hs ax (Or.inl rfl)) ea hea
      · exact (ih'.mp (fun x hx => hs x (Or.inr hx))) _ ⟨ea, hea, rfl⟩
    · intro hs a ha
      rcases ha with rfl | hrest
      · exact hax.mpr fun ea hea => hs ea.toAxiom (Or.inl ⟨ea, hea, rfl⟩)
      · exact (ih'.mpr (fun x hx => hs x (Or.inr hx))) a hrest

theorem directELNormalize_models_iff {dm : DatatypeMap} (i : Interpretation dm)
    {o : Ontology} {axs : List ELAxiom} (h : directELNormalize o = some axs) :
    models i o ↔ models i (elOntology axs) :=
  exists_congr fun assign => directELNormalize_satisfies_iff (i.withAnonymous assign) h

/-- Certified single-pass polynomial $\mathcal{EL}^{++}$ classifier directly on OWL 2 `Ontology`. -/
def classifyDirectEL (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  (directELNormalize o).bind fun axs => classifyELSinglePass axs namedClasses

theorem classifyDirectEL_sound_complete {dm : DatatypeMap}
    {o : Ontology} {namedClasses : List IRI} {h : ClassHierarchy}
    (hcls : classifyDirectEL o namedClasses = some h) :
    (h.consistent = false → ¬ Satisfiable dm o) ∧
    (h.consistent = true →
      Satisfiable dm o ∧
      (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm o [.subClassOf (.named c) (.named nothing)]) ∧
      (∀ a b, (a, b) ∈ h.subsumptions ↔
        a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm o [.subClassOf (.named a) (.named b)])) := by
  simp only [classifyDirectEL, Option.bind_eq_some_iff] at hcls
  obtain ⟨axs, hnorm, hel⟩ := hcls
  have hsatEq : Satisfiable dm o ↔ Satisfiable dm (elOntology axs) :=
    exists_congr fun i => directELNormalize_models_iff i hnorm
  have hentEq : ∀ q, Entails dm o q ↔ Entails dm (elOntology axs) q := fun q =>
    forall_congr' fun i => imp_congr (directELNormalize_models_iff i hnorm) Iff.rfl
  obtain ⟨h1, h2⟩ := classifyELSinglePass_sound_complete (dm := dm) hel
  refine ⟨fun hf hs => h1 hf (hsatEq.mp hs), fun ht => ?_⟩
  obtain ⟨hs, hu, hsub⟩ := h2 ht
  refine ⟨hsatEq.mpr hs, fun c => by rw [hu c, hentEq], fun a b => by rw [hsub a b, hentEq]⟩

/-! ### 5. Certified Enhanced Traversal with `FastLocality.LocalityIndex` -/

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

/-- Seed `knownFalse` from told `DisjointClasses` axioms whenever the left class is in `satSet`. -/
private def seedDisjointFromList (cs : List ClassExpr) (st : ClsCache) : ClsCache :=
  let indexed := cs.zipIdx
  indexed.foldl (fun s1 (c1, i1) =>
    match c1 with
    | .named a =>
      if s1.satSet.contains a then
        indexed.foldl (fun s2 (c2, i2) =>
          match c2 with
          | .named b =>
            if i1 != i2 && s2.satSet.contains a then
              { s2 with knownFalse := s2.knownFalse.insert (a, b) }
            else s2
          | _ => s2) s1
      else s1
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
    {cs : List ClassExpr} (hmem : .disjointClasses cs ∈ o) (st : ClsCache)
    (hv : st.Valid dm o) : (seedDisjointFromList cs st).Valid dm o := by
  have inner : ∀ (a : IRI) (i1 : Nat), cs[i1]? = some (ClassExpr.named a) →
      ∀ (ys : List (ClassExpr × Nat)), (∀ p ∈ ys, p ∈ cs.zipIdx) →
      ∀ (s : ClsCache), s.Valid dm o →
      (ys.foldl (fun s2 (c2, i2) =>
        match c2 with
        | ClassExpr.named b =>
          if i1 != i2 && s2.satSet.contains a then
            { s2 with knownFalse := s2.knownFalse.insert (a, b) }
          else s2
        | _ => s2) s).Valid dm o := by
    intro a i1 hi1 ys
    induction ys with
    | nil => intro _ s hs; exact hs
    | cons p tl ih =>
      intro hsub s hs
      rcases p with ⟨c2, i2⟩
      simp only [List.foldl_cons]
      have htl := ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
      cases c2 with
      | named b =>
        cases hc : (i1 != i2 && s.satSet.contains a)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact htl s hs
        · simp only [↓reduceIte]
          obtain ⟨hne, hsatA⟩ := Bool.and_eq_true_iff.mp hc
          have hi2 : cs[i2]? = some (ClassExpr.named b) := mem_zipIdx_getElem? (hsub _ (List.mem_cons_self ..))
          exact htl _ (ClsCache.valid_insertFalse hs
            (not_entails_sub_of_disjoint_pairwise hmem ⟨i1, i2, bne_iff_ne.mp hne, hi1, hi2⟩ (hs.2.2.1 a hsatA)))
      | _ => exact htl s hs
  have outer : ∀ (xs : List (ClassExpr × Nat)), (∀ p ∈ xs, p ∈ cs.zipIdx) →
      ∀ (s : ClsCache), s.Valid dm o →
      (xs.foldl (fun s1 (c1, i1) =>
        match c1 with
        | ClassExpr.named a =>
          if s1.satSet.contains a then
            cs.zipIdx.foldl (fun s2 (c2, i2) =>
              match c2 with
              | ClassExpr.named b =>
                if i1 != i2 && s2.satSet.contains a then
                  { s2 with knownFalse := s2.knownFalse.insert (a, b) }
                else s2
              | _ => s2) s1
          else s1
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
        cases hsat : s.satSet.contains a with
        | false =>
          simp only [hsat, Bool.false_eq_true, ↓reduceIte]
          exact htl s hs
        | true =>
          simp only [hsat, ↓reduceIte]
          have hi1 : cs[i1]? = some (ClassExpr.named a) := mem_zipIdx_getElem? (hsub _ (List.mem_cons_self ..))
          exact htl _ (inner a i1 hi1 cs.zipIdx (fun _ h => h) s hs)
      | _ => exact htl s hs
  exact outer cs.zipIdx (fun _ h => h) st hv

private def seedToldDisjoint (xs : Ontology) (st : ClsCache) : ClsCache :=
  xs.foldl (fun acc ax =>
    match ax with
    | .disjointClasses cs => seedDisjointFromList cs acc
    | _ => acc) st

private theorem seedToldDisjoint_valid {dm : DatatypeMap} {o : Ontology} (xs : Ontology)
    (hsub : ∀ ax ∈ xs, ax ∈ o) :
    ∀ st, st.Valid dm o → (seedToldDisjoint xs st).Valid dm o := by
  induction xs with
  | nil => intro st hv; exact hv
  | cons ax tl ih =>
    intro st hv
    simp only [seedToldDisjoint, List.foldl_cons]
    have htl := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    have hmem : ax ∈ o := hsub ax (List.mem_cons_self ..)
    cases ax with
    | disjointClasses cs => exact htl _ (seedDisjointFromList_valid hmem st hv)
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
                exact ihd _ (ClsCache.valid_insertTrue hvs (entails_sub_of_unsat (hvs.2.2.2 _ hc)))
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

/-- Enhanced Traversal over a list of candidate pairs `(a, b)`:
    1. Checks `knownTrue` / `knownFalse` in `O(1)`
    2. Checks transitive `knownTrue` witnesses (`a ⊑ mid ∧ mid ⊑ b`)
    3. Checks Enhanced Traversal contrapositive witnesses (`mid ⊑ a ∧ mid ⋢ b` or `b ⊑ mid ∧ a ⋢ mid`)
    4. Only queries `solve` on the per-pair ⊥-local module when still undecided, and eagerly
       propagates the result (plus any verified countermodel non-subsumptions from `harvest`). -/
private def traversePairs (solve : Ontology → Option Bool)
    (harvest : Ontology → IRI → IRI → List (IRI × IRI))
    (idx : LocalityIndex) (o : Ontology) (allClasses : List IRI) :
    List (IRI × IRI) → ClsCache → Option (List (IRI × IRI) × ClsCache)
  | [], st => some ([], st)
  | (a, b) :: rest, st =>
    if st.knownTrue.contains (a, b) then
      (traversePairs solve harvest idx o allClasses rest st).map fun (ps, st') => ((a, b) :: ps, st')
    else if st.knownFalse.contains (a, b) then
      traversePairs solve harvest idx o allClasses rest st
    else if allClasses.any fun mid => st.knownTrue.contains (a, mid) && st.knownTrue.contains (mid, b) then
      let st1 := insertTrueAndClose allClasses a b st
      (traversePairs solve harvest idx o allClasses rest st1).map fun (ps, st') => ((a, b) :: ps, st')
    else if allClasses.any fun mid =>
        (st.knownTrue.contains (mid, a) && st.knownFalse.contains (mid, b)) ||
        (st.knownTrue.contains (b, mid) && st.knownFalse.contains (a, mid)) then
      let st1 := insertFalseAndClose allClasses a b st
      traversePairs solve harvest idx o allClasses rest st1
    else
      let seed := axiomSig (.subClassOf (.named a) (.named b))
      let mod := (extractBotModuleWithIndex idx o seed).1
      (decidesSubsumption solve mod a b).bind fun isSub =>
        if isSub then
          let st1 := insertTrueAndClose allClasses a b st
          (traversePairs solve harvest idx o allClasses rest st1).map fun (ps, st') => ((a, b) :: ps, st')
        else
          let st1 := insertFalseAndClose allClasses a b st
          let harvested := harvest mod a b
          let st2 := harvested.foldl (fun s p => { s with knownFalse := s.knownFalse.insert p }) st1
          traversePairs solve harvest idx o allClasses rest st2

private theorem traversePairs_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    (idx : LocalityIndex) (o : Ontology)
    {harvest : Ontology → IRI → IRI → List (IRI × IRI)}
    (hharv : ∀ {mod a b p},
      (∃ seed σ, ValidBotModule o seed mod σ) →
      p ∈ harvest mod a b → ¬ Entails dm o [.subClassOf (.named p.1) (.named p.2)])
    (allClasses : List IRI) (rem : List (IRI × IRI)) :
    ∀ st ps st', st.Valid dm o →
      traversePairs solve harvest idx o allClasses rem st = some (ps, st') →
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
    simp only [traversePairs] at h
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
            obtain ⟨isSub, hdec, hrest⟩ := h
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

/-- Certified Enhanced Traversal classifier parameterized by any exact consistency
    solver `solve` and optional certified countermodel harvester `harvest`. -/
def classifyEnhancedCore (solve : Ontology → Option Bool)
    (initHarvest : Ontology → List IRI → List (IRI × IRI))
    (stepHarvest : Ontology → IRI → IRI → List (IRI × IRI))
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
        let st2 := seedToldDisjoint o st1
        let st3 := (initHarvest o namedClasses).foldl
          (fun s p => { s with knownFalse := s.knownFalse.insert p }) st2
        let allPairs := orderedPairs namedClasses
        (traversePairs solve stepHarvest idx o namedClasses allPairs st3).map fun (subs, _) =>
          let satClasses := namedClasses.filter (!unsat.contains ·)
          let subSet := setOfPairs subs
          {
            consistent := true
            classes := namedClasses
            unsatisfiable := unsat
            subsumptions := subs
            equivalences := computeEquivClassesFast satClasses subSet
            directParents := computeDirectParentsFast satClasses subSet
          }

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
  unfold classifyEnhancedCore at hcls
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
    have hv2 : (seedToldDisjoint o st1).Valid dm o :=
      seedToldDisjoint_valid o (fun _ hx => hx) st1 hv1
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

/-! ### 6. Certified `SROIQDModel` Countermodel Caching (`datatypeMap`) -/

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

/-- Extract all `(c, d)` pairs among `namedClasses` refuted by a verified `SROIQDModel` `m`
    for `o` (zero additional tableau calls). -/
def harvestModelPairs (o : Ontology) (namedClasses : List IRI) (m : SROIQDModel) :
    List (IRI × IRI) :=
  match normalizeWithDefs o with
  | none => []
  | some (_, p) =>
    if p.root == .top && checkModel p m then
      (orderedPairs namedClasses).filter fun (c, d) =>
        c != thing && c != nothing && d != thing && d != nothing && checkModelCounterAt m c d
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
      have hflt := (List.mem_filter.mp hmem).2
      simp only [Bool.and_eq_true, bne_iff_ne] at hflt
      obtain ⟨⟨⟨⟨hcT, hcN⟩, hdT⟩, hdN⟩, hcnt⟩ := hflt
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

/-! ### 7. Fast Hybrid Runtime Classifier -/

private def hasWiderDataOrRealFast (p : Problem) : Bool :=
  p.allDataAtoms.any (fun
    | .datatype t | .restriction t _ => t == owlReal
    | _ => false) ||
  p.allDataAtoms.any SROIQD.Termination.WiderData.isOrderedExactAtom ||
  p.allDataAtoms.any SROIQD.Termination.WiderData.isStringFacetExtraAtom ||
  p.allDataProps.any (fun dp => dp == topDataProperty || dp == bottomDataProperty)

private def checkTableauRolesOkFast (p : Problem) : Bool :=
  let closed := Sabrina.ALC.roleClosure p.rules
  p.simpleRoles.all (fun r => (RoleChains.SimpleRoles.firstComposite closed p.chains r).isNone) &&
  RoleChains.checkRegular (RoleChains.inferRank p.rules p.chains) p.rules p.chains

private def proposeInitModelPairs (o : Ontology) (namedClasses : List IRI) : List (IRI × IRI) :=
  match normalizeWithDefs o with
  | none => []
  | some (_, p) =>
    if !hasWiderDataOrRealFast p && checkTableauRolesOkFast p && p.root == .top then
      let limits : Limits := {}
      match propose p limits with
      | some (.model m) => harvestModelPairs o namedClasses m
      | _ => []
    else []

private def checkELRegular (elAxs : List ELAxiom) : Bool := Id.run do
  let mut rules : Sabrina.ALC.RoleTheory := []
  let mut chains : List RoleChains.Chain := []
  for ax in elAxs do
    match ax with
    | .roleSub r s => rules := ⟨(r, false), (s, false)⟩ :: rules
    | .roleChain r1 r2 s => chains := RoleChains.Chain.named [r1, r2] s :: chains
    | _ => pure ()
  return RoleChains.checkRegular (RoleChains.inferRank rules chains) rules chains

/-- Certified Enhanced Traversal + `SROIQDModel` countermodel seeding over `datatypeMap`. -/
def classifyEnhancedStd (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  match classifyDirectEL o namedClasses with
  | some h => some h
  | none =>
    classifyEnhancedCore SROIQD.Termination.WiderData.decideWithWiderDataRanges?
      proposeInitModelPairs (fun _ _ _ => []) o namedClasses

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
    refine classifyEnhancedCore_sound_complete decideWithWiderDataRanges_iff
      (fun {o' cs' p'} hp => ?_) (fun _ hp => by cases hp) hcls
    unfold proposeInitModelPairs at hp
    split at hp
    · cases hp
    · split at hp
      · dsimp only at hp
        split at hp
        · exact harvestModelPairs_sound hp
        · cases hp
      · cases hp

/-- Fast hybrid runtime TBox classifier:
    1. Pure $\mathcal{EL}^{++}$ ontologies: single-pass polynomial `classifyELSinglePass`
       (1 `saturateEL` pass for the entire ontology instead of `O(n²)` solver calls)
    2. General $\mathcal{SROIQ}(\mathcal{D})$ ontologies: `classifyEnhancedCore` with
       pre-built `FastLocality.LocalityIndex`, told subsumers + transitive closure,
       monotone sat/unsat sweep, told disjointness pruning, `SROIQDModel` countermodel
       seeding, Enhanced Traversal closure, and `Classification.fastConsistencyCheck`. -/
def classifyOntologyFastRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) :
    Option ClassHierarchy :=
  let namedClasses := collectNamedClasses o decls
  let fp := profileOntology o
  if fp.leastFragment == .el then
    match normalizeEL o with
    | some elAxs =>
      if checkELRegular elAxs then
        match classifyELSinglePass elAxs namedClasses with
        | some h => some h
        | none => classifyEnhancedCore fastConsistencyCheck proposeInitModelPairs (fun _ _ _ => []) o namedClasses
      else
        classifyEnhancedCore fastConsistencyCheck proposeInitModelPairs (fun _ _ _ => []) o namedClasses
    | none => classifyEnhancedCore fastConsistencyCheck proposeInitModelPairs (fun _ _ _ => []) o namedClasses
  else
    classifyEnhancedCore fastConsistencyCheck proposeInitModelPairs (fun _ _ _ => []) o namedClasses

/-- Fast hash-indexed direct-type computation (`O(|types|²)` with `O(1)` lookup). -/
def computeDirectTypesFast (types : List IRI) (subSet : Std.HashSet (IRI × IRI)) : List IRI :=
  let strictSub (a b : IRI) : Bool := subSet.contains (a, b) && !subSet.contains (b, a)
  types.filter fun c => !types.any fun moreSpec => strictSub moreSpec c

/-- Fast hybrid runtime ABox realizer backed by `classifyOntologyFastRuntime` and
    cached `FastLocality.LocalityIndex` per-assertion modules. -/
def realizeOntologyFastRuntime (o : Ontology) (decls : List FunctionalSyntax.EntityDecl := []) :
    Option RealizationResult :=
  let namedClasses := collectNamedClasses o decls
  let namedInds := collectNamedIndividuals o decls
  (classifyOntologyFastRuntime o decls).bind fun hier =>
    if !hier.consistent then
      some { consistent := false, individuals := namedInds, entries := [] }
    else
      let idx := LocalityIndex.build o
      let subSet := setOfPairs hier.subsumptions
      let rec goInds : List IRI → Option (List IndividualTypes)
        | [] => some []
        | ind :: rest =>
          let rec goCls : List IRI → Option (List IRI)
            | [] => some []
            | c :: cs =>
              let seed := axiomSig (.classAssertion (.named c) (.named ind))
              let mod := (extractBotModuleWithIndex idx o seed).1
              (decidesInstance fastConsistencyCheck mod c ind).bind fun holds =>
                (goCls cs).map fun tl => if holds then c :: tl else tl
          (goCls namedClasses).bind fun ts =>
            (goInds rest).map fun tl =>
              { individual := ind
                allTypes := ts
                directTypes := computeDirectTypesFast ts subSet } :: tl
      (goInds namedInds).map fun entries =>
        { consistent := true, individuals := namedInds, entries }

end Sabrina.OWL2.FastClassification
