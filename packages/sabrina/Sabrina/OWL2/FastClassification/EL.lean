import Std.Data.HashSet
import Std.Data.HashMap
import Sabrina.OWL2.Classification
import Sabrina.OWL2.EL
import Sabrina.OWL2.FastEL

/-! Single-pass EL classification and its direct OWL 2 normalization bridge. -/

namespace Sabrina.OWL2.FastClassification

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.EL
open Sabrina.OWL2.Classification

/-! ### Hash-indexed equivalence classes and direct parents -/

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

protected def setOfPairs (ps : List (IRI × IRI)) : Std.HashSet (IRI × IRI) :=
  ps.foldl (fun s p => s.insert p) {}

protected theorem entails_sub_of_unsat {dm : DatatypeMap} {o : Ontology} {a b : IRI}
    (hbot : Entails dm o [.subClassOf (.named a) (.named nothing)]) :
    Entails dm o [.subClassOf (.named a) (.named b)] := by
  intro i hmod
  obtain ⟨assign, hs⟩ := hbot i hmod
  have h0 := hs _ (List.mem_singleton.mpr rfl)
  refine satisfies_models fun q hq => ?_
  simp only [List.mem_singleton] at hq; subst hq
  intro x hx
  exact absurd (h0 x hx) ((i.withAnonymous assign).nothingExt x)

/-! ### Single-pass polynomial EL++ classification -/

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
            · exact ⟨Or.inl rfl, hb, FastClassification.entails_sub_of_unsat hEntBot⟩
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
        let subSet := FastClassification.setOfPairs subs
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

/-! ### Direct EL++ normalization without auxiliary symbols -/

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

/-- Certified parallel polynomial $\mathcal{EL}^{++}$ classifier directly on OWL 2 `Ontology`.
    Dispatches to the parallel integer-interned single-model engine (`FastEL.classifyFastELToHierarchy`)
    and falls back to `classifyELSinglePass` only if built-in top/bottom object properties appear. -/
def classifyDirectEL (o : Ontology) (namedClasses : List IRI) : Option ClassHierarchy :=
  (directELNormalize o).bind fun axs =>
    match FastEL.classifyFastELToHierarchy axs namedClasses with
    | some h => some h
    | none => classifyELSinglePass axs namedClasses

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
  have hEL :
      (h.consistent = false → ¬ Satisfiable dm (elOntology axs)) ∧
      (h.consistent = true →
        Satisfiable dm (elOntology axs) ∧
        (∀ c, c ∈ h.unsatisfiable ↔ c ∈ namedClasses ∧ Entails dm (elOntology axs) [.subClassOf (.named c) (.named nothing)]) ∧
        (∀ a b, (a, b) ∈ h.subsumptions ↔
          a ∈ namedClasses ∧ b ∈ namedClasses ∧ Entails dm (elOntology axs) [.subClassOf (.named a) (.named b)])) := by
    cases hfast : FastEL.classifyFastELToHierarchy axs namedClasses with
    | some h0 =>
      rw [hfast] at hel; simp only [Option.some.injEq] at hel; subst hel
      exact FastEL.classifyFastELToHierarchy_sound_complete (dm := dm) hfast
    | none =>
      rw [hfast] at hel
      exact classifyELSinglePass_sound_complete (dm := dm) hel
  obtain ⟨h1, h2⟩ := hEL
  refine ⟨fun hf hs => h1 hf (hsatEq.mp hs), fun ht => ?_⟩
  obtain ⟨hs, hu, hsub⟩ := h2 ht
  refine ⟨hsatEq.mpr hs, fun c => by rw [hu c, hentEq], fun a b => by rw [hsub a b, hentEq]⟩

end Sabrina.OWL2.FastClassification
