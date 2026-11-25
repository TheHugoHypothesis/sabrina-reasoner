import Sabrina.OWL2.SROIQD.Termination.SourceImportConformance

/-! Exact four-way query entailment (`ENTAILED`, `REFUTED`, `SENTENCE_INDEPENDENT`,
`INCONSISTENT_ONTOLOGY`) over the full wider datatype and built-in property
fragment, for both `datatypeMap` and Dedekind-cut `realDatatypeMap`.

Every supported OWL 2 DL query axiom without anonymous individuals (`SubClassOf`,
`EquivalentClasses`, `DisjointClasses`, `ClassAssertion`,
`(Negative)ObjectPropertyAssertion`, `(Negative)DataPropertyAssertion`,
`SameIndividual`, `DifferentIndividuals`) has an exact semantic negation axiom
using `owl:topObjectProperty` existential witnesses (requiring no fresh
individual names and preserving `HasKey` semantics identically). Four-way
classification then reduces directly to consistency calls on
`decideRealOntology?` / `decideWithWiderDataRanges?`. -/

namespace Sabrina.OWL2.SROIQD.Termination.ExactQuery

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.WellFormed
open Sabrina.ALC (InclusionVerdict)
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.XMLLiteral
open Sabrina.OWL2.SROIQD.Termination.SourceImport

/-! ### 1. Parametric four-way verdict specification -/

/-- Semantic meaning of an `InclusionVerdict` for query `qAx` against ontology
`o` over an arbitrary datatype map `dm`. Coincides definitionally with
`Normalize.queryVerdictClaim` when `dm = datatypeMap`. -/
def queryVerdictClaimWith (dm : DatatypeMap) (o : Ontology) (qAx : Axiom) :
    InclusionVerdict → Prop
  | .entailed => Satisfiable dm o ∧ Entails dm o [qAx]
  | .refuted => Satisfiable dm o ∧ ¬ Satisfiable dm (qAx :: o)
  | .independent => ¬ Entails dm o [qAx] ∧ Satisfiable dm (qAx :: o)
  | .inconsistent => ¬ Satisfiable dm o

theorem queryVerdictClaimWith_std_iff (o : Ontology) (qAx : Axiom) (v : InclusionVerdict) :
    queryVerdictClaimWith datatypeMap o qAx v ↔ Normalize.queryVerdictClaim o qAx v := by
  cases v <;> exact Iff.rfl

/-! ### 2. Anonymous-individual freedom for query axioms -/

def isNamedIndividual : Individual → Bool
  | .named _ => true
  | .anonymous _ _ => false

def hasNoAnonIndsClassExpr : ClassExpr → Bool
  | .named _ => true
  | .complement c => hasNoAnonIndsClassExpr c
  | .intersection a b | .union a b => hasNoAnonIndsClassExpr a && hasNoAnonIndsClassExpr b
  | .oneOf inds => inds.all isNamedIndividual
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c =>
    hasNoAnonIndsClassExpr c
  | .objectValue _ a => isNamedIndividual a
  | .objectSelf _ => true
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _
  | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => true

private theorem dataHolds_withAnonymous {dm : DatatypeMap} (i : Interpretation dm)
    (assign : String → String → i.Object) (y : i.Data) (d : DataRange) :
    dataHolds (i.withAnonymous assign) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => exact Iff.rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ia ib => exact and_congr ia ib
  | union _ _ ia ib => exact or_congr ia ib

private theorem classHolds_withAnonymous_oneOf {dm : DatatypeMap} (i : Interpretation dm)
    (assign : String → String → i.Object) (x : i.Object) {inds : List Individual}
    (h : inds.all isNamedIndividual = true) :
    (∃ a ∈ inds, (i.withAnonymous assign).individuals a = x) ↔
      ∃ a ∈ inds, i.individuals a = x := by
  have hall := List.all_eq_true.mp h
  constructor
  · rintro ⟨a, ha, heq⟩
    cases a with
    | named _ => exact ⟨_, ha, heq⟩
    | anonymous _ _ => cases hall _ ha
  · rintro ⟨a, ha, heq⟩
    cases a with
    | named _ => exact ⟨_, ha, heq⟩
    | anonymous _ _ => cases hall _ ha

private theorem classHolds_withAnonymous_of_noAnon {dm : DatatypeMap} (i : Interpretation dm)
    (assign : String → String → i.Object) (x : i.Object) {c : ClassExpr}
    (h : hasNoAnonIndsClassExpr c = true) :
    classHolds (i.withAnonymous assign) x c ↔ classHolds i x c := by
  induction c generalizing x with
  | named _ => exact Iff.rfl
  | complement c ih => exact not_congr (ih x h)
  | intersection a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    exact and_congr (iha x ha) (ihb x hb)
  | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    exact or_congr (iha x ha) (ihb x hb)
  | oneOf inds =>
    exact classHolds_withAnonymous_oneOf i assign x h
  | objectSome r c ih =>
    exact exists_congr fun y => and_congr Iff.rfl (ih y h)
  | objectAll r c ih =>
    exact forall_congr' fun y => imp_congr Iff.rfl (ih y h)
  | objectValue r a =>
    cases a with
    | named _ => exact Iff.rfl
    | anonymous _ _ => cases h
  | objectSelf _ => exact Iff.rfl
  | objectMin n r c ih =>
    simp only [classHolds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y h))))
  | objectMax n r c ih =>
    simp only [classHolds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y h)))))
  | objectExact n r c ih =>
    simp only [classHolds]
    exact and_congr
      (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y h)))))
      (not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y h))))))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withAnonymous i assign y d)
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withAnonymous i assign y d)
  | dataValue _ _ => exact Iff.rfl
  | dataMin n dp d =>
    simp only [classHolds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous i assign y d))))
  | dataMax n dp d =>
    simp only [classHolds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous i assign y d)))))
  | dataExact n dp d =>
    simp only [classHolds]
    exact and_congr
      (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous i assign y d)))))
      (not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous i assign y d))))))

/-! ### 3. Exact semantic negation for all 10 OWL 2 DL query axiom forms -/

/-- Expresses `∃ x, classHolds i x e` as a standard OWL 2 DL GCI using
`owl:topObjectProperty` (introducing no fresh individual names). -/
def existsWitnessAxiom (e : ClassExpr) : Axiom :=
  .subClassOf (.named thing) (.objectSome (.named topObjectProperty) e)

private theorem existsWitnessAxiom_holds_iff {dm : DatatypeMap} (i : Interpretation dm)
    (e : ClassExpr) :
    axiomHolds i (existsWitnessAxiom e) ↔ ∃ x, classHolds i x e := by
  simp only [existsWitnessAxiom, axiomHolds, classHolds, objectHolds, i.thingExt, i.topObjectExt,
    true_and, true_implies]
  exact ⟨fun h => i.objectNonempty.elim h, fun h _ => h⟩

/-- Construct an exact semantic negation axiom for every supported query axiom
form (requiring no anonymous individuals in the query). -/
def negateQueryAxiom : Axiom → Option Axiom
  | .subClassOf a b =>
    if hasNoAnonIndsClassExpr a && hasNoAnonIndsClassExpr b then
      some (existsWitnessAxiom (.intersection a (.complement b)))
    else none
  | .equivalentClasses [a, b] =>
    if hasNoAnonIndsClassExpr a && hasNoAnonIndsClassExpr b then
      some (existsWitnessAxiom
        (.union (.intersection a (.complement b)) (.intersection b (.complement a))))
    else none
  | .disjointClasses [a, b] =>
    if hasNoAnonIndsClassExpr a && hasNoAnonIndsClassExpr b then
      some (existsWitnessAxiom (.intersection a b))
    else none
  | .classAssertion c (.named a) =>
    if hasNoAnonIndsClassExpr c then
      some (.classAssertion (.complement c) (.named a))
    else none
  | .objectAssertion r (.named a) (.named b) =>
    some (.negativeObjectAssertion r (.named a) (.named b))
  | .negativeObjectAssertion r (.named a) (.named b) =>
    some (.objectAssertion r (.named a) (.named b))
  | .dataAssertion dp (.named a) l =>
    some (.negativeDataAssertion dp (.named a) l)
  | .negativeDataAssertion dp (.named a) l =>
    some (.dataAssertion dp (.named a) l)
  | .sameIndividuals [.named a, .named b] =>
    some (.differentIndividuals [.named a, .named b])
  | .differentIndividuals [.named a, .named b] =>
    some (.sameIndividuals [.named a, .named b])
  | _ => none

theorem negateQueryAxiom_spec {dm : DatatypeMap} (i : Interpretation dm)
    {qAx negAx : Axiom} (h : negateQueryAxiom qAx = some negAx) :
    (axiomHolds i negAx ↔ ¬ axiomHolds i qAx) ∧
    (∀ assign, axiomHolds (i.withAnonymous assign) qAx ↔ axiomHolds i qAx) ∧
    (∀ assign, axiomHolds (i.withAnonymous assign) negAx ↔ axiomHolds i negAx) := by
  classical
  cases qAx with
  | subClassOf a b =>
    simp only [negateQueryAxiom] at h
    split at h
    · rename_i hno
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hno
      cases h
      refine ⟨?_, ?_, ?_⟩
      · rw [existsWitnessAxiom_holds_iff]
        simp only [axiomHolds, classHolds]
        constructor
        · rintro ⟨x, hxa, hnb⟩ hall
          exact hnb (hall x hxa)
        · intro hnot
          apply Classical.byContradiction
          intro hnoEx
          apply hnot
          intro x hxa
          exact Classical.byContradiction fun hnb => hnoEx ⟨x, hxa, hnb⟩
      · intro assign
        simp only [axiomHolds]
        exact forall_congr' fun x => imp_congr
          (classHolds_withAnonymous_of_noAnon i assign x ha)
          (classHolds_withAnonymous_of_noAnon i assign x hb)
      · intro assign
        simp only [existsWitnessAxiom_holds_iff, classHolds]
        exact exists_congr fun x => and_congr
          (classHolds_withAnonymous_of_noAnon i assign x ha)
          (not_congr (classHolds_withAnonymous_of_noAnon i assign x hb))
    · cases h
  | equivalentClasses cs =>
    rcases cs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [negateQueryAxiom] at h
    any_goals cases h
    split at h
    · rename_i hno
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hno
      cases h
      have hEquiv (j : Interpretation dm) :
          axiomHolds j (.equivalentClasses [a, b]) ↔ ∀ x, classHolds j x a ↔ classHolds j x b := by
        simp only [axiomHolds, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hEq x
          exact hEq a (Or.inl rfl) b (Or.inr rfl) x
        · intro hAll c1 hc1 c2 hc2 x
          rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
          · exact Iff.rfl
          · exact hAll x
          · exact (hAll x).symm
          · exact Iff.rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [existsWitnessAxiom_holds_iff, hEquiv i]
        simp only [classHolds]
        constructor
        · rintro ⟨x, ⟨hxa, hnb⟩ | ⟨hxb, hna⟩⟩ hall
          · exact hnb ((hall x).mp hxa)
          · exact hna ((hall x).mpr hxb)
        · intro hnot
          apply Classical.byContradiction
          intro hnoEx
          apply hnot
          intro x
          constructor
          · intro hxa
            exact Classical.byContradiction fun hnb => hnoEx ⟨x, Or.inl ⟨hxa, hnb⟩⟩
          · intro hxb
            exact Classical.byContradiction fun hna => hnoEx ⟨x, Or.inr ⟨hxb, hna⟩⟩
      · intro assign
        rw [hEquiv, hEquiv]
        exact forall_congr' fun x => iff_congr
          (classHolds_withAnonymous_of_noAnon i assign x ha)
          (classHolds_withAnonymous_of_noAnon i assign x hb)
      · intro assign
        simp only [existsWitnessAxiom_holds_iff, classHolds]
        exact exists_congr fun x => or_congr
          (and_congr (classHolds_withAnonymous_of_noAnon i assign x ha)
            (not_congr (classHolds_withAnonymous_of_noAnon i assign x hb)))
          (and_congr (classHolds_withAnonymous_of_noAnon i assign x hb)
            (not_congr (classHolds_withAnonymous_of_noAnon i assign x ha)))
    · cases h
  | disjointClasses cs =>
    rcases cs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [negateQueryAxiom] at h
    any_goals cases h
    split at h
    · rename_i hno
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hno
      cases h
      have hDisj (j : Interpretation dm) :
          axiomHolds j (.disjointClasses [a, b]) ↔ ∀ x, ¬ (classHolds j x a ∧ classHolds j x b) := by
        simp [axiomHolds]
      refine ⟨?_, ?_, ?_⟩
      · rw [existsWitnessAxiom_holds_iff, hDisj i]
        simp only [classHolds]
        constructor
        · rintro ⟨x, hxa, hxb⟩ hall; exact hall x ⟨hxa, hxb⟩
        · intro hnot
          apply Classical.byContradiction
          intro hnoEx
          apply hnot
          intro x ⟨hxa, hxb⟩
          exact hnoEx ⟨x, hxa, hxb⟩
      · intro assign
        rw [hDisj, hDisj]
        exact forall_congr' fun x => not_congr (and_congr
          (classHolds_withAnonymous_of_noAnon i assign x ha)
          (classHolds_withAnonymous_of_noAnon i assign x hb))
      · intro assign
        simp only [existsWitnessAxiom_holds_iff, classHolds]
        exact exists_congr fun x => and_congr
          (classHolds_withAnonymous_of_noAnon i assign x ha)
          (classHolds_withAnonymous_of_noAnon i assign x hb)
    · cases h
  | classAssertion c ind =>
    cases ind with
    | anonymous _ _ => simp [negateQueryAxiom] at h
    | named a =>
      simp only [negateQueryAxiom] at h
      split at h
      · rename_i hc
        cases h
        refine ⟨Iff.rfl, fun assign => ?_, fun assign => ?_⟩
        · exact classHolds_withAnonymous_of_noAnon i assign (i.individuals (.named a)) hc
        · exact not_congr (classHolds_withAnonymous_of_noAnon i assign (i.individuals (.named a)) hc)
      · cases h
  | objectAssertion r ind1 ind2 =>
    cases ind1 with | anonymous _ _ => simp [negateQueryAxiom] at h | named a =>
    cases ind2 with | anonymous _ _ => simp [negateQueryAxiom] at h | named b =>
    cases h
    refine ⟨Iff.rfl, fun _ => ?_, fun _ => ?_⟩
    all_goals cases r <;> exact Iff.rfl
  | negativeObjectAssertion r ind1 ind2 =>
    cases ind1 with | anonymous _ _ => simp [negateQueryAxiom] at h | named a =>
    cases ind2 with | anonymous _ _ => simp [negateQueryAxiom] at h | named b =>
    cases h
    refine ⟨Classical.not_not.symm, fun _ => ?_, fun _ => ?_⟩
    all_goals cases r <;> exact Iff.rfl
  | dataAssertion dp ind l =>
    cases ind with | anonymous _ _ => simp [negateQueryAxiom] at h | named a =>
    cases h
    exact ⟨Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | negativeDataAssertion dp ind l =>
    cases ind with | anonymous _ _ => simp [negateQueryAxiom] at h | named a =>
    cases h
    exact ⟨Classical.not_not.symm, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | sameIndividuals inds =>
    rcases inds with _ | ⟨ind1, _ | ⟨ind2, _ | _⟩⟩ <;> simp only [negateQueryAxiom] at h
    any_goals cases h
    cases ind1 with | anonymous _ _ => simp at h | named a =>
    cases ind2 with | anonymous _ _ => simp at h | named b =>
    cases h
    have hSame (j : Interpretation dm) :
        axiomHolds j (.sameIndividuals [.named a, .named b]) ↔
          j.individuals (.named a) = j.individuals (.named b) := by
      simp only [axiomHolds, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun h => h _ (Or.inl rfl) _ (Or.inr rfl), fun heq u hu v hv => by
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · rfl
        · exact heq
        · exact heq.symm
        · rfl⟩
    have hDiff (j : Interpretation dm) :
        axiomHolds j (.differentIndividuals [.named a, .named b]) ↔
          j.individuals (.named a) ≠ j.individuals (.named b) := by
      simp [axiomHolds]
    refine ⟨?_, fun _ => by rw [hSame, hSame]; exact Iff.rfl,
      fun _ => by rw [hDiff, hDiff]; exact Iff.rfl⟩
    rw [hDiff, hSame]
  | differentIndividuals inds =>
    rcases inds with _ | ⟨ind1, _ | ⟨ind2, _ | _⟩⟩ <;> simp only [negateQueryAxiom] at h
    any_goals cases h
    cases ind1 with | anonymous _ _ => simp at h | named a =>
    cases ind2 with | anonymous _ _ => simp at h | named b =>
    cases h
    have hSame (j : Interpretation dm) :
        axiomHolds j (.sameIndividuals [.named a, .named b]) ↔
          j.individuals (.named a) = j.individuals (.named b) := by
      simp only [axiomHolds, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun h => h _ (Or.inl rfl) _ (Or.inr rfl), fun heq u hu v hv => by
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · rfl
        · exact heq
        · exact heq.symm
        · rfl⟩
    have hDiff (j : Interpretation dm) :
        axiomHolds j (.differentIndividuals [.named a, .named b]) ↔
          j.individuals (.named a) ≠ j.individuals (.named b) := by
      simp [axiomHolds]
    refine ⟨?_, fun _ => by rw [hDiff, hDiff]; exact Iff.rfl,
      fun _ => by rw [hSame, hSame]; exact Iff.rfl⟩
    rw [hSame, hDiff]
    exact Classical.not_not.symm
  | _ => simp [negateQueryAxiom] at h

theorem counterexample_sat_iff {dm : DatatypeMap} (o : Ontology) {qAx negAx : Axiom}
    (h : negateQueryAxiom qAx = some negAx) :
    Satisfiable dm (negAx :: o) ↔ ¬ Entails dm o [qAx] := by
  classical
  have hModSingle (i : Interpretation dm) : models i [qAx] ↔ axiomHolds i qAx := by
    have hno := (negateQueryAxiom_spec i h).2.1
    constructor
    · rintro ⟨assign, hsat⟩
      exact (hno assign).mp (hsat qAx (List.mem_cons_self ..))
    · intro hax
      obtain ⟨x₀⟩ := i.objectNonempty
      refine ⟨fun _ _ => x₀, fun a ha => ?_⟩
      simp only [List.mem_singleton] at ha
      subst ha
      exact (hno _).mpr hax
  have hSatCons (i : Interpretation dm) : models i (negAx :: o) ↔ models i o ∧ ¬ axiomHolds i qAx := by
    have ⟨hneg, _, hnoNeg⟩ := negateQueryAxiom_spec i h
    constructor
    · rintro ⟨assign, hsat⟩
      exact ⟨⟨assign, fun a ha => hsat a (List.mem_cons_of_mem _ ha)⟩,
        hneg.mp ((hnoNeg assign).mp (hsat negAx (List.mem_cons_self ..)))⟩
    · rintro ⟨⟨assign, hsat⟩, hnotQ⟩
      refine ⟨assign, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact (hnoNeg assign).mpr (hneg.mpr hnotQ)
      · exact hsat a ha'
  constructor
  · rintro ⟨i, hm⟩ hent
    obtain ⟨hmo, hnotQ⟩ := (hSatCons i).mp hm
    exact hnotQ ((hModSingle i).mp (hent i hmo))
  · intro hnotEnt
    apply Classical.byContradiction
    intro hno
    apply hnotEnt
    intro i hmo
    exact (hModSingle i).mpr (Classical.byContradiction fun hnotQ =>
      hno ⟨i, (hSatCons i).mpr ⟨hmo, hnotQ⟩⟩)

/-! ### 4. Generic four-way verdict classification from any exact consistency solver -/

def classifyQueryWith (solve : Ontology → Option Bool) (o : Ontology) (qAx : Axiom) :
    Option InclusionVerdict :=
  (negateQueryAxiom qAx).bind fun negAx =>
    (solve o).bind fun base =>
      if !base then some .inconsistent
      else
        match solve (negAx :: o) with
        | some false => some .entailed
        | some true =>
          match solve (qAx :: o) with
          | some false => some .refuted
          | some true => some .independent
          | none => none
        | none =>
          match solve (qAx :: o) with
          | some false => some .refuted
          | _ => none

theorem classifyQueryWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : classifyQueryWith solve o qAx = some v) :
    queryVerdictClaimWith dm o qAx v := by
  simp only [classifyQueryWith, Option.bind_eq_some_iff] at h
  obtain ⟨negAx, hneg, base, hbase, hrest⟩ := h
  cases base with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest
    subst hrest
    exact fun hsat => Bool.noConfusion ((hsolve hbase).mpr hsat)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrest
    have hBaseSat : Satisfiable dm o := (hsolve hbase).mp rfl
    cases hcnt : solve (negAx :: o) with
    | some bc =>
      cases bc with
      | false =>
        simp only [hcnt, Option.some.injEq] at hrest
        subst hrest
        refine ⟨hBaseSat, Classical.byContradiction fun hnotEnt => ?_⟩
        have hsatNeg : Satisfiable dm (negAx :: o) := (counterexample_sat_iff o hneg).mpr hnotEnt
        exact Bool.noConfusion ((hsolve hcnt).mpr hsatNeg)
      | true =>
        simp only [hcnt] at hrest
        have hNotEnt : ¬ Entails dm o [qAx] :=
          (counterexample_sat_iff o hneg).mp ((hsolve hcnt).mp rfl)
        cases hinc : solve (qAx :: o) with
        | none => simp [hinc] at hrest
        | some bi =>
          cases bi with
          | false =>
            simp only [hinc, Option.some.injEq] at hrest
            subst hrest
            exact ⟨hBaseSat, fun hsat => Bool.noConfusion ((hsolve hinc).mpr hsat)⟩
          | true =>
            simp only [hinc, Option.some.injEq] at hrest
            subst hrest
            exact ⟨hNotEnt, (hsolve hinc).mp rfl⟩
    | none =>
      simp only [hcnt] at hrest
      cases hinc : solve (qAx :: o) with
      | none => simp [hinc] at hrest
      | some bi =>
        cases bi with
        | false =>
          simp only [hinc, Option.some.injEq] at hrest
          subst hrest
          exact ⟨hBaseSat, fun hsat => Bool.noConfusion ((hsolve hinc).mpr hsat)⟩
        | true => simp [hinc] at hrest

/-! ### 5. Typed & resolved-source query adapters for `realDatatypeMap` and `datatypeMap` -/

def decideRealQuery? (o : Ontology) (qAx : Axiom) : Option InclusionVerdict :=
  classifyQueryWith decideRealOntology? o qAx

theorem decideRealQuery_sound {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideRealQuery? o qAx = some v) :
    queryVerdictClaimWith realDatatypeMap o qAx v :=
  classifyQueryWith_sound decideRealOntology_iff h

def decideWiderQuery? (o : Ontology) (qAx : Axiom) : Option InclusionVerdict :=
  classifyQueryWith decideWithWiderDataRanges? o qAx

theorem decideWiderQuery_sound {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideWiderQuery? o qAx = some v) :
    Normalize.queryVerdictClaim o qAx v :=
  (queryVerdictClaimWith_std_iff o qAx v).mp (classifyQueryWith_sound decideWithWiderDataRanges_iff h)

/-- Total verified parser for any standalone query axiom using the root
document's prefixes (and optional additional prefix declarations). -/
def parseSourceQuery (prefixes : PrefixMap) (input : String) : Option Axiom := do
  let tokens ← tokenizeTotal input
  let (prefixes, rest) ← parsePrefixDeclsTotal (tokens.length + 1) prefixes tokens
  match parseAxiomTotal "query" prefixes (rest.length + 1) rest with
  | some (some ax, []) => some ax
  | _ => none

/-- Decide any supported query axiom over a resolved finite `.ofn` import
closure under the Dedekind-cut `realDatatypeMap` semantics. -/
def decideRealSourceQuery? (rootOFN query : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Axiom × InclusionVerdict) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    (parseSourceQuery closure.root.prefixes query).bind fun qAx =>
      if checkWellFormedOntology closure.flattened &&
         checkWellFormedOntology (qAx :: closure.flattened) &&
         ontologyXMLLiteralsValid true (qAx :: closure.flattened) then
        (decideRealQuery? closure.flattened qAx).map fun v => (closure, qAx, v)
      else none

theorem decideRealSourceQuery_sound
    {rootOFN query : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideRealSourceQuery? rootOFN query library = some (closure, qAx, v)) :
    resolveSourceImports rootOFN library = some closure ∧
    WellFormedOntology closure.flattened ∧
    WellFormedOntology (qAx :: closure.flattened) ∧
    ontologyXMLLiteralsValid true (qAx :: closure.flattened) = true ∧
    parseSourceQuery closure.root.prefixes query = some qAx ∧
    queryVerdictClaimWith realDatatypeMap closure.flattened qAx v := by
  simp only [decideRealSourceQuery?, Option.bind_eq_some_iff] at h
  obtain ⟨cl, hcl, q, hparse, hrest⟩ := h
  split at hrest
  · rename_i hgate
    obtain ⟨⟨hwf1, hwf2⟩, hxml⟩ := Bool.and_eq_true_iff.mp hgate |>.imp Bool.and_eq_true_iff.mp id
    obtain ⟨v', hv', hpair⟩ := Option.map_eq_some_iff.mp hrest
    cases hpair
    exact ⟨hcl, (checkWellFormedOntology_iff _).mp hwf1, (checkWellFormedOntology_iff _).mp hwf2,
      hxml, hparse, decideRealQuery_sound hv'⟩
  · contradiction

/-- Decide any supported query axiom over a resolved finite `.ofn` import
closure under the standard `datatypeMap` semantics. -/
def decideWiderSourceQuery? (rootOFN query : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Axiom × InclusionVerdict) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    (parseSourceQuery closure.root.prefixes query).bind fun qAx =>
      if checkWellFormedOntology closure.flattened &&
         checkWellFormedOntology (qAx :: closure.flattened) &&
         ontologyXMLLiteralsValid true (qAx :: closure.flattened) then
        (decideWiderQuery? closure.flattened qAx).map fun v => (closure, qAx, v)
      else none

theorem decideWiderSourceQuery_sound
    {rootOFN query : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideWiderSourceQuery? rootOFN query library = some (closure, qAx, v)) :
    resolveSourceImports rootOFN library = some closure ∧
    WellFormedOntology closure.flattened ∧
    WellFormedOntology (qAx :: closure.flattened) ∧
    ontologyXMLLiteralsValid true (qAx :: closure.flattened) = true ∧
    parseSourceQuery closure.root.prefixes query = some qAx ∧
    Normalize.queryVerdictClaim closure.flattened qAx v := by
  simp only [decideWiderSourceQuery?, Option.bind_eq_some_iff] at h
  obtain ⟨cl, hcl, q, hparse, hrest⟩ := h
  split at hrest
  · rename_i hgate
    obtain ⟨⟨hwf1, hwf2⟩, hxml⟩ := Bool.and_eq_true_iff.mp hgate |>.imp Bool.and_eq_true_iff.mp id
    obtain ⟨v', hv', hpair⟩ := Option.map_eq_some_iff.mp hrest
    cases hpair
    exact ⟨hcl, (checkWellFormedOntology_iff _).mp hwf1, (checkWellFormedOntology_iff _).mp hwf2,
      hxml, hparse, decideWiderQuery_sound hv'⟩
  · contradiction

#print axioms negateQueryAxiom_spec
#print axioms counterexample_sat_iff
#print axioms classifyQueryWith_sound
#print axioms decideRealQuery_sound
#print axioms decideWiderQuery_sound
#print axioms decideRealSourceQuery_sound
#print axioms decideWiderSourceQuery_sound

end Sabrina.OWL2.SROIQD.Termination.ExactQuery
