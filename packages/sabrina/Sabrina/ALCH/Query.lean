import Sabrina.ALC.Query
import Sabrina.ALCH.Reduction

namespace Sabrina.ALCH

open Sabrina.ALC

def Consistent (o : Ontology) : Prop := ∃ i : Interpretation, Models o i

def Subsumes (o : Ontology) (q : Inclusion) : Prop :=
  ∀ i : Interpretation, Models o i → ∀ x, holds i x q.sub → holds i x q.sup

def EntailsNegatedInclusion (o : Ontology) (q : Inclusion) : Prop :=
  ∀ i : Interpretation, Models o i → ¬ (∀ x, holds i x q.sub → holds i x q.sup)

private theorem forall_models_iff (o : Ontology) (P : Interpretation → Prop) :
    (∀ i : Interpretation, models i (o.tbox.map (translateInclusion (close o.hierarchy))) →
      P (liftRoles (close o.hierarchy) i)) ↔
    ∀ i : Interpretation, Models o i → P i := by
  constructor
  · intro h i hm
    have he := liftRoles_eq hm.2
    have hlift : Models o (liftRoles (close o.hierarchy) i) := by rwa [he]
    have hp := h i ((models_lift_iff o i).mpr hlift)
    rwa [he] at hp
  · intro h i hm
    exact h _ ((models_lift_iff o i).mp hm)

theorem consistent_compile_iff (o : Ontology) (q : Inclusion) :
    ALC.Consistent (compile o q).1 ↔ Consistent o := by
  rw [ALC.consistent_iff]
  change ALC.ConceptSat (o.tbox.map (translateInclusion (close o.hierarchy)))
    (translate (close o.hierarchy) .top) ↔ Consistent o
  rw [conceptSat_iff]
  constructor
  · rintro ⟨i, hm, _⟩
    exact ⟨i, hm⟩
  · rintro ⟨i, hm⟩
    obtain ⟨x⟩ := i.nonempty
    exact ⟨i, hm, x, trivial⟩

theorem subsumes_compile_iff (o : Ontology) (q : Inclusion) :
    ALC.Subsumes (compile o q).1 (compile o q).2.sub (compile o q).2.sup ↔ Subsumes o q := by
  simp only [ALC.Subsumes, compile, translateInclusion,
    holds_inclusion_translate (close o.hierarchy) _ q]
  exact forall_models_iff o (fun i => ∀ x, holds i x q.sub → holds i x q.sup)

theorem entailsNegatedInclusion_compile_iff (o : Ontology) (q : Inclusion) :
    ALC.EntailsNegatedInclusion (compile o q).1 (compile o q).2.sub (compile o q).2.sup ↔
      EntailsNegatedInclusion o q := by
  simp only [ALC.EntailsNegatedInclusion, compile, translateInclusion,
    holds_inclusion_translate (close o.hierarchy) _ q]
  exact forall_models_iff o (fun i => ¬ (∀ x, holds i x q.sub → holds i x q.sup))

def FiniteConceptSat (o : Ontology) (c : Concept) : Prop :=
  ∃ i : Interpretation, Models o i ∧
    (∃ carrier : List i.Domain, ∀ x, x ∈ carrier) ∧ ∃ x, holds i x c

theorem finite_model_property (o : Ontology) (c : Concept) (h : ConceptSat o c) :
    FiniteConceptSat o c := by
  obtain ⟨i, hm, hfinite, x, hx⟩ :=
    ALC.finite_model_property _ _ ((conceptSat_iff o c).mpr h)
  exact ⟨liftRoles (close o.hierarchy) i, (models_lift_iff o i).mp hm, hfinite, x,
    (holds_translate _ i x c).mp hx⟩

def verdictClaim (o : Ontology) (q : Inclusion) : InclusionVerdict → Prop
  | .entailed => Subsumes o q ∧ Consistent o
  | .refuted => EntailsNegatedInclusion o q ∧ Consistent o
  | .independent => ¬ Subsumes o q ∧ ¬ EntailsNegatedInclusion o q
  | .inconsistent => ¬ Consistent o

theorem verdictClaim_compile_iff (o : Ontology) (q : Inclusion) (v : InclusionVerdict) :
    v.claim (compile o q).1 (compile o q).2 ↔ verdictClaim o q v := by
  cases v <;> simp only [InclusionVerdict.claim, verdictClaim,
    consistent_compile_iff, subsumes_compile_iff, entailsNegatedInclusion_compile_iff]

def searchInclusion (o : Ontology) (q : Inclusion) : InclusionEvidence :=
  let compiled := compile o q
  ALC.searchInclusion compiled.1 compiled.2

def checkInclusion (o : Ontology) (q : Inclusion) (e : InclusionEvidence) : Bool :=
  let compiled := compile o q
  ALC.checkInclusion compiled.1 compiled.2 e

theorem searchInclusion_checked (o : Ontology) (q : Inclusion) :
    checkInclusion o q (searchInclusion o q) = true :=
  ALC.searchInclusion_checked (compile o q).1 (compile o q).2

theorem checkInclusion_sound {o : Ontology} {q : Inclusion} {e : InclusionEvidence}
    (h : checkInclusion o q e = true) : verdictClaim o q e.verdict :=
  (verdictClaim_compile_iff o q e.verdict).mp (ALC.checkInclusion_sound h)

/-- Total search returns the correct verdict for the original role hierarchy. -/
theorem searchInclusion_correct (o : Ontology) (q : Inclusion) :
    verdictClaim o q (searchInclusion o q).verdict :=
  checkInclusion_sound (searchInclusion_checked o q)

theorem searchInclusion_independent_iff (o : Ontology) (q : Inclusion) :
    (searchInclusion o q).verdict = .independent ↔
      ¬ Subsumes o q ∧ ¬ EntailsNegatedInclusion o q := by
  have hs := searchInclusion_correct o q
  constructor
  · intro h
    simpa only [h, verdictClaim] using hs
  · intro h
    cases hv : (searchInclusion o q).verdict with
    | entailed =>
      rw [hv, verdictClaim] at hs
      exact (h.1 hs.1).elim
    | refuted =>
      rw [hv, verdictClaim] at hs
      exact (h.2 hs.1).elim
    | independent => rfl
    | inconsistent =>
      rw [hv, verdictClaim] at hs
      exact (h.1 fun i hi => (hs ⟨i, hi⟩).elim).elim

end Sabrina.ALCH
