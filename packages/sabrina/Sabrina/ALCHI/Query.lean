import Sabrina.ALC.Query

namespace Sabrina.ALCHI

open Sabrina.ALC

def Consistent (rules : RoleTheory) (tbox : TBox) : Prop :=
  ∃ i : Interpretation, modelsRoles i rules ∧ models i tbox

def Subsumes (rules : RoleTheory) (tbox : TBox) (q : Inclusion) : Prop :=
  ∀ i : Interpretation, modelsRoles i rules → models i tbox →
    ∀ x, holds i x q.sub → holds i x q.sup

def EntailsNegatedInclusion (rules : RoleTheory) (tbox : TBox) (q : Inclusion) : Prop :=
  ∀ i : Interpretation, modelsRoles i rules → models i tbox →
    ¬ (∀ x, holds i x q.sub → holds i x q.sup)

/-- An inverse declaration equates the named relation with the converse of another. -/
def inverseRules (r s : String) : RoleTheory :=
  [((r,false), (s,true)), ((s,true), (r,false))]

theorem models_inverseRules_iff (i : Interpretation) (r s : String) :
    modelsRoles i (inverseRules r s) ↔ ∀ x y, i.role r x y ↔ i.role s y x := by
  constructor
  · intro h x y
    exact ⟨h (r,false) (s,true) (by simp [inverseRules]) x y,
      h (s,true) (r,false) (by simp [inverseRules]) x y⟩
  · intro h a b hab x y
    simp only [inverseRules, List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with e | e <;> cases e
    · exact (h x y).mp
    · exact (h x y).mpr

theorem holds_some_inverse {i : Interpretation} {rules : RoleTheory} {r s : String}
    (hm : modelsRoles i rules) (h : ∀ rule ∈ inverseRules r s, rule ∈ rules)
    (x : i.Domain) (c : Concept) :
    holds i x (.some s c) ↔ ∃ y, i.role r y x ∧ holds i y c := by
  have hi := models_inverseRules_iff i r s |>.mp
    (fun a b hab => hm a b (h (a,b) hab))
  simp only [holds, hi]

private def counterRoot (q : Inclusion) : Concept := .conj q.sub (.neg q.sup)

def searchInclusion (rules : RoleTheory) (tbox : TBox) (q : Inclusion) : InclusionEvidence :=
  ⟨searchUnder rules tbox (counterRoot q), searchUnder rules (q :: tbox) .top⟩

def checkInclusion (rules : RoleTheory) (tbox : TBox) (q : Inclusion) (e : InclusionEvidence) : Bool :=
  checkCertificateUnder rules tbox (counterRoot q) e.counterexample &&
  checkCertificateUnder rules (q :: tbox) .top e.inclusion

theorem searchInclusion_checked (rules : RoleTheory) (tbox : TBox) (q : Inclusion) :
    checkInclusion rules tbox q (searchInclusion rules tbox q) = true := by
  simp [checkInclusion, searchInclusion, searchUnder_checked]

def verdictClaim (rules : RoleTheory) (tbox : TBox) (q : Inclusion) : InclusionVerdict → Prop
  | .entailed => Subsumes rules tbox q ∧ Consistent rules tbox
  | .refuted => EntailsNegatedInclusion rules tbox q ∧ Consistent rules tbox
  | .independent => ¬ Subsumes rules tbox q ∧ ¬ EntailsNegatedInclusion rules tbox q
  | .inconsistent => ¬ Consistent rules tbox

private theorem entails_of_no_counter {rules tbox q}
    (h : ¬ ConceptSatUnder rules tbox (counterRoot q)) : Subsumes rules tbox q := by
  classical
  intro i hr hm x hx
  exact Classical.byContradiction (fun hn => h ⟨i, hr, hm, x, hx, hn⟩)

theorem checkInclusion_sound {rules tbox q e}
    (h : checkInclusion rules tbox q e = true) : verdictClaim rules tbox q e.verdict := by
  rcases e with ⟨counter, inclusion⟩
  simp only [checkInclusion, Bool.and_eq_true] at h
  have hc := checkCertificateUnder_sound h.1
  have hi := checkCertificateUnder_sound h.2
  cases counter <;> cases inclusion <;>
    simp only [certificateClaimUnder] at hc hi <;>
    simp only [InclusionEvidence.verdict, verdictClaim]
  · obtain ⟨i, hr, hm, x, ha, hnb⟩ := hc
    obtain ⟨j, hjr, hjm, _⟩ := hi
    have ⟨hq, hj⟩ := (models_cons j q tbox).mp hjm
    exact ⟨fun hs => hnb (hs i hr hm x ha), fun hn => hn j hjr hj hq⟩
  · obtain ⟨i, hr, hm, _⟩ := hc
    refine ⟨?_, ⟨i, hr, hm⟩⟩
    intro j hjr hj hq
    obtain ⟨x⟩ := j.nonempty
    exact hi ⟨j, hjr, (models_cons j q tbox).mpr ⟨hq, hj⟩, x, trivial⟩
  · obtain ⟨i, hr, hm, _⟩ := hi
    exact ⟨entails_of_no_counter hc, ⟨i, hr, ((models_cons i q tbox).mp hm).2⟩⟩
  · rintro ⟨i, hr, hm⟩
    obtain ⟨x⟩ := i.nonempty
    exact hi ⟨i, hr, (models_cons i q tbox).mpr ⟨entails_of_no_counter hc i hr hm, hm⟩, x, trivial⟩

theorem searchInclusion_correct (rules : RoleTheory) (tbox : TBox) (q : Inclusion) :
    verdictClaim rules tbox q (searchInclusion rules tbox q).verdict :=
  checkInclusion_sound (searchInclusion_checked rules tbox q)

theorem searchInclusion_independent_iff (rules : RoleTheory) (tbox : TBox) (q : Inclusion) :
    (searchInclusion rules tbox q).verdict = .independent ↔
      ¬ Subsumes rules tbox q ∧ ¬ EntailsNegatedInclusion rules tbox q := by
  have hs := searchInclusion_correct rules tbox q
  constructor
  · intro h
    simpa only [h, verdictClaim] using hs
  · intro h
    cases hv : (searchInclusion rules tbox q).verdict with
    | entailed =>
      rw [hv, verdictClaim] at hs
      exact (h.1 hs.1).elim
    | refuted =>
      rw [hv, verdictClaim] at hs
      exact (h.2 hs.1).elim
    | independent => rfl
    | inconsistent =>
      rw [hv, verdictClaim] at hs
      exact (h.1 fun i hr hm => (hs ⟨i, hr, hm⟩).elim).elim

theorem finite_model_property (rules : RoleTheory) (tbox : TBox) (root : Concept)
    (hs : ConceptSatUnder rules tbox root) : FiniteConceptSatUnder rules tbox root := by
  have h := searchUnder_checked rules tbox root
  cases he : searchUnder rules tbox root with
  | model pool =>
    rw [he] at h
    exact checkModelUnder_finite_sound h
  | refutation rounds =>
    rw [he] at h
    exact (checkRefutationUnder_sound h hs).elim

end Sabrina.ALCHI
