import Sabrina.ALC.Search

namespace Sabrina.ALC

/-- Evidence for satisfiability of the counterexample and inclusion problems. -/
structure InclusionEvidence where
  counterexample : Certificate
  inclusion : Certificate

def searchInclusion (tbox : TBox) (q : Inclusion) : InclusionEvidence :=
  ⟨search tbox (.conj q.sub (.neg q.sup)), search (q :: tbox) .top⟩

def checkInclusion (tbox : TBox) (q : Inclusion) (e : InclusionEvidence) : Bool :=
  checkCertificate tbox (.conj q.sub (.neg q.sup)) e.counterexample &&
  checkCertificate (q :: tbox) .top e.inclusion

theorem searchInclusion_checked (tbox : TBox) (q : Inclusion) :
    checkInclusion tbox q (searchInclusion tbox q) = true := by
  simp [checkInclusion, searchInclusion, search_checked]

inductive InclusionVerdict where
  | entailed
  | refuted
  | independent
  | inconsistent
  deriving DecidableEq

def InclusionEvidence.verdict (e : InclusionEvidence) : InclusionVerdict :=
  match e.counterexample, e.inclusion with
  | .refutation _, .model _ => .entailed
  | .model _, .refutation _ => .refuted
  | .model _, .model _ => .independent
  | .refutation _, .refutation _ => .inconsistent

def InclusionVerdict.claim (tbox : TBox) (q : Inclusion) : InclusionVerdict → Prop
  | .entailed => Subsumes tbox q.sub q.sup ∧ Consistent tbox
  | .refuted => EntailsNegatedInclusion tbox q.sub q.sup ∧ Consistent tbox
  | .independent => ¬ Subsumes tbox q.sub q.sup ∧ ¬ EntailsNegatedInclusion tbox q.sub q.sup
  | .inconsistent => ¬ Consistent tbox

theorem checkInclusion_sound {tbox : TBox} {q : Inclusion} {e : InclusionEvidence}
    (h : checkInclusion tbox q e = true) : e.verdict.claim tbox q := by
  rcases e with ⟨counter, inclusion⟩
  simp only [checkInclusion, Bool.and_eq_true] at h
  have hc := checkCertificate_sound h.1
  have hi := checkCertificate_sound h.2
  cases counter <;> cases inclusion <;>
    simp only [certificateClaim] at hc hi <;>
    simp only [InclusionEvidence.verdict, InclusionVerdict.claim]
  · exact ⟨fun hs => (subsumes_iff tbox q.sub q.sup).mp hs hc,
      fun hn => (entailsNegatedInclusion_iff tbox q.sub q.sup).mp hn hi⟩
  · obtain ⟨i, hm, _⟩ := hc
    exact ⟨(entailsNegatedInclusion_iff tbox q.sub q.sup).mpr hi, ⟨i, hm⟩⟩
  · obtain ⟨i, hm, _⟩ := hi
    exact ⟨(subsumes_iff tbox q.sub q.sup).mpr hc, ⟨i, ((models_cons i q tbox).mp hm).2⟩⟩
  · intro hconsistent
    obtain ⟨i, hm, x, hx⟩ := (consistent_iff tbox).mp hconsistent
    have hs := (subsumes_iff tbox q.sub q.sup).mpr hc
    exact hi ⟨i, (models_cons i q tbox).mpr ⟨hs i hm, hm⟩, x, hx⟩

end Sabrina.ALC
