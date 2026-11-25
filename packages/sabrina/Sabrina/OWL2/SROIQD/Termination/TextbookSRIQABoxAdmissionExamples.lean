import Sabrina.OWL2.SROIQD.Termination.HierarchyExamples
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQABoxExamples

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

/-- The reference regularity check admits this hierarchy. The universal
decision path checks its models directly. -/
def converseRecursionABox : KnowledgeBase where
  tboxRBox := { hierarchy := converseRecursion }
  abox := [.concept .top "a"]

theorem converseRecursionABox_wellFormed : converseRecursionABox.WellFormed := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact converseRecursion_regular
  · simp [converseRecursionABox]
  · simp [converseRecursionABox]
  · intro a ha
    have heq := List.mem_singleton.mp ha
    subst a
    trivial

theorem converseRecursionABox_rank_rejected : converseRecursionABox.decideRanked? = none := by
  decide

theorem converseRecursionABox_not_rank_admitted : ¬ converseRecursionABox.RankAdmitted := by
  intro h
  have hadm := (kb_decide_ranked_admitted_iff converseRecursionABox).mpr h
  rw [converseRecursionABox_rank_rejected] at hadm
  contradiction

theorem converseRecursionABox_admitted : converseRecursionABox.Admitted :=
  Or.inr (by decide)

theorem converseRecursionABox_decides_sat : converseRecursionABox.decide? = some true := by
  decide

theorem converseRecursionABox_sat : converseRecursionABox.Sat :=
  (kb_decide_sat_iff converseRecursionABox_admitted).mp converseRecursionABox_decides_sat

private def reciprocalEdges : KnowledgeBase :=
  { converseRecursionABox with
    abox := [.role (.named "r") "b" "a", .role (.named "r") "b" "b", .different "a" "b"] }

/-- The two asserted edges force `r(a, b)` under the converse chain. -/
private def forbiddenReciprocalEdge : KnowledgeBase :=
  { reciprocalEdges with abox := .concept (.all (.named "r") .bottom) "a" :: reciprocalEdges.abox }

theorem forbiddenReciprocalEdge_unsat : ¬ forbiddenReciprocalEdge.Sat := by
  rintro ⟨m, hm⟩
  have hba := hm.2 (.role (.named "r") "b" "a") (by simp [forbiddenReciprocalEdge, reciprocalEdges])
  have hbb := hm.2 (.role (.named "r") "b" "b") (by simp [forbiddenReciprocalEdge, reciprocalEdges])
  have hnone := hm.2 (.concept (.all (.named "r") .bottom) "a") (by simp [forbiddenReciprocalEdge])
  let rule : Inclusion := ⟨.inverse "r", [.inverse "r"], "r"⟩
  have hchain : m.toModel.path rule.body (m.individuals "a") (m.individuals "b") :=
    .cons hba (.cons hbb (.nil _))
  exact hnone (m.individuals "b")
    (hm.1.2.1 rule (by simp [forbiddenReciprocalEdge, reciprocalEdges, converseRecursionABox,
      converseRecursion, rule]) _ _ hchain)

theorem forbiddenReciprocalEdge_decides_unsat : forbiddenReciprocalEdge.decide? = some false :=
  (kb_decide_unsat_iff (Or.inr (by decide))).mpr forbiddenReciprocalEdge_unsat

-- A rank failure is distinguishable from a checked contradiction.
#guard reciprocalEdges.decideRanked? == none
#guard reciprocalEdges.decide? == some true
#guard forbiddenReciprocalEdge.decide? == some false

-- An existential in a GCI antecedent occurs at negative polarity.
private def forcedOutgoingClass : KnowledgeBase where
  tboxRBox := { reciprocalEdges.tboxRBox with
    tbox := [(.some (.named "r") .top, .atom "Outgoing")] }
  abox := .concept (.neg (.atom "Outgoing")) "a" :: reciprocalEdges.abox

#guard forcedOutgoingClass.isUniversal
#guard forcedOutgoingClass.decide? == some false

-- An existential in a positive ABox assertion may need an extra witness.
private def needsExistential : KnowledgeBase :=
  { reciprocalEdges with abox := .concept (.some (.named "r") .top) "a" :: reciprocalEdges.abox }

#guard !needsExistential.isUniversal
#guard needsExistential.decide? == none

#print axioms converseRecursionABox_wellFormed
#print axioms converseRecursionABox_rank_rejected
#print axioms converseRecursionABox_not_rank_admitted
#print axioms converseRecursionABox_decides_sat
#print axioms converseRecursionABox_sat
#print axioms forbiddenReciprocalEdge_decides_unsat

end Sabrina.OWL2.SROIQD.TextbookSRIQ
