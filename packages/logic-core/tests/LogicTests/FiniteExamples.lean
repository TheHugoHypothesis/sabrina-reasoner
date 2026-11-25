import Logic.Proof.Finite
import LogicTests.EigenExamples

namespace Logic.Proof
open Logic.FOL

private def p (n : Nat) : Formula Unit Empty Nat := .rel () [.var n]

/-- A concrete finite proof with the chosen eigenvariable 1. -/
theorem finite_universal_identity :
    FiniteDerives [.allv 0 (p 0)] (.allv 0 (p 0)) := by
  apply FiniteDerives.allIntro 1
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    simp [p, Formula.freeVars, Term.freeVars, freeVarsOfTerms]
  · simp [p, Formula.freeVars, Term.freeVars, freeVarsOfTerms]
  · exact FiniteDerives.allElim (.var 1) (FiniteDerives.assumption (by simp))

/-- The same eigenvariable is forbidden when it occurs in a premise. -/
theorem finite_eigen_rejects_open_context : ¬ FreshIn 1 [p 1] := by
  intro h
  exact h (p 1) (by simp) (by simp [p, Formula.freeVars, Term.freeVars, freeVarsOfTerms])

theorem finite_universal_identity_sound :
    Entails [.allv 0 (p 0)] (.allv 0 (p 0)) :=
  finite_sound finite_universal_identity

end Logic.Proof
