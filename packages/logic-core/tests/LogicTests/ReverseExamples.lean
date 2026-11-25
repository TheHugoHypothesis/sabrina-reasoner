import Logic.Proof.ReverseFragment
import LogicTests.CertificateExamples

namespace Logic.Proof
open Logic.FOL

private def p (n : Nat) : Formula String String Nat := .rel "p" [.var n]

/-- The checked quantifier-instantiation certificate translates back to the
original relation without an eigenvariable-renaming assumption. -/
theorem original_from_checked_instantiation :
    Derives [.allv 0 (p 0)] (.exv 0 (p 0)) := by
  apply eigenFree_check_derives universalExistentialCertificate
  · exact universal_existential_checked
  · rfl

/-- A tree using universal introduction is outside the proved fragment. -/
example : eigenFree quantifiedCertificate = false := rfl

end Logic.Proof
