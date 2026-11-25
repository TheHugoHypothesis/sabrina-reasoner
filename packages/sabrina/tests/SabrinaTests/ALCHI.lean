import Sabrina.ALCHI.Query

namespace SabrinaTests.ALCHI

open Sabrina.ALC

private def rules : RoleTheory := Sabrina.ALCHI.inverseRules "r" "backR"
private def root : Concept := .some "r" (.neg (.some "backR" .top))

-- An r-successor cannot lack a predecessor when backR denotes the converse of r.
example : (match searchUnder rules [] root with | .refutation _ => true | .model _ => false) = true := by decide

-- Removing the inverse axiom invalidates the refutation for this same expression.
example : checkCertificateUnder [] [] root (searchUnder rules [] root) = false := by decide

end SabrinaTests.ALCHI
