import Logic.Proof.Certificate

namespace Logic.Proof
open Logic.FOL
set_option linter.unusedSimpArgs false

private def p (n : Nat) : Formula String String Nat := .rel "p" [.var n]

def identityCertificate : Certificate String String Nat := .impIntro .assumption

theorem identity_certificate_checked :
    check [] (.impl (p 0) (p 0)) identityCertificate = true := by
  simp [check, identityCertificate, p, termDecEq, termListDecEq]

theorem identity_certificate_sound : Entails [] (.impl (p 0) (p 0)) :=
  check_sound identityCertificate [] _ identity_certificate_checked

def quantifiedCertificate : Certificate String String Nat :=
  .allIntro 1 (.allElim 0 (p 0) (.var 1) .assumption)

theorem quantified_certificate_checked :
    check [.allv 0 (p 0)] (.allv 0 (p 0)) quantifiedCertificate = true := by
  simp [check, quantifiedCertificate, p, termDecEq, termListDecEq,
    Formula.subst, substFuel, Formula.depth, Term.subst', Formula.freeVars,
    Term.freeVars, freeVarsOfTerms]

/-- An eigenvariable free in the context must be rejected. -/
theorem invalid_eigenvariable_rejected :
    check [p 1] (.allv 0 (p 0)) (.allIntro 1 .assumption) = false := by decide

/-- A valid proof tree is rejected for a different conclusion. -/
theorem wrong_conclusion_rejected :
    check [] (.impl (p 0) (p 1)) identityCertificate = false := by
  simp [check, identityCertificate, p, termDecEq, termListDecEq]

def universalExistentialCertificate : Certificate String String Nat :=
  .existsIntro (.var 2) (.allElim 0 (p 0) (.var 2) .assumption)

theorem universal_existential_checked :
    check [.allv 0 (p 0)] (.exv 0 (p 0)) universalExistentialCertificate = true := by
  simp [check, universalExistentialCertificate, p, Formula.subst, substFuel,
    Formula.depth, Term.subst']

def identityExistentialCertificate : Certificate String String Nat :=
  .existsElim 0 1 (p 0) .assumption (.existsIntro (.var 1) .assumption)

theorem existential_elimination_checked :
    check [.exv 0 (p 0)] (.exv 0 (p 0)) identityExistentialCertificate = true := by
  simp [check, identityExistentialCertificate, p, Formula.subst, substFuel,
    Formula.depth, Term.subst', Formula.freeVars, Term.freeVars, freeVarsOfTerms]

theorem existential_bad_conclusion_rejected :
    check [.exv 0 (p 0)] (p 1) (.existsElim 0 1 (p 0) .assumption .assumption) = false := by
  simp [check, p, Formula.freeVars, Term.freeVars, freeVarsOfTerms]

theorem false_equality_rejected :
    check [] (.eql (.var 0) (.var 1) : Formula String String Nat) .eqRefl = false := by
  simp [check, termDecEq]

def equalityUnderBinderCertificate : Certificate Nat Nat Nat :=
  .eqSubst 99 (.allv 0 (.rel 0 [.var 0, .var 99])) (.var 1) (.var 2)
    .assumption .assumption

theorem equality_under_binder_checked :
    check [(.eql (.var 1) (.var 2) : Formula Nat Nat Nat),
           .allv 0 (.rel 0 [.var 0, .var 1])]
      (.allv 0 (.rel 0 [.var 0, .var 2])) equalityUnderBinderCertificate = true := by
  simp [check, equalityUnderBinderCertificate, Formula.subst, substFuel,
    Formula.depth, subst'List, Term.subst', Term.hasFreeVar?, Term.freeVars]

/-- Capturing variable 0 without renaming must not be accepted as substitution. -/
theorem capture_wrong_result_rejected :
    check [(.eql (.var 1) (.var 0) : Formula Nat Nat Nat),
           .allv 0 (.rel 0 [.var 0, .var 1])]
      (.allv 0 (.rel 0 [.var 0, .var 0]))
      (.eqSubst 99 (.allv 0 (.rel 0 [.var 0, .var 99])) (.var 1) (.var 0)
        .assumption .assumption) = false := by
  simp [check, Formula.subst, substFuel, Formula.depth, subst'List, Term.subst',
    Term.hasFreeVar?, Term.freeVars, freeVarsOfTerms, Formula.vars, Fresh.fresh]

end Logic.Proof
