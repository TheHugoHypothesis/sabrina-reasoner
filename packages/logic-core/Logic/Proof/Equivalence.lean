import Logic.Proof.Renaming
import Logic.Proof.Certificate

/-! The certificate checker and both derivation relations prove the same sequents.
This is equivalence of proof systems, not completeness for semantic entailment. -/
namespace Logic.Proof
open Logic.FOL

/-- Every accepted certificate yields an original derivation, including both
chosen-eigenvariable rules. -/
theorem check_original_derives [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (cert : Certificate R F V) (Γ : List (Formula R F V)) (φ : Formula R F V)
    (h : check Γ φ cert = true) : Derives Γ φ :=
  finite_to_derivation (check_derives cert Γ φ h)

/-- An original derivation exists exactly when a finite certificate is accepted. -/
theorem derivation_iff_certificate [DecidableEq V] [Fresh V]
    [DecidableEq (Term F V)] [DecidableEq (Formula R F V)]
    (Γ : List (Formula R F V)) (φ : Formula R F V) :
    Derives Γ φ ↔ ∃ cert, check Γ φ cert = true :=
  derivation_iff_finite.trans (finite_iff_certificate Γ φ)

end Logic.Proof
