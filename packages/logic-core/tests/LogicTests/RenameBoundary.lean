import Logic.FOL.SubstIdentity
import Logic.Proof.DecidableSyntax
import Logic.Proof.Renaming

/-! A concrete capture-avoidance regression explaining why raw syntactic
substitution composition cannot replace proof-level alpha reasoning. -/
namespace Logic.Proof
open Logic.FOL

private def nestedBody : Formula Nat Nat Nat :=
  .allv 1 (.rel 0 [.var 0, .var 1])

theorem nested_instantiation_not_syntactically_compositional :
    ((nestedBody.subst 0 (.var 1)).subst 1 (.var 2)) ≠
      nestedBody.subst 0 (.var 2) := by decide

theorem nested_instantiation_same_semantics
    (s : Structure Nat Nat Nat) (σ : Nat → Elem s) :
    satisfies s σ ((nestedBody.subst 0 (.var 1)).subst 1 (.var 2)) ↔
      satisfies s σ (nestedBody.subst 0 (.var 2)) := by
  rw [satisfies_subst, satisfies_subst, satisfies_subst]
  apply satisfies_agree
  intro v hv
  simp [nestedBody, Formula.freeVars, Term.freeVars, freeVarsOfTerms] at hv
  subst v
  simp [Term.eval]

/-- The unequal named ASTs are equal after syntactic binder abstraction. -/
theorem nested_instantiation_alpha :
    ((nestedBody.subst 0 (.var 1)).subst 1 (.var 2)).Alpha
      (nestedBody.subst 0 (.var 2)) := by
  intro σ
  rw [Formula.bindingTree_subst, Formula.bindingTree_subst, Formula.bindingTree_subst]
  apply Formula.bindingTree_agree
  intro v hv
  simp [nestedBody, Formula.freeVars, Term.freeVars, freeVarsOfTerms] at hv
  subst v
  simp [Term.expand]

/-- The earlier composition obstruction is now bridged by actual derivations. -/
theorem nested_instantiation_interderivable (Γ : List (Formula Nat Nat Nat)) :
    Derives Γ ((nestedBody.subst 0 (.var 1)).subst 1 (.var 2)) ↔
      Derives Γ (nestedBody.subst 0 (.var 2)) :=
  alpha_derives nested_instantiation_alpha Γ

end Logic.Proof
