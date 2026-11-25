import Logic.Proof.Equivalence

/-! Capture-sensitive checks of the unrestricted reverse bridge. The chosen
outer eigenvariable coincides with an inner binder, forcing alpha conversion. -/
namespace Logic.Proof
open Logic.FOL

private def nestedReflexivity : Formula Nat Nat Nat :=
  .allv 1 (.eql (.var 0) (.var 0))

theorem nested_all_certificate_checked :
    check [] (.allv 0 nestedReflexivity) (.allIntro 1 (.allIntro 4 .eqRefl)) = true := by
  simp [check, nestedReflexivity, Formula.subst, substFuel, Formula.depth,
    Formula.rename, Term.rename, Term.subst, Term.subst', Term.hasFreeVar?,
    Formula.freeVars, Term.freeVars, Formula.vars, Fresh.fresh]

theorem nested_all_original_derivation : Derives [] (.allv 0 nestedReflexivity) :=
  check_original_derives _ _ _ nested_all_certificate_checked

theorem nested_exists_certificate_checked :
    check [.exv 0 nestedReflexivity] (.exv 0 nestedReflexivity)
      (.existsElim 0 1 nestedReflexivity .assumption (.existsIntro (.var 1) .assumption)) = true := by
  simp [check, nestedReflexivity, Formula.subst, substFuel, Formula.depth,
    Formula.rename, Term.rename, Term.subst, Term.subst', Term.hasFreeVar?,
    Formula.freeVars, Term.freeVars, Formula.vars, Fresh.fresh]

theorem nested_exists_original_derivation :
    Derives [.exv 0 nestedReflexivity] (.exv 0 nestedReflexivity) :=
  check_original_derives _ _ _ nested_exists_certificate_checked

/-- Binding-tree comparison must reject capture of a previously free variable. -/
theorem alpha_rejects_capture :
    ¬ (Formula.allv 0 (.rel 0 [.var 0, .var 1]) : Formula Nat Nat Nat).Alpha
      (.allv 1 (.rel 0 [.var 1, .var 1])) := by
  intro h
  have hb := congrFun (BindingTree.allv.inj (h Term.var)) (.var 2)
  simp [Formula.bindingTree, expandTerms, Term.expand] at hb

/-- Alpha comparison retains syntactic logical constructors, rather than
identifying all semantically equivalent propositions. -/
theorem alpha_rejects_connective_change :
    ¬ (Formula.tr : Formula Nat Nat Nat).Alpha (.conj .tr .tr) := by
  intro h
  have hb := h Term.var
  cases hb

end Logic.Proof
