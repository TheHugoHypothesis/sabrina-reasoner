import Logic.Proof.Derivation

/-! Positive uses of the eigenvariable rules, and semantic counterexamples showing
that each freshness side condition is necessary: dropping it would let the rule
derive a formula that is not a semantic consequence. The unsound variants are
never constructors; they are only tested semantically. -/
namespace Logic.Proof
open Logic.FOL

/-- `∀x.body ⊢ ∀x.body`, through universal introduction on a fresh eigenvariable. -/
theorem allIntro_example [DecidableEq V] [Fresh V] (x : V) (body : Formula R F V) :
    Derives [.allv x body] (.allv x body) :=
  Derives.allIntro fun y _ _ =>
    Derives.allElim (.var y) (Derives.assumption (by simp))

/-- Existential elimination: from `∃x.body` conclude `∃x.body` by opening it. -/
theorem existsElim_example [DecidableEq V] [Fresh V] (x : V) (body : Formula R F V) :
    Derives [.exv x body] (.exv x body) :=
  Derives.existsElim (x := x) (body := body)
    (Derives.assumption (φ := .exv x body) (by simp)) fun y _ _ _ =>
    Derives.existsIntro (.var y)
      (Derives.assumption (φ := body.subst x (.var y)) (by simp))

/-- A one-predicate test structure on `Bool`: `P` holds exactly of `true`. -/
def boolP : Structure Unit Empty Nat where
  univ := Bool
  rel := fun _ l => decide (l = [true])
  fapp := fun f _ => f.elim

private abbrev P (t : Term Empty Nat) : Formula Unit Empty Nat := .rel () [t]

/-- Universal introduction needs the eigenvariable to be absent from the context.
`P y ⊢ P y` holds (and is the `x := y` instance of `P x`), but with `y` free in the
undischarged premise `P y`, `∀x. P x` is not a consequence. -/
theorem allIntro_needs_fresh_context :
    ¬ FreshIn (1 : Nat) [P (.var 1)] ∧
    Entails [P (.var 1)] (P (.var 1)) ∧
    ¬ Entails [P (.var 1)] (.allv 0 (P (.var 0))) := by
  refine ⟨?_, fun _ _ h => h _ (by simp), ?_⟩
  · intro h
    exact h (P (.var 1)) (by simp)
      (by simp [Formula.freeVars, Term.freeVars, freeVarsOfTerms])
  · intro h
    have := h boolP (fun _ => true) (by
      intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      simp [satisfies, boolP, Term.eval]) false
    simp [satisfies, boolP, Term.eval] at this

/-- Universal introduction needs the eigenvariable to be absent from the
conclusion: `⊢ y = y` but `⊬ ∀x. x = y`. -/
theorem allIntro_needs_fresh_conclusion :
    (1 : Nat) ∈ (Formula.allv 0 (Formula.eql (Term.var 0) (Term.var 1) :
        Formula Unit Empty Nat)).freeVars ∧
    Entails [] (Formula.eql (Term.var 1) (Term.var 1) : Formula Unit Empty Nat) ∧
    ¬ Entails [] (Formula.allv 0 (Formula.eql (Term.var 0) (Term.var 1) :
        Formula Unit Empty Nat)) := by
  refine ⟨by simp [Formula.freeVars, Term.freeVars], fun _ _ _ => rfl, ?_⟩
  intro h
  have := h boolP (fun _ => true) (by simp) false
  simp [satisfies, boolP, Term.eval] at this

/-- Existential elimination needs the eigenvariable to be absent from the
conclusion: `P y, ∃x. P x ⊢ P y` is derivable by assumption, but `∃x. P x ⊬ P y`. -/
theorem existsElim_needs_fresh_conclusion :
    (1 : Nat) ∈ (P (.var 1)).freeVars ∧
    ¬ Entails [.exv 0 (P (.var 0))] (P (.var 1)) := by
  refine ⟨by simp [Formula.freeVars, Term.freeVars, freeVarsOfTerms], ?_⟩
  intro h
  have := h boolP (fun _ => false) (by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨true, by simp [satisfies, boolP, Term.eval]⟩)
  simp [satisfies, boolP, Term.eval] at this

end Logic.Proof
