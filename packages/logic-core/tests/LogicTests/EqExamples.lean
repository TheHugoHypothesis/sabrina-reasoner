import Logic.Proof.Derivation

/-! Examples for the Leibniz rule `eqSubst`, including replacement below a binder
and a capture-avoidance check. -/
namespace Logic.Proof
open Logic.FOL

/-- Congruence for a unary predicate: `a = b, P a ⊢ P b`, with `P x` instantiated
at the fresh-looking variable `99` (assumed not to occur in `a`, `b`). -/
theorem eqSubst_rel_example :
    Derives [(Formula.eql (Term.var 1) (Term.var 2) : Formula Nat Nat Nat),
             Formula.rel 0 [Term.var 1]] (Formula.rel 0 [Term.var 2]) :=
  Derives.eqSubst (a := Term.var 1) (b := Term.var 2) 99
    (Formula.rel 0 [Term.var 99])
    (Derives.assumption (by simp))
    (Derives.assumption (by simp [Formula.subst, substFuel, Formula.depth, subst'List,
      Term.subst']))

/-- Replacement below a binder, derived with `eqSubst` itself:
`1 = 2, ∀x. R x 1 ⊢ ∀x. R x 2`, taking `φ := ∀x. R x 99`. -/
theorem eqSubst_below_binder_derivation :
    Derives [(Formula.eql (Term.var 1) (Term.var 2) : Formula Nat Nat Nat),
             Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 1])]
            (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 2])) := by
  have e1 : Formula.subst 99 (Term.var 1)
      (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 99]) : Formula Nat Nat Nat) =
      Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 1]) := rfl
  have e2 : Formula.subst 99 (Term.var 2)
      (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 99]) : Formula Nat Nat Nat) =
      Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 2]) := rfl
  have h := Derives.eqSubst (Γ := [(Formula.eql (Term.var 1) (Term.var 2) : Formula Nat Nat Nat),
             Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 1])])
    (a := Term.var 1) (b := Term.var 2) 99
    (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 99]))
    (Derives.assumption (by simp)) (by rw [e1]; exact Derives.assumption (by simp))
  rwa [e2] at h

/-- Replacement below a binder: `y = z, ∀x. R x y ⊨ ∀x. R x z` (semantic check). -/
theorem eqSubst_under_binder :
    Entails [(Formula.eql (Term.var 1) (Term.var 2) : Formula Nat Nat Nat),
             Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 1])]
            (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 2])) := by
  intro s σ hs d
  have h1 := hs (Formula.eql (Term.var 1) (Term.var 2)) (by simp)
  have h2 := hs (Formula.allv 0 (Formula.rel 0 [Term.var 0, Term.var 1])) (by simp) d
  simp [satisfies, Term.eval] at h1 h2 ⊢
  simpa [← h1] using h2

/-- Capture check: the bound name `1` differs from the free names `0`, `2`;
`x = w, ∀y. R y x ⊨ ∀y. R y w` keeps `x` free (no capture by `∀y`). -/
theorem eqSubst_capture_example :
    Entails [(Formula.eql (Term.var 0) (Term.var 2) : Formula Nat Nat Nat),
             Formula.allv 1 (Formula.rel 0 [Term.var 1, Term.var 0])]
            (Formula.allv 1 (Formula.rel 0 [Term.var 1, Term.var 2])) := by
  intro s σ hs d
  have h1 := hs (Formula.eql (Term.var 0) (Term.var 2)) (by simp)
  have h2 := hs (Formula.allv 1 (Formula.rel 0 [Term.var 1, Term.var 0])) (by simp) d
  simp [satisfies, Term.eval] at h1 h2 ⊢
  simpa [← h1] using h2

end Logic.Proof
