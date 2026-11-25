import Logic.FOL.Models

/-! A finite-domain evaluator with a correctness proof. The enumeration must
cover the structure's entire domain; computation alone is not the theorem. -/
namespace Logic.FOL

/-- Evaluate a formula against an explicitly enumerated finite domain. -/
def evalBool [DecidableEq V] (s : Structure R F V) [DecidableEq (Elem s)]
    (domain : List (Elem s)) (σ : V → Elem s) : Formula R F V → Bool
  | .tr => true
  | .fls => false
  | .eql a b => decide (a.eval s σ = b.eval s σ)
  | .rel r args => s.rel r (args.map (·.eval s σ))
  | .conj a b => evalBool s domain σ a && evalBool s domain σ b
  | .disj a b => evalBool s domain σ a || evalBool s domain σ b
  | .impl a b => !evalBool s domain σ a || evalBool s domain σ b
  | .iffT a b => evalBool s domain σ a == evalBool s domain σ b
  | .neg a => !evalBool s domain σ a
  | .allv x a => domain.all (fun d => evalBool s domain (fun w => if w = x then d else σ w) a)
  | .exv x a => domain.any (fun d => evalBool s domain (fun w => if w = x then d else σ w) a)

/-- The evaluator is correct when the supplied domain list is exhaustive. -/
theorem evalBool_correct [DecidableEq V]
    (s : Structure R F V) [DecidableEq (Elem s)] (domain : List (Elem s)) (cover : ∀ d, d ∈ domain)
    (φ : Formula R F V) (σ : V → Elem s) :
    evalBool s domain σ φ = true ↔ satisfies s σ φ := by
  induction φ generalizing σ with
  | tr | fls | eql | rel => simp [evalBool, satisfies]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp [evalBool, satisfies, ← ia σ, ← ib σ]
  | neg a ia => simp [evalBool, satisfies, ← ia σ]
  | allv x a ia => simp [evalBool, satisfies, List.all_eq_true, cover, ia]
  | exv x a ia => simp [evalBool, satisfies, List.any_eq_true, cover, ia]

end Logic.FOL
