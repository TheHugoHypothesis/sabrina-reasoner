import Logic.FOL.Syntax

/-!
# Model-theoretic semantics

A structure gives a domain and an interpretation for every relation symbol and
function symbol. `satisfies` is the standard Tarskian valuation, defined with a
variable assignment (a total function `V → domain`) rather than a finite map: the
syntax has *named* variables, so an assignment is a function, and the valuation
only looks up the finitely many variables that occur.

Relation symbols are interpreted as predicates on *lists* of domain elements; the
arity discipline (a symbol is only ever applied to its declared arity) is stated
separately, because the same structure type serves both the axiom symbols
(arities 1–3) and the model file's symbols, and CLIF itself does not carry arity
information.

`Entails` and `Satisfiable` quantify over all domains and structures. These are
the statements the rest of the project is about:

* **Consistency**: `Satisfiable bfoAxioms` — the 379 CLIF axioms have a model.
* **Soundness**: anything derivable from the axioms satisfies
  `Entails (bfoAxioms, a) a`.
-/

namespace Logic.FOL

/-- A first-order structure over relation symbols `R`, function symbols `F`, and
variable type `V`. -/
structure Structure (R F V : Type) where
  univ : Type
  rel  : R → List univ → Bool
  fapp : F → List univ → univ

/-- The domain type of `s`, uncurried. -/
abbrev Elem (s : Structure R F V) := s.univ

/-- Evaluate a term under an assignment. -/
def Term.eval (s : Structure R F V) (σ : V → Elem s) : Term F V → Elem s
  | Term.var x => σ x
  | Term.app f ts => s.fapp f (ts.map (·.eval s σ))

/-- Tarskian satisfaction. -/
def satisfies [DecidableEq V] (s : Structure R F V) (σ : V → Elem s) : Formula R F V → Prop
  | Formula.tr => True
  | Formula.fls => False
  | Formula.eql a b => a.eval s σ = b.eval s σ
  | Formula.rel r args => s.rel r (args.map (·.eval s σ))
  | Formula.conj a b => satisfies s σ a ∧ satisfies s σ b
  | Formula.disj a b => satisfies s σ a ∨ satisfies s σ b
  | Formula.impl a b => ¬ satisfies s σ a ∨ satisfies s σ b
  | Formula.iffT a b => satisfies s σ a ↔ satisfies s σ b
  | Formula.neg f => ¬ satisfies s σ f
  | Formula.allv x b => ∀ d : Elem s, satisfies s (fun w => if w = x then d else σ w) b
  | Formula.exv x b => ∃ d : Elem s, satisfies s (fun w => if w = x then d else σ w) b

/-- Universal validity relative to a theory: every structure satisfying every
formula in `Γ` also satisfies `φ`. -/
def Entails [DecidableEq V] (Γ : List (Formula R F V)) (φ : Formula R F V) : Prop :=
  ∀ (s : Structure R F V) (σ : V → Elem s), (∀ a ∈ Γ, satisfies s σ a) → satisfies s σ φ

/-- Satisfiability of a theory. -/
def Satisfiable [DecidableEq V] (Γ : List (Formula R F V)) : Prop :=
  ∃ (s : Structure R F V) (σ : V → Elem s), ∀ a ∈ Γ, satisfies s σ a

/-! The elementary soundness lemmas below are the shape of every verification
argument in this project: a derived formula is valid in exactly the structures
where its premises are. -/

/-- Conjunction introduction: if `φ` and `ψ` follow from `Γ`, so does `φ ∧ ψ`. -/
theorem entails_conj [DecidableEq V] (Γ : List (Formula R F V)) (a b : Formula R F V)
    (ha : Entails Γ a) (hb : Entails Γ b) : Entails Γ (a.conj b) := by
  intro s σ hγ
  exact ⟨ha s σ hγ, hb s σ hγ⟩

/-- Modus ponens: `φ → ψ` and `φ` give `ψ`. -/
theorem entails_mp [DecidableEq V] (Γ : List (Formula R F V)) (a b : Formula R F V)
    (himp : Entails Γ (a.impl b)) (ha : Entails Γ a) : Entails Γ b := by
  intro s σ hγ
  cases himp s σ hγ with
  | inl hna => exact False.elim (hna (ha s σ hγ))
  | inr hb => exact hb

/-- `false` is not valid: in any structure it is false under every assignment. -/
theorem not_entails_fls : ¬ Entails ([] : List (Formula Nat Nat Nat)) Formula.fls := by
  intro h
  let s : Structure Nat Nat Nat := ⟨Bool, fun _ _ => true, fun _ _ => false⟩
  exact (h s (fun _ => false) (by simp)).elim

end Logic.FOL
