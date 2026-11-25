import Init.Data.List.Basic

/-!
# First-order syntax

The shape of the syntax is dictated by the CLIF axiomatization of BFO 2020
(`packages/bfo2020/specs/bfo-2020/21838-2/common-logic/*.cl`): *named* variables, relation symbols
of varying arity, function symbols, and equality.

Two design points matter later, so they are fixed here:

* **Symbols and variables are abstract types, not `String`.** A finite symbol encoding may make model evaluation more compact. `String` is used only by the
  parser and the CLIF printer. See `docs/notes/10-design-decisions.md` D10.
* **Named variables, not de Bruijn indices**, so that `print (parse s) = s` is a
  meaningful faithfulness test against the upstream CLIF text (D3).
-/

namespace Logic.FOL

/-- Terms: variables and function applications. -/
inductive Term (F V : Type) where
  | var : V → Term F V
  | app : F → List (Term F V) → Term F V
  deriving BEq, Repr

/-- Formulas. `iffT` and `impl` mirror CLIF's `iff` and `if`; `conj`/`disj` mirror
`and`/`or`; `neg` mirrors `not`. Constructor names avoid clashing with core names
so that pattern matching elaborates unambiguously. -/
inductive Formula (R F V : Type) where
  | tr
  | fls
  | eql : Term F V → Term F V → Formula R F V
  | rel : R → List (Term F V) → Formula R F V
  | conj : Formula R F V → Formula R F V → Formula R F V
  | disj : Formula R F V → Formula R F V → Formula R F V
  | impl : Formula R F V → Formula R F V → Formula R F V
  | iffT : Formula R F V → Formula R F V → Formula R F V
  | neg : Formula R F V → Formula R F V
  | allv : V → Formula R F V → Formula R F V
  | exv : V → Formula R F V → Formula R F V
  deriving BEq, Repr

mutual
def Term.freeVars : Term F V → List V
  | Term.var x => [x]
  | Term.app _ args => freeVarsOfTerms args

def freeVarsOfTerms : List (Term F V) → List V
  | [] => []
  | t :: ts => Term.freeVars t ++ freeVarsOfTerms ts
end

/-- Free variables, duplicates permitted. `filter` rather than `erase`: `List.erase`
removes only the first occurrence, which would leave a variable "free" when it occurs
more than once — a bug that would silently make axioms fail the sentence check. -/
def Formula.freeVars [DecidableEq V] : Formula R F V → List V
  | Formula.tr | Formula.fls => []
  | Formula.eql a b => Term.freeVars a ++ Term.freeVars b
  | Formula.rel _ args => freeVarsOfTerms args
  | Formula.conj a b | Formula.disj a b | Formula.impl a b | Formula.iffT a b =>
      Formula.freeVars a ++ Formula.freeVars b
  | Formula.neg f => Formula.freeVars f
  | Formula.allv x b | Formula.exv x b => (Formula.freeVars b).filter (fun w => w != x)

/-- A sentence has no free variables. Every CLIF axiom is one. -/
def Formula.isSentence [DecidableEq V] (φ : Formula R F V) : Bool := φ.freeVars.isEmpty

/-- The quantifier variables at the top of the formula, in source order: keys a
generated axiom against the upstream `(forall (a b t) …)` prefix. -/
def Formula.binders : Formula R F V → List V
  | Formula.allv x b => x :: Formula.binders b
  | Formula.exv x b => x :: Formula.binders b
  | _ => []

/-- A CLIF-shaped sample, with `Nat`-coded symbols and variables:
`∀ a t. instance-of a independent-continuant t → continuant-part-of a a t` (`[mcd-1]`).

Universals are *constants* in CLIF (`Term.app c []`), not variables — they are terms
that denote classes, and conflating them with variables would make the sentence
appear to have free variables. See `docs/notes/30-gap-list.md` G7. -/
def mcd_1 : Formula Nat Nat Nat :=
  Formula.allv 0 (Formula.allv 1
    (Formula.impl
      (Formula.rel 2 [Term.var 0, Term.app 4 [], Term.var 1])
      (Formula.rel 3 [Term.var 0, Term.var 0, Term.var 1])))

/-! These two checks are kernel-checked: `decide` reduces both `Nat`- and `String`-coded
syntax on small formulas (verified in this toolchain). The binding constraint for
Stage 3 is combinatorial, not reduction — see `docs/notes/10-design-decisions.md` D10. -/
example : mcd_1.isSentence = true := by decide
example : mcd_1.binders = [0, 1] := by decide

end Logic.FOL
