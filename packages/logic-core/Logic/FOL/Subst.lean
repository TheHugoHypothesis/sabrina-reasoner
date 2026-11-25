import Logic.FOL.Syntax
import Logic.FOL.Fresh

/-!
# Capture-avoiding substitution

Named binders shadow substitution. Conflicting binders are alpha-renamed to a
name fresh for all variables in the body and replacement. The examples are regression checks. The general semantic theorem is proved in
`packages/logic-core/Logic/FOL/SubstFull.lean`.
-/

namespace Logic.FOL

mutual
/-- Does `w` occur in the free variables of `t`, computed as a plain `Bool`? -/
def Term.hasFreeVar? [DecidableEq V] (w : V) : Term F V → Bool
  | Term.var x => decide (x == w)
  | Term.app _ ts => hasFreeVars? w ts

def hasFreeVars? [DecidableEq V] (w : V) : List (Term F V) → Bool
  | [] => false
  | t :: ts => (t.hasFreeVar? w) || (hasFreeVars? w ts)
end

mutual
/-- Rename all free occurrences of `y` to `z`. A binder for `y` stays as it is: the
occurrences it binds are not free occurrences of `y`. -/
def Term.rename [DecidableEq V] (y z : V) : Term F V → Term F V
  | Term.var x => if decide (x == y) then Term.var z else Term.var x
  | Term.app f args => Term.app f (renameTerms y z args)

def renameTerms [DecidableEq V] (y z : V) : List (Term F V) → List (Term F V)
  | [] => []
  | t :: ts => (t.rename y z) :: (renameTerms y z ts)
end

def Formula.rename [DecidableEq V] (y z : V) : Formula R F V → Formula R F V
  | Formula.tr => Formula.tr
  | Formula.fls => Formula.fls
  | Formula.eql a b => Formula.eql (a.rename y z) (b.rename y z)
  | Formula.rel r args => Formula.rel r (renameTerms y z args)
  | Formula.conj a b => Formula.conj (a.rename y z) (b.rename y z)
  | Formula.disj a b => Formula.disj (a.rename y z) (b.rename y z)
  | Formula.impl a b => Formula.impl (a.rename y z) (b.rename y z)
  | Formula.iffT a b => Formula.iffT (a.rename y z) (b.rename y z)
  | Formula.neg f => Formula.neg (f.rename y z)
  | Formula.allv w b => Formula.allv w (if decide (w == y) then b else (b.rename y z))
  | Formula.exv w b => Formula.exv w (if decide (w == y) then b else (b.rename y z))

mutual
/-- Substitution for terms: plain structural replacement, no binders to protect. -/
def Term.subst' [DecidableEq V] (p : V × Term F V) : Term F V → Term F V
  | Term.var y => if decide (y == p.1) then p.2 else Term.var y
  | Term.app f args => Term.app f (subst'List p args)

def subst'List [DecidableEq V] (p : V × Term F V) : List (Term F V) → List (Term F V)
  | [] => []
  | t :: ts => (Term.subst' p t) :: (subst'List p ts)
end

def Term.subst [DecidableEq V] (x : V) (s : Term F V) : Term F V → Term F V :=
  fun t => Term.subst' ⟨x, s⟩ t

/-- All variable names occurring in a formula, including binders. Fresh alpha-renaming
must avoid bound names as well as free names, or an inner binder can capture the
renamed occurrences. -/
def Formula.vars : Formula R F V → List V
  | .tr | .fls => []
  | .eql a b => a.freeVars ++ b.freeVars
  | .rel _ ts => freeVarsOfTerms ts
  | .conj a b | .disj a b | .impl a b | .iffT a b => a.vars ++ b.vars
  | .neg a => a.vars
  | .allv x a | .exv x a => x :: a.vars

/-- Fuel-bounded substitution. A binder for the target blocks substitution; a
conflicting binder is alpha-renamed before descending. The public entry point gives
more fuel than the formula's depth. -/
def substFuel [DecidableEq V] [Fresh V] (x : V) (s : Term F V) : Nat → Formula R F V → Formula R F V
  | 0, φ => φ
  | n + 1, φ =>
    let go := substFuel x s n
    match φ with
    | .tr => .tr
    | .fls => .fls
    | .eql a b => .eql (Term.subst x s a) (Term.subst x s b)
    | .rel r ts => .rel r (subst'List (x, s) ts)
    | .conj a b => .conj (go a) (go b)
    | .disj a b => .disj (go a) (go b)
    | .impl a b => .impl (go a) (go b)
    | .iffT a b => .iffT (go a) (go b)
    | .neg a => .neg (go a)
    | .allv w b =>
        if w = x then .allv w b
        else if s.hasFreeVar? w then
          let z := Fresh.fresh (x :: w :: (s.freeVars ++ b.vars))
          .allv z (go (b.rename w z))
        else .allv w (go b)
    | .exv w b =>
        if w = x then .exv w b
        else if s.hasFreeVar? w then
          let z := Fresh.fresh (x :: w :: (s.freeVars ++ b.vars))
          .exv z (go (b.rename w z))
        else .exv w (go b)

/-- Formula depth, unchanged by renaming. -/
def Formula.depth : Formula R F V → Nat
  | .tr | .fls | .eql .. | .rel .. => 1
  | .conj a b | .disj a b | .impl a b | .iffT a b => max a.depth b.depth + 1
  | .neg a | .allv _ a | .exv _ a => a.depth + 1

/-- Capture-avoiding substitution for formulas. -/
def Formula.subst [DecidableEq V] [Fresh V] (x : V) (s : Term F V)
    (φ : Formula R F V) : Formula R F V := substFuel x s φ.depth φ

example : (Formula.allv 1 (Formula.rel 0 [Term.var 1, Term.var 0]) : Formula Nat Nat Nat).subst 0 (Term.var 1) =
    Formula.allv 2 (Formula.rel 0 [Term.var 2, Term.var 1]) := rfl

example : (Formula.allv 0 (Formula.rel 0 [Term.var 0]) : Formula Nat Nat Nat).subst 0 (Term.var 1) =
    Formula.allv 0 (Formula.rel 0 [Term.var 0]) := rfl

example : (Formula.allv 1 (Formula.allv 2 (Formula.rel 0 [Term.var 1, Term.var 0])) : Formula Nat Nat Nat).subst 0 (Term.var 1) =
    Formula.allv 3 (Formula.allv 2 (Formula.rel 0 [Term.var 3, Term.var 1])) := rfl

example : (Formula.eql (Term.var 0) (Term.var 2) : Formula Nat Nat Nat).subst 0 (Term.app 4 []) =
    Formula.eql (Term.app 4 []) (Term.var 2) := rfl

example : (Formula.fls : Formula Nat Nat Nat).rename 0 1 = Formula.fls := rfl

end Logic.FOL
