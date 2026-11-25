import Logic.FOL.SubstFull

/-! Syntactic identity laws for capture-avoiding substitution. -/
namespace Logic.FOL

mutual
theorem Term.subst_self [DecidableEq V] (x : V) (t : Term F V) :
    Term.subst x (.var x) t = t := by
  cases t with
  | var y => by_cases h : y = x <;> simp [Term.subst, Term.subst', h]
  | app f ts =>
    change Term.app f (subst'List (x, .var x) ts) = Term.app f ts
    rw [substList_self]

theorem substList_self [DecidableEq V] (x : V) (ts : List (Term F V)) :
    subst'List (x, .var x) ts = ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have ht := Term.subst_self x t
    change Term.subst' (x, .var x) t = t at ht
    simp [subst'List, ht, substList_self]
end

theorem substFuel_self [DecidableEq V] [Fresh V]
    (x : V) (n : Nat) (φ : Formula R F V) :
    substFuel x (.var x) n φ = φ := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    cases φ with
    | tr | fls => rfl
    | eql a b =>
      simp only [substFuel]
      rw [Term.subst_self x a, Term.subst_self x b]
    | rel r args => simp [substFuel, substList_self]
    | conj a b | disj a b | impl a b | iffT a b => simp [substFuel, ih]
    | neg a => simp [substFuel, ih]
    | allv y body | exv y body =>
      by_cases h : y = x
      · subst y; simp [substFuel]
      · simp [substFuel, h, Ne.symm h, Term.hasFreeVar?, ih]

theorem Formula.subst_self [DecidableEq V] [Fresh V]
    (x : V) (φ : Formula R F V) : φ.subst x (.var x) = φ :=
  substFuel_self x φ.depth φ

end Logic.FOL
