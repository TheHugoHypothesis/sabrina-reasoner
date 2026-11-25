import Logic.FOL.Syntax

/-! Computable structural equality for terms and formulas. -/
namespace Logic.FOL

mutual
def termDecEq [DecidableEq F] [DecidableEq V] (a b : Term F V) : Decidable (a = b) :=
  match a, b with
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .var _, .app _ _ => isFalse (by simp)
  | .app _ _, .var _ => isFalse (by simp)
  | .app f xs, .app g ys =>
    letI : Decidable (xs = ys) := termListDecEq xs ys
    decidable_of_iff (f = g ∧ xs = ys) (by simp)
termination_by sizeOf a

def termListDecEq [DecidableEq F] [DecidableEq V] (a b : List (Term F V)) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | x :: xs, y :: ys =>
    letI : Decidable (x = y) := termDecEq x y
    letI : Decidable (xs = ys) := termListDecEq xs ys
    decidable_of_iff (x = y ∧ xs = ys) (by simp)
termination_by sizeOf a
end

instance [DecidableEq F] [DecidableEq V] : DecidableEq (Term F V) := termDecEq
deriving instance DecidableEq for Formula

end Logic.FOL
