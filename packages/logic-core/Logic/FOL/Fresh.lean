import Logic.FOL.Syntax

/-!
# Fresh variable names

Capture-avoiding substitution needs a name outside a given set, with a proof that it is
outside. Numbers give that cheaply: the fresh name is one above the largest name in use,
so membership is refuted by arithmetic rather than by string reasoning.

Both `Nat` and `String` have fresh-name instances. A finite `Fin n` supply cannot
promise a name outside every finite list.
-/

namespace Logic.FOL

/-- Fresh-name supply: `fresh used` is a variable name outside `used`. -/
class Fresh (V : Type) where
  fresh : List V → V
  fresh_notMem : ∀ (used : List V) (y : V), y ∈ used → fresh used ≠ y

/-- A left fold of `max` never goes below its seed. -/
theorem foldl_max_ge_init (init : Nat) (as : List Nat) :
    init ≤ List.foldl (fun a b => max a b) init as := by
  induction as generalizing init with
  | nil => exact Nat.le_refl init
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left init a) (ih (max init a))

/-- Every element of a list is at most the left fold of `max` from `init`. -/
theorem foldl_max_ge (init : Nat) (as : List Nat) (x : Nat) (hx : x ∈ as) :
    x ≤ List.foldl (fun a b => max a b) init as := by
  induction as generalizing init x with
  | nil =>
      simp at hx
  | cons a as ih =>
      simp only [List.mem_cons] at hx
      cases hx with
      | inl =>
          subst x
          exact Nat.le_trans (Nat.le_max_right init a) (foldl_max_ge_init (max init a) as)
      | inr h' =>
          exact ih (max init a) x h'

instance : Fresh Nat where
  fresh used := used.foldl (fun acc x => max acc x) 0 + 1
  fresh_notMem used y hy := by
    have h := foldl_max_ge 0 used y hy
    omega

/-- Strings have an infinite supply: use a string longer than every used name. -/
instance : Fresh String where
  fresh used := String.ofList (List.replicate
    ((used.map String.length).foldl (fun acc x => max acc x) 0 + 1) 'x')
  fresh_notMem used y hy := by
    have hmem : y.length ∈ used.map String.length := List.mem_map.mpr ⟨y, hy, rfl⟩
    have hmax := foldl_max_ge 0 (used.map String.length) y.length hmem
    intro he
    have hlen := congrArg String.length he
    simp only [String.length_ofList, List.length_replicate] at hlen
    omega

end Logic.FOL
