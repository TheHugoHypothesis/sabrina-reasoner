import Logic.FOL.RenameSemantics

namespace Logic.FOL

/-- Fuel-bounded substitution preserves satisfaction when the fuel covers the
formula depth. This includes alpha-renaming at conflicting binders. -/
theorem satisfies_substFuel [DecidableEq V] [Fresh V]
    (s : Structure R F V) (σ : V → Elem s) (x : V) (replacement : Term F V)
    (n : Nat) (φ : Formula R F V) (hn : φ.depth ≤ n) :
    satisfies s σ (substFuel x replacement n φ) ↔
      satisfies s (fun y => if y = x then replacement.eval s σ else σ y) φ := by
  induction n generalizing φ σ with
  | zero => cases φ <;> simp [Formula.depth] at hn
  | succ n ih =>
    cases φ with
    | tr | fls => simp [substFuel, satisfies]
    | eql a b => simp [substFuel, satisfies, Term.eval_subst]
    | rel r args => simp [substFuel, satisfies, eval_subst_list]
    | conj a b | disj a b | impl a b | iffT a b =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      have ha : a.depth ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hb : b.depth ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
      simp only [substFuel, satisfies]
      rw [ih σ a ha, ih σ b hb]
    | neg a =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      simp only [substFuel, satisfies]
      rw [ih σ a hn]
    | allv w a | exv w a =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      by_cases hwx : w = x
      · subst w
        simp only [substFuel, ite_true, satisfies]
        have eqfun (d : Elem s) :
            (fun v => if v = x then d else σ v) =
            (fun v => if v = x then d else if v = x then replacement.eval s σ else σ v) := by
          funext v; by_cases h : v = x <;> simp [h]
        simp only [← eqfun]
      · by_cases hfree : replacement.hasFreeVar? w = true
        · let z := Fresh.fresh (x :: w :: (replacement.freeVars ++ a.vars))
          have hz : z ∉ x :: w :: (replacement.freeVars ++ a.vars) := by
            intro h
            exact Fresh.fresh_notMem _ z h rfl
          simp only [List.mem_cons, List.mem_append, not_or] at hz
          have heval (d : Elem s) :
              replacement.eval s (fun v => if v = z then d else σ v) = replacement.eval s σ := by
            apply Term.eval_agree
            intro v hv
            have hvz : v ≠ z := by intro he; subst v; exact hz.2.2.1 hv
            simp [hvz]
          have equiv (d : Elem s) :
              satisfies s (fun v => if v = z then d else σ v)
                  (substFuel x replacement n (a.rename w z)) ↔
              satisfies s (fun v => if v = w then d else if v = x then replacement.eval s σ else σ v) a := by
            have hd : (a.rename w z).depth ≤ n := by simpa [Formula.rename_depth] using hn
            calc
              _ ↔ satisfies s (fun v => if v = x then replacement.eval s (fun v => if v = z then d else σ v)
                                        else if v = z then d else σ v) (a.rename w z) := ih _ _ hd
              _ ↔ satisfies s (fun v => if v = w then
                    (if z = x then replacement.eval s (fun v => if v = z then d else σ v) else d)
                    else if v = x then replacement.eval s (fun v => if v = z then d else σ v)
                    else if v = z then d else σ v) a := by
                simpa using (satisfies_rename s a w z hz.2.2.2
                  (fun v => if v = x then replacement.eval s (fun v => if v = z then d else σ v)
                            else if v = z then d else σ v))
              _ ↔ _ := by
                apply satisfies_agree
                intro v hv
                have hvz : v ≠ z := by
                  intro he; subst v; exact hz.2.2.2 (a.freeVars_subset_vars z hv)
                by_cases hvw : v = w <;> by_cases hvx : v = x <;> simp_all
          simp [substFuel, hwx, hfree, satisfies, equiv, z]
        · have hnot : w ∉ replacement.freeVars := by
            intro hw
            exact hfree ((Term.hasFreeVar_iff w replacement).mpr hw)
          have heval (d : Elem s) :
              replacement.eval s (fun v => if v = w then d else σ v) = replacement.eval s σ := by
            apply Term.eval_agree
            intro v hv
            have hvw : v ≠ w := by intro he; subst v; exact hnot hv
            simp [hvw]
          have eqfun (d : Elem s) :
              (fun v => if v = x then replacement.eval s (fun v => if v = w then d else σ v)
                        else if v = w then d else σ v) =
              (fun v => if v = w then d else if v = x then replacement.eval s σ else σ v) := by
            funext v
            by_cases hvx : v = x <;> by_cases hvw : v = w <;> simp_all
          have equiv (d : Elem s) :
              satisfies s (fun v => if v = w then d else σ v) (substFuel x replacement n a) ↔
              satisfies s (fun v => if v = w then d else if v = x then replacement.eval s σ else σ v) a := by
            rw [← eqfun d]
            exact ih _ a hn
          simp [substFuel, hwx, hfree, satisfies, equiv]

/-- Capture-avoiding formula substitution has the standard assignment semantics. -/
theorem satisfies_subst [DecidableEq V] [Fresh V]
    (s : Structure R F V) (σ : V → Elem s) (x : V) (replacement : Term F V)
    (φ : Formula R F V) :
    satisfies s σ (Formula.subst x replacement φ) ↔
      satisfies s (fun y => if y = x then replacement.eval s σ else σ y) φ :=
  satisfies_substFuel s σ x replacement φ.depth φ (Nat.le_refl _)

end Logic.FOL
