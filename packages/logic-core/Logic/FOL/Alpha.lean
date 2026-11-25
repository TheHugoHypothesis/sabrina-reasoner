import Logic.FOL.SubstIdentity

/-!
# Syntactic binder abstraction

`BindingTree` keeps every logical constructor and every function/relation symbol.
A binder is represented by a function from syntactic terms to trees, rather than
by a variable spelling. This is syntax, not truth in a structure. Equality of
these trees will support alpha conversion without semantic completeness.
-/
namespace Logic.FOL

inductive BindingTree (R F V : Type) where
  | tr | fls
  | eql : Term F V → Term F V → BindingTree R F V
  | rel : R → List (Term F V) → BindingTree R F V
  | conj : BindingTree R F V → BindingTree R F V → BindingTree R F V
  | disj : BindingTree R F V → BindingTree R F V → BindingTree R F V
  | impl : BindingTree R F V → BindingTree R F V → BindingTree R F V
  | iffT : BindingTree R F V → BindingTree R F V → BindingTree R F V
  | neg : BindingTree R F V → BindingTree R F V
  | allv : (Term F V → BindingTree R F V) → BindingTree R F V
  | exv : (Term F V → BindingTree R F V) → BindingTree R F V

mutual
def Term.expand (σ : V → Term F W) : Term F V → Term F W
  | .var x => σ x
  | .app f ts => .app f (expandTerms σ ts)
def expandTerms (σ : V → Term F W) : List (Term F V) → List (Term F W)
  | [] => []
  | t :: ts => t.expand σ :: expandTerms σ ts
end

def Formula.bindingTree [DecidableEq V] (φ : Formula R F V)
    (σ : V → Term F W) : BindingTree R F W :=
  match φ with
  | .tr => .tr
  | .fls => .fls
  | .eql a b => .eql (a.expand σ) (b.expand σ)
  | .rel r ts => .rel r (expandTerms σ ts)
  | .conj a b => .conj (a.bindingTree σ) (b.bindingTree σ)
  | .disj a b => .disj (a.bindingTree σ) (b.bindingTree σ)
  | .impl a b => .impl (a.bindingTree σ) (b.bindingTree σ)
  | .iffT a b => .iffT (a.bindingTree σ) (b.bindingTree σ)
  | .neg a => .neg (a.bindingTree σ)
  | .allv x a => .allv (fun t => a.bindingTree (fun v => if v = x then t else σ v))
  | .exv x a => .exv (fun t => a.bindingTree (fun v => if v = x then t else σ v))

mutual
/-- Syntactic expansions agree when their term assignments agree on the free variables. -/
theorem Term.expand_agree (σ τ : V → Term F W)
    (t : Term F V) (h : ∀ v ∈ t.freeVars, σ v = τ v) :
    t.expand σ = t.expand τ := by
  cases t with
  | var x => simpa [Term.expand, Term.freeVars] using h x (by simp [Term.freeVars])
  | app f ts =>
    simp only [Term.expand]
    congr 1
    exact expand_terms_agree σ τ ts h

/-- List companion for syntactic term expansion. -/
theorem expand_terms_agree (σ τ : V → Term F W)
    (ts : List (Term F V)) (h : ∀ v ∈ freeVarsOfTerms ts, σ v = τ v) :
    expandTerms σ ts = expandTerms τ ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [freeVarsOfTerms, List.mem_append] at h
    simp only [expandTerms]
    rw [Term.expand_agree σ τ t (fun v hv => h v (Or.inl hv)),
        expand_terms_agree σ τ ts (fun v hv => h v (Or.inr hv))]
end

/-- Binding trees are equal when term assignments agree on all free variables. -/
theorem Formula.bindingTree_agree [DecidableEq V]
    (φ : Formula R F V) (σ τ : V → Term F W)
    (h : ∀ v ∈ φ.freeVars, σ v = τ v) : φ.bindingTree σ = φ.bindingTree τ := by
  induction φ generalizing σ τ with
  | tr | fls => rfl
  | eql a b =>
    simp only [Formula.freeVars, List.mem_append] at h
    simp only [Formula.bindingTree]
    rw [Term.expand_agree σ τ a (fun v hv => h v (Or.inl hv)),
        Term.expand_agree σ τ b (fun v hv => h v (Or.inr hv))]
  | rel r args =>
    simp only [Formula.freeVars] at h
    simp only [Formula.bindingTree]
    rw [expand_terms_agree σ τ args h]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.freeVars, List.mem_append] at h
    have ha := ia σ τ (fun v hv => h v (Or.inl hv))
    have hb := ib σ τ (fun v hv => h v (Or.inr hv))
    simp only [Formula.bindingTree, ha, hb]
  | neg a ia =>
    simp only [Formula.freeVars] at h
    simp only [Formula.bindingTree, ia σ τ h]
  | allv x a ia | exv x a ia =>
    simp only [Formula.freeVars, List.mem_filter] at h
    have upd (d : Term F W) : ∀ v ∈ a.freeVars,
        (if v = x then d else σ v) = (if v = x then d else τ v) := by
      intro v hv
      by_cases he : v = x
      · simp [he]
      · simp [he, h v ⟨hv, by simp [he]⟩]
    simp only [Formula.bindingTree]
    congr 1
    funext d
    exact ia _ _ (upd d)

mutual
/-- Expanding a substituted term agrees with updating the term assignment. -/
theorem Term.expand_subst [DecidableEq V] (σ : V → Term F W)
    (x : V) (replacement : Term F V) (t : Term F V) :
    (Term.subst x replacement t).expand σ =
      t.expand (fun y => if y = x then replacement.expand σ else σ y) := by
  cases t with
  | var y =>
    by_cases h : y = x <;> simp [Term.subst, Term.subst', Term.expand, h]
  | app f args =>
    simp only [Term.subst, Term.subst', Term.expand]
    rw [expand_subst_list σ x replacement args]

/-- List companion used for function arguments. -/
theorem expand_subst_list [DecidableEq V] (σ : V → Term F W)
    (x : V) (replacement : Term F V) (ts : List (Term F V)) :
    expandTerms σ (subst'List (x, replacement) ts) =
      expandTerms (fun y => if y = x then replacement.expand σ else σ y) ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [subst'List, expandTerms]
    change (Term.subst x replacement t).expand σ :: _ = _
    rw [Term.expand_subst σ x replacement t,
        expand_subst_list σ x replacement ts]
end

mutual
/-- Expanding a renamed term agrees with updating the renamed variable. -/
theorem Term.expand_rename [DecidableEq V] (σ : V → Term F W)
    (y z : V) (t : Term F V) :
    (t.rename y z).expand σ = t.expand (fun v => if v = y then σ z else σ v) := by
  cases t with
  | var v => by_cases h : v = y <;> simp [Term.rename, Term.expand, h]
  | app f args =>
    simp only [Term.rename, Term.expand]
    rw [expand_rename_terms σ y z args]

theorem expand_rename_terms [DecidableEq V] (σ : V → Term F W)
    (y z : V) (ts : List (Term F V)) :
    expandTerms σ (renameTerms y z ts) =
      expandTerms (fun v => if v = y then σ z else σ v) ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [renameTerms, expandTerms, Term.expand_rename,
      expand_rename_terms]
end

/-- Renaming `y` to a name absent from all variables in the formula agrees
with assigning to `y` the syntactic term assigned to the fresh name. -/
theorem Formula.bindingTree_rename [DecidableEq V]
    (φ : Formula R F V) (y z : V) (hz : z ∉ φ.vars) (σ : V → Term F W) :
    (φ.rename y z).bindingTree σ =
      φ.bindingTree (fun v => if v = y then σ z else σ v) := by
  induction φ generalizing σ with
  | tr | fls => rfl
  | eql a b => simp [Formula.rename, Formula.bindingTree, Term.expand_rename]
  | rel r ts => simp [Formula.rename, Formula.bindingTree, expand_rename_terms]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.vars, List.mem_append, not_or] at hz
    simp only [Formula.rename, Formula.bindingTree]
    rw [ia hz.1 σ, ib hz.2 σ]
  | neg a ia =>
    simp only [Formula.vars] at hz
    simp only [Formula.rename, Formula.bindingTree]
    rw [ia hz σ]
  | allv w a ia | exv w a ia =>
    simp only [Formula.vars, List.mem_cons, not_or] at hz
    by_cases hwy : w = y
    · subst w
      simp only [Formula.rename, beq_self_eq_true, decide_true, ite_true, Formula.bindingTree]
      have eqfun (d : Term F W) :
          (fun v => if v = y then d else (if v = y then σ z else σ v)) =
          (fun v => if v = y then d else σ v) := by
        funext v
        by_cases h : v = y <;> simp [h]
      simp only [eqfun]
    · simp only [Formula.rename, beq_iff_eq, hwy, decide_false, Formula.bindingTree]
      have eqfun (d : Term F W) :
          (fun v => if v = y then (if z = w then d else σ z)
                    else (if v = w then d else σ v)) =
          (fun v => if v = w then d else (if v = y then σ z else σ v)) := by
        funext v
        have hzw : z ≠ w := hz.1
        by_cases hvy : v = y <;> by_cases hvw : v = w <;> simp_all
      have equiv (d : Term F W) :
          (a.rename y z).bindingTree (fun v => if v = w then d else σ v) =
          a.bindingTree (fun v => if v = w then d else if v = y then σ z else σ v) := by
        rw [← eqfun d]
        exact ia hz.2 _
      simp only [Bool.false_eq_true, ↓reduceIte, equiv]


/-- Fuel-bounded substitution preserves the syntactic binding tree when the fuel covers the
formula depth. This includes alpha-renaming at conflicting binders. -/
theorem Formula.bindingTree_substFuel [DecidableEq V] [Fresh V]
    (σ : V → Term F W) (x : V) (replacement : Term F V)
    (n : Nat) (φ : Formula R F V) (hn : φ.depth ≤ n) :
    (substFuel x replacement n φ).bindingTree σ =
      φ.bindingTree (fun y => if y = x then replacement.expand σ else σ y) := by
  induction n generalizing φ σ with
  | zero => cases φ <;> simp [Formula.depth] at hn
  | succ n ih =>
    cases φ with
    | tr | fls => simp [substFuel, Formula.bindingTree]
    | eql a b => simp [substFuel, Formula.bindingTree, Term.expand_subst]
    | rel r args => simp [substFuel, Formula.bindingTree, expand_subst_list]
    | conj a b | disj a b | impl a b | iffT a b =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      have ha : a.depth ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hb : b.depth ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
      simp only [substFuel, Formula.bindingTree]
      rw [ih σ a ha, ih σ b hb]
    | neg a =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      simp only [substFuel, Formula.bindingTree]
      rw [ih σ a hn]
    | allv w a | exv w a =>
      simp only [Formula.depth, Nat.succ_le_succ_iff] at hn
      by_cases hwx : w = x
      · subst w
        simp only [substFuel, ite_true, Formula.bindingTree]
        have eqfun (d : Term F W) :
            (fun v => if v = x then d else σ v) =
            (fun v => if v = x then d else if v = x then replacement.expand σ else σ v) := by
          funext v; by_cases h : v = x <;> simp [h]
        simp only [← eqfun]
      · by_cases hfree : replacement.hasFreeVar? w = true
        · let z := Fresh.fresh (x :: w :: (replacement.freeVars ++ a.vars))
          have hz : z ∉ x :: w :: (replacement.freeVars ++ a.vars) := by
            intro h
            exact Fresh.fresh_notMem _ z h rfl
          simp only [List.mem_cons, List.mem_append, not_or] at hz
          have heval (d : Term F W) :
              replacement.expand (fun v => if v = z then d else σ v) = replacement.expand σ := by
            apply Term.expand_agree
            intro v hv
            have hvz : v ≠ z := by intro he; subst v; exact hz.2.2.1 hv
            simp [hvz]
          have equiv (d : Term F W) :
              (substFuel x replacement n (a.rename w z)).bindingTree (fun v => if v = z then d else σ v) =
              a.bindingTree (fun v => if v = w then d else if v = x then replacement.expand σ else σ v) := by
            have hd : (a.rename w z).depth ≤ n := by simpa [Formula.rename_depth] using hn
            calc
              _ = (a.rename w z).bindingTree (fun v => if v = x then replacement.expand (fun v => if v = z then d else σ v)
                                        else if v = z then d else σ v) := ih _ _ hd
              _ = a.bindingTree (fun v => if v = w then
                    (if z = x then replacement.expand (fun v => if v = z then d else σ v) else d)
                    else if v = x then replacement.expand (fun v => if v = z then d else σ v)
                    else if v = z then d else σ v) := by
                simpa using (Formula.bindingTree_rename a w z hz.2.2.2
                  (fun v => if v = x then replacement.expand (fun v => if v = z then d else σ v)
                            else if v = z then d else σ v))
              _ = _ := by
                apply Formula.bindingTree_agree
                intro v hv
                have hvz : v ≠ z := by
                  intro he; subst v; exact hz.2.2.2 (a.freeVars_subset_vars z hv)
                by_cases hvw : v = w <;> by_cases hvx : v = x <;> simp_all
          simp [substFuel, hwx, hfree, Formula.bindingTree, equiv, z]
        · have hnot : w ∉ replacement.freeVars := by
            intro hw
            exact hfree ((Term.hasFreeVar_iff w replacement).mpr hw)
          have heval (d : Term F W) :
              replacement.expand (fun v => if v = w then d else σ v) = replacement.expand σ := by
            apply Term.expand_agree
            intro v hv
            have hvw : v ≠ w := by intro he; subst v; exact hnot hv
            simp [hvw]
          have eqfun (d : Term F W) :
              (fun v => if v = x then replacement.expand (fun v => if v = w then d else σ v)
                        else if v = w then d else σ v) =
              (fun v => if v = w then d else if v = x then replacement.expand σ else σ v) := by
            funext v
            by_cases hvx : v = x <;> by_cases hvw : v = w <;> simp_all
          have equiv (d : Term F W) :
              (substFuel x replacement n a).bindingTree (fun v => if v = w then d else σ v) =
              a.bindingTree (fun v => if v = w then d else if v = x then replacement.expand σ else σ v) := by
            rw [← eqfun d]
            exact ih _ a hn
          simp [substFuel, hwx, hfree, Formula.bindingTree, equiv]


/-- Syntactic substitution theorem, including conflicting binders. -/
theorem Formula.bindingTree_subst [DecidableEq V] [Fresh V]
    (φ : Formula R F V) (σ : V → Term F W) (x : V) (t : Term F V) :
    (φ.subst x t).bindingTree σ =
      φ.bindingTree (fun v => if v = x then t.expand σ else σ v) :=
  Formula.bindingTree_substFuel σ x t φ.depth φ (Nat.le_refl _)

/-- Alpha comparison preserves constructors and compares binder bodies at every
syntactic term. No models, entailment, or proof relation occur in this definition. -/
def Formula.Alpha [DecidableEq V] (a b : Formula R F V) : Prop :=
  ∀ σ : V → Term F V, a.bindingTree σ = b.bindingTree σ

mutual
@[simp] theorem Term.expand_var (t : Term F V) : t.expand Term.var = t := by
  cases t with
  | var x => rfl
  | app f ts => simp [Term.expand, expandTerms_var]
@[simp] theorem expandTerms_var (ts : List (Term F V)) : expandTerms Term.var ts = ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp [expandTerms, Term.expand_var, expandTerms_var]
end

theorem substFuel_depth [DecidableEq V] [Fresh V]
    (n : Nat) (φ : Formula R F V) (x : V) (t : Term F V) :
    (substFuel x t n φ).depth = φ.depth := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    cases φ with
    | tr | fls | eql | rel => rfl
    | conj | disj | impl | iffT | neg => simp only [substFuel, Formula.depth, ih]
    | allv w a | exv w a =>
      simp only [substFuel]
      split
      · rfl
      · split <;> simp only [Formula.depth, ih, Formula.rename_depth]

theorem Formula.subst_depth [DecidableEq V] [Fresh V]
    (φ : Formula R F V) (x : V) (t : Term F V) :
    (φ.subst x t).depth = φ.depth := substFuel_depth φ.depth φ x t

end Logic.FOL
