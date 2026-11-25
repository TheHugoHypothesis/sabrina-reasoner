import Logic.FOL.Alpha

/-! Uniform renaming of both bound and free variables. Bijective renaming is
capture-safe; substitution commutes with it up to syntactic alpha conversion. -/
namespace Logic.FOL

mutual
def Term.mapNames (ρ : V → W) : Term F V → Term F W
  | .var v => .var (ρ v)
  | .app f ts => .app f (mapTermNames ρ ts)
def mapTermNames (ρ : V → W) : List (Term F V) → List (Term F W)
  | [] => []
  | t :: ts => t.mapNames ρ :: mapTermNames ρ ts
end

def Formula.mapNames (ρ : V → W) : Formula R F V → Formula R F W
  | .tr => .tr
  | .fls => .fls
  | .eql a b => .eql (a.mapNames ρ) (b.mapNames ρ)
  | .rel r ts => .rel r (mapTermNames ρ ts)
  | .conj a b => .conj (a.mapNames ρ) (b.mapNames ρ)
  | .disj a b => .disj (a.mapNames ρ) (b.mapNames ρ)
  | .impl a b => .impl (a.mapNames ρ) (b.mapNames ρ)
  | .iffT a b => .iffT (a.mapNames ρ) (b.mapNames ρ)
  | .neg a => .neg (a.mapNames ρ)
  | .allv x a => .allv (ρ x) (a.mapNames ρ)
  | .exv x a => .exv (ρ x) (a.mapNames ρ)

mutual
theorem Term.expand_mapNames (ρ : V → W) (σ : W → Term F U) (t : Term F V) :
    (t.mapNames ρ).expand σ = t.expand (fun v => σ (ρ v)) := by
  cases t with
  | var => rfl
  | app f ts => simp only [Term.mapNames, Term.expand, expand_mapTermNames]
theorem expand_mapTermNames (ρ : V → W) (σ : W → Term F U) (ts : List (Term F V)) :
    expandTerms σ (mapTermNames ρ ts) = expandTerms (fun v => σ (ρ v)) ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [mapTermNames, expandTerms, Term.expand_mapNames, expand_mapTermNames]
end

theorem Formula.bindingTree_mapNames [DecidableEq V] [DecidableEq W]
    (ρ : V → W) (hinj : ∀ a b, ρ a = ρ b → a = b)
    (φ : Formula R F V) (σ : W → Term F U) :
    (φ.mapNames ρ).bindingTree σ = φ.bindingTree (fun v => σ (ρ v)) := by
  have heq (v x : V) : ρ v = ρ x ↔ v = x := ⟨hinj v x, congrArg ρ⟩
  induction φ generalizing σ with
  | tr | fls => rfl
  | eql | rel => simp only [Formula.mapNames, Formula.bindingTree, Term.expand_mapNames, expand_mapTermNames]
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.mapNames, Formula.bindingTree, ia, ib]
  | neg a ia => simp only [Formula.mapNames, Formula.bindingTree, ia]
  | allv x a ia | exv x a ia =>
    simp only [Formula.mapNames, Formula.bindingTree, ia, heq]

theorem Formula.mapNames_subst_alpha [DecidableEq V] [Fresh V]
    (ρ : V → V) (hinj : ∀ a b, ρ a = ρ b → a = b)
    (φ : Formula R F V) (x : V) (t : Term F V) :
    ((φ.subst x t).mapNames ρ).Alpha ((φ.mapNames ρ).subst (ρ x) (t.mapNames ρ)) := by
  intro σ
  have heq (v : V) : ρ v = ρ x ↔ v = x := ⟨hinj v x, congrArg ρ⟩
  simp only [Formula.bindingTree_mapNames ρ hinj, Formula.bindingTree_subst,
    Term.expand_mapNames, heq]

mutual
theorem Term.mem_mapNames_freeVars [DecidableEq V]
    (ρ : V → V) (hinv : ∀ v, ρ (ρ v) = v) (t : Term F V) (v : V) :
    ρ v ∈ (t.mapNames ρ).freeVars ↔ v ∈ t.freeVars := by
  have heq (w : V) : ρ v = ρ w ↔ v = w :=
    ⟨fun h => by have := congrArg ρ h; simpa only [hinv] using this, congrArg ρ⟩
  cases t with
  | var w => simp only [Term.mapNames, Term.freeVars, List.mem_singleton, heq]
  | app f ts => exact mem_mapTermNames_freeVars ρ hinv ts v
theorem mem_mapTermNames_freeVars [DecidableEq V]
    (ρ : V → V) (hinv : ∀ v, ρ (ρ v) = v) (ts : List (Term F V)) (v : V) :
    ρ v ∈ freeVarsOfTerms (mapTermNames ρ ts) ↔ v ∈ freeVarsOfTerms ts := by
  cases ts with
  | nil => simp [mapTermNames, freeVarsOfTerms]
  | cons t ts => simp only [mapTermNames, freeVarsOfTerms, List.mem_append,
      Term.mem_mapNames_freeVars ρ hinv, mem_mapTermNames_freeVars ρ hinv]
end

theorem Formula.mem_mapNames_freeVars [DecidableEq V]
    (ρ : V → V) (hinv : ∀ v, ρ (ρ v) = v) (φ : Formula R F V) (v : V) :
    ρ v ∈ (φ.mapNames ρ).freeVars ↔ v ∈ φ.freeVars := by
  have heq (w : V) : ρ v = ρ w ↔ v = w :=
    ⟨fun h => by have := congrArg ρ h; simpa only [hinv] using this, congrArg ρ⟩
  induction φ with
  | tr | fls => simp [Formula.mapNames, Formula.freeVars]
  | eql => simp only [Formula.mapNames, Formula.freeVars, List.mem_append, Term.mem_mapNames_freeVars ρ hinv]
  | rel => exact mem_mapTermNames_freeVars ρ hinv _ v
  | conj a b ia ib | disj a b ia ib | impl a b ia ib | iffT a b ia ib =>
    simp only [Formula.mapNames, Formula.freeVars, List.mem_append, ia, ib]
  | neg a ia => exact ia
  | allv x a ia | exv x a ia =>
    simp only [Formula.mapNames, Formula.freeVars, List.mem_filter, bne_iff_ne, ia, ne_eq, heq]

/-- Transpose two names; this also handles the case that they are equal. -/
def swapNames [DecidableEq V] (x y v : V) : V :=
  if v = x then y else if v = y then x else v

theorem swapNames_involutive [DecidableEq V] (x y v : V) :
    swapNames x y (swapNames x y v) = v := by
  by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hxy : x = y <;>
    simp_all [swapNames]

theorem swapNames_injective [DecidableEq V] (x y a b : V)
    (h : swapNames x y a = swapNames x y b) : a = b := by
  have := congrArg (swapNames x y) h
  simpa only [swapNames_involutive] using this

/-- A swap of names absent from the free variables changes at most binder spelling. -/
theorem Formula.swapNames_alpha [DecidableEq V] (φ : Formula R F V) (y z : V)
    (hy : y ∉ φ.freeVars) (hz : z ∉ φ.freeVars) :
    (φ.mapNames (swapNames y z)).Alpha φ := by
  intro σ
  rw [Formula.bindingTree_mapNames _ (swapNames_injective y z)]
  apply Formula.bindingTree_agree
  intro v hv
  have hvy : v ≠ y := fun e => hy (e ▸ hv)
  have hvz : v ≠ z := fun e => hz (e ▸ hv)
  simp [swapNames, hvy, hvz]

/-- Swapping the two fresh eigenvariables carries one instance to the other,
even when the substitutions choose different names for inner binders. -/
theorem Formula.swapNames_instance_alpha [DecidableEq V] [Fresh V]
    (body : Formula R F V) (x y z : V)
    (hy : y ∉ (Formula.allv x body).freeVars)
    (hz : z ∉ (Formula.allv x body).freeVars) :
    ((body.subst x (.var y)).mapNames (swapNames y z)).Alpha (body.subst x (.var z)) := by
  intro σ
  rw [Formula.bindingTree_mapNames _ (swapNames_injective y z)]
  simp only [Formula.bindingTree_subst, Term.expand]
  apply Formula.bindingTree_agree
  intro v hv
  by_cases hvx : v = x
  · simp [hvx, swapNames]
  · have hvfree : v ∈ (Formula.allv x body).freeVars := by
      simp only [Formula.freeVars, List.mem_filter, bne_iff_ne]
      exact ⟨hv, hvx⟩
    have hvy : v ≠ y := fun e => hy (e ▸ hvfree)
    have hvz : v ≠ z := fun e => hz (e ▸ hvfree)
    simp [hvx, swapNames, hvy, hvz]

end Logic.FOL
