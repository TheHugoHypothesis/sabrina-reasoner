import Logic.FOL.Models

/-!
A model-theoretic bridge for a segregated first-order fragment. This is not
an implementation of all ISO Common Logic: in particular, source text
modules, non-discourse declarations, and names shared between symbol roles
are not yet handled. Relation and function names denote reference objects,
while quantified variables range over the separate discourse domain.
-/
namespace Logic.FOL.CLFragment

structure Interpretation (R F V : Type) where
  discourse : Type
  reference : Type
  embed : discourse → reference
  embed_injective : Function.Injective embed
  relationName : R → reference
  functionName : F → reference
  relationExtension : reference → List discourse → Bool
  functionExtension : reference → List discourse → discourse

def asFOL (m : Interpretation R F V) : Structure R F V where
  univ := m.discourse
  rel r args := m.relationExtension (m.relationName r) args
  fapp f args := m.functionExtension (m.functionName f) args

def term (m : Interpretation R F V) (σ : V → m.discourse) (t : Term F V) : m.discourse :=
  t.eval (asFOL m) σ

def holds [DecidableEq V] (m : Interpretation R F V) (σ : V → m.discourse) :
    Formula R F V → Prop
  | .tr => True
  | .fls => False
  | .eql a b => term m σ a = term m σ b
  | .rel r args => m.relationExtension (m.relationName r) (args.map (term m σ))
  | .conj a b => holds m σ a ∧ holds m σ b
  | .disj a b => holds m σ a ∨ holds m σ b
  | .impl a b => ¬ holds m σ a ∨ holds m σ b
  | .iffT a b => holds m σ a ↔ holds m σ b
  | .neg a => ¬ holds m σ a
  | .allv x a => ∀ d, holds m (fun w => if w = x then d else σ w) a
  | .exv x a => ∃ d, holds m (fun w => if w = x then d else σ w) a

theorem term_agrees (m : Interpretation R F V) (σ : V → m.discourse)
    (t : Term F V) : term m σ t = t.eval (asFOL m) σ := rfl

theorem holds_agrees [DecidableEq V] (m : Interpretation R F V) (σ : V → m.discourse)
    (φ : Formula R F V) : holds m σ φ ↔ satisfies (asFOL m) σ φ := by
  induction φ generalizing σ with
  | tr => rfl
  | fls => rfl
  | eql a b => rfl
  | rel r args => rfl
  | conj a b ih₁ ih₂ => simp only [holds, satisfies, ih₁, ih₂]
  | disj a b ih₁ ih₂ => simp only [holds, satisfies, ih₁, ih₂]
  | impl a b ih₁ ih₂ => simp only [holds, satisfies, ih₁, ih₂]
  | iffT a b ih₁ ih₂ => simp only [holds, satisfies, ih₁, ih₂]
  | neg a ih => simp only [holds, satisfies, ih]
  | allv x a ih => simpa only [holds, satisfies, asFOL, Elem] using (show (∀ d, holds m (fun w => if w = x then d else σ w) a) ↔ (∀ d, satisfies (asFOL m) (fun w => if w = x then d else σ w) a) from forall_congr' (fun d => ih _))
  | exv x a ih => simpa only [holds, satisfies, asFOL, Elem] using (show (∃ d, holds m (fun w => if w = x then d else σ w) a) ↔ (∃ d, satisfies (asFOL m) (fun w => if w = x then d else σ w) a) from exists_congr (fun d => ih _))

/-- Expand a nonempty FOL structure with separate denotations for symbol names.
This construction does not yet interpret source-level Common Logic modules. -/
def ofFOL (s : Structure R F V) (default : Elem s) : Interpretation R F V where
  discourse := Elem s
  reference := Sum (Elem s) (Sum R F)
  embed := Sum.inl
  embed_injective := by intro a b h; exact Sum.inl.inj h
  relationName r := Sum.inr (Sum.inl r)
  functionName f := Sum.inr (Sum.inr f)
  relationExtension name args :=
    match name with
    | .inr (.inl r) => s.rel r args
    | _ => false
  functionExtension name args :=
    match name with
    | .inr (.inr f) => s.fapp f args
    | _ => default

theorem ofFOL_satisfies [DecidableEq V] (s : Structure R F V) (default : Elem s)
    (σ : V → Elem s) (φ : Formula R F V) :
    holds (ofFOL s default) σ φ ↔ satisfies s σ φ := by
  exact holds_agrees (ofFOL s default) σ φ

/-- A reference entity is out-of-discourse if it is not in the image of `embed`. -/
def isOutDiscourse (m : Interpretation R F V) (ref : m.reference) : Prop :=
  ∀ d : m.discourse, ref ≠ m.embed d

/-- A relation symbol denotes an out-of-discourse reference entity. -/
def isOutDiscourseRelation (m : Interpretation R F V) (r : R) : Prop :=
  isOutDiscourse m (m.relationName r)

/-- A function/constant symbol denotes an out-of-discourse reference entity. -/
def isOutDiscourseFunction (m : Interpretation R F V) (f : F) : Prop :=
  isOutDiscourse m (m.functionName f)

theorem ofFOL_relation_outdiscourse (s : Structure R F V) (default : Elem s) (r : R) :
    isOutDiscourseRelation (ofFOL s default) r := by
  intro d h
  cases h

theorem ofFOL_function_outdiscourse (s : Structure R F V) (default : Elem s) (f : F) :
    isOutDiscourseFunction (ofFOL s default) f := by
  intro d h
  cases h

/-- A Common Logic module consisting of a module URI/name, declared non-discourse
relation and function symbols (e.g. from `cl:outdiscourse`), and sentences. -/
structure CLModule (R F V : Type) where
  name : String
  outDiscourseRelations : List R
  outDiscourseFunctions : List F
  sentences : List (Formula R F V)

/-- An interpretation satisfies a Common Logic module iff it satisfies all its sentences
and respects its declared non-discourse symbol segregation. -/
def satisfiesModule [DecidableEq V] (m : Interpretation R F V) (σ : V → m.discourse)
    (mod : CLModule R F V) : Prop :=
  (∀ φ ∈ mod.sentences, holds m σ φ) ∧
  (∀ r ∈ mod.outDiscourseRelations, isOutDiscourseRelation m r) ∧
  (∀ f ∈ mod.outDiscourseFunctions, isOutDiscourseFunction m f)

/-- A Common Logic theory consisting of a collection of named modules. -/
structure CLTheory (R F V : Type) where
  modules : List (CLModule R F V)

/-- An interpretation satisfies a Common Logic theory iff it satisfies every module in the theory. -/
def satisfiesTheory [DecidableEq V] (m : Interpretation R F V) (σ : V → m.discourse)
    (thy : CLTheory R F V) : Prop :=
  ∀ mod ∈ thy.modules, satisfiesModule m σ mod

/-- A Common Logic theory is satisfiable iff there exists an interpretation and variable
assignment satisfying all modules and non-discourse conditions. -/
def CLTheorySatisfiable [DecidableEq V] (thy : CLTheory R F V) : Prop :=
  ∃ (m : Interpretation R F V) (σ : V → m.discourse), satisfiesTheory m σ thy

theorem ofFOL_satisfiesModule [DecidableEq V] (s : Structure R F V) (default : Elem s)
    (σ : V → Elem s) (mod : CLModule R F V)
    (h_sentences : ∀ φ ∈ mod.sentences, satisfies s σ φ) :
    satisfiesModule (ofFOL s default) σ mod := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ
    rw [ofFOL_satisfies]
    exact h_sentences φ hφ
  · intro r hr
    exact ofFOL_relation_outdiscourse s default r
  · intro f hf
    exact ofFOL_function_outdiscourse s default f

theorem ofFOL_satisfiesTheory [DecidableEq V] (s : Structure R F V) (default : Elem s)
    (σ : V → Elem s) (thy : CLTheory R F V)
    (h_thy : ∀ mod ∈ thy.modules, ∀ φ ∈ mod.sentences, satisfies s σ φ) :
    satisfiesTheory (ofFOL s default) σ thy := by
  intro mod hmod
  exact ofFOL_satisfiesModule s default σ mod (h_thy mod hmod)

end Logic.FOL.CLFragment
