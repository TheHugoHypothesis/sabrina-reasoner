/-!
The object language of Horrocks, Kutz, and Sattler's *The Irresistible SRIQ*,
 Sections 2.1–2.2, restricted to TBoxes and RBoxes. This reference defines its
 own syntax, interpretation, regularity and simplicity. It has no dependency
 on SABRINA's OWL syntax, normalization, or tableau.
-/

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

inductive Role where
  | named (name : String)
  | inverse (name : String)
  deriving DecidableEq, Repr

def Role.name : Role → String
  | .named name | .inverse name => name

/-- The paper takes the head to be a role name. The body is nonempty. -/
structure Inclusion where
  first : Role
  rest : List Role
  head : String
  deriving DecidableEq, Repr

def Inclusion.body (a : Inclusion) : List Role := a.first :: a.rest

inductive RoleAssertion where
  | localReflexive (r : Role)
  | irreflexive (r : Role)
  | symmetric (r : Role)
  | transitive (r : Role)
  | disjoint (r s : Role)
  deriving DecidableEq, Repr

inductive Concept where
  | atom (name : String)
  | top
  | bottom
  | neg (c : Concept)
  | conj (c e : Concept)
  | disj (c e : Concept)
  | some (r : Role) (c : Concept)
  | all (r : Role) (c : Concept)
  | self (r : Role)
  | min (n : Nat) (r : Role) (c : Concept)
  | max (n : Nat) (r : Role) (c : Concept)
  deriving DecidableEq, Repr

structure TBoxRBox where
  tbox : List (Concept × Concept) := []
  hierarchy : List Inclusion := []
  assertions : List RoleAssertion := []
  deriving DecidableEq, Repr

def Inclusion.regularFor (lt : Role → Role → Prop) (a : Inclusion) : Prop :=
  let head := Role.named a.head
  let below := fun body : List Role => ∀ r ∈ body, lt r head
  a.body = [head, head] ∨
  a.body = [.inverse a.head] ∨
  below a.body ∨
  (∃ tail : List Role, tail ≠ [] ∧ a.body = head :: tail ∧ below tail) ∨
  (∃ init : List Role, init ≠ [] ∧ a.body = init ++ [head] ∧ below init)

/-- Definition 2 uses an order on oriented roles. -/
def Regular (hierarchy : List Inclusion) : Prop :=
  ∃ lt : Role → Role → Prop,
    (∀ r, ¬ lt r r) ∧
    (∀ r s t, lt r s → lt s t → lt r t) ∧
    ∀ a ∈ hierarchy, a.regularFor lt

/-- Definition 3 gives equivalent inclusions for symmetry and transitivity.
For an inverse role the equivalent inclusion is oriented to the named head. -/
def RoleAssertion.asInclusion : RoleAssertion → Option Inclusion
  | .symmetric r => some ⟨.inverse r.name, [], r.name⟩
  | .transitive r => some ⟨.named r.name, [.named r.name], r.name⟩
  | _ => none

def TBoxRBox.expandedHierarchy (o : TBoxRBox) : List Inclusion :=
  o.hierarchy ++ o.assertions.filterMap RoleAssertion.asInclusion

/-- The paper's inductive simplicity clauses after expanding symmetry and
transitivity. If the head is absent, the premise of `named` holds vacuously. -/
inductive Simple (hierarchy : List Inclusion) : Role → Prop where
  | named (name : String)
      (unary : ∀ a ∈ hierarchy, a.head = name → a.rest = [])
      (premises : ∀ a ∈ hierarchy, a.head = name → Simple hierarchy a.first) :
      Simple hierarchy (.named name)
  | inverse {name : String} :
      Simple hierarchy (.named name) → Simple hierarchy (.inverse name)

def RoleAssertion.simpleFor (hierarchy : List Inclusion) : RoleAssertion → Prop
  | .localReflexive r | .irreflexive r => Simple hierarchy r
  | .disjoint r s => Simple hierarchy r ∧ Simple hierarchy s
  | .symmetric _ | .transitive _ => True

def Concept.simpleFor (hierarchy : List Inclusion) : Concept → Prop
  | .atom _ | .top | .bottom => True
  | .neg c | .some _ c | .all _ c => c.simpleFor hierarchy
  | .conj c e | .disj c e => c.simpleFor hierarchy ∧ e.simpleFor hierarchy
  | .self r => Simple hierarchy r
  | .min _ r c | .max _ r c => Simple hierarchy r ∧ c.simpleFor hierarchy

def TBoxRBox.WellFormed (o : TBoxRBox) : Prop :=
  Regular o.expandedHierarchy ∧
  (∀ a ∈ o.assertions, a.simpleFor o.expandedHierarchy) ∧
  ∀ gci ∈ o.tbox, gci.1.simpleFor o.expandedHierarchy ∧ gci.2.simpleFor o.expandedHierarchy

structure Model where
  Object : Type
  nonempty : Nonempty Object
  classes : String → Object → Prop
  relations : String → Object → Object → Prop

def Model.edge (m : Model) : Role → m.Object → m.Object → Prop
  | .named name, x, y => m.relations name x y
  | .inverse name, x, y => m.relations name y x

inductive Model.path (m : Model) : List Role → m.Object → m.Object → Prop where
  | nil (x) : m.path [] x x
  | cons {r rs x y z} : m.edge r x y → m.path rs y z → m.path (r :: rs) x z

theorem Model.path_nil_iff (m : Model) (x y : m.Object) :
    m.path [] x y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil x

theorem Model.path_cons_iff (m : Model) (r : Role) (rs : List Role) (x y : m.Object) :
    m.path (r :: rs) x y ↔ ∃ z, m.edge r x z ∧ m.path rs z y := by
  constructor
  · intro h
    cases h with
    | cons he hp => exact ⟨_, he, hp⟩
  · rintro ⟨_, he, hp⟩
    exact .cons he hp

/-- A finite lower bound on the cardinality of a subset of an arbitrary domain. -/
def HasCardinalityAtLeast {α : Type} (n : Nat) (p : α → Prop) : Prop :=
  ∃ f : Fin n → α, (∀ a b, f a = f b → a = b) ∧ ∀ a, p (f a)

def Model.holds (m : Model) (x : m.Object) : Concept → Prop
  | .atom name => m.classes name x
  | .top => True
  | .bottom => False
  | .neg c => ¬ m.holds x c
  | .conj c e => m.holds x c ∧ m.holds x e
  | .disj c e => m.holds x c ∨ m.holds x e
  | .some r c => ∃ y, m.edge r x y ∧ m.holds y c
  | .all r c => ∀ y, m.edge r x y → m.holds y c
  | .self r => m.edge r x x
  | .min n r c => HasCardinalityAtLeast n (fun y => m.edge r x y ∧ m.holds y c)
  | .max n r c => ¬ HasCardinalityAtLeast (n + 1) (fun y => m.edge r x y ∧ m.holds y c)

def Model.holdsAssertion (m : Model) : RoleAssertion → Prop
  | .localReflexive r => ∀ x, (∃ y, m.edge r x y) → m.edge r x x
  | .irreflexive r => ∀ x, ¬ m.edge r x x
  | .symmetric r => ∀ x y, m.edge r x y → m.edge r y x
  | .transitive r => ∀ x y z, m.edge r x y → m.edge r y z → m.edge r x z
  | .disjoint r s => ∀ x y, ¬ (m.edge r x y ∧ m.edge s x y)

def Model.Models (m : Model) (o : TBoxRBox) : Prop :=
  (∀ c ∈ o.tbox, ∀ x, m.holds x c.1 → m.holds x c.2) ∧
  (∀ a ∈ o.hierarchy, ∀ x y, m.path a.body x y → m.edge (.named a.head) x y) ∧
  ∀ a ∈ o.assertions, m.holdsAssertion a

def TBoxRBox.Sat (o : TBoxRBox) : Prop := ∃ m : Model, m.Models o

end Sabrina.OWL2.SROIQD.TextbookSRIQ
