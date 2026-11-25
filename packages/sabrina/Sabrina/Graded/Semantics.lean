import Sabrina.RoleChains.SimpleRoles

/-! Class restrictions over the object domain with arbitrary finite bounds. -/

namespace Sabrina.Graded

open ALC RoleChains

inductive Concept where
  | top | bottom
  | lit (name : String) (positive : Bool)
  | nom (name : String) (positive : Bool)
  | self (role : String) (positive : Bool)
  | conj (left right : Concept)
  | disj (left right : Concept)
  | some (role : String) (filler : Concept)
  | all (role : String) (filler : Concept)
  | min (count : Nat) (role : String) (filler : Concept)
  | max (count : Nat) (role : String) (filler : Concept)
  deriving DecidableEq, Repr

abbrev Concept.atom (name : String) : Concept := .lit name true

def Concept.oneOf (individuals : List String) : Concept :=
  individuals.foldr (fun a acc => .disj (.nom a true) acc) .bottom

def Concept.hasValue (role individual : String) : Concept :=
  .some role (.nom individual true)

def Concept.dual : Concept → Concept
  | .top => .bottom
  | .bottom => .top
  | .lit p b => .lit p (!b)
  | .nom a b => .nom a (!b)
  | .self r b => .self r (!b)
  | .conj a b => .disj a.dual b.dual
  | .disj a b => .conj a.dual b.dual
  | .some r c => .all r c.dual
  | .all r c => .some r c.dual
  -- Keep the syntactic role occurrence available to the structural validator.
  | .min 0 r c => .conj .bottom (.min 0 r c)
  | .min (n + 1) r c => .max n r c
  | .max n r c => .min (n + 1) r c

def Concept.exact (n : Nat) (r : String) (c : Concept) : Concept :=
  .conj (.min n r c) (.max n r c)

structure Inclusion where
  sub : Concept
  sup : Concept
  deriving DecidableEq, Repr

abbrev TBox := List Inclusion

/-- Additional OWL 2 DL object property characteristics and role disjointness. -/
structure RoleChars where
  reflexive : List String := []
  irreflexive : List String := []
  asymmetric : List String := []
  disjoint : List (OrientedRole × OrientedRole) := []
  deriving DecidableEq, Repr

def RoleChars.roles (chars : RoleChars) : List String :=
  chars.reflexive ++ chars.irreflexive ++ chars.asymmetric ++
    chars.disjoint.flatMap fun (r, s) => [r.1, s.1]

/-- Roles that must be simple under OWL 2 DL global restrictions for `RoleChars`. -/
def RoleChars.simpleRoles (chars : RoleChars) : List OrientedRole :=
  (chars.irreflexive.map (·, false) ++ chars.asymmetric.map (·, false) ++
    chars.disjoint.flatMap fun (r, s) => [r, s]).eraseDups

def modelsRoleChars (i : Interpretation) (chars : RoleChars) : Prop :=
  (∀ r ∈ chars.reflexive, ∀ x, i.role r x x) ∧
  (∀ r ∈ chars.irreflexive, ∀ x, ¬ i.role r x x) ∧
  (∀ r ∈ chars.asymmetric, ∀ x y, i.role r x y → ¬ i.role r y x) ∧
  (∀ p ∈ chars.disjoint, ∀ x y, ¬ (holdsRole i p.1 x y ∧ holdsRole i p.2 x y))

/-- Actual distinct domain elements, regardless of how a certificate names them. -/
def AtLeast {α : Type} (n : Nat) (p : α → Prop) : Prop :=
  ∃ xs : List α, xs.length = n ∧ xs.Nodup ∧ ∀ x ∈ xs, p x

def holds (i : Interpretation) (nom : String → i.Domain) (x : i.Domain) : Concept → Prop
  | .top => True
  | .bottom => False
  | .lit p true => i.atom p x
  | .lit p false => ¬ i.atom p x
  | .nom a true => x = nom a
  | .nom a false => x ≠ nom a
  | .self r true => i.role r x x
  | .self r false => ¬ i.role r x x
  | .conj a b => holds i nom x a ∧ holds i nom x b
  | .disj a b => holds i nom x a ∨ holds i nom x b
  | .some r c => ∃ y, i.role r x y ∧ holds i nom y c
  | .all r c => ∀ y, i.role r x y → holds i nom y c
  | .min n r c => AtLeast n (fun y => i.role r x y ∧ holds i nom y c)
  | .max n r c => ¬ AtLeast (n + 1) (fun y => i.role r x y ∧ holds i nom y c)

theorem holds_dual (i : Interpretation) (nom : String → i.Domain) (x : i.Domain) (c : Concept) :
    holds i nom x c.dual ↔ ¬ holds i nom x c := by
  classical
  induction c generalizing x with
  | top | bottom => simp [Concept.dual, holds]
  | lit p sign =>
    cases sign <;> simp [Concept.dual, holds]
  | nom a sign =>
    cases sign <;> simp [Concept.dual, holds]
  | self r sign =>
    cases sign <;> simp [Concept.dual, holds]
  | conj a b ha hb =>
    simp only [Concept.dual, holds, ha, hb]
    exact Classical.not_and_iff_not_or_not.symm
  | disj a b ha hb => simp [Concept.dual, holds, ha, hb]
  | some r c ih => simp [Concept.dual, holds, ih]
  | all r c ih => simp [Concept.dual, holds, ih, Classical.not_imp]
  | min n r c =>
    cases n with
    | zero =>
      have h : AtLeast 0 (fun y => i.role r x y ∧ holds i nom y c) := ⟨[],rfl,List.nodup_nil,by simp⟩
      simp [Concept.dual, holds, h]
    | succ n => rfl
  | max n r c => simp [Concept.dual, holds]

def models (i : Interpretation) (nom : String → i.Domain) (tbox : TBox) : Prop :=
  ∀ ax ∈ tbox, ∀ x, holds i nom x ax.sub → holds i nom x ax.sup

def ConceptSat (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (root : Concept)
    (chars : RoleChars := {}) : Prop :=
  ∃ (i : Interpretation) (nom : String → i.Domain),
    modelsRoles i rules ∧ modelsChains i chains ∧ modelsRoleChars i chars ∧ models i nom tbox ∧
    ∃ x, holds i nom x root

def Concept.roles : Concept → List String
  | .top | .bottom | .lit _ _ | .nom _ _ => []
  | .self r _ => [r]
  | .conj a b | .disj a b => a.roles ++ b.roles
  | .some r c | .all r c | .min _ r c | .max _ r c => r :: c.roles

def Concept.nominals : Concept → List String
  | .top | .bottom | .lit _ _ | .self _ _ => []
  | .nom a _ => [a]
  | .conj a b | .disj a b => a.nominals ++ b.nominals
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.nominals

/-- All roles used at number restrictions or `ObjectHasSelf`, including ones nested inside fillers. -/
def Concept.countedRoles : Concept → List String
  | .top | .bottom | .lit _ _ | .nom _ _ => []
  | .self r _ => [r]
  | .conj a b | .disj a b => a.countedRoles ++ b.countedRoles
  | .some _ c | .all _ c => c.countedRoles
  | .min _ r c | .max _ r c => r :: c.countedRoles

theorem Concept.countedRoles_dual (c : Concept) : c.dual.countedRoles = c.countedRoles := by
  induction c with
  | top | bottom | lit | nom | self => rfl
  | conj a b ha hb | disj a b ha hb => simp only [dual,countedRoles,ha,hb]
  | some r c ih | all r c ih => exact ih
  | min n r c => cases n <;> rfl
  | max => rfl

def countedRoles (tbox : TBox) (q : Inclusion) : List String :=
  ((q.sub.countedRoles ++ q.sup.countedRoles) ++
    tbox.flatMap (fun ax => ax.sub.countedRoles ++ ax.sup.countedRoles)).eraseDups

def checkSimple (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (q : Inclusion)
    (chars : RoleChars := {}) : Bool :=
  let closed := roleClosure rules
  (countedRoles tbox q).all (fun r => (SimpleRoles.firstComposite closed chains (r,false)).isNone) &&
  chars.simpleRoles.all (fun r => (SimpleRoles.firstComposite closed chains r).isNone)

theorem checkSimple_iff {rules chains tbox q chars} :
    checkSimple rules chains tbox q chars = true ↔
      (∀ r ∈ countedRoles tbox q, SimpleRoles.Simple rules chains (r,false)) ∧
      (∀ r ∈ chars.simpleRoles, SimpleRoles.Simple rules chains r) := by
  unfold checkSimple
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun r hr => SimpleRoles.check_iff.mp (h1 r hr),
                          fun r hr => SimpleRoles.check_iff.mp (h2 r hr)⟩,
         fun ⟨h1, h2⟩ => ⟨fun r hr => SimpleRoles.check_iff.mpr (h1 r hr),
                          fun r hr => SimpleRoles.check_iff.mpr (h2 r hr)⟩⟩

end Sabrina.Graded
