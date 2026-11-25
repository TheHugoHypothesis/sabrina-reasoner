import Init.Data.List.Lemmas

/-! ALC concepts and finite lists of general concept inclusions. -/
namespace Sabrina.ALC

inductive Concept where
  | top
  | atom (name : String)
  | neg (body : Concept)
  | conj (left right : Concept)
  | some (role : String) (body : Concept)
  deriving DecidableEq, Repr

namespace Concept

def bottom : Concept := .neg .top

def disj (left right : Concept) : Concept := .neg (.conj (.neg left) (.neg right))

def all (role : String) (body : Concept) : Concept := .neg (.some role (.neg body))

end Concept

structure Inclusion where
  sub : Concept
  sup : Concept
  deriving DecidableEq, Repr

abbrev TBox := List Inclusion

structure Interpretation where
  Domain : Type
  nonempty : Nonempty Domain
  atom : String → Domain → Prop
  role : String → Domain → Domain → Prop

def holds (i : Interpretation) (x : i.Domain) : Concept → Prop
  | .top => True
  | .atom name => i.atom name x
  | .neg body => ¬ holds i x body
  | .conj left right => holds i x left ∧ holds i x right
  | .some role body => ∃ y, i.role role x y ∧ holds i y body

def models (i : Interpretation) (tbox : TBox) : Prop :=
  ∀ ax ∈ tbox, ∀ x, holds i x ax.sub → holds i x ax.sup

def ConceptSat (tbox : TBox) (c : Concept) : Prop :=
  ∃ i : Interpretation, models i tbox ∧ ∃ x, holds i x c

/-- The carrier has an exhaustive finite enumeration and a root witness. -/
def FiniteConceptSat (tbox : TBox) (c : Concept) : Prop :=
  ∃ i : Interpretation, models i tbox ∧
    (∃ carrier : List i.Domain, ∀ x, x ∈ carrier) ∧ ∃ x, holds i x c

def Consistent (tbox : TBox) : Prop := ∃ i : Interpretation, models i tbox

def Subsumes (tbox : TBox) (a b : Concept) : Prop :=
  ∀ i : Interpretation, models i tbox → ∀ x, holds i x a → holds i x b

def Disjoint (tbox : TBox) (a b : Concept) : Prop :=
  ∀ i : Interpretation, models i tbox → ∀ x, ¬ (holds i x a ∧ holds i x b)

def EntailsNegatedInclusion (tbox : TBox) (a b : Concept) : Prop :=
  ∀ i : Interpretation, models i tbox → ¬ (∀ x, holds i x a → holds i x b)

theorem holds_bottom (i : Interpretation) (x : i.Domain) : ¬ holds i x .bottom :=
  fun h => h trivial

theorem holds_disj (i : Interpretation) (x : i.Domain) (a b : Concept) :
    holds i x (.disj a b) ↔ holds i x a ∨ holds i x b := by
  classical
  change (¬ (¬ holds i x a ∧ ¬ holds i x b)) ↔ _
  constructor
  · intro h
    by_cases ha : holds i x a
    · exact Or.inl ha
    · by_cases hb : holds i x b
      · exact Or.inr hb
      · exact False.elim (h ⟨ha, hb⟩)
  · rintro (ha | hb) ⟨hna, hnb⟩
    · exact hna ha
    · exact hnb hb

theorem holds_all (i : Interpretation) (x : i.Domain) (r : String) (c : Concept) :
    holds i x (.all r c) ↔ ∀ y, i.role r x y → holds i y c := by
  classical
  change (¬ ∃ y, i.role r x y ∧ ¬ holds i y c) ↔ _
  constructor
  · intro h y hr
    apply Classical.byContradiction
    intro hm
    exact h ⟨y, hr, hm⟩
  · rintro h ⟨y, hr, hm⟩
    exact hm (h y hr)

theorem consistent_iff (tbox : TBox) : Consistent tbox ↔ ConceptSat tbox .top := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨x⟩ := i.nonempty
    exact ⟨i, hi, x, trivial⟩
  · rintro ⟨i, hi, _⟩
    exact ⟨i, hi⟩

theorem subsumes_iff (tbox : TBox) (a b : Concept) :
    Subsumes tbox a b ↔ ¬ ConceptSat tbox (.conj a (.neg b)) := by
  classical
  constructor
  · rintro h ⟨i, hi, x, ha, hnb⟩
    exact hnb (h i hi x ha)
  · intro h i hi x ha
    apply Classical.byContradiction
    intro hnb
    exact h ⟨i, hi, x, ha, hnb⟩

theorem disjoint_iff (tbox : TBox) (a b : Concept) :
    Disjoint tbox a b ↔ ¬ ConceptSat tbox (.conj a b) := by
  constructor
  · rintro h ⟨i, hi, x, hab⟩
    exact h i hi x hab
  · intro h i hi x hab
    exact h ⟨i, hi, x, hab⟩

theorem models_cons (i : Interpretation) (ax : Inclusion) (tbox : TBox) :
    models i (ax :: tbox) ↔
      (∀ x, holds i x ax.sub → holds i x ax.sup) ∧ models i tbox := by
  constructor
  · intro h
    exact ⟨h ax (List.mem_cons_self ..), fun g hg => h g (List.mem_cons_of_mem _ hg)⟩
  · rintro ⟨hax, htail⟩ g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hax
    · exact htail g hg

theorem entailsNegatedInclusion_iff (tbox : TBox) (a b : Concept) :
    EntailsNegatedInclusion tbox a b ↔ ¬ ConceptSat (⟨a, b⟩ :: tbox) .top := by
  constructor
  · rintro h ⟨i, hi, _⟩
    obtain ⟨hab, htail⟩ := (models_cons i _ _).mp hi
    exact h i htail hab
  · intro h i hi hab
    obtain ⟨x⟩ := i.nonempty
    exact h ⟨i, (models_cons i _ _).mpr ⟨hab, hi⟩, x, trivial⟩

/-- Negations in this representation occur only at atoms. -/
inductive NNF where
  | top | bottom
  | literal (name : String) (positive : Bool)
  | conj (left right : NNF)
  | disj (left right : NNF)
  | some (role : String) (body : NNF)
  | all (role : String) (body : NNF)
  deriving DecidableEq, Repr

def NNF.toConcept : NNF → Concept
  | .top => .top
  | .bottom => .bottom
  | .literal name true => .atom name
  | .literal name false => .neg (.atom name)
  | .conj a b => .conj a.toConcept b.toConcept
  | .disj a b => .disj a.toConcept b.toConcept
  | .some r c => .some r c.toConcept
  | .all r c => .all r c.toConcept

def normalize (positive : Bool) : Concept → NNF
  | .top => if positive then .top else .bottom
  | .atom name => .literal name positive
  | .neg c => normalize (!positive) c
  | .conj a b => if positive then .conj (normalize true a) (normalize true b)
                 else .disj (normalize false a) (normalize false b)
  | .some r c => if positive then .some r (normalize true c) else .all r (normalize false c)

theorem normalize_sound (i : Interpretation) (x : i.Domain) (c : Concept) (positive : Bool) :
    holds i x (normalize positive c).toConcept ↔
      if positive then holds i x c else ¬ holds i x c := by
  classical
  induction c generalizing x positive with
  | top => cases positive <;> simp [normalize, NNF.toConcept, Concept.bottom, holds]
  | atom name => cases positive <;> simp [normalize, NNF.toConcept, holds]
  | neg c ih => cases positive <;> simp [normalize, ih, holds]
  | conj a b iha ihb =>
    cases positive
    · simp only [normalize, Bool.false_eq_true, ↓reduceIte, NNF.toConcept, holds_disj,
        iha, ihb, holds]
      constructor
      · rintro (hna | hnb) ⟨ha, hb⟩
        · exact hna ha
        · exact hnb hb
      · intro h
        by_cases ha : holds i x a
        · exact Or.inr (fun hb => h ⟨ha, hb⟩)
        · exact Or.inl ha
    · simp [normalize, NNF.toConcept, holds, iha, ihb]
  | some r c ih =>
    cases positive
    · simp [normalize, NNF.toConcept, holds_all, holds, ih, not_exists, not_and]
    · simp [normalize, NNF.toConcept, holds, ih]

theorem normalize_root (tbox : TBox) (c : Concept) :
    ConceptSat tbox (normalize true c).toConcept ↔ ConceptSat tbox c := by
  constructor <;> rintro ⟨i, hi, x, hx⟩
  · exact ⟨i, hi, x, (normalize_sound i x c true).mp hx⟩
  · exact ⟨i, hi, x, (normalize_sound i x c true).mpr hx⟩

def normalizeInclusion (ax : Inclusion) : Inclusion :=
  ⟨(normalize true ax.sub).toConcept, (normalize true ax.sup).toConcept⟩

theorem normalize_tbox (i : Interpretation) (tbox : TBox) :
    models i (tbox.map normalizeInclusion) ↔ models i tbox := by
  constructor
  · intro h ax hax x hx
    have hm := h _ (List.mem_map.mpr ⟨ax, hax, rfl⟩) x ((normalize_sound i x ax.sub true).mpr hx)
    exact (normalize_sound i x ax.sup true).mp hm
  · intro h ax hax x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hax
    exact (normalize_sound i x g.sup true).mpr (h g hg x ((normalize_sound i x g.sub true).mp hx))

theorem normalize_problem (tbox : TBox) (c : Concept) :
    ConceptSat (tbox.map normalizeInclusion) (normalize true c).toConcept ↔ ConceptSat tbox c := by
  rw [normalize_root]
  constructor <;> rintro ⟨i, hi, x, hx⟩
  · exact ⟨i, (normalize_tbox i tbox).mp hi, x, hx⟩
  · exact ⟨i, (normalize_tbox i tbox).mpr hi, x, hx⟩

end Sabrina.ALC
