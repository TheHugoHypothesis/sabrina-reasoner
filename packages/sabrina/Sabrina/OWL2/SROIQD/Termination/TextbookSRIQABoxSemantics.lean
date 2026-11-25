import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQ

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

/-! ### 1. Textbook ABox syntax, simplicity, and semantics (no UNA) -/

inductive ABoxAssertion where
  | concept (c : Concept) (a : String)
  | role (r : Role) (a b : String)
  | negRole (r : Role) (a b : String)
  | same (a b : String)
  | different (a b : String)
  deriving DecidableEq, Repr

structure KnowledgeBase where
  tboxRBox : TBoxRBox := {}
  abox : List ABoxAssertion := []
  deriving DecidableEq, Repr

def TBoxRBox.toKB (o : TBoxRBox) : KnowledgeBase :=
  { tboxRBox := o, abox := [] }

/-- Simplicity check for this reference adapter. Counting and self restrictions
use simple roles. Positive and negative role assertions may use arbitrary
oriented roles. -/
def ABoxAssertion.simpleFor (hierarchy : List Inclusion) : ABoxAssertion → Prop
  | .concept c _ => c.simpleFor hierarchy
  | .role _ _ _ | .negRole _ _ _ | .same _ _ | .different _ _ => True

/-- Stricter simplicity clause that additionally requires simple roles in
negated role assertions `¬R(a, b)`. -/
def ABoxAssertion.simpleNegRole (hierarchy : List Inclusion) : ABoxAssertion → Prop
  | .concept c _ => c.simpleFor hierarchy
  | .negRole r _ _ => Simple hierarchy r
  | .role _ _ _ | .same _ _ | .different _ _ => True

theorem ABoxAssertion.simpleNegRole_implies_simpleFor {hierarchy : List Inclusion}
    {a : ABoxAssertion} (h : a.simpleNegRole hierarchy) :
    a.simpleFor hierarchy := by
  cases a <;> simp [ABoxAssertion.simpleNegRole, ABoxAssertion.simpleFor] at h ⊢
  exact h

def KnowledgeBase.WellFormed (kb : KnowledgeBase) : Prop :=
  kb.tboxRBox.WellFormed ∧
  ∀ a ∈ kb.abox, a.simpleFor kb.tboxRBox.expandedHierarchy

/-- Interpretation of a textbook SRIQ knowledge base. `individuals` is an
unconstrained function `String → Object`, reflecting the absence of a
unique-name assumption. -/
structure ABoxModel where
  toModel : Model
  individuals : String → toModel.Object

def ABoxModel.holdsABox (m : ABoxModel) : ABoxAssertion → Prop
  | .concept c a => m.toModel.holds (m.individuals a) c
  | .role r a b => m.toModel.edge r (m.individuals a) (m.individuals b)
  | .negRole r a b => ¬ m.toModel.edge r (m.individuals a) (m.individuals b)
  | .same a b => m.individuals a = m.individuals b
  | .different a b => m.individuals a ≠ m.individuals b

def ABoxModel.Models (m : ABoxModel) (kb : KnowledgeBase) : Prop :=
  m.toModel.Models kb.tboxRBox ∧ ∀ a ∈ kb.abox, m.holdsABox a

def KnowledgeBase.Sat (kb : KnowledgeBase) : Prop :=
  ∃ m : ABoxModel, m.Models kb

theorem TBoxRBox.toKB_sat_iff (o : TBoxRBox) : o.toKB.Sat ↔ o.Sat := by
  constructor
  · rintro ⟨m, hm, _⟩
    exact ⟨m.toModel, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨m, fun _ => Classical.choice m.nonempty⟩, hm, by simp [TBoxRBox.toKB]⟩

end Sabrina.OWL2.SROIQD.TextbookSRIQ
