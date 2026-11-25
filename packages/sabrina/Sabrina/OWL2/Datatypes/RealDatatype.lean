import Sabrina.OWL2.Datatypes
import Sabrina.OWL2.Datatypes.IrrationalCuts

/-! Reference datatype map for the real numbers. A rational is kept in the
ordinary carrier. Every irrational real is represented by its Dedekind cut.
Values used solely as solver witnesses have no datatype membership here. -/

namespace Sabrina.OWL2.Datatypes

def Value.isIrrationalWitness : Value → Bool
  | .irrational _ => true
  | _ => false

theorem decodeLiteral_not_witness {l : Literal} {v : Value}
    (h : decodeLiteral l = some v) : v.isIrrationalWitness = false := by
  cases v <;> try rfl
  case irrational q => exact (decodeLiteral_ne_irrational l q h).elim

abbrev RealValue := Value ⊕ IrrationalCut

def realValueSpace (t : IRI) : RealValue → Prop
  | .inl v => v.isIrrationalWitness = false ∧ valueSpace t v
  | .inr _ => t = owlReal

def realApplicableFacet (t f : IRI) : RealValue → Prop
  | .inl v => applicableFacet t f v
  | .inr _ => t = owlReal ∧ (orderFacet f).isSome = true

def IrrationalCut.atFacet (c : IrrationalCut) (b : Rat) : OrderFacet → Prop
  | .minInclusive | .minExclusive => c.lower b
  | .maxInclusive | .maxExclusive => ¬ c.lower b

def IrrationalCut.atRational (c : IrrationalCut) (q : Rat) : OrderFacet → Prop
  | .minInclusive | .minExclusive => ¬ c.lower q
  | .maxInclusive | .maxExclusive => c.lower q

def IrrationalCut.atCut (c b : IrrationalCut) : OrderFacet → Prop
  | .minInclusive => ∀ q, b.lower q → c.lower q
  | .maxInclusive => ∀ q, c.lower q → b.lower q
  | .minExclusive => ∃ q, c.lower q ∧ ¬ b.lower q
  | .maxExclusive => ∃ q, b.lower q ∧ ¬ c.lower q

def realFacetSpace (t f : IRI) : RealValue → RealValue → Prop
  | .inl b, .inl v => v.isIrrationalWitness = false ∧ facetSpace t f b v
  | .inl (.number b), .inr c =>
    t = owlReal ∧ ∃ order, orderFacet f = some order ∧ c.atFacet b order
  | .inr c, .inl (.number q) =>
    t = owlReal ∧ ∃ order, orderFacet f = some order ∧ c.atRational q order
  | .inr b, .inr c =>
    t = owlReal ∧ ∃ order, orderFacet f = some order ∧ c.atCut b order
  | _, _ => False

def realDatatypeMap : DatatypeMap where
  Value := RealValue
  builtin := datatypeMap.builtin
  valueSpace := realValueSpace
  lexicalValue l := (decodeLiteral l).map Sum.inl
  applicableFacet := realApplicableFacet
  facetSpace := realFacetSpace
  literal_not_builtin := datatypeMap.literal_not_builtin
  lexical_typed l v h := by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    have ⟨hb, ht⟩ := datatypeMap.lexical_typed l w hw
    exact ⟨hb, decodeLiteral_not_witness hw, ht⟩
  facet_typed t f b v hb hv := by
    cases b with
    | inl b =>
      cases v with
      | inl v => exact ⟨hv.1, datatypeMap.facet_typed t f b v hb hv.2⟩
      | inr c =>
        cases b <;> try contradiction
        exact hv.1
    | inr b =>
      cases v with
      | inl v =>
        cases v <;> try contradiction
        exact ⟨rfl, hv.1 ▸ (valueSpace_real_iff _).mpr (.inl ⟨_, rfl⟩)⟩
      | inr c => exact hv.1

theorem realDatatypeMap_lexical (l : Literal) (v : Value) (h : decodeLiteral l = some v) :
    realDatatypeMap.lexicalValue l = some (.inl v) := by
  change (decodeLiteral l).map Sum.inl = _
  rw [h]
  rfl

end Sabrina.OWL2.Datatypes
