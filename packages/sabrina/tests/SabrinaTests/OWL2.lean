import Sabrina.OWL2.GradedBridge

namespace SabrinaTests.OWL2

open Sabrina.OWL2

private def smallType : IRI := "urn:example:coordinate"
private def link : IRI := "urn:example:link"
private def dataRole : IRI := "urn:example:value"

private def zeroLiteral : Literal := ⟨"0",smallType⟩
private def aliasLiteral : Literal := ⟨"00",smallType⟩

private def parseSmall (l : Literal) : Option Nat :=
  if l.datatype = smallType ∧ (l.lexical = "0" ∨ l.lexical = "00") then some 0 else none

private abbrev map : DatatypeMap where
  Value := Nat
  builtin r := r = smallType
  valueSpace r x := r = smallType ∧ x = 0
  lexicalValue := parseSmall
  applicableFacet t f v := t = smallType ∧ f = "urn:example:maxInclusive" ∧ v = 0
  facetSpace t f b v := t = smallType ∧ f = "urn:example:maxInclusive" ∧ b = 0 ∧ v = 0
  literal_not_builtin := by decide
  lexical_typed := by
    intro l v hv
    unfold parseSmall at hv
    split at hv
    · rename_i h
      cases hv
      exact ⟨h.1,h.1,rfl⟩
    · contradiction
  facet_typed := by
    intro t f v w ht hw
    exact ⟨ht.1,hw.2.2.2⟩

private abbrev model : Interpretation map where
  Object := Fin 3
  objectNonempty := ⟨0⟩
  Data := Option Nat
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes r _ := r = thing
  objectProperties r x y := r = topObjectProperty ∨ (r = link ∧ x ≠ 2 ∧ y = 2)
  dataProperties r x y := r = topDataProperty ∨ (r = dataRole ∧ x = 0 ∧ y = some 0)
  individuals
    | .named "urn:example:b" => 1
    | _ => 0
  datatypes r y := r = literalDatatype ∨ (r = smallType ∧ y = some 0)
  literalValue := parseSmall
  lexicalAgreement := fun _ _ h => h
  named x := x ≠ 2
  namedIndividual := by
    intro a
    by_cases h : a = "urn:example:b"
    · subst a
      decide
    · simp [h]
  thingExt _ := rfl
  nothingExt := fun _ => by decide
  topObjectExt _ _ := Or.inl rfl
  bottomObjectExt := by
    intro x y
    exact fun h => h.elim (by decide) (fun h' => (by decide : bottomObjectProperty ≠ link) h'.1)
  topDataExt _ _ := Or.inl rfl
  bottomDataExt := by
    intro x y
    exact fun h => h.elim (by decide) (fun h' => (by decide : bottomDataProperty ≠ dataRole) h'.1)
  literalDatatypeExt _ := Or.inl rfl
  datatypeAgreement := by
    intro t ht y
    change t = smallType at ht
    subst t
    change smallType = literalDatatype ∨ (smallType = smallType ∧ y = some 0) ↔
      ∃ v : Nat, (smallType = smallType ∧ v = 0) ∧ some v = y
    have h : smallType ≠ literalDatatype := by decide
    simp [h,eq_comm]

-- Lexical aliases share a data value, so counting a restriction with both
-- spellings still counts one successor.
example : classHolds model 0 (.dataExact 1 dataRole (.oneOf [zeroLiteral,aliasLiteral])) := by
  have hz : model.literalValue zeroLiteral = some 0 := rfl
  have ha : model.literalValue aliasLiteral = some 0 := rfl
  refine ⟨⟨[some 0],rfl,by simp,?_⟩,?_⟩
  · intro y hy
    cases List.mem_singleton.mp hy
    exact ⟨Or.inr ⟨rfl,rfl,rfl⟩,zeroLiteral,by simp,hz⟩
  · apply (atMostOne_iff _).mpr
    rintro x y ⟨_,lx,hlx,hx⟩ ⟨_,ly,hly,hy⟩
    have same (s : Option Nat) (l : Literal) (hl : l ∈ [zeroLiteral,aliasLiteral])
        (he : model.literalValue l = s) : s = some 0 := by
      rcases List.mem_cons.mp hl with rfl | h
      · exact he.symm.trans hz
      · cases List.mem_singleton.mp h
        exact he.symm.trans ha
    exact (same x lx hlx hx).trans (same y ly hly hy).symm

example : dataHolds model (some 0)
    (.restriction smallType [⟨"urn:example:maxInclusive",aliasLiteral⟩]) := by
  refine ⟨Or.inr ⟨rfl,rfl⟩,?_⟩
  intro f hf
  cases List.mem_singleton.mp hf
  exact ⟨0,0,rfl,⟨rfl,rfl,rfl,rfl⟩,rfl⟩

-- Subjects zero and one share a target, but that target lies outside NAMED.
example : axiomHolds model (.hasKey (.named thing) [.named link] []) := by
  intro x y _ _ _ _ h _
  obtain ⟨z,hn,he,_⟩ := h (.named link) (by simp)
  rcases he with htop | hh
  · exact ((by decide : link ≠ topObjectProperty) htop).elim
  · exact (hn hh.2.2).elim

private def anonOntology : Ontology :=
  [.differentIndividuals [.named "urn:example:a",.anonymous "doc" "x"]]

example : models model anonOntology := by
  refine ⟨fun _ _ => 1,?_⟩
  intro ax hx
  cases List.mem_singleton.mp hx
  simp [axiomHolds,Interpretation.withAnonymous,List.pairwise_cons]


example : ¬ satisfies model anonOntology := by
  intro h
  have hc := h _ (List.mem_cons_self ..)
  simp [axiomHolds,List.pairwise_cons] at hc


end SabrinaTests.OWL2
