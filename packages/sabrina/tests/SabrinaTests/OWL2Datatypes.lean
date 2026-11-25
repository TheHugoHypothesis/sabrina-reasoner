import Sabrina.OWL2.Datatypes
import Sabrina.OWL2.DataCertificates
import Sabrina.OWL2.GradedBridge

namespace SabrinaTests.OWL2Datatypes

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes

example : decodeLiteral ⟨"true",xsd "boolean"⟩ = some (.boolean true) := by decide
example : decodeLiteral ⟨"0",xsd "boolean"⟩ = some (.boolean false) := by decide
example : decodeLiteral ⟨"True",xsd "boolean"⟩ = none := by decide
example : decodeLiteral ⟨" 1",xsd "integer"⟩ = none := by decide
example : decodeLiteral ⟨"1_000",xsd "integer"⟩ = none := by decide
example : decodeLiteral ⟨"١",xsd "integer"⟩ = none := by decide
example : decodeLiteral ⟨"+",xsd "integer"⟩ = none := by decide
example : decodeLiteral ⟨"-",xsd "integer"⟩ = none := by decide
example : decodeLiteral ⟨"-0",xsd "nonNegativeInteger"⟩ = some (.integer 0) := by decide
example : decodeLiteral ⟨"-0",xsd "negativeInteger"⟩ = none := by decide
example : decodeLiteral ⟨"+0",xsd "nonPositiveInteger"⟩ = some (.integer 0) := by decide
example : decodeLiteral ⟨"+0",xsd "positiveInteger"⟩ = none := by decide
example : decodeLiteral ⟨"127",xsd "byte"⟩ = some (.integer 127) := by decide
example : decodeLiteral ⟨"-128",xsd "byte"⟩ = some (.integer (-128)) := by decide
example : decodeLiteral ⟨"128",xsd "byte"⟩ = none := by decide
example : decodeLiteral ⟨"-129",xsd "byte"⟩ = none := by decide
example : decodeLiteral ⟨"256",xsd "unsignedByte"⟩ = none := by decide
example : decodeLiteral ⟨"32768",xsd "short"⟩ = none := by decide
example : decodeLiteral ⟨"-32768",xsd "short"⟩ = some (.integer (-32768)) := by decide
example : decodeLiteral ⟨"65536",xsd "unsignedShort"⟩ = none := by decide
example : decodeLiteral ⟨"2147483648",xsd "int"⟩ = none := by decide
example : decodeLiteral ⟨"4294967296",xsd "unsignedInt"⟩ = none := by decide
example : decodeLiteral ⟨"-9223372036854775808",xsd "long"⟩ =
    some (.integer (-9223372036854775808)) := by decide
example : decodeLiteral ⟨"9223372036854775808",xsd "long"⟩ = none := by decide
example : decodeLiteral ⟨"18446744073709551615",xsd "unsignedLong"⟩ =
    some (.integer 18446744073709551615) := by decide
example : decodeLiteral ⟨"18446744073709551616",xsd "unsignedLong"⟩ = none := by decide

example : decodeLiteral ⟨"-.50",xsd "decimal"⟩ = some (.number (mkRat (-1) 2)) := by decide
example : decodeLiteral ⟨"1.",xsd "decimal"⟩ = some (.integer 1) := by decide
example : decodeLiteral ⟨".",xsd "decimal"⟩ = none := by decide
example : decodeLiteral ⟨".-5",xsd "decimal"⟩ = none := by decide
example : decodeLiteral ⟨"1e2",xsd "decimal"⟩ = none := by decide
example : decodeLiteral ⟨"1.2.3",xsd "decimal"⟩ = none := by decide
example : decodeLiteral ⟨"0.10",xsd "decimal"⟩ =
    decodeLiteral ⟨"1/10",owlRational⟩ := by decide
example : decodeLiteral ⟨"+1/03",owlRational⟩ = some (.number (mkRat 1 3)) := by decide
example : decodeLiteral ⟨"1/0",owlRational⟩ = none := by decide
example : decodeLiteral ⟨"1/+3",owlRational⟩ = none := by decide
example : decodeLiteral ⟨"1/-3",owlRational⟩ = none := by decide
example : decodeLiteral ⟨"1.0/3",owlRational⟩ = none := by decide
example : decodeLiteral ⟨"1/3/5",owlRational⟩ = none := by decide
example : decodeLiteral ⟨"1 /3",owlRational⟩ = none := by decide

theorem one_third_rational : valueSpace owlRational (.number (mkRat 1 3)) :=
  (checkValue_iff _ _).mp (by decide)

theorem one_third_not_decimal : ¬ valueSpace (xsd "decimal") (.number (mkRat 1 3)) := by
  intro h
  have hvalue := (checkValue_iff _ _).mpr h
  have expected : checkValue (xsd "decimal") (.number (mkRat 1 3)) = false := by decide
  rw [expected] at hvalue
  cases hvalue

example : checkValue (xsd "decimal") (.number (mkRat 1 8)) = true := by decide
example : checkValue (xsd "byte") (.number (mkRat 256 2)) = false := by decide

/-- Comparing an exact decimal with a nearby rational keeps their strict order. -/
example : checkFacet owlRational (xsd "minExclusive")
    (.number (mkRat 333333333333333333 1000000000000000000))
    (.number (mkRat 1 3)) = true := by decide

example : checkFacet (xsd "decimal") (xsd "minExclusive")
    (.number (mkRat 333333333333333333 1000000000000000000))
    (.number (mkRat 1 3)) = false := by decide

example : checkFacet (xsd "integer") (xsd "maxExclusive")
    (.number (mkRat 3 2)) (.integer 1) = true := by decide

private def minimumZero : Facet := ⟨xsd "minInclusive", ⟨"0",xsd "integer"⟩⟩

theorem integer_facet_allows_200 (i : Interpretation datatypeMap) :
    facetHolds i (xsd "integer") minimumZero (i.embedValue (.integer 200)) := by
  apply (facetHolds_iff_check i _ _ (.integer 0) (.integer 200) (by decide)).mpr
  decide

theorem byte_facet_excludes_200 (i : Interpretation datatypeMap) :
    ¬ facetHolds i (xsd "byte") minimumZero (i.embedValue (.integer 200)) := by
  intro h
  have he := (facetHolds_iff_check i _ _ (.integer 0) (.integer 200) (by decide)).mp h
  have expected : checkFacet (xsd "byte") (xsd "minInclusive") (.integer 0) (.integer 200) = false := by
    decide
  change checkFacet (xsd "byte") (xsd "minInclusive") (.integer 0) (.integer 200) = true at he
  rw [expected] at he
  cases he

example : checkFacet (xsd "integer") (xsd "maxInclusive") (.integer 0) (.integer 0) = true := by decide
example : checkFacet (xsd "integer") (xsd "maxExclusive") (.integer 0) (.integer 0) = false := by decide
example : checkFacet (xsd "integer") (xsd "minExclusive") (.integer 0) (.integer 0) = false := by decide
example : checkFacet (xsd "boolean") (xsd "maxInclusive") (.boolean true) (.boolean false) = false := by
  decide

def hasScore : IRI := "urn:example:hasScore"
def subject : Individual := .named "urn:example:submission"

private def integerOne : Literal := ⟨"01",xsd "integer"⟩
private def decimalOne : Literal := ⟨"1.0",xsd "decimal"⟩
private def rationalOne : Literal := ⟨"2/2",owlRational⟩

private def scoreAssertions (values : List Literal) : Ontology :=
  .functionalDataProperty hasScore :: values.map (fun l => .dataAssertion hasScore subject l)

def scoreOntology (other : String) : Ontology :=
  scoreAssertions [integerOne,⟨other,xsd "byte"⟩]

def mixedScoreOntology (other : String) : Ontology :=
  scoreAssertions [integerOne,decimalOne,⟨other,owlRational⟩]

private def singleObject : Sabrina.ALC.Interpretation :=
  ⟨Unit, ⟨()⟩, fun _ _ => False, fun _ _ _ => False⟩

private noncomputable def scoreModel : Interpretation datatypeMap :=
  { GradedBridge.extend datatypeMap singleObject with
    dataProperties r _ y := r = topDataProperty ∨ (r = hasScore ∧ y = some (.integer 1))
    topDataExt := fun _ _ => Or.inl rfl
    bottomDataExt := by
      intro _ _ h
      rcases h with ht | ⟨hs,_⟩
      · exact (by decide : bottomDataProperty ≠ topDataProperty) ht
      · exact (by decide : bottomDataProperty ≠ hasScore) hs }

private theorem scoreAssertions_satisfiable (ls : List Literal)
    (hvalues : ∀ l ∈ ls, decodeLiteral l = some (.integer 1)) :
    Satisfiable datatypeMap (scoreAssertions ls) := by
  have top_ne_score : hasScore ≠ topDataProperty := by decide
  refine ⟨scoreModel,satisfies_models ?_⟩
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | hax
  · intro _ y z hy hz
    rcases hy with ht | ⟨_,he⟩
    · exact (top_ne_score ht).elim
    rcases hz with ht | ⟨_,hf⟩
    · exact (top_ne_score ht).elim
    exact he.trans hf.symm
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hax
    exact Or.inr ⟨rfl,scoreModel.lexicalAgreement l _ (hvalues l hl)⟩

theorem equivalent_scores_satisfiable : Satisfiable datatypeMap (scoreOntology "+1") := by
  apply scoreAssertions_satisfiable
  intro l hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl <;> decide

theorem different_scores_inconsistent : ¬ Satisfiable datatypeMap (scoreOntology "2") := by
  have h₁ : decodeLiteral integerOne = some (.integer 1) := by decide
  have h₂ : decodeLiteral ⟨"2",xsd "byte"⟩ = some (.integer 2) := by decide
  exact functional_data_conflict
    (r := hasScore) (a := subject) (l := integerOne) (m := ⟨"2",xsd "byte"⟩)
    (by simp [scoreOntology,scoreAssertions]) (by simp [scoreOntology,scoreAssertions])
    (by simp [scoreOntology,scoreAssertions]) h₁ h₂
    (show (Value.integer 1 : Value) ≠ .integer 2 by decide)

theorem integer_decimal_rational_literals_identical (i : Interpretation datatypeMap) :
    i.literalValue integerOne = i.literalValue decimalOne ∧
    i.literalValue integerOne = i.literalValue rationalOne := by
  have hi : decodeLiteral integerOne = some (.integer 1) := by decide
  have hd : decodeLiteral decimalOne = some (.integer 1) := by decide
  have hr : decodeLiteral rationalOne = some (.integer 1) := by decide
  exact ⟨(literal_value_eq_iff i hi hd).mpr rfl,(literal_value_eq_iff i hi hr).mpr rfl⟩

theorem mixed_scores_satisfiable : Satisfiable datatypeMap (mixedScoreOntology "2/2") := by
  apply scoreAssertions_satisfiable
  intro l hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl <;> decide

theorem mixed_scores_inconsistent : ¬ Satisfiable datatypeMap (mixedScoreOntology "1/3") := by
  have h₁ : decodeLiteral integerOne = some (.integer 1) := by decide
  have h₂ : decodeLiteral ⟨"1/3",owlRational⟩ = some (.number (mkRat 1 3)) := by decide
  exact functional_data_conflict
    (r := hasScore) (a := subject) (l := integerOne) (m := ⟨"1/3",owlRational⟩)
    (by simp [mixedScoreOntology,scoreAssertions]) (by simp [mixedScoreOntology,scoreAssertions])
    (by simp [mixedScoreOntology,scoreAssertions]) h₁ h₂
    (show (Value.integer 1 : Value) ≠ .number (mkRat 1 3) by decide)

theorem checked_equal_scores : Satisfiable datatypeMap (mixedScoreOntology "2/2") :=
  DataCertificates.solve_sound (cert := .model [⟨hasScore,"urn:example:submission",.integer 1⟩])
    (by decide)

theorem checked_distinct_scores : ¬ Satisfiable datatypeMap (mixedScoreOntology "1/3") :=
  DataCertificates.solve_sound (cert := .functionalClash 0 1 3) (by decide)

example : DataCertificates.check (mixedScoreOntology "2/2") (.functionalClash 0 1 3) = false :=
  by decide

example : DataCertificates.check (mixedScoreOntology "1/3") (.functionalClash 1 0 3) = false :=
  by decide

example : DataCertificates.check (mixedScoreOntology "1/3") (.functionalClash 0 1 9) = false :=
  by decide

example : DataCertificates.check (mixedScoreOntology "1/3") (.model []) = false := by decide

example : DataCertificates.solve [.dataAssertion hasScore subject ⟨"1/0",owlRational⟩] =
    .unsupported := by decide

example : DataCertificates.solve [.dataPropertyRange hasScore (.datatype "urn:example:UnknownDatatype")] =
    .unsupported := by decide

example : DataCertificates.check [] (.model [⟨bottomDataProperty,"urn:example:submission",.integer 1⟩]) =
    false := by decide

private def restrictedScore := DataRange.intersection
  (.restriction (xsd "integer") [minimumZero])
  (.complement (.oneOf [integerOne]))

example : DataCertificates.solve [.dataPropertyRange hasScore restrictedScore,
    .dataAssertion hasScore subject decimalOne] = .checked (.rangeClash 0 1) := by decide

example : DataCertificates.solve [.dataAssertion hasScore subject integerOne,
    .negativeDataAssertion hasScore subject rationalOne] = .checked (.assertionClash 0 1) := by decide

private def closedIntRange (lo hi : String) : DataRange :=
  .restriction (xsd "integer") [
    ⟨xsd "minInclusive", ⟨lo, xsd "integer"⟩⟩,
    ⟨xsd "maxInclusive", ⟨hi, xsd "integer"⟩⟩
  ]

def requiredScoreOntology (lo hi : String) : Ontology :=
  [.classAssertion (.dataSome hasScore (closedIntRange lo hi)) subject]

theorem checked_required_score_valid :
    Satisfiable datatypeMap (requiredScoreOntology "0" "100") :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .integer 0⟩])
    (by decide)

theorem checked_required_score_empty :
    ¬ Satisfiable datatypeMap (requiredScoreOntology "100" "0") :=
  DataCertificates.solve_sound (cert := .emptyRangeClash 0 100 0) (by decide)

theorem checked_required_score_singleton :
    Satisfiable datatypeMap (requiredScoreOntology "42" "42") :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .integer 42⟩])
    (by decide)

theorem range_evidence_inhabitant (i : Interpretation datatypeMap) :
    dataHolds i (i.embedValue (.integer 50)) (closedIntRange "0" "100") :=
  DataRanges.checkRangeEvidence_sound (e := .witness (.integer 50)) (by decide) i

theorem range_evidence_empty (i : Interpretation datatypeMap) (y : i.Data) :
    ¬ dataHolds i y (closedIntRange "100" "0") :=
  DataRanges.checkRangeEvidence_sound (e := .emptyIntInterval 100 0) (by decide) i y

example : DataCertificates.check (requiredScoreOntology "0" "100") (.model []) = false := by decide
example : DataCertificates.check (requiredScoreOntology "0" "100")
    (.model [⟨hasScore, "urn:example:submission", .integer 101⟩]) = false := by decide
example : DataCertificates.check (requiredScoreOntology "0" "100")
    (.emptyRangeClash 0 100 0) = false := by decide
example : DataCertificates.check (requiredScoreOntology "42" "42")
    (.model [⟨hasScore, "urn:example:submission", .integer 41⟩]) = false := by decide
example : DataCertificates.check (requiredScoreOntology "50" "0")
    (.emptyRangeClash 0 100 0) = false := by decide
example : DataCertificates.check (requiredScoreOntology "100" "0")
    (.emptyRangeClash 1 100 0) = false := by decide

/-- Invalid bounds and unsupported existential ranges are explicitly rejected. -/
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore (closedIntRange "abc" "100")) subject] =
    .unsupported := by decide
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore
      (.restriction (xsd "integer") [
        ⟨xsd "minInclusive", ⟨"1.5", xsd "decimal"⟩⟩,
        ⟨xsd "maxInclusive", ⟨"100", xsd "integer"⟩⟩])) subject] =
    .unsupported := by decide
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore
      (.restriction (xsd "integer") [
        ⟨xsd "minInclusive", ⟨"128", xsd "byte"⟩⟩,
        ⟨xsd "maxInclusive", ⟨"100", xsd "integer"⟩⟩])) subject] =
    .unsupported := by decide
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore (.datatype (xsd "integer"))) subject] =
    .checked (.model [⟨hasScore, "urn:example:submission", .integer 0⟩]) := by decide
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore (.datatype "urn:example:UnknownDatatype")) subject] =
    .unsupported := by decide

/-- Decimal, rational, and Boolean existentials, data cardinality, and HasKey. -/
theorem checked_decimal_open_interval_valid :
    Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "decimal") [
          ⟨xsd "minExclusive", ⟨"0", xsd "integer"⟩⟩,
          ⟨xsd "maxExclusive", ⟨"1", xsd "integer"⟩⟩])) subject] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .number (mkRat 1 8)⟩]) (by decide)

theorem checked_decimal_one_third_empty :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "decimal") [
          ⟨xsd "minInclusive", ⟨"1/3", owlRational⟩⟩,
          ⟨xsd "maxInclusive", ⟨"1/3", owlRational⟩⟩])) subject] :=
  DataCertificates.solve_sound (cert := .emptySolvedRangeClash 0) (by decide)

theorem checked_rational_half_open_empty :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction owlRational [
          ⟨xsd "minExclusive", ⟨"1", xsd "integer"⟩⟩,
          ⟨xsd "maxInclusive", ⟨"1", xsd "integer"⟩⟩])) subject] :=
  DataCertificates.solve_sound (cert := .emptySolvedRangeClash 0) (by decide)

theorem checked_boolean_min3_inconsistent :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataMin 3 hasScore (.datatype (xsd "boolean"))) subject] :=
  DataCertificates.solve_sound (cert := .dataMinFiniteClash 0) (by decide)

theorem checked_int_interval_min4_inconsistent :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataMin 4 hasScore (closedIntRange "1" "3")) subject] :=
  DataCertificates.solve_sound (cert := .dataMinFiniteClash 0) (by decide)

theorem checked_int_interval_exact3_satisfiable :
    Satisfiable datatypeMap [
      .classAssertion (.dataExact 3 hasScore (closedIntRange "1" "3")) subject] :=
  DataCertificates.solve_sound
    (cert := .model [
      ⟨hasScore, "urn:example:submission", .integer 1⟩,
      ⟨hasScore, "urn:example:submission", .integer 2⟩,
      ⟨hasScore, "urn:example:submission", .integer 3⟩]) (by decide)

theorem checked_data_max_clash :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataMax 1 hasScore (.datatype (xsd "integer"))) subject,
      .dataAssertion hasScore subject ⟨"1", xsd "integer"⟩,
      .dataAssertion hasScore subject ⟨"2", xsd "integer"⟩] :=
  DataCertificates.solve_sound (cert := .dataMaxClash 0 [1, 2]) (by decide)

def otherSubject : Individual := .named "urn:example:submission2"

theorem checked_key_clash_cross_datatype :
    ¬ Satisfiable datatypeMap [
      .hasKey (.named "urn:example:Submission") [] [hasScore],
      .differentIndividuals [subject, otherSubject],
      .classAssertion (.named "urn:example:Submission") subject,
      .classAssertion (.named "urn:example:Submission") otherSubject,
      .dataAssertion hasScore subject integerOne,
      .dataAssertion hasScore otherSubject decimalOne] :=
  DataCertificates.solve_sound (cert := .keyClash 0 1 2 3 [(4, 5)]) (by decide)

theorem checked_key_distinct_values_satisfiable :
    Satisfiable datatypeMap [
      .hasKey (.named "urn:example:Submission") [] [hasScore],
      .differentIndividuals [subject, otherSubject],
      .classAssertion (.named "urn:example:Submission") subject,
      .classAssertion (.named "urn:example:Submission") otherSubject,
      .dataAssertion hasScore subject integerOne,
      .dataAssertion hasScore otherSubject ⟨"2.0", xsd "decimal"⟩] :=
  DataCertificates.solve_sound
    (cert := .model
      [⟨hasScore, "urn:example:submission", .integer 1⟩,
       ⟨hasScore, "urn:example:submission2", .integer 2⟩]
      [⟨"urn:example:Submission", "urn:example:submission"⟩,
       ⟨"urn:example:Submission", "urn:example:submission2"⟩]) (by decide)

/-- Open/exclusive bounds and integer subtypes are solved and certified. -/
theorem checked_open_int_interval_empty :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "integer") [
          ⟨xsd "minExclusive", ⟨"5", xsd "integer"⟩⟩,
          ⟨xsd "maxExclusive", ⟨"6", xsd "integer"⟩⟩])) subject] :=
  DataCertificates.solve_sound (cert := .emptyRangeClash 0 6 5) (by decide)

theorem checked_positive_integer_max_zero_empty :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "positiveInteger") [
          ⟨xsd "maxInclusive", ⟨"0", xsd "integer"⟩⟩])) subject] :=
  DataCertificates.solve_sound (cert := .emptyRangeClash 0 1 0) (by decide)

/-- Compatible mixtures are checked against every axiom, including witness selection
    that respects ranges and avoids negative assertions. -/
example : DataCertificates.solve [
    .classAssertion (.dataSome hasScore (closedIntRange "0" "100")) subject,
    .functionalDataProperty hasScore,
    .dataPropertyRange hasScore (.datatype (xsd "integer"))] =
    .checked (.model [⟨hasScore, "urn:example:submission", .integer 0⟩]) := by decide

theorem checked_existential_avoids_negative :
    Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore (closedIntRange "0" "2")) subject,
      .negativeDataAssertion hasScore subject ⟨"0", xsd "integer"⟩] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .integer 1⟩]) (by decide)

theorem checked_existential_range_clash :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore (closedIntRange "0" "100")) subject,
      .dataPropertyRange hasScore (closedIntRange "200" "300")] :=
  DataCertificates.solve_sound (cert := .existentialRangeClash 0 1 200 100) (by decide)

theorem checked_functional_existential_clash :
    ¬ Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .classAssertion (.dataSome hasScore (closedIntRange "0" "100")) subject,
      .dataAssertion hasScore subject ⟨"150", xsd "integer"⟩] :=
  DataCertificates.solve_sound (cert := .functionalExistentialClash 0 1 2) (by decide)

theorem checked_negative_existential_clash :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore (closedIntRange "0" "1")) subject,
      .negativeDataAssertion hasScore subject ⟨"0", xsd "integer"⟩,
      .negativeDataAssertion hasScore subject ⟨"1", xsd "integer"⟩] :=
  DataCertificates.solve_sound (cert := .negativeExistentialClash 0 [1, 2] 0 1) (by decide)

/-- Subclass data existentials: empty range alone leaves the class empty (satisfiable);
    adding a class membership premise produces a checked clash. -/
def submissionClass : IRI := "urn:example:Submission"

theorem checked_subclass_empty_range_vacuously_satisfiable :
    Satisfiable datatypeMap [
      .subClassOf (.named submissionClass) (.dataSome hasScore (closedIntRange "100" "0"))] :=
  DataCertificates.solve_sound (cert := .model [] []) (by decide)

theorem checked_subclass_inhabited_satisfiable :
    Satisfiable datatypeMap [
      .subClassOf (.named submissionClass) (.dataSome hasScore (closedIntRange "0" "100")),
      .classAssertion (.named submissionClass) subject] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .integer 0⟩]
      [⟨submissionClass, "urn:example:submission"⟩]) (by decide)

theorem checked_subclass_empty_range_clash :
    ¬ Satisfiable datatypeMap [
      .subClassOf (.named submissionClass) (.dataSome hasScore (closedIntRange "100" "0")),
      .classAssertion (.named submissionClass) subject] :=
  DataCertificates.solve_sound (cert := .subclassEmptyRangeClash 0 1 100 0) (by decide)

/-- SolvedRange disjointness resolves [0, 100] vs oneOf [200] directly! -/
theorem checked_existential_vs_oneOf_clash :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore (closedIntRange "0" "100")) subject,
      .dataPropertyRange hasScore (.oneOf [⟨"200", xsd "integer"⟩])] :=
  DataCertificates.solve_sound (cert := .existentialSolvedRangeClash 0 1) (by decide)

/-- Strings, length facets, cross-family disjointness, and acyclic DatatypeDefinition. -/
theorem checked_string_length_valid :
    Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "string") [
          ⟨xsd "minLength", ⟨"3", xsd "nonNegativeInteger"⟩⟩,
          ⟨xsd "maxLength", ⟨"5", xsd "nonNegativeInteger"⟩⟩])) subject] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .string "aaa"⟩]) (by decide)

theorem checked_string_length_empty :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore
        (.restriction (xsd "string") [
          ⟨xsd "minLength", ⟨"5", xsd "nonNegativeInteger"⟩⟩,
          ⟨xsd "maxLength", ⟨"3", xsd "nonNegativeInteger"⟩⟩])) subject] :=
  DataCertificates.solve_sound (cert := .emptySolvedRangeClash 0) (by decide)

theorem checked_string_vs_integer_disjoint :
    ¬ Satisfiable datatypeMap [
      .classAssertion (.dataSome hasScore (.datatype (xsd "string"))) subject,
      .dataPropertyRange hasScore (.datatype (xsd "integer"))] :=
  DataCertificates.solve_sound (cert := .existentialSolvedRangeClash 0 1) (by decide)

def validScoreType : IRI := "urn:example:ValidScore"
def passingScoreType : IRI := "urn:example:PassingScore"

theorem checked_datatype_definition_chain_satisfiable :
    Satisfiable datatypeMap [
      .datatypeDefinition validScoreType (closedIntRange "0" "100"),
      .datatypeDefinition passingScoreType
        (.intersection (.datatype validScoreType)
          (.restriction (xsd "integer") [⟨xsd "minInclusive", ⟨"60", xsd "integer"⟩⟩])),
      .classAssertion (.dataSome hasScore (.datatype passingScoreType)) subject] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .integer 60⟩]) (by decide)

theorem checked_datatype_definition_clash :
    ¬ Satisfiable datatypeMap [
      .datatypeDefinition validScoreType (closedIntRange "0" "100"),
      .dataPropertyRange hasScore (.datatype validScoreType),
      .dataAssertion hasScore subject ⟨"150", xsd "integer"⟩] :=
  DataCertificates.solve_sound (cert := .rangeClash 1 2) (by decide)

/-- Cyclic datatype definitions are explicitly rejected as unsupported. -/
example : DataCertificates.solve [
    .datatypeDefinition validScoreType (.datatype passingScoreType),
    .datatypeDefinition passingScoreType (.datatype validScoreType)] = .unsupported := by decide

/-- Full OWL 2 DL datatype map: float/double, PlainLiteral & string subtypes,
    hexBinary/base64Binary, dateTime/dateTimeStamp, anyURI, owl:real, XMLLiteral. -/
theorem checked_float_signed_zeros_distinct :
    ¬ Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject ⟨"-0.0", xsd "float"⟩,
      .dataAssertion hasScore subject ⟨"0.0", xsd "float"⟩] :=
  DataCertificates.solve_sound (cert := .functionalClash 0 1 2) (by decide)

theorem checked_float_double_disjoint :
    ¬ Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject ⟨"1.0", xsd "float"⟩,
      .dataAssertion hasScore subject ⟨"1.0", xsd "double"⟩] :=
  DataCertificates.solve_sound (cert := .functionalClash 0 1 2) (by decide +kernel)

theorem checked_float_nan_fails_order_facet :
    ¬ Satisfiable datatypeMap [
      .dataPropertyRange hasScore (.restriction (xsd "float") [⟨xsd "minInclusive", ⟨"-INF", xsd "float"⟩⟩]),
      .dataAssertion hasScore subject ⟨"NaN", xsd "float"⟩] :=
  DataCertificates.solve_sound (cert := .rangeClash 0 1) (by decide)

#guard decodeLiteral ⟨"0.1", xsd "float"⟩ ==
  some (.float (.finite (mkRat 13421773 134217728)))
#guard decodeLiteral ⟨"0.1", xsd "double"⟩ ==
  some (.double (.finite (mkRat 3602879701896397 36028797018963968)))
#guard decodeLiteral ⟨"16777217", xsd "float"⟩ ==
  decodeLiteral ⟨"16777216", xsd "float"⟩
#guard decodeLiteral ⟨"16777217", xsd "double"⟩ !=
  decodeLiteral ⟨"16777216", xsd "double"⟩
#guard decodeLiteral ⟨"1.401298464324817e-45", xsd "float"⟩ ==
  some (.float (.finite (mkRat 1 (2 ^ 149))))
#guard decodeLiteral ⟨"-1e-1000", xsd "float"⟩ == some (.float .negZero)
#guard decodeLiteral ⟨"1e39", xsd "float"⟩ == some (.float .posInf)

theorem checked_plain_literal_equals_string :
    Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject ⟨"hello", xsd "string"⟩,
      .dataAssertion hasScore subject ⟨"hello@", rdf "PlainLiteral"⟩] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .string "hello"⟩]) (by decide)

theorem checked_plain_literal_lang_case_insensitive :
    Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject ⟨"hello@EN", rdf "PlainLiteral"⟩,
      .dataAssertion hasScore subject ⟨"hello@en", rdf "PlainLiteral"⟩] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .plainLiteral "hello" "en"⟩]) (by decide)

example : decodeLiteral ⟨"a  b", xsd "token"⟩ = none := by decide
example : decodeLiteral ⟨"a:b", xsd "NCName"⟩ = none := by decide
example : (decodeLiteral ⟨"a:b", xsd "Name"⟩).isSome = true := by decide

theorem checked_hex_binary_case_insensitive :
    Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject ⟨"0a1B", xsd "hexBinary"⟩,
      .dataAssertion hasScore subject ⟨"0A1b", xsd "hexBinary"⟩] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .hexBinary [10, 27]⟩]) (by decide)

theorem checked_base64_length_facet :
    Satisfiable datatypeMap [
      .dataPropertyRange hasScore (.restriction (xsd "base64Binary") [
        ⟨xsd "length", ⟨"3", xsd "nonNegativeInteger"⟩⟩]),
      .dataAssertion hasScore subject ⟨"AQID", xsd "base64Binary"⟩] :=
  DataCertificates.solve_sound
    (cert := .model [⟨hasScore, "urn:example:submission", .base64Binary [1, 2, 3]⟩]) (by decide)

private def midnightUTC : Literal := ⟨"1970-01-01T00:00:00Z", xsd "dateTimeStamp"⟩
private def midnightOffset : Literal := ⟨"1970-01-01T00:01:00+00:01", xsd "dateTimeStamp"⟩

set_option maxRecDepth 4096 in
theorem checked_datetime_offset_clash :
    ¬ Satisfiable datatypeMap [
      .functionalDataProperty hasScore,
      .dataAssertion hasScore subject midnightUTC,
      .dataAssertion hasScore subject midnightOffset] := by
  rintro ⟨i, assign, h⟩
  let j := i.withAnonymous assign
  have hfunc := h (.functionalDataProperty hasScore) (by simp)
  have h1 := h (.dataAssertion hasScore subject midnightUTC) (by simp)
  have h2 := h (.dataAssertion hasScore subject midnightOffset) (by simp)
  have he := hfunc (j.individuals subject) (j.literalValue midnightUTC)
    (j.literalValue midnightOffset) h1 h2
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (show (decodeLiteral midnightUTC).isSome = true from rfl)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (show (decodeLiteral midnightOffset).isSome = true from rfl)
  rw [j.lexicalAgreement midnightUTC a ha, j.lexicalAgreement midnightOffset b hb] at he
  let offset : Option Value → Option (Option Int)
    | some (.dateTime dt) => some dt.timezoneOffset
    | _ => none
  have hne : offset (decodeLiteral midnightUTC) ≠ offset (decodeLiteral midnightOffset) := by
    change some (some (0 : Int)) ≠ some (some 60)
    decide
  apply hne
  rw [ha, hb, j.embedValue_injective he]

#guard ((parseDateTime true "1970-01-01T12:00:00Z").map DateTimeVal.epochSeconds) ==
    ((parseDateTime true "1970-01-01T14:00:00+02:00").map DateTimeVal.epochSeconds)

#guard parseDateTime true "1970-01-01T12:00:00Z" ==
    parseDateTime true "1970-01-01T12:00:00+00:00"

#guard (parseDateTime false "0000-02-29T00:00:00").isSome
#guard (parseDateTime false "02026-01-01T00:00:00").isNone

#guard (parseDateTime true "1970-01-01T12:00:00Z").any
    (fun a => (parseDateTime false "1970-01-01T12:00:00").any (fun b => !a.le b && !b.le a))

#guard (parseDateTime true "1970-01-01T12:00:00Z").any
    (fun a => (parseDateTime false "1970-01-02T12:00:00").any (a.lt ·))

theorem checked_datetime_order_clash :
    ¬ Satisfiable datatypeMap [
      .dataPropertyRange hasScore (.restriction (xsd "dateTimeStamp") [
        ⟨xsd "minInclusive", ⟨"2026-01-01T15:00:00Z", xsd "dateTimeStamp"⟩⟩]),
      .dataAssertion hasScore subject ⟨"2026-01-01T14:00:00Z", xsd "dateTimeStamp"⟩] :=
  DataCertificates.check_sound (cert := .rangeClash 0 1) (by decide)

example : decodeLiteral ⟨"2026-01-01T12:00:00", xsd "dateTimeStamp"⟩ = none := by decide
example : (decodeLiteral ⟨"2026-01-01T12:00:00", xsd "dateTime"⟩).isSome = true := by decide
example : decodeLiteral ⟨"1", owlReal⟩ = none := by decide

end SabrinaTests.OWL2Datatypes
