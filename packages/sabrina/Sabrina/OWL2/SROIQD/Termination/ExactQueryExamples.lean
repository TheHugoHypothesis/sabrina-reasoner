import Sabrina.OWL2.SROIQD.Termination.ExactQueryDecision

/-! Live fuel-free regressions for exact four-way query entailment across all
10 query axiom forms, all 4 verdicts (`entailed`, `refuted`, `independent`,
`inconsistent`), wider datatypes (`owl:real`, `xsd:float`, `xsd:dateTime`,
`xsd:pattern`, `rdf:langRange`), built-in data properties, `HasKey`, and
resolved finite imports. -/

namespace Sabrina.OWL2.SROIQD.Termination.ExactQueryExamples

open Sabrina.OWL2
open Sabrina.ALC (InclusionVerdict)
open Sabrina.OWL2.SROIQD.Termination.ExactQuery

private def pfx : String :=
  "Prefix(:=<http://example.org/>)\n" ++
  "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n" ++
  "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n" ++
  "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n" ++
  "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"

private def checkQuery (body query : String) (expected : InclusionVerdict)
    (lib : List (IRI × String) := []) : Bool :=
  let src := pfx ++ "Ontology(\n" ++ body ++ "\n)"
  let realOk := (decideRealSourceQuery? src query lib).map (fun r => r.2.2) == some expected
  let stdOk := (decideWiderSourceQuery? src query lib).map (fun r => r.2.2) == some expected
  realOk && stdOk

/-! ### 1. SubClassOf, EquivalentClasses, DisjointClasses over wider datatypes -/

-- Irrational owl:real range: SubClassOf(A, B) entailed, refuted, independent, inconsistent
#guard checkQuery "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:x))
  SubClassOf(:A DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
  SubClassOf(DataSomeValuesFrom(:x owl:real) :B)
" "SubClassOf(:A :B)" .entailed

#guard checkQuery "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:a))
  Declaration(DataProperty(:x))
  ClassAssertion(:A :a)
  ClassAssertion(DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))) :a)
  SubClassOf(:B DataAllValuesFrom(:x owl:rational))
" "SubClassOf(:A :B)" .refuted

#guard checkQuery "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:x))
  SubClassOf(:A DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
" "SubClassOf(:A :B)" .independent

#guard checkQuery "
  Declaration(NamedIndividual(:a))
  Declaration(DataProperty(:x))
  ClassAssertion(DataSomeValuesFrom(:x DataIntersectionOf(
    DatatypeRestriction(owl:real xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"1\"^^xsd:integer)
    DataComplementOf(owl:rational))) :a)
" "SubClassOf(:A :B)" .inconsistent

-- EquivalentClasses over xsd:pattern & xsd:string length facets
#guard checkQuery "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:code))
  EquivalentClasses(:A DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)))
  EquivalentClasses(:B DataSomeValuesFrom(:code DataOneOf(\"a\"^^xsd:string \"b\"^^xsd:string)))
" "EquivalentClasses(:A :B)" .entailed

#guard checkQuery "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:a))
  Declaration(DataProperty(:code))
  ClassAssertion(:A :a)
  ClassAssertion(DataAllValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern \"a\"^^xsd:string)) :a)
  SubClassOf(:B DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern \"b\"^^xsd:string)))
" "EquivalentClasses(:A :B)" .refuted

-- DisjointClasses over rdf:langRange
#guard checkQuery "
  Declaration(Class(:EnDoc))
  Declaration(Class(:FrDoc))
  Declaration(DataProperty(:label))
  FunctionalDataProperty(:label)
  SubClassOf(:EnDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string)))
  SubClassOf(:FrDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"fr\"^^xsd:string)))
" "DisjointClasses(:EnDoc :FrDoc)" .entailed

#guard checkQuery "
  Declaration(Class(:EnDoc))
  Declaration(Class(:EnUsDoc))
  Declaration(NamedIndividual(:d))
  Declaration(DataProperty(:label))
  ClassAssertion(:EnUsDoc :d)
  SubClassOf(:EnUsDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en-US\"^^xsd:string)))
  EquivalentClasses(:EnDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string)))
" "DisjointClasses(:EnDoc :EnUsDoc)" .refuted

/-! ### 2. Instance, Property Assertion, and Same/Different Individual Queries -/

-- ClassAssertion entailed via xsd:float order facets
#guard checkQuery "
  Declaration(Class(:ZeroSensor))
  Declaration(DataProperty(:v))
  Declaration(NamedIndividual(:s))
  EquivalentClasses(:ZeroSensor DataMinCardinality(2 :v
    DatatypeRestriction(xsd:float xsd:minInclusive \"-0.0\"^^xsd:float xsd:maxInclusive \"0.0\"^^xsd:float)))
  DataPropertyAssertion(:v :s \"-0.0\"^^xsd:float)
  DataPropertyAssertion(:v :s \"0.0\"^^xsd:float)
" "ClassAssertion(:ZeroSensor :s)" .entailed

-- ObjectPropertyAssertion & NegativeObjectPropertyAssertion
#guard checkQuery "
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  SubObjectPropertyOf(:r :s)
  ObjectPropertyAssertion(:r :a :b)
" "ObjectPropertyAssertion(:s :a :b)" .entailed

#guard checkQuery "
  Declaration(ObjectProperty(:r))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  ObjectPropertyAssertion(:r :a :b)
" "NegativeObjectPropertyAssertion(:r :a :b)" .refuted

-- DataPropertyAssertion & NegativeDataPropertyAssertion with owl:topDataProperty & owl:bottomDataProperty
#guard checkQuery "
  Declaration(NamedIndividual(:a))
" "DataPropertyAssertion(owl:topDataProperty :a \"42\"^^xsd:integer)" .entailed

#guard checkQuery "
  Declaration(NamedIndividual(:a))
" "NegativeDataPropertyAssertion(owl:bottomDataProperty :a \"42\"^^xsd:integer)" .entailed

#guard checkQuery "
  Declaration(NamedIndividual(:a))
" "DataPropertyAssertion(owl:bottomDataProperty :a \"42\"^^xsd:integer)" .refuted

-- SameIndividual & DifferentIndividuals forced by HasKey over singleton xsd:pattern
#guard checkQuery "
  Declaration(Class(:A))
  Declaration(DataProperty(:tag))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  HasKey(:A () (:tag))
  DataPropertyRange(:tag DatatypeRestriction(xsd:string xsd:pattern \"only\"^^xsd:string))
  ClassAssertion(:A :a)
  ClassAssertion(:A :b)
  ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :a)
  ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :b)
" "SameIndividual(:a :b)" .entailed

#guard checkQuery "
  Declaration(Class(:A))
  Declaration(DataProperty(:tag))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  HasKey(:A () (:tag))
  DataPropertyRange(:tag DatatypeRestriction(xsd:string xsd:pattern \"only\"^^xsd:string))
  ClassAssertion(:A :a)
  ClassAssertion(:A :b)
  ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :a)
  ClassAssertion(DataSomeValuesFrom(:tag xsd:string) :b)
" "DifferentIndividuals(:a :b)" .refuted

/-! ### 3. Query over resolved finite import closure with DatatypeDefinition -/

private def importedRangeDoc : String :=
  pfx ++ "Ontology(<http://example.org/codes>\n" ++
  "  Declaration(Datatype(:TwoLetter))\n" ++
  "  DatatypeDefinition(:TwoLetter DatatypeRestriction(xsd:string xsd:pattern \"[a-z]{2}\"^^xsd:string))\n" ++
  ")"

#guard checkQuery "
  Import(<http://example.org/codes>)
  Declaration(Class(:CodeItem))
  Declaration(DataProperty(:code))
  SubClassOf(:CodeItem DataSomeValuesFrom(:code :TwoLetter))
" "SubClassOf(:CodeItem DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:length \"2\"^^xsd:integer)))"
  .entailed [("http://example.org/codes", importedRangeDoc)]

end Sabrina.OWL2.SROIQD.Termination.ExactQueryExamples
