import Sabrina.OWL2.SROIQD.Termination.SourceImportConformance

/-! Live fuel-free regressions for `owl:bottomDataProperty` and
`owl:topDataProperty` across both `decideWithWiderDataRanges?` (standard
`datatypeMap`) and `decideRealSourceClosure?` (Dedekind-cut `realDatatypeMap`). -/

namespace Sabrina.OWL2.SROIQD.Termination.BuiltInDataPropsExamples

open Sabrina.OWL2
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.SourceImport

private def pfx : String :=
  "Prefix(:=<http://example.org/>)\n" ++
  "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n" ++
  "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n" ++
  "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n" ++
  "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"

private def wrapOFN (body : String) : String :=
  pfx ++ "Ontology(\n" ++ body ++ "\n)"

private def checkBoth (body : String) (expected : Bool) : Bool :=
  let src := wrapOFN body
  let realOk := (decideRealSourceClosure? src []).map Prod.snd == some expected
  let stdOk := match FunctionalSyntax.parseDocument src with
    | .ok doc => decideWithWiderDataRanges? doc.ontology == some expected
    | .error _ => false
  realOk && stdOk

/-! ### 1. `owl:bottomDataProperty` in the wider & real solvers -/

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataExactCardinality(0 owl:bottomDataProperty owl:real) :a)
  NegativeDataPropertyAssertion(owl:bottomDataProperty :a \"1\"^^xsd:integer)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(1 owl:bottomDataProperty owl:real) :a)
" false

#guard checkBoth "
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(:p owl:bottomDataProperty)
  ClassAssertion(DataSomeValuesFrom(:p DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)) :a)
" false

#guard checkBoth "
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(:p owl:bottomDataProperty)
  ClassAssertion(DataMaxCardinality(0 :p owl:real) :a)
" true

#guard checkBoth "
  Declaration(Class(:A))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  HasKey(:A () (owl:bottomDataProperty))
  ClassAssertion(:A :a)
  ClassAssertion(:A :b)
  DifferentIndividuals(:a :b)
" true

/-! ### 2. `owl:topDataProperty` in class expressions (`dataSome`, `dataAll`, `dataMin`, `dataMax`, `dataValue`) -/

-- Nonempty irrational real range vs empty irrational real range
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataSomeValuesFrom(owl:topDataProperty
    DataIntersectionOf(owl:real DataComplementOf(owl:rational))) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataSomeValuesFrom(owl:topDataProperty
    DataIntersectionOf(
      DatatypeRestriction(owl:real xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"1\"^^xsd:integer)
      DataComplementOf(owl:rational))) :a)
" false

-- Disjoint regex patterns under owl:topDataProperty
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataSomeValuesFrom(owl:topDataProperty
    DataIntersectionOf(
      DatatypeRestriction(xsd:string xsd:pattern \"a.*\"^^xsd:string)
      DatatypeRestriction(xsd:string xsd:pattern \"b.*\"^^xsd:string))) :a)
" false

-- Universal restriction on owl:topDataProperty:
-- Fails for xsd:integer on an inhabited individual, succeeds on an empty class,
-- succeeds unconditionally for rdfs:Literal and tautologies.
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataAllValuesFrom(owl:topDataProperty xsd:integer) :a)
" false

#guard checkBoth "
  Declaration(Class(:Empty))
  SubClassOf(:Empty DataAllValuesFrom(owl:topDataProperty xsd:integer))
" true

#guard checkBoth "
  Declaration(Class(:Empty))
  Declaration(NamedIndividual(:a))
  SubClassOf(:Empty DataAllValuesFrom(owl:topDataProperty xsd:integer))
  ClassAssertion(:Empty :a)
" false

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataAllValuesFrom(owl:topDataProperty rdfs:Literal) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataAllValuesFrom(owl:topDataProperty
    DataUnionOf(xsd:integer DataComplementOf(xsd:integer))) :a)
" true

-- Exact finite cardinality on xsd:pattern via owl:topDataProperty
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(2 owl:topDataProperty
    DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(3 owl:topDataProperty
    DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)) :a)
" false

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMaxCardinality(2 owl:topDataProperty
    DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMaxCardinality(1 owl:topDataProperty
    DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)) :a)
" false

-- Exact finite cardinality on signed zeros of xsd:float via owl:topDataProperty
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataExactCardinality(2 owl:topDataProperty
    DatatypeRestriction(xsd:float xsd:minInclusive \"-0.0\"^^xsd:float xsd:maxInclusive \"0.0\"^^xsd:float)) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMaxCardinality(1 owl:topDataProperty
    DatatypeRestriction(xsd:float xsd:minInclusive \"-0.0\"^^xsd:float xsd:maxInclusive \"0.0\"^^xsd:float)) :a)
" false

-- Infinite ranges (irrational cuts & complements of built-in datatypes) preserve
-- constraints over values outside any finite witness set.
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(5 owl:topDataProperty
    DataIntersectionOf(owl:real DataComplementOf(owl:rational))) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMaxCardinality(5 owl:topDataProperty
    DataIntersectionOf(owl:real DataComplementOf(owl:rational))) :a)
" false

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMinCardinality(5 owl:topDataProperty
    DataComplementOf(xsd:integer)) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataMaxCardinality(5 owl:topDataProperty
    DataComplementOf(xsd:integer)) :a)
" false

-- DataHasValue on owl:topDataProperty
#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(DataHasValue(owl:topDataProperty \"42\"^^xsd:integer) :a)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  ClassAssertion(ObjectComplementOf(DataHasValue(owl:topDataProperty \"42\"^^xsd:integer)) :a)
" false

/-! ### 3. `owl:topDataProperty` in axioms, `HasKey`, assertions, and transitive closure -/

#guard checkBoth "
  DataPropertyRange(owl:topDataProperty xsd:string)
" false

#guard checkBoth "
  DataPropertyRange(owl:topDataProperty rdfs:Literal)
" true

#guard checkBoth "
  Declaration(Class(:C))
  Declaration(NamedIndividual(:a))
  DataPropertyDomain(owl:topDataProperty :C)
  ClassAssertion(ObjectComplementOf(:C) :a)
" false

#guard checkBoth "
  FunctionalDataProperty(owl:topDataProperty)
" false

#guard checkBoth "
  Declaration(DataProperty(:p))
  Declaration(NamedIndividual(:a))
  DisjointDataProperties(owl:topDataProperty :p)
  DataPropertyAssertion(:p :a \"1\"^^xsd:integer)
" false

#guard checkBoth "
  Declaration(DataProperty(:p))
  DisjointDataProperties(owl:topDataProperty :p)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  DataPropertyAssertion(owl:topDataProperty :a \"1\"^^xsd:integer)
" true

#guard checkBoth "
  Declaration(NamedIndividual(:a))
  NegativeDataPropertyAssertion(owl:topDataProperty :a \"1\"^^xsd:integer)
" false

#guard checkBoth "
  Declaration(Class(:A))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  HasKey(:A () (owl:topDataProperty))
  ClassAssertion(:A :a)
  ClassAssertion(:A :b)
  DifferentIndividuals(:a :b)
" false

-- Transitive universal data-property closure: topDataProperty ⊑ :p1 ⊑ :p2
#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  FunctionalDataProperty(:p2)
" false

#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  NegativeDataPropertyAssertion(:p2 :a \"hi\"^^xsd:string)
" false

#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  SubDataPropertyOf(:p2 owl:bottomDataProperty)
" false

#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  ClassAssertion(DataAllValuesFrom(:p2 xsd:boolean) :a)
" false

#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  ClassAssertion(DataMinCardinality(2 :p2 DatatypeRestriction(xsd:string xsd:pattern \"x|y\"^^xsd:string)) :a)
" true

#guard checkBoth "
  Declaration(DataProperty(:p1))
  Declaration(DataProperty(:p2))
  Declaration(NamedIndividual(:a))
  SubDataPropertyOf(owl:topDataProperty :p1)
  SubDataPropertyOf(:p1 :p2)
  ClassAssertion(DataMinCardinality(3 :p2 DatatypeRestriction(xsd:string xsd:pattern \"x|y\"^^xsd:string)) :a)
" false

end Sabrina.OWL2.SROIQD.Termination.BuiltInDataPropsExamples
