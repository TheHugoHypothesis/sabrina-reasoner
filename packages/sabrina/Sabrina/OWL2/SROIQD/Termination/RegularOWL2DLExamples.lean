import Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLDecision

/-! Live fuel-free regressions for unified combined regular OWL 2 DL admission
(`RegularOWL2DLDecision`), exercising `checkAcyclicOWL2DLInput`,
`decideAcyclicOWL2DLReal`, `decideRealProblem?`, `decideRealOntology?`,
`decideWithWiderDataRanges?`, and `decideRealQuery?` across cyclic GCIs,
qualified cardinalities, nominals, mixed object/data `HasKey`, irrational
`owl:real`, `xsd:float` order facets, `xsd:pattern`, `rdf:langRange`,
`owl:topObjectProperty` (class restrictions, unary rules, top-headed chains,
and top-body chains), `owl:bottomObjectProperty` (including the `⊥`-alias cycle
edge case), `owl:topDataProperty`, `owl:bottomDataProperty`, equal-rank unary
cycles through composite heads, and rankless/non-simple rejections. -/

namespace Sabrina.OWL2.RoleHierarchy.UnifiedExamples

open Sabrina.OWL2
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.ExactQuery
open Sabrina.OWL2.RoleHierarchy.Unified
open Sabrina.ALC (InclusionVerdict)

private def pfx : String :=
  "Prefix(:=<http://example.org/>)\n" ++
  "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n" ++
  "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n" ++
  "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n" ++
  "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"

private def parseAndNorm (body : String) : Option (FunctionalSyntax.ParsedDocument × Problem) :=
  match FunctionalSyntax.parseDocument (pfx ++ "Ontology(\n" ++ body ++ "\n)") with
  | .ok doc =>
    match Normalize.normalizeWithDefs doc.ontology with
    | some (_, p) => some (doc, p)
    | none => none
  | .error _ => none

private def checkUnified (body : String) (expectedSat : Bool) : Bool :=
  match parseAndNorm body with
  | none => false
  | some (doc, p) =>
    if h : checkAcyclicOWL2DLInput p = true then
      let ha : AcyclicOWL2DLInput p := (checkAcyclicOWL2DLInput_iff p).mp h
      decideAcyclicOWL2DLReal p ha == expectedSat &&
      decideWithWiderDataRanges? doc.ontology == some expectedSat
    else
      false

private def checkRejected (body : String) : Bool :=
  match parseAndNorm body with
  | none => false
  | some (_, p) => checkAcyclicOWL2DLInput p == false

/-! ### 1. Combined regular OWL 2 DL: cyclic GCI + qualified cardinality + wider datatypes + built-in properties -/

-- Cyclic GCI + qualified cardinality + irrational owl:real + owl:topDataProperty + owl:bottomDataProperty
private def cyclicRealBuiltInBody : String := "
  Declaration(Class(:Node))
  Declaration(ObjectProperty(:next))
  Declaration(DataProperty(:meas))
  Declaration(NamedIndividual(:n0))
  SubClassOf(:Node ObjectSomeValuesFrom(:next :Node))
  SubClassOf(:Node ObjectMinCardinality(1 :next :Node))
  ClassAssertion(:Node :n0)
  SubClassOf(:Node DataSomeValuesFrom(:meas DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
  SubClassOf(:Node DataSomeValuesFrom(owl:topDataProperty xsd:integer))
  SubClassOf(DataSomeValuesFrom(owl:bottomDataProperty xsd:string) owl:Nothing)
"

#guard checkUnified cyclicRealBuiltInBody true

private def cyclicRealUnsatBody : String := cyclicRealBuiltInBody ++ "
  SubClassOf(:Node DataAllValuesFrom(:meas owl:rational))
"

#guard checkUnified cyclicRealUnsatBody false

-- Combined regular role chains + top-headed chain + top-body chain + universal restriction + bottom object property
private def topChainAndRestrictionBody : String := "
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:p))
  Declaration(ObjectProperty(:q))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:viaTop))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
  SubObjectPropertyOf(ObjectPropertyChain(:r :p) owl:topObjectProperty)
  SubObjectPropertyOf(ObjectPropertyChain(:p owl:topObjectProperty :q) :viaTop)
  SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))
  SubClassOf(ObjectSomeValuesFrom(owl:bottomObjectProperty :A) owl:Nothing)
  ClassAssertion(:A :a)
  ObjectPropertyAssertion(:p :a :a)
  ObjectPropertyAssertion(:q :b :b)
"

#guard checkUnified topChainAndRestrictionBody true

private def topChainUnsatBody : String := topChainAndRestrictionBody ++ "
  NegativeObjectPropertyAssertion(:viaTop :a :b)
"

#guard checkUnified topChainUnsatBody false

-- Mixed object/data HasKey + nominals + xsd:float order facets + xsd:pattern + rdf:langRange
private def mixedKeyFacetsBody : String := "
  Declaration(Class(:Sensor))
  Declaration(ObjectProperty(:link))
  Declaration(DataProperty(:temp))
  Declaration(DataProperty(:code))
  Declaration(DataProperty(:lbl))
  Declaration(NamedIndividual(:s0))
  Declaration(NamedIndividual(:s1))
  HasKey(:Sensor (:link) (:code))
  SubClassOf(ObjectOneOf(:s0 :s1) :Sensor)
  ClassAssertion(:Sensor :s0)
  SubClassOf(:Sensor DataSomeValuesFrom(:temp DatatypeRestriction(xsd:float xsd:minInclusive \"-0.0\"^^xsd:float xsd:maxInclusive \"0.0\"^^xsd:float)))
  SubClassOf(:Sensor DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern \"a|b\"^^xsd:string)))
  SubClassOf(:Sensor DataSomeValuesFrom(:lbl DatatypeRestriction(rdf:PlainLiteral rdf:langRange \"en\"^^xsd:string)))
"

#guard checkUnified mixedKeyFacetsBody true

private def mixedKeyFacetsUnsatBody : String := mixedKeyFacetsBody ++ "
  ClassAssertion(:Sensor :s1)
  DifferentIndividuals(:s0 :s1)
  ObjectPropertyAssertion(:link :s0 :s0)
  ObjectPropertyAssertion(:link :s1 :s0)
  DataPropertyAssertion(:code :s0 \"a\"^^xsd:string)
  DataPropertyAssertion(:code :s1 \"a\"^^xsd:string)
"

#guard checkUnified mixedKeyFacetsUnsatBody false

/-! ### 2. Bottom-property alias edge case (`a ⊑ b ⊑ ⊥ ⊑ a` with `c ∘ a ∘ d ⊑ b`) -/

private def bottomAliasEdgeBody : String := "
  Declaration(ObjectProperty(:a))
  Declaration(ObjectProperty(:b))
  Declaration(ObjectProperty(:c))
  Declaration(ObjectProperty(:d))
  Declaration(NamedIndividual(:x))
  Declaration(NamedIndividual(:y))
  SubObjectPropertyOf(:a :b)
  SubObjectPropertyOf(:b owl:bottomObjectProperty)
  SubObjectPropertyOf(owl:bottomObjectProperty :a)
  SubObjectPropertyOf(ObjectPropertyChain(:c :a :d) :b)
  ObjectPropertyAssertion(:c :x :y)
"

#guard checkUnified bottomAliasEdgeBody true

private def bottomAliasUnsatBody : String := bottomAliasEdgeBody ++ "
  ObjectPropertyAssertion(:b :x :y)
"

#guard checkUnified bottomAliasUnsatBody false

/-! ### 3. Equal-rank unary cycle through a composite head (`AcyclicOWL2DLInput` strictly beyond `WeaklyRegular`) -/

private def equalRankCycleBody : String := "
  Declaration(ObjectProperty(:a))
  Declaration(ObjectProperty(:b))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  Declaration(NamedIndividual(:x))
  Declaration(NamedIndividual(:y))
  Declaration(NamedIndividual(:z))
  SubObjectPropertyOf(:r :s)
  SubObjectPropertyOf(:s :r)
  SubObjectPropertyOf(ObjectPropertyChain(:a :b) :r)
  ObjectPropertyAssertion(:a :x :y)
  ObjectPropertyAssertion(:b :y :z)
"

#guard checkUnified equalRankCycleBody true

private def equalRankCycleUnsatBody : String := equalRankCycleBody ++ "
  NegativeObjectPropertyAssertion(:s :x :z)
"

#guard checkUnified equalRankCycleUnsatBody false

/-! ### 4. Rejections of rankless hierarchies and non-simple cardinalities -/

-- Converse-square rankless chain: r⁻ ∘ r⁻ ⊑ r
#guard checkRejected "
  Declaration(ObjectProperty(:r))
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
"

-- Mutually recursive rankless chains: r ∘ s ⊑ s and s ∘ r ⊑ r
#guard checkRejected "
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubObjectPropertyOf(ObjectPropertyChain(:r :s) :s)
  SubObjectPropertyOf(ObjectPropertyChain(:s :r) :r)
"

-- Non-simple qualified cardinality over owl:topObjectProperty
#guard checkRejected "
  Declaration(Class(:A))
  SubClassOf(:A ObjectMinCardinality(2 owl:topObjectProperty :A))
"

-- Non-simple qualified cardinality over a chain head
#guard checkRejected "
  Declaration(Class(:A))
  Declaration(ObjectProperty(:p))
  Declaration(ObjectProperty(:q))
  Declaration(ObjectProperty(:r))
  SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
  SubClassOf(:A ObjectMinCardinality(1 :r :A))
"

/-! ### 5. Total four-way query entailment over unified regular OWL 2 DL -/

private def checkUnifiedQuery (body query : String) (expected : InclusionVerdict) : Bool :=
  match parseAndNorm body with
  | some (doc, _) =>
    match parseSourceQuery doc.prefixes query with
    | some qAx => decideRealQuery? doc.ontology qAx == some expected
    | none => false
  | none => false

private def queryBody : String := "
  Declaration(Class(:Node))
  Declaration(DataProperty(:meas))
  Declaration(NamedIndividual(:n0))
  ClassAssertion(:Node :n0)
  SubClassOf(:Node DataSomeValuesFrom(:meas DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
  SubClassOf(:Node DataSomeValuesFrom(owl:topDataProperty xsd:integer))
  SubClassOf(DataSomeValuesFrom(owl:bottomDataProperty xsd:string) owl:Nothing)
"

private def queryBodyUnsat : String := queryBody ++ "
  SubClassOf(:Node DataAllValuesFrom(:meas owl:rational))
"

#guard checkUnifiedQuery queryBody
  "SubClassOf(:Node DataSomeValuesFrom(:meas owl:real))" .entailed

#guard checkUnifiedQuery queryBody
  "SubClassOf(:Node DataAllValuesFrom(:meas owl:rational))" .refuted

#guard checkUnifiedQuery queryBody
  "SubClassOf(:Node :Other)" .independent

#guard checkUnifiedQuery queryBodyUnsat
  "SubClassOf(:Node :Other)" .inconsistent

end Sabrina.OWL2.RoleHierarchy.UnifiedExamples
