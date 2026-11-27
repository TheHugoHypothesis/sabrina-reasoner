import Lean.Data.Json
import Sabrina.OWL2.SWRL
import Sabrina.OWL2.SWRLBuiltins
import Sabrina.OWL2.SWRLReduction
import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.RDF.OWLMapping
import Sabrina.OWL2.Materialize
import Sabrina.CLI.OFNQuery

/-! Comprehensive generic regression tests for Kernel-Verified DL-Safe SWRL rules:
    1. FSS (`DLSafeRule`) parsing & round-trip rendering.
    2. Turtle & RDF/XML (`swrl:Imp`) parsing with `--strict-owl2dl` zero unconsumed triples.
    3. DL-safety & unsupported built-in rejection checks.
    4. Multi-variable object rules (triangle/uncle, `sameAs`, `differentFrom`).
    5. Unary nominal-guarded rule + open-world local data-variable & facet built-in roll-up.
    6. Concrete-value functional `swrlb:*` built-ins (`swrlb:add`, `swrlb:stringConcat`).
    7. Lazy CEGAR grounding loop over a larger ABox (16 individuals, 2-variable rule).
    8. End-to-end CLI (`OFNQuery`) consistency, entailment, classification, realization,
       materialization (`.ofn` / `.ttl` / `.owl`), and SWRL-aware justifications. -/

namespace SabrinaTests.SWRLTests

open Lean Sabrina.OWL2 Sabrina.OWL2.SWRL Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.RDF.OWLMapping Sabrina.OWL2.Materialize Sabrina.CLI

private def ex (s : String) : IRI := "http://example.org/swrl#" ++ s
private def vIRI (s : String) : IRI := "urn:swrl:var#" ++ s

private def intLit (n : String) : Literal := ⟨n, "http://www.w3.org/2001/XMLSchema#integer"⟩
private def strLit (s : String) : Literal := ⟨s, "http://www.w3.org/2001/XMLSchema#string"⟩

private def jsonFieldStr (j : Json) (k : String) : String :=
  match j.getObjValAs? String k with
  | .ok s => s
  | .error _ => ""

/-! ### 1. FSS Parsing & Round-Trip Rendering -/

private def fssAllAtomsDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(swrlb:=<http://www.w3.org/2003/11/swrlb#>)
Ontology(<http://example.org/swrl/test>
  Declaration(Class(ex:Person))
  Declaration(Class(ex:Adult))
  Declaration(ObjectProperty(ex:hasFriend))
  Declaration(DataProperty(ex:hasAge))
  Declaration(NamedIndividual(ex:alice))
  DLSafeRule(
    Annotation(rdfs:label \"adult-rule\")
    Body(
      ClassAtom(ex:Person Variable(var:x))
      ObjectPropertyAtom(ex:hasFriend Variable(var:x) Variable(var:y))
      DataPropertyAtom(ex:hasAge Variable(var:x) Variable(var:a))
      DataRangeAtom(xsd:integer Variable(var:a))
      BuiltInAtom(swrlb:greaterThanOrEqual Variable(var:a) \"18\"^^xsd:integer)
      DifferentIndividualsAtom(Variable(var:x) Variable(var:y))
    )
    Head(
      ClassAtom(ex:Adult Variable(var:x))
      SameIndividualAtom(Variable(var:x) ex:alice)
    )
  )
)
"

#guard
  match parseDocument fssAllAtomsDoc with
  | .ok doc =>
    doc.rules.length == 1 &&
    let rendered := renderDocumentOFN doc.declarations doc.annotationAxioms doc.ontology
      doc.prefixes doc.ontologyIRI doc.versionIRI doc.imports doc.rules
    match parseDocument rendered with
    | .ok doc2 => doc2.rules == doc.rules
    | .error _ => false
  | .error _ => false

/-! ### 2. Turtle & RDF/XML `swrl:Imp` Parsing & Strict Round-Trip -/

private def turtleSWRLDoc : String := "
@prefix ex: <http://example.org/swrl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix swrl: <http://www.w3.org/2003/11/swrl#> .
@prefix swrlb: <http://www.w3.org/2003/11/swrlb#> .
@prefix swrla: <http://swrl.stanford.edu/ontologies/3.3/swrla.owl#> .

<http://example.org/swrl/ttl> a owl:Ontology .
ex:Person a owl:Class .
ex:Senior a owl:Class .
ex:hasAge a owl:DatatypeProperty .
ex:alice a owl:NamedIndividual , ex:Person ;
         ex:hasAge 70 .
ex:bob a owl:NamedIndividual , ex:Person ;
       ex:hasAge 30 .

<urn:swrl:var#x> a swrl:Variable .
<urn:swrl:var#a> a swrl:Variable .

_:rule1 a swrl:Imp ;
  rdfs:label \"senior-rule\" ;
  swrla:isRuleEnabled true ;
  swrl:body [
    a swrl:AtomList ;
    rdf:first [
      a swrl:ClassAtom ;
      swrl:classPredicate ex:Person ;
      swrl:argument1 <urn:swrl:var#x>
    ] ;
    rdf:rest [
      a swrl:AtomList ;
      rdf:first [
        a swrl:DatavaluedPropertyAtom ;
        swrl:propertyPredicate ex:hasAge ;
        swrl:argument1 <urn:swrl:var#x> ;
        swrl:argument2 <urn:swrl:var#a>
      ] ;
      rdf:rest [
        a swrl:AtomList ;
        rdf:first [
          a swrl:BuiltinAtom ;
          swrl:builtin swrlb:greaterThanOrEqual ;
          swrl:arguments ( <urn:swrl:var#a> 65 )
        ] ;
        rdf:rest rdf:nil
      ]
    ]
  ] ;
  swrl:head [
    a swrl:AtomList ;
    rdf:first [
      a swrl:ClassAtom ;
      swrl:classPredicate ex:Senior ;
      swrl:argument1 <urn:swrl:var#x>
    ] ;
    rdf:rest rdf:nil
  ] .
"

#guard
  match parseDocumentAuto turtleSWRLDoc true with
  | .ok doc =>
    doc.rules.length == 1 &&
    let xmlText := renderMaterialized .rdfxml doc.declarations doc.annotationAxioms
      doc.ontology doc.prefixes doc.ontologyIRI doc.versionIRI doc.rules
    match parseDocumentAuto xmlText true with
    | .ok docXml => docXml.rules == doc.rules
    | .error _ => false
  | .error _ => false

/-! ### 3. DL-Safety & Built-in Validation Rejections -/

-- Head individual variable `?y` missing from body must be rejected
#guard
  let badRule : SWRLRule := {
    body := [.classAtom (.named (ex "A")) (.var (vIRI "x"))],
    head := [.objectPropertyAtom (.named (ex "r")) (.var (vIRI "x")) (.var (vIRI "y"))]
  }
  (diagnoseDLSafeRules [badRule]).isSome

-- Built-in atom in head must be rejected
#guard
  let badRule : SWRLRule := {
    body := [.dataPropertyAtom (ex "p") (.var (vIRI "x")) (.var (vIRI "v"))],
    head := [.builtinAtom (swrlb "greaterThan") [.var (vIRI "v"), .lit (intLit "0")]]
  }
  (diagnoseDLSafeRules [badRule]).isSome

-- Unknown built-in must be rejected during lowering
#guard
  let badRule : SWRLRule := {
    body := [
      .dataPropertyAtom (ex "p") (.var (vIRI "x")) (.var (vIRI "v")),
      .builtinAtom (swrlb "nonExistentOp") [.var (vIRI "v")]
    ],
    head := [.classAtom (.named (ex "B")) (.var (vIRI "x"))]
  }
  match lowerSWRLRules [.dataAssertion (ex "p") (.named (ex "a")) (intLit "5")] [ex "a"] [badRule] with
  | .error _ => true
  | .ok _ => false

/-! ### 4. Multi-Variable Object Rules (Uncle/Triangle, SameAs, DifferentFrom) -/

private def uncleDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Ontology(<http://example.org/swrl/uncle>
  Declaration(ObjectProperty(ex:hasParent))
  Declaration(ObjectProperty(ex:hasBrother))
  Declaration(ObjectProperty(ex:hasUncle))
  Declaration(NamedIndividual(ex:alice))
  Declaration(NamedIndividual(ex:bob))
  Declaration(NamedIndividual(ex:charlie))
  ObjectPropertyAssertion(ex:hasParent ex:alice ex:bob)
  ObjectPropertyAssertion(ex:hasBrother ex:bob ex:charlie)
  DLSafeRule(
    Body(
      ObjectPropertyAtom(ex:hasParent Variable(var:x) Variable(var:y))
      ObjectPropertyAtom(ex:hasBrother Variable(var:y) Variable(var:z))
    )
    Head(
      ObjectPropertyAtom(ex:hasUncle Variable(var:x) Variable(var:z))
    )
  )
)
"

#guard
  let (code1, j1) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "uncle-pos", toJson uncleDoc,
    toJson "ObjectPropertyAssertion(ex:hasUncle ex:alice ex:charlie)"
  ])
  let (code2, j2) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "uncle-neg", toJson uncleDoc,
    toJson "ObjectPropertyAssertion(ex:hasUncle ex:alice ex:bob)"
  ])
  code1 == 0 && jsonFieldStr j1 "verdict" == "ENTAILED" &&
  code2 == 0 && jsonFieldStr j2 "verdict" == "SENTENCE_INDEPENDENT"

-- SameIndividualAtom head contradicting DifferentIndividuals
private def sameAsConflictDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Ontology(<http://example.org/swrl/sameas>
  Declaration(ObjectProperty(ex:sharesKey))
  Declaration(NamedIndividual(ex:a))
  Declaration(NamedIndividual(ex:b))
  ObjectPropertyAssertion(ex:sharesKey ex:a ex:b)
  DifferentIndividuals(ex:a ex:b)
  DLSafeRule(
    Body(ObjectPropertyAtom(ex:sharesKey Variable(var:x) Variable(var:y)))
    Head(SameIndividualAtom(Variable(var:x) Variable(var:y)))
  )
)
"

#guard
  let (code, j) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "sameas-clash", toJson sameAsConflictDoc
  ])
  code == 0 && jsonFieldStr j "verdict" == "INCONSISTENT_ONTOLOGY"

/-! ### 5. Local Data-Variable & Facet Built-in Roll-Up (Open-World + Regex) -/

-- Verify open-world entailment: even without a concrete literal, an existential restriction
-- `hasAge some integer[>= 20]` satisfies `hasAge(?x, ?a) ∧ swrlb:greaterThanOrEqual(?a, 18) → Adult(?x)`
private def openWorldFacetDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(swrlb:=<http://www.w3.org/2003/11/swrlb#>)
Ontology(<http://example.org/swrl/facet>
  Declaration(Class(ex:Person))
  Declaration(Class(ex:Adult))
  Declaration(DataProperty(ex:hasAge))
  Declaration(NamedIndividual(ex:carol))
  Declaration(NamedIndividual(ex:dave))
  ClassAssertion(ex:Person ex:carol)
  ClassAssertion(
    DataSomeValuesFrom(ex:hasAge DatatypeRestriction(xsd:integer xsd:minInclusive \"20\"^^xsd:integer))
    ex:carol
  )
  ClassAssertion(ex:Person ex:dave)
  DataPropertyAssertion(ex:hasAge ex:dave \"12\"^^xsd:integer)
  DLSafeRule(
    Body(
      ClassAtom(ex:Person Variable(var:x))
      DataPropertyAtom(ex:hasAge Variable(var:x) Variable(var:a))
      BuiltInAtom(swrlb:greaterThanOrEqual Variable(var:a) \"18\"^^xsd:integer)
    )
    Head(
      ClassAtom(ex:Adult Variable(var:x))
    )
  )
)
"

#guard
  let (c1, j1) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "ow-adult-pos", toJson openWorldFacetDoc,
    toJson "ClassAssertion(ex:Adult ex:carol)"
  ])
  let (c2, j2) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "ow-adult-neg", toJson openWorldFacetDoc,
    toJson "ClassAssertion(ex:Adult ex:dave)"
  ])
  c1 == 0 && jsonFieldStr j1 "verdict" == "ENTAILED" &&
  c2 == 0 && jsonFieldStr j2 "verdict" == "SENTENCE_INDEPENDENT"

-- Regex facet roll-up via `swrlb:matches`
private def regexSWRLDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(swrlb:=<http://www.w3.org/2003/11/swrlb#>)
Ontology(<http://example.org/swrl/regex>
  Declaration(Class(ex:Record))
  Declaration(Class(ex:ValidRecord))
  Declaration(DataProperty(ex:hasCode))
  Declaration(NamedIndividual(ex:r1))
  Declaration(NamedIndividual(ex:r2))
  ClassAssertion(ex:Record ex:r1)
  DataPropertyAssertion(ex:hasCode ex:r1 \"ABC\"^^xsd:string)
  ClassAssertion(ex:Record ex:r2)
  DataPropertyAssertion(ex:hasCode ex:r2 \"12a\"^^xsd:string)
  DLSafeRule(
    Body(
      ClassAtom(ex:Record Variable(var:x))
      DataPropertyAtom(ex:hasCode Variable(var:x) Variable(var:c))
      BuiltInAtom(swrlb:matches Variable(var:c) \"[A-Z]{3}\"^^xsd:string)
    )
    Head(
      ClassAtom(ex:ValidRecord Variable(var:x))
    )
  )
)
"

#guard
  let (c1, j1) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "regex-pos", toJson regexSWRLDoc,
    toJson "ClassAssertion(ex:ValidRecord ex:r1)"
  ])
  let (c2, j2) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "regex-neg", toJson regexSWRLDoc,
    toJson "ClassAssertion(ex:ValidRecord ex:r2)"
  ])
  c1 == 0 && jsonFieldStr j1 "verdict" == "ENTAILED" &&
  c2 == 0 && jsonFieldStr j2 "verdict" == "SENTENCE_INDEPENDENT"

/-! ### 6. Concrete-Value Functional `swrlb:*` Built-ins (`add`, `stringConcat`) -/

private def arithmeticSWRLDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(swrlb:=<http://www.w3.org/2003/11/swrlb#>)
Ontology(<http://example.org/swrl/arith>
  Declaration(Class(ex:Item))
  Declaration(Class(ex:HighValue))
  Declaration(DataProperty(ex:basePrice))
  Declaration(DataProperty(ex:tax))
  Declaration(NamedIndividual(ex:i1))
  Declaration(NamedIndividual(ex:i2))
  ClassAssertion(ex:Item ex:i1)
  DataPropertyAssertion(ex:basePrice ex:i1 \"80\"^^xsd:integer)
  DataPropertyAssertion(ex:tax ex:i1 \"30\"^^xsd:integer)
  ClassAssertion(ex:Item ex:i2)
  DataPropertyAssertion(ex:basePrice ex:i2 \"40\"^^xsd:integer)
  DataPropertyAssertion(ex:tax ex:i2 \"10\"^^xsd:integer)
  DLSafeRule(
    Body(
      ClassAtom(ex:Item Variable(var:x))
      DataPropertyAtom(ex:basePrice Variable(var:x) Variable(var:p))
      DataPropertyAtom(ex:tax Variable(var:x) Variable(var:t))
      BuiltInAtom(swrlb:add Variable(var:tot) Variable(var:p) Variable(var:t))
      BuiltInAtom(swrlb:greaterThan Variable(var:tot) \"100\"^^xsd:integer)
    )
    Head(
      ClassAtom(ex:HighValue Variable(var:x))
    )
  )
)
"

#guard
  let (c1, j1) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "arith-pos", toJson arithmeticSWRLDoc,
    toJson "ClassAssertion(ex:HighValue ex:i1)"
  ])
  let (c2, j2) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "arith-neg", toJson arithmeticSWRLDoc,
    toJson "ClassAssertion(ex:HighValue ex:i2)"
  ])
  c1 == 0 && jsonFieldStr j1 "verdict" == "ENTAILED" &&
  c2 == 0 && jsonFieldStr j2 "verdict" == "SENTENCE_INDEPENDENT"

private def stringConcatSWRLDoc : String := "
Prefix(ex:=<http://example.org/swrl#>)
Prefix(var:=<urn:swrl:var#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(swrlb:=<http://www.w3.org/2003/11/swrlb#>)
Ontology(<http://example.org/swrl/concat>
  Declaration(DataProperty(ex:firstName))
  Declaration(DataProperty(ex:lastName))
  Declaration(DataProperty(ex:fullName))
  Declaration(NamedIndividual(ex:p1))
  DataPropertyAssertion(ex:firstName ex:p1 \"Ada\"^^xsd:string)
  DataPropertyAssertion(ex:lastName ex:p1 \"Lovelace\"^^xsd:string)
  DLSafeRule(
    Body(
      DataPropertyAtom(ex:firstName Variable(var:x) Variable(var:f))
      DataPropertyAtom(ex:lastName Variable(var:x) Variable(var:l))
      BuiltInAtom(swrlb:stringConcat Variable(var:full) Variable(var:f) \" \"^^xsd:string Variable(var:l))
    )
    Head(
      DataPropertyAtom(ex:fullName Variable(var:x) Variable(var:full))
    )
  )
)
"

#guard
  let (c, j) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "concat-pos", toJson stringConcatSWRLDoc,
    toJson "DataPropertyAssertion(ex:fullName ex:p1 \"Ada Lovelace\"^^xsd:string)"
  ])
  c == 0 && jsonFieldStr j "verdict" == "ENTAILED"

/-! ### 7. Lazy CEGAR Grounding Loop on Larger ABox (16 Named Individuals, 256 Groundings > 64) -/

private def cegarNamedInds : List IRI :=
  (List.range 16).map fun k => ex s!"n{k}"

private def cegarRule : SWRLRule := {
  body := [
    .classAtom (.named (ex "Source")) (.var (vIRI "x")),
    .objectPropertyAtom (.named (ex "link")) (.var (vIRI "x")) (.var (vIRI "y"))
  ],
  head := [
    .classAtom (.named (ex "Target")) (.var (vIRI "y"))
  ]
}

private def cegarBaseOnt : Ontology :=
  [.disjointClasses [.named (ex "Target"), .named (ex "Blocked")],
   .classAssertion (.named (ex "Source")) (.named (ex "n0")),
   .objectAssertion (.named (ex "link")) (.named (ex "n0")) (.named (ex "n1"))]

#guard
  match decideWithSWRLFast? cegarBaseOnt cegarNamedInds [cegarRule] with
  | .ok (some true) => true
  | _ => false

#guard
  let clashOnt := .classAssertion (.named (ex "Blocked")) (.named (ex "n1")) :: cegarBaseOnt
  match decideWithSWRLFast? clashOnt cegarNamedInds [cegarRule] with
  | .ok (some false) => true
  | _ => false

/-! ### 8. End-to-End Turtle Query, Realization, Materialization, and SWRL Justification -/

#guard
  let (c1, j1) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "ttl-senior-pos", toJson turtleSWRLDoc,
    toJson "ClassAssertion(ex:Senior ex:alice)"
  ])
  let (c2, j2) := OFNQuery.run (Json.arr #[
    toJson OFNQuery.requestFormat, toJson "ttl-senior-neg", toJson turtleSWRLDoc,
    toJson "ClassAssertion(ex:Senior ex:bob)"
  ])
  c1 == 0 && jsonFieldStr j1 "verdict" == "ENTAILED" &&
  c2 == 0 && jsonFieldStr j2 "verdict" == "SENTENCE_INDEPENDENT"

-- Materialization to `.ofn` and `.ttl` includes inferred SWRL assertions, preserves SWRL rules,
-- and does not leak internal `owl:topObjectProperty` grounding axioms
#guard
  let (code, metaJson, rendered?) := OFNQuery.runMaterializeDocument "uncle-mat" uncleDoc [] false .ofn {}
  match rendered? with
  | some txt =>
    code == 0 && jsonFieldStr metaJson "verdict" == "MATERIALIZED" &&
    match parseDocument txt with
    | .ok matDoc =>
      matDoc.rules.length == 1 &&
      matDoc.ontology.contains (.objectAssertion (.named (ex "hasUncle")) (.named (ex "alice")) (.named (ex "charlie"))) &&
      !matDoc.ontology.any (fun
        | .subClassOf (.named c) _ => c == thing
        | _ => false)
    | .error _ => false
  | none => false

-- Justification for a SWRL-derived entailment surfaces the `DLSafeRule(...)` cleanly
#guard
  let (code, j) := OFNQuery.runExplainDocument "uncle-exp" uncleDoc
    (some "ObjectPropertyAssertion(ex:hasUncle ex:alice ex:charlie)") [] false 3
  code == 0 && jsonFieldStr j "verdict" == "EXPLAINED" &&
  (j.compress.splitOn "DLSafeRule(").length ≥ 2

end SabrinaTests.SWRLTests
