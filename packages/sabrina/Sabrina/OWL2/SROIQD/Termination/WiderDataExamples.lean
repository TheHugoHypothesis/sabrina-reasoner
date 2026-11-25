import Sabrina.OWL2.SROIQD.Termination.WiderDataReduction
import Sabrina.OWL2.FunctionalSyntax

/-!
Live fuel-free `#guard` regressions for `decideWithWiderDataRanges?`, exercising:
- `xsd:decimal`, `owl:rational`, and `owl:real` order facets (dense proper decimals,
  non-decimal rationals, singleton intervals, cross-numeric literal identity);
- 7-tier string subtype hierarchy (`NCName ⊂ Name ⊂ token ⊂ normalizedString ⊂ string ⊂ PlainLiteral`,
  `NMTOKEN ⊂ token`);
- `length` / `minLength` / `maxLength` facets on `xsd:string`, `rdf:PlainLiteral`,
  `xsd:anyURI`, `xsd:hexBinary`, and `xsd:base64Binary` (including the subtle contrast
  between singleton `xsd:string[length 0]` and infinite `rdf:PlainLiteral[length 0]`);
- `xsd:dateTimeStamp ⊂ xsd:dateTime`;
- `HasKey` over wider decimal/length-constrained data properties;
- `DatatypeDefinition` unfolding + `owl:topObjectProperty` composition + Functional-Style Syntax.
-/

namespace Sabrina.OWL2.SROIQD.Termination.WiderDataExamples

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.WiderData

private def ex (n : String) : IRI := "http://example.org/wider#" ++ n
private def intLit (s : String) : Literal := ⟨s, xsd "integer"⟩
private def decLit (s : String) : Literal := ⟨s, xsd "decimal"⟩
private def ratLit (s : String) : Literal := ⟨s, owlRational⟩
private def strLit (s : String) : Literal := ⟨s, xsd "string"⟩

private def clsA : ClassExpr := .named (ex "A")
private def indA : Individual := .named (ex "a")
private def indB : Individual := .named (ex "b")

/-! ### 1. General decimal, rational, and real order facets -/

-- (1) Dense proper decimals in (0.5, 1.5): dataMin 3 is SAT even though only integer 1 is inside
private def decOpenRange : DataRange :=
  .restriction (xsd "decimal")
    [⟨xsd "minExclusive", decLit "0.5"⟩, ⟨xsd "maxExclusive", decLit "1.5"⟩]

private def ontDecDense : Ontology :=
  [.classAssertion (.dataMin 3 (ex "score") decOpenRange) indA]

#guard decideWithWiderDataRanges? ontDecDense = some true

-- (2) Disjoint decimal intervals (0.0, 1.0) ∩ (1.0, 2.0) is UNSAT
private def ontDecDisjoint : Ontology :=
  [.classAssertion
    (.dataSome (ex "score")
      (.intersection
        (.restriction (xsd "decimal") [⟨xsd "minExclusive", decLit "0.0"⟩, ⟨xsd "maxExclusive", decLit "1.0"⟩])
        (.restriction (xsd "decimal") [⟨xsd "minExclusive", decLit "1.0"⟩, ⟨xsd "maxExclusive", decLit "2.0"⟩])))
    indA]

#guard decideWithWiderDataRanges? ontDecDisjoint = some false

-- (3) Singleton closed decimal interval [2.5, 2.5]: dataMin 1 is SAT, dataMin 2 is UNSAT
private def decSingleton : DataRange :=
  .restriction (xsd "decimal")
    [⟨xsd "minInclusive", decLit "2.5"⟩, ⟨xsd "maxInclusive", decLit "2.5"⟩]

#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 1 (ex "p") decSingleton) indA] = some true
#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 2 (ex "p") decSingleton) indA] = some false

-- (4) Proper decimals in (0.0, 1.0) \ xsd:integer: dataMin 3 is SAT
private def ontProperDecOnly : Ontology :=
  [.classAssertion
    (.dataMin 3 (ex "p")
      (.intersection
        (.restriction (xsd "decimal") [⟨xsd "minExclusive", decLit "0.0"⟩, ⟨xsd "maxExclusive", decLit "1.0"⟩])
        (.complement (.datatype (xsd "integer")))))
    indA]

#guard decideWithWiderDataRanges? ontProperDecOnly = some true

-- (5) xsd:integer ∩ xsd:decimal(0.5, 1.5): unique integer 1 -> dataMin 1 SAT, dataMin 2 UNSAT
private def intInDecOpen : DataRange :=
  .intersection (.datatype (xsd "integer")) decOpenRange

#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 1 (ex "p") intInDecOpen) indA] = some true
#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 2 (ex "p") intInDecOpen) indA] = some false

-- (6) Non-decimal rationals in (0, 1): owl:rational \ xsd:decimal has infinitely many (1/3, 1/6, ...)
private def ontNonDecRat : Ontology :=
  [.classAssertion
    (.dataMin 3 (ex "p")
      (.intersection
        (.restriction owlRational [⟨xsd "minExclusive", intLit "0"⟩, ⟨xsd "maxExclusive", intLit "1"⟩])
        (.complement (.datatype (xsd "decimal")))))
    indA]

#guard decideWithWiderDataRanges? ontNonDecRat = some true

-- (7) owl:real singleton [1/3, 1/3]: dataMin 1 SAT, dataMin 2 UNSAT, and disjoint from xsd:decimal
private def thirdSingleton : DataRange :=
  .restriction owlReal [⟨xsd "minInclusive", ratLit "1/3"⟩, ⟨xsd "maxInclusive", ratLit "1/3"⟩]

#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 1 (ex "p") thirdSingleton) indA] = some true
#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 2 (ex "p") thirdSingleton) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "p") (.intersection thirdSingleton (.datatype (xsd "decimal")))) indA] = some false

-- (8) Cross-datatype numeric identity: "2.0"^^xsd:decimal = "4/2"^^owl:rational = "2"^^xsd:integer
private def ontCrossNumericClash : Ontology :=
  [.dataAssertion (ex "p") indA (decLit "2.0"),
   .negativeDataAssertion (ex "p") indA (ratLit "4/2")]

#guard decideWithWiderDataRanges? ontCrossNumericClash = some false

/-! ### 2. 7-tier string subtype hierarchy -/

-- Strict inclusions: NCName ⊂ Name ⊂ token ⊂ normalizedString ⊂ string ⊂ PlainLiteral
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "NCName")) (.complement (.datatype (xsd "Name"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.intersection (.datatype (xsd "Name")) (.complement (.datatype (xsd "NCName"))))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "Name")) (.complement (.datatype (xsd "token"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.intersection (.datatype (xsd "token")) (.complement (.datatype (xsd "Name"))))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "token")) (.complement (.datatype (xsd "normalizedString"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.intersection (.datatype (xsd "normalizedString")) (.complement (.datatype (xsd "token"))))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "normalizedString")) (.complement (.datatype (xsd "string"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.intersection (.datatype (xsd "string")) (.complement (.datatype (xsd "normalizedString"))))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "string")) (.complement (.datatype (rdf "PlainLiteral"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.intersection (.datatype (rdf "PlainLiteral")) (.complement (.datatype (xsd "string"))))) indA] = some true

-- NMTOKEN ⊂ token
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s") (.intersection (.datatype (xsd "NMTOKEN")) (.complement (.datatype (xsd "token"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "s") (.intersection (.datatype (xsd "token")) (.complement (.datatype (xsd "NMTOKEN"))))) indA] = some true

-- NMTOKEN can appear with both Name and NCName in the same partition.
private def tokenButNotName : DataRange :=
  .intersection (.datatype (xsd "NMTOKEN")) (.complement (.datatype (xsd "Name")))

#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") tokenButNotName) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s")
    (.intersection (.datatype (xsd "NCName")) (.complement (.datatype (xsd "NMTOKEN"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "s")
    (.intersection (.datatype (xsd "NMTOKEN"))
      (.intersection (.datatype (xsd "Name")) (.complement (.datatype (xsd "NCName")))))) indA] = some true

/-! ### 3. Length facets across strings, PlainLiteral, anyURI, hexBinary, base64Binary -/

-- The xsd:language datatype consists of untagged strings with the language syntax.
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s") (.datatype (xsd "language"))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s")
    (.intersection (.datatype (xsd "language")) (.complement (.datatype (xsd "NCName"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "s")
    (.intersection (.datatype (xsd "NCName")) (.complement (.datatype (xsd "language"))))) indA] = some true

-- One-character Name minus NCName has exactly one value, the colon.
private def singleColon : DataRange :=
  .intersection (.datatype (xsd "Name"))
    (.intersection (.complement (.datatype (xsd "NCName")))
      (.restriction (xsd "string") [⟨xsd "length", intLit "1"⟩]))

#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 1 (ex "s") singleColon) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "s") singleColon) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s")
    (.intersection singleColon (.complement (.oneOf [strLit ":"])))) indA] = some false

-- Exercise an unbounded length cell and a bounded PlainLiteral length cell.
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s")
    (.intersection (.datatype (xsd "language"))
      (.restriction (rdf "PlainLiteral") [⟨xsd "minLength", intLit "9"⟩]))) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s")
    (.intersection (.datatype (xsd "NMTOKEN"))
      (.restriction (rdf "PlainLiteral") [⟨xsd "length", intLit "0"⟩]))) indA] = some false

-- Above the former cap, a bounded character alphabet can still supply 50,001 witnesses.
#guard ((BoundedWords.scalars.sample 50001 1 1).length == 50001)
-- A cell with only one byte has exactly 256 possibilities even for a larger request.
#guard ((BoundedWords.bytes.sample 50001 1 1).length == 256)
-- The byte-word generator can use more than two digits of the alphabet.
#guard ((BoundedWords.bytes.sample 65537 3 3).length == 65537)
#guard ((BoundedWords.bytes.word 3 65536) == [0, 0, 1])

-- xsd:string[length 0] is singleton {""}: dataMin 1 SAT, dataMin 2 UNSAT
private def emptyStr : DataRange :=
  .restriction (xsd "string") [⟨xsd "length", intLit "0"⟩]

#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 1 (ex "s") emptyStr) indA] = some true
#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 2 (ex "s") emptyStr) indA] = some false

-- Contrast: rdf:PlainLiteral[length 0] is INFINITE (different language tags!): dataMin 3 SAT
private def emptyPlain : DataRange :=
  .restriction (rdf "PlainLiteral") [⟨xsd "length", intLit "0"⟩]

#guard decideWithWiderDataRanges? [.classAssertion (.dataMin 3 (ex "s") emptyPlain) indA] = some true

-- Contradictory string length bounds [minLength 3, maxLength 2] -> UNSAT
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "s")
    (.restriction (xsd "string") [⟨xsd "minLength", intLit "3"⟩, ⟨xsd "maxLength", intLit "2"⟩])) indA] = some false

-- Positive length interval [minLength 2, maxLength 4] with dataMin 3 -> SAT
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "s")
    (.restriction (xsd "string") [⟨xsd "minLength", intLit "2"⟩, ⟨xsd "maxLength", intLit "4"⟩])) indA] = some true

-- xsd:string[length 1] \ {"a"} with dataMin 2 -> SAT
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "s")
    (.intersection (.restriction (xsd "string") [⟨xsd "length", intLit "1"⟩])
      (.complement (.oneOf [strLit "a"])))) indA] = some true

-- xsd:anyURI length facets
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "u") (.restriction (xsd "anyURI") [⟨xsd "length", intLit "0"⟩])) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "u")
    (.restriction (xsd "anyURI") [⟨xsd "minLength", intLit "2"⟩, ⟨xsd "maxLength", intLit "5"⟩])) indA] = some true

-- xsd:hexBinary & xsd:base64Binary length facets
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "h") (.restriction (xsd "hexBinary") [⟨xsd "length", intLit "0"⟩])) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 3 (ex "h") (.restriction (xsd "hexBinary") [⟨xsd "length", intLit "1"⟩])) indA] = some true
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "b") (.restriction (xsd "base64Binary") [⟨xsd "length", intLit "0"⟩])) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "b")
    (.restriction (xsd "base64Binary") [⟨xsd "minLength", intLit "2"⟩, ⟨xsd "maxLength", intLit "3"⟩])) indA] = some true

/-! ### 4. xsd:dateTime and xsd:dateTimeStamp -/

#guard decideWithWiderDataRanges?
  [.classAssertion (.dataSome (ex "t")
    (.intersection (.datatype (xsd "dateTimeStamp")) (.complement (.datatype (xsd "dateTime"))))) indA] = some false
#guard decideWithWiderDataRanges?
  [.classAssertion (.dataMin 2 (ex "t")
    (.intersection (.datatype (xsd "dateTime")) (.complement (.datatype (xsd "dateTimeStamp"))))) indA] = some true

/-! ### 5. HasKey over wider decimal ranges, DatatypeDefinition, and owl:topObjectProperty -/

-- HasKey(A () (price)) + price ∈ [1.0, 1.0] forces a = b, clashing with DifferentIndividuals(a b)
private def ontHasKeyDecClash : Ontology :=
  [.hasKey clsA [] [ex "price"],
   .dataPropertyRange (ex "price")
     (.restriction (xsd "decimal") [⟨xsd "minInclusive", decLit "1.0"⟩, ⟨xsd "maxInclusive", decLit "1.0"⟩]),
   .classAssertion clsA indA,
   .classAssertion clsA indB,
   .classAssertion (.dataSome (ex "price") (.datatype (xsd "decimal"))) indA,
   .classAssertion (.dataSome (ex "price") (.datatype (xsd "decimal"))) indB,
   .differentIndividuals [indA, indB]]

#guard decideWithWiderDataRanges? ontHasKeyDecClash = some false

-- Widening price range to [1.0, 2.0] makes it SAT
private def ontHasKeyDecSat : Ontology :=
  [.hasKey clsA [] [ex "price"],
   .dataPropertyRange (ex "price")
     (.restriction (xsd "decimal") [⟨xsd "minInclusive", decLit "1.0"⟩, ⟨xsd "maxInclusive", decLit "2.0"⟩]),
   .classAssertion clsA indA,
   .classAssertion clsA indB,
   .classAssertion (.dataSome (ex "price") (.datatype (xsd "decimal"))) indA,
   .classAssertion (.dataSome (ex "price") (.datatype (xsd "decimal"))) indB,
   .differentIndividuals [indA, indB]]

#guard decideWithWiderDataRanges? ontHasKeyDecSat = some true

-- DatatypeDefinition + owl:topObjectProperty restriction composed together
private def ontDefAndTop : Ontology :=
  [.datatypeDefinition (ex "UnitDecimal")
     (.restriction (xsd "decimal") [⟨xsd "minExclusive", decLit "0.0"⟩, ⟨xsd "maxExclusive", decLit "1.0"⟩]),
   .subClassOf (.named thing) (.objectSome (.named topObjectProperty) (.dataMin 2 (ex "w") (.datatype (ex "UnitDecimal"))))]

#guard decideWithWiderDataRanges? ontDefAndTop = some true

-- Functional-Style Syntax round-trip with xsd:decimal facets
private def fssDecimalSample : String :=
  "Prefix(:=<http://example.org/fss#>)\n" ++
  "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n" ++
  "Ontology(<http://example.org/fss>\n" ++
  "  Declaration(DataProperty(:temp))\n" ++
  "  Declaration(NamedIndividual(:sensor1))\n" ++
  "  ClassAssertion(\n" ++
  "    DataMinCardinality(2 :temp DatatypeRestriction(xsd:decimal xsd:minInclusive \"36.5\"^^xsd:decimal xsd:maxInclusive \"36.5\"^^xsd:decimal))\n" ++
  "    :sensor1)\n" ++
  ")\n"

#guard
  match FunctionalSyntax.parseDocument fssDecimalSample with
  | .ok doc => decideWithWiderDataRanges? doc.ontology == some false
  | .error _ => false

end Sabrina.OWL2.SROIQD.Termination.WiderDataExamples
