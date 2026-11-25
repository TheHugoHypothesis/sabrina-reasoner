import Sabrina.OWL2.StrictOWL2DL
import Sabrina.CLI.OFNQuery

/-! Regression tests for:
1. Milestone C.1: W3C XSD 1.1 regular expressions (`\d` = Unicode `\p{Nd}`,
   `\w` = `[^\p{P}\p{Z}\p{C}]`, `\p{...}` / `\P{...}` Unicode General Categories
   and `Is...` blocks, nested character-class subtraction `[base-[sub]]`,
   and malformed pattern rejection), including exact OWL 2 DL satisfiability
   over the full Unicode scalar space.
2. Milestone A: Strict W3C OWL 2 DL §11.1–§11.2 global restriction validator
   (`checkStrictOWL2DL`, `diagnoseStrictOWL2DL`, `decideStrictOWL2DLReal`,
   and `--strict-owl2dl` / `"strict_owl2dl": true` CLI dispatch). -/

namespace SabrinaTests.StrictAndRegex

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.StrictOWL2DL
open Sabrina.OWL2.SROIQD.Termination.SourceImport

/-! ### 1. Milestone C.1 — Unicode `\d`, `\w`, `\p{...}`, and Character Class Subtraction -/

-- \d matches ASCII digits AND non-ASCII Unicode Nd decimal digits
#guard matchesPattern "\\d" "0"
#guard matchesPattern "\\d" "9"
#guard matchesPattern "\\d" (String.ofList [Char.ofNat 0x0660]) -- Arabic-Indic digit zero '٠'
#guard matchesPattern "\\d" (String.ofList [Char.ofNat 0x0966]) -- Devanagari digit zero '०'
#guard matchesPattern "\\d" (String.ofList [Char.ofNat 0xFF10]) -- Fullwidth digit zero '０'
#guard matchesPattern "\\d" (String.ofList [Char.ofNat 0x1D7CE]) -- Mathematical bold digit zero '𝟎'
#guard !matchesPattern "\\d" "a"
#guard !matchesPattern "\\d" (String.ofList [Char.ofNat 0x2160]) -- Roman numeral I (Nl, not Nd)

-- \D is the exact complement of \d
#guard matchesPattern "\\D" "a"
#guard !matchesPattern "\\D" "5"
#guard !matchesPattern "\\D" (String.ofList [Char.ofNat 0x0660])

-- W3C XSD 1.1 \w excludes '_' (Pc) and spaces (Z), includes Unicode letters, digits, symbols
#guard matchesPattern "\\w" "A"
#guard matchesPattern "\\w" "7"
#guard matchesPattern "\\w" (String.ofList [Char.ofNat 0x03B1]) -- Greek alpha 'α'
#guard matchesPattern "\\w" "$" -- Currency symbol (Sc)
#guard !matchesPattern "\\w" "_" -- Pc punctuation
#guard !matchesPattern "\\w" " " -- Zs separator
#guard matchesPattern "\\W" "_"

-- Unicode General Categories (\p{...} and \P{...})
#guard matchesPattern "\\p{Lu}+" "ABC"
#guard !matchesPattern "\\p{Lu}+" "AbC"
#guard matchesPattern "\\p{Ll}+" "abc"
#guard matchesPattern "\\p{Sc}" "$"
#guard matchesPattern "\\p{Sc}" (String.ofList [Char.ofNat 0x20AC]) -- Euro '€'
#guard !matchesPattern "\\p{Sc}" "A"
#guard matchesPattern "\\P{P}" "a"
#guard !matchesPattern "\\P{P}" "."

-- Unicode Blocks (\p{Is...})
#guard matchesPattern "\\p{IsBasicLatin}+" "Hello!"
#guard !matchesPattern "\\p{IsBasicLatin}+" (String.ofList [Char.ofNat 0x03B1])
#guard matchesPattern "\\p{IsGreek}+" (String.ofList [Char.ofNat 0x03B1, Char.ofNat 0x03B2])
#guard !matchesPattern "\\p{IsGreek}+" "ab"
#guard matchesPattern "\\p{IsHiragana}" (String.ofList [Char.ofNat 0x3042]) -- 'あ'
#guard matchesPattern "\\p{IsCJKUnifiedIdeographs}" (String.ofList [Char.ofNat 0x4E00]) -- '一'

-- Character class subtraction [base-[sub]] and nested subtraction
#guard matchesPattern "[a-z-[aeiou]]" "b"
#guard matchesPattern "[a-z-[aeiou]]" "z"
#guard !matchesPattern "[a-z-[aeiou]]" "a"
#guard !matchesPattern "[a-z-[aeiou]]" "e"
#guard !matchesPattern "[a-z-[aeiou]]" "A"

#guard matchesPattern "[a-z-[b-y-[e-g]]]" "a"
#guard matchesPattern "[a-z-[b-y-[e-g]]]" "e"
#guard matchesPattern "[a-z-[b-y-[e-g]]]" "g"
#guard matchesPattern "[a-z-[b-y-[e-g]]]" "z"
#guard !matchesPattern "[a-z-[b-y-[e-g]]]" "b"
#guard !matchesPattern "[a-z-[b-y-[e-g]]]" "h"

-- Subtracting ASCII digits from \d yields non-ASCII Unicode Nd digits!
#guard matchesPattern "[\\d-[0-9]]" (String.ofList [Char.ofNat 0x0660])
#guard !matchesPattern "[\\d-[0-9]]" "5"

-- Escaped single-char range endpoints and metacharacters
#guard matchesPattern "[\\--0]" "-"
#guard matchesPattern "[\\--0]" "0"
#guard matchesPattern "\\[a\\]" "[a]"

-- Malformed XSD 1.1 regular expressions must be rejected (`none`)
#guard (parseCompleteRegex "[z-a]").isNone
#guard (parseCompleteRegex "[]").isNone
#guard (parseCompleteRegex "[^]").isNone
#guard (parseCompleteRegex "[a-z").isNone
#guard (parseCompleteRegex "[a[b]").isNone
#guard (parseCompleteRegex "\\p{NoSuchCategory}").isNone
#guard (parseCompleteRegex "\\p{Lu").isNone
#guard (parseCompleteRegex "\\q").isNone
#guard (parseCompleteRegex "a{5,2}").isNone
#guard (parseCompleteRegex "*a").isNone

-- End-to-end exact OWL 2 DL reasoning over full Unicode \d, \p{...}, and subtraction!
private def nonAsciiDigitOFN : String := "
Prefix(:=<http://example.org/rx#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/rx>
  Declaration(DataProperty(:code))
  ClassAssertion(
    DataSomeValuesFrom(:code
      DataIntersectionOf(
        DatatypeRestriction(xsd:string xsd:pattern \"\\\\d\"^^xsd:string)
        DataComplementOf(DatatypeRestriction(xsd:string xsd:pattern \"[0-9]\"^^xsd:string))))
    :x)
)"

private def dEquivNdClashOFN : String := "
Prefix(:=<http://example.org/rx#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/rx>
  ClassAssertion(
    DataSomeValuesFrom(:code
      DataIntersectionOf(
        DatatypeRestriction(xsd:string xsd:pattern \"\\\\d\"^^xsd:string)
        DataComplementOf(DatatypeRestriction(xsd:string xsd:pattern \"\\\\p{Nd}\"^^xsd:string))))
    :x)
)"

private def subtractionEmptyClashOFN : String := "
Prefix(:=<http://example.org/rx#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/rx>
  ClassAssertion(
    DataSomeValuesFrom(:code
      DatatypeRestriction(xsd:string xsd:pattern \"[a-c-[a-z]]\"^^xsd:string))
    :x)
)"

private def greekDisjointBasicLatinOFN : String := "
Prefix(:=<http://example.org/rx#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/rx>
  ClassAssertion(
    DataSomeValuesFrom(:code
      DataIntersectionOf(
        DatatypeRestriction(xsd:string xsd:pattern \"\\\\p{IsGreek}\"^^xsd:string)
        DatatypeRestriction(xsd:string xsd:pattern \"\\\\p{IsBasicLatin}\"^^xsd:string)))
    :x)
)"

private def nonAsciiDigitSubSatOFN : String := "
Prefix(:=<http://example.org/rx#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/rx>
  ClassAssertion(
    DataSomeValuesFrom(:code
      DatatypeRestriction(xsd:string xsd:pattern \"[\\\\d-[0-9]]\"^^xsd:string))
    :x)
)"

#guard (decideRealSourceClosure? nonAsciiDigitOFN []).map Prod.snd == some true
#guard (decideRealSourceClosure? dEquivNdClashOFN []).map Prod.snd == some false
#guard (decideRealSourceClosure? subtractionEmptyClashOFN []).map Prod.snd == some false
#guard (decideRealSourceClosure? greekDisjointBasicLatinOFN []).map Prod.snd == some false
#guard (decideRealSourceClosure? nonAsciiDigitSubSatOFN []).map Prod.snd == some true

/-! ### 2. Milestone A — Strict W3C OWL 2 DL §11.1–§11.2 Validator -/

private def parseOnt! (s : String) : Ontology :=
  match parseDocument s with
  | .ok doc => doc.ontology
  | .error _ => []

-- Valid OWL 2 DL: topDataProperty as superproperty + in class expression
private def validTopDataSuperOFN : String := "
Prefix(:=<http://example.org/s#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/s>
  SubDataPropertyOf(:dp owl:topDataProperty)
  SubClassOf(:A DataSomeValuesFrom(owl:topDataProperty xsd:integer))
)"

-- Invalid OWL 2 DL (§11.2): topDataProperty as subproperty (T6-TOP-2)
private def invalidTopDataSubOFN : String := "
Prefix(:=<http://example.org/s#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://example.org/s>
  SubDataPropertyOf(owl:topDataProperty :dp)
)"

-- Invalid OWL 2 DL (§11.2): topDataProperty in FunctionalDataProperty / EquivalentDataProperties
private def invalidTopDataFuncOFN : String := "
Prefix(:=<http://example.org/s#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://example.org/s>
  FunctionalDataProperty(owl:topDataProperty)
)"

-- Invalid OWL 2 DL (§11.2): rankless converse-square chain r^- o r^- <= r (T6-INF-2)
private def invalidConverseSquareOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
)"

-- Valid OWL 2 DL (§11.2): anonymous individuals forming a simple tree with 1 named root
private def validAnonTreeOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  ClassAssertion(:A _:x)
  ObjectPropertyAssertion(:r :a _:x)
  ObjectPropertyAssertion(:r _:x _:y)
  ObjectPropertyAssertion(:r _:x _:z)
)"

-- Invalid OWL 2 DL (§11.2): anonymous individual in ObjectOneOf
private def invalidAnonOneOfOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  SubClassOf(:A ObjectOneOf(_:x))
)"

-- Invalid OWL 2 DL (§11.2): anonymous individual in SameIndividual
private def invalidAnonSameOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  SameIndividual(:a _:x)
)"

-- Invalid OWL 2 DL (§11.2): anonymous individual in NegativeObjectPropertyAssertion
private def invalidAnonNegObjOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  NegativeObjectPropertyAssertion(:r :a _:x)
)"

-- Invalid OWL 2 DL (§11.2): anonymous self-loop
private def invalidAnonSelfLoopOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  ObjectPropertyAssertion(:r _:x _:x)
)"

-- Invalid OWL 2 DL (§11.2): anonymous cycle _:x - _:y - _:z - _:x
private def invalidAnonCycleOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  ObjectPropertyAssertion(:r _:x _:y)
  ObjectPropertyAssertion(:r _:y _:z)
  ObjectPropertyAssertion(:r _:z _:x)
)"

-- Invalid OWL 2 DL (§11.2): anonymous parallel edges between same pair
private def invalidAnonParallelOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  ObjectPropertyAssertion(:r _:x _:y)
  ObjectPropertyAssertion(:s _:x _:y)
)"

-- Invalid OWL 2 DL (§11.2): anonymous component connected to two named individuals
private def invalidAnonTwoNamedOFN : String := "
Prefix(:=<http://example.org/s#>)
Ontology(<http://example.org/s>
  ObjectPropertyAssertion(:r :a _:x)
  ObjectPropertyAssertion(:r _:x _:y)
  ObjectPropertyAssertion(:r :b _:y)
)"

-- Invalid OWL 2 DL / XSD 1.1: malformed xsd:pattern
private def invalidPatternOFN : String := "
Prefix(:=<http://example.org/s#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/s>
  DataPropertyRange(:code DatatypeRestriction(xsd:string xsd:pattern \"[z-a]\"^^xsd:string))
)"

#guard checkStrictOWL2DL (parseOnt! validTopDataSuperOFN)
#guard checkStrictOWL2DL (parseOnt! validAnonTreeOFN)
#guard checkStrictOWL2DL (parseOnt! nonAsciiDigitOFN)

#guard !checkStrictOWL2DL (parseOnt! invalidTopDataSubOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidTopDataFuncOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidConverseSquareOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonOneOfOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonSameOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonNegObjOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonSelfLoopOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonCycleOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonParallelOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidAnonTwoNamedOFN)
#guard !checkStrictOWL2DL (parseOnt! invalidPatternOFN)

-- CLI strict mode (`--strict-owl2dl` / `"strict_owl2dl": true`) end-to-end checks
#guard
  let req := Lean.Json.arr #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "strict-reject", Lean.toJson invalidTopDataSubOFN]
  let (code, res) := Sabrina.CLI.OFNQuery.run req true
  code == 2 && (res.getObjValAs? String "verdict").toOption == some "UNSUPPORTED" &&
    (res.getObjValAs? Bool "owl2dl_valid").toOption == some false

#guard
  let req := Lean.Json.arr #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "strict-reject-json",
    Lean.toJson invalidConverseSquareOFN, Lean.Json.mkObj [("strict_owl2dl", Lean.toJson true)]]
  let (code, res) := Sabrina.CLI.OFNQuery.run req false
  code == 2 && (res.getObjValAs? String "verdict").toOption == some "UNSUPPORTED" &&
    (res.getObjValAs? Bool "owl2dl_valid").toOption == some false

#guard
  let req := Lean.Json.arr #[Lean.toJson "sabrina-ofn-query-v1", Lean.toJson "strict-accept-unicode",
    Lean.toJson nonAsciiDigitOFN, Lean.Json.mkObj [("strict_owl2dl", Lean.toJson true)]]
  let (code, res) := Sabrina.CLI.OFNQuery.run req false
  code == 0 && (res.getObjValAs? String "verdict").toOption == some "SATISFIABLE" &&
    (res.getObjValAs? Bool "owl2dl_valid").toOption == some true

end SabrinaTests.StrictAndRegex
