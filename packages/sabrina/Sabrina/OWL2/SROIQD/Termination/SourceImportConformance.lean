import Sabrina.OWL2.WellFormed
import Sabrina.OWL2.SROIQD.Termination.RealDecision
import Sabrina.OWL2.SROIQD.Termination.XMLLiteralValidation

/-!
The total Functional-Style Syntax parser reads the typed logical ontology,
the ontology and version IRIs, and import requests. It skips declarations
and annotations. The canonical renderer round-trips for clean tokens and
properly scoped anonymous individuals. The round trip is stated for this
renderer and parser.

The finite import resolver terminates on the lexicographic pair
`(rem.length, queue.length)`. It handles cycles, diamonds, and matches by
catalog key, version IRI, or ontology IRI. The Lean proofs establish
document-ID uniqueness, source reachability, import coverage, and model
equivalence with the flattened collection of loaded documents.

The decision adapters compose the resolver, the stricter XML scanner, the
optional typed well-formedness check, and the wider datatype decision
procedure. Their verdict theorems use SABRINA's typed Direct Semantics.
-/

namespace Sabrina.OWL2.SROIQD.Termination.SourceImport

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.WellFormed
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.XMLLiteral

/-! ### 1. Total Tokenizer for W3C OWL 2 Functional-Style Syntax -/

inductive SrcToken where
  | lparen
  | rparen
  | eq
  | caret2
  | atSign
  | iri (val : String)
  | str (val : String)
  | ident (val : String)
  deriving Repr, BEq, DecidableEq

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == ':' || c == '.' || c == '#' || c == '/'

def skipComment : List Char → List Char
  | [] => []
  | c :: rest => if c == '\n' then rest else skipComment rest

private theorem skipComment_length_le (cs : List Char) : (skipComment cs).length ≤ cs.length := by
  induction cs with
  | nil => simp [skipComment]
  | cons c rest ih =>
    simp only [skipComment, List.length_cons]
    split
    · exact Nat.le_succ _
    · exact Nat.le_succ_of_le ih

def readUntilGT : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | c :: rest, acc =>
    if c = '>' then some (String.ofList acc.reverse, rest)
    else readUntilGT rest (c :: acc)

private theorem readUntilGT_length_lt {cs acc : List Char} {s : String} {rem : List Char}
    (h : readUntilGT cs acc = some (s, rem)) : rem.length < cs.length := by
  induction cs generalizing acc with
  | nil => simp [readUntilGT] at h
  | cons c rest ih =>
    simp only [readUntilGT] at h
    split at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (ih h)

def readStrLit : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | c :: rest, acc =>
    if c = '"' then some (String.ofList acc.reverse, rest)
    else if c = '\\' then
      if rest.head? = some '"' ∨ rest.head? = some '\\' then
        readStrLit rest.tail (rest.headD '\\' :: acc)
      else none
    else readStrLit rest (c :: acc)
termination_by cs _ => cs.length
decreasing_by all_goals (simp_wf <;> omega)

private theorem readStrLit_length_lt {cs acc : List Char} {s : String} {rem : List Char}
    (h : readStrLit cs acc = some (s, rem)) : rem.length < cs.length := by
  match cs with
  | [] => simp [readStrLit] at h
  | c :: rest =>
    rw [readStrLit] at h
    split at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.lt_succ_self _
    · split at h
      · split at h
        · have := readStrLit_length_lt h
          simp only [List.length_tail] at this
          simp only [List.length_cons]
          omega
        · contradiction
      · exact Nat.lt_succ_of_lt (readStrLit_length_lt h)
termination_by cs.length
decreasing_by all_goals (simp_wf <;> omega)

def readIdent (cs : List Char) (acc : List Char) : String × List Char :=
  match cs with
  | [] => (String.ofList acc.reverse, [])
  | c :: rest =>
    if isIdentChar c then readIdent rest (c :: acc)
    else (String.ofList acc.reverse, c :: rest)

private theorem readIdent_length_le (cs acc : List Char) :
    (readIdent cs acc).2.length ≤ cs.length := by
  induction cs generalizing acc with
  | nil => simp [readIdent]
  | cons c rest ih =>
    unfold readIdent
    split
    · exact Nat.le_succ_of_le (ih (c :: acc))
    · exact Nat.le_refl _

/-- Total, structurally terminating lexer for W3C OWL 2 Functional-Style Syntax. -/
def tokenizeChars : List Char → Option (List SrcToken)
  | [] => some []
  | c :: rest =>
    if c.isWhitespace then
      tokenizeChars rest
    else if c == '#' then
      have _ : (skipComment rest).length < (c :: rest).length :=
        Nat.lt_succ_of_le (skipComment_length_le rest)
      tokenizeChars (skipComment rest)
    else if c == '(' then
      (tokenizeChars rest).map (.lparen :: ·)
    else if c == ')' then
      (tokenizeChars rest).map (.rparen :: ·)
    else if c == '=' then
      (tokenizeChars rest).map (.eq :: ·)
    else if c == '@' then
      (tokenizeChars rest).map (.atSign :: ·)
    else if c == '^' then
      if rest.head? == some '^' then (tokenizeChars rest.tail).map (.caret2 :: ·) else none
    else if c == '<' then
      match h : readUntilGT rest [] with
      | none => none
      | some (s, rem) =>
        have _ : rem.length < (c :: rest).length :=
          Nat.lt_trans (readUntilGT_length_lt h) (Nat.lt_succ_self _)
        (tokenizeChars rem).map (.iri s :: ·)
    else if c == '"' then
      match h : readStrLit rest [] with
      | none => none
      | some (s, rem) =>
        have _ : rem.length < (c :: rest).length :=
          Nat.lt_trans (readStrLit_length_lt h) (Nat.lt_succ_self _)
        (tokenizeChars rem).map (.str s :: ·)
    else if isIdentChar c then
      let res := readIdent rest [c]
      have _ : res.2.length < (c :: rest).length :=
        Nat.lt_succ_of_le (readIdent_length_le rest [c])
      (tokenizeChars res.2).map (.ident res.1 :: ·)
    else
      none
termination_by cs => cs.length
decreasing_by all_goals first | assumption | (simp_wf <;> omega)

def tokenizeTotal (input : String) : Option (List SrcToken) :=
  tokenizeChars input.toList

/-! ### 2. Total Recursive-Descent Parser for W3C OWL 2 Functional-Style Syntax -/

abbrev PrefixMap := FunctionalSyntax.PrefixMap

def defaultPrefixes : PrefixMap := [
  ("owl", "http://www.w3.org/2002/07/owl#"),
  ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
  ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
  ("xsd", "http://www.w3.org/2001/XMLSchema#")
]

def splitPrefixChars (acc : List Char) : List Char → Option (String × String)
  | [] => none
  | ':' :: rest => some (String.ofList acc.reverse, String.ofList rest)
  | c :: rest => splitPrefixChars (c :: acc) rest

def splitPrefix (s : String) : Option (String × String) :=
  splitPrefixChars [] s.toList

def expandIRITotal (pfx : PrefixMap) (s : String) : Option IRI :=
  match splitPrefix s with
  | some (p, loc) => (pfx.lookup p).map (· ++ loc)
  | none => none

def parseIRITotal (pfx : PrefixMap) : List SrcToken → Option (IRI × List SrcToken)
  | .iri s :: rest => some (s, rest)
  | .ident s :: rest => (expandIRITotal pfx s).map fun iri => (iri, rest)
  | _ => none

def parseIndividualTotal (docId : String) (pfx : PrefixMap) :
    List SrcToken → Option (Individual × List SrcToken)
  | .iri s :: rest => some (.named s, rest)
  | .ident s :: rest =>
    match s.toList with
    | '_' :: ':' :: lid => some (.anonymous docId (String.ofList lid), rest)
    | _ => (expandIRITotal pfx s).map fun iri => (.named iri, rest)
  | _ => none

def digitVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

def parseNatLoop (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    match digitVal? c with
    | some d => parseNatLoop (acc * 10 + d) rest
    | none => none

def parseNatStr (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | c :: rest =>
    match digitVal? c with
    | some d => parseNatLoop d rest
    | none => none

def parseNatTotal : List SrcToken → Option (Nat × List SrcToken)
  | .ident s :: rest => (parseNatStr s).map fun n => (n, rest)
  | _ => none

def parseLiteralTotal (pfx : PrefixMap) : List SrcToken → Option (Literal × List SrcToken)
  | .str raw :: .caret2 :: rest =>
    (parseIRITotal pfx rest).map fun (dt, rem) => (⟨raw, dt⟩, rem)
  | .str raw :: .atSign :: .ident lang :: rest =>
    some (⟨raw ++ "@" ++ lang, rdf "PlainLiteral"⟩, rest)
  | .str _ :: .atSign :: _ => none
  | .str raw :: rest =>
    some (⟨raw ++ "@", rdf "PlainLiteral"⟩, rest)
  | _ => none

def parseObjPropTotal (pfx : PrefixMap) : List SrcToken → Option (ObjectProperty × List SrcToken)
  | .ident "ObjectInverseOf" :: .lparen :: rest =>
    match parseIRITotal pfx rest with
    | some (r, .rparen :: rem) => some (.inverse r, rem)
    | _ => none
  | toks => (parseIRITotal pfx toks).map fun (r, rem) => (.named r, rem)

def skipBalancedLoop (depth : Nat) : List SrcToken → Option (List SrcToken)
  | [] => none
  | .lparen :: rest => skipBalancedLoop (depth + 1) rest
  | .rparen :: rest =>
    match depth with
    | 0 => none
    | 1 => some rest
    | d + 1 => skipBalancedLoop d rest
  | _ :: rest => skipBalancedLoop depth rest

def skipBalancedTotal : List SrcToken → Option (List SrcToken)
  | .lparen :: rest => skipBalancedLoop 1 rest
  | _ => none

def skipAnnotationsTotal : Nat → List SrcToken → Option (List SrcToken)
  | 0, toks => some toks
  | fuel + 1, toks =>
    if toks.head? = some (.ident "Annotation") then
      (skipBalancedTotal toks.tail).bind (skipAnnotationsTotal fuel)
    else some toks

def parseManySimple {α : Type} (p : List SrcToken → Option (α × List SrcToken)) :
    Nat → List SrcToken → List α → Option (List α × List SrcToken)
  | 0, _, _ => none
  | _ + 1, .rparen :: rest, acc => some (acc.reverse, rest)
  | fuel + 1, toks, acc =>
    (p toks).bind fun (a, rem) => parseManySimple p fuel rem (a :: acc)

def parseFacetTotal (pfx : PrefixMap) (toks : List SrcToken) : Option (Facet × List SrcToken) :=
  (parseIRITotal pfx toks).bind fun (f, rem1) =>
    (parseLiteralTotal pfx rem1).map fun (b, rem2) => (⟨f, b⟩, rem2)

def foldDataIntersect : List DataRange → DataRange
  | [] => .datatype literalDatatype
  | [d] => d
  | d :: ds => .intersection d (foldDataIntersect ds)

def foldDataUnite : List DataRange → DataRange
  | [] => .complement (.datatype literalDatatype)
  | [d] => d
  | d :: ds => .union d (foldDataUnite ds)

def foldClassIntersect : List ClassExpr → ClassExpr
  | [] => .named thing
  | [c] => c
  | c :: cs => .intersection c (foldClassIntersect cs)

def foldClassUnite : List ClassExpr → ClassExpr
  | [] => .named nothing
  | [c] => c
  | c :: cs => .union c (foldClassUnite cs)

mutual
def parseDataRangeTotal (pfx : PrefixMap) : Nat → List SrcToken → Option (DataRange × List SrcToken)
  | 0, _ => none
  | fuel + 1, .ident "DataIntersectionOf" :: .lparen :: rest =>
    (parseDataRangeList pfx fuel rest []).map fun (ds, rem) => (foldDataIntersect ds, rem)
  | fuel + 1, .ident "DataUnionOf" :: .lparen :: rest =>
    (parseDataRangeList pfx fuel rest []).map fun (ds, rem) => (foldDataUnite ds, rem)
  | fuel + 1, .ident "DataComplementOf" :: .lparen :: rest =>
    match parseDataRangeTotal pfx fuel rest with
    | some (d, .rparen :: rem) => some (.complement d, rem)
    | _ => none
  | fuel + 1, .ident "DataOneOf" :: .lparen :: rest =>
    (parseManySimple (parseLiteralTotal pfx) fuel rest []).map fun (ls, rem) => (.oneOf ls, rem)
  | fuel + 1, .ident "DatatypeRestriction" :: .lparen :: rest =>
    (parseIRITotal pfx rest).bind fun (dt, rem1) =>
      (parseManySimple (parseFacetTotal pfx) fuel rem1 []).map fun (fs, rem2) =>
        (.restriction dt fs, rem2)
  | _ + 1, toks =>
    (parseIRITotal pfx toks).map fun (dt, rem) => (.datatype dt, rem)

def parseDataRangeList (pfx : PrefixMap) :
    Nat → List SrcToken → List DataRange → Option (List DataRange × List SrcToken)
  | 0, _, _ => none
  | _ + 1, .rparen :: rest, acc => some (acc.reverse, rest)
  | fuel + 1, toks, acc =>
    (parseDataRangeTotal pfx fuel toks).bind fun (d, rem) =>
      parseDataRangeList pfx fuel rem (d :: acc)
end

mutual
def parseClassExprTotal (docId : String) (pfx : PrefixMap) :
    Nat → List SrcToken → Option (ClassExpr × List SrcToken)
  | 0, _ => none
  | fuel + 1, .ident "ObjectIntersectionOf" :: .lparen :: rest =>
    (parseClassExprList docId pfx fuel rest []).map fun (cs, rem) => (foldClassIntersect cs, rem)
  | fuel + 1, .ident "ObjectUnionOf" :: .lparen :: rest =>
    (parseClassExprList docId pfx fuel rest []).map fun (cs, rem) => (foldClassUnite cs, rem)
  | fuel + 1, .ident "ObjectComplementOf" :: .lparen :: rest =>
    match parseClassExprTotal docId pfx fuel rest with
    | some (c, .rparen :: rem) => some (.complement c, rem)
    | _ => none
  | fuel + 1, .ident "ObjectOneOf" :: .lparen :: rest =>
    (parseManySimple (parseIndividualTotal docId pfx) fuel rest []).map fun (inds, rem) =>
      (.oneOf inds, rem)
  | fuel + 1, .ident "ObjectSomeValuesFrom" :: .lparen :: rest =>
    (parseObjPropTotal pfx rest).bind fun (r, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (c, .rparen :: rem2) => some (.objectSome r c, rem2)
      | _ => none
  | fuel + 1, .ident "ObjectAllValuesFrom" :: .lparen :: rest =>
    (parseObjPropTotal pfx rest).bind fun (r, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (c, .rparen :: rem2) => some (.objectAll r c, rem2)
      | _ => none
  | _ + 1, .ident "ObjectHasValue" :: .lparen :: rest =>
    (parseObjPropTotal pfx rest).bind fun (r, rem1) =>
      match parseIndividualTotal docId pfx rem1 with
      | some (a, .rparen :: rem2) => some (.objectValue r a, rem2)
      | _ => none
  | _ + 1, .ident "ObjectHasSelf" :: .lparen :: rest =>
    match parseObjPropTotal pfx rest with
    | some (r, .rparen :: rem) => some (.objectSelf r, rem)
    | _ => none
  | fuel + 1, .ident "ObjectMinCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseObjPropTotal pfx rem1).bind fun (r, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.objectMin n r (.named thing), rem3)
        | _ =>
          match parseClassExprTotal docId pfx fuel rem2 with
          | some (c, .rparen :: rem3) => some (.objectMin n r c, rem3)
          | _ => none
  | fuel + 1, .ident "ObjectMaxCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseObjPropTotal pfx rem1).bind fun (r, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.objectMax n r (.named thing), rem3)
        | _ =>
          match parseClassExprTotal docId pfx fuel rem2 with
          | some (c, .rparen :: rem3) => some (.objectMax n r c, rem3)
          | _ => none
  | fuel + 1, .ident "ObjectExactCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseObjPropTotal pfx rem1).bind fun (r, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.objectExact n r (.named thing), rem3)
        | _ =>
          match parseClassExprTotal docId pfx fuel rem2 with
          | some (c, .rparen :: rem3) => some (.objectExact n r c, rem3)
          | _ => none
  | fuel + 1, .ident "DataSomeValuesFrom" :: .lparen :: rest =>
    (parseIRITotal pfx rest).bind fun (dp, rem1) =>
      match parseDataRangeTotal pfx fuel rem1 with
      | some (d, .rparen :: rem2) => some (.dataSome dp d, rem2)
      | _ => none
  | fuel + 1, .ident "DataAllValuesFrom" :: .lparen :: rest =>
    (parseIRITotal pfx rest).bind fun (dp, rem1) =>
      match parseDataRangeTotal pfx fuel rem1 with
      | some (d, .rparen :: rem2) => some (.dataAll dp d, rem2)
      | _ => none
  | _ + 1, .ident "DataHasValue" :: .lparen :: rest =>
    (parseIRITotal pfx rest).bind fun (dp, rem1) =>
      match parseLiteralTotal pfx rem1 with
      | some (l, .rparen :: rem2) => some (.dataValue dp l, rem2)
      | _ => none
  | fuel + 1, .ident "DataMinCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseIRITotal pfx rem1).bind fun (dp, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.dataMin n dp (.datatype literalDatatype), rem3)
        | _ =>
          match parseDataRangeTotal pfx fuel rem2 with
          | some (d, .rparen :: rem3) => some (.dataMin n dp d, rem3)
          | _ => none
  | fuel + 1, .ident "DataMaxCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseIRITotal pfx rem1).bind fun (dp, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.dataMax n dp (.datatype literalDatatype), rem3)
        | _ =>
          match parseDataRangeTotal pfx fuel rem2 with
          | some (d, .rparen :: rem3) => some (.dataMax n dp d, rem3)
          | _ => none
  | fuel + 1, .ident "DataExactCardinality" :: .lparen :: rest =>
    (parseNatTotal rest).bind fun (n, rem1) =>
      (parseIRITotal pfx rem1).bind fun (dp, rem2) =>
        match rem2 with
        | .rparen :: rem3 => some (.dataExact n dp (.datatype literalDatatype), rem3)
        | _ =>
          match parseDataRangeTotal pfx fuel rem2 with
          | some (d, .rparen :: rem3) => some (.dataExact n dp d, rem3)
          | _ => none
  | _ + 1, toks =>
    (parseIRITotal pfx toks).map fun (c, rem) => (.named c, rem)

def parseClassExprList (docId : String) (pfx : PrefixMap) :
    Nat → List SrcToken → List ClassExpr → Option (List ClassExpr × List SrcToken)
  | 0, _, _ => none
  | _ + 1, .rparen :: rest, acc => some (acc.reverse, rest)
  | fuel + 1, toks, acc =>
    (parseClassExprTotal docId pfx fuel toks).bind fun (c, rem) =>
      parseClassExprList docId pfx fuel rem (c :: acc)
end

inductive AxiomTag where
  | subClassOf
  | equivalentClasses
  | disjointClasses
  | disjointUnion
  | subObjectPropertyOf
  | equivalentObjectProperties
  | disjointObjectProperties
  | inverseObjectProperties
  | objectPropertyDomain
  | objectPropertyRange
  | functionalObjectProperty
  | inverseFunctionalObjectProperty
  | reflexiveObjectProperty
  | irreflexiveObjectProperty
  | symmetricObjectProperty
  | asymmetricObjectProperty
  | transitiveObjectProperty
  | subDataPropertyOf
  | equivalentDataProperties
  | disjointDataProperties
  | dataPropertyDomain
  | dataPropertyRange
  | functionalDataProperty
  | datatypeDefinition
  | hasKey
  | sameIndividual
  | differentIndividuals
  | classAssertion
  | objectPropertyAssertion
  | negativeObjectPropertyAssertion
  | dataPropertyAssertion
  | negativeDataPropertyAssertion

private def readAxiomTag : String → Option AxiomTag
  | "SubClassOf" => some .subClassOf
  | "EquivalentClasses" => some .equivalentClasses
  | "DisjointClasses" => some .disjointClasses
  | "DisjointUnion" => some .disjointUnion
  | "SubObjectPropertyOf" => some .subObjectPropertyOf
  | "EquivalentObjectProperties" => some .equivalentObjectProperties
  | "DisjointObjectProperties" => some .disjointObjectProperties
  | "InverseObjectProperties" => some .inverseObjectProperties
  | "ObjectPropertyDomain" => some .objectPropertyDomain
  | "ObjectPropertyRange" => some .objectPropertyRange
  | "FunctionalObjectProperty" => some .functionalObjectProperty
  | "InverseFunctionalObjectProperty" => some .inverseFunctionalObjectProperty
  | "ReflexiveObjectProperty" => some .reflexiveObjectProperty
  | "IrreflexiveObjectProperty" => some .irreflexiveObjectProperty
  | "SymmetricObjectProperty" => some .symmetricObjectProperty
  | "AsymmetricObjectProperty" => some .asymmetricObjectProperty
  | "TransitiveObjectProperty" => some .transitiveObjectProperty
  | "SubDataPropertyOf" => some .subDataPropertyOf
  | "EquivalentDataProperties" => some .equivalentDataProperties
  | "DisjointDataProperties" => some .disjointDataProperties
  | "DataPropertyDomain" => some .dataPropertyDomain
  | "DataPropertyRange" => some .dataPropertyRange
  | "FunctionalDataProperty" => some .functionalDataProperty
  | "DatatypeDefinition" => some .datatypeDefinition
  | "HasKey" => some .hasKey
  | "SameIndividual" => some .sameIndividual
  | "DifferentIndividuals" => some .differentIndividuals
  | "ClassAssertion" => some .classAssertion
  | "ObjectPropertyAssertion" => some .objectPropertyAssertion
  | "NegativeObjectPropertyAssertion" => some .negativeObjectPropertyAssertion
  | "DataPropertyAssertion" => some .dataPropertyAssertion
  | "NegativeDataPropertyAssertion" => some .negativeDataPropertyAssertion
  | _ => none

private def parseAxiomArgs (docId : String) (pfx : PrefixMap) (fuel : Nat)
    (rem0 : List SrcToken) : AxiomTag → Option (Option Axiom × List SrcToken)
  | .subClassOf =>
    (parseClassExprTotal docId pfx fuel rem0).bind fun (a, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (b, .rparen :: rem2) => some (some (.subClassOf a b), rem2)
      | _ => none
  | .equivalentClasses =>
    (parseClassExprList docId pfx fuel rem0 []).map fun (cs, rem1) =>
      (some (.equivalentClasses cs), rem1)
  | .disjointClasses =>
    (parseClassExprList docId pfx fuel rem0 []).map fun (cs, rem1) =>
      (some (.disjointClasses cs), rem1)
  | .disjointUnion =>
    (parseIRITotal pfx rem0).bind fun (h, rem1) =>
      (parseClassExprList docId pfx fuel rem1 []).map fun (cs, rem2) =>
        (some (.disjointUnion h cs), rem2)
  | .subObjectPropertyOf =>
    match rem0 with
    | .ident "ObjectPropertyChain" :: .lparen :: rem1 =>
      (parseManySimple (parseObjPropTotal pfx) fuel rem1 []).bind fun (rs, rem2) =>
        match parseObjPropTotal pfx rem2 with
        | some (sup, .rparen :: rem3) => some (some (.subObjectPropertyChain rs sup), rem3)
        | _ => none
    | _ =>
      (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
        match parseObjPropTotal pfx rem1 with
        | some (s, .rparen :: rem2) => some (some (.subObjectProperty r s), rem2)
        | _ => none
  | .equivalentObjectProperties =>
    (parseManySimple (parseObjPropTotal pfx) fuel rem0 []).map fun (rs, rem1) =>
      (some (.equivalentObjectProperties rs), rem1)
  | .disjointObjectProperties =>
    (parseManySimple (parseObjPropTotal pfx) fuel rem0 []).map fun (rs, rem1) =>
      (some (.disjointObjectProperties rs), rem1)
  | .inverseObjectProperties =>
    (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
      match parseObjPropTotal pfx rem1 with
      | some (s, .rparen :: rem2) => some (some (.inverseObjectProperties r s), rem2)
      | _ => none
  | .objectPropertyDomain =>
    (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (c, .rparen :: rem2) => some (some (.objectPropertyDomain r c), rem2)
      | _ => none
  | .objectPropertyRange =>
    (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (c, .rparen :: rem2) => some (some (.objectPropertyRange r c), rem2)
      | _ => none
  | .functionalObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.functionalObjectProperty r), rem1)
    | _ => none
  | .inverseFunctionalObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.inverseFunctionalObjectProperty r), rem1)
    | _ => none
  | .reflexiveObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.reflexiveObjectProperty r), rem1)
    | _ => none
  | .irreflexiveObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.irreflexiveObjectProperty r), rem1)
    | _ => none
  | .symmetricObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.symmetricObjectProperty r), rem1)
    | _ => none
  | .asymmetricObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.asymmetricObjectProperty r), rem1)
    | _ => none
  | .transitiveObjectProperty =>
    match parseObjPropTotal pfx rem0 with
    | some (r, .rparen :: rem1) => some (some (.transitiveObjectProperty r), rem1)
    | _ => none
  | .subDataPropertyOf =>
    (parseIRITotal pfx rem0).bind fun (r, rem1) =>
      match parseIRITotal pfx rem1 with
      | some (s, .rparen :: rem2) => some (some (.subDataProperty r s), rem2)
      | _ => none
  | .equivalentDataProperties =>
    (parseManySimple (parseIRITotal pfx) fuel rem0 []).map fun (ds, rem1) =>
      (some (.equivalentDataProperties ds), rem1)
  | .disjointDataProperties =>
    (parseManySimple (parseIRITotal pfx) fuel rem0 []).map fun (ds, rem1) =>
      (some (.disjointDataProperties ds), rem1)
  | .dataPropertyDomain =>
    (parseIRITotal pfx rem0).bind fun (dp, rem1) =>
      match parseClassExprTotal docId pfx fuel rem1 with
      | some (c, .rparen :: rem2) => some (some (.dataPropertyDomain dp c), rem2)
      | _ => none
  | .dataPropertyRange =>
    (parseIRITotal pfx rem0).bind fun (dp, rem1) =>
      match parseDataRangeTotal pfx fuel rem1 with
      | some (d, .rparen :: rem2) => some (some (.dataPropertyRange dp d), rem2)
      | _ => none
  | .functionalDataProperty =>
    match parseIRITotal pfx rem0 with
    | some (dp, .rparen :: rem1) => some (some (.functionalDataProperty dp), rem1)
    | _ => none
  | .datatypeDefinition =>
    (parseIRITotal pfx rem0).bind fun (dt, rem1) =>
      match parseDataRangeTotal pfx fuel rem1 with
      | some (d, .rparen :: rem2) => some (some (.datatypeDefinition dt d), rem2)
      | _ => none
  | .hasKey =>
    (parseClassExprTotal docId pfx fuel rem0).bind fun (c, rem1) =>
      match rem1 with
      | .lparen :: rem2 =>
        (parseManySimple (parseObjPropTotal pfx) fuel rem2 []).bind fun (os, rem3) =>
          match rem3 with
          | .lparen :: rem4 =>
            match parseManySimple (parseIRITotal pfx) fuel rem4 [] with
            | some (ds, .rparen :: rem5) => some (some (.hasKey c os ds), rem5)
            | _ => none
          | _ => none
      | _ => none
  | .sameIndividual =>
    (parseManySimple (parseIndividualTotal docId pfx) fuel rem0 []).map fun (inds, rem1) =>
      (some (.sameIndividuals inds), rem1)
  | .differentIndividuals =>
    (parseManySimple (parseIndividualTotal docId pfx) fuel rem0 []).map fun (inds, rem1) =>
      (some (.differentIndividuals inds), rem1)
  | .classAssertion =>
    (parseClassExprTotal docId pfx fuel rem0).bind fun (c, rem1) =>
      match parseIndividualTotal docId pfx rem1 with
      | some (a, .rparen :: rem2) => some (some (.classAssertion c a), rem2)
      | _ => none
  | .objectPropertyAssertion =>
    (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
      (parseIndividualTotal docId pfx rem1).bind fun (a, rem2) =>
        match parseIndividualTotal docId pfx rem2 with
        | some (b, .rparen :: rem3) => some (some (.objectAssertion r a b), rem3)
        | _ => none
  | .negativeObjectPropertyAssertion =>
    (parseObjPropTotal pfx rem0).bind fun (r, rem1) =>
      (parseIndividualTotal docId pfx rem1).bind fun (a, rem2) =>
        match parseIndividualTotal docId pfx rem2 with
        | some (b, .rparen :: rem3) => some (some (.negativeObjectAssertion r a b), rem3)
        | _ => none
  | .dataPropertyAssertion =>
    (parseIRITotal pfx rem0).bind fun (dp, rem1) =>
      (parseIndividualTotal docId pfx rem1).bind fun (a, rem2) =>
        match parseLiteralTotal pfx rem2 with
        | some (l, .rparen :: rem3) => some (some (.dataAssertion dp a l), rem3)
        | _ => none
  | .negativeDataPropertyAssertion =>
    (parseIRITotal pfx rem0).bind fun (dp, rem1) =>
      (parseIndividualTotal docId pfx rem1).bind fun (a, rem2) =>
        match parseLiteralTotal pfx rem2 with
        | some (l, .rparen :: rem3) => some (some (.negativeDataAssertion dp a l), rem3)
        | _ => none

def parseAxiomTotal (docId : String) (pfx : PrefixMap) (fuel : Nat) :
    List SrcToken → Option (Option Axiom × List SrcToken)
  | .ident tag :: .lparen :: rest =>
    match readAxiomTag tag with
    | some form =>
      (skipAnnotationsTotal fuel rest).bind fun args => parseAxiomArgs docId pfx fuel args form
    | none =>
      if ["Declaration", "AnnotationAssertion", "SubAnnotationPropertyOf",
          "AnnotationPropertyDomain", "AnnotationPropertyRange", "Annotation"].contains tag then
        (skipBalancedTotal (.lparen :: rest)).map fun rem => (none, rem)
      else none
  | _ => none

def parsePrefixDeclsTotal : Nat → PrefixMap → List SrcToken → Option (PrefixMap × List SrcToken)
  | 0, _, _ => none
  | fuel + 1, pfx, .ident "Prefix" :: .lparen :: .ident s :: .eq :: .iri iri :: .rparen :: rest =>
    if s.endsWith ":" then
      let name := String.ofList s.toList.dropLast
      parsePrefixDeclsTotal fuel ((name, iri) :: pfx) rest
    else none
  | _ + 1, pfx, toks => some (pfx, toks)

def parseOntologyBodyTotal (docId : String) (pfx : PrefixMap) :
    Nat → List SrcToken → List IRI → Ontology → Option (List IRI × Ontology × List SrcToken)
  | 0, _, _, _ => none
  | _ + 1, .rparen :: rest, imps, axs => some (imps.reverse, axs.reverse, rest)
  | fuel + 1, .ident "Import" :: .lparen :: rest, imps, axs =>
    match parseIRITotal pfx rest with
    | some (imp, .rparen :: rem) =>
      parseOntologyBodyTotal docId pfx fuel rem (imp :: imps) axs
    | _ => none
  | fuel + 1, toks, imps, axs =>
    (parseAxiomTotal docId pfx fuel toks).bind fun (ax?, rem) =>
      match ax? with
      | some ax => parseOntologyBodyTotal docId pfx fuel rem imps (ax :: axs)
      | none => parseOntologyBodyTotal docId pfx fuel rem imps axs

structure SourceDocument where
  docId : String
  prefixes : PrefixMap
  ontologyIRI : Option IRI := none
  versionIRI : Option IRI := none
  imports : List IRI := []
  ontology : Ontology
  deriving Repr, BEq

private def parseOntologyHeader : List SrcToken → Option IRI × Option IRI × List SrcToken
  | .iri o :: .iri v :: r => (some o, some v, r)
  | .iri o :: r => (some o, none, r)
  | r => (none, none, r)

def parseDocumentTokens (docId : String) (toks : List SrcToken) : Option SourceDocument :=
  let fuel := toks.length + 1
  (parsePrefixDeclsTotal fuel defaultPrefixes toks).bind fun (pfx, rem0) =>
    match rem0 with
    | .ident "Ontology" :: .lparen :: rem1 =>
      let (ontIRI, verIRI, rem2) := parseOntologyHeader rem1
      match parseOntologyBodyTotal docId pfx fuel rem2 [] [] with
      | some (imps, ont, []) => some ⟨docId, pfx, ontIRI, verIRI, imps, ont⟩
      | _ => none
    | _ => none

/-- Total parser for the supported OWL 2 Functional-Style Syntax,
scoping all anonymous individuals `_:lid` to `docId`. -/
def parseSourceDocument (docId : String) (input : String) : Option SourceDocument :=
  (tokenizeTotal input).bind fun tokens =>
    (parseDocumentTokens docId tokens).bind fun doc =>
      if doc.docId == docId && docInScope docId doc.ontology then some doc else none

/-! ### 3. Universal Document-Scope Invariant for Arbitrary Source Text -/

/-- Successful parsing checks the document identifier and the scope of all
anonymous individuals before exposing the typed document. -/
theorem parseSourceDocument_inScope {docId : String} {input : String} {doc : SourceDocument}
    (h : parseSourceDocument docId input = some doc) :
    doc.docId = docId ∧ docInScope docId doc.ontology = true := by
  simp only [parseSourceDocument, Option.bind_eq_some_iff] at h
  obtain ⟨tokens, _, parsed, _, hresult⟩ := h
  split at hresult
  · rename_i hscope
    cases hresult
    simpa only [Bool.and_eq_true, beq_iff_eq] using hscope
  · contradiction

/-! ### 4. Canonical Functional-Style Rendering & Exact Text-Level Round-Trip -/

private def natDigitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

private theorem digitVal_natDigitChar {d : Nat} (hd : d < 10) :
    digitVal? (natDigitChar d) = some d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

private theorem isIdentChar_natDigitChar (d : Nat) :
    isIdentChar (natDigitChar d) = true := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => decide
  | _ + 9 => simp only [natDigitChar]; decide

def natToChars (n : Nat) : List Char :=
  if n < 10 then [natDigitChar n]
  else natToChars (n / 10) ++ [natDigitChar (n % 10)]
termination_by n

private theorem natToChars_ne_nil (n : Nat) : natToChars n ≠ [] := by
  unfold natToChars; split <;> simp

private theorem natToChars_all_ident (n : Nat) :
    ∀ c ∈ natToChars n, isIdentChar c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natToChars
    split
    · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact isIdentChar_natDigitChar n
    · intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) c h1
      · simp only [List.mem_singleton] at h2; subst h2; exact isIdentChar_natDigitChar (n % 10)

private theorem natToChars_head_digit (n : Nat) :
    ∃ c rest, natToChars n = c :: rest ∧ '0' ≤ c ∧ c ≤ '9' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natToChars
    split
    · refine ⟨natDigitChar n, [], rfl, ?_⟩
      match n with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
      | _ + 10 => omega
    · obtain ⟨c, rest, hEq, hlo, hhi⟩ := ih (n / 10) (Nat.div_lt_self (by omega) (by decide))
      exact ⟨c, rest ++ [natDigitChar (n % 10)], by rw [hEq, List.cons_append], hlo, hhi⟩

private theorem parseNatLoop_append (acc : Nat) (cs : List Char) (c : Char) :
    parseNatLoop acc (cs ++ [c]) =
      (parseNatLoop acc cs).bind fun m => (digitVal? c).map fun d => m * 10 + d := by
  induction cs generalizing acc with
  | nil =>
    simp only [List.nil_append, parseNatLoop, Option.bind_some]
    cases digitVal? c <;> rfl
  | cons a rest ih =>
    simp only [List.cons_append, parseNatLoop]
    cases digitVal? a with
    | none => rfl
    | some d => exact ih (acc * 10 + d)

private theorem parseNatStr_natToChars (n : Nat) :
    parseNatStr (String.ofList (natToChars n)) = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natToChars
    split
    · rename_i hlt
      simp only [parseNatStr, String.toList_ofList, digitVal_natDigitChar hlt, parseNatLoop]
    · rename_i hge
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      have ih' := ih (n / 10) hlt
      cases hcs : natToChars (n / 10) with
      | nil => exact absurd hcs (natToChars_ne_nil _)
      | cons a rest =>
        simp only [parseNatStr, String.toList_ofList, hcs] at ih'
        simp only [parseNatStr, String.toList_ofList, List.cons_append]
        cases hd : digitVal? a with
        | none => simp [hd] at ih'
        | some d =>
          simp [hd] at ih'
          simp only
          rw [parseNatLoop_append, ih']
          simp only [Option.bind_some, digitVal_natDigitChar (Nat.mod_lt n (by decide)),
            Option.map_some, Option.some.injEq]
          omega

def printSrcToken : SrcToken → String
  | .lparen => "("
  | .rparen => ")"
  | .eq => "="
  | .caret2 => "^^"
  | .atSign => "@"
  | .iri s => "<" ++ s ++ ">"
  | .str s => "\"" ++ s ++ "\""
  | .ident s => s

def printSrcTokens (ts : List SrcToken) : String :=
  ts.foldr (fun t acc => printSrcToken t ++ " " ++ acc) ""

def CleanIRI (s : IRI) : Prop := ∀ c ∈ s.toList, c ≠ '>'
def CleanLexical (s : String) : Prop := ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\'
def CleanLocalId (s : String) : Prop := ∀ c ∈ s.toList, isIdentChar c = true

def CleanIdent (s : String) : Prop :=
  ∃ c rest, s.toList = c :: rest ∧
    !c.isWhitespace ∧ c ≠ '#' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '=' ∧ c ≠ '@' ∧
    c ≠ '^' ∧ c ≠ '<' ∧ c ≠ '"' ∧ isIdentChar c = true ∧
    ∀ ch ∈ rest, isIdentChar ch = true

def CleanToken : SrcToken → Prop
  | .lparen | .rparen | .eq | .caret2 | .atSign => True
  | .iri s => CleanIRI s
  | .str s => CleanLexical s
  | .ident s => CleanIdent s

private theorem readUntilGT_append (xs rest acc : List Char) (hclean : ∀ c ∈ xs, c ≠ '>') :
    readUntilGT (xs ++ '>' :: rest) acc = some (String.ofList (acc.reverse ++ xs), rest) := by
  induction xs generalizing acc with
  | nil => simp [readUntilGT]
  | cons c tail ih =>
    have hne : c ≠ '>' := hclean c (List.mem_cons_self ..)
    have htail : ∀ ch ∈ tail, ch ≠ '>' := fun ch hch => hclean ch (List.mem_cons_of_mem _ hch)
    simp only [List.cons_append, readUntilGT, hne, ite_false]
    rw [ih (c :: acc) htail]
    simp [List.reverse_cons, List.append_assoc]

private theorem readStrLit_append (xs rest acc : List Char)
    (hclean : ∀ c ∈ xs, c ≠ '"' ∧ c ≠ '\\') :
    readStrLit (xs ++ '"' :: rest) acc = some (String.ofList (acc.reverse ++ xs), rest) := by
  induction xs generalizing acc with
  | nil => simp +decide [readStrLit]
  | cons c tail ih =>
    have hc := hclean c (List.mem_cons_self ..)
    have htail : ∀ ch ∈ tail, ch ≠ '"' ∧ ch ≠ '\\' := fun ch hch => hclean ch (List.mem_cons_of_mem _ hch)
    simp only [List.cons_append]
    rw [readStrLit, ite_eq_right hc.1, ite_eq_right hc.2]
    rw [ih (c :: acc) htail]
    simp [List.reverse_cons, List.append_assoc]

private theorem readIdent_append_space (xs rest acc : List Char)
    (hclean : ∀ c ∈ xs, isIdentChar c = true) :
    readIdent (xs ++ ' ' :: rest) acc = (String.ofList (acc.reverse ++ xs), ' ' :: rest) := by
  induction xs generalizing acc with
  | nil =>
    have hsp : isIdentChar ' ' = false := by decide
    simp [readIdent, hsp]
  | cons c tail ih =>
    have hc : isIdentChar c = true := hclean c (List.mem_cons_self ..)
    have htail : ∀ ch ∈ tail, isIdentChar ch = true := fun ch hch => hclean ch (List.mem_cons_of_mem _ hch)
    simp only [List.cons_append]
    unfold readIdent
    rw [ite_eq_left hc, ih (c :: acc) htail]
    simp [List.reverse_cons, List.append_assoc]

private theorem tokenizeChars_cons_space (rest : List Char) :
    tokenizeChars (' ' :: rest) = tokenizeChars rest := by
  conv => lhs; rw [tokenizeChars]
  simp +decide

private theorem tokenizeChars_printToken (t : SrcToken) (rest : List Char) (ht : CleanToken t) :
    tokenizeChars ((printSrcToken t ++ " ").toList ++ rest) =
      (tokenizeChars rest).map (t :: ·) := by
  cases t with
  | lparen =>
    have h : (printSrcToken .lparen ++ " ").toList ++ rest = '(' :: ' ' :: rest := rfl
    rw [h, tokenizeChars]; simp +decide [tokenizeChars_cons_space]
  | rparen =>
    have h : (printSrcToken .rparen ++ " ").toList ++ rest = ')' :: ' ' :: rest := rfl
    rw [h, tokenizeChars]; simp +decide [tokenizeChars_cons_space]
  | eq =>
    have h : (printSrcToken .eq ++ " ").toList ++ rest = '=' :: ' ' :: rest := rfl
    rw [h, tokenizeChars]; simp +decide [tokenizeChars_cons_space]
  | caret2 =>
    have h : (printSrcToken .caret2 ++ " ").toList ++ rest = '^' :: '^' :: ' ' :: rest := rfl
    rw [h, tokenizeChars]; simp +decide [tokenizeChars_cons_space]
  | atSign =>
    have h : (printSrcToken .atSign ++ " ").toList ++ rest = '@' :: ' ' :: rest := rfl
    rw [h, tokenizeChars]; simp +decide [tokenizeChars_cons_space]
  | iri s =>
    have hlist : (printSrcToken (.iri s) ++ " ").toList ++ rest =
        '<' :: (s.toList ++ '>' :: ' ' :: rest) := by
      simp [printSrcToken, String.toList_append, List.append_assoc]
    rw [hlist, tokenizeChars]
    have hgt := readUntilGT_append s.toList (' ' :: rest) [] ht
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hgt
    simp +decide
    split <;> simp_all [tokenizeChars_cons_space]
  | str s =>
    have hlist : (printSrcToken (.str s) ++ " ").toList ++ rest =
        '"' :: (s.toList ++ '"' :: ' ' :: rest) := by
      simp [printSrcToken, String.toList_append, List.append_assoc]
    rw [hlist, tokenizeChars]
    have hstr := readStrLit_append s.toList (' ' :: rest) [] ht
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hstr
    simp +decide
    split <;> simp_all [tokenizeChars_cons_space]
  | ident s =>
    rcases ht with ⟨c, tail, hcs, hws, h1, h2, h3, h4, h5, h6, h7, h8, hid, htail⟩
    have hws' : c.isWhitespace = false := by
      cases h : c.isWhitespace <;> simp_all
    have hlist : (printSrcToken (.ident s) ++ " ").toList ++ rest =
        c :: (tail ++ ' ' :: rest) := by
      simp [printSrcToken, String.toList_append, hcs, List.append_assoc]
    rw [hlist, tokenizeChars]
    have hrid := readIdent_append_space tail rest [c] htail
    have hstrEq : String.ofList (c :: tail) = s := by rw [← hcs, String.ofList_toList]
    simp only [hws', Bool.false_eq_true, ↓reduceIte, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, h8, hid]
    rw [hrid]
    simp only [List.reverse_singleton, List.singleton_append, hstrEq, tokenizeChars_cons_space]

theorem tokenizeTotal_printSrcTokens (ts : List SrcToken) (hclean : ∀ t ∈ ts, CleanToken t) :
    tokenizeTotal (printSrcTokens ts) = some ts := by
  unfold tokenizeTotal
  induction ts with
  | nil => simp [printSrcTokens, tokenizeChars]
  | cons t rest ih =>
    have ht : CleanToken t := hclean t (List.mem_cons_self ..)
    have hrest : ∀ u ∈ rest, CleanToken u := fun u hu => hclean u (List.mem_cons_of_mem _ hu)
    have hlist : (printSrcTokens (t :: rest)).toList =
        (printSrcToken t ++ " ").toList ++ (printSrcTokens rest).toList := by
      simp [printSrcTokens, String.toList_append, List.append_assoc]
    rw [hlist, tokenizeChars_printToken t _ ht, ih hrest]
    rfl

/-! #### Token-level canonical encoder for the full OWL 2 DL AST -/

def renderIndividualTokens : Individual → List SrcToken
  | .named iri => [.iri iri]
  | .anonymous _ lid => [.ident ("_:" ++ lid)]

def renderObjectPropertyTokens : ObjectProperty → List SrcToken
  | .named iri => [.iri iri]
  | .inverse iri => [.ident "ObjectInverseOf", .lparen, .iri iri, .rparen]

def renderLiteralTokens (l : Literal) : List SrcToken :=
  [.str l.lexical, .caret2, .iri l.datatype]

def renderFacetTokens (f : Facet) : List SrcToken :=
  .iri f.name :: renderLiteralTokens f.bound

def renderDataRangeTokens : DataRange → List SrcToken
  | .datatype dt => [.iri dt]
  | .complement d => [.ident "DataComplementOf", .lparen] ++ renderDataRangeTokens d ++ [.rparen]
  | .intersection a b =>
    [.ident "DataIntersectionOf", .lparen] ++ renderDataRangeTokens a ++ renderDataRangeTokens b ++ [.rparen]
  | .union a b =>
    [.ident "DataUnionOf", .lparen] ++ renderDataRangeTokens a ++ renderDataRangeTokens b ++ [.rparen]
  | .oneOf ls =>
    [.ident "DataOneOf", .lparen] ++ ls.flatMap renderLiteralTokens ++ [.rparen]
  | .restriction dt fs =>
    [.ident "DatatypeRestriction", .lparen, .iri dt] ++ fs.flatMap renderFacetTokens ++ [.rparen]

def renderClassExprTokens : ClassExpr → List SrcToken
  | .named c => [.iri c]
  | .complement c => [.ident "ObjectComplementOf", .lparen] ++ renderClassExprTokens c ++ [.rparen]
  | .intersection a b =>
    [.ident "ObjectIntersectionOf", .lparen] ++ renderClassExprTokens a ++ renderClassExprTokens b ++ [.rparen]
  | .union a b =>
    [.ident "ObjectUnionOf", .lparen] ++ renderClassExprTokens a ++ renderClassExprTokens b ++ [.rparen]
  | .oneOf inds =>
    [.ident "ObjectOneOf", .lparen] ++ inds.flatMap renderIndividualTokens ++ [.rparen]
  | .objectSome r c =>
    [.ident "ObjectSomeValuesFrom", .lparen] ++ renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .objectAll r c =>
    [.ident "ObjectAllValuesFrom", .lparen] ++ renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .objectValue r a =>
    [.ident "ObjectHasValue", .lparen] ++ renderObjectPropertyTokens r ++ renderIndividualTokens a ++ [.rparen]
  | .objectSelf r =>
    [.ident "ObjectHasSelf", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .objectMin n r c =>
    [.ident "ObjectMinCardinality", .lparen, .ident (String.ofList (natToChars n))] ++
      renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .objectMax n r c =>
    [.ident "ObjectMaxCardinality", .lparen, .ident (String.ofList (natToChars n))] ++
      renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .objectExact n r c =>
    [.ident "ObjectExactCardinality", .lparen, .ident (String.ofList (natToChars n))] ++
      renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .dataSome dp d =>
    [.ident "DataSomeValuesFrom", .lparen, .iri dp] ++ renderDataRangeTokens d ++ [.rparen]
  | .dataAll dp d =>
    [.ident "DataAllValuesFrom", .lparen, .iri dp] ++ renderDataRangeTokens d ++ [.rparen]
  | .dataValue dp l =>
    [.ident "DataHasValue", .lparen, .iri dp] ++ renderLiteralTokens l ++ [.rparen]
  | .dataMin n dp d =>
    [.ident "DataMinCardinality", .lparen, .ident (String.ofList (natToChars n)), .iri dp] ++
      renderDataRangeTokens d ++ [.rparen]
  | .dataMax n dp d =>
    [.ident "DataMaxCardinality", .lparen, .ident (String.ofList (natToChars n)), .iri dp] ++
      renderDataRangeTokens d ++ [.rparen]
  | .dataExact n dp d =>
    [.ident "DataExactCardinality", .lparen, .ident (String.ofList (natToChars n)), .iri dp] ++
      renderDataRangeTokens d ++ [.rparen]

def renderAxiomTokens : Axiom → List SrcToken
  | .subClassOf a b =>
    [.ident "SubClassOf", .lparen] ++ renderClassExprTokens a ++ renderClassExprTokens b ++ [.rparen]
  | .equivalentClasses cs =>
    [.ident "EquivalentClasses", .lparen] ++ cs.flatMap renderClassExprTokens ++ [.rparen]
  | .disjointClasses cs =>
    [.ident "DisjointClasses", .lparen] ++ cs.flatMap renderClassExprTokens ++ [.rparen]
  | .disjointUnion h cs =>
    [.ident "DisjointUnion", .lparen, .iri h] ++ cs.flatMap renderClassExprTokens ++ [.rparen]
  | .subObjectProperty r s =>
    [.ident "SubObjectPropertyOf", .lparen] ++ renderObjectPropertyTokens r ++ renderObjectPropertyTokens s ++ [.rparen]
  | .subObjectPropertyChain rs s =>
    [.ident "SubObjectPropertyOf", .lparen, .ident "ObjectPropertyChain", .lparen] ++
      rs.flatMap renderObjectPropertyTokens ++ [.rparen] ++ renderObjectPropertyTokens s ++ [.rparen]
  | .equivalentObjectProperties rs =>
    [.ident "EquivalentObjectProperties", .lparen] ++ rs.flatMap renderObjectPropertyTokens ++ [.rparen]
  | .disjointObjectProperties rs =>
    [.ident "DisjointObjectProperties", .lparen] ++ rs.flatMap renderObjectPropertyTokens ++ [.rparen]
  | .inverseObjectProperties r s =>
    [.ident "InverseObjectProperties", .lparen] ++ renderObjectPropertyTokens r ++ renderObjectPropertyTokens s ++ [.rparen]
  | .objectPropertyDomain r c =>
    [.ident "ObjectPropertyDomain", .lparen] ++ renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .objectPropertyRange r c =>
    [.ident "ObjectPropertyRange", .lparen] ++ renderObjectPropertyTokens r ++ renderClassExprTokens c ++ [.rparen]
  | .functionalObjectProperty r =>
    [.ident "FunctionalObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .inverseFunctionalObjectProperty r =>
    [.ident "InverseFunctionalObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .reflexiveObjectProperty r =>
    [.ident "ReflexiveObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .irreflexiveObjectProperty r =>
    [.ident "IrreflexiveObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .symmetricObjectProperty r =>
    [.ident "SymmetricObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .asymmetricObjectProperty r =>
    [.ident "AsymmetricObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .transitiveObjectProperty r =>
    [.ident "TransitiveObjectProperty", .lparen] ++ renderObjectPropertyTokens r ++ [.rparen]
  | .subDataProperty r s =>
    [.ident "SubDataPropertyOf", .lparen, .iri r, .iri s, .rparen]
  | .equivalentDataProperties ds =>
    [.ident "EquivalentDataProperties", .lparen] ++ ds.map .iri ++ [.rparen]
  | .disjointDataProperties ds =>
    [.ident "DisjointDataProperties", .lparen] ++ ds.map .iri ++ [.rparen]
  | .dataPropertyDomain dp c =>
    [.ident "DataPropertyDomain", .lparen, .iri dp] ++ renderClassExprTokens c ++ [.rparen]
  | .dataPropertyRange dp d =>
    [.ident "DataPropertyRange", .lparen, .iri dp] ++ renderDataRangeTokens d ++ [.rparen]
  | .functionalDataProperty dp =>
    [.ident "FunctionalDataProperty", .lparen, .iri dp, .rparen]
  | .datatypeDefinition dt d =>
    [.ident "DatatypeDefinition", .lparen, .iri dt] ++ renderDataRangeTokens d ++ [.rparen]
  | .hasKey c os ds =>
    [.ident "HasKey", .lparen] ++ renderClassExprTokens c ++ [.lparen] ++
      os.flatMap renderObjectPropertyTokens ++ [.rparen, .lparen] ++ ds.map .iri ++ [.rparen, .rparen]
  | .sameIndividuals inds =>
    [.ident "SameIndividual", .lparen] ++ inds.flatMap renderIndividualTokens ++ [.rparen]
  | .differentIndividuals inds =>
    [.ident "DifferentIndividuals", .lparen] ++ inds.flatMap renderIndividualTokens ++ [.rparen]
  | .classAssertion c a =>
    [.ident "ClassAssertion", .lparen] ++ renderClassExprTokens c ++ renderIndividualTokens a ++ [.rparen]
  | .objectAssertion r a b =>
    [.ident "ObjectPropertyAssertion", .lparen] ++ renderObjectPropertyTokens r ++
      renderIndividualTokens a ++ renderIndividualTokens b ++ [.rparen]
  | .negativeObjectAssertion r a b =>
    [.ident "NegativeObjectPropertyAssertion", .lparen] ++ renderObjectPropertyTokens r ++
      renderIndividualTokens a ++ renderIndividualTokens b ++ [.rparen]
  | .dataAssertion dp a l =>
    [.ident "DataPropertyAssertion", .lparen, .iri dp] ++
      renderIndividualTokens a ++ renderLiteralTokens l ++ [.rparen]
  | .negativeDataAssertion dp a l =>
    [.ident "NegativeDataPropertyAssertion", .lparen, .iri dp] ++
      renderIndividualTokens a ++ renderLiteralTokens l ++ [.rparen]

def renderOntologyTokens (ont : Ontology) (ontIRI : Option IRI := none)
    (verIRI : Option IRI := none) (imports : List IRI := []) : List SrcToken :=
  let header : List SrcToken :=
    match ontIRI, verIRI with
    | some o, some v => [.iri o, .iri v]
    | some o, none => [.iri o]
    | none, _ => []
  let impToks : List SrcToken := imports.flatMap fun imp => [.ident "Import", .lparen, .iri imp, .rparen]
  [.ident "Ontology", .lparen] ++ header ++ impToks ++ ont.flatMap renderAxiomTokens ++ [.rparen]

/-- Canonical W3C OWL 2 Functional-Style Syntax serializer with a kernel-checked
exact round-trip theorem (`parseSourceDocument_renderCanonicalOFN`). -/
def renderCanonicalOFN (ont : Ontology) (ontIRI : Option IRI := none)
    (verIRI : Option IRI := none) (imports : List IRI := []) : String :=
  printSrcTokens (renderOntologyTokens ont ontIRI verIRI imports)

/-! #### Token-level round-trip lemmas -/

private theorem renderDataRangeTokens_pos (d : DataRange) : 0 < (renderDataRangeTokens d).length := by
  cases d <;> simp [renderDataRangeTokens]

private theorem renderDataRangeTokens_head_ne_rparen (d : DataRange) (rest : List SrcToken) :
    ∀ tail, renderDataRangeTokens d ++ rest ≠ .rparen :: tail := by
  cases d <;> intro tail <;> simp [renderDataRangeTokens]

private theorem renderClassExprTokens_pos (c : ClassExpr) : 0 < (renderClassExprTokens c).length := by
  cases c <;> simp [renderClassExprTokens]

private theorem renderClassExprTokens_head_ne_rparen (c : ClassExpr) (rest : List SrcToken) :
    ∀ tail, renderClassExprTokens c ++ rest ≠ .rparen :: tail := by
  cases c <;> intro tail <;> simp [renderClassExprTokens]

private theorem renderAxiomTokens_pos (ax : Axiom) : 0 < (renderAxiomTokens ax).length := by
  cases ax <;> simp [renderAxiomTokens]

private theorem parseIndividualTotal_render (docId : String) (pfx : PrefixMap)
    (a : Individual) (rest : List SrcToken) (hscope : indInScope docId a = true) :
    parseIndividualTotal docId pfx (renderIndividualTokens a ++ rest) = some (a, rest) := by
  cases a with
  | named iri => rfl
  | anonymous d lid =>
    simp only [indInScope, beq_iff_eq] at hscope
    subst hscope
    simp [renderIndividualTokens, parseIndividualTotal, String.toList_append, String.ofList_toList]

private theorem parseObjPropTotal_render (pfx : PrefixMap)
    (r : ObjectProperty) (rest : List SrcToken) :
    parseObjPropTotal pfx (renderObjectPropertyTokens r ++ rest) = some (r, rest) := by
  cases r with
  | named iri => rfl
  | inverse iri => rfl

private theorem parseLiteralTotal_render (pfx : PrefixMap)
    (l : Literal) (rest : List SrcToken) :
    parseLiteralTotal pfx (renderLiteralTokens l ++ rest) = some (l, rest) := by
  cases l; rfl

private theorem parseFacetTotal_render (pfx : PrefixMap)
    (f : Facet) (rest : List SrcToken) :
    parseFacetTotal pfx (renderFacetTokens f ++ rest) = some (f, rest) := by
  cases f with
  | mk name bound =>
    simp [renderFacetTokens, parseFacetTotal, parseIRITotal, parseLiteralTotal_render]

private theorem parseManySimple_render {α : Type}
    (p : List SrcToken → Option (α × List SrcToken))
    (enc : α → List SrcToken) (P : α → Prop)
    (hpos : ∀ x, 0 < (enc x).length)
    (hne : ∀ x rest tail, enc x ++ rest ≠ .rparen :: tail)
    (hstep : ∀ x rest, P x → p (enc x ++ rest) = some (x, rest))
    (xs : List α) (hP : ∀ x ∈ xs, P x) (acc : List α) (rest : List SrcToken) (fuel : Nat)
    (hfuel : (xs.flatMap enc).length + 1 ≤ fuel) :
    parseManySimple p fuel (xs.flatMap enc ++ .rparen :: rest) acc =
      some (acc.reverse ++ xs, rest) := by
  induction xs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ f => simp [parseManySimple]
  | cons x tail ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.flatMap_cons, List.length_append] at hfuel
      have hxpos := hpos x
      have hPx : P x := hP x (List.mem_cons_self ..)
      have hPt : ∀ y ∈ tail, P y := fun y hy => hP y (List.mem_cons_of_mem _ hy)
      simp only [List.flatMap_cons, List.append_assoc]
      have hne' := hne x (tail.flatMap enc ++ .rparen :: rest)
      cases htoks : enc x ++ (tail.flatMap enc ++ .rparen :: rest) with
      | nil =>
        have : 0 = (enc x ++ (tail.flatMap enc ++ .rparen :: rest)).length := by rw [htoks]; rfl
        simp only [List.length_append] at this; omega
      | cons t r =>
        cases t with
        | rparen => exact absurd htoks (hne' r)
        | _ =>
          have hstep' := hstep x (tail.flatMap enc ++ .rparen :: rest) hPx
          rw [htoks] at hstep'
          simp only [parseManySimple, hstep', Option.bind_some]
          have hrem := ih hPt (x :: acc) f (by omega)
          simpa [List.reverse_cons, List.append_assoc] using hrem

private theorem parseDataRangeTotal_render (pfx : PrefixMap) (d : DataRange) :
    ∀ (rest : List SrcToken) (fuel : Nat),
      (renderDataRangeTokens d).length ≤ fuel →
      parseDataRangeTotal pfx fuel (renderDataRangeTokens d ++ rest) = some (d, rest) := by
  induction d with
  | datatype dt =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f => rfl
  | complement d ih =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f =>
      simp only [renderDataRangeTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderDataRangeTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseDataRangeTotal]
      rw [ih (.rparen :: rest) f (by omega)]
  | intersection a b iha ihb =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f =>
      simp only [renderDataRangeTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      have haPos := renderDataRangeTokens_pos a
      have hbPos := renderDataRangeTokens_pos b
      cases f with
      | zero => omega
      | succ f1 =>
        cases f1 with
        | zero => omega
        | succ f2 =>
          simp only [renderDataRangeTokens, List.cons_append, List.nil_append, List.append_assoc,
            parseDataRangeTotal]
          have hneA := renderDataRangeTokens_head_ne_rparen a (renderDataRangeTokens b ++ .rparen :: rest)
          have hneB := renderDataRangeTokens_head_ne_rparen b (.rparen :: rest)
          have hA := iha (renderDataRangeTokens b ++ .rparen :: rest) (f2 + 1) (by omega)
          have hB := ihb (.rparen :: rest) f2 (by omega)
          have hL1 : parseDataRangeList pfx (f2 + 2)
              (renderDataRangeTokens a ++ (renderDataRangeTokens b ++ .rparen :: rest)) [] =
              some ([a, b], rest) := by
            cases htA : renderDataRangeTokens a ++ (renderDataRangeTokens b ++ .rparen :: rest) with
            | nil =>
              have := congrArg List.length htA; simp only [List.length_append, List.length_nil] at this; omega
            | cons tA rA =>
              cases tA with
              | rparen => exact absurd htA (hneA rA)
              | _ =>
                rw [htA] at hA
                simp only [parseDataRangeList, hA, Option.bind_some]
                cases htB : renderDataRangeTokens b ++ .rparen :: rest with
                | nil =>
                  have := congrArg List.length htB; simp only [List.length_append, List.length_nil] at this; omega
                | cons tB rB =>
                  cases tB with
                  | rparen => exact absurd htB (hneB rB)
                  | _ =>
                    rw [htB] at hB
                    simp only [hB, Option.bind_some]
                    cases f2 with
                    | zero => omega
                    | succ f3 => simp [parseDataRangeList]
          rw [hL1]; rfl
  | union a b iha ihb =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f =>
      simp only [renderDataRangeTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      have haPos := renderDataRangeTokens_pos a
      have hbPos := renderDataRangeTokens_pos b
      cases f with
      | zero => omega
      | succ f1 =>
        cases f1 with
        | zero => omega
        | succ f2 =>
          simp only [renderDataRangeTokens, List.cons_append, List.nil_append, List.append_assoc,
            parseDataRangeTotal]
          have hneA := renderDataRangeTokens_head_ne_rparen a (renderDataRangeTokens b ++ .rparen :: rest)
          have hneB := renderDataRangeTokens_head_ne_rparen b (.rparen :: rest)
          have hA := iha (renderDataRangeTokens b ++ .rparen :: rest) (f2 + 1) (by omega)
          have hB := ihb (.rparen :: rest) f2 (by omega)
          have hL1 : parseDataRangeList pfx (f2 + 2)
              (renderDataRangeTokens a ++ (renderDataRangeTokens b ++ .rparen :: rest)) [] =
              some ([a, b], rest) := by
            cases htA : renderDataRangeTokens a ++ (renderDataRangeTokens b ++ .rparen :: rest) with
            | nil =>
              have := congrArg List.length htA; simp only [List.length_append, List.length_nil] at this; omega
            | cons tA rA =>
              cases tA with
              | rparen => exact absurd htA (hneA rA)
              | _ =>
                rw [htA] at hA
                simp only [parseDataRangeList, hA, Option.bind_some]
                cases htB : renderDataRangeTokens b ++ .rparen :: rest with
                | nil =>
                  have := congrArg List.length htB; simp only [List.length_append, List.length_nil] at this; omega
                | cons tB rB =>
                  cases tB with
                  | rparen => exact absurd htB (hneB rB)
                  | _ =>
                    rw [htB] at hB
                    simp only [hB, Option.bind_some]
                    cases f2 with
                    | zero => omega
                    | succ f3 => simp [parseDataRangeList]
          rw [hL1]; rfl
  | oneOf ls =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f =>
      simp only [renderDataRangeTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderDataRangeTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseDataRangeTotal]
      rw [parseManySimple_render (parseLiteralTotal pfx) renderLiteralTokens (fun _ => True)
        (fun l => by simp [renderLiteralTokens])
        (fun l r tail => by simp [renderLiteralTokens])
        (fun l r _ => parseLiteralTotal_render pfx l r)
        ls (fun _ _ => trivial) [] rest f (by omega)]
      rfl
  | restriction dt fs =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp [renderDataRangeTokens] at hfuel
    | succ f =>
      simp only [renderDataRangeTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderDataRangeTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseDataRangeTotal, parseIRITotal, Option.bind_some]
      rw [parseManySimple_render (parseFacetTotal pfx) renderFacetTokens (fun _ => True)
        (fun fac => by simp [renderFacetTokens, renderLiteralTokens])
        (fun fac r tail => by simp [renderFacetTokens])
        (fun fac r _ => parseFacetTotal_render pfx fac r)
        fs (fun _ _ => trivial) [] rest f (by omega)]
      rfl

private theorem parseClassExprTotal_render (docId : String) (pfx : PrefixMap) (c : ClassExpr) :
    ∀ (rest : List SrcToken) (fuel : Nat),
      classInScope docId c = true →
      (renderClassExprTokens c).length ≤ fuel →
      parseClassExprTotal docId pfx fuel (renderClassExprTokens c ++ rest) = some (c, rest) := by
  induction c with
  | named iri =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f => rfl
  | complement c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [ih (.rparen :: rest) f hsc (by omega)]
  | intersection a b iha ihb =>
    intro rest fuel hsc hfuel
    obtain ⟨hsa, hsb⟩ := Bool.and_eq_true_iff.mp hsc
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      have haPos := renderClassExprTokens_pos a
      have hbPos := renderClassExprTokens_pos b
      cases f with
      | zero => omega
      | succ f1 =>
        cases f1 with
        | zero => omega
        | succ f2 =>
          simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
            parseClassExprTotal]
          have hneA := renderClassExprTokens_head_ne_rparen a (renderClassExprTokens b ++ .rparen :: rest)
          have hneB := renderClassExprTokens_head_ne_rparen b (.rparen :: rest)
          have hA := iha (renderClassExprTokens b ++ .rparen :: rest) (f2 + 1) hsa (by omega)
          have hB := ihb (.rparen :: rest) f2 hsb (by omega)
          have hL1 : parseClassExprList docId pfx (f2 + 2)
              (renderClassExprTokens a ++ (renderClassExprTokens b ++ .rparen :: rest)) [] =
              some ([a, b], rest) := by
            cases htA : renderClassExprTokens a ++ (renderClassExprTokens b ++ .rparen :: rest) with
            | nil =>
              have := congrArg List.length htA; simp only [List.length_append, List.length_nil] at this; omega
            | cons tA rA =>
              cases tA with
              | rparen => exact absurd htA (hneA rA)
              | _ =>
                rw [htA] at hA
                simp only [parseClassExprList, hA, Option.bind_some]
                cases htB : renderClassExprTokens b ++ .rparen :: rest with
                | nil =>
                  have := congrArg List.length htB; simp only [List.length_append, List.length_nil] at this; omega
                | cons tB rB =>
                  cases tB with
                  | rparen => exact absurd htB (hneB rB)
                  | _ =>
                    rw [htB] at hB
                    simp only [hB, Option.bind_some]
                    cases f2 with
                    | zero => omega
                    | succ f3 => simp [parseClassExprList]
          rw [hL1]; rfl
  | union a b iha ihb =>
    intro rest fuel hsc hfuel
    obtain ⟨hsa, hsb⟩ := Bool.and_eq_true_iff.mp hsc
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      have haPos := renderClassExprTokens_pos a
      have hbPos := renderClassExprTokens_pos b
      cases f with
      | zero => omega
      | succ f1 =>
        cases f1 with
        | zero => omega
        | succ f2 =>
          simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
            parseClassExprTotal]
          have hneA := renderClassExprTokens_head_ne_rparen a (renderClassExprTokens b ++ .rparen :: rest)
          have hneB := renderClassExprTokens_head_ne_rparen b (.rparen :: rest)
          have hA := iha (renderClassExprTokens b ++ .rparen :: rest) (f2 + 1) hsa (by omega)
          have hB := ihb (.rparen :: rest) f2 hsb (by omega)
          have hL1 : parseClassExprList docId pfx (f2 + 2)
              (renderClassExprTokens a ++ (renderClassExprTokens b ++ .rparen :: rest)) [] =
              some ([a, b], rest) := by
            cases htA : renderClassExprTokens a ++ (renderClassExprTokens b ++ .rparen :: rest) with
            | nil =>
              have := congrArg List.length htA; simp only [List.length_append, List.length_nil] at this; omega
            | cons tA rA =>
              cases tA with
              | rparen => exact absurd htA (hneA rA)
              | _ =>
                rw [htA] at hA
                simp only [parseClassExprList, hA, Option.bind_some]
                cases htB : renderClassExprTokens b ++ .rparen :: rest with
                | nil =>
                  have := congrArg List.length htB; simp only [List.length_append, List.length_nil] at this; omega
                | cons tB rB =>
                  cases tB with
                  | rparen => exact absurd htB (hneB rB)
                  | _ =>
                    rw [htB] at hB
                    simp only [hB, Option.bind_some]
                    cases f2 with
                    | zero => omega
                    | succ f3 => simp [parseClassExprList]
          rw [hL1]; rfl
  | oneOf inds =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [parseManySimple_render (parseIndividualTotal docId pfx) renderIndividualTokens
        (fun a => indInScope docId a = true)
        (fun a => by cases a <;> simp [renderIndividualTokens])
        (fun a r tail => by cases a <;> simp [renderIndividualTokens])
        (fun a r ha => parseIndividualTotal_render docId pfx a r ha)
        inds (List.all_eq_true.mp hsc) [] rest f (by omega)]
      rfl
  | objectSome r c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [parseObjPropTotal_render, Option.bind_some, ih (.rparen :: rest) f hsc (by omega)]
  | objectAll r c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [parseObjPropTotal_render, Option.bind_some, ih (.rparen :: rest) f hsc (by omega)]
  | objectValue r a =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [parseObjPropTotal_render, Option.bind_some, parseIndividualTotal_render docId pfx a _ hsc]
  | objectSelf r =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal]
      rw [parseObjPropTotal_render]
  | objectMin n r c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some]
      rw [parseObjPropTotal_render, Option.bind_some]
      have hne := renderClassExprTokens_head_ne_rparen c (.rparen :: rest)
      have hC := ih (.rparen :: rest) f hsc (by omega)
      cases ht : renderClassExprTokens c ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderClassExprTokens_pos c
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hC; simp [hC]
  | objectMax n r c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some]
      rw [parseObjPropTotal_render, Option.bind_some]
      have hne := renderClassExprTokens_head_ne_rparen c (.rparen :: rest)
      have hC := ih (.rparen :: rest) f hsc (by omega)
      cases ht : renderClassExprTokens c ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderClassExprTokens_pos c
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hC; simp [hC]
  | objectExact n r c ih =>
    intro rest fuel hsc hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some]
      rw [parseObjPropTotal_render, Option.bind_some]
      have hne := renderClassExprTokens_head_ne_rparen c (.rparen :: rest)
      have hC := ih (.rparen :: rest) f hsc (by omega)
      cases ht : renderClassExprTokens c ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderClassExprTokens_pos c
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hC; simp [hC]
  | dataSome dp d =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseIRITotal, Option.bind_some]
      rw [parseDataRangeTotal_render pfx d (.rparen :: rest) f (by omega)]
  | dataAll dp d =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseIRITotal, Option.bind_some]
      rw [parseDataRangeTotal_render pfx d (.rparen :: rest) f (by omega)]
  | dataValue dp l =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseIRITotal, Option.bind_some]
      rw [parseLiteralTotal_render pfx l]
  | dataMin n dp d =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some,
        parseIRITotal]
      have hne := renderDataRangeTokens_head_ne_rparen d (.rparen :: rest)
      have hD := parseDataRangeTotal_render pfx d (.rparen :: rest) f (by omega)
      cases ht : renderDataRangeTokens d ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderDataRangeTokens_pos d
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hD; simp [hD]
  | dataMax n dp d =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some,
        parseIRITotal]
      have hne := renderDataRangeTokens_head_ne_rparen d (.rparen :: rest)
      have hD := parseDataRangeTotal_render pfx d (.rparen :: rest) f (by omega)
      cases ht : renderDataRangeTokens d ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderDataRangeTokens_pos d
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hD; simp [hD]
  | dataExact n dp d =>
    intro rest fuel _ hfuel
    cases fuel with
    | zero => simp [renderClassExprTokens] at hfuel
    | succ f =>
      simp only [renderClassExprTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [renderClassExprTokens, List.cons_append, List.nil_append, List.append_assoc,
        parseClassExprTotal, parseNatTotal, parseNatStr_natToChars, Option.map_some, Option.bind_some,
        parseIRITotal]
      have hne := renderDataRangeTokens_head_ne_rparen d (.rparen :: rest)
      have hD := parseDataRangeTotal_render pfx d (.rparen :: rest) f (by omega)
      cases ht : renderDataRangeTokens d ++ .rparen :: rest with
      | nil =>
        have hlen := congrArg List.length ht; have := renderDataRangeTokens_pos d
        simp only [List.length_append, List.length_nil] at hlen; omega
      | cons t r' =>
        cases t with
        | rparen => exact absurd ht (hne r')
        | _ => rw [ht] at hD; simp [hD]

private theorem parseClassExprList_render (docId : String) (pfx : PrefixMap)
    (cs : List ClassExpr) (hsc : cs.all (classInScope docId) = true)
    (acc : List ClassExpr) (rest : List SrcToken) (fuel : Nat)
    (hfuel : (cs.flatMap renderClassExprTokens).length + 1 ≤ fuel) :
    parseClassExprList docId pfx fuel (cs.flatMap renderClassExprTokens ++ .rparen :: rest) acc =
      some (acc.reverse ++ cs, rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ f => simp [parseClassExprList]
  | cons c tail ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.all_cons, Bool.and_eq_true] at hsc
      simp only [List.flatMap_cons, List.length_append] at hfuel
      have hcPos := renderClassExprTokens_pos c
      simp only [List.flatMap_cons, List.append_assoc]
      have hne := renderClassExprTokens_head_ne_rparen c (tail.flatMap renderClassExprTokens ++ .rparen :: rest)
      have hC := parseClassExprTotal_render docId pfx c
        (tail.flatMap renderClassExprTokens ++ .rparen :: rest) f hsc.1 (by omega)
      cases ht : renderClassExprTokens c ++ (tail.flatMap renderClassExprTokens ++ .rparen :: rest) with
      | nil =>
        have := congrArg List.length ht; simp only [List.length_append, List.length_nil] at this; omega
      | cons t r =>
        cases t with
        | rparen => exact absurd ht (hne r)
        | _ =>
          rw [ht] at hC
          simp only [parseClassExprList, hC, Option.bind_some]
          simpa [List.reverse_cons, List.append_assoc] using ih hsc.2 (c :: acc) f (by omega)

private theorem skipAnnotationsTotal_ne_annot (fuel : Nat) (toks : List SrcToken)
    (h : ∀ rest, toks ≠ .ident "Annotation" :: rest) :
    skipAnnotationsTotal fuel toks = some toks := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [skipAnnotationsTotal]
    split
    · cases toks with
      | nil => contradiction
      | cons t rest =>
        rename_i heq
        have ht : t = .ident "Annotation" := Option.some.inj heq
        subst t
        exact False.elim (h rest rfl)
    · rfl

private theorem renderClassExprTokens_ne_annot (c : ClassExpr) (rest : List SrcToken) :
    ∀ tail, renderClassExprTokens c ++ rest ≠ .ident "Annotation" :: tail := by
  cases c <;> intro tail <;> simp [renderClassExprTokens]

private theorem renderObjPropTokens_ne_annot (r : ObjectProperty) (rest : List SrcToken) :
    ∀ tail, renderObjectPropertyTokens r ++ rest ≠ .ident "Annotation" :: tail := by
  cases r <;> intro tail <;> simp [renderObjectPropertyTokens]

private theorem flatMap_ne_annot {α : Type} {enc : α → List SrcToken}
    (hne : ∀ x rest tail, enc x ++ rest ≠ .ident "Annotation" :: tail)
    (xs : List α) (rest : List SrcToken) :
    ∀ tail, xs.flatMap enc ++ .rparen :: rest ≠ .ident "Annotation" :: tail := by
  cases xs with
  | nil => intro tail; simp
  | cons x xs' =>
    intro tail
    simpa [List.flatMap_cons, List.append_assoc] using hne x (xs'.flatMap enc ++ .rparen :: rest) tail

private theorem map_iri_ne_annot (ds : List IRI) (rest : List SrcToken) :
    ∀ tail, ds.map .iri ++ .rparen :: rest ≠ .ident "Annotation" :: tail := by
  cases ds <;> intro tail <;> simp

private theorem map_iri_eq_flatMap (ds : List IRI) :
    ds.map SrcToken.iri = ds.flatMap (fun i => [SrcToken.iri i]) := by
  induction ds <;> simp [*]

private theorem parseAxiomTotal_render (docId : String) (pfx : PrefixMap) (ax : Axiom)
    (rest : List SrcToken) (fuel : Nat)
    (hsc : axiomInScope docId ax = true)
    (hfuel : (renderAxiomTokens ax).length ≤ fuel) :
    parseAxiomTotal docId pfx fuel (renderAxiomTokens ax ++ rest) = some (some ax, rest) := by
  cases ax with
  | subClassOf a b =>
    obtain ⟨hsa, hsb⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderClassExprTokens_ne_annot a _), Option.bind_some]
    rw [parseClassExprTotal_render docId pfx a _ fuel hsa (by omega), Option.bind_some]
    rw [parseClassExprTotal_render docId pfx b _ fuel hsb (by omega)]
  | equivalentClasses cs =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot renderClassExprTokens_ne_annot cs rest),
      Option.bind_some]
    rw [parseClassExprList_render docId pfx cs hsc [] rest fuel (by omega)]; rfl
  | disjointClasses cs =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot renderClassExprTokens_ne_annot cs rest),
      Option.bind_some]
    rw [parseClassExprList_render docId pfx cs hsc [] rest fuel (by omega)]; rfl
  | disjointUnion h cs =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseClassExprList_render docId pfx cs hsc [] rest fuel (by omega)]; rfl
  | subObjectProperty r s =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    cases r <;> cases s <;> rfl
  | subObjectPropertyChain rs s =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    change ((parseManySimple (parseObjPropTotal pfx) fuel
        (rs.flatMap renderObjectPropertyTokens ++ .rparen :: (renderObjectPropertyTokens s ++ .rparen :: rest))
        []).bind fun x =>
          match parseObjPropTotal pfx x.2 with
          | some (sup, .rparen :: rem) => some (some (Axiom.subObjectPropertyChain x.1 sup), rem)
          | _ => none) = _
    rw [parseManySimple_render (parseObjPropTotal pfx) renderObjectPropertyTokens (fun _ => True)
      (fun r => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem tail => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem _ => parseObjPropTotal_render pfx r rem)
      rs (fun _ _ => trivial) [] (renderObjectPropertyTokens s ++ .rparen :: rest) fuel (by omega)]
    simp only [List.reverse_nil, List.nil_append, Option.bind_some]
    rw [parseObjPropTotal_render]
  | equivalentObjectProperties rs =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot renderObjPropTokens_ne_annot rs rest),
      Option.bind_some]
    rw [parseManySimple_render (parseObjPropTotal pfx) renderObjectPropertyTokens (fun _ => True)
      (fun r => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem tail => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem _ => parseObjPropTotal_render pfx r rem)
      rs (fun _ _ => trivial) [] rest fuel (by omega)]; rfl
  | disjointObjectProperties rs =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot renderObjPropTokens_ne_annot rs rest),
      Option.bind_some]
    rw [parseManySimple_render (parseObjPropTotal pfx) renderObjectPropertyTokens (fun _ => True)
      (fun r => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem tail => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem _ => parseObjPropTotal_render pfx r rem)
      rs (fun _ _ => trivial) [] rest fuel (by omega)]; rfl
  | inverseObjectProperties r s =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    rw [parseObjPropTotal_render, Option.bind_some, parseObjPropTotal_render]
  | objectPropertyDomain r c =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    rw [parseObjPropTotal_render, Option.bind_some, parseClassExprTotal_render docId pfx c _ fuel hsc (by omega)]
  | objectPropertyRange r c =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    rw [parseObjPropTotal_render, Option.bind_some, parseClassExprTotal_render docId pfx c _ fuel hsc (by omega)]
  | functionalObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | inverseFunctionalObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | reflexiveObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | irreflexiveObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | symmetricObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | asymmetricObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | transitiveObjectProperty r =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some,
      parseObjPropTotal_render]
  | subDataProperty r s =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, parseAxiomTotal]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp)]; rfl
  | equivalentDataProperties ds =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil, List.length_map] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (map_iri_ne_annot ds rest), Option.bind_some]
    have hmap := map_iri_eq_flatMap ds
    rw [hmap]
    rw [parseManySimple_render (parseIRITotal pfx) (fun i => [SrcToken.iri i]) (fun _ => True)
      (fun _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
      ds (fun _ _ => trivial) [] rest fuel (by rw [← hmap, List.length_map]; omega)]; rfl
  | disjointDataProperties ds =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil, List.length_map] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (map_iri_ne_annot ds rest), Option.bind_some]
    have hmap := map_iri_eq_flatMap ds
    rw [hmap]
    rw [parseManySimple_render (parseIRITotal pfx) (fun i => [SrcToken.iri i]) (fun _ => True)
      (fun _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
      ds (fun _ _ => trivial) [] rest fuel (by rw [← hmap, List.length_map]; omega)]; rfl
  | dataPropertyDomain dp c =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseClassExprTotal_render docId pfx c _ fuel hsc (by omega)]
  | dataPropertyRange dp d =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseDataRangeTotal_render pfx d _ fuel (by omega)]
  | functionalDataProperty dp =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, parseAxiomTotal]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp)]; rfl
  | datatypeDefinition dt d =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseDataRangeTotal_render pfx d _ fuel (by omega)]
  | hasKey c os ds =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil, List.length_map] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderClassExprTokens_ne_annot c _), Option.bind_some]
    rw [parseClassExprTotal_render docId pfx c _ fuel hsc (by omega), Option.bind_some]
    dsimp only [Prod.fst, Prod.snd]
    rw [parseManySimple_render (parseObjPropTotal pfx) renderObjectPropertyTokens (fun _ => True)
      (fun r => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem tail => by cases r <;> simp [renderObjectPropertyTokens])
      (fun r rem _ => parseObjPropTotal_render pfx r rem)
      os (fun _ _ => trivial) [] (SrcToken.lparen :: (ds.map SrcToken.iri ++ .rparen :: .rparen :: rest)) fuel (by omega)]
    simp only [List.reverse_nil, List.nil_append, Option.bind_some]
    have hmap := map_iri_eq_flatMap ds
    rw [hmap]
    rw [parseManySimple_render (parseIRITotal pfx) (fun i => [SrcToken.iri i]) (fun _ => True)
      (fun _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
      ds (fun _ _ => trivial) [] (.rparen :: rest) fuel (by rw [← hmap, List.length_map]; omega)]
    rfl
  | sameIndividuals inds =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot
      (fun a r tail => by
        cases a with
        | named _ => simp [renderIndividualTokens]
        | anonymous _ lid =>
          simp only [renderIndividualTokens, List.singleton_append, ne_eq, List.cons.injEq,
            SrcToken.ident.injEq, not_and]
          intro heq
          have := congrArg String.toList heq
          simp [String.toList_append] at this) inds rest), Option.bind_some]
    rw [parseManySimple_render (parseIndividualTotal docId pfx) renderIndividualTokens
      (fun a => indInScope docId a = true)
      (fun a => by cases a <;> simp [renderIndividualTokens])
      (fun a r tail => by cases a <;> simp [renderIndividualTokens])
      (fun a r ha => parseIndividualTotal_render docId pfx a r ha)
      inds (List.all_eq_true.mp hsc) [] rest fuel (by omega)]; rfl
  | differentIndividuals inds =>
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (flatMap_ne_annot
      (fun a r tail => by
        cases a with
        | named _ => simp [renderIndividualTokens]
        | anonymous _ lid =>
          simp only [renderIndividualTokens, List.singleton_append, ne_eq, List.cons.injEq,
            SrcToken.ident.injEq, not_and]
          intro heq
          have := congrArg String.toList heq
          simp [String.toList_append] at this) inds rest), Option.bind_some]
    rw [parseManySimple_render (parseIndividualTotal docId pfx) renderIndividualTokens
      (fun a => indInScope docId a = true)
      (fun a => by cases a <;> simp [renderIndividualTokens])
      (fun a r tail => by cases a <;> simp [renderIndividualTokens])
      (fun a r ha => parseIndividualTotal_render docId pfx a r ha)
      inds (List.all_eq_true.mp hsc) [] rest fuel (by omega)]; rfl
  | classAssertion c a =>
    obtain ⟨hscC, hscA⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [renderAxiomTokens, List.length_append, List.length_cons, List.length_nil] at hfuel
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderClassExprTokens_ne_annot c _), Option.bind_some]
    rw [parseClassExprTotal_render docId pfx c _ fuel hscC (by omega), Option.bind_some]
    rw [parseIndividualTotal_render docId pfx a _ hscA]
  | objectAssertion r a b =>
    obtain ⟨hscA, hscB⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    rw [parseObjPropTotal_render, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx a _ hscA, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx b _ hscB]
  | negativeObjectAssertion r a b =>
    obtain ⟨hscA, hscB⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (renderObjPropTokens_ne_annot r _), Option.bind_some]
    rw [parseObjPropTotal_render, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx a _ hscA, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx b _ hscB]
  | dataAssertion dp a l =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx a _ hsc, Option.bind_some]
    rw [parseLiteralTotal_render pfx l]
  | negativeDataAssertion dp a l =>
    simp only [renderAxiomTokens, List.cons_append, List.nil_append, List.append_assoc, parseAxiomTotal, readAxiomTag,
      parseAxiomArgs]
    rw [skipAnnotationsTotal_ne_annot fuel _ (fun _ => by simp), Option.bind_some]
    simp only [parseIRITotal, Option.bind_some]
    rw [parseIndividualTotal_render docId pfx a _ hsc, Option.bind_some]
    rw [parseLiteralTotal_render pfx l]

private theorem renderAxiomTokens_head_ne_rparen_import (ax : Axiom) (rest : List SrcToken) :
    (∀ t, renderAxiomTokens ax ++ rest ≠ .rparen :: t) ∧
    (∀ t, renderAxiomTokens ax ++ rest ≠ .ident "Import" :: t) := by
  cases ax <;> constructor <;> intro t <;> simp [renderAxiomTokens]

private theorem parseOntologyBodyTotal_renderAxioms (docId : String) (pfx : PrefixMap)
    (ont : Ontology) (hscope : docInScope docId ont = true)
    (impsAcc : List IRI) (axsAcc : Ontology) (fuel : Nat)
    (hfuel : (ont.flatMap renderAxiomTokens).length + 1 ≤ fuel) :
    parseOntologyBodyTotal docId pfx fuel (ont.flatMap renderAxiomTokens ++ [.rparen]) impsAcc axsAcc =
      some (impsAcc.reverse, axsAcc.reverse ++ ont, []) := by
  induction ont generalizing axsAcc fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ f => simp [parseOntologyBodyTotal]
  | cons ax tail ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [docInScope, List.all_cons, Bool.and_eq_true] at hscope
      simp only [List.flatMap_cons, List.length_append] at hfuel
      have hpos := renderAxiomTokens_pos ax
      simp only [List.flatMap_cons, List.append_assoc]
      have ⟨hneR, hneI⟩ := renderAxiomTokens_head_ne_rparen_import ax (tail.flatMap renderAxiomTokens ++ [.rparen])
      have hAx := parseAxiomTotal_render docId pfx ax
        (tail.flatMap renderAxiomTokens ++ [.rparen]) f hscope.1 (by omega)
      cases ht : renderAxiomTokens ax ++ (tail.flatMap renderAxiomTokens ++ [.rparen]) with
      | nil =>
        have := congrArg List.length ht; simp only [List.length_append, List.length_nil] at this; omega
      | cons t r =>
        cases t with
        | rparen => exact absurd ht (hneR r)
        | ident s =>
          by_cases hs : s = "Import"
          · subst hs; exact absurd ht (hneI r)
          · rw [ht] at hAx
            rw [parseOntologyBodyTotal.eq_4 _ _ _ _ _ _ (by simp) (by simp [hs])]
            simp only [hAx, Option.bind_some]
            simpa [List.reverse_cons, List.append_assoc] using ih hscope.2 (ax :: axsAcc) f (by omega)
        | _ =>
          rw [ht] at hAx
          simp only [parseOntologyBodyTotal, hAx, Option.bind_some]
          simpa [List.reverse_cons, List.append_assoc] using ih hscope.2 (ax :: axsAcc) f (by omega)

private theorem parseOntologyBodyTotal_renderImports (docId : String) (pfx : PrefixMap)
    (imports : List IRI) (ont : Ontology) (hscope : docInScope docId ont = true)
    (impsAcc : List IRI) (fuel : Nat)
    (hfuel : (imports.flatMap fun imp => [SrcToken.ident "Import", .lparen, .iri imp, .rparen]).length +
      (ont.flatMap renderAxiomTokens).length + 1 ≤ fuel) :
    parseOntologyBodyTotal docId pfx fuel
      ((imports.flatMap fun imp => [.ident "Import", .lparen, .iri imp, .rparen]) ++
        ont.flatMap renderAxiomTokens ++ [.rparen]) impsAcc [] =
      some (impsAcc.reverse ++ imports, ont, []) := by
  induction imports generalizing impsAcc fuel with
  | nil =>
    simpa using parseOntologyBodyTotal_renderAxioms docId pfx ont hscope impsAcc [] fuel (by omega)
  | cons imp rest ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at hfuel
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
        parseOntologyBodyTotal, parseIRITotal]
      have hrec := ih (imp :: impsAcc) f (by omega)
      simpa [List.reverse_cons, List.append_assoc] using hrec

private theorem head_body_not_iri (imports : List IRI) (ont : Ontology) :
    ∀ s r, (imports.flatMap fun imp => [SrcToken.ident "Import", .lparen, .iri imp, .rparen]) ++
      ont.flatMap renderAxiomTokens ++ [.rparen] ≠ .iri s :: r := by
  cases imports with
  | cons _ _ => intro s r; simp
  | nil =>
    cases ont with
    | nil => intro s r; simp
    | cons ax _ =>
      cases ax <;> intro s r <;> simp [renderAxiomTokens]

private theorem parseOntologyHeader_noIRI (body : List SrcToken)
    (h : ∀ s r, body ≠ .iri s :: r) :
    parseOntologyHeader body = (none, none, body) := by
  unfold parseOntologyHeader
  split
  · exfalso; exact h _ _ rfl
  · exfalso; exact h _ _ rfl
  · rfl

private theorem parseOntologyHeader_one (o : IRI) (body : List SrcToken)
    (h : ∀ s r, body ≠ .iri s :: r) :
    parseOntologyHeader (.iri o :: body) = (some o, none, body) := by
  cases body with
  | nil => rfl
  | cons t r =>
    cases t with
    | iri s => exact False.elim (h s r rfl)
    | _ => rfl

theorem parseDocumentTokens_renderOntologyTokens (docId : String) (ont : Ontology)
    (ontIRI verIRI : Option IRI) (imports : List IRI)
    (hver : ontIRI = none → verIRI = none)
    (hscope : docInScope docId ont = true) :
    parseDocumentTokens docId (renderOntologyTokens ont ontIRI verIRI imports) =
      some ⟨docId, defaultPrefixes, ontIRI, verIRI, imports, ont⟩ := by
  let body := (imports.flatMap fun imp => [SrcToken.ident "Import", .lparen, .iri imp, .rparen]) ++
    (ont.flatMap renderAxiomTokens ++ [.rparen])
  have hnot : ∀ i rest, body ≠ .iri i :: rest := by
    simpa [body, List.append_assoc] using head_body_not_iri imports ont
  let header := (ontIRI.toList ++ verIRI.toList).map SrcToken.iri
  have hr : renderOntologyTokens ont ontIRI verIRI imports =
      .ident "Ontology" :: .lparen :: (header ++ body) := by
    cases ontIRI with
    | none =>
      have hv := hver rfl
      subst verIRI
      simp [renderOntologyTokens, header, body, List.append_assoc]
    | some o =>
      cases verIRI <;> simp [renderOntologyTokens, header, body, List.append_assoc]
  have hh : parseOntologyHeader (header ++ body) = (ontIRI, verIRI, body) := by
    cases ontIRI with
    | none =>
      have hv := hver rfl
      subst verIRI
      exact parseOntologyHeader_noIRI body hnot
    | some o =>
      cases verIRI with
      | none => exact parseOntologyHeader_one o body hnot
      | some v => rfl
  rw [hr]
  let tokens := SrcToken.ident "Ontology" :: SrcToken.lparen :: (header ++ body)
  let fuel := tokens.length + 1
  change parseDocumentTokens docId tokens = _
  simp only [parseDocumentTokens]
  change (match parseOntologyBodyTotal docId defaultPrefixes fuel
          (parseOntologyHeader (header ++ body)).2.2 [] [] with
        | some (imps, ontology, []) =>
          some (SourceDocument.mk docId defaultPrefixes
            (parseOntologyHeader (header ++ body)).1 (parseOntologyHeader (header ++ body)).2.1 imps ontology)
        | _ => none) = _
  rw [hh]
  have hlen : (imports.flatMap fun imp => [SrcToken.ident "Import", .lparen, .iri imp, .rparen]).length +
      (ont.flatMap renderAxiomTokens).length + 1 ≤
      (SrcToken.ident "Ontology" :: SrcToken.lparen :: (header ++ body)).length + 1 := by
    simp [body, List.length_append] <;> omega
  have hbody := parseOntologyBodyTotal_renderImports docId defaultPrefixes imports ont hscope [] _ hlen
  have hb : parseOntologyBodyTotal docId defaultPrefixes fuel body [] [] =
      some (imports, ont, []) := by
    simpa only [body, List.append_assoc, List.reverse_nil, List.nil_append] using hbody
  rw [hb]

/-- Exact text-level round trip for the typed logical AST:
parsing `renderCanonicalOFN ont ontIRI verIRI imports` recovers the exact typed
ontology, header IRIs, and `Import(...)` declarations whenever every token in
`renderOntologyTokens` is lexically clean (no `'>'` in IRIs, no `'"'`/`'\\'` in
raw literals, identifier-safe anonymous local IDs) and anonymous individuals are
scoped to `docId`. -/
theorem parseSourceDocument_renderCanonicalOFN (docId : String) (ont : Ontology)
    (ontIRI verIRI : Option IRI) (imports : List IRI)
    (hver : ontIRI = none → verIRI = none)
    (hscope : docInScope docId ont = true)
    (hclean : ∀ t ∈ renderOntologyTokens ont ontIRI verIRI imports, CleanToken t) :
    parseSourceDocument docId (renderCanonicalOFN ont ontIRI verIRI imports) =
      some ⟨docId, defaultPrefixes, ontIRI, verIRI, imports, ont⟩ := by
  unfold parseSourceDocument renderCanonicalOFN
  rw [tokenizeTotal_printSrcTokens _ hclean, Option.bind_some]
  rw [parseDocumentTokens_renderOntologyTokens docId ont ontIRI verIRI imports hver hscope]
  simp [hscope]

/-! ### 5. Total Verified Multi-Document `owl:imports` Closure Resolver -/

/-- Canonical document identifier `"doc:<idx>"`, reusing `WiderData.natToDigits`
so injectivity follows from the decimal printer round trip. -/
def mkDocId (idx : Nat) : String :=
  "doc:" ++ String.ofList (natToChars idx)

theorem mkDocId_injective {m n : Nat} (h : mkDocId m = mkDocId n) : m = n := by
  have hlist := congrArg String.toList h
  simp only [mkDocId, String.toList_append, String.toList_ofList] at hlist
  have hdig : natToChars m = natToChars n := List.append_cancel_left hlist
  have hdec := congrArg (fun cs => parseNatStr (String.ofList cs)) hdig
  simpa only [parseNatStr_natToChars, Option.some.injEq] using hdec

structure LibraryEntry where
  key : IRI
  doc : SourceDocument
  deriving Repr, BEq

def parseLibrary (idx : Nat) : List (IRI × String) → Option (List LibraryEntry)
  | [] => some []
  | (key, text) :: rest =>
    (parseSourceDocument (mkDocId idx) text).bind fun doc =>
      (parseLibrary (idx + 1) rest).map fun entries =>
        ⟨key, doc⟩ :: entries

private theorem parseLibrary_spec :
    ∀ (idx : Nat) (lib : List (IRI × String)) (entries : List LibraryEntry),
      parseLibrary idx lib = some entries →
      (entries.map (fun e => e.doc.docId)).Nodup ∧
      (∀ e ∈ entries,
        (∃ k ≥ idx, e.doc.docId = mkDocId k ∧
          ∃ txt, (e.key, txt) ∈ lib ∧ parseSourceDocument (mkDocId k) txt = some e.doc) ∧
        docInScope e.doc.docId e.doc.ontology = true) := by
  intro idx lib
  induction lib generalizing idx with
  | nil =>
    intro entries h
    simp only [parseLibrary, Option.some.injEq] at h
    subst h; simp
  | cons pair rest ih =>
    rcases pair with ⟨key, text⟩
    intro entries h
    simp only [parseLibrary, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    rcases h with ⟨doc, hdoc, tail, htail, rfl⟩
    obtain ⟨hdocId, hdocScope⟩ := parseSourceDocument_inScope hdoc
    obtain ⟨hndTail, hspecTail⟩ := ih (idx + 1) tail htail
    constructor
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hndTail⟩
      intro hmem
      obtain ⟨e, heMem, heEq⟩ := List.mem_map.mp hmem
      obtain ⟨⟨k, hkGe, hkId, _⟩, _⟩ := hspecTail e heMem
      have heq : k = idx := mkDocId_injective (hkId.symm.trans (heEq.trans hdocId))
      omega
    · intro e heMem
      rcases List.mem_cons.mp heMem with rfl | heTail
      · exact ⟨⟨idx, Nat.le_refl _, hdocId, text, List.mem_cons_self .., hdoc⟩,
          by simpa [hdocId] using hdocScope⟩
      · obtain ⟨⟨k, hkGe, hkId, txt, htxtMem, htxtParse⟩, hsc⟩ := hspecTail e heTail
        exact ⟨⟨k, by omega, hkId, txt, List.mem_cons_of_mem _ htxtMem, htxtParse⟩, hsc⟩

def docMatchesIRI (key? : Option IRI) (doc : SourceDocument) (target : IRI) : Bool :=
  key? == some target || doc.versionIRI == some target || doc.ontologyIRI == some target

def extractFirstBy (pred : LibraryEntry → Bool) :
    List LibraryEntry → Option (LibraryEntry × List LibraryEntry)
  | [] => none
  | e :: rest =>
    if pred e then some (e, rest)
    else (extractFirstBy pred rest).map fun (hit, rem') => (hit, e :: rem')

private theorem extractFirstBy_spec {pred : LibraryEntry → Bool} {rem rem' : List LibraryEntry}
    {hit : LibraryEntry} (h : extractFirstBy pred rem = some (hit, rem')) :
    pred hit = true ∧
    hit ∈ rem ∧
    (∀ e ∈ rem', e ∈ rem) ∧
    rem'.length < rem.length ∧
    ((rem.map (fun e => e.doc.docId)).Nodup →
      (hit.doc.docId :: rem'.map (fun e => e.doc.docId)).Nodup) := by
  induction rem generalizing rem' with
  | nil => simp [extractFirstBy] at h
  | cons e rest ih =>
    unfold extractFirstBy at h
    split at h
    · rename_i hpred
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hpred, List.mem_cons_self .., fun x hx => List.mem_cons_of_mem _ hx,
        Nat.lt_succ_self _, id⟩
    · simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨⟨hit', rem1⟩, hrec, hpair⟩
      cases hpair
      obtain ⟨hpred, hmem, hsub, hlt, hnd⟩ := ih hrec
      refine ⟨hpred, List.mem_cons_of_mem _ hmem, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx1
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub x hx1)
      · simp only [List.length_cons]; omega
      · intro hndCons
        rw [List.map_cons, List.nodup_cons] at hndCons
        have hnd1 := hnd hndCons.2
        rw [List.nodup_cons] at hnd1
        rw [List.map_cons, List.nodup_cons, List.nodup_cons]
        refine ⟨?_, ?_, hnd1.2⟩
        · intro hIn
          rcases List.mem_cons.mp hIn with heq | hInRem1
          · exact hndCons.1 (heq ▸ List.mem_map_of_mem hmem)
          · exact hnd1.1 hInRem1
        · intro hInRem1
          obtain ⟨x, hxMem, hxEq⟩ := List.mem_map.mp hInRem1
          exact hndCons.1 (List.mem_map.mpr ⟨x, hsub x hxMem, hxEq⟩)

/-- Match an import target IRI against remaining library entries with W3C/SABRINA
priority: library key IRI, then declared `versionIRI`, then declared `ontologyIRI`. -/
def extractMatchingEntry (target : IRI) (rem : List LibraryEntry) :
    Option (LibraryEntry × List LibraryEntry) :=
  match extractFirstBy (fun e => e.key == target) rem with
  | some res => some res
  | none =>
    match extractFirstBy (fun e => e.doc.versionIRI == some target) rem with
    | some res => some res
    | none => extractFirstBy (fun e => e.doc.ontologyIRI == some target) rem

private theorem extractMatchingEntry_spec {target : IRI} {rem rem' : List LibraryEntry}
    {hit : LibraryEntry} (h : extractMatchingEntry target rem = some (hit, rem')) :
    docMatchesIRI (some hit.key) hit.doc target = true ∧
    hit ∈ rem ∧
    (∀ e ∈ rem', e ∈ rem) ∧
    rem'.length < rem.length ∧
    ((rem.map (fun e => e.doc.docId)).Nodup →
      (hit.doc.docId :: rem'.map (fun e => e.doc.docId)).Nodup) := by
  unfold extractMatchingEntry at h
  cases h1 : extractFirstBy (fun e => e.key == target) rem with
  | some res =>
    rw [h1] at h; cases h
    obtain ⟨hp, hm, hs, hl, hn⟩ := extractFirstBy_spec h1
    exact ⟨by simp [docMatchesIRI, hp], hm, hs, hl, hn⟩
  | none =>
    rw [h1] at h
    cases h2 : extractFirstBy (fun e => e.doc.versionIRI == some target) rem with
    | some res =>
      rw [h2] at h; cases h
      obtain ⟨hp, hm, hs, hl, hn⟩ := extractFirstBy_spec h2
      exact ⟨by simp [docMatchesIRI, hp], hm, hs, hl, hn⟩
    | none =>
      rw [h2] at h
      obtain ⟨hp, hm, hs, hl, hn⟩ := extractFirstBy_spec h
      exact ⟨by simp [docMatchesIRI, hp], hm, hs, hl, hn⟩

/-- Total, fuel-free transitive `owl:imports` closure loop terminating on the
lexicographic measure `(rem.length, queue.length)`. -/
def resolveLoop (queue : List IRI) (loaded : List (Option IRI × SourceDocument))
    (rem : List LibraryEntry) : Option (List (Option IRI × SourceDocument)) :=
  match queue with
  | [] => some loaded
  | imp :: rest =>
    if loaded.any (fun p => docMatchesIRI p.1 p.2 imp) then
      resolveLoop rest loaded rem
    else
      match h : extractMatchingEntry imp rem with
      | none => none
      | some (entry, rem') =>
        have _ : rem'.length < rem.length := (extractMatchingEntry_spec h).2.2.2.1
        resolveLoop (rest ++ entry.doc.imports) (loaded ++ [(some entry.key, entry.doc)]) rem'
termination_by (rem.length, queue.length)

private theorem nodup_move_mid {α : Type} {xs ys : List α} {a : α}
    (h1 : (xs ++ a :: ys).Nodup) : ((xs ++ [a]) ++ ys).Nodup := by
  simpa [List.append_assoc] using h1

private theorem resolveLoop_inv
    (queue : List IRI) (loaded : List (Option IRI × SourceDocument)) (rem : List LibraryEntry)
    (loadedFinal : List (Option IRI × SourceDocument))
    (hres : resolveLoop queue loaded rem = some loadedFinal)
    (hnd : (loaded.map (·.2.docId) ++ rem.map (·.doc.docId)).Nodup)
    (hscopeL : ∀ p ∈ loaded, docInScope p.2.docId p.2.ontology = true)
    (hscopeR : ∀ e ∈ rem, docInScope e.doc.docId e.doc.ontology = true)
    (hclosed : ∀ p ∈ loaded, ∀ imp ∈ p.2.imports,
      imp ∈ queue ∨ ∃ q ∈ loaded, docMatchesIRI q.1 q.2 imp = true) :
    (loadedFinal.map (·.2.docId)).Nodup ∧
    (∀ p ∈ loaded, p ∈ loadedFinal) ∧
    (∀ p ∈ loadedFinal, p ∈ loaded ∨ ∃ e ∈ rem, p = (some e.key, e.doc)) ∧
    (∀ p ∈ loadedFinal, docInScope p.2.docId p.2.ontology = true) ∧
    (∀ p ∈ loadedFinal, ∀ imp ∈ p.2.imports, ∃ q ∈ loadedFinal, docMatchesIRI q.1 q.2 imp = true) := by
  cases queue with
  | nil =>
    rw [resolveLoop] at hres
    cases hres
    refine ⟨(List.nodup_append.mp hnd).1, fun _ h => h, fun _ h => Or.inl h, hscopeL, ?_⟩
    intro p hp imp himp
    rcases hclosed p hp imp himp with hnil | hhit
    · cases hnil
    · exact hhit
  | cons imp rest =>
    rw [resolveLoop] at hres
    split at hres
    · rename_i hany
      obtain ⟨qHit, hqHitMem, hqHitMatch⟩ := List.any_eq_true.mp hany
      have hclosed' : ∀ p ∈ loaded, ∀ tgt ∈ p.2.imports,
          tgt ∈ rest ∨ ∃ q ∈ loaded, docMatchesIRI q.1 q.2 tgt = true := by
        intro p hp tgt htgt
        rcases hclosed p hp tgt htgt with hInQ | hHit
        · rcases List.mem_cons.mp hInQ with rfl | hInRest
          · exact Or.inr ⟨qHit, hqHitMem, hqHitMatch⟩
          · exact Or.inl hInRest
        · exact Or.inr hHit
      exact resolveLoop_inv rest loaded rem loadedFinal hres hnd hscopeL hscopeR hclosed'
    · split at hres
      · cases hres
      · rename_i entry rem' hextr
        obtain ⟨hmatch, hmem, hsub, hlt, hndMove⟩ := extractMatchingEntry_spec hextr
        have hndSplit := List.nodup_append.mp hnd
        have hndEntryRem' := hndMove hndSplit.2.1
        have hnd' : ((loaded ++ [(some entry.key, entry.doc)]).map (·.2.docId) ++
            rem'.map (·.doc.docId)).Nodup := by
          rw [List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]
          rw [List.nodup_append]
          refine ⟨hndSplit.1, hndEntryRem', ?_⟩
          intro a ha b hb
          rcases List.mem_cons.mp hb with rfl | hbRem'
          · exact hndSplit.2.2 a ha entry.doc.docId (List.mem_map_of_mem hmem)
          · obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hbRem'
            exact hndSplit.2.2 a ha x.doc.docId (List.mem_map_of_mem (hsub x hxMem))
        have hscopeL' : ∀ p ∈ loaded ++ [(some entry.key, entry.doc)],
            docInScope p.2.docId p.2.ontology = true := by
          intro p hp
          rcases List.mem_append.mp hp with hpL | hpE
          · exact hscopeL p hpL
          · simp only [List.mem_singleton] at hpE; subst hpE; exact hscopeR entry hmem
        have hscopeR' : ∀ e ∈ rem', docInScope e.doc.docId e.doc.ontology = true :=
          fun e he => hscopeR e (hsub e he)
        have hclosed' : ∀ p ∈ loaded ++ [(some entry.key, entry.doc)], ∀ tgt ∈ p.2.imports,
            tgt ∈ rest ++ entry.doc.imports ∨
              ∃ q ∈ loaded ++ [(some entry.key, entry.doc)], docMatchesIRI q.1 q.2 tgt = true := by
          intro p hp tgt htgt
          rcases List.mem_append.mp hp with hpL | hpE
          · rcases hclosed p hpL tgt htgt with hInQ | ⟨q, hqL, hqM⟩
            · rcases List.mem_cons.mp hInQ with rfl | hInRest
              · exact Or.inr ⟨(some entry.key, entry.doc), by simp, hmatch⟩
              · exact Or.inl (List.mem_append_left _ hInRest)
            · exact Or.inr ⟨q, List.mem_append_left _ hqL, hqM⟩
          · simp only [List.mem_singleton] at hpE; subst hpE
            exact Or.inl (List.mem_append_right _ htgt)
        obtain ⟨hndF, hpreF, hsrcF, hscF, hclF⟩ :=
          resolveLoop_inv (rest ++ entry.doc.imports) (loaded ++ [(some entry.key, entry.doc)])
            rem' loadedFinal hres hnd' hscopeL' hscopeR' hclosed'
        refine ⟨hndF, fun p hp => hpreF p (List.mem_append_left _ hp), ?_, hscF, hclF⟩
        intro p hpF
        rcases hsrcF p hpF with hpL' | ⟨e, heRem', heq⟩
        · rcases List.mem_append.mp hpL' with hpL | hpE
          · exact Or.inl hpL
          · simp only [List.mem_singleton] at hpE; exact Or.inr ⟨entry, hmem, hpE⟩
        · exact Or.inr ⟨e, hsub e heRem', heq⟩
termination_by (rem.length, queue.length)

structure ResolvedImportClosure where
  root : SourceDocument
  entries : List (Option IRI × SourceDocument)
  deriving Repr

def ResolvedImportClosure.docs (c : ResolvedImportClosure) : List SourceDocument :=
  c.entries.map Prod.snd

def ResolvedImportClosure.flattened (c : ResolvedImportClosure) : Ontology :=
  flattenDocs (c.docs.map (·.ontology))

/-- Total verified `owl:imports` closure resolver from raw `.ofn` source text
and a library of `(keyIRI, ofnText)` source documents. -/
def resolveSourceImports (rootOFN : String) (library : List (IRI × String)) :
    Option ResolvedImportClosure :=
  (parseSourceDocument (mkDocId 0) rootOFN).bind fun rootDoc =>
    (parseLibrary 1 library).bind fun parsedLib =>
      (resolveLoop rootDoc.imports [(none, rootDoc)] parsedLib).map fun loaded =>
        ⟨rootDoc, loaded⟩

theorem resolveSourceImports_spec
    {rootOFN : String} {library : List (IRI × String)} {closure : ResolvedImportClosure}
    (h : resolveSourceImports rootOFN library = some closure) :
    parseSourceDocument (mkDocId 0) rootOFN = some closure.root ∧
    (none, closure.root) ∈ closure.entries ∧
    closure.root ∈ closure.docs ∧
    (closure.docs.map (·.docId)).Nodup ∧
    (∀ d ∈ closure.docs, docInScope d.docId d.ontology = true) ∧
    (∀ p ∈ closure.entries,
      p = (none, closure.root) ∨
      ∃ k ≥ 1, ∃ key txt, (key, txt) ∈ library ∧
        parseSourceDocument (mkDocId k) txt = some p.2 ∧ p.1 = some key) ∧
    (∀ p ∈ closure.entries, ∀ imp ∈ p.2.imports,
      ∃ q ∈ closure.entries, docMatchesIRI q.1 q.2 imp = true) := by
  simp only [resolveSourceImports, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  rcases h with ⟨rootDoc, hroot, parsedLib, hlib, loaded, hloop, rfl⟩
  obtain ⟨hrootId, hrootScope⟩ := parseSourceDocument_inScope hroot
  obtain ⟨hndLib, hspecLib⟩ := parseLibrary_spec 1 library parsedLib hlib
  have hndInit : (([(none, rootDoc)] : List (Option IRI × SourceDocument)).map (·.2.docId) ++ parsedLib.map (·.doc.docId)).Nodup := by
    simp only [List.map_singleton, List.singleton_append, List.nodup_cons]
    refine ⟨?_, hndLib⟩
    intro hmem
    obtain ⟨e, heMem, heEq⟩ := List.mem_map.mp hmem
    obtain ⟨⟨k, hkGe, hkId, _⟩, _⟩ := hspecLib e heMem
    have : k = 0 := mkDocId_injective (hkId.symm.trans (heEq.trans hrootId))
    omega
  have hscInitL : ∀ p ∈ ([(none, rootDoc)] : List (Option IRI × SourceDocument)),
      docInScope p.2.docId p.2.ontology = true := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp
    simpa [hrootId] using hrootScope
  have hscInitR : ∀ e ∈ parsedLib, docInScope e.doc.docId e.doc.ontology = true :=
    fun e he => (hspecLib e he).2
  have hclInit : ∀ p ∈ ([(none, rootDoc)] : List (Option IRI × SourceDocument)),
      ∀ imp ∈ p.2.imports, imp ∈ rootDoc.imports ∨
        ∃ q ∈ ([(none, rootDoc)] : List (Option IRI × SourceDocument)),
          docMatchesIRI q.1 q.2 imp = true := by
    intro p hp imp himp; simp only [List.mem_singleton] at hp; subst hp
    exact Or.inl himp
  obtain ⟨hndF, hpreF, hsrcF, hscF, hclF⟩ :=
    resolveLoop_inv rootDoc.imports [(none, rootDoc)] parsedLib loaded hloop
      hndInit hscInitL hscInitR hclInit
  have hrootEntry : (none, rootDoc) ∈ loaded := hpreF (none, rootDoc) (List.mem_cons_self ..)
  have hmapEq : (loaded.map Prod.snd).map (·.docId) = loaded.map (·.2.docId) := by
    simp [List.map_map, Function.comp_def]
  refine ⟨hroot, hrootEntry, List.mem_map.mpr ⟨(none, rootDoc), hrootEntry, rfl⟩,
    by simpa [ResolvedImportClosure.docs, hmapEq] using hndF, ?_, ?_, hclF⟩
  · intro d hd
    obtain ⟨p, hpMem, rfl⟩ := List.mem_map.mp hd
    exact hscF p hpMem
  · intro p hp
    rcases hsrcF p hp with hpInit | ⟨e, heLib, rfl⟩
    · simp only [List.mem_singleton] at hpInit; exact Or.inl hpInit
    · obtain ⟨⟨k, hkGe, _, txt, htxtMem, htxtParse⟩, _⟩ := hspecLib e heLib
      exact Or.inr ⟨k, hkGe, e.key, txt, htxtMem, htxtParse, rfl⟩

/-- A path of import requests from the root through the supplied catalog.
Each edge records the IRI used to match the target. -/
inductive ImportReachable (root : SourceDocument) (catalog : List LibraryEntry) :
    (Option IRI × SourceDocument) → Prop where
  | rootEntry : ImportReachable root catalog (none, root)
  | importEntry {source : Option IRI × SourceDocument} {target : LibraryEntry} {iri : IRI} :
      ImportReachable root catalog source → iri ∈ source.2.imports →
      target ∈ catalog → docMatchesIRI (some target.key) target.doc iri = true →
      ImportReachable root catalog (some target.key, target.doc)

private theorem resolveLoop_reachable (root : SourceDocument) (catalog : List LibraryEntry)
    (queue : List IRI) (loaded : List (Option IRI × SourceDocument))
    (rem : List LibraryEntry) (result : List (Option IRI × SourceDocument))
    (hres : resolveLoop queue loaded rem = some result)
    (hloaded : ∀ entry ∈ loaded, ImportReachable root catalog entry)
    (hrem : ∀ e ∈ rem, e ∈ catalog)
    (hqueue : ∀ iri ∈ queue, ∃ entry ∈ loaded, iri ∈ entry.2.imports) :
    ∀ entry ∈ result, ImportReachable root catalog entry := by
  cases queue with
  | nil =>
    rw [resolveLoop] at hres
    cases hres
    exact hloaded
  | cons iri rest =>
    rw [resolveLoop] at hres
    split at hres
    · exact resolveLoop_reachable root catalog rest loaded rem result hres hloaded hrem
        (fun target htarget => hqueue target (List.mem_cons_of_mem _ htarget))
    · split at hres
      · cases hres
      · rename_i selected rem' hselected
        obtain ⟨hmatch, hmem, hsub, _, _⟩ := extractMatchingEntry_spec hselected
        let entry : Option IRI × SourceDocument := (some selected.key, selected.doc)
        obtain ⟨source, hsource, himport⟩ := hqueue iri (List.mem_cons_self ..)
        have hreach : ImportReachable root catalog entry :=
          .importEntry (hloaded source hsource) himport (hrem selected hmem) hmatch
        have hloaded' : ∀ e ∈ loaded ++ [entry], ImportReachable root catalog e := by
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact hloaded e he
          · obtain rfl := List.mem_singleton.mp he
            exact hreach
        have hqueue' : ∀ target ∈ rest ++ selected.doc.imports,
            ∃ e ∈ loaded ++ [entry], target ∈ e.2.imports := by
          intro target htarget
          rcases List.mem_append.mp htarget with ht | ht
          · obtain ⟨e, he, himp⟩ := hqueue target (List.mem_cons_of_mem _ ht)
            exact ⟨e, List.mem_append_left _ he, himp⟩
          · exact ⟨entry, List.mem_append_right _ (List.mem_singleton_self _), ht⟩
        exact resolveLoop_reachable root catalog (rest ++ selected.doc.imports) (loaded ++ [entry])
          rem' result hres hloaded' (fun e he => hrem e (hsub e he)) hqueue'
termination_by (rem.length, queue.length)

/-- Successful resolution adds only documents reachable through the parsed catalog. -/
theorem resolveSourceImports_reachable
    {rootOFN : String} {library : List (IRI × String)} {closure : ResolvedImportClosure}
    (h : resolveSourceImports rootOFN library = some closure) :
    ∃ catalog, parseLibrary 1 library = some catalog ∧
      ∀ entry ∈ closure.entries, ImportReachable closure.root catalog entry := by
  simp only [resolveSourceImports, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  rcases h with ⟨root, _, catalog, hcatalog, entries, hloop, rfl⟩
  refine ⟨catalog, hcatalog, ?_⟩
  apply resolveLoop_reachable root catalog root.imports [(none, root)] catalog entries hloop
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    exact .rootEntry
  · exact fun _ he => he
  · intro iri hiri
    exact ⟨(none, root), List.mem_singleton_self _, hiri⟩

/-- Semantic correspondence from raw `.ofn` source text and resolved `owl:imports`
closure to the flattened typed `Ontology`, preserving W3C OWL 2 §5.6.2
document-scoped anonymous individuals via `WellFormed.scopedImports_models_iff`. -/
theorem resolveSourceImports_models_iff
    {rootOFN : String} {library : List (IRI × String)} {closure : ResolvedImportClosure}
    (h : resolveSourceImports rootOFN library = some closure)
    (i : Interpretation dm) :
    models i closure.flattened ↔ ∀ d ∈ closure.docs, models i d.ontology := by
  obtain ⟨_, _, _, hnd, hscope, _, _⟩ := resolveSourceImports_spec h
  let documents : List (String × Ontology) := closure.docs.map fun d => (d.docId, d.ontology)
  have hfst : documents.map Prod.fst = closure.docs.map (·.docId) := by
    simp [documents, List.map_map, Function.comp_def]
  have hsnd : documents.map Prod.snd = closure.docs.map (·.ontology) := by
    simp [documents, List.map_map, Function.comp_def]
  have hsc : ∀ p ∈ documents, docInScope p.1 p.2 = true := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact hscope d hd
  have hmain := scopedImports_models_iff i documents (hfst ▸ hnd) hsc
  rw [hsnd] at hmain
  rw [ResolvedImportClosure.flattened, hmain]
  constructor
  · intro hall d hd
    exact hall (d.docId, d.ontology) (List.mem_map.mpr ⟨d, hd, rfl⟩)
  · intro hall p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact hall d hd

theorem resolveSourceImports_sat_iff
    {rootOFN : String} {library : List (IRI × String)} {closure : ResolvedImportClosure}
    (h : resolveSourceImports rootOFN library = some closure) :
    Satisfiable dm closure.flattened ↔
      ∃ i : Interpretation dm, ∀ d ∈ closure.docs, models i d.ontology := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (resolveSourceImports_models_iff h i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (resolveSourceImports_models_iff h i).mpr hi⟩

/-! ### 6. End-to-End Source + Import-Closure Conformance Decision Adapters -/

private def decideParsedClosure? (decideOntology : Ontology → Option Bool) (rootOFN : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Bool) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    if ontologyXMLLiteralsValid true closure.flattened then
      (decideOntology closure.flattened).map fun b => (closure, b)
    else none

private theorem decideParsedClosure_iff
    {decideOntology : Ontology → Option Bool}
    (correct : ∀ {o b}, decideOntology o = some b → (b = true ↔ Satisfiable datatypeMap o))
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideParsedClosure? decideOntology rootOFN library = some (closure, b)) :
    resolveSourceImports rootOFN library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology) := by
  simp only [decideParsedClosure?, Option.bind_eq_some_iff] at h
  rcases h with ⟨cl, hcl, hrest⟩
  split at hrest
  · rename_i hxml
    simp only [Option.map_eq_some_iff] at hrest
    rcases hrest with ⟨b', hb', hpair⟩
    cases hpair
    exact ⟨hcl, hxml, (correct hb').trans (resolveSourceImports_sat_iff hcl)⟩
  · cases hrest

/-- Resolve the source import closure and decide it using the wider typed adapter,
which includes the universal object fragment. -/
def decideSourceClosure? (rootOFN : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Bool) :=
  decideParsedClosure? decideWithWiderDataRanges? rootOFN library

def decideObjectSourceClosure? := decideParsedClosure? ObjectRoleBounds.decideObjectHierarchy?

theorem decideObjectSourceClosure_iff {root library closure b}
    (h : decideObjectSourceClosure? root library = some (closure, b)) :
    resolveSourceImports root library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology) :=
  decideParsedClosure_iff ObjectRoleBounds.decideObjectHierarchy_iff h

/-- The universal decision alone, for callers with an existing ranked path. -/
def decideUniversalSourceClosure? (rootOFN : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Bool) :=
  decideParsedClosure? OWLUniversal.decideUniversalOntology? rootOFN library

theorem decideSourceClosure_iff
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideSourceClosure? rootOFN library = some (closure, b)) :
    resolveSourceImports rootOFN library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology) :=
  decideParsedClosure_iff decideWithWiderDataRanges_iff h

theorem decideUniversalSourceClosure_iff
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideUniversalSourceClosure? rootOFN library = some (closure, b)) :
    resolveSourceImports rootOFN library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology) :=
  decideParsedClosure_iff OWLUniversal.decideUniversalOntology_iff h

/-- Parse a standalone subclass query with the root document's prefixes.
The query may declare additional prefixes. -/
def parseSourceSubclass (prefixes : PrefixMap) (input : String) : Option (ClassExpr × ClassExpr) := do
  let tokens ← tokenizeTotal input
  let (prefixes, rest) ← parsePrefixDeclsTotal (tokens.length + 1) prefixes tokens
  match parseAxiomTotal "query" prefixes (rest.length + 1) rest with
  | some (some (.subClassOf a b), []) => some (a, b)
  | _ => none

/-- Decide a supported subclass query against the full resolved import closure. -/
private def decideSourceSubclassUsing? (solve : Ontology → ClassExpr → ClassExpr → Option Sabrina.ALC.InclusionVerdict)
    (rootOFN query : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × (ClassExpr × ClassExpr) × Sabrina.ALC.InclusionVerdict) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    if ontologyXMLLiteralsValid true closure.flattened then
      (parseSourceSubclass closure.root.prefixes query).bind fun (a, b) =>
        (solve closure.flattened a b).map fun v =>
          (closure, (a, b), v)
    else none

private theorem decideSourceSubclassUsing_sound
    {solve : Ontology → ClassExpr → ClassExpr → Option Sabrina.ALC.InclusionVerdict}
    (correct : ∀ {o a b v}, solve o a b = some v → Normalize.queryVerdictClaim o (.subClassOf a b) v)
    {rootOFN query : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {a b : ClassExpr} {v : Sabrina.ALC.InclusionVerdict}
    (h : decideSourceSubclassUsing? solve rootOFN query library = some (closure, (a, b), v)) :
    resolveSourceImports rootOFN library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    parseSourceSubclass closure.root.prefixes query = some (a, b) ∧
    Normalize.queryVerdictClaim closure.flattened (.subClassOf a b) v := by
  simp only [decideSourceSubclassUsing?, Option.bind_eq_some_iff] at h
  obtain ⟨cl, hcl, h⟩ := h
  split at h
  · rename_i hxml
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, e⟩, hparse, verdict, hdec, hpair⟩ := h
    cases hpair
    exact ⟨hcl, hxml, hparse, correct hdec⟩
  · contradiction

def decideUniversalSourceSubclass? := decideSourceSubclassUsing? OWLUniversal.decideUniversalSubclass?

theorem decideUniversalSourceSubclass_sound {root query library closure a b v}
    (h : decideUniversalSourceSubclass? root query library = some (closure, (a, b), v)) :
    resolveSourceImports root library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    parseSourceSubclass closure.root.prefixes query = some (a, b) ∧
    Normalize.queryVerdictClaim closure.flattened (.subClassOf a b) v :=
  decideSourceSubclassUsing_sound OWLUniversal.decideUniversalSubclass_sound h

def decideObjectSourceSubclass? := decideSourceSubclassUsing? OWLUniversal.decideObjectSubclass?

theorem decideObjectSourceSubclass_sound {root query library closure a b v}
    (h : decideObjectSourceSubclass? root query library = some (closure, (a, b), v)) :
    resolveSourceImports root library = some closure ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    parseSourceSubclass closure.root.prefixes query = some (a, b) ∧
    Normalize.queryVerdictClaim closure.flattened (.subClassOf a b) v :=
  decideSourceSubclassUsing_sound OWLUniversal.decideObjectSubclass_sound h

theorem decideSourceClosure_unsat_iff
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideSourceClosure? rootOFN library = some (closure, b)) :
    b = false ↔ ¬ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology := by
  rw [← (decideSourceClosure_iff h).2.2]
  cases b <;> simp

/-- Stricter end-to-end conformance adapter additionally gating on
`WellFormed.checkWellFormedOntology` (reserved vocabulary, arities, literal/facet
validity, simple-role restriction, and regular role hierarchy). -/
def decideWellFormedSourceClosure? (rootOFN : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Bool) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    if checkWellFormedOntology closure.flattened && ontologyXMLLiteralsValid true closure.flattened then
      (decideWithWiderDataRanges? closure.flattened).map fun b => (closure, b)
    else none

theorem decideWellFormedSourceClosure_iff
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideWellFormedSourceClosure? rootOFN library = some (closure, b)) :
    resolveSourceImports rootOFN library = some closure ∧
    WellFormedOntology closure.flattened ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation datatypeMap, ∀ d ∈ closure.docs, models i d.ontology) := by
  simp only [decideWellFormedSourceClosure?, Option.bind_eq_some_iff] at h
  rcases h with ⟨cl, hcl, hrest⟩
  split at hrest
  · rename_i hgate
    obtain ⟨hwf, hxml⟩ := Bool.and_eq_true_iff.mp hgate
    simp only [Option.map_eq_some_iff] at hrest
    rcases hrest with ⟨b', hb', hpair⟩
    cases hpair
    exact ⟨hcl, (checkWellFormedOntology_iff _).mp hwf, hxml,
      (decideWithWiderDataRanges_iff hb').trans (resolveSourceImports_sat_iff hcl)⟩
  · cases hrest

/-- Resolve, check, and decide a source import closure in the admitted real fragment. -/
def decideRealSourceClosure? (rootOFN : String) (library : List (IRI × String)) :
    Option (ResolvedImportClosure × Bool) :=
  (resolveSourceImports rootOFN library).bind fun closure =>
    if checkWellFormedOntology closure.flattened && ontologyXMLLiteralsValid true closure.flattened then
      (decideRealOntology? closure.flattened).map fun b => (closure, b)
    else none

theorem decideRealSourceClosure_iff
    {rootOFN : String} {library : List (IRI × String)}
    {closure : ResolvedImportClosure} {b : Bool}
    (h : decideRealSourceClosure? rootOFN library = some (closure, b)) :
    resolveSourceImports rootOFN library = some closure ∧
    WellFormedOntology closure.flattened ∧
    ontologyXMLLiteralsValid true closure.flattened = true ∧
    (b = true ↔ ∃ i : Interpretation Datatypes.realDatatypeMap,
      ∀ d ∈ closure.docs, models i d.ontology) := by
  simp only [decideRealSourceClosure?, Option.bind_eq_some_iff] at h
  obtain ⟨cl, hcl, hanswer⟩ := h
  split at hanswer
  · rename_i hgate
    obtain ⟨hwf, hxml⟩ := Bool.and_eq_true_iff.mp hgate
    obtain ⟨b', hb', hpair⟩ := Option.map_eq_some_iff.mp hanswer
    cases hpair
    exact ⟨hcl, (checkWellFormedOntology_iff _).mp hwf, hxml,
      (decideRealOntology_iff hb').trans (resolveSourceImports_sat_iff hcl)⟩
  · contradiction

/-! ### 7. End-to-End Live `#guard` Regressions -/

private def exPrefix : String :=
  "Prefix(:=<http://example.org/>)\n" ++
  "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n" ++
  "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n" ++
  "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n"

-- 1. Single-document wider decimal range + annotation/declaration skipping
private def docDecimalSat : String :=
  exPrefix ++
  "Ontology(<http://example.org/dec>\n" ++
  "  Declaration(Class(:Sensor))\n" ++
  "  AnnotationAssertion(<http://example.org/label> :Sensor \"Sensor\"@en)\n" ++
  "  SubClassOf(Annotation(<http://example.org/note> \"ok\") :Sensor\n" ++
  "    DataSomeValuesFrom(:temp DatatypeRestriction(xsd:decimal xsd:minExclusive \"0.0\"^^xsd:decimal xsd:maxExclusive \"1.0\"^^xsd:decimal)))\n" ++
  "  ClassAssertion(:Sensor :s1)\n" ++
  ")\n"

#guard (decideSourceClosure? docDecimalSat []).map Prod.snd == some true
#guard (decideWellFormedSourceClosure? docDecimalSat []).map Prod.snd == some true

-- 2. Same-document anonymous individual _:x collides (UNSAT)
private def docSameBnodeUnsat : String :=
  exPrefix ++
  "Ontology(<http://example.org/sameBnode>\n" ++
  "  ClassAssertion(:A _:x)\n" ++
  "  ClassAssertion(ObjectComplementOf(:A) _:x)\n" ++
  ")\n"

#guard (decideSourceClosure? docSameBnodeUnsat []).map Prod.snd == some false

-- A bare string is the OWL 2 shorthand for rdf:PlainLiteral with no language tag.
#guard (parseSourceDocument "doc:0"
    r#"Ontology(DataPropertyAssertion(<http://example.org/p> <http://example.org/a> "abc"))"#).map
    (·.ontology) ==
  some [.dataAssertion "http://example.org/p" (.named "http://example.org/a") ⟨"abc@", rdf "PlainLiteral"⟩]

-- 3. Cross-document anonymous individual _:x does NOT collide (SAT per W3C OWL 2 §5.6.2!)
private def docBnodeRoot : String :=
  exPrefix ++
  "Ontology(<http://example.org/rootBnode>\n" ++
  "  Import(<http://example.org/importedBnode>)\n" ++
  "  ClassAssertion(:A _:x)\n" ++
  ")\n"

private def docBnodeImp : String :=
  exPrefix ++
  "Ontology(<http://example.org/importedBnode>\n" ++
  "  ClassAssertion(ObjectComplementOf(:A) _:x)\n" ++
  ")\n"

#guard (decideSourceClosure? docBnodeRoot [("http://example.org/importedBnode", docBnodeImp)]).map Prod.snd == some true

-- 4. Diamond + cyclic imports matched by versionIRI and ontologyIRI
private def docCycleRoot : String :=
  exPrefix ++
  "Ontology(<http://example.org/cycRoot> <http://example.org/cycRoot/v1>\n" ++
  "  Import(<http://example.org/modA/v2>)\n" ++
  "  Import(<http://example.org/modB>)\n" ++
  "  ClassAssertion(:Root :a)\n" ++
  ")\n"

private def docModA : String :=
  exPrefix ++
  "Ontology(<http://example.org/modA> <http://example.org/modA/v2>\n" ++
  "  Import(<http://example.org/shared>)\n" ++
  "  Import(<http://example.org/cycRoot/v1>)\n" ++
  "  SubClassOf(:Root DataSomeValuesFrom(:score DatatypeRestriction(xsd:decimal xsd:minInclusive \"1.5\"^^xsd:decimal)))\n" ++
  ")\n"

private def docModB : String :=
  exPrefix ++
  "Ontology(<http://example.org/modB>\n" ++
  "  Import(<http://example.org/shared>)\n" ++
  "  SubClassOf(:Root DataAllValuesFrom(:score DatatypeRestriction(xsd:decimal xsd:maxExclusive \"1.5\"^^xsd:decimal)))\n" ++
  ")\n"

private def docShared : String :=
  exPrefix ++
  "Ontology(<http://example.org/shared>\n" ++
  "  FunctionalDataProperty(:score)\n" ++
  ")\n"

private def cycleLib : List (IRI × String) := [
  ("http://example.org/keyA", docModA),
  ("http://example.org/keyB", docModB),
  ("http://example.org/keyShared", docShared)
]

-- Conflict across cyclic diamond imports (score ≥ 1.5 ∧ score < 1.5) -> UNSAT
#guard (decideSourceClosure? docCycleRoot cycleLib).map Prod.snd == some false
-- Closure contains all 4 unique documents
#guard (resolveSourceImports docCycleRoot cycleLib).map (fun c => c.docs.length) == some 4

-- 5. Missing import rejected with none
#guard (decideSourceClosure? docCycleRoot [("http://example.org/keyA", docModA)]).isNone == true

-- 6. Cross-import HasKey + decimal interval + owl:topObjectProperty + canonical rdf:XMLLiteral
private def docFullRoot : String :=
  exPrefix ++
  "Ontology(<http://example.org/fullRoot>\n" ++
  "  Import(<http://example.org/fullBase>)\n" ++
  "  ClassAssertion(:Item :i1)\n" ++
  "  ClassAssertion(:Item :i2)\n" ++
  "  DifferentIndividuals(:i1 :i2)\n" ++
  "  DataPropertyAssertion(:code :i1 \"0.5\"^^xsd:decimal)\n" ++
  "  DataPropertyAssertion(:code :i2 \"0.50\"^^xsd:decimal)\n" ++
  "  DataPropertyAssertion(:xml :i1 \"<doc a=\\\"1\\\" b=\\\"2\\\"></doc>\"^^rdf:XMLLiteral)\n" ++
  ")\n"

private def docFullBase : String :=
  exPrefix ++
  "Ontology(<http://example.org/fullBase>\n" ++
  "  HasKey(:Item (owl:topObjectProperty) (:code))\n" ++
  ")\n"

-- "0.5" and "0.50" denote the same decimal + HasKey(Item, (topObjectProperty), (code)) forces i1 = i2 -> UNSAT
#guard (decideSourceClosure? docFullRoot [("http://example.org/fullBase", docFullBase)]).map Prod.snd == some false

-- 7. The stricter XML gate rejects non-canonical <doc/> in imported document
private def docBadXMLImp : String :=
  exPrefix ++
  "Ontology(<http://example.org/badXML>\n" ++
  "  DataPropertyAssertion(:xml :i1 \"<doc/>\"^^rdf:XMLLiteral)\n" ++
  ")\n"

private def docBadXMLRoot : String :=
  exPrefix ++
  "Ontology(<http://example.org/badXMLRoot>\n" ++
  "  Import(<http://example.org/badXML>)\n" ++
  ")\n"

#guard (decideSourceClosure? docBadXMLRoot [("http://example.org/badXML", docBadXMLImp)]).isNone == true

-- 8. Canonical OFN serializer round-trip check on an ontology with multiple constructors
private def sampleOnt : Ontology := [
  .subClassOf (.named "http://example.org/A")
    (.objectSome (.inverse "http://example.org/r")
      (.dataMin 2 "http://example.org/d"
        (.restriction (xsd "decimal") [⟨xsd "minExclusive", ⟨"0.5", xsd "decimal"⟩⟩]))),
  .hasKey (.named "http://example.org/A") [.named topObjectProperty] ["http://example.org/d"],
  .classAssertion (.named "http://example.org/A") (.anonymous "doc:0" "b1")
]

#guard (parseSourceDocument "doc:0"
  (renderCanonicalOFN sampleOnt (some "http://example.org/o") (some "http://example.org/o/v1")
    ["http://example.org/imp"])).map (fun d => (d.ontologyIRI, d.versionIRI, d.imports, d.ontology)) ==
  some (some "http://example.org/o", some "http://example.org/o/v1", ["http://example.org/imp"], sampleOnt)

-- Both source adapters keep unsupported input separate from contradictory ABoxes.
#guard (decideWellFormedSourceClosure? docSameBnodeUnsat []).map Prod.snd == some false
#guard (decideWellFormedSourceClosure? docBnodeRoot
    [("http://example.org/importedBnode", docBnodeImp)]).map Prod.snd == some true
#guard (decideWellFormedSourceClosure? docBnodeRoot []).isNone
#guard (decideWellFormedSourceClosure? docBadXMLRoot [("http://example.org/badXML", docBadXMLImp)]).isNone

private def nonSimpleCardinalityABox : String :=
  exPrefix ++ r#"Ontology(
    TransitiveObjectProperty(:r)
    ClassAssertion(ObjectMaxCardinality(1 :r) :a)
  )"#

#guard (decideSourceClosure? nonSimpleCardinalityABox []).isNone
#guard (decideWellFormedSourceClosure? nonSimpleCardinalityABox []).isNone
#guard (decideSourceClosure? (exPrefix ++ "Ontology(ClassAssertion(:A))") []).isNone

-- The inverse-square chain forces r(a,b) from r(b,a) and r(b,b).
private def converseChainCase (extra : String) : String :=
  exPrefix ++ r#"Ontology(
    SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
    ObjectPropertyAssertion(:r :b :a)
    ObjectPropertyAssertion(:r :b :b)
    DifferentIndividuals(:a :b)
    "# ++ extra ++ ")"

#guard (decideUniversalSourceClosure? (converseChainCase "") []).map Prod.snd == some true
#guard (decideSourceClosure? (converseChainCase "") []).map Prod.snd == some true
#guard (decideSourceClosure?
  (converseChainCase "ClassAssertion(ObjectAllValuesFrom(:r owl:Nothing) :a)") []).map Prod.snd == some false
#guard (decideUniversalSourceClosure?
  (converseChainCase "ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :a)") []).isNone
#guard (decideSourceClosure?
  (converseChainCase "ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :a)") []).map Prod.snd == some true
#guard (decideWellFormedSourceClosure? (converseChainCase "") []).isNone

private def inverseHeadCase : String :=
  exPrefix ++ r#"Ontology(
    SubObjectPropertyOf(ObjectPropertyChain(:r :r) ObjectInverseOf(:r))
    ObjectPropertyAssertion(:r :b :a)
    ObjectPropertyAssertion(:r :b :b)
    NegativeObjectPropertyAssertion(ObjectInverseOf(:r) :b :a)
  )"#

#guard (decideUniversalSourceClosure? inverseHeadCase []).map Prod.snd == some false

private def converseImport : String :=
  exPrefix ++ r#"Ontology(<http://example.org/chains>
    SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
    ClassAssertion(ObjectComplementOf(:C) _:x)
  )"#

private def unrankedScopedRoot (extra : String) : String :=
  exPrefix ++ r#"Ontology(
    Import(<http://example.org/chains>)
    ClassAssertion(:C _:x)
    "# ++ extra ++ ")"

private def converseCatalog : List (IRI × String) :=
  [("http://example.org/chains", converseImport)]

#guard (decideSourceClosure? (unrankedScopedRoot "") converseCatalog).map Prod.snd == some true
#guard (decideSourceClosure?
  (unrankedScopedRoot "ClassAssertion(ObjectComplementOf(:C) _:x)") converseCatalog).map Prod.snd == some false
#guard (decideSourceClosure? (unrankedScopedRoot "") []).isNone

private def subtypeLengthCase (count range : String) : String :=
  exPrefix ++ "Ontology(Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) " ++
    "ClassAssertion(DataMinCardinality(" ++ count ++ " :p " ++ range ++ ") :a))"

private def bothSubtypeLengthSpellings (subtype facets count : String)
    (wrap : String → String) (expected : Bool) : Bool :=
  let direct := "DatatypeRestriction(xsd:" ++ subtype ++ " " ++ facets ++ ")"
  let rewritten := "DataIntersectionOf(xsd:" ++ subtype ++
    " DatatypeRestriction(xsd:string " ++ facets ++ "))"
  [direct, rewritten].all fun range =>
    (decideWellFormedSourceClosure? (subtypeLengthCase count (wrap range)) []).map Prod.snd ==
      some expected

-- All six string subtypes support direct length bounds through the strict source adapter.
#guard ["normalizedString", "token", "language", "NMTOKEN", "Name", "NCName"].all fun subtype =>
  bothSubtypeLengthSpellings subtype
    "xsd:minLength \"1\"^^xsd:integer xsd:maxLength \"2\"^^xsd:integer" "2" id true

-- The only one-character Name outside NCName is ":". It cannot fill two slots.
private def outsideNCName (range : String) : String :=
  "DataIntersectionOf(" ++ range ++ " DataComplementOf(xsd:NCName))"

#guard bothSubtypeLengthSpellings "Name" "xsd:length \"1\"^^xsd:integer" "1" outsideNCName true
#guard bothSubtypeLengthSpellings "Name" "xsd:length \"1\"^^xsd:integer" "2" outsideNCName false

-- A restriction nested inside a complement excludes the one-character candidate.
#guard bothSubtypeLengthSpellings "Name" "xsd:length \"1\"^^xsd:integer" "1" (fun range =>
  "DataIntersectionOf(DataOneOf(\":\"^^xsd:string) DataComplementOf(" ++ range ++ "))") false

private def namePatternRestriction (base pattern : String) (facets : String := "") : String :=
  "DatatypeRestriction(xsd:" ++ base ++ " xsd:pattern \"" ++ pattern ++ "\"^^xsd:string " ++ facets ++ ")"

private def decideStringRange (count range : String) : Option Bool :=
  (decideWellFormedSourceClosure? (subtypeLengthCase count range) []).map Prod.snd

private def namePatternOver (pattern values : String) : String :=
  "DataIntersectionOf(" ++ namePatternRestriction "string" pattern ++ " DataOneOf(" ++ values ++ "))"

-- Latin-1 and supplementary-plane starts count as distinct values.
#guard decideStringRange "2" (namePatternOver r"\\i" r#""é"^^xsd:NCName "𐐀"^^xsd:Name"#) == some true
#guard decideStringRange "3" (namePatternOver r"\\i" r#""é"^^xsd:NCName "𐐀"^^xsd:Name"#) == some false

-- U+00B7 is a continuation character. U+037E is in a gap in the XML tables.
#guard decideStringRange "1" (namePatternOver r"\\i" r#""·"^^xsd:string"#) == some false
#guard decideStringRange "1" (namePatternOver r"\\c" r#""·"^^xsd:string"#) == some true
#guard decideStringRange "1" (namePatternOver r"\\c" r#"";"^^xsd:string"#) == some false
#guard decideStringRange "1" (namePatternOver r"\\c+" r#""·é"^^xsd:string"#) == some true

-- An NCName constraint still excludes colons, and the pattern combines with length.
#guard decideStringRange "1" ("DataIntersectionOf(" ++ namePatternRestriction "NCName" r"\\i\\c*"
    r#"xsd:length "2"^^xsd:integer"# ++ r#" DataOneOf("é·"^^xsd:string))"#) == some true
#guard decideStringRange "1" ("DataIntersectionOf(" ++ namePatternRestriction "NCName" r"\\i\\c*"
    r#"xsd:length "2"^^xsd:integer"# ++ r#" DataOneOf(":é"^^xsd:string))"#) == some false

-- Among single-character ASCII NCNames, only "_" fails xsd:language.
-- The second witness therefore needs the Unicode character sampler.
#guard decideStringRange "2" ("DataIntersectionOf(" ++ namePatternRestriction "NCName" r"\\i" ++
    " DataComplementOf(xsd:language))") == some true
-- General XSD patterns are now admitted by the exact cyclic solver; malformed patterns return none.
#guard decideStringRange "1" (namePatternRestriction "string" "[a-z]+") == some true
#guard decideStringRange "1" (namePatternRestriction "string" "[a-z") == none

private def irrationalRange : String :=
  "DataIntersectionOf(owl:real DataComplementOf(owl:rational))"

private def boundedIrrationalRange (facets : String) : String :=
  "DataIntersectionOf(DatatypeRestriction(owl:real " ++ facets ++
    ") DataComplementOf(owl:rational))"

private def openRealUnit : String :=
  boundedIrrationalRange r#"xsd:minExclusive "0"^^xsd:integer xsd:maxExclusive "1"^^xsd:integer"#

-- Irrational values are usable in Boolean ranges without having literal spellings.
#guard decideStringRange "1" irrationalRange == some true
#guard decideStringRange "3" openRealUnit == some true
#guard decideStringRange "1" (boundedIrrationalRange
  r#"xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "1"^^xsd:integer"#) == some false
#guard decideStringRange "2" ("DataIntersectionOf(" ++ openRealUnit ++
  r#" DataComplementOf(DatatypeRestriction(owl:real xsd:minExclusive "0.5"^^xsd:decimal)))"#) ==
  some true
#guard decideStringRange "1" ("DataIntersectionOf(" ++ irrationalRange ++
  r#" DataOneOf("1/2"^^owl:rational "0.6"^^xsd:decimal))"#) == some false

private def realKeyCase (range : String) : String :=
  exPrefix ++ r#"Ontology(
    Declaration(Class(:A))
    Declaration(NamedIndividual(:a))
    Declaration(NamedIndividual(:b))
    Declaration(NamedIndividual(:owner))
    Declaration(ObjectProperty(:ownedBy))
    Declaration(DataProperty(:p))
    DifferentIndividuals(:a :b)
    ClassAssertion(:A :a)
    ClassAssertion(:A :b)
    ObjectPropertyAssertion(:ownedBy :a :owner)
    ObjectPropertyAssertion(:ownedBy :b :owner)
    HasKey(:A (:ownedBy) (:p))
    SubClassOf(:A DataSomeValuesFrom(:p "# ++ range ++ ")))"

-- Two distinct irrational values satisfy the mixed key. One rational value cannot.
#guard (decideWellFormedSourceClosure? (realKeyCase openRealUnit) []).map Prod.snd == some true
#guard (decideWellFormedSourceClosure? (realKeyCase
  r#"DatatypeRestriction(owl:real xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "1"^^xsd:integer)"#)
  []).map Prod.snd == some false

-- The cut-semantics entry point exercises the verified datatype reduction.
#guard (decideRealSourceClosure? (subtypeLengthCase "3" openRealUnit) []).map Prod.snd == some true
#guard (decideRealSourceClosure? (realKeyCase openRealUnit) []).map Prod.snd == some true
#guard (decideRealSourceClosure? (realKeyCase
  r#"DatatypeRestriction(owl:real xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "1"^^xsd:integer)"#)
  []).map Prod.snd == some false

private def realImport : String :=
  exPrefix ++ "Ontology(<http://example.org/real-ranges> Declaration(Datatype(:Irrational)) " ++
    "DatatypeDefinition(:Irrational " ++ irrationalRange ++ "))"

private def realImportRoot : String :=
  exPrefix ++ r#"Ontology(
    Import(<http://example.org/real-ranges>)
    Declaration(DataProperty(:p))
    Declaration(NamedIndividual(:a))
    ClassAssertion(DataMinCardinality(2 :p :Irrational) :a)
  )"#

#guard (decideRealSourceClosure? realImportRoot
  [("http://example.org/real-ranges", realImport)]).map Prod.snd == some true

private def decideOrderedRange (count range : String) : Option Bool :=
  (decideRealSourceClosure? (subtypeLengthCase count range) []).map Prod.snd

private def adjacentFloatRange : String :=
  r#"DatatypeRestriction(xsd:float xsd:minInclusive "1"^^xsd:float
    xsd:maxInclusive "1.00000011920928955078125"^^xsd:float)"#

private def adjacentDoubleRange : String :=
  r#"DatatypeRestriction(xsd:double xsd:minInclusive "1"^^xsd:double
    xsd:maxInclusive "1.0000000000000002220446049250313080847263336181640625"^^xsd:double)"#

#guard decideOrderedRange "2" adjacentFloatRange == some true
#guard decideOrderedRange "3" adjacentFloatRange == some false
#guard decideOrderedRange "2" adjacentDoubleRange == some true
#guard decideOrderedRange "3" adjacentDoubleRange == some false

private def signedZeroRange : String :=
  r#"DatatypeRestriction(xsd:float xsd:minInclusive "-0.0"^^xsd:float xsd:maxInclusive "0.0"^^xsd:float)"#

#guard decideOrderedRange "2" signedZeroRange == some true
#guard decideOrderedRange "3" signedZeroRange == some false

private def nanRange : String :=
  r#"DataIntersectionOf(xsd:double DataComplementOf(
    DatatypeRestriction(xsd:double xsd:maxInclusive "INF"^^xsd:double)))"#

#guard decideOrderedRange "1" nanRange == some true
#guard decideOrderedRange "2" nanRange == some false

private def localSingletonRange : String :=
  r#"DatatypeRestriction(xsd:dateTime xsd:minInclusive "2000-01-01T12:00:00"^^xsd:dateTime
    xsd:maxInclusive "2000-01-01T12:00:00"^^xsd:dateTime)"#

#guard decideOrderedRange "1" localSingletonRange == some true
#guard decideOrderedRange "2" localSingletonRange == some false

private def dateAtMixedBound (localSeconds : String) : String :=
  r#"DataIntersectionOf(
    DatatypeRestriction(xsd:dateTime xsd:minInclusive "2000-01-01T00:00:00Z"^^xsd:dateTime)
    DataOneOf("2000-01-01T14:00:"# ++ localSeconds ++ r#""^^xsd:dateTime))"#

#guard decideOrderedRange "1" (dateAtMixedBound "00") == some false
#guard decideOrderedRange "1" (dateAtMixedBound "00.0001") == some true

private def tinyLocalInterval : String :=
  r#"DatatypeRestriction(xsd:dateTime xsd:minExclusive "2000-01-01T12:00:00"^^xsd:dateTime
    xsd:maxExclusive "2000-01-01T12:00:00.0001"^^xsd:dateTime)"#

#guard decideOrderedRange "3" tinyLocalInterval == some true

private def sameZonedInstant : String :=
  r#"DatatypeRestriction(xsd:dateTimeStamp
    xsd:minInclusive "2000-01-01T12:00:00Z"^^xsd:dateTimeStamp
    xsd:maxInclusive "2000-01-01T13:00:00+01:00"^^xsd:dateTimeStamp)"#

-- Timezone offsets contribute distinct values even at the same ordered instant.
#guard decideOrderedRange "2" sameZonedInstant == some true

private def finitePatternRange : String :=
  r#"DataIntersectionOf(DataOneOf("ab"^^xsd:string "ac"^^xsd:string "za"^^xsd:string)
    DatatypeRestriction(xsd:string xsd:pattern "a[b-c]"^^xsd:string))"#

#guard decideOrderedRange "2" finitePatternRange == some true
#guard decideOrderedRange "3" finitePatternRange == some false

private def finiteLanguageRange : String :=
  r#"DataIntersectionOf(
    DatatypeRestriction(rdf:PlainLiteral xsd:length "3"^^xsd:integer rdf:langRange "EN"^^xsd:string)
    DataOneOf("cat@en-US"^^rdf:PlainLiteral "dog@en"^^rdf:PlainLiteral
      "perro@es"^^rdf:PlainLiteral "fish@en-GB"^^rdf:PlainLiteral))"#

#guard decideOrderedRange "2" finiteLanguageRange == some true
#guard decideOrderedRange "3" finiteLanguageRange == some false

private def finiteUnicodePatternRange : String :=
  r#"DataIntersectionOf(
    DataOneOf("é1"^^xsd:string "𐐀2"^^xsd:string "ab"^^xsd:string)
    DataComplementOf(DatatypeRestriction(xsd:string xsd:pattern "[a-z]+"^^xsd:string)))"#

#guard decideOrderedRange "2" finiteUnicodePatternRange == some true
#guard decideOrderedRange "3" finiteUnicodePatternRange == some false

-- Unbounded xsd:pattern, rdf:langRange, length, subtype, and Boolean combinations.
#guard decideOrderedRange "2" r#"DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)"# == some true
#guard decideOrderedRange "3" r#"DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)"# == some false

#guard decideOrderedRange "3"
  r#"DatatypeRestriction(xsd:string xsd:pattern "a*"^^xsd:string xsd:maxLength "2"^^xsd:integer)"# == some true
#guard decideOrderedRange "4"
  r#"DatatypeRestriction(xsd:string xsd:pattern "a*"^^xsd:string xsd:maxLength "2"^^xsd:integer)"# == some false

#guard decideOrderedRange "1"
  r#"DataIntersectionOf(
    DatatypeRestriction(xsd:string xsd:pattern "a.*"^^xsd:string)
    DatatypeRestriction(xsd:string xsd:pattern "b.*"^^xsd:string))"# == some false

-- Complement of patterns: {"a","b","c"} \ {"a","b"} has exactly 1 value.
#guard decideOrderedRange "1"
  r#"DataIntersectionOf(
    DatatypeRestriction(xsd:string xsd:pattern "a|b|c"^^xsd:string)
    DataComplementOf(DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)))"# == some true
#guard decideOrderedRange "2"
  r#"DataIntersectionOf(
    DatatypeRestriction(xsd:string xsd:pattern "a|b|c"^^xsd:string)
    DataComplementOf(DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)))"# == some false

-- String subtypes combined with general xsd:pattern.
#guard decideOrderedRange "1"
  r#"DataIntersectionOf(xsd:NCName DatatypeRestriction(xsd:string xsd:pattern "[0-9]+"^^xsd:string))"# == some false
#guard decideOrderedRange "1"
  r#"DatatypeRestriction(xsd:token xsd:pattern " a|a  b"^^xsd:string)"# == some false
#guard decideOrderedRange "1"
  r#"DatatypeRestriction(xsd:token xsd:pattern "a b|a  b"^^xsd:string)"# == some true
#guard decideOrderedRange "2"
  r#"DatatypeRestriction(xsd:token xsd:pattern "a b|a  b"^^xsd:string)"# == some false
#guard decideOrderedRange "2"
  r#"DatatypeRestriction(xsd:language xsd:pattern "[a-z]{2}-[A-Z]{2}"^^xsd:string)"# == some true
#guard decideOrderedRange "1"
  r#"DatatypeRestriction(xsd:language xsd:pattern "[0-9]+"^^xsd:string)"# == some false

-- rdf:langRange on rdf:PlainLiteral: subsumption, disjointness, complements, and length/pattern mixes.
#guard decideOrderedRange "1"
  r#"DataIntersectionOf(
    DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en-US"^^xsd:string)
    DataComplementOf(DatatypeRestriction(rdf:PlainLiteral rdf:langRange "EN"^^xsd:string)))"# == some false
#guard decideOrderedRange "2"
  r#"DataIntersectionOf(
    DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string)
    DataComplementOf(DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en-US"^^xsd:string)))"# == some true
#guard decideOrderedRange "1"
  r#"DataIntersectionOf(
    DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string)
    DatatypeRestriction(rdf:PlainLiteral rdf:langRange "fr"^^xsd:string))"# == some false
#guard decideOrderedRange "1"
  r#"DataIntersectionOf(
    DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string)
    xsd:string)"# == some false
#guard decideOrderedRange "3"
  r#"DatatypeRestriction(rdf:PlainLiteral xsd:length "0"^^xsd:integer rdf:langRange "en"^^xsd:string)"# == some true
#guard decideOrderedRange "2"
  r#"DatatypeRestriction(rdf:PlainLiteral xsd:pattern "hi|ok"^^xsd:string rdf:langRange "en"^^xsd:string)"# == some true

-- xsd:anyURI with xsd:pattern and length facets.
#guard decideOrderedRange "2"
  r#"DatatypeRestriction(xsd:anyURI xsd:pattern "http://(a|b)"^^xsd:string)"# == some true
#guard decideOrderedRange "3"
  r#"DatatypeRestriction(xsd:anyURI xsd:pattern "http://(a|b)"^^xsd:string)"# == some false
#guard decideOrderedRange "2"
  r#"DatatypeRestriction(xsd:anyURI xsd:pattern "https://[a-z]+"^^xsd:string xsd:maxLength "10"^^xsd:integer)"# == some true

-- Mixed HasKey with xsd:pattern: singleton pattern forces a = b (UNSAT), two-value pattern is SAT.
#guard (decideRealSourceClosure? (realKeyCase
  r#"DatatypeRestriction(xsd:string xsd:pattern "only"^^xsd:string)"#) []).map Prod.snd == some false
#guard (decideRealSourceClosure? (realKeyCase
  r#"DatatypeRestriction(xsd:string xsd:pattern "one|two"^^xsd:string)"#) []).map Prod.snd == some true

#print axioms parseSourceDocument_inScope
#print axioms tokenizeTotal_printSrcTokens
#print axioms parseDocumentTokens_renderOntologyTokens
#print axioms parseSourceDocument_renderCanonicalOFN
#print axioms mkDocId_injective
#print axioms resolveSourceImports_spec
#print axioms resolveSourceImports_reachable
#print axioms resolveSourceImports_models_iff
#print axioms resolveSourceImports_sat_iff
#print axioms decideSourceClosure_iff
#print axioms decideUniversalSourceClosure_iff
#print axioms decideObjectSourceClosure_iff
#print axioms decideObjectSourceSubclass_sound
#print axioms decideUniversalSourceSubclass_sound
#print axioms decideSourceClosure_unsat_iff
#print axioms decideWellFormedSourceClosure_iff
#print axioms decideRealSourceClosure_iff

end Sabrina.OWL2.SROIQD.Termination.SourceImport
