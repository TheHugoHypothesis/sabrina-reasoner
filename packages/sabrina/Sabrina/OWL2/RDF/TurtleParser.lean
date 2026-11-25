import Sabrina.OWL2.RDF.Graph

/-! Native Lean 4 W3C Turtle 1.1 parser (`parseTurtle`).

Supports:
- `@prefix` / `PREFIX` and `@base` / `BASE` directives (case-insensitive SPARQL style)
- `<IRI>` with RFC 3986 relative resolution, prefixed names (`ex:Foo`, `:Bar`, `PN_LOCAL_ESC`),
  blank nodes (`_:id`), predicate shorthand `a` (`rdf:type`)
- Predicate-object lists (`;`), object lists (`,`), blank-node property lists (`[ ... ]`),
  collections (`( ... )` and `()`)
- Single-quoted and triple-quoted string literals (`"..."`, `'...'`, `"""..."""`, `'''...'''`)
  with `\n`, `\r`, `\t`, `\\`, `\"`, `\'`, `\uXXXX`, `\UXXXXXXXX` escapes, `^^datatype`, `@lang`
- Shorthand numeric (`xsd:integer`, `xsd:decimal`, `xsd:double`) and boolean (`xsd:boolean`) literals
- `#` line comments. -/

namespace Sabrina.OWL2.RDF.Turtle

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.RDF

private inductive TToken where
  | dot
  | semi
  | comma
  | lbrack
  | rbrack
  | lparen
  | rparen
  | caret2
  | atPrefix
  | atBase
  | langTag (tag : String)
  | iri (val : String)
  | str (val : String)
  | bnode (id : String)
  | numLit (lex : String) (dt : IRI)
  | ident (val : String)
  deriving Repr, BEq

private def isPnLocalEsc (c : Char) : Bool :=
  c == '_' || c == '~' || c == '.' || c == '-' || c == '!' || c == '$' || c == '&' ||
  c == '\'' || c == '(' || c == ')' || c == '*' || c == '+' || c == ',' || c == ';' ||
  c == '=' || c == '/' || c == '?' || c == '#' || c == '@' || c == '%'

private def parseHex (cs : List Char) : Option Nat :=
  cs.foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (acc * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (acc * 16 + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c && c ≤ 'F' then some (acc * 16 + (c.toNat - 'A'.toNat + 10))
    else none) 0

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == ':' || c == '.' || c.toNat ≥ 0x80

private def tokenizeTurtle (input : String) : Except String (List TToken) := Id.run do
  let cleaned := if input.startsWith "\uFEFF" then String.ofList (input.toList.drop 1) else input
  let cs := cleaned.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut toks : List TToken := []
  while i < n do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c == '#' then
      while i < n && cs[i]! != '\n' do i := i + 1
    else if c == ';' then toks := .semi :: toks; i := i + 1
    else if c == ',' then toks := .comma :: toks; i := i + 1
    else if c == '[' then toks := .lbrack :: toks; i := i + 1
    else if c == ']' then toks := .rbrack :: toks; i := i + 1
    else if c == '(' then toks := .lparen :: toks; i := i + 1
    else if c == ')' then toks := .rparen :: toks; i := i + 1
    else if c == '^' then
      if i + 1 < n && cs[i + 1]! == '^' then
        toks := .caret2 :: toks; i := i + 2
      else return .error "unexpected single '^' in Turtle"
    else if c == '@' then
      i := i + 1
      let mut buf : List Char := []
      while i < n && (cs[i]!.isAlphanum || cs[i]! == '-') do
        buf := cs[i]! :: buf; i := i + 1
      let word := String.ofList buf.reverse
      if word == "prefix" then toks := .atPrefix :: toks
      else if word == "base" then toks := .atBase :: toks
      else if !word.isEmpty then toks := .langTag word :: toks
      else return .error "empty '@' directive or language tag in Turtle"
    else if c == '<' then
      i := i + 1
      let mut buf : List Char := []
      while i < n && cs[i]! != '>' do
        let ch := cs[i]!
        if ch == '\\' && i + 1 < n then
          let esc := cs[i + 1]!
          if esc == 'u' && i + 5 < n then
            let hex := [cs[i+2]!, cs[i+3]!, cs[i+4]!, cs[i+5]!]
            match parseHex hex with
            | some cp => buf := Char.ofNat cp :: buf; i := i + 6
            | none => return .error "invalid \\u escape in Turtle IRI"
          else if esc == 'U' && i + 9 < n then
            let hex := [cs[i+2]!, cs[i+3]!, cs[i+4]!, cs[i+5]!, cs[i+6]!, cs[i+7]!, cs[i+8]!, cs[i+9]!]
            match parseHex hex with
            | some cp => buf := Char.ofNat cp :: buf; i := i + 10
            | none => return .error "invalid \\U escape in Turtle IRI"
          else return .error s!"invalid escape '\\{esc}' in Turtle IRI"
        else if ch.isWhitespace || ch == '<' then
          return .error s!"invalid character '{ch}' in Turtle <IRI>"
        else
          buf := ch :: buf; i := i + 1
      if i >= n then return .error "unterminated <IRI> in Turtle"
      i := i + 1
      toks := .iri (String.ofList buf.reverse) :: toks
    else if c == '"' || c == '\'' then
      let q := c
      let isLong := i + 2 < n && cs[i + 1]! == q && cs[i + 2]! == q
      i := if isLong then i + 3 else i + 1
      let mut buf : List Char := []
      let mut closed := false
      while i < n do
        if isLong && i + 2 < n && cs[i]! == q && cs[i + 1]! == q && cs[i + 2]! == q then
          i := i + 3; closed := true; break
        else if !isLong && cs[i]! == q then
          i := i + 1; closed := true; break
        else if cs[i]! == '\\' && i + 1 < n then
          let esc := cs[i + 1]!
          match esc with
          | 't' => buf := '\t' :: buf; i := i + 2
          | 'b' => buf := Char.ofNat 8 :: buf; i := i + 2
          | 'n' => buf := '\n' :: buf; i := i + 2
          | 'r' => buf := '\r' :: buf; i := i + 2
          | 'f' => buf := Char.ofNat 12 :: buf; i := i + 2
          | '"' => buf := '"' :: buf; i := i + 2
          | '\'' => buf := '\'' :: buf; i := i + 2
          | '\\' => buf := '\\' :: buf; i := i + 2
          | 'u' =>
            if i + 5 < n then
              match parseHex [cs[i+2]!, cs[i+3]!, cs[i+4]!, cs[i+5]!] with
              | some cp => buf := Char.ofNat cp :: buf; i := i + 6
              | none => return .error "invalid \\u escape in Turtle string"
            else return .error "truncated \\u escape in Turtle string"
          | 'U' =>
            if i + 9 < n then
              match parseHex [cs[i+2]!, cs[i+3]!, cs[i+4]!, cs[i+5]!, cs[i+6]!, cs[i+7]!, cs[i+8]!, cs[i+9]!] with
              | some cp => buf := Char.ofNat cp :: buf; i := i + 10
              | none => return .error "invalid \\U escape in Turtle string"
            else return .error "truncated \\U escape in Turtle string"
          | _ => return .error s!"unknown escape '\\{esc}' in Turtle string"
        else
          buf := cs[i]! :: buf; i := i + 1
      if !closed then return .error "unterminated string literal in Turtle"
      toks := .str (String.ofList buf.reverse) :: toks
    else if c == '.' then
      -- Check if starting a decimal like .5
      if i + 1 < n && cs[i + 1]!.isDigit then
        let mut buf : List Char := ['.']
        i := i + 1
        while i < n && cs[i]!.isDigit do buf := cs[i]! :: buf; i := i + 1
        let mut isDouble := false
        if i < n && (cs[i]! == 'e' || cs[i]! == 'E') then
          isDouble := true
          buf := cs[i]! :: buf; i := i + 1
          if i < n && (cs[i]! == '+' || cs[i]! == '-') then buf := cs[i]! :: buf; i := i + 1
          while i < n && cs[i]!.isDigit do buf := cs[i]! :: buf; i := i + 1
        toks := .numLit (String.ofList buf.reverse) (if isDouble then xsdDouble else xsdDecimal) :: toks
      else
        toks := .dot :: toks; i := i + 1
    else if c.isDigit || ((c == '+' || c == '-') && i + 1 < n && (cs[i + 1]!.isDigit || cs[i + 1]! == '.')) then
      let mut buf : List Char := [c]
      i := i + 1
      let mut hasDot := false
      let mut hasExp := false
      while i < n && cs[i]!.isDigit do buf := cs[i]! :: buf; i := i + 1
      if i < n && cs[i]! == '.' && i + 1 < n && cs[i + 1]!.isDigit then
        hasDot := true
        buf := '.' :: buf; i := i + 1
        while i < n && cs[i]!.isDigit do buf := cs[i]! :: buf; i := i + 1
      if i < n && (cs[i]! == 'e' || cs[i]! == 'E') then
        hasExp := true
        buf := cs[i]! :: buf; i := i + 1
        if i < n && (cs[i]! == '+' || cs[i]! == '-') then buf := cs[i]! :: buf; i := i + 1
        while i < n && cs[i]!.isDigit do buf := cs[i]! :: buf; i := i + 1
      let dt := if hasExp then xsdDouble else if hasDot then xsdDecimal else xsdInteger
      toks := .numLit (String.ofList buf.reverse) dt :: toks
    else if c == '_' && i + 1 < n && cs[i + 1]! == ':' then
      i := i + 2
      let mut buf : List Char := []
      while i < n && (cs[i]!.isAlphanum || cs[i]! == '_' || cs[i]! == '-' || cs[i]! == '.') do
        buf := cs[i]! :: buf; i := i + 1
      -- Strip trailing '.' if it terminates a statement
      while buf.head? == some '.' do
        buf := buf.tail; i := i - 1
      if buf.isEmpty then return .error "empty blank node label '_:' in Turtle"
      toks := .bnode (String.ofList buf.reverse) :: toks
    else if isNameChar c || c == '\\' then
      let mut buf : List Char := []
      while i < n do
        let ch := cs[i]!
        if ch == '\\' && i + 1 < n && isPnLocalEsc cs[i + 1]! then
          buf := cs[i + 1]! :: buf; i := i + 2
        else if isNameChar ch then
          buf := ch :: buf; i := i + 1
        else break
      -- A trailing '.' on a prefixed name is a statement terminator per Turtle 1.1
      while buf.head? == some '.' do
        buf := buf.tail; i := i - 1
      let word := String.ofList buf.reverse
      if word.isEmpty then return .error "unexpected token in Turtle"
      toks := .ident word :: toks
    else
      return .error s!"unexpected character '{c}' in Turtle"
  return .ok toks.reverse

private structure TurtleState where
  tokens : List TToken
  prefixes : PrefixMap := []
  baseIRI : Option IRI := none
  triples : List RDFTriple := []
  nextBNode : Nat := 0

private abbrev TtlP (α : Type) := StateT TurtleState (Except String) α

private def peek : TtlP (Option TToken) := return (← get).tokens.head?

private def nextTok : TtlP TToken := do
  let st ← get
  match st.tokens with
  | [] => throw "unexpected end of Turtle input"
  | t :: rest =>
    set { st with tokens := rest }
    return t

private def expectTok (expected : TToken) : TtlP Unit := do
  let t ← nextTok
  if t != expected then throw s!"expected {repr expected} in Turtle, got {repr t}"

private def freshBNode : TtlP RDFTerm := do
  let st ← get
  set { st with nextBNode := st.nextBNode + 1 }
  return .bnode s!"ttl_b{st.nextBNode}"

private def emit (s : RDFTerm) (p : IRI) (o : RDFTerm) : TtlP Unit :=
  modify fun st => { st with triples := ⟨s, p, o⟩ :: st.triples }

private def expandPName (s : String) : TtlP IRI := do
  let st ← get
  match s.splitOn ":" with
  | pfx :: rest =>
    if rest.isEmpty then throw s!"expected prefixed name containing ':', got '{s}'"
    let loc := ":".intercalate rest
    match st.prefixes.find? (fun (k, _) => k == pfx) with
    | some (_, ns) => return ns ++ loc
    | none => throw s!"undeclared Turtle prefix '{pfx}:' in '{s}'"
  | [] => throw "empty prefixed name in Turtle"

private def parseIRI : TtlP IRI := do
  match ← nextTok with
  | .iri s => return resolveIRI (← get).baseIRI s
  | .ident s => expandPName s
  | t => throw s!"expected IRI or prefixed name in Turtle, got {repr t}"

private def parseVerb : TtlP IRI := do
  match ← peek with
  | some (.ident "a") =>
    let _ ← nextTok
    return rdfType
  | _ => parseIRI

mutual

private partial def parseObject : TtlP RDFTerm := do
  match ← peek with
  | some (.iri _) => return .iri (← parseIRI)
  | some (.bnode id) =>
    let _ ← nextTok
    return .bnode id
  | some (.str lex) =>
    let _ ← nextTok
    match ← peek with
    | some .caret2 =>
      let _ ← nextTok
      let dt ← parseIRI
      return .literal lex dt none
    | some (.langTag tag) =>
      let _ ← nextTok
      return .literal lex rdfLangString (some tag)
    | _ => return .literal lex xsdString none
  | some (.numLit lex dt) =>
    let _ ← nextTok
    return .literal lex dt none
  | some (.ident "true") =>
    let _ ← nextTok
    return .literal "true" xsdBoolean none
  | some (.ident "false") =>
    let _ ← nextTok
    return .literal "false" xsdBoolean none
  | some (.ident s) =>
    let _ ← nextTok
    return .iri (← expandPName s)
  | some .lbrack =>
    let _ ← nextTok
    let b ← freshBNode
    if (← peek) == some .rbrack then
      let _ ← nextTok
      return b
    parsePredicateObjectList b
    expectTok .rbrack
    return b
  | some .lparen =>
    let _ ← nextTok
    let mut items : List RDFTerm := []
    while (← peek) != some .rparen do
      items := (← parseObject) :: items
    expectTok .rparen
    let rec buildList : List RDFTerm → TtlP RDFTerm
      | [] => return .iri rdfNil
      | x :: xs => do
        let cell ← freshBNode
        let rest ← buildList xs
        emit cell rdfFirst x
        emit cell rdfRest rest
        return cell
    buildList items.reverse
  | other => throw s!"unexpected token while parsing Turtle object: {repr other}"

private partial def parseObjectList (subj : RDFTerm) (pred : IRI) : TtlP Unit := do
  let obj ← parseObject
  emit subj pred obj
  while (← peek) == some .comma do
    let _ ← nextTok
    let nextObj ← parseObject
    emit subj pred nextObj

private partial def parsePredicateObjectList (subj : RDFTerm) : TtlP Unit := do
  let pred ← parseVerb
  parseObjectList subj pred
  while (← peek) == some .semi do
    let _ ← nextTok
    match ← peek with
    | some .dot | some .rbrack | none => break
    | _ =>
      let p ← parseVerb
      parseObjectList subj p

end

private def isCiEq (a b : String) : Bool :=
  a.toList.map (fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c) ==
  b.toList.map (fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

private def parsePrefixName : TtlP String := do
  match ← nextTok with
  | .ident s =>
    if s.endsWith ":" then return String.ofList s.toList.dropLast
    else throw s!"expected prefix label ending with ':', got '{s}'"
  | t => throw s!"expected prefix label, got {repr t}"

private def parseStatement : TtlP Unit := do
  match ← peek with
  | some .atPrefix =>
    let _ ← nextTok
    let pfx ← parsePrefixName
    let iri ← match ← nextTok with
      | .iri s => pure (resolveIRI (← get).baseIRI s)
      | t => throw s!"expected <IRI> in @prefix, got {repr t}"
    expectTok .dot
    modify fun st => { st with prefixes := (pfx, iri) :: st.prefixes }
  | some .atBase =>
    let _ ← nextTok
    let iri ← match ← nextTok with
      | .iri s => pure (resolveIRI (← get).baseIRI s)
      | t => throw s!"expected <IRI> in @base, got {repr t}"
    expectTok .dot
    modify fun st => { st with baseIRI := some iri }
  | some (.ident w) =>
    if isCiEq w "PREFIX" then
      let _ ← nextTok
      let pfx ← parsePrefixName
      let iri ← match ← nextTok with
        | .iri s => pure (resolveIRI (← get).baseIRI s)
        | t => throw s!"expected <IRI> in PREFIX, got {repr t}"
      modify fun st => { st with prefixes := (pfx, iri) :: st.prefixes }
    else if isCiEq w "BASE" then
      let _ ← nextTok
      let iri ← match ← nextTok with
        | .iri s => pure (resolveIRI (← get).baseIRI s)
        | t => throw s!"expected <IRI> in BASE, got {repr t}"
      modify fun st => { st with baseIRI := some iri }
    else
      let subj ← parseObject
      parsePredicateObjectList subj
      expectTok .dot
  | some .lbrack =>
    let _ ← nextTok
    let b ← freshBNode
    if (← peek) != some .rbrack then
      parsePredicateObjectList b
    expectTok .rbrack
    if (← peek) != some .dot then
      parsePredicateObjectList b
    expectTok .dot
  | _ =>
    let subj ← parseObject
    parsePredicateObjectList subj
    expectTok .dot

/-- Parse a W3C Turtle 1.1 document into an `RDFGraph`. -/
def parseTurtle (input : String) : Except String RDFGraph := do
  let toks ← tokenizeTurtle input
  let ((), st) ← (do
    while (← peek).isSome do
      parseStatement).run { tokens := toks }
  return {
    triples := st.triples.reverse
    prefixes := st.prefixes.reverse
    baseIRI := st.baseIRI
  }

end Sabrina.OWL2.RDF.Turtle
