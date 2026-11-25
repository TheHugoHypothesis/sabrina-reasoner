import Sabrina.OWL2.Syntax

/-! Recursive-descent parser for W3C OWL 2 Functional-Style Syntax (`.ofn`)
    producing `Sabrina.OWL2.Ontology`, standalone OWL 2 query axioms, and
    multi-document `Import(...)` closure resolution with version IRIs and
    document-scoped anonymous individuals. -/

namespace Sabrina.OWL2.FunctionalSyntax

open Sabrina.OWL2

private inductive Token where
  | lparen
  | rparen
  | eq
  | caret2
  | atSign
  | iri (val : String)
  | str (val : String)
  | ident (val : String)
  deriving Repr, BEq

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == ':' || c == '.' || c == '#' || c == '/' ||
  c == '~' || c == '%' || (c.toNat ≥ 0x80 && !c.isWhitespace)

/-- W3C SPARQL/OWL 2 `PN_LOCAL_ESC` characters permitted after `\` inside prefixed names. -/
private def isPnLocalEsc (c : Char) : Bool :=
  c == '_' || c == '~' || c == '.' || c == '-' || c == '!' || c == '$' || c == '&' ||
  c == '\'' || c == '(' || c == ')' || c == '*' || c == '+' || c == ',' || c == ';' ||
  c == '=' || c == '/' || c == '?' || c == '#' || c == '@' || c == '%'

private def tokenize (input : String) : Except String (List Token) := Id.run do
  let cs := input.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut toks : List Token := []
  while i < n do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c == '#' then
      while i < n && cs[i]! != '\n' do
        i := i + 1
    else if c == '(' then
      toks := .lparen :: toks; i := i + 1
    else if c == ')' then
      toks := .rparen :: toks; i := i + 1
    else if c == '=' then
      toks := .eq :: toks; i := i + 1
    else if c == '@' then
      toks := .atSign :: toks; i := i + 1
    else if c == '^' then
      if i + 1 < n && cs[i + 1]! == '^' then
        toks := .caret2 :: toks; i := i + 2
      else
        return .error "unexpected single '^' in Functional Syntax"
    else if c == '<' then
      i := i + 1
      let mut buf : List Char := []
      while i < n && cs[i]! != '>' do
        let ch := cs[i]!
        if ch.isWhitespace || ch == '<' then
          return .error s!"invalid character '{ch}' inside <IRI>"
        buf := ch :: buf; i := i + 1
      if i >= n then return .error "unterminated <IRI>"
      i := i + 1
      toks := .iri (String.ofList buf.reverse) :: toks
    else if c == '"' then
      i := i + 1
      let mut buf : List Char := []
      let mut closed := false
      while i < n do
        let ch := cs[i]!
        if ch == '\\' && i + 1 < n then
          buf := cs[i + 1]! :: buf; i := i + 2
        else if ch == '"' then
          i := i + 1; closed := true; break
        else
          buf := ch :: buf; i := i + 1
      if !closed then return .error "unterminated string literal"
      toks := .str (String.ofList buf.reverse) :: toks
    else if isIdentChar c then
      let mut buf : List Char := []
      while i < n do
        let ch := cs[i]!
        if ch == '\\' && i + 1 < n && isPnLocalEsc cs[i + 1]! then
          buf := cs[i + 1]! :: buf; i := i + 2
        else if isIdentChar ch then
          buf := ch :: buf; i := i + 1
        else
          break
      toks := .ident (String.ofList buf.reverse) :: toks
    else
      return .error s!"unexpected character '{c}' in Functional Syntax"
  return .ok toks.reverse

abbrev PrefixMap := List (String × String)

private def defaultPrefixes : PrefixMap := [
  ("owl", "http://www.w3.org/2002/07/owl#"),
  ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
  ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
  ("xsd", "http://www.w3.org/2001/XMLSchema#")
]

private structure ParseState where
  tokens : List Token
  prefixes : PrefixMap := defaultPrefixes
  docId : String := "doc:0"

private abbrev Parser (α : Type) := StateT ParseState (Except String) α

private def peek : Parser (Option Token) := do
  return (← get).tokens.head?

private def nextTok : Parser Token := do
  let st ← get
  match st.tokens with
  | [] => throw "unexpected end of Functional Syntax input"
  | t :: rest => set { st with tokens := rest }; return t

private def expectLParen : Parser Unit := do
  match ← nextTok with
  | .lparen => return ()
  | t => throw s!"expected '(', got {repr t}"

private def expectRParen : Parser Unit := do
  match ← nextTok with
  | .rparen => return ()
  | t => throw s!"expected ')', got {repr t}"

private def splitPrefix (s : String) : Option (String × String) :=
  let rec go (acc : List Char) : List Char → Option (String × String)
    | [] => none
    | ':' :: rest => some (String.ofList acc.reverse, String.ofList rest)
    | c :: rest => go (c :: acc) rest
  go [] s.toList

private def expandIRI (s : String) : Parser IRI := do
  let st ← get
  match splitPrefix s with
  | some (pfx, loc) =>
    match st.prefixes.lookup pfx with
    | some base => return base ++ loc
    | none => throw s!"undeclared prefix '{pfx}:' in '{s}'"
  | none => throw s!"expected <IRI> or prefixed name, got '{s}'"

private def parseIRI : Parser IRI := do
  match ← nextTok with
  | .iri s => return s
  | .ident s => expandIRI s
  | t => throw s!"expected IRI, got {repr t}"

private def parseIndividual : Parser Individual := do
  match ← nextTok with
  | .iri s => return .named s
  | .ident s =>
    if s.startsWith "_:" then
      let doc := (← get).docId
      return .anonymous doc (String.ofList (s.toList.drop 2))
    else
      return .named (← expandIRI s)
  | t => throw s!"expected individual, got {repr t}"

private def parseNat : Parser Nat := do
  match ← nextTok with
  | .ident s =>
    match s.toNat? with
    | some n => return n
    | none => throw s!"expected nonnegative integer, got '{s}'"
  | t => throw s!"expected nonnegative integer, got {repr t}"

private def parseLiteral : Parser Literal := do
  match ← nextTok with
  | .str raw =>
    match ← peek with
    | some .caret2 =>
      let _ ← nextTok
      let dt ← parseIRI
      return ⟨raw, dt⟩
    | some .atSign =>
      let _ ← nextTok
      match ← nextTok with
      | .ident lang =>
        return ⟨s!"{raw}@{lang}", "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"⟩
      | t => throw s!"expected language tag after '@', got {repr t}"
    | _ => return ⟨raw, "http://www.w3.org/2001/XMLSchema#string"⟩
  | t => throw s!"expected string literal, got {repr t}"

private def parseObjProp : Parser ObjectProperty := do
  match ← peek with
  | some (.ident "ObjectInverseOf") =>
    let _ ← nextTok
    expectLParen
    let r ← parseIRI
    expectRParen
    return .inverse r
  | _ => return .named (← parseIRI)

private partial def skipBalanced : Parser Unit := do
  expectLParen
  let mut depth := 1
  while depth > 0 do
    match ← nextTok with
    | .lparen => depth := depth + 1
    | .rparen => depth := depth - 1
    | _ => pure ()

private partial def skipAnnotations : Parser Unit := do
  while (← peek) == some (.ident "Annotation") do
    let _ ← nextTok
    skipBalanced

private partial def parseManyUntilRParen {α : Type} (p : Parser α) : Parser (List α) := do
  let mut acc : List α := []
  while (← peek) != some .rparen do
    acc := (← p) :: acc
  expectRParen
  return acc.reverse

private def foldDataIntersect : List DataRange → DataRange
  | [] => .datatype literalDatatype
  | [d] => d
  | d :: ds => .intersection d (foldDataIntersect ds)

private def foldDataUnite : List DataRange → DataRange
  | [] => .complement (.datatype literalDatatype)
  | [d] => d
  | d :: ds => .union d (foldDataUnite ds)

private def foldClassIntersect : List ClassExpr → ClassExpr
  | [] => .named thing
  | [c] => c
  | c :: cs => .intersection c (foldClassIntersect cs)

private def foldClassUnite : List ClassExpr → ClassExpr
  | [] => .named nothing
  | [c] => c
  | c :: cs => .union c (foldClassUnite cs)

private partial def parseDataRange : Parser DataRange := do
  match ← peek with
  | some (.ident "DataIntersectionOf") =>
    let _ ← nextTok; expectLParen
    let ds ← parseManyUntilRParen parseDataRange
    return foldDataIntersect ds
  | some (.ident "DataUnionOf") =>
    let _ ← nextTok; expectLParen
    let ds ← parseManyUntilRParen parseDataRange
    return foldDataUnite ds
  | some (.ident "DataComplementOf") =>
    let _ ← nextTok; expectLParen
    let d ← parseDataRange; expectRParen
    return .complement d
  | some (.ident "DataOneOf") =>
    let _ ← nextTok; expectLParen
    let ls ← parseManyUntilRParen parseLiteral
    return .oneOf ls
  | some (.ident "DatatypeRestriction") =>
    let _ ← nextTok; expectLParen
    let dt ← parseIRI
    let fs ← parseManyUntilRParen do
      let f ← parseIRI
      let b ← parseLiteral
      return ⟨f, b⟩
    return .restriction dt fs
  | _ => return .datatype (← parseIRI)

private partial def parseClassExpr : Parser ClassExpr := do
  match ← peek with
  | some (.ident "ObjectIntersectionOf") =>
    let _ ← nextTok; expectLParen
    let cs ← parseManyUntilRParen parseClassExpr
    return foldClassIntersect cs
  | some (.ident "ObjectUnionOf") =>
    let _ ← nextTok; expectLParen
    let cs ← parseManyUntilRParen parseClassExpr
    return foldClassUnite cs
  | some (.ident "ObjectComplementOf") =>
    let _ ← nextTok; expectLParen
    let c ← parseClassExpr; expectRParen
    return .complement c
  | some (.ident "ObjectOneOf") =>
    let _ ← nextTok; expectLParen
    let inds ← parseManyUntilRParen parseIndividual
    return .oneOf inds
  | some (.ident "ObjectSomeValuesFrom") =>
    let _ ← nextTok; expectLParen
    let r ← parseObjProp; let c ← parseClassExpr; expectRParen
    return .objectSome r c
  | some (.ident "ObjectAllValuesFrom") =>
    let _ ← nextTok; expectLParen
    let r ← parseObjProp; let c ← parseClassExpr; expectRParen
    return .objectAll r c
  | some (.ident "ObjectHasValue") =>
    let _ ← nextTok; expectLParen
    let r ← parseObjProp; let a ← parseIndividual; expectRParen
    return .objectValue r a
  | some (.ident "ObjectHasSelf") =>
    let _ ← nextTok; expectLParen
    let r ← parseObjProp; expectRParen
    return .objectSelf r
  | some (.ident "ObjectMinCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let r ← parseObjProp
    let c ← if (← peek) == some .rparen then pure (.named thing) else parseClassExpr
    expectRParen
    return .objectMin n r c
  | some (.ident "ObjectMaxCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let r ← parseObjProp
    let c ← if (← peek) == some .rparen then pure (.named thing) else parseClassExpr
    expectRParen
    return .objectMax n r c
  | some (.ident "ObjectExactCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let r ← parseObjProp
    let c ← if (← peek) == some .rparen then pure (.named thing) else parseClassExpr
    expectRParen
    return .objectExact n r c
  | some (.ident "DataSomeValuesFrom") =>
    let _ ← nextTok; expectLParen
    let dp ← parseIRI; let d ← parseDataRange; expectRParen
    return .dataSome dp d
  | some (.ident "DataAllValuesFrom") =>
    let _ ← nextTok; expectLParen
    let dp ← parseIRI; let d ← parseDataRange; expectRParen
    return .dataAll dp d
  | some (.ident "DataHasValue") =>
    let _ ← nextTok; expectLParen
    let dp ← parseIRI; let l ← parseLiteral; expectRParen
    return .dataValue dp l
  | some (.ident "DataMinCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let dp ← parseIRI
    let d ← if (← peek) == some .rparen then pure (.datatype literalDatatype) else parseDataRange
    expectRParen
    return .dataMin n dp d
  | some (.ident "DataMaxCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let dp ← parseIRI
    let d ← if (← peek) == some .rparen then pure (.datatype literalDatatype) else parseDataRange
    expectRParen
    return .dataMax n dp d
  | some (.ident "DataExactCardinality") =>
    let _ ← nextTok; expectLParen
    let n ← parseNat; let dp ← parseIRI
    let d ← if (← peek) == some .rparen then pure (.datatype literalDatatype) else parseDataRange
    expectRParen
    return .dataExact n dp d
  | _ => return .named (← parseIRI)

/-- W3C OWL 2 §5 entity declaration kinds. -/
inductive EntityKind where
  | cls
  | datatype
  | objectProperty
  | dataProperty
  | annotationProperty
  | namedIndividual
  deriving DecidableEq, Repr

/-- W3C OWL 2 §5.8 `Declaration(Entity)` axiom. -/
structure EntityDecl where
  kind : EntityKind
  iri : IRI
  deriving DecidableEq, Repr

/-- W3C OWL 2 §10.2.1 annotation subject (IRI or document-scoped anonymous individual). -/
inductive AnnotationSubject where
  | iri (v : IRI)
  | anonymous (docId localId : String)
  deriving DecidableEq, Repr

/-- W3C OWL 2 §10.2.1 annotation value (IRI, anonymous individual, or literal). -/
inductive AnnotationValue where
  | iri (v : IRI)
  | anonymous (docId localId : String)
  | literal (l : Literal)
  deriving DecidableEq, Repr

/-- W3C OWL 2 §10.2 annotation axioms (semantically inert under Direct Semantics,
    retained in `ParsedDocument` for §5.8.2 typing and punning validation). -/
inductive AnnotationAxiom where
  | assertion (prop : IRI) (subj : AnnotationSubject) (val : AnnotationValue)
  | subProperty (sub sup : IRI)
  | domain (prop dom : IRI)
  | range (prop rng : IRI)
  deriving DecidableEq, Repr

private def parseAnnotationSubject : Parser AnnotationSubject := do
  match ← nextTok with
  | .iri s => return .iri s
  | .ident s =>
    if s.startsWith "_:" then
      let doc := (← get).docId
      return .anonymous doc (String.ofList (s.toList.drop 2))
    else
      return .iri (← expandIRI s)
  | t => throw s!"expected annotation subject (IRI or anonymous individual), got {repr t}"

private def parseAnnotationValue : Parser AnnotationValue := do
  match ← peek with
  | some (.str _) => return .literal (← parseLiteral)
  | _ =>
    match ← nextTok with
    | .iri s => return .iri s
    | .ident s =>
      if s.startsWith "_:" then
        let doc := (← get).docId
        return .anonymous doc (String.ofList (s.toList.drop 2))
      else
        return .iri (← expandIRI s)
    | t => throw s!"expected annotation value (IRI, anonymous individual, or literal), got {repr t}"

private def parseEntityDecl : Parser EntityDecl := do
  expectLParen; skipAnnotations
  let kind ← match ← nextTok with
    | .ident "Class" => pure EntityKind.cls
    | .ident "Datatype" => pure EntityKind.datatype
    | .ident "ObjectProperty" => pure EntityKind.objectProperty
    | .ident "DataProperty" => pure EntityKind.dataProperty
    | .ident "AnnotationProperty" => pure EntityKind.annotationProperty
    | .ident "NamedIndividual" => pure EntityKind.namedIndividual
    | t => throw s!"expected entity declaration kind (Class, Datatype, ObjectProperty, DataProperty, AnnotationProperty, NamedIndividual), got {repr t}"
  expectLParen
  let iri ← parseIRI
  expectRParen
  expectRParen
  return ⟨kind, iri⟩

private inductive ParsedItem where
  | logical (ax : Axiom)
  | decl (d : EntityDecl)
  | annot (a : AnnotationAxiom)
  | ontAnnot
  deriving Repr

private partial def parseItem : Parser ParsedItem := do
  match ← nextTok with
  | .ident "Declaration" =>
    return .decl (← parseEntityDecl)
  | .ident "Annotation" =>
    skipBalanced; return .ontAnnot
  | .ident "AnnotationAssertion" =>
    expectLParen; skipAnnotations
    let prop ← parseIRI
    let subj ← parseAnnotationSubject
    let val ← parseAnnotationValue
    expectRParen
    return .annot (.assertion prop subj val)
  | .ident "SubAnnotationPropertyOf" =>
    expectLParen; skipAnnotations
    let sub ← parseIRI
    let sup ← parseIRI
    expectRParen
    return .annot (.subProperty sub sup)
  | .ident "AnnotationPropertyDomain" =>
    expectLParen; skipAnnotations
    let prop ← parseIRI
    let dom ← parseIRI
    expectRParen
    return .annot (.domain prop dom)
  | .ident "AnnotationPropertyRange" =>
    expectLParen; skipAnnotations
    let prop ← parseIRI
    let rng ← parseIRI
    expectRParen
    return .annot (.range prop rng)
  | .ident "SubClassOf" =>
    expectLParen; skipAnnotations
    let a ← parseClassExpr; let b ← parseClassExpr; expectRParen
    return .logical (.subClassOf a b)
  | .ident "EquivalentClasses" =>
    expectLParen; skipAnnotations
    let cs ← parseManyUntilRParen parseClassExpr
    return .logical (.equivalentClasses cs)
  | .ident "DisjointClasses" =>
    expectLParen; skipAnnotations
    let cs ← parseManyUntilRParen parseClassExpr
    return .logical (.disjointClasses cs)
  | .ident "DisjointUnion" =>
    expectLParen; skipAnnotations
    let h ← parseIRI
    let cs ← parseManyUntilRParen parseClassExpr
    return .logical (.disjointUnion h cs)
  | .ident "SubObjectPropertyOf" =>
    expectLParen; skipAnnotations
    match ← peek with
    | some (.ident "ObjectPropertyChain") =>
      let _ ← nextTok; expectLParen
      let rs ← parseManyUntilRParen parseObjProp
      let sup ← parseObjProp; expectRParen
      return .logical (.subObjectPropertyChain rs sup)
    | _ =>
      let r ← parseObjProp; let s ← parseObjProp; expectRParen
      return .logical (.subObjectProperty r s)
  | .ident "EquivalentObjectProperties" =>
    expectLParen; skipAnnotations
    let rs ← parseManyUntilRParen parseObjProp
    return .logical (.equivalentObjectProperties rs)
  | .ident "DisjointObjectProperties" =>
    expectLParen; skipAnnotations
    let rs ← parseManyUntilRParen parseObjProp
    return .logical (.disjointObjectProperties rs)
  | .ident "InverseObjectProperties" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; let s ← parseObjProp; expectRParen
    return .logical (.inverseObjectProperties r s)
  | .ident "ObjectPropertyDomain" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; let c ← parseClassExpr; expectRParen
    return .logical (.objectPropertyDomain r c)
  | .ident "ObjectPropertyRange" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; let c ← parseClassExpr; expectRParen
    return .logical (.objectPropertyRange r c)
  | .ident "FunctionalObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.functionalObjectProperty r)
  | .ident "InverseFunctionalObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.inverseFunctionalObjectProperty r)
  | .ident "ReflexiveObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.reflexiveObjectProperty r)
  | .ident "IrreflexiveObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.irreflexiveObjectProperty r)
  | .ident "SymmetricObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.symmetricObjectProperty r)
  | .ident "AsymmetricObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.asymmetricObjectProperty r)
  | .ident "TransitiveObjectProperty" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; expectRParen
    return .logical (.transitiveObjectProperty r)
  | .ident "SubDataPropertyOf" =>
    expectLParen; skipAnnotations
    let r ← parseIRI; let s ← parseIRI; expectRParen
    return .logical (.subDataProperty r s)
  | .ident "EquivalentDataProperties" =>
    expectLParen; skipAnnotations
    let ds ← parseManyUntilRParen parseIRI
    return .logical (.equivalentDataProperties ds)
  | .ident "DisjointDataProperties" =>
    expectLParen; skipAnnotations
    let ds ← parseManyUntilRParen parseIRI
    return .logical (.disjointDataProperties ds)
  | .ident "DataPropertyDomain" =>
    expectLParen; skipAnnotations
    let dp ← parseIRI; let c ← parseClassExpr; expectRParen
    return .logical (.dataPropertyDomain dp c)
  | .ident "DataPropertyRange" =>
    expectLParen; skipAnnotations
    let dp ← parseIRI; let d ← parseDataRange; expectRParen
    return .logical (.dataPropertyRange dp d)
  | .ident "FunctionalDataProperty" =>
    expectLParen; skipAnnotations
    let dp ← parseIRI; expectRParen
    return .logical (.functionalDataProperty dp)
  | .ident "DatatypeDefinition" =>
    expectLParen; skipAnnotations
    let dt ← parseIRI; let d ← parseDataRange; expectRParen
    return .logical (.datatypeDefinition dt d)
  | .ident "HasKey" =>
    expectLParen; skipAnnotations
    let c ← parseClassExpr
    expectLParen
    let os ← parseManyUntilRParen parseObjProp
    expectLParen
    let ds ← parseManyUntilRParen parseIRI
    expectRParen
    return .logical (.hasKey c os ds)
  | .ident "SameIndividual" =>
    expectLParen; skipAnnotations
    let inds ← parseManyUntilRParen parseIndividual
    return .logical (.sameIndividuals inds)
  | .ident "DifferentIndividuals" =>
    expectLParen; skipAnnotations
    let inds ← parseManyUntilRParen parseIndividual
    return .logical (.differentIndividuals inds)
  | .ident "ClassAssertion" =>
    expectLParen; skipAnnotations
    let c ← parseClassExpr; let a ← parseIndividual; expectRParen
    return .logical (.classAssertion c a)
  | .ident "ObjectPropertyAssertion" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; let a ← parseIndividual; let b ← parseIndividual; expectRParen
    return .logical (.objectAssertion r a b)
  | .ident "NegativeObjectPropertyAssertion" =>
    expectLParen; skipAnnotations
    let r ← parseObjProp; let a ← parseIndividual; let b ← parseIndividual; expectRParen
    return .logical (.negativeObjectAssertion r a b)
  | .ident "DataPropertyAssertion" =>
    expectLParen; skipAnnotations
    let dp ← parseIRI; let a ← parseIndividual; let l ← parseLiteral; expectRParen
    return .logical (.dataAssertion dp a l)
  | .ident "NegativeDataPropertyAssertion" =>
    expectLParen; skipAnnotations
    let dp ← parseIRI; let a ← parseIndividual; let l ← parseLiteral; expectRParen
    return .logical (.negativeDataAssertion dp a l)
  | .ident kw => throw s!"unsupported Functional Syntax axiom: {kw}"
  | t => throw s!"expected axiom keyword, got {repr t}"

private def parseAxiom? : Parser (Option Axiom) := do
  match ← parseItem with
  | .logical ax => return some ax
  | _ => return none

private def parsePrefixDecls : Parser Unit := do
  while (← peek) == some (.ident "Prefix") do
    let _ ← nextTok
    expectLParen
    let pfxTok ← nextTok
    let pfx ← match pfxTok with
      | .ident s =>
        if s.endsWith ":" then pure (String.ofList (s.toList.dropLast))
        else throw s!"expected prefix name ending with ':', got '{s}'"
      | t => throw s!"expected prefix name, got {repr t}"
    match ← nextTok with
    | .eq => pure ()
    | t => throw s!"expected '=' in Prefix declaration, got {repr t}"
    let iri ← match ← nextTok with
      | .iri s =>
        if s.isEmpty then throw "empty <IRI> in Prefix declaration"
        else pure s
      | t => throw s!"expected <IRI> in Prefix declaration, got {repr t}"
    expectRParen
    modify fun st => { st with prefixes := (pfx, iri) :: st.prefixes }

private def parseOptionalHeaderIRI : Parser (Option IRI) := do
  match ← peek with
  | some (.iri s) =>
    let _ ← nextTok
    return some s
  | some (.ident s) =>
    if s.contains ':' then
      let _ ← nextTok
      return some (← expandIRI s)
    else
      return none
  | _ => return none

structure ParsedDocument where
  prefixes : PrefixMap
  ontologyIRI : Option IRI := none
  versionIRI : Option IRI := none
  imports : List IRI := []
  declarations : List EntityDecl := []
  annotationAxioms : List AnnotationAxiom := []
  ontology : Ontology
  deriving Repr

/-- Parse a W3C OWL 2 Functional-Style Syntax document (`Prefix(...) Ontology(...)`)
    scoping anonymous individuals `_:x` to `docId` and retaining entity declarations
    and annotation axioms for §5.8.2 typing validation. -/
def parseDocumentWithId (docId : String) (input : String) : Except String ParsedDocument := do
  let toks ← tokenize input
  let ((ontIRI, verIRI, imps, decls, annots, ont), st) ← (do
    parsePrefixDecls
    match ← nextTok with
    | .ident "Ontology" =>
      expectLParen
      let ontIRI ← parseOptionalHeaderIRI
      let verIRI ← if ontIRI.isSome then parseOptionalHeaderIRI else pure none
      let mut imps : List IRI := []
      let mut decls : List EntityDecl := []
      let mut annots : List AnnotationAxiom := []
      let mut axioms : List Axiom := []
      while (← peek) != some Token.rparen do
        if (← peek) == some (Token.ident "Import") then
          let _ ← nextTok
          expectLParen
          let target ← parseIRI
          expectRParen
          imps := target :: imps
        else
          match ← parseItem with
          | .logical ax => axioms := ax :: axioms
          | .decl d => decls := d :: decls
          | .annot a => annots := a :: annots
          | .ontAnnot => pure ()
      expectRParen
      return (ontIRI, verIRI, imps.reverse, decls.reverse, annots.reverse, axioms.reverse)
    | t => throw s!"expected 'Ontology', got {repr t}").run { tokens := toks, docId := docId }
  if !st.tokens.isEmpty then
    throw "trailing tokens after Ontology(...)"
  return {
    prefixes := st.prefixes
    ontologyIRI := ontIRI
    versionIRI := verIRI
    imports := imps
    declarations := decls
    annotationAxioms := annots
    ontology := ont
  }

/-- Parse a single W3C OWL 2 Functional-Style Syntax document (`Prefix(...) Ontology(...)`). -/
def parseDocument (input : String) : Except String ParsedDocument :=
  parseDocumentWithId "doc:0" input

/-- Full resolved import closure retaining declarations and annotation axioms
    across every reachable document for W3C §5.8.2 typing validation. -/
structure ResolvedOFNClosure where
  prefixes : PrefixMap
  declarations : List EntityDecl
  annotationAxioms : List AnnotationAxiom
  ontology : Ontology
  ontologyIRI : Option IRI := none
  versionIRI : Option IRI := none
  deriving Repr

/-- Resolve the transitive `Import(...)` closure of `rootOFN` against a library
    of `(keyIRI, ofnText)` documents, retaining all declarations and annotation
    axioms across the closure. -/
def resolveImportClosure (rootOFN : String) (library : List (IRI × String)) :
    Except String ResolvedOFNClosure := do
  let rootDoc ← parseDocumentWithId "doc:0" rootOFN
  let mut parsedLib : List (IRI × ParsedDocument) := []
  let mut idx := 1
  for (key, text) in library do
    let doc ← parseDocumentWithId s!"doc:{idx}" text
    parsedLib := (key, doc) :: parsedLib
    idx := idx + 1
  parsedLib := parsedLib.reverse
  let findDoc (target : IRI) : Option ParsedDocument :=
    match parsedLib.find? (fun (k, _) => k == target) with
    | some (_, d) => some d
    | none =>
      match parsedLib.find? (fun (_, d) => d.versionIRI == some target) with
      | some (_, d) => some d
      | none =>
        match parsedLib.find? (fun (_, d) => d.ontologyIRI == some target) with
        | some (_, d) => some d
        | none => none
  let mut visited : List IRI := []
  if let some iri := rootDoc.ontologyIRI then visited := iri :: visited
  if let some iri := rootDoc.versionIRI then visited := iri :: visited
  let mut queue : List IRI := rootDoc.imports
  let mut allDecls : List EntityDecl := rootDoc.declarations
  let mut allAnnots : List AnnotationAxiom := rootDoc.annotationAxioms
  let mut allAxioms : Ontology := rootDoc.ontology
  let mut fuel := (parsedLib.length + 1) * (parsedLib.length + 2) + 64
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match queue with
    | [] => break
    | imp :: rest =>
      queue := rest
      if visited.contains imp then continue
      match findDoc imp with
      | none => throw s!"missing imported ontology: {imp}"
      | some doc =>
        visited := imp :: visited
        if let some iri := doc.ontologyIRI then visited := iri :: visited
        if let some iri := doc.versionIRI then visited := iri :: visited
        allDecls := allDecls ++ doc.declarations
        allAnnots := allAnnots ++ doc.annotationAxioms
        allAxioms := allAxioms ++ doc.ontology
        queue := queue ++ doc.imports
  return {
    prefixes := rootDoc.prefixes
    declarations := allDecls
    annotationAxioms := allAnnots
    ontology := allAxioms
    ontologyIRI := rootDoc.ontologyIRI
    versionIRI := rootDoc.versionIRI
  }

/-- Resolve the transitive `Import(...)` closure of `rootOFN` against a library
    of `(keyIRI, ofnText)` documents. Matches imports by map key, declared
    `versionIRI`, or declared `ontologyIRI`, handles import cycles cleanly,
    rejects missing imports, and scopes anonymous individuals (`_:x`) to their
    originating document per W3C OWL 2 Section 5.6.2. -/
def resolveImports (rootOFN : String) (library : List (IRI × String)) :
    Except String (PrefixMap × Ontology) := do
  let res ← resolveImportClosure rootOFN library
  return (res.prefixes, res.ontology)

/-- Parse a standalone OWL 2 Functional-Style Syntax query axiom using the
    document's declared prefixes (plus standard `owl:`, `rdf:`, `rdfs:`, `xsd:`). -/
def parseQueryAxiom (prefixes : PrefixMap) (input : String) : Except String Axiom := do
  let toks ← tokenize input
  let (ax?, st) ← (do
    parsePrefixDecls
    parseAxiom?).run { tokens := toks, prefixes := prefixes, docId := "query" }
  if !st.tokens.isEmpty then
    throw "trailing tokens in Functional Syntax query"
  match ax? with
  | some ax => return ax
  | none => throw "query must be a logical axiom, not a declaration or annotation"

/-! ### Canonical Functional-Style Rendering & Certified Structural Round-Trip -/

/-- Render an `IRI` as a full bracketed `<IRI>`. -/
def renderIRI (iri : IRI) : String := s!"<{iri}>"

/-- Render an `Individual` in W3C Functional-Style Syntax. -/
def renderIndividual : Individual → String
  | .named iri => renderIRI iri
  | .anonymous _ localId => s!"_:{localId}"

/-- Render an `ObjectProperty` in W3C Functional-Style Syntax. -/
def renderObjectProperty : ObjectProperty → String
  | .named iri => renderIRI iri
  | .inverse iri => s!"ObjectInverseOf({renderIRI iri})"

/-- Render a `Literal` in W3C Functional-Style Syntax. -/
def renderLiteral (l : Literal) : String :=
  s!"\"{l.lexical}\"^^{renderIRI l.datatype}"

/-- Render a `Facet` constraint in W3C Functional-Style Syntax. -/
def renderFacet (f : Facet) : String :=
  s!"{renderIRI f.name} {renderLiteral f.bound}"

/-- Render a `DataRange` in W3C Functional-Style Syntax. -/
def renderDataRange : DataRange → String
  | .datatype iri => renderIRI iri
  | .complement d => s!"DataComplementOf({renderDataRange d})"
  | .intersection a b => s!"DataIntersectionOf({renderDataRange a} {renderDataRange b})"
  | .union a b => s!"DataUnionOf({renderDataRange a} {renderDataRange b})"
  | .oneOf ls => s!"DataOneOf({" ".intercalate (ls.map renderLiteral)})"
  | .restriction dt fs => s!"DatatypeRestriction({renderIRI dt} {" ".intercalate (fs.map renderFacet)})"

/-- Render a `ClassExpr` in W3C Functional-Style Syntax. -/
def renderClassExpr : ClassExpr → String
  | .named iri => renderIRI iri
  | .complement c => s!"ObjectComplementOf({renderClassExpr c})"
  | .intersection a b => s!"ObjectIntersectionOf({renderClassExpr a} {renderClassExpr b})"
  | .union a b => s!"ObjectUnionOf({renderClassExpr a} {renderClassExpr b})"
  | .oneOf inds => s!"ObjectOneOf({" ".intercalate (inds.map renderIndividual)})"
  | .objectSome r c => s!"ObjectSomeValuesFrom({renderObjectProperty r} {renderClassExpr c})"
  | .objectAll r c => s!"ObjectAllValuesFrom({renderObjectProperty r} {renderClassExpr c})"
  | .objectValue r a => s!"ObjectHasValue({renderObjectProperty r} {renderIndividual a})"
  | .objectSelf r => s!"ObjectHasSelf({renderObjectProperty r})"
  | .objectMin n r c => s!"ObjectMinCardinality({n} {renderObjectProperty r} {renderClassExpr c})"
  | .objectMax n r c => s!"ObjectMaxCardinality({n} {renderObjectProperty r} {renderClassExpr c})"
  | .objectExact n r c => s!"ObjectExactCardinality({n} {renderObjectProperty r} {renderClassExpr c})"
  | .dataSome dp d => s!"DataSomeValuesFrom({renderIRI dp} {renderDataRange d})"
  | .dataAll dp d => s!"DataAllValuesFrom({renderIRI dp} {renderDataRange d})"
  | .dataValue dp l => s!"DataHasValue({renderIRI dp} {renderLiteral l})"
  | .dataMin n dp d => s!"DataMinCardinality({n} {renderIRI dp} {renderDataRange d})"
  | .dataMax n dp d => s!"DataMaxCardinality({n} {renderIRI dp} {renderDataRange d})"
  | .dataExact n dp d => s!"DataExactCardinality({n} {renderIRI dp} {renderDataRange d})"

/-- Render an `Axiom` in W3C Functional-Style Syntax. -/
def renderAxiom : Axiom → String
  | .subClassOf a b => s!"SubClassOf({renderClassExpr a} {renderClassExpr b})"
  | .equivalentClasses cs => s!"EquivalentClasses({" ".intercalate (cs.map renderClassExpr)})"
  | .disjointClasses cs => s!"DisjointClasses({" ".intercalate (cs.map renderClassExpr)})"
  | .disjointUnion h cs => s!"DisjointUnion({renderIRI h} {" ".intercalate (cs.map renderClassExpr)})"
  | .subObjectProperty r s => s!"SubObjectPropertyOf({renderObjectProperty r} {renderObjectProperty s})"
  | .subObjectPropertyChain rs s =>
    s!"SubObjectPropertyOf(ObjectPropertyChain({" ".intercalate (rs.map renderObjectProperty)}) {renderObjectProperty s})"
  | .equivalentObjectProperties rs =>
    s!"EquivalentObjectProperties({" ".intercalate (rs.map renderObjectProperty)})"
  | .disjointObjectProperties rs =>
    s!"DisjointObjectProperties({" ".intercalate (rs.map renderObjectProperty)})"
  | .inverseObjectProperties r s =>
    s!"InverseObjectProperties({renderObjectProperty r} {renderObjectProperty s})"
  | .objectPropertyDomain r c => s!"ObjectPropertyDomain({renderObjectProperty r} {renderClassExpr c})"
  | .objectPropertyRange r c => s!"ObjectPropertyRange({renderObjectProperty r} {renderClassExpr c})"
  | .functionalObjectProperty r => s!"FunctionalObjectProperty({renderObjectProperty r})"
  | .inverseFunctionalObjectProperty r => s!"InverseFunctionalObjectProperty({renderObjectProperty r})"
  | .reflexiveObjectProperty r => s!"ReflexiveObjectProperty({renderObjectProperty r})"
  | .irreflexiveObjectProperty r => s!"IrreflexiveObjectProperty({renderObjectProperty r})"
  | .symmetricObjectProperty r => s!"SymmetricObjectProperty({renderObjectProperty r})"
  | .asymmetricObjectProperty r => s!"AsymmetricObjectProperty({renderObjectProperty r})"
  | .transitiveObjectProperty r => s!"TransitiveObjectProperty({renderObjectProperty r})"
  | .subDataProperty r s => s!"SubDataPropertyOf({renderIRI r} {renderIRI s})"
  | .equivalentDataProperties ds => s!"EquivalentDataProperties({" ".intercalate (ds.map renderIRI)})"
  | .disjointDataProperties ds => s!"DisjointDataProperties({" ".intercalate (ds.map renderIRI)})"
  | .dataPropertyDomain dp c => s!"DataPropertyDomain({renderIRI dp} {renderClassExpr c})"
  | .dataPropertyRange dp d => s!"DataPropertyRange({renderIRI dp} {renderDataRange d})"
  | .functionalDataProperty dp => s!"FunctionalDataProperty({renderIRI dp})"
  | .datatypeDefinition dt d => s!"DatatypeDefinition({renderIRI dt} {renderDataRange d})"
  | .hasKey c os ds =>
    s!"HasKey({renderClassExpr c} ({" ".intercalate (os.map renderObjectProperty)}) ({" ".intercalate (ds.map renderIRI)}))"
  | .sameIndividuals inds => s!"SameIndividual({" ".intercalate (inds.map renderIndividual)})"
  | .differentIndividuals inds => s!"DifferentIndividuals({" ".intercalate (inds.map renderIndividual)})"
  | .classAssertion c a => s!"ClassAssertion({renderClassExpr c} {renderIndividual a})"
  | .objectAssertion r a b =>
    s!"ObjectPropertyAssertion({renderObjectProperty r} {renderIndividual a} {renderIndividual b})"
  | .negativeObjectAssertion r a b =>
    s!"NegativeObjectPropertyAssertion({renderObjectProperty r} {renderIndividual a} {renderIndividual b})"
  | .dataAssertion dp a l =>
    s!"DataPropertyAssertion({renderIRI dp} {renderIndividual a} {renderLiteral l})"
  | .negativeDataAssertion dp a l =>
    s!"NegativeDataPropertyAssertion({renderIRI dp} {renderIndividual a} {renderLiteral l})"

/-- Render an `EntityDecl` as a W3C Functional-Style Syntax `Declaration(...)` axiom. -/
def renderEntityDecl (d : EntityDecl) : String :=
  match d.kind with
  | .cls => s!"Declaration(Class({renderIRI d.iri}))"
  | .datatype => s!"Declaration(Datatype({renderIRI d.iri}))"
  | .objectProperty => s!"Declaration(ObjectProperty({renderIRI d.iri}))"
  | .dataProperty => s!"Declaration(DataProperty({renderIRI d.iri}))"
  | .annotationProperty => s!"Declaration(AnnotationProperty({renderIRI d.iri}))"
  | .namedIndividual => s!"Declaration(NamedIndividual({renderIRI d.iri}))"

/-- Render an `AnnotationSubject` in W3C Functional-Style Syntax. -/
def renderAnnotationSubject : AnnotationSubject → String
  | .iri v => renderIRI v
  | .anonymous _ loc => s!"_:{loc}"

/-- Render an `AnnotationValue` in W3C Functional-Style Syntax. -/
def renderAnnotationValue : AnnotationValue → String
  | .iri v => renderIRI v
  | .anonymous _ loc => s!"_:{loc}"
  | .literal l => renderLiteral l

/-- Render an `AnnotationAxiom` in W3C Functional-Style Syntax. -/
def renderAnnotationAxiom : AnnotationAxiom → String
  | .assertion p s v =>
    s!"AnnotationAssertion({renderIRI p} {renderAnnotationSubject s} {renderAnnotationValue v})"
  | .subProperty sub sup =>
    s!"SubAnnotationPropertyOf({renderIRI sub} {renderIRI sup})"
  | .domain p dom =>
    s!"AnnotationPropertyDomain({renderIRI p} {renderIRI dom})"
  | .range p rng =>
    s!"AnnotationPropertyRange({renderIRI p} {renderIRI rng})"

/-- Render an `Ontology` as a complete W3C Functional-Style Syntax document. -/
def renderOntology (ont : Ontology) (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (imports : List IRI := []) : String :=
  let header := match ontIRI, verIRI with
    | some o, some v => s!" {renderIRI o} {renderIRI v}"
    | some o, none => s!" {renderIRI o}"
    | none, _ => ""
  let impLines := imports.map fun imp => s!"  Import({renderIRI imp})\n"
  let axLines := ont.map fun ax => s!"  {renderAxiom ax}\n"
  s!"Ontology({header}\n{"".intercalate impLines}{"".intercalate axLines})"

/-- Render a full W3C Functional-Style Syntax document including `Prefix(...)`
    declarations, `Declaration(...)` entity axioms, annotation axioms, and logical axioms. -/
def renderDocumentOFN (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology)
    (prefixes : PrefixMap := []) (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (imports : List IRI := []) : String :=
  let pfxLines := prefixes.map fun (p, ns) => s!"Prefix({p}:={renderIRI ns})\n"
  let header := match ontIRI, verIRI with
    | some o, some v => s!" {renderIRI o} {renderIRI v}"
    | some o, none => s!" {renderIRI o}"
    | none, _ => ""
  let impLines := imports.map fun imp => s!"  Import({renderIRI imp})\n"
  let declLines := decls.map fun d => s!"  {renderEntityDecl d}\n"
  let annotLines := annots.map fun a => s!"  {renderAnnotationAxiom a}\n"
  let axLines := ont.map fun ax => s!"  {renderAxiom ax}\n"
  s!"{"".intercalate pfxLines}Ontology({header}\n{"".intercalate impLines}{"".intercalate declLines}{"".intercalate annotLines}{"".intercalate axLines})\n"

/-- Explicit tag for every OWL 2 DL AST constructor in canonical S-expression form. -/
inductive ASTTag where
  | namedIndividual | anonymousIndividual
  | objectProperty | objectInverseOf
  | literal | facet
  | datatype | dataComplementOf | dataIntersectionOf | dataUnionOf | dataOneOf | datatypeRestriction
  | classIRI | objectComplementOf | objectIntersectionOf | objectUnionOf | objectOneOf
  | objectSomeValuesFrom | objectAllValuesFrom | objectHasValue | objectHasSelf
  | objectMinCardinality | objectMaxCardinality | objectExactCardinality
  | dataSomeValuesFrom | dataAllValuesFrom | dataHasValue
  | dataMinCardinality | dataMaxCardinality | dataExactCardinality
  | subClassOf | equivalentClasses | disjointClasses | disjointUnion
  | subObjectPropertyOf | subObjectPropertyChain | equivalentObjectProperties
  | disjointObjectProperties | inverseObjectProperties
  | objectPropertyDomain | objectPropertyRange
  | functionalObjectProperty | inverseFunctionalObjectProperty
  | reflexiveObjectProperty | irreflexiveObjectProperty
  | symmetricObjectProperty | asymmetricObjectProperty | transitiveObjectProperty
  | subDataPropertyOf | equivalentDataProperties | disjointDataProperties
  | dataPropertyDomain | dataPropertyRange | functionalDataProperty
  | datatypeDefinition | hasKey
  | sameIndividual | differentIndividuals
  | classAssertion | objectPropertyAssertion | negativeObjectPropertyAssertion
  | dataPropertyAssertion | negativeDataPropertyAssertion
  | ontology
  deriving DecidableEq, Repr, BEq

/-- Canonical structural S-expression representation for the full OWL 2 DL AST,
    providing total, proved-unambiguous structural encoding and decoding. -/
inductive SExpr where
  | tag (t : ASTTag)
  | atom (val : String)
  | nat (val : Nat)
  | list (items : List SExpr)
  deriving Repr, BEq

def encodeIRI (s : IRI) : SExpr := .atom s

def decodeIRI : SExpr → Option IRI
  | .atom s => some s
  | _ => none

theorem decodeIRI_encodeIRI (s : IRI) : decodeIRI (encodeIRI s) = some s := rfl

def encodeIndividual : Individual → SExpr
  | .named iri => .list [.tag .namedIndividual, .atom iri]
  | .anonymous doc loc => .list [.tag .anonymousIndividual, .atom doc, .atom loc]

def decodeIndividual : SExpr → Option Individual
  | .list [.tag .namedIndividual, .atom iri] => some (.named iri)
  | .list [.tag .anonymousIndividual, .atom doc, .atom loc] => some (.anonymous doc loc)
  | _ => none

theorem decodeIndividual_encodeIndividual (a : Individual) :
    decodeIndividual (encodeIndividual a) = some a := by
  cases a <;> rfl

def encodeObjectProperty : ObjectProperty → SExpr
  | .named iri => .list [.tag .objectProperty, .atom iri]
  | .inverse iri => .list [.tag .objectInverseOf, .atom iri]

def decodeObjectProperty : SExpr → Option ObjectProperty
  | .list [.tag .objectProperty, .atom iri] => some (.named iri)
  | .list [.tag .objectInverseOf, .atom iri] => some (.inverse iri)
  | _ => none

theorem decodeObjectProperty_encodeObjectProperty (r : ObjectProperty) :
    decodeObjectProperty (encodeObjectProperty r) = some r := by
  cases r <;> rfl

def encodeLiteral : Literal → SExpr
  | ⟨lex, dt⟩ => .list [.tag .literal, .atom lex, .atom dt]

def decodeLiteral : SExpr → Option Literal
  | .list [.tag .literal, .atom lex, .atom dt] => some ⟨lex, dt⟩
  | _ => none

theorem decodeLiteral_encodeLiteral (l : Literal) :
    decodeLiteral (encodeLiteral l) = some l := by
  cases l; rfl

def encodeFacet : Facet → SExpr
  | ⟨f, b⟩ => .list [.tag .facet, .atom f, encodeLiteral b]

def decodeFacet : SExpr → Option Facet
  | .list [.tag .facet, .atom f, b] => (decodeLiteral b).map (Facet.mk f)
  | _ => none

theorem decodeFacet_encodeFacet (f : Facet) :
    decodeFacet (encodeFacet f) = some f := by
  cases f; rfl

private theorem mapM_decode_encode {α : Type} (enc : α → SExpr) (dec : SExpr → Option α)
    (h : ∀ x, dec (enc x) = some x) (xs : List α) :
    (xs.map enc).mapM dec = some xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.mapM_cons, h x, Bind.bind, Option.bind, ih, pure]

def encodeDataRange : DataRange → SExpr
  | .datatype iri => .list [.tag .datatype, .atom iri]
  | .complement d => .list [.tag .dataComplementOf, encodeDataRange d]
  | .intersection a b => .list [.tag .dataIntersectionOf, encodeDataRange a, encodeDataRange b]
  | .union a b => .list [.tag .dataUnionOf, encodeDataRange a, encodeDataRange b]
  | .oneOf ls => .list [.tag .dataOneOf, .list (ls.map encodeLiteral)]
  | .restriction dt fs => .list [.tag .datatypeRestriction, .atom dt, .list (fs.map encodeFacet)]

def decodeDataRange : SExpr → Option DataRange
  | .list [.tag .datatype, .atom iri] => some (.datatype iri)
  | .list [.tag .dataComplementOf, d] => (decodeDataRange d).map .complement
  | .list [.tag .dataIntersectionOf, a, b] => do
    return .intersection (← decodeDataRange a) (← decodeDataRange b)
  | .list [.tag .dataUnionOf, a, b] => do
    return .union (← decodeDataRange a) (← decodeDataRange b)
  | .list [.tag .dataOneOf, .list ls] => (ls.mapM decodeLiteral).map .oneOf
  | .list [.tag .datatypeRestriction, .atom dt, .list fs] =>
    (fs.mapM decodeFacet).map (.restriction dt)
  | _ => none

theorem decodeDataRange_encodeDataRange (d : DataRange) :
    decodeDataRange (encodeDataRange d) = some d := by
  induction d with
  | datatype _ => rfl
  | complement d ih => simp [encodeDataRange, decodeDataRange, ih]
  | intersection a b iha ihb => simp [encodeDataRange, decodeDataRange, iha, ihb, Bind.bind, Option.bind, pure]
  | union a b iha ihb => simp [encodeDataRange, decodeDataRange, iha, ihb, Bind.bind, Option.bind, pure]
  | oneOf ls =>
    simp [encodeDataRange, decodeDataRange, mapM_decode_encode encodeLiteral decodeLiteral decodeLiteral_encodeLiteral]
  | restriction dt fs =>
    simp [encodeDataRange, decodeDataRange, mapM_decode_encode encodeFacet decodeFacet decodeFacet_encodeFacet]

def encodeClassExpr : ClassExpr → SExpr
  | .named iri => .list [.tag .classIRI, .atom iri]
  | .complement c => .list [.tag .objectComplementOf, encodeClassExpr c]
  | .intersection a b => .list [.tag .objectIntersectionOf, encodeClassExpr a, encodeClassExpr b]
  | .union a b => .list [.tag .objectUnionOf, encodeClassExpr a, encodeClassExpr b]
  | .oneOf inds => .list [.tag .objectOneOf, .list (inds.map encodeIndividual)]
  | .objectSome r c => .list [.tag .objectSomeValuesFrom, encodeObjectProperty r, encodeClassExpr c]
  | .objectAll r c => .list [.tag .objectAllValuesFrom, encodeObjectProperty r, encodeClassExpr c]
  | .objectValue r a => .list [.tag .objectHasValue, encodeObjectProperty r, encodeIndividual a]
  | .objectSelf r => .list [.tag .objectHasSelf, encodeObjectProperty r]
  | .objectMin n r c => .list [.tag .objectMinCardinality, .nat n, encodeObjectProperty r, encodeClassExpr c]
  | .objectMax n r c => .list [.tag .objectMaxCardinality, .nat n, encodeObjectProperty r, encodeClassExpr c]
  | .objectExact n r c => .list [.tag .objectExactCardinality, .nat n, encodeObjectProperty r, encodeClassExpr c]
  | .dataSome dp d => .list [.tag .dataSomeValuesFrom, .atom dp, encodeDataRange d]
  | .dataAll dp d => .list [.tag .dataAllValuesFrom, .atom dp, encodeDataRange d]
  | .dataValue dp l => .list [.tag .dataHasValue, .atom dp, encodeLiteral l]
  | .dataMin n dp d => .list [.tag .dataMinCardinality, .nat n, .atom dp, encodeDataRange d]
  | .dataMax n dp d => .list [.tag .dataMaxCardinality, .nat n, .atom dp, encodeDataRange d]
  | .dataExact n dp d => .list [.tag .dataExactCardinality, .nat n, .atom dp, encodeDataRange d]

def decodeClassExpr : SExpr → Option ClassExpr
  | .list [.tag .classIRI, .atom iri] => some (.named iri)
  | .list [.tag .objectComplementOf, c] => (decodeClassExpr c).map .complement
  | .list [.tag .objectIntersectionOf, a, b] => do
    return .intersection (← decodeClassExpr a) (← decodeClassExpr b)
  | .list [.tag .objectUnionOf, a, b] => do
    return .union (← decodeClassExpr a) (← decodeClassExpr b)
  | .list [.tag .objectOneOf, .list inds] => (inds.mapM decodeIndividual).map .oneOf
  | .list [.tag .objectSomeValuesFrom, r, c] => do
    return .objectSome (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .objectAllValuesFrom, r, c] => do
    return .objectAll (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .objectHasValue, r, a] => do
    return .objectValue (← decodeObjectProperty r) (← decodeIndividual a)
  | .list [.tag .objectHasSelf, r] => (decodeObjectProperty r).map .objectSelf
  | .list [.tag .objectMinCardinality, .nat n, r, c] => do
    return .objectMin n (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .objectMaxCardinality, .nat n, r, c] => do
    return .objectMax n (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .objectExactCardinality, .nat n, r, c] => do
    return .objectExact n (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .dataSomeValuesFrom, .atom dp, d] => (decodeDataRange d).map (.dataSome dp)
  | .list [.tag .dataAllValuesFrom, .atom dp, d] => (decodeDataRange d).map (.dataAll dp)
  | .list [.tag .dataHasValue, .atom dp, l] => (decodeLiteral l).map (.dataValue dp)
  | .list [.tag .dataMinCardinality, .nat n, .atom dp, d] => (decodeDataRange d).map (.dataMin n dp)
  | .list [.tag .dataMaxCardinality, .nat n, .atom dp, d] => (decodeDataRange d).map (.dataMax n dp)
  | .list [.tag .dataExactCardinality, .nat n, .atom dp, d] => (decodeDataRange d).map (.dataExact n dp)
  | _ => none

theorem decodeClassExpr_encodeClassExpr (c : ClassExpr) :
    decodeClassExpr (encodeClassExpr c) = some c := by
  induction c with
  | named _ => rfl
  | complement c ih => simp [encodeClassExpr, decodeClassExpr, ih]
  | intersection a b iha ihb => simp [encodeClassExpr, decodeClassExpr, iha, ihb, Bind.bind, Option.bind, pure]
  | union a b iha ihb => simp [encodeClassExpr, decodeClassExpr, iha, ihb, Bind.bind, Option.bind, pure]
  | oneOf inds =>
    simp [encodeClassExpr, decodeClassExpr, mapM_decode_encode encodeIndividual decodeIndividual decodeIndividual_encodeIndividual]
  | objectSome r c ih =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, ih, Bind.bind, Option.bind, pure]
  | objectAll r c ih =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, ih, Bind.bind, Option.bind, pure]
  | objectValue r a =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, decodeIndividual_encodeIndividual, Bind.bind, Option.bind, pure]
  | objectSelf r =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty]
  | objectMin n r c ih =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, ih, Bind.bind, Option.bind, pure]
  | objectMax n r c ih =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, ih, Bind.bind, Option.bind, pure]
  | objectExact n r c ih =>
    simp [encodeClassExpr, decodeClassExpr, decodeObjectProperty_encodeObjectProperty, ih, Bind.bind, Option.bind, pure]
  | dataSome dp d => simp [encodeClassExpr, decodeClassExpr, decodeDataRange_encodeDataRange]
  | dataAll dp d => simp [encodeClassExpr, decodeClassExpr, decodeDataRange_encodeDataRange]
  | dataValue dp l => simp [encodeClassExpr, decodeClassExpr, decodeLiteral_encodeLiteral]
  | dataMin n dp d => simp [encodeClassExpr, decodeClassExpr, decodeDataRange_encodeDataRange]
  | dataMax n dp d => simp [encodeClassExpr, decodeClassExpr, decodeDataRange_encodeDataRange]
  | dataExact n dp d => simp [encodeClassExpr, decodeClassExpr, decodeDataRange_encodeDataRange]

def encodeAxiom : Axiom → SExpr
  | .subClassOf a b => .list [.tag .subClassOf, encodeClassExpr a, encodeClassExpr b]
  | .equivalentClasses cs => .list [.tag .equivalentClasses, .list (cs.map encodeClassExpr)]
  | .disjointClasses cs => .list [.tag .disjointClasses, .list (cs.map encodeClassExpr)]
  | .disjointUnion h cs => .list [.tag .disjointUnion, .atom h, .list (cs.map encodeClassExpr)]
  | .subObjectProperty r s => .list [.tag .subObjectPropertyOf, encodeObjectProperty r, encodeObjectProperty s]
  | .subObjectPropertyChain rs s => .list [.tag .subObjectPropertyChain, .list (rs.map encodeObjectProperty), encodeObjectProperty s]
  | .equivalentObjectProperties rs => .list [.tag .equivalentObjectProperties, .list (rs.map encodeObjectProperty)]
  | .disjointObjectProperties rs => .list [.tag .disjointObjectProperties, .list (rs.map encodeObjectProperty)]
  | .inverseObjectProperties r s => .list [.tag .inverseObjectProperties, encodeObjectProperty r, encodeObjectProperty s]
  | .objectPropertyDomain r c => .list [.tag .objectPropertyDomain, encodeObjectProperty r, encodeClassExpr c]
  | .objectPropertyRange r c => .list [.tag .objectPropertyRange, encodeObjectProperty r, encodeClassExpr c]
  | .functionalObjectProperty r => .list [.tag .functionalObjectProperty, encodeObjectProperty r]
  | .inverseFunctionalObjectProperty r => .list [.tag .inverseFunctionalObjectProperty, encodeObjectProperty r]
  | .reflexiveObjectProperty r => .list [.tag .reflexiveObjectProperty, encodeObjectProperty r]
  | .irreflexiveObjectProperty r => .list [.tag .irreflexiveObjectProperty, encodeObjectProperty r]
  | .symmetricObjectProperty r => .list [.tag .symmetricObjectProperty, encodeObjectProperty r]
  | .asymmetricObjectProperty r => .list [.tag .asymmetricObjectProperty, encodeObjectProperty r]
  | .transitiveObjectProperty r => .list [.tag .transitiveObjectProperty, encodeObjectProperty r]
  | .subDataProperty r s => .list [.tag .subDataPropertyOf, .atom r, .atom s]
  | .equivalentDataProperties ds => .list [.tag .equivalentDataProperties, .list (ds.map encodeIRI)]
  | .disjointDataProperties ds => .list [.tag .disjointDataProperties, .list (ds.map encodeIRI)]
  | .dataPropertyDomain dp c => .list [.tag .dataPropertyDomain, .atom dp, encodeClassExpr c]
  | .dataPropertyRange dp d => .list [.tag .dataPropertyRange, .atom dp, encodeDataRange d]
  | .functionalDataProperty dp => .list [.tag .functionalDataProperty, .atom dp]
  | .datatypeDefinition dt d => .list [.tag .datatypeDefinition, .atom dt, encodeDataRange d]
  | .hasKey c os ds => .list [.tag .hasKey, encodeClassExpr c, .list (os.map encodeObjectProperty), .list (ds.map encodeIRI)]
  | .sameIndividuals inds => .list [.tag .sameIndividual, .list (inds.map encodeIndividual)]
  | .differentIndividuals inds => .list [.tag .differentIndividuals, .list (inds.map encodeIndividual)]
  | .classAssertion c a => .list [.tag .classAssertion, encodeClassExpr c, encodeIndividual a]
  | .objectAssertion r a b => .list [.tag .objectPropertyAssertion, encodeObjectProperty r, encodeIndividual a, encodeIndividual b]
  | .negativeObjectAssertion r a b => .list [.tag .negativeObjectPropertyAssertion, encodeObjectProperty r, encodeIndividual a, encodeIndividual b]
  | .dataAssertion dp a l => .list [.tag .dataPropertyAssertion, .atom dp, encodeIndividual a, encodeLiteral l]
  | .negativeDataAssertion dp a l => .list [.tag .negativeDataPropertyAssertion, .atom dp, encodeIndividual a, encodeLiteral l]

def decodeAxiom : SExpr → Option Axiom
  | .list [.tag .subClassOf, a, b] => do
    return .subClassOf (← decodeClassExpr a) (← decodeClassExpr b)
  | .list [.tag .equivalentClasses, .list cs] => (cs.mapM decodeClassExpr).map .equivalentClasses
  | .list [.tag .disjointClasses, .list cs] => (cs.mapM decodeClassExpr).map .disjointClasses
  | .list [.tag .disjointUnion, .atom h, .list cs] => (cs.mapM decodeClassExpr).map (.disjointUnion h)
  | .list [.tag .subObjectPropertyOf, r, s] => do
    return .subObjectProperty (← decodeObjectProperty r) (← decodeObjectProperty s)
  | .list [.tag .subObjectPropertyChain, .list rs, s] => do
    return .subObjectPropertyChain (← rs.mapM decodeObjectProperty) (← decodeObjectProperty s)
  | .list [.tag .equivalentObjectProperties, .list rs] =>
    (rs.mapM decodeObjectProperty).map .equivalentObjectProperties
  | .list [.tag .disjointObjectProperties, .list rs] =>
    (rs.mapM decodeObjectProperty).map .disjointObjectProperties
  | .list [.tag .inverseObjectProperties, r, s] => do
    return .inverseObjectProperties (← decodeObjectProperty r) (← decodeObjectProperty s)
  | .list [.tag .objectPropertyDomain, r, c] => do
    return .objectPropertyDomain (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .objectPropertyRange, r, c] => do
    return .objectPropertyRange (← decodeObjectProperty r) (← decodeClassExpr c)
  | .list [.tag .functionalObjectProperty, r] => (decodeObjectProperty r).map .functionalObjectProperty
  | .list [.tag .inverseFunctionalObjectProperty, r] => (decodeObjectProperty r).map .inverseFunctionalObjectProperty
  | .list [.tag .reflexiveObjectProperty, r] => (decodeObjectProperty r).map .reflexiveObjectProperty
  | .list [.tag .irreflexiveObjectProperty, r] => (decodeObjectProperty r).map .irreflexiveObjectProperty
  | .list [.tag .symmetricObjectProperty, r] => (decodeObjectProperty r).map .symmetricObjectProperty
  | .list [.tag .asymmetricObjectProperty, r] => (decodeObjectProperty r).map .asymmetricObjectProperty
  | .list [.tag .transitiveObjectProperty, r] => (decodeObjectProperty r).map .transitiveObjectProperty
  | .list [.tag .subDataPropertyOf, .atom r, .atom s] => some (.subDataProperty r s)
  | .list [.tag .equivalentDataProperties, .list ds] => (ds.mapM decodeIRI).map .equivalentDataProperties
  | .list [.tag .disjointDataProperties, .list ds] => (ds.mapM decodeIRI).map .disjointDataProperties
  | .list [.tag .dataPropertyDomain, .atom dp, c] => (decodeClassExpr c).map (.dataPropertyDomain dp)
  | .list [.tag .dataPropertyRange, .atom dp, d] => (decodeDataRange d).map (.dataPropertyRange dp)
  | .list [.tag .functionalDataProperty, .atom dp] => some (.functionalDataProperty dp)
  | .list [.tag .datatypeDefinition, .atom dt, d] => (decodeDataRange d).map (.datatypeDefinition dt)
  | .list [.tag .hasKey, c, .list os, .list ds] => do
    return .hasKey (← decodeClassExpr c) (← os.mapM decodeObjectProperty) (← ds.mapM decodeIRI)
  | .list [.tag .sameIndividual, .list inds] => (inds.mapM decodeIndividual).map .sameIndividuals
  | .list [.tag .differentIndividuals, .list inds] => (inds.mapM decodeIndividual).map .differentIndividuals
  | .list [.tag .classAssertion, c, a] => do
    return .classAssertion (← decodeClassExpr c) (← decodeIndividual a)
  | .list [.tag .objectPropertyAssertion, r, a, b] => do
    return .objectAssertion (← decodeObjectProperty r) (← decodeIndividual a) (← decodeIndividual b)
  | .list [.tag .negativeObjectPropertyAssertion, r, a, b] => do
    return .negativeObjectAssertion (← decodeObjectProperty r) (← decodeIndividual a) (← decodeIndividual b)
  | .list [.tag .dataPropertyAssertion, .atom dp, a, l] => do
    return .dataAssertion dp (← decodeIndividual a) (← decodeLiteral l)
  | .list [.tag .negativeDataPropertyAssertion, .atom dp, a, l] => do
    return .negativeDataAssertion dp (← decodeIndividual a) (← decodeLiteral l)
  | _ => none

theorem decodeAxiom_encodeAxiom (ax : Axiom) :
    decodeAxiom (encodeAxiom ax) = some ax := by
  cases ax <;> simp [encodeAxiom, decodeAxiom,
    decodeClassExpr_encodeClassExpr, decodeDataRange_encodeDataRange,
    decodeObjectProperty_encodeObjectProperty, decodeIndividual_encodeIndividual,
    decodeLiteral_encodeLiteral,
    mapM_decode_encode encodeClassExpr decodeClassExpr decodeClassExpr_encodeClassExpr,
    mapM_decode_encode encodeObjectProperty decodeObjectProperty decodeObjectProperty_encodeObjectProperty,
    mapM_decode_encode encodeIndividual decodeIndividual decodeIndividual_encodeIndividual,
    mapM_decode_encode encodeIRI decodeIRI decodeIRI_encodeIRI,
    Bind.bind, Option.bind, pure]

def encodeOntology (o : Ontology) : SExpr :=
  .list [.tag .ontology, .list (o.map encodeAxiom)]

def decodeOntology : SExpr → Option Ontology
  | .list [.tag .ontology, .list axs] => axs.mapM decodeAxiom
  | _ => none

theorem decodeOntology_encodeOntology (o : Ontology) :
    decodeOntology (encodeOntology o) = some o := by
  simp [encodeOntology, decodeOntology, mapM_decode_encode encodeAxiom decodeAxiom decodeAxiom_encodeAxiom]

theorem encodeAxiom_injective (a1 a2 : Axiom) :
    encodeAxiom a1 = encodeAxiom a2 ↔ a1 = a2 :=
  ⟨fun h => Option.some.inj ((decodeAxiom_encodeAxiom a1).symm.trans (h ▸ decodeAxiom_encodeAxiom a2)),
   fun h => h ▸ rfl⟩

theorem encodeOntology_injective (o1 o2 : Ontology) :
    encodeOntology o1 = encodeOntology o2 ↔ o1 = o2 :=
  ⟨fun h => Option.some.inj ((decodeOntology_encodeOntology o1).symm.trans (h ▸ decodeOntology_encodeOntology o2)),
   fun h => h ▸ rfl⟩

end Sabrina.OWL2.FunctionalSyntax
