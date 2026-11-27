import Sabrina.OWL2.RDF.Graph

/-! Native Lean 4 W3C RDF/XML 1.1 parser (`parseRDFXML`).

Supports:
- XML 1.0 prolog (`<?xml ...?>`), `<!DOCTYPE ...>` internal `<!ENTITY name "val">`
  definitions, comments (`<!-- ... -->`), processing instructions, `<![CDATA[...]]>`,
  named/numeric XML character references (`&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`,
  `&#dec;`, `&#xhex;`, and custom DOCTYPE entities).
- Full XML Namespaces (`xmlns`, `xmlns:prefix`), `xml:base` inheritance, `xml:lang`
  inheritance, and RFC 3986 relative IRI resolution.
- W3C RDF/XML node elements (`rdf:Description` and typed node elements), `rdf:about`,
  `rdf:ID`, `rdf:nodeID`, property attributes, property elements with `rdf:resource`,
  `rdf:nodeID`, `rdf:datatype`, `rdf:parseType="Resource"|"Collection"|"Literal"`,
  nested node elements, and plain/typed/language-tagged literal text. -/

namespace Sabrina.OWL2.RDF.XML

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.RDF

private structure XMLAttr where
  name : String
  value : String
  deriving Repr

private inductive XMLNode where
  | elem (tag : String) (attrs : List XMLAttr) (children : List XMLNode)
  | text (content : String)
  deriving Repr, Inhabited

private structure XmlState where
  chars : Array Char
  pos : Nat := 0
  entities : List (String × String) := []

private abbrev XmlP (α : Type) := StateT XmlState (Except String) α

private def peekChar : XmlP (Option Char) := do
  let st ← get
  return st.chars[st.pos]?

private def nextChar : XmlP Char := do
  let st ← get
  match st.chars[st.pos]? with
  | some c =>
    set { st with pos := st.pos + 1 }
    return c
  | none => throw "unexpected end of XML input"

private def startsWithStr (s : String) : XmlP Bool := do
  let st ← get
  let target := s.toList
  let mut idx := st.pos
  for c in target do
    match st.chars[idx]? with
    | some ch => if ch != c then return false
    | none => return false
    idx := idx + 1
  return true

private def consumeStr (s : String) : XmlP Unit := do
  if !(← startsWithStr s) then
    throw s!"expected '{s}' in XML"
  modify fun st => { st with pos := st.pos + s.toList.length }

private def skipWS : XmlP Unit := do
  while true do
    match ← peekChar with
    | some c =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
        let _ ← nextChar
      else break
    | none => break

private def parseHexNat (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (acc * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (acc * 16 + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c && c ≤ 'F' then some (acc * 16 + (c.toNat - 'A'.toNat + 10))
    else none) 0

private def parseDecNat (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (acc * 10 + (c.toNat - '0'.toNat))
    else none) 0

private def decodeEntity (entities : List (String × String)) (name : String) : Except String String :=
  match name with
  | "amp" => .ok "&"
  | "lt" => .ok "<"
  | "gt" => .ok ">"
  | "quot" => .ok "\""
  | "apos" => .ok "'"
  | _ =>
    if name.startsWith "#x" || name.startsWith "#X" then
      match parseHexNat (name.toList.drop 2) with
      | some n => .ok (String.singleton (Char.ofNat n))
      | none => .error s!"invalid hex character reference '&{name};'"
    else if name.startsWith "#" then
      match parseDecNat (name.toList.drop 1) with
      | some n => .ok (String.singleton (Char.ofNat n))
      | none => .error s!"invalid decimal character reference '&{name};'"
    else
      match entities.find? (fun (k, _) => k == name) with
      | some (_, v) => .ok v
      | none => .error s!"unknown XML entity '&{name};'"

private def unescapeEntities (entities : List (String × String)) (s : String) : Except String String := do
  let cs := s.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : List Char := []
  while i < n do
    let c := cs[i]!
    if c == '&' then
      let mut j := i + 1
      let mut nameBuf : List Char := []
      while j < n && cs[j]! != ';' do
        nameBuf := cs[j]! :: nameBuf
        j := j + 1
      if j >= n then throw "unterminated XML entity reference"
      let expanded ← decodeEntity entities (String.ofList nameBuf.reverse)
      for ch in expanded.toList do
        out := ch :: out
      i := j + 1
    else
      out := c :: out
      i := i + 1
  return String.ofList out.reverse

private def isXmlNameChar (c : Char) : Bool :=
  c.isAlphanum || c == ':' || c == '_' || c == '-' || c == '.' || c.toNat ≥ 0x80

private def parseName : XmlP String := do
  let mut buf : List Char := []
  while true do
    match ← peekChar with
    | some c =>
      if isXmlNameChar c then
        buf := (← nextChar) :: buf
      else break
    | none => break
  if buf.isEmpty then throw "expected XML name"
  return String.ofList buf.reverse

private def parseQuotedRaw : XmlP String := do
  let q ← nextChar
  if q != '"' && q != '\'' then throw s!"expected quoted XML string, got '{q}'"
  let mut buf : List Char := []
  while true do
    let c ← nextChar
    if c == q then break
    buf := c :: buf
  return String.ofList buf.reverse

private def skipComment : XmlP Unit := do
  consumeStr "<!--"
  while true do
    if ← startsWithStr "-->" then
      consumeStr "-->"
      return
    let _ ← nextChar

private def skipPI : XmlP Unit := do
  consumeStr "<?"
  while true do
    if ← startsWithStr "?>" then
      consumeStr "?>"
      return
    let _ ← nextChar

private def parseDoctype : XmlP Unit := do
  consumeStr "<!DOCTYPE"
  while true do
    skipWS
    if ← startsWithStr "[" then
      let _ ← nextChar
      while true do
        skipWS
        if ← startsWithStr "]" then
          let _ ← nextChar
          break
        else if ← startsWithStr "<!--" then
          skipComment
        else if ← startsWithStr "<!ENTITY" then
          consumeStr "<!ENTITY"
          skipWS
          -- Skip parameter entities (% ...)
          if (← peekChar) == some '%' then
            let _ ← nextChar; skipWS
            let _ ← parseName; skipWS
            let _ ← parseQuotedRaw; skipWS
            consumeStr ">"
          else
            let entName ← parseName
            skipWS
            let rawVal ← parseQuotedRaw
            let ents := (← get).entities
            let val ← match unescapeEntities ents rawVal with
              | .ok v => pure v
              | .error e => throw e
            skipWS
            consumeStr ">"
            modify fun st => { st with entities := (entName, val) :: st.entities }
        else if ← startsWithStr "<!" then
          while (← nextChar) != '>' do pure ()
        else
          let _ ← nextChar
    else if ← startsWithStr ">" then
      let _ ← nextChar
      return
    else
      let _ ← nextChar

private def skipProlog : XmlP Unit := do
  while true do
    skipWS
    if ← startsWithStr "<?" then skipPI
    else if ← startsWithStr "<!--" then skipComment
    else if ← startsWithStr "<!DOCTYPE" then parseDoctype
    else break

private def parseAttrs : XmlP (List XMLAttr) := do
  let mut attrs : List XMLAttr := []
  while true do
    skipWS
    match ← peekChar with
    | none | some '>' | some '/' => break
    | some _ =>
      let name ← parseName
      skipWS
      consumeStr "="
      skipWS
      let rawVal ← parseQuotedRaw
      let ents := (← get).entities
      let val ← match unescapeEntities ents rawVal with
        | .ok v => pure v
        | .error e => throw e
      attrs := ⟨name, val⟩ :: attrs
  return attrs.reverse

private def parseCDATA : XmlP String := do
  consumeStr "<![CDATA["
  let mut buf : List Char := []
  while true do
    if ← startsWithStr "]]>" then
      consumeStr "]]>"
      return String.ofList buf.reverse
    buf := (← nextChar) :: buf
  return String.ofList buf.reverse

private partial def parseElement : XmlP XMLNode := do
  consumeStr "<"
  let tag ← parseName
  let attrs ← parseAttrs
  skipWS
  if ← startsWithStr "/>" then
    consumeStr "/>"
    return .elem tag attrs []
  consumeStr ">"
  let mut children : List XMLNode := []
  while true do
    if ← startsWithStr "</" then
      consumeStr "</"
      let closeTag ← parseName
      skipWS
      consumeStr ">"
      if closeTag != tag then
        throw s!"mismatched XML closing tag: expected </{tag}>, got </{closeTag}>"
      return .elem tag attrs children.reverse
    else if ← startsWithStr "<!--" then
      skipComment
    else if ← startsWithStr "<?" then
      skipPI
    else if ← startsWithStr "<![CDATA[" then
      let txt ← parseCDATA
      children := .text txt :: children
    else if ← startsWithStr "<" then
      let child ← parseElement
      children := child :: children
    else
      let mut buf : List Char := []
      while true do
        match ← peekChar with
        | none | some '<' => break
        | some _ => buf := (← nextChar) :: buf
      if buf.isEmpty then throw s!"unterminated XML element <{tag}>"
      let ents := (← get).entities
      let txt ← match unescapeEntities ents (String.ofList buf.reverse) with
        | .ok v => pure v
        | .error e => throw e
      children := .text txt :: children
  return .elem tag attrs children.reverse

private def parseXMLDocument (input : String) : Except String XMLNode := do
  -- Strip optional UTF-8 BOM
  let cleaned := if input.startsWith "\uFEFF" then String.ofList (input.toList.drop 1) else input
  let (root, _) ← (do
    skipProlog
    let root ← parseElement
    skipProlog
    return root).run { chars := cleaned.toList.toArray }
  return root

/-! ### RDF/XML Tree-to-Triples Interpreter -/

private structure RdfXmlCtx where
  nsMap : PrefixMap := [
    ("rdf", rdfNS),
    ("rdfs", rdfsNS),
    ("owl", owlNS),
    ("xsd", xsdNS),
    ("xml", "http://www.w3.org/XML/1998/namespace")
  ]
  defaultNS : Option IRI := none
  baseIRI : Option IRI := none
  lang : Option String := none

private structure EmitState where
  triples : List RDFTriple := []
  nextBNode : Nat := 0
  prefixes : PrefixMap := []
  rootBase : Option IRI := none

private abbrev EmitM (α : Type) := StateT EmitState (Except String) α

private def freshBNode : EmitM RDFTerm := do
  let st ← get
  set { st with nextBNode := st.nextBNode + 1 }
  return .bnode s!"rdfxml_b{st.nextBNode}"

private def emit (s : RDFTerm) (p : IRI) (o : RDFTerm) : EmitM Unit :=
  modify fun st => { st with triples := ⟨s, p, o⟩ :: st.triples }

private def updateCtx (ctx : RdfXmlCtx) (attrs : List XMLAttr) : EmitM RdfXmlCtx := do
  let mut nsMap := ctx.nsMap
  let mut defaultNS := ctx.defaultNS
  let mut baseIRI := ctx.baseIRI
  let mut lang := ctx.lang
  for a in attrs do
    if a.name == "xmlns" then
      defaultNS := if a.value.isEmpty then none else some a.value
      modify fun st => { st with prefixes := ("", a.value) :: st.prefixes }
    else if a.name.startsWith "xmlns:" then
      let pfx := String.ofList (a.name.toList.drop 6)
      nsMap := (pfx, a.value) :: nsMap
      modify fun st => { st with prefixes := (pfx, a.value) :: st.prefixes }
    else if a.name == "xml:base" then
      let resolved := resolveIRI baseIRI a.value
      baseIRI := some resolved
      let st ← get
      if st.rootBase.isNone then
        set { st with rootBase := some resolved }
    else if a.name == "xml:lang" then
      lang := if a.value.isEmpty then none else some a.value
  return { nsMap, defaultNS, baseIRI, lang }

private def expandQName (ctx : RdfXmlCtx) (isAttr : Bool) (qname : String) : Except String IRI :=
  match qname.splitOn ":" with
  | [localName] =>
    if isAttr then
      -- Unprefixed attributes are not in the default namespace per XML Namespaces,
      -- except legacy unqualified RDF attributes if ever encountered.
      match ctx.defaultNS with
      | some ns => .ok (ns ++ localName)
      | none => .ok localName
    else
      match ctx.defaultNS with
      | some ns => .ok (ns ++ localName)
      | none => .error s!"unprefixed XML element <{qname}> without default xmlns"
  | [pfx, localName] =>
    match ctx.nsMap.find? (fun (k, _) => k == pfx) with
    | some (_, ns) => .ok (ns ++ localName)
    | none => .error s!"undeclared XML namespace prefix '{pfx}' in '{qname}'"
  | _ => .error s!"malformed XML qualified name '{qname}'"

private def isControlAttr (name : String) : Bool :=
  name == "xmlns" || name.startsWith "xmlns:" || name.startsWith "xml:"

private def findExpandedAttr (ctx : RdfXmlCtx) (attrs : List XMLAttr) (target : IRI) : Option String :=
  attrs.findSome? fun a =>
    if isControlAttr a.name then none
    else match expandQName ctx true a.name with
      | .ok iri => if iri == target then some a.value else none
      | .error _ => none

private def isRDFSyntaxAttr (iri : IRI) : Bool :=
  iri == rdfNS ++ "about" || iri == rdfNS ++ "ID" || iri == rdfNS ++ "nodeID" ||
  iri == rdfNS ++ "resource" || iri == rdfNS ++ "parseType" || iri == rdfNS ++ "datatype"

private def xmlEscapeText (s : String) : String :=
  s.toList.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | _ => acc.push c) ""

private def xmlEscapeAttr (s : String) : String :=
  s.toList.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | _ => acc.push c) ""

private partial def serializeXMLNode : XMLNode → String
  | .text s => xmlEscapeText s
  | .elem tag attrs children =>
    let attrStr := attrs.foldl (fun acc a => s!"{acc} {a.name}=\"{xmlEscapeAttr a.value}\"") ""
    let inner := "".intercalate (children.map serializeXMLNode)
    s!"<{tag}{attrStr}>{inner}</{tag}>"

private def isWhitespaceText : XMLNode → Bool
  | .text s => s.toList.all (·.isWhitespace)
  | .elem _ _ _ => false

private def collectText (children : List XMLNode) : Except String String := do
  let mut parts : List String := []
  for ch in children do
    match ch with
    | .text s => parts := s :: parts
    | .elem t _ _ => throw s!"unexpected nested element <{t}> inside literal property element"
  return "".intercalate parts.reverse

private def makeLiteralTerm (lex : String) (dt? : Option IRI) (lang? : Option String) : RDFTerm :=
  match dt? with
  | some dt => .literal lex dt none
  | none =>
    match lang? with
    | some l => .literal lex rdfLangString (some l)
    | none => .literal lex xsdString none

mutual

private partial def parsePropertyAttrs (ctx : RdfXmlCtx) (subj : RDFTerm) (attrs : List XMLAttr) : EmitM Unit := do
  for a in attrs do
    if isControlAttr a.name then continue
    let iri ← match expandQName ctx true a.name with
      | .ok i => pure i
      | .error e => throw e
    if isRDFSyntaxAttr iri then continue
    if iri == rdfType then
      emit subj rdfType (.iri (resolveIRI ctx.baseIRI a.value))
    else
      emit subj iri (makeLiteralTerm a.value none ctx.lang)

private partial def parseNodeElement (parentCtx : RdfXmlCtx) (node : XMLNode) : EmitM RDFTerm := do
  let .elem tag attrs children := node | throw "expected XML element for RDF node"
  let ctx ← updateCtx parentCtx attrs
  let tagIRI ← match expandQName ctx false tag with
    | .ok i => pure i
    | .error e => throw e
  let about? := findExpandedAttr ctx attrs (rdfNS ++ "about")
  let id? := findExpandedAttr ctx attrs (rdfNS ++ "ID")
  let nodeId? := findExpandedAttr ctx attrs (rdfNS ++ "nodeID")
  let subj : RDFTerm ← match about?, id?, nodeId? with
    | some a, none, none => pure (.iri (resolveIRI ctx.baseIRI a))
    | none, some i, none => pure (.iri (resolveIRI ctx.baseIRI ("#" ++ i)))
    | none, none, some nid => pure (.bnode nid)
    | none, none, none => freshBNode
    | _, _, _ => throw s!"RDF/XML node element <{tag}> has conflicting rdf:about / rdf:ID / rdf:nodeID attributes"
  if tagIRI != rdfNS ++ "Description" then
    emit subj rdfType (.iri tagIRI)
  parsePropertyAttrs ctx subj attrs
  for ch in children do
    if isWhitespaceText ch then continue
    parsePropertyElement ctx subj ch
  return subj

private partial def parsePropertyElement (parentCtx : RdfXmlCtx) (subj : RDFTerm) (node : XMLNode) : EmitM Unit := do
  let .elem tag attrs children := node | throw "expected XML element for RDF property"
  let ctx ← updateCtx parentCtx attrs
  let predIRI ← match expandQName ctx false tag with
    | .ok i => pure i
    | .error e => throw e
  let resource? := findExpandedAttr ctx attrs (rdfNS ++ "resource")
  let nodeId? := findExpandedAttr ctx attrs (rdfNS ++ "nodeID")
  let parseType? := findExpandedAttr ctx attrs (rdfNS ++ "parseType")
  let datatype? := findExpandedAttr ctx attrs (rdfNS ++ "datatype")
  let elemChildren := children.filter fun
    | .elem _ _ _ => true
    | .text _ => false
  let nonWsChildren := children.filter fun c => !isWhitespaceText c
  -- Check if there are extra property attributes on this property element
  let mut hasExtraPropAttrs := false
  for a in attrs do
    if isControlAttr a.name then continue
    if let .ok i := expandQName ctx true a.name then
      if !isRDFSyntaxAttr i then hasExtraPropAttrs := true
  match parseType? with
  | some "Resource" =>
    let b ← freshBNode
    emit subj predIRI b
    for ch in nonWsChildren do
      parsePropertyElement ctx b ch
  | some "Collection" =>
    let mut items : List RDFTerm := []
    for ch in elemChildren do
      let item ← parseNodeElement ctx ch
      items := item :: items
    let ordered := items.reverse
    let rec buildList : List RDFTerm → EmitM RDFTerm
      | [] => pure (.iri rdfNil)
      | x :: xs => do
        let cell ← freshBNode
        let rest ← buildList xs
        emit cell rdfFirst x
        emit cell rdfRest rest
        return cell
    let head ← buildList ordered
    emit subj predIRI head
  | some "Literal" =>
    let xmlStr := "".intercalate (children.map serializeXMLNode)
    emit subj predIRI (.literal xmlStr rdfXMLLiteral none)
  | some other =>
    throw s!"unsupported rdf:parseType='{other}'"
  | none =>
    match resource?, nodeId? with
    | some r, none =>
      let obj := RDFTerm.iri (resolveIRI ctx.baseIRI r)
      emit subj predIRI obj
      if hasExtraPropAttrs then parsePropertyAttrs ctx obj attrs
    | none, some nid =>
      let obj := RDFTerm.bnode nid
      emit subj predIRI obj
      if hasExtraPropAttrs then parsePropertyAttrs ctx obj attrs
    | some _, some _ =>
      throw s!"property element <{tag}> cannot have both rdf:resource and rdf:nodeID"
    | none, none =>
      if hasExtraPropAttrs && nonWsChildren.isEmpty then
        let obj ← freshBNode
        emit subj predIRI obj
        parsePropertyAttrs ctx obj attrs
      else if !elemChildren.isEmpty then
        if elemChildren.length != 1 then
          throw s!"property element <{tag}> must have at most one child node element"
        let obj ← parseNodeElement ctx elemChildren.head!
        emit subj predIRI obj
      else
        let lex ← match collectText children with
          | .ok s => pure s
          | .error e => throw e
        let dtOpt := datatype?.map (resolveIRI ctx.baseIRI)
        emit subj predIRI (makeLiteralTerm lex dtOpt ctx.lang)

end

/-- Parse a W3C RDF/XML document into an `RDFGraph`. -/
def parseRDFXML (input : String) : Except String RDFGraph := do
  let root ← parseXMLDocument input
  let .elem tag attrs children := root | throw "RDF/XML root must be an XML element"
  let ((), st) ← (do
    let baseCtx : RdfXmlCtx := {}
    let ctx ← updateCtx baseCtx attrs
    let tagIRI ← match expandQName ctx false tag with
      | .ok i => pure i
      | .error e => throw e
    if tagIRI == rdfNS ++ "RDF" then
      for ch in children do
        if isWhitespaceText ch then continue
        let _ ← parseNodeElement ctx ch
    else
      let _ ← parseNodeElement baseCtx root).run {}
  return {
    triples := st.triples.reverse
    prefixes := st.prefixes.reverse
    baseIRI := st.rootBase
  }

end Sabrina.OWL2.RDF.XML
