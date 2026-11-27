import Std.Data.HashMap
import Sabrina.OWL2.RDF.Graph

/-! Native Lean 4 W3C Turtle 1.1 (`renderTurtle`) and RDF/XML 1.1 (`renderRDFXML`)
    serializers for `Sabrina.OWL2.RDF.RDFGraph`.

    Used together with `Sabrina.OWL2.RDF.OWLMapping.encodeOntologyRDF` to export
    materialized OWL 2 DL ontologies as `.ttl` and `.owl` (RDF/XML) files that
    round-trip cleanly through both SABRINA's native parsers and external OWL 2 tools. -/

namespace Sabrina.OWL2.RDF.Serialize

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.RDF

/-! ### 1. Shared Helpers -/

private def standardPrefixes : List (String × IRI) := [
  ("rdf", rdfNS),
  ("rdfs", rdfsNS),
  ("owl", owlNS),
  ("xsd", xsdNS)
]

private def isXMLNameStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isXMLNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.'

private def isValidNCName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isXMLNameStart c && rest.all isXMLNameChar

private def sanitizeBNodeId (id : String) : String :=
  let cleaned := String.ofList (id.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_')
  match cleaned.toList with
  | [] => "b0"
  | c :: _ => if c.isAlpha || c == '_' then cleaned else "b_" ++ cleaned

/-- Split an `rdf:PlainLiteral` lexical value `"text@lang"` at the last `'@'`. -/
private def splitPlainLiteral (lex : String) : String × String :=
  let cs := lex.toList.reverse
  let rec go (langRev : List Char) : List Char → Option (String × String)
    | [] => none
    | '@' :: rest => some (String.ofList rest.reverse, String.ofList langRev)
    | c :: rest => go (c :: langRev) rest
  match go [] cs with
  | some p => p
  | none => (lex, "")

/-! ### 2. W3C Turtle 1.1 Serializer -/

private def escapeTurtleString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _ => acc.push c) ""

private def renderTurtleIRI (prefixes : List (String × IRI)) (iri : IRI) : String :=
  let matched := prefixes.findSome? fun (pfx, ns) =>
    if !ns.isEmpty && iri.startsWith ns then
      let loc := String.ofList (iri.toList.drop ns.length)
      if isValidNCName loc then some s!"{pfx}:{loc}" else none
    else none
  match matched with
  | some qname => qname
  | none => s!"<{iri}>"

private def renderTurtleTerm (prefixes : List (String × IRI)) : RDFTerm → String
  | .iri i => renderTurtleIRI prefixes i
  | .bnode id => s!"_:{sanitizeBNodeId id}"
  | .literal lex dt lang? =>
    if dt == rdfPlainLiteral then
      let (txt, tag) := splitPlainLiteral lex
      let esc := escapeTurtleString txt
      if tag.isEmpty then s!"\"{esc}\"" else s!"\"{esc}\"@{tag}"
    else
      let esc := escapeTurtleString lex
      match lang? with
      | some l => if l.isEmpty then s!"\"{esc}\"" else s!"\"{esc}\"@{l}"
      | none =>
        if dt == xsdString then s!"\"{esc}\""
        else s!"\"{esc}\"^^{renderTurtleIRI prefixes dt}"

private def mergePrefixes (custom : PrefixMap) (triples : List RDFTriple := []) : List (String × IRI) := Id.run do
  let mut out : List (String × IRI) := standardPrefixes
  let usesSWRL := triples.any fun t =>
    t.predicate.startsWith swrlNS ||
    match t.object with | .iri u => u.startsWith swrlNS | _ => false
  let usesSWRLB := triples.any fun t =>
    match t.object with | .iri u => u.startsWith swrlbNS | _ => false
  if usesSWRL && !custom.any (fun (p, _) => p == "swrl") then
    out := out ++ [("swrl", swrlNS)]
  if usesSWRLB && !custom.any (fun (p, _) => p == "swrlb") then
    out := out ++ [("swrlb", swrlbNS)]
  for (pfx, ns) in custom do
    if !out.any (fun (p, _) => p == pfx) && !ns.isEmpty then
      out := out ++ [(pfx, ns)]
  return out

/-- Render an `RDFGraph` as a valid W3C Turtle 1.1 document. -/
def renderTurtle (g : RDFGraph) : String := Id.run do
  let pfxs := mergePrefixes g.prefixes g.triples
  let mut lines : Array String := #[]
  for (pfx, ns) in pfxs do
    lines := lines.push s!"@prefix {pfx}: <{ns}> ."
  if !g.triples.isEmpty then
    lines := lines.push ""
  for t in g.triples do
    let s := renderTurtleTerm pfxs t.subject
    let p := renderTurtleIRI pfxs t.predicate
    let o := renderTurtleTerm pfxs t.object
    lines := lines.push s!"{s} {p} {o} ."
  return "\n".intercalate lines.toList ++ "\n"

/-! ### 3. W3C RDF/XML 1.1 Serializer -/

private def xmlEscapeText (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | _ => acc.push c) ""

private def xmlEscapeAttr (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | '\'' => acc ++ "&apos;"
    | _ => acc.push c) ""

/-- Split a predicate IRI into `(namespace, localNCName)` for RDF/XML QName emission. -/
private def splitPredicateIRI (iri : IRI) : String × String :=
  let cs := iri.toList
  let rec findSplit (sep : Char) (i : Nat) (best : Option Nat) : List Char → Option Nat
    | [] => best
    | c :: rest =>
      let best' := if c == sep then some (i + 1) else best
      findSplit sep (i + 1) best' rest
  let tryAt (idx? : Option Nat) : Option (String × String) :=
    idx?.bind fun idx =>
      let ns := String.ofList (cs.take idx)
      let loc := String.ofList (cs.drop idx)
      if !ns.isEmpty && isValidNCName loc then some (ns, loc) else none
  match tryAt (findSplit '#' 0 none cs) with
  | some p => p
  | none =>
    match tryAt (findSplit '/' 0 none cs) with
    | some p => p
    | none =>
      match tryAt (findSplit ':' 0 none cs) with
      | some p => p
      | none =>
        -- Fallback: scan backwards for the longest trailing NCName suffix
        let rec scan (idx : Nat) (rest : List Char) : String × String :=
          match rest with
          | [] => (iri, "prop")
          | _ :: tl =>
            let cand := String.ofList rest
            if idx > 0 && isValidNCName cand then
              (String.ofList (cs.take idx), cand)
            else scan (idx + 1) tl
        scan 0 cs

private def subjectKey : RDFTerm → String
  | .iri i => "I:" ++ i
  | .bnode id => "B:" ++ sanitizeBNodeId id
  | .literal lex dt _ => "L:" ++ dt ++ ":" ++ lex

/-- Render an `RDFGraph` as a valid W3C RDF/XML 1.1 document. -/
def renderRDFXML (g : RDFGraph) : String := Id.run do
  -- 1. Build namespace → prefix mapping covering all predicate IRIs
  let mut nsToPfx : Std.HashMap String String := {}
  let mut pfxList : Array (String × String) := #[]
  for (pfx, ns) in standardPrefixes do
    nsToPfx := nsToPfx.insert ns pfx
    pfxList := pfxList.push (pfx, ns)
  let usesSWRL := g.triples.any fun t =>
    t.predicate.startsWith swrlNS ||
    match t.object with | .iri u => u.startsWith swrlNS | _ => false
  if usesSWRL && !nsToPfx.contains swrlNS then
    nsToPfx := nsToPfx.insert swrlNS "swrl"
    pfxList := pfxList.push ("swrl", swrlNS)
  for (pfx, ns) in g.prefixes do
    if !pfx.isEmpty && isValidNCName pfx && !ns.isEmpty && !nsToPfx.contains ns &&
        !pfxList.any (fun (p, _) => p == pfx) then
      nsToPfx := nsToPfx.insert ns pfx
      pfxList := pfxList.push (pfx, ns)
  let mut nextNs : Nat := 1
  for t in g.triples do
    let (ns, _) := splitPredicateIRI t.predicate
    if !nsToPfx.contains ns then
      let mut pfx := s!"ns{nextNs}"
      nextNs := nextNs + 1
      while pfxList.any (fun (p, _) => p == pfx) do
        pfx := s!"ns{nextNs}"
        nextNs := nextNs + 1
      nsToPfx := nsToPfx.insert ns pfx
      pfxList := pfxList.push (pfx, ns)
  -- 2. Group triples by subject preserving first-seen order
  let mut order : Array String := #[]
  let mut groups : Std.HashMap String (RDFTerm × Array RDFTriple) := {}
  for t in g.triples do
    let key := subjectKey t.subject
    match groups.get? key with
    | some _ =>
      groups := groups.alter key fun
        | some (s, arr) => some (s, arr.push t)
        | none => some (t.subject, #[t])
    | none =>
      order := order.push key
      groups := groups.insert key (t.subject, #[t])
  -- 3. Emit XML document
  let mut lines : Array String := #["<?xml version=\"1.0\" encoding=\"UTF-8\"?>"]
  let xmlnsAttrs := pfxList.toList.map fun (pfx, ns) =>
    s!"    xmlns:{pfx}=\"{xmlEscapeAttr ns}\""
  lines := lines.push ("<rdf:RDF\n" ++ "\n".intercalate xmlnsAttrs ++ ">")
  for key in order do
    if let some (subj, triples) := groups.get? key then
      let openTag := match subj with
        | .iri i => s!"  <rdf:Description rdf:about=\"{xmlEscapeAttr i}\">"
        | .bnode id => s!"  <rdf:Description rdf:nodeID=\"{sanitizeBNodeId id}\">"
        | .literal _ _ _ => "  <rdf:Description>"
      lines := lines.push openTag
      for t in triples do
        let (ns, loc) := splitPredicateIRI t.predicate
        let pfx := nsToPfx.getD ns "ns0"
        let tag := s!"{pfx}:{loc}"
        let elemLine := match t.object with
          | .iri u =>
            s!"    <{tag} rdf:resource=\"{xmlEscapeAttr u}\"/>"
          | .bnode id =>
            s!"    <{tag} rdf:nodeID=\"{sanitizeBNodeId id}\"/>"
          | .literal lex dt lang? =>
            if dt == rdfPlainLiteral then
              let (txt, ltag) := splitPlainLiteral lex
              if ltag.isEmpty then
                s!"    <{tag}>{xmlEscapeText txt}</{tag}>"
              else
                s!"    <{tag} xml:lang=\"{xmlEscapeAttr ltag}\">{xmlEscapeText txt}</{tag}>"
            else
              match lang? with
              | some l =>
                if l.isEmpty then s!"    <{tag}>{xmlEscapeText lex}</{tag}>"
                else s!"    <{tag} xml:lang=\"{xmlEscapeAttr l}\">{xmlEscapeText lex}</{tag}>"
              | none =>
                if dt == xsdString then
                  s!"    <{tag}>{xmlEscapeText lex}</{tag}>"
                else
                  s!"    <{tag} rdf:datatype=\"{xmlEscapeAttr dt}\">{xmlEscapeText lex}</{tag}>"
        lines := lines.push elemLine
      lines := lines.push "  </rdf:Description>"
  lines := lines.push "</rdf:RDF>"
  return "\n".intercalate lines.toList ++ "\n"

end Sabrina.OWL2.RDF.Serialize
