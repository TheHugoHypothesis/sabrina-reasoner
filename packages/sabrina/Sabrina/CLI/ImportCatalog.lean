import Sabrina.OWL2.FunctionalSyntax
import Sabrina.OWL2.RDF.OWLMapping

/-! OASIS XML Catalog (`catalog-v001.xml`) and local directory loader for
    OWL 2 Functional-Style Syntax import libraries.

    The XML catalog parser (`parseOasisCatalogEntries`) is pure and total;
    file reading happens strictly in `IO` before handing the resulting finite
    `(IRI × String)` catalog to the verified import-closure resolver
    (`FunctionalSyntax.resolveImportClosure` / `SourceImportConformance`). -/

namespace Sabrina.CLI.ImportCatalog

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax

private def skipWs (cs : List Char) : List Char :=
  cs.dropWhile Char.isWhitespace

private def parseAttrValue (cs : List Char) : Option (String × List Char) :=
  match skipWs cs with
  | '"' :: rest =>
    let (val, tail) := rest.span (· != '"')
    match tail with
    | '"' :: rem => some (String.ofList val, rem)
    | _ => none
  | '\'' :: rest =>
    let (val, tail) := rest.span (· != '\'')
    match tail with
    | '\'' :: rem => some (String.ofList val, rem)
    | _ => none
  | _ => none

private def parseTagAttrs (cs : List Char) : List (String × String) :=
  let rec go (fuel : Nat) (s : List Char) (acc : List (String × String)) : List (String × String) :=
    match fuel with
    | 0 => acc.reverse
    | f + 1 =>
      let s := skipWs s
      match s with
      | [] | '>' :: _ | '/' :: '>' :: _ => acc.reverse
      | _ =>
        let (kCs, rest) := s.span fun c => !c.isWhitespace && c != '=' && c != '>' && c != '/'
        let key := String.ofList kCs
        match skipWs rest with
        | '=' :: afterEq =>
          match parseAttrValue afterEq with
          | some (val, rem) => go f rem ((key, val) :: acc)
          | none => acc.reverse
        | _ =>
          match rest with
          | [] => acc.reverse
          | _ :: rem => go f rem acc
  go (cs.length + 1) cs []

private def joinRelPath (base rel : String) : String :=
  if base.isEmpty || rel.startsWith "/" || rel.startsWith "http://" || rel.startsWith "https://" || rel.startsWith "file:" then
    rel
  else if base.endsWith "/" then base ++ rel
  else base ++ "/" ++ rel

/-- Pure parser for OASIS XML Catalog / Protégé `catalog-v001.xml` documents.
    Extracts `(importIRI, relativeOrAbsoluteUri)` pairs from `<uri name="..." uri="..."/>`
    elements, respecting enclosing `<group xml:base="..."/>` scopes. -/
def parseOasisCatalogEntries (xmlText : String) : List (IRI × String) := Id.run do
  let cs := xmlText.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut baseStack : List String := []
  let mut entries : List (IRI × String) := []
  while i < n do
    if cs[i]! != '<' then
      i := i + 1
    else if i + 3 < n && cs[i + 1]! == '!' && cs[i + 2]! == '-' && cs[i + 3]! == '-' then
      -- Skip XML comment <!-- ... -->
      i := i + 4
      while i + 2 < n && !(cs[i]! == '-' && cs[i + 1]! == '-' && cs[i + 2]! == '>') do
        i := i + 1
      i := min n (i + 3)
    else
      i := i + 1
      let mut tagBuf : List Char := []
      while i < n && cs[i]! != '>' do
        tagBuf := cs[i]! :: tagBuf
        i := i + 1
      if i < n then i := i + 1
      let tagChars := skipWs tagBuf.reverse
      let isClosing := tagChars.head? == some '/'
      let isSelfClosing := tagChars.reverse.head? == some '/'
      let body := if isClosing then tagChars.drop 1 else tagChars
      let (nameCs, rest) := body.span fun c => !c.isWhitespace && c != '/'
      let tagName := String.ofList nameCs
      let localName := match tagName.splitOn ":" with
        | [_, loc] => loc
        | _ => tagName
      if isClosing then
        if localName == "group" then
          baseStack := baseStack.drop 1
      else if localName == "group" then
        let attrs := parseTagAttrs rest
        let base := (attrs.lookup "xml:base").getD ""
        if !isSelfClosing then
          baseStack := base :: baseStack
      else if localName == "uri" then
        let attrs := parseTagAttrs rest
        match attrs.lookup "name", attrs.lookup "uri" with
        | some nameIri, some targetUri =>
          let curBase := baseStack.foldr (fun b acc => joinRelPath b acc) ""
          let resolved := joinRelPath curBase targetUri
          entries := (nameIri, resolved) :: entries
        | _, _ => pure ()
  return entries.reverse

private def stripFileScheme (uri : String) : String :=
  if uri.startsWith "file://" then String.ofList (uri.toList.drop 7)
  else uri

/-- Load an OASIS XML Catalog (`catalog-v001.xml`) from disk and read all mapped
    local `.ofn` files into a finite `(IRI × String)` import library. -/
def loadOasisCatalog (catalogPath : System.FilePath) : IO (Except String (List (IRI × String))) := do
  try
    let xmlText ← IO.FS.readFile catalogPath
    let parentDir := catalogPath.parent.getD (System.FilePath.mk ".")
    let pairs := parseOasisCatalogEntries xmlText
    let mut lib : List (IRI × String) := []
    for (iri, target) in pairs do
      let rel := stripFileScheme target
      let filePath :=
        if rel.startsWith "/" then System.FilePath.mk rel
        else parentDir / rel
      if ← filePath.pathExists then
        let contents ← IO.FS.readFile filePath
        lib := (iri, contents) :: lib
      else
        return .error s!"catalog entry for <{iri}> points to missing file: {filePath}"
    return .ok lib.reverse
  catch e =>
    return .error s!"failed to load OASIS catalog {catalogPath}: {e}"

/-- Load all `.ofn` files in a local directory into a finite `(IRI × String)` import
    library indexed by each document's declared `ontologyIRI` (or filename). -/
def loadImportDir (dir : System.FilePath) : IO (Except String (List (IRI × String))) := do
  try
    let entries ← dir.readDir
    let mut lib : List (IRI × String) := []
    for entry in entries do
      let fn := entry.fileName
      if fn.endsWith ".ofn" || fn.endsWith ".rdf" || fn.endsWith ".owl" || fn.endsWith ".ttl" then
        let contents ← IO.FS.readFile entry.path
        let key := match RDF.OWLMapping.parseDocumentAuto contents false with
          | .ok doc => doc.ontologyIRI.getD (doc.versionIRI.getD fn)
          | .error _ => fn
        lib := (key, contents) :: lib
    return .ok lib.reverse
  catch e =>
    return .error s!"failed to load import directory {dir}: {e}"

end Sabrina.CLI.ImportCatalog
