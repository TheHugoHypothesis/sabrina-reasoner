import Sabrina.OWL2.SROIQD.Termination.WiderDataReduction

/-!
The typed XML datatype accepts fixed points of the namespace-aware
canonicalization pass. The proofs below characterize its lexical and value
spaces, and connect the source-level gate to the wider decision procedure.
The earlier namespace-oblivious scanner provides a comparison.
-/

namespace Sabrina.OWL2.SROIQD.Termination.XMLLiteral

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.WiderData

/-! ### 1. W3C XML 1.0 character classes -/

/-- W3C XML 1.0 Fifth Edition Production [2] `Char`. -/
def isXML10Char (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xD ||
  (0x20 ≤ n && n ≤ 0xD7FF) ||
  (0xE000 ≤ n && n ≤ 0xFFFD) ||
  (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- W3C XML 1.0 Production [3] `S` (whitespace). -/
def isXMLSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- W3C XML 1.0 Fifth Edition Production [4] `NameStartChar`. -/
def isXMLNameStartChar (c : Char) : Bool :=
  let n := c.toNat
  c == ':' || c == '_' ||
  (0x41 ≤ n && n ≤ 0x5A) || (0x61 ≤ n && n ≤ 0x7A) ||
  (0xC0 ≤ n && n ≤ 0xD6) || (0xD8 ≤ n && n ≤ 0xF6) ||
  (0xF8 ≤ n && n ≤ 0x2FF) || (0x370 ≤ n && n ≤ 0x37D) ||
  (0x37F ≤ n && n ≤ 0x1FFF) || (0x200C ≤ n && n ≤ 0x200D) ||
  (0x2070 ≤ n && n ≤ 0x218F) || (0x2C00 ≤ n && n ≤ 0x2FEF) ||
  (0x3001 ≤ n && n ≤ 0xD7FF) || (0xF900 ≤ n && n ≤ 0xFDCF) ||
  (0xFDF0 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0xEFFFF)

/-- W3C XML 1.0 Fifth Edition Production [4a] `NameChar`. -/
def isXMLNameChar (c : Char) : Bool :=
  isXMLNameStartChar c || c == '-' || c == '.' ||
  ('0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat) ||
  c.toNat == 0xB7 ||
  (0x0300 ≤ c.toNat && c.toNat ≤ 0x036F) ||
  (0x203F ≤ c.toNat && c.toNat ≤ 0x2040)

/-! ### 2. Total structurally-terminating XML 1.0 / Exc-C14N content scanner -/

private def skipXMLSpaces : List Char → List Char
  | c :: rest => if isXMLSpace c then skipXMLSpaces rest else c :: rest
  | [] => []

private def takeNameChars : List Char → List Char × List Char
  | c :: rest =>
    if isXMLNameChar c then
      let (ns, rem) := takeNameChars rest
      (c :: ns, rem)
    else ([], c :: rest)
  | [] => ([], [])

private def readXMLName : List Char → Option (String × List Char)
  | c :: rest =>
    if isXMLNameStartChar c then
      let (more, rem) := takeNameChars rest
      some (String.ofList (c :: more), rem)
    else none
  | [] => none

private def parseDecNat (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    if '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat then
      parseDecNat (acc * 10 + (c.toNat - '0'.toNat)) rest
    else none

private def hexDigitVal (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then some (10 + c.toNat - 'a'.toNat)
  else if 'A'.toNat ≤ c.toNat && c.toNat ≤ 'F'.toNat then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseHexNat (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    match hexDigitVal c with
    | some d => parseHexNat (acc * 16 + d) rest
    | none => none

private def isXML10Codepoint (n : Nat) : Bool :=
  n == 0x9 || n == 0xA || n == 0xD ||
  (0x20 ≤ n && n ≤ 0xD7FF) ||
  (0xE000 ≤ n && n ≤ 0xFFFD) ||
  (0x10000 ≤ n && n ≤ 0x10FFFF)

private def takeUntilSemi : List Char → Option (List Char × List Char)
  | [] => none
  | ';' :: rest => some ([], rest)
  | c :: rest =>
    (takeUntilSemi rest).map fun (body, rem) => (c :: body, rem)

/-- Validate an XML reference starting right after `&`.
When `strictCanon = true`, restricts to canonical Exc-C14N references:
in text: `&amp;`, `&lt;`, `&gt;`, `&#xD;`;
in attributes: `&amp;`, `&lt;`, `&quot;`, `&#x9;`, `&#xA;`, `&#xD;`. -/
private def parseXMLRef (strictCanon inAttr : Bool) (cs : List Char) : Option (List Char) :=
  match takeUntilSemi cs with
  | none => none
  | some (body, rem) =>
    if strictCanon then
      let s := String.ofList body
      let ok :=
        if inAttr then
          s == "amp" || s == "lt" || s == "quot" || s == "#x9" || s == "#xA" || s == "#xD"
        else
          s == "amp" || s == "lt" || s == "gt" || s == "#xD"
      if ok then some rem else none
    else
      match body with
      | '#' :: 'x' :: hex =>
        if hex.isEmpty then none
        else match parseHexNat 0 hex with
        | some cp => if isXML10Codepoint cp then some rem else none
        | none => none
      | '#' :: dec =>
        if dec.isEmpty then none
        else match parseDecNat 0 dec with
        | some cp => if isXML10Codepoint cp then some rem else none
        | none => none
      | _ =>
        let s := String.ofList body
        if s == "amp" || s == "lt" || s == "gt" || s == "quot" || s == "apos" then some rem
        else none

/-- Parse an attribute value starting right after the opening quote `q`. -/
private def parseAttrValueLoop (strictCanon : Bool) (q : Char) :
    Nat → List Char → Option (List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: rest =>
    if c == q then some rest
    else if c == '<' || !isXML10Char c then none
    else if strictCanon && (c == '\r' || c == '\n' || c == '\t') then none
    else if c == '&' then
      match parseXMLRef strictCanon true rest with
      | some rem => parseAttrValueLoop strictCanon q fuel rem
      | none => none
    else parseAttrValueLoop strictCanon q fuel rest

private def parseAttrValue (strictCanon : Bool) (q : Char) (cs : List Char) : Option (List Char) :=
  parseAttrValueLoop strictCanon q (cs.length + 1) cs

/-- Classify an attribute name for Exc-C14N ordering: namespace declarations
(`xmlns`, `xmlns:*`) precede normal attributes, and each group is sorted
lexicographically. -/
private def isXmlnsAttr (name : String) : Bool :=
  name == "xmlns" || name.startsWith "xmlns:"

private def canonAttrLt (a b : String) : Bool :=
  match isXmlnsAttr a, isXmlnsAttr b with
  | true, false => true
  | false, true => false
  | _, _ => a < b

/-- Parse attributes inside a start/empty tag up to `>` or `/>`.
Returns `(isSelfClosing, remainingChars)`. -/
private def parseTagAttrsLoop (strictCanon : Bool) :
    Nat → List String → Option String → List Char → Option (Bool × List Char)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | _ + 1, _, _, '>' :: rest => some (false, rest)
  | _ + 1, _, _, '/' :: '>' :: rest =>
    if strictCanon then none else some (true, rest)
  | fuel + 1, seen, prevAttr, c :: rest =>
    if isXMLSpace c then
      if strictCanon then
        if c != ' ' then none
        else
          match readXMLName rest with
          | none => none
          | some (aname, rem1) =>
            if seen.contains aname then none
            else if match prevAttr with | some p => !canonAttrLt p aname | none => false then none
            else
              match rem1 with
              | '=' :: '"' :: rem2 =>
                match parseAttrValue true '"' rem2 with
                | none => none
                | some rem3 => parseTagAttrsLoop true fuel (aname :: seen) (some aname) rem3
              | _ => none
      else
        let rem0 := skipXMLSpaces rest
        match rem0 with
        | '>' :: rem1 => some (false, rem1)
        | '/' :: '>' :: rem1 => some (true, rem1)
        | _ =>
          match readXMLName rem0 with
          | none => none
          | some (aname, rem1) =>
            if seen.contains aname then none
            else
              let rem2 := skipXMLSpaces rem1
              match rem2 with
              | '=' :: rem3 =>
                let rem4 := skipXMLSpaces rem3
                match rem4 with
                | q :: rem5 =>
                  if q == '"' || q == '\'' then
                    match parseAttrValue false q rem5 with
                    | none => none
                    | some rem6 => parseTagAttrsLoop false fuel (aname :: seen) (some aname) rem6
                  else none
                | [] => none
              | _ => none
    else none

private def parseTagAttrs (strictCanon : Bool) (cs : List Char) : Option (Bool × List Char) :=
  parseTagAttrsLoop strictCanon (cs.length + 1) [] none cs

/-- Scan an XML comment body starting right after `<!--`.
W3C XML 1.0 Production [15]: `--` is forbidden inside comment body and `-` cannot
immediately precede `-->`. -/
private def skipCommentBody : List Char → Option (List Char)
  | '-' :: '-' :: '>' :: rest => some rest
  | '-' :: '-' :: _ => none
  | c :: rest => if isXML10Char c then skipCommentBody rest else none
  | [] => none

/-- Scan a CDATA section starting right after `<![CDATA[`. -/
private def skipCDATABody : List Char → Option (List Char)
  | ']' :: ']' :: '>' :: rest => some rest
  | c :: rest => if isXML10Char c then skipCDATABody rest else none
  | [] => none

/-- Scan a Processing Instruction body starting right after `<?target`. -/
private def skipPIBody : List Char → Option (List Char)
  | '?' :: '>' :: rest => some rest
  | c :: rest => if isXML10Char c then skipPIBody rest else none
  | [] => none

private def isXMLTargetDisallowed (s : String) : Bool :=
  s.toLower == "xml"

/-- Total structurally-terminating XML 1.0 / Exc-C14N content validator. -/
private def scanXMLContentLoop (strictCanon : Bool) : Nat → List String → List Char → Bool
  | 0, _, _ => false
  | _ + 1, stack, [] => stack.isEmpty
  | fuel + 1, stack, '<' :: '/' :: rest =>
    match readXMLName rest with
    | none => false
    | some (ename, rem1) =>
      match stack with
      | top :: tail =>
        if top != ename then false
        else
          let rem2 := if strictCanon then rem1 else skipXMLSpaces rem1
          match rem2 with
          | '>' :: rem3 => scanXMLContentLoop strictCanon fuel tail rem3
          | _ => false
      | [] => false
  | fuel + 1, stack, '<' :: '!' :: '-' :: '-' :: rest =>
    if strictCanon then false
    else
      match skipCommentBody rest with
      | none => false
      | some rem => scanXMLContentLoop strictCanon fuel stack rem
  | fuel + 1, stack, '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: rest =>
    if strictCanon then false
    else
      match skipCDATABody rest with
      | none => false
      | some rem => scanXMLContentLoop strictCanon fuel stack rem
  | fuel + 1, stack, '<' :: '?' :: rest =>
    match readXMLName rest with
    | none => false
    | some (target, rem1) =>
      if isXMLTargetDisallowed target then false
      else
        match rem1 with
        | '?' :: '>' :: rem2 => scanXMLContentLoop strictCanon fuel stack rem2
        | c :: rem2 =>
          if isXMLSpace c then
            match skipPIBody rem2 with
            | none => false
            | some rem3 => scanXMLContentLoop strictCanon fuel stack rem3
          else false
        | [] => false
  | fuel + 1, stack, '<' :: rest =>
    match readXMLName rest with
    | none => false
    | some (tname, rem1) =>
      match parseTagAttrs strictCanon rem1 with
      | none => false
      | some (selfClose, rem2) =>
        if selfClose then scanXMLContentLoop strictCanon fuel stack rem2
        else scanXMLContentLoop strictCanon fuel (tname :: stack) rem2
  | fuel + 1, stack, '&' :: rest =>
    match parseXMLRef strictCanon false rest with
    | none => false
    | some rem => scanXMLContentLoop strictCanon fuel stack rem
  | _ + 1, _, ']' :: ']' :: '>' :: _ => false
  | fuel + 1, stack, c :: rest =>
    if !isXML10Char c then false
    else if strictCanon && (c == '\r' || c == '>') then false
    else scanXMLContentLoop strictCanon fuel stack rest

/-- Balanced-content check using XML 1.0 character classes (without XML Namespace checks). -/
def checkWellFormedXMLContent (s : String) : Bool :=
  let cs := s.toList
  scanXMLContentLoop false (cs.length + 1) [] cs

/-- Balanced-content check with lexical restrictions drawn from Exclusive XML
Canonicalization, but without XML Namespace binding checks. -/
def checkCanonicalXMLContentNoNS (s : String) : Bool :=
  let cs := s.toList
  checkWellFormedXMLContent s && scanXMLContentLoop true (cs.length + 1) [] cs

/-- Namespace-aware check for input to the canonicalizer. -/
abbrev checkWellFormedXMLLiteral (s : String) : Bool :=
  Datatypes.checkWellFormedXMLLiteral s

/-- Check for the canonical fixed points used by the typed datatype map. -/
abbrev checkCanonicalXMLLiteral (s : String) : Bool :=
  Datatypes.checkCanonicalXMLLiteral s

theorem canonicalXMLLiteral_implies_wellFormed {s : String}
    (h : checkCanonicalXMLLiteral s = true) : checkWellFormedXMLLiteral s = true :=
  Datatypes.canonicalXMLLiteral_implies_wellFormed h

/-- The namespace-oblivious XML 1.0 content scanner accepts `<p:e></p:e>`,
but the namespace-aware XML checker and typed map enforce declared prefixes. -/
theorem xmlContentNoNS_accepts_undeclared_prefix :
    checkCanonicalXMLContentNoNS "<p:e></p:e>" = true ∧
    checkWellFormedXMLLiteral "<p:e></p:e>" = false ∧
    checkCanonicalXMLLiteral "<p:e></p:e>" = false ∧
    decodeLiteral ⟨"<p:e></p:e>", rdf "XMLLiteral"⟩ = none := by
  decide

/-! ### 3. Correspondence with the executable XML checker -/

theorem datatypeMap_xmlLiteral_iff (raw s : String) :
    decodeLiteral ⟨raw, rdf "XMLLiteral"⟩ = some (.xmlLiteral s) ↔
      raw = s ∧ checkCanonicalXMLLiteral raw = true :=
  decodeXMLLiteral_iff raw s

theorem datatypeMap_valueSpace_xmlLiteral_iff (v : Value) :
    datatypeMap.valueSpace (rdf "XMLLiteral") v ↔
      ∃ s : String, checkCanonicalXMLLiteral s = true ∧ v = .xmlLiteral s :=
  valueSpace_xmlLiteral_iff v

theorem datatypeMap_validLiteral_xmlLiteral_iff (raw : String) :
    datatypeMap.validLiteral ⟨raw, rdf "XMLLiteral"⟩ ↔
      checkCanonicalXMLLiteral raw = true := by
  change (∃ v, decodeLiteral ⟨raw, rdf "XMLLiteral"⟩ = some v) ↔ _
  rw [decodeXMLLiteral_eq]
  cases h : checkCanonicalXMLLiteral raw <;> simp [h]

/-- `Datatypes.datatypeMap` rejects malformed XML 1.0 content such as `"<a></b>"`. -/
theorem datatypeMap_rejects_malformed_xml :
    decodeLiteral ⟨"<a></b>", rdf "XMLLiteral"⟩ = none := by
  rw [decodeXMLLiteral_eq]; decide

/-- `Datatypes.datatypeMap` rejects namespace-ill-formed XML content (undeclared
prefix, empty prefix declaration `xmlns:p=""`, and duplicate expanded attributes). -/
theorem datatypeMap_rejects_illFormed_namespaces :
    decodeLiteral ⟨"<p:e></p:e>", rdf "XMLLiteral"⟩ = none ∧
    decodeLiteral ⟨"<e xmlns:p=\"\"></e>", rdf "XMLLiteral"⟩ = none ∧
    decodeLiteral ⟨"<e xmlns:p=\"http://x.org\" xmlns:q=\"http://x.org\" p:a=\"1\" q:a=\"2\"></e>",
      rdf "XMLLiteral"⟩ = none := by
  repeat rw [decodeXMLLiteral_eq]
  refine ⟨by decide, by decide, by decide⟩

/-- Only the canonical spelling is in the lexical space of the typed map. -/
theorem datatypeMap_rejects_noncanonical_xml :
    decodeLiteral ⟨"<a b='2' a='1'/>", rdf "XMLLiteral"⟩ = none ∧
    decodeLiteral ⟨"<a a=\"1\" b=\"2\"></a>", rdf "XMLLiteral"⟩ =
      some (.xmlLiteral "<a a=\"1\" b=\"2\"></a>") := by
  repeat rw [decodeXMLLiteral_eq]
  exact ⟨by decide, by decide⟩

/-! ### 4. Ontology-level strict `rdf:XMLLiteral` gate -/

def dataRangeLiterals : DataRange → List Literal
  | .datatype _ => []
  | .complement d => dataRangeLiterals d
  | .intersection a b | .union a b => dataRangeLiterals a ++ dataRangeLiterals b
  | .oneOf ls => ls
  | .restriction _ fs => fs.map Facet.bound

def classExprLiterals : ClassExpr → List Literal
  | .named _ | .oneOf _ | .objectValue _ _ | .objectSelf _ => []
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classExprLiterals c
  | .intersection a b | .union a b => classExprLiterals a ++ classExprLiterals b
  | .dataSome _ d | .dataAll _ d | .dataMin _ _ d | .dataMax _ _ d | .dataExact _ _ d =>
    dataRangeLiterals d
  | .dataValue _ l => [l]

def axiomLiterals : Axiom → List Literal
  | .subClassOf a b => classExprLiterals a ++ classExprLiterals b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classExprLiterals
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ | .classAssertion c _ => classExprLiterals c
  | .dataPropertyRange _ d | .datatypeDefinition _ d => dataRangeLiterals d
  | .dataAssertion _ _ l | .negativeDataAssertion _ _ l => [l]
  | _ => []

def ontologyLiterals (o : Ontology) : List Literal :=
  o.flatMap axiomLiterals

def literalXMLValid (strictCanon : Bool) (l : Literal) : Bool :=
  if l.datatype == rdf "XMLLiteral" then
    if strictCanon then checkCanonicalXMLLiteral l.lexical
    else checkWellFormedXMLLiteral l.lexical
  else true

def ontologyXMLLiteralsValid (strictCanon : Bool) (o : Ontology) : Bool :=
  (ontologyLiterals o).all (literalXMLValid strictCanon)

theorem ontologyXMLLiteralsValid_iff (strictCanon : Bool) (o : Ontology) :
    ontologyXMLLiteralsValid strictCanon o = true ↔
      ∀ l ∈ ontologyLiterals o, l.datatype = rdf "XMLLiteral" →
        (if strictCanon then checkCanonicalXMLLiteral l.lexical
         else checkWellFormedXMLLiteral l.lexical) = true := by
  simp only [ontologyXMLLiteralsValid, List.all_eq_true, literalXMLValid]
  constructor
  · intro h l hl hdt
    have := h l hl
    simpa [hdt] using this
  · intro h l hl
    by_cases hdt : l.datatype = rdf "XMLLiteral"
    · simpa [hdt] using h l hl hdt
    · simp [beq_false_of_ne hdt]

/-- Wider-datatype decision adapter that requires each XML literal to already be
in strict Exc-C14N canonical lexical form (`checkCanonicalXMLLiteral`). -/
def decideWithStrictXMLLiterals? (o : Ontology) : Option Bool :=
  if ontologyXMLLiteralsValid true o then decideWithWiderDataRanges? o else none

theorem decideWithStrictXMLLiterals_iff {o : Ontology} {b : Bool}
    (h : decideWithStrictXMLLiterals? o = some b) :
    ontologyXMLLiteralsValid true o = true ∧ (b = true ↔ Satisfiable datatypeMap o) := by
  unfold decideWithStrictXMLLiterals? at h
  split at h
  · rename_i hxml
    exact ⟨hxml, decideWithWiderDataRanges_iff h⟩
  · cases h

/-! ### 5. Live `#guard` regressions for XML 1.0, Namespaces in XML 1.0, & Exc-C14N -/

-- Well-formed AND canonical Exc-C14N literals
#guard checkCanonicalXMLLiteral "" == true
#guard checkCanonicalXMLLiteral "plain text" == true
#guard checkCanonicalXMLLiteral "<a>hello &amp; world</a>" == true
#guard checkCanonicalXMLLiteral "<a xmlns=\"http://e.org\" a=\"1\" b=\"2\"><b></b></a>" == true
#guard checkCanonicalXMLLiteral "<e x=\"a&quot;b&lt;c&#xA;d\">1 &lt; 2 &amp; 3 &gt; 0</e>" == true
#guard checkCanonicalXMLLiteral "<a></a><b></b>" == true
#guard checkCanonicalXMLLiteral "<p:e xmlns:p=\"http://e.org\"></p:e>" == true
#guard checkCanonicalXMLLiteral "<xmlns></xmlns>" == true
#guard checkCanonicalXMLLiteral "<p:e xmlns:p=\"relative\"></p:e>" == false

-- Well-formed XML 1.0 + Namespaces, but NOT in Exc-C14N canonical form
#guard checkWellFormedXMLLiteral "<a/>" == true
#guard checkCanonicalXMLLiteral "<a/>" == false
#guard checkWellFormedXMLLiteral "<a b=\"1\" a=\"2\"></a>" == true
#guard checkCanonicalXMLLiteral "<a b=\"1\" a=\"2\"></a>" == false
#guard checkWellFormedXMLLiteral "<a x='1'></a>" == true
#guard checkCanonicalXMLLiteral "<a x='1'></a>" == false
#guard checkWellFormedXMLLiteral "<!-- comment --><a/>" == true
#guard checkCanonicalXMLLiteral "<!-- comment --><a></a>" == true
#guard checkWellFormedXMLLiteral "<![CDATA[x < y]]>" == true
#guard checkCanonicalXMLLiteral "<![CDATA[x < y]]>" == false
#guard checkWellFormedXMLLiteral "a > b" == true
#guard checkCanonicalXMLLiteral "a > b" == false
#guard checkWellFormedXMLLiteral "&apos;hi&#65;" == true
#guard checkCanonicalXMLLiteral "&apos;hi&#65;" == false
#guard checkWellFormedXMLLiteral "<a xmlns:p=\"http://e.org\" xmlns:u=\"http://u.org\"><p:b/></a>" == true
#guard checkCanonicalXMLLiteral "<a xmlns:p=\"http://e.org\" xmlns:u=\"http://u.org\"><p:b/></a>" == false

-- Namespace-ill-formed XML (rejected by normative `checkWellFormedXMLLiteral` and `decodeLiteral`)
#guard checkWellFormedXMLLiteral "<p:e></p:e>" == false
#guard checkCanonicalXMLLiteral "<p:e></p:e>" == false
#guard checkWellFormedXMLLiteral "<e p:a=\"1\"></e>" == false
#guard checkWellFormedXMLLiteral "<e xmlns:p=\"\"></e>" == false
#guard checkWellFormedXMLLiteral "<e xmlns:xmlns=\"http://e.org\"></e>" == false
#guard checkWellFormedXMLLiteral "<e xmlns:xml=\"http://wrong.org\"></e>" == false
#guard checkWellFormedXMLLiteral "<e xmlns:p=\"http://www.w3.org/XML/1998/namespace\"></e>" == false
#guard checkWellFormedXMLLiteral "<e xmlns:p=\"http://x.org\" xmlns:q=\"http://x.org\" p:a=\"1\" q:a=\"2\"></e>" == false
#guard checkWellFormedXMLLiteral "<a:b:c></a:b:c>" == false

-- Malformed XML 1.0 (rejected by all validators)
#guard checkWellFormedXMLLiteral "<a></b>" == false
#guard checkWellFormedXMLLiteral "<unclosed>" == false
#guard checkWellFormedXMLLiteral "</orphan>" == false
#guard checkWellFormedXMLLiteral "<a x=\"1\" x=\"2\"></a>" == false
#guard checkWellFormedXMLLiteral "a < b" == false
#guard checkWellFormedXMLLiteral "&bogus;" == false
#guard checkWellFormedXMLLiteral "a ]]> b" == false
#guard checkWellFormedXMLLiteral "<!-- bad -- comment -->" == false
#guard checkWellFormedXMLLiteral "<?xml version=\"1.0\"?>" == false
#guard checkWellFormedXMLLiteral "<1bad></1bad>" == false

-- End-to-end strict XML gate with solver
#guard decideWithStrictXMLLiterals?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a>ok</a>", rdf "XMLLiteral"⟩] == some true
#guard decideWithStrictXMLLiterals?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a></b>", rdf "XMLLiteral"⟩] == none
#guard decideWithStrictXMLLiterals?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a/>", rdf "XMLLiteral"⟩] == none
#guard decideWithStrictXMLLiterals?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<p:e></p:e>", rdf "XMLLiteral"⟩] == none

-- The main solver also enforces canonical spelling. Comments distinguish values.
#guard decideWithWiderDataRanges?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<p:e></p:e>", rdf "XMLLiteral"⟩] == none
#guard decideWithWiderDataRanges?
  [.dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a/>", rdf "XMLLiteral"⟩] == none
#guard decideWithWiderDataRanges?
  [.functionalDataProperty "http://example.org/doc",
   .dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a><!--x--></a>", rdf "XMLLiteral"⟩,
   .dataAssertion "http://example.org/doc" (.named "http://example.org/a") ⟨"<a></a>", rdf "XMLLiteral"⟩] == some false

#print axioms canonicalXMLLiteral_implies_wellFormed
#print axioms xmlContentNoNS_accepts_undeclared_prefix
#print axioms datatypeMap_xmlLiteral_iff
#print axioms datatypeMap_valueSpace_xmlLiteral_iff
#print axioms datatypeMap_validLiteral_xmlLiteral_iff
#print axioms datatypeMap_rejects_malformed_xml
#print axioms datatypeMap_rejects_illFormed_namespaces
#print axioms datatypeMap_rejects_noncanonical_xml
#print axioms ontologyXMLLiteralsValid_iff
#print axioms decideWithStrictXMLLiterals_iff

end Sabrina.OWL2.SROIQD.Termination.XMLLiteral
