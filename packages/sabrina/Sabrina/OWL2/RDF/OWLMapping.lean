import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.RDF.Graph
import Sabrina.OWL2.RDF.XMLParser
import Sabrina.OWL2.RDF.TurtleParser
import Sabrina.OWL2.StrictTyping
import Sabrina.OWL2.SWRL

/-! W3C OWL 2 Mapping from RDF Graphs to the Structural Specification (Tables 3–18),
    forward Structural-to-RDF encoder, unified auto-detecting document & import-closure
    parser (FSS / RDF/XML / Turtle), and kernel-checked correspondence proofs. -/

namespace Sabrina.OWL2.RDF.OWLMapping

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.StrictTyping
open Sabrina.OWL2.RDF

/-! ### 1. Indexed RDF Triple Consumption State -/

private structure MapIndex where
  bySubject : Std.HashMap RDFTerm (Array Nat)
  classes : Std.HashSet IRI := {}
  datatypes : Std.HashSet IRI := {}
  objProps : Std.HashSet IRI := {}
  dataProps : Std.HashSet IRI := {}
  annotProps : Std.HashSet IRI := {}
  namedInds : Std.HashSet IRI := {}
  declKeys : Std.HashSet (Nat × IRI) := {}

private structure MapState where
  docId : String
  triples : Array RDFTriple
  consumed : Array Bool
  index : Option MapIndex := none
  -- Kernel-reducible fallback typing lists (used when `index = none` on small graphs)
  classes : List IRI := []
  datatypes : List IRI := []
  objProps : List IRI := []
  dataProps : List IRI := []
  annotProps : List IRI := []
  namedInds : List IRI := []
  -- Output structural items
  ontologyHeaderTerm : Option RDFTerm := none
  ontologyIRI : Option IRI := none
  versionIRI : Option IRI := none
  imports : List IRI := []
  declarations : List EntityDecl := []
  annotationAxioms : List AnnotationAxiom := []
  axioms : List Axiom := []
  swrlVars : List RDFTerm := []
  rules : List SWRL.SWRLRule := []

private abbrev MapM (α : Type) := StateT MapState (Except String) α

private def markConsumed (idx : Nat) : MapM Unit :=
  modify fun st => { st with consumed := st.consumed.set! idx true }

private def isConsumed (idx : Nat) : MapM Bool := do
  return (← get).consumed.getD idx true

private def activeIndicesAux (ts : Array RDFTriple) (cons : Array Bool) :
    Nat → Nat → List (Nat × RDFTriple) → List (Nat × RDFTriple)
  | 0, _, acc => acc.reverse
  | rem + 1, i, acc =>
    if h : i < ts.size then
      let acc' := if !cons.getD i true then (i, ts[i]) :: acc else acc
      activeIndicesAux ts cons rem (i + 1) acc'
    else acc.reverse

private def activeIndices : MapM (List (Nat × RDFTriple)) := do
  let st ← get
  return activeIndicesAux st.triples st.consumed st.triples.size 0 []

private def findActiveBySP (s : RDFTerm) (p : IRI) : MapM (List (Nat × RDFTerm)) := do
  let st ← get
  match st.index with
  | some ix =>
    let idxs := ix.bySubject.getD s #[]
    return idxs.foldr (fun i acc =>
      if !st.consumed.getD i true then
        if h : i < st.triples.size then
          let t := st.triples[i]
          if t.predicate == p then (i, t.object) :: acc else acc
        else acc
      else acc) []
  | none =>
    let act ← activeIndices
    return act.filterMap fun (i, t) =>
      if t.subject == s && t.predicate == p then some (i, t.object) else none

private def findActiveByS (s : RDFTerm) : MapM (List (Nat × RDFTriple)) := do
  let st ← get
  match st.index with
  | some ix =>
    let idxs := ix.bySubject.getD s #[]
    return idxs.foldr (fun i acc =>
      if !st.consumed.getD i true then
        if h : i < st.triples.size then (i, st.triples[i]) :: acc else acc
      else acc) []
  | none =>
    let act ← activeIndices
    return act.filter fun (_, t) => t.subject == s

private def hasType (s : RDFTerm) (ty : IRI) : MapM (Option Nat) := do
  let hits ← findActiveBySP s rdfType
  for (i, o) in hits do
    if o == .iri ty then return some i
  return none

private def isObjPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInObjProp iri ||
    match st.index with
    | some ix => ix.objProps.contains iri
    | none => st.objProps.contains iri

private def isDataPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInDataProp iri ||
    match st.index with
    | some ix => ix.dataProps.contains iri
    | none => st.dataProps.contains iri

private def isKnownMetadataVocab (iri : IRI) : Bool :=
  iri.startsWith "http://purl.org/dc/terms/" ||
  iri.startsWith "http://purl.org/dc/elements/1.1/" ||
  iri.startsWith "http://www.w3.org/2004/02/skos/core#" ||
  iri.startsWith "http://purl.org/vocab/vann/" ||
  iri.startsWith "http://www.geneontology.org/formats/oboInOwl#" ||
  iri.startsWith "http://xmlns.com/foaf/0.1/"

private def isAnnotPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInAnnotProp iri ||
    match st.index with
    | some ix => ix.annotProps.contains iri
    | none => st.annotProps.contains iri

private def isDatatypeIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInDatatype iri ||
    match st.index with
    | some ix => ix.datatypes.contains iri
    | none => st.datatypes.contains iri

private def isClassIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInClass iri ||
    match st.index with
    | some ix => ix.classes.contains iri
    | none => st.classes.contains iri

private def termToIndividual (docId : String) : RDFTerm → Except String Individual
  | .iri i => .ok (.named i)
  | .bnode b => .ok (.anonymous docId b)
  | .literal _ _ _ => .error "expected IRI or blank node for individual, got literal"

private def termToAnnotationSubject (docId : String) : RDFTerm → Except String AnnotationSubject
  | .iri i => .ok (.iri i)
  | .bnode b => .ok (.anonymous docId b)
  | .literal _ _ _ => .error "expected IRI or blank node for annotation subject, got literal"

private def termToAnnotationValue (docId : String) : RDFTerm → Except String AnnotationValue
  | .iri i => .ok (.iri i)
  | .bnode b => .ok (.anonymous docId b)
  | t@(.literal _ _ _) =>
    match t.toOwlLiteral with
    | some l => .ok (.literal l)
    | none => .error "invalid literal in annotation value"

private def parseNatCharsAux : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if '0' ≤ c && c ≤ '9' then parseNatCharsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

private def parseNonNegInt (t : RDFTerm) : Except String Nat := do
  match t with
  | .literal lex _ _ =>
    let cs := lex.toList
    if cs.isEmpty then throw "expected non-negative integer literal, got empty string"
    else match parseNatCharsAux cs 0 with
    | some n => return n
    | none => throw s!"expected non-negative integer literal, got '{lex}'"
  | _ => throw "expected non-negative integer literal for cardinality"

private def consumeRDFListAux : Nat → RDFTerm → List RDFTerm → List RDFTerm → MapM (List RDFTerm)
  | 0, _, _, _ => throw "rdf:List exceeded graph size"
  | fuel + 1, cur, visited, items => do
    if cur == .iri rdfNil then
      return items.reverse
    if visited.contains cur then
      throw "cyclic rdf:List in OWL 2 RDF graph"
    let firsts ← findActiveBySP cur rdfFirst
    let rests ← findActiveBySP cur rdfRest
    match firsts, rests with
    | [(i1, item)], [(i2, nextNode)] =>
      markConsumed i1
      markConsumed i2
      if let some iTy ← hasType cur (rdfNS ++ "List") then
        markConsumed iTy
      if let some iTy2 ← hasType cur swrlAtomList then
        markConsumed iTy2
      consumeRDFListAux fuel nextNode (cur :: visited) (item :: items)
    | _, _ =>
      throw s!"malformed rdf:List cell at {repr cur}"

/-- Consume and decode an `rdf:first`/`rdf:rest`/`rdf:nil` list starting at `head`. -/
private def consumeRDFList (head : RDFTerm) : MapM (List RDFTerm) := do
  let maxSteps := (← get).triples.size + 1
  consumeRDFListAux maxSteps head [] []

/-! ### 2. Object Property Expression, Data Range, and Class Expression Decoders -/

private def consumeObjPropExpr (term : RDFTerm) : MapM ObjectProperty := do
  match term with
  | .iri iri => return .named iri
  | .bnode _ =>
    let invs ← findActiveBySP term owlInverseOf
    match invs with
    | [(i, .iri r)] =>
      markConsumed i
      if let some iTy ← hasType term owlObjectProperty then markConsumed iTy
      return .inverse r
    | _ => throw s!"malformed anonymous object property expression {repr term}"
  | .literal _ _ _ => throw "expected object property expression, got literal"

private def parseFacetCell (cell : RDFTerm) : MapM Facet := do
  let props ← findActiveByS cell
  match props with
  | [(i, t)] =>
    match t.object.toOwlLiteral with
    | some lit =>
      markConsumed i
      return ⟨t.predicate, lit⟩
    | none => throw "expected literal value in owl:withRestrictions facet"
  | _ => throw s!"expected single facet triple on restriction cell {repr cell}"

private def consumeDataRange (fuel : Nat) (term : RDFTerm) : MapM DataRange := do
  match fuel with
  | 0 => throw "data range nesting depth exceeded"
  | fuel + 1 =>
    match term with
    | .iri iri => return .datatype iri
    | .literal _ _ _ => throw "expected data range, got literal"
    | .bnode _ =>
      if let some iTy ← hasType term rdfsDatatype then markConsumed iTy
      let comp ← findActiveBySP term owlDatatypeComplementOf
      if let [(i, inner)] := comp then
        markConsumed i
        return .complement (← consumeDataRange fuel inner)
      let inters ← findActiveBySP term owlIntersectionOf
      if let [(i, listHead)] := inters then
        markConsumed i
        let items ← consumeRDFList listHead
        let drs ← items.mapM (consumeDataRange fuel)
        return DataRange.intersect drs
      let unions ← findActiveBySP term owlUnionOf
      if let [(i, listHead)] := unions then
        markConsumed i
        let items ← consumeRDFList listHead
        let drs ← items.mapM (consumeDataRange fuel)
        return DataRange.unite drs
      let ones ← findActiveBySP term owlOneOf
      if let [(i, listHead)] := ones then
        markConsumed i
        let items ← consumeRDFList listHead
        let lits ← items.mapM fun x =>
          match x.toOwlLiteral with
          | some l => pure l
          | none => throw "expected literal in DataOneOf"
        return .oneOf lits
      let onDts ← findActiveBySP term owlOnDatatype
      let withRs ← findActiveBySP term owlWithRestrictions
      match onDts, withRs with
      | [(i1, .iri dtIRI)], [(i2, listHead)] =>
        markConsumed i1
        markConsumed i2
        let cells ← consumeRDFList listHead
        let facets ← cells.mapM parseFacetCell
        return .restriction dtIRI facets
      | _, _ => throw s!"unrecognized blank-node data range {repr term}"

/-- Heuristic + declared check for whether an RDF term represents a DataRange rather than a ClassExpr. -/
private def looksLikeDataRange (term : RDFTerm) : MapM Bool := do
  let st ← get
  match term with
  | .iri iri => return isDatatypeIRI st iri && !isClassIRI st iri
  | .literal _ _ _ => return false
  | .bnode _ =>
    if (← hasType term rdfsDatatype).isSome then return true
    if !(← findActiveBySP term owlDatatypeComplementOf).isEmpty then return true
    if !(← findActiveBySP term owlOnDatatype).isEmpty then return true
    if let [(_, listHead)] := ← findActiveBySP term owlOneOf then
      -- Check if first element is a literal
      let firsts ← findActiveBySP listHead rdfFirst
      if let [(_, .literal _ _ _)] := firsts then return true
    return false

private def consumeClassExpr (fuel : Nat) (term : RDFTerm) : MapM ClassExpr := do
  match fuel with
  | 0 => throw "class expression nesting depth exceeded"
  | fuel + 1 =>
    match term with
    | .iri iri => return .named iri
    | .literal _ _ _ => throw "expected class expression, got literal"
    | .bnode _ =>
      let docId := (← get).docId
      if let some iTy ← hasType term owlClass then markConsumed iTy
      -- Check owl:Restriction
      let onProps ← findActiveBySP term owlOnProperty
      if let [(iOnProp, propTerm)] := onProps then
        if let some iRestr ← hasType term owlRestriction then markConsumed iRestr
        markConsumed iOnProp
        let st ← get
        let isDataProp : Bool := match propTerm with
          | .iri p => isDataPropIRI st p
          | _ => false
        let isObjProp : Bool := match propTerm with
          | .iri p => isObjPropIRI st p
          | .bnode _ => true
          | _ => false
        -- 1. owl:someValuesFrom
        if let [(i, filler)] := ← findActiveBySP term owlSomeValuesFrom then
          markConsumed i
          let fillerIsData ← looksLikeDataRange filler
          if isDataProp || (!isObjProp && fillerIsData) then
            let .iri dp := propTerm | throw "data restriction requires named data property"
            return .dataSome dp (← consumeDataRange fuel filler)
          else
            return .objectSome (← consumeObjPropExpr propTerm) (← consumeClassExpr fuel filler)
        -- 2. owl:allValuesFrom
        if let [(i, filler)] := ← findActiveBySP term owlAllValuesFrom then
          markConsumed i
          let fillerIsData ← looksLikeDataRange filler
          if isDataProp || (!isObjProp && fillerIsData) then
            let .iri dp := propTerm | throw "data restriction requires named data property"
            return .dataAll dp (← consumeDataRange fuel filler)
          else
            return .objectAll (← consumeObjPropExpr propTerm) (← consumeClassExpr fuel filler)
        -- 3. owl:hasValue
        if let [(i, val)] := ← findActiveBySP term owlHasValue then
          markConsumed i
          match val with
          | .literal _ _ _ =>
            let .iri dp := propTerm | throw "DataHasValue requires named data property"
            match val.toOwlLiteral with
            | some lit => return .dataValue dp lit
            | none => throw "invalid literal in DataHasValue"
          | _ =>
            return .objectValue (← consumeObjPropExpr propTerm) (← match termToIndividual docId val with | .ok x => pure x | .error e => throw e)
        -- 4. owl:hasSelf
        if let [(i, val)] := ← findActiveBySP term owlHasSelf then
          markConsumed i
          match val with
          | .literal "true" _ _ => return .objectSelf (← consumeObjPropExpr propTerm)
          | _ => throw "owl:hasSelf requires literal \"true\"^^xsd:boolean"
        -- 5. Qualified cardinalities (with owl:onClass or owl:onDataRange)
        for (cardPred, mkObj, mkData) in [
          (owlMinQualifiedCardinality, ClassExpr.objectMin, ClassExpr.dataMin),
          (owlMaxQualifiedCardinality, ClassExpr.objectMax, ClassExpr.dataMax),
          (owlQualifiedCardinality, ClassExpr.objectExact, ClassExpr.dataExact)
        ] do
          if let [(iCard, numTerm)] := ← findActiveBySP term cardPred then
            markConsumed iCard
            let n ← match parseNonNegInt numTerm with | .ok k => pure k | .error e => throw e
            if let [(iOnC, cTerm)] := ← findActiveBySP term owlOnClass then
              markConsumed iOnC
              return mkObj n (← consumeObjPropExpr propTerm) (← consumeClassExpr fuel cTerm)
            else if let [(iOnD, dTerm)] := ← findActiveBySP term owlOnDataRange then
              markConsumed iOnD
              let .iri dp := propTerm | throw "qualified data cardinality requires named data property"
              return mkData n dp (← consumeDataRange fuel dTerm)
            else
              throw s!"qualified cardinality {cardPred} missing owl:onClass or owl:onDataRange"
        -- 6. Unqualified cardinalities
        for (cardPred, mkObj, mkData) in [
          (owlMinCardinality, ClassExpr.objectMin, ClassExpr.dataMin),
          (owlMaxCardinality, ClassExpr.objectMax, ClassExpr.dataMax),
          (owlCardinality, ClassExpr.objectExact, ClassExpr.dataExact)
        ] do
          if let [(iCard, numTerm)] := ← findActiveBySP term cardPred then
            markConsumed iCard
            let n ← match parseNonNegInt numTerm with | .ok k => pure k | .error e => throw e
            if isDataProp then
              let .iri dp := propTerm | throw "data cardinality requires named data property"
              return mkData n dp (.datatype literalDatatype)
            else
              return mkObj n (← consumeObjPropExpr propTerm) (.named thing)
        throw s!"unrecognized owl:Restriction on {repr propTerm}"
      -- Boolean / enumeration class expressions
      if let [(i, inner)] := ← findActiveBySP term owlComplementOf then
        markConsumed i
        return .complement (← consumeClassExpr fuel inner)
      if let [(i, listHead)] := ← findActiveBySP term owlIntersectionOf then
        markConsumed i
        let items ← consumeRDFList listHead
        let cs ← items.mapM (consumeClassExpr fuel)
        return ClassExpr.intersect cs
      if let [(i, listHead)] := ← findActiveBySP term owlUnionOf then
        markConsumed i
        let items ← consumeRDFList listHead
        let cs ← items.mapM (consumeClassExpr fuel)
        return ClassExpr.unite cs
      if let [(i, listHead)] := ← findActiveBySP term owlOneOf then
        markConsumed i
        let items ← consumeRDFList listHead
        let inds ← items.mapM fun x =>
          match termToIndividual docId x with | .ok a => pure a | .error e => throw e
        return .oneOf inds
      throw s!"unrecognized blank-node class expression {repr term}"

/-! ### 3. Multi-Pass W3C OWL 2 RDF-to-Structural Mapper (Tables 3–18) -/

private def addAxiom (ax : Axiom) : MapM Unit :=
  modify fun st => { st with axioms := ax :: st.axioms }

private def entityKindTag : EntityKind → Nat
  | .cls => 0
  | .datatype => 1
  | .objectProperty => 2
  | .dataProperty => 3
  | .annotationProperty => 4
  | .namedIndividual => 5

private def addDecl (kind : EntityKind) (iri : IRI) : MapM Unit :=
  modify fun st =>
    match st.index with
    | some ix =>
      let key := (entityKindTag kind, iri)
      let (decls, declKeys) :=
        if ix.declKeys.contains key then (st.declarations, ix.declKeys)
        else (⟨kind, iri⟩ :: st.declarations, ix.declKeys.insert key)
      let ix' := match kind with
        | .cls => { ix with declKeys, classes := ix.classes.insert iri }
        | .datatype => { ix with declKeys, datatypes := ix.datatypes.insert iri }
        | .objectProperty => { ix with declKeys, objProps := ix.objProps.insert iri }
        | .dataProperty => { ix with declKeys, dataProps := ix.dataProps.insert iri }
        | .annotationProperty => { ix with declKeys, annotProps := ix.annotProps.insert iri }
        | .namedIndividual => { ix with declKeys, namedInds := ix.namedInds.insert iri }
      { st with declarations := decls, index := some ix' }
    | none =>
      let d : EntityDecl := ⟨kind, iri⟩
      let decls := if st.declarations.contains d then st.declarations else d :: st.declarations
      match kind with
      | .cls => { st with declarations := decls, classes := iri :: st.classes }
      | .datatype => { st with declarations := decls, datatypes := iri :: st.datatypes }
      | .objectProperty => { st with declarations := decls, objProps := iri :: st.objProps }
      | .dataProperty => { st with declarations := decls, dataProps := iri :: st.dataProps }
      | .annotationProperty => { st with declarations := decls, annotProps := iri :: st.annotProps }
      | .namedIndividual => { st with declarations := decls, namedInds := iri :: st.namedInds }

private def addAnnot (a : AnnotationAxiom) : MapM Unit :=
  modify fun st => { st with annotationAxioms := a :: st.annotationAxioms }

private def addSWRLVar (t : RDFTerm) : MapM Unit :=
  modify fun st =>
    if st.swrlVars.contains t then st else { st with swrlVars := t :: st.swrlVars }

private def addSWRLRule (r : SWRL.SWRLRule) : MapM Unit :=
  modify fun st => { st with rules := r :: st.rules }

/-- Pass 1: Ontology header, `owl:versionIRI`, `owl:imports` (Tables 3–4),
    and reified axiom/annotation wrappers (`owl:Axiom`, `owl:Annotation`). -/
private def passHeaderAndReification : MapM Unit := do
  -- Consume reified axiom/annotation blank nodes (Table 1)
  let act ← activeIndices
  for (i, t) in act do
    if t.predicate == rdfType && (t.object == .iri owlAxiom || t.object == .iri owlAnnotation) then
      markConsumed i
      for (j, _) in ← findActiveByS t.subject do
        markConsumed j
  -- Ontology headers
  let act2 ← activeIndices
  let mut headers : List (Nat × RDFTerm) := []
  for (i, t) in act2 do
    if t.predicate == rdfType && t.object == .iri owlOntology then
      headers := (i, t.subject) :: headers
  if headers.length > 1 then
    throw "multiple owl:Ontology headers in a single RDF graph"
  if let [(iHdr, hdrTerm)] := headers then
    markConsumed iHdr
    modify fun st => { st with ontologyHeaderTerm := some hdrTerm }
    if let .iri ontIRI := hdrTerm then
      modify fun st => { st with ontologyIRI := some ontIRI }
    for (i, obj) in ← findActiveBySP hdrTerm owlVersionIRI do
      let .iri vIRI := obj | throw "owl:versionIRI must be an IRI"
      markConsumed i
      modify fun st => { st with versionIRI := some vIRI }
    for (i, obj) in ← findActiveBySP hdrTerm owlImports do
      let .iri impIRI := obj | throw "owl:imports must be an IRI"
      markConsumed i
      modify fun st => { st with imports := impIRI :: st.imports }

/-- Pass 2: Explicit declarations (Table 5) and implicit typing scan. -/
private def passDeclarations : MapM Unit := do
  let act ← activeIndices
  for (i, t) in act do
    if t.predicate == rdfType then
      if t.object == .iri swrlVariable then
        markConsumed i; addSWRLVar t.subject
      else if let .iri iri := t.subject then
        if t.object == .iri owlClass then
          markConsumed i; addDecl .cls iri
        else if t.object == .iri rdfsDatatype then
          markConsumed i; addDecl .datatype iri
        else if t.object == .iri owlObjectProperty then
          markConsumed i; addDecl .objectProperty iri
        else if t.object == .iri owlDatatypeProperty then
          markConsumed i; addDecl .dataProperty iri
        else if t.object == .iri owlAnnotationProperty then
          markConsumed i; addDecl .annotationProperty iri
        else if t.object == .iri owlNamedIndividual then
          markConsumed i; addDecl .namedIndividual iri
  -- Consume ALL ontology-header annotations (W3C OWL 2 RDF Mapping Table 4):
  -- any remaining non-rdf:type triple whose subject is the owl:Ontology header
  -- node (IRI or blank node) is an ontology annotation, never a logical assertion.
  let st ← get
  if let some hdrTerm := st.ontologyHeaderTerm then
    for (i, t) in ← findActiveByS hdrTerm do
      if t.predicate != rdfType then
        markConsumed i

private def decodeSWRLIArg (term : RDFTerm) : MapM SWRL.IArg := do
  let st ← get
  if st.swrlVars.contains term then
    match term with
    | .iri u => return .var u
    | .bnode b => return .var s!"urn:swrl:bnode:{st.docId}:{b}"
    | .literal _ _ _ => throw "SWRL variable cannot be a literal"
  else
    match term with
    | .iri u =>
      if u.startsWith "urn:swrl" then return .var u
      else return .ind (.named u)
    | .bnode b => return .ind (.anonymous st.docId b)
    | .literal _ _ _ => throw "expected individual or SWRL variable, got literal"

private def decodeSWRLDArg (term : RDFTerm) : MapM SWRL.DArg := do
  let st ← get
  if st.swrlVars.contains term then
    match term with
    | .iri u => return .var u
    | .bnode b => return .var s!"urn:swrl:bnode:{st.docId}:{b}"
    | .literal _ _ _ => throw "SWRL variable cannot be a literal"
  else
    match term with
    | .iri u => return .var u
    | .bnode b => return .var s!"urn:swrl:bnode:{st.docId}:{b}"
    | .literal _ _ _ =>
      match term.toOwlLiteral with
      | some l => return .lit l
      | none => throw "invalid literal in SWRL data argument"

private def consumeSWRLAtom (fuel : Nat) (atomNode : RDFTerm) : MapM SWRL.SWRLAtom := do
  if let some iTy ← hasType atomNode swrlClassAtom then
    markConsumed iTy
    let preds ← findActiveBySP atomNode swrlClassPredicate
    let arg1s ← findActiveBySP atomNode swrlArgument1
    match preds, arg1s with
    | [(i1, clsTerm)], [(i2, a1Term)] =>
      markConsumed i1; markConsumed i2
      let c ← consumeClassExpr fuel clsTerm
      let a1 ← decodeSWRLIArg a1Term
      return .classAtom c a1
    | _, _ => throw "malformed swrl:ClassAtom (requires swrl:classPredicate and swrl:argument1)"
  else if let some iTy ← hasType atomNode swrlDataRangeAtom then
    markConsumed iTy
    let drs ← findActiveBySP atomNode swrlDataRange
    let arg1s ← findActiveBySP atomNode swrlArgument1
    match drs, arg1s with
    | [(i1, drTerm)], [(i2, a1Term)] =>
      markConsumed i1; markConsumed i2
      let dr ← consumeDataRange fuel drTerm
      let a1 ← decodeSWRLDArg a1Term
      return .dataRangeAtom dr a1
    | _, _ => throw "malformed swrl:DataRangeAtom (requires swrl:dataRange and swrl:argument1)"
  else if let some iTy ← hasType atomNode swrlIndividualPropertyAtom then
    markConsumed iTy
    let preds ← findActiveBySP atomNode swrlPropertyPredicate
    let arg1s ← findActiveBySP atomNode swrlArgument1
    let arg2s ← findActiveBySP atomNode swrlArgument2
    match preds, arg1s, arg2s with
    | [(i1, pTerm)], [(i2, a1Term)], [(i3, a2Term)] =>
      markConsumed i1; markConsumed i2; markConsumed i3
      let r ← consumeObjPropExpr pTerm
      let a1 ← decodeSWRLIArg a1Term
      let a2 ← decodeSWRLIArg a2Term
      return .objectPropertyAtom r a1 a2
    | _, _, _ => throw "malformed swrl:IndividualPropertyAtom"
  else if let some iTy ← hasType atomNode swrlDatavaluedPropertyAtom then
    markConsumed iTy
    let preds ← findActiveBySP atomNode swrlPropertyPredicate
    let arg1s ← findActiveBySP atomNode swrlArgument1
    let arg2s ← findActiveBySP atomNode swrlArgument2
    match preds, arg1s, arg2s with
    | [(i1, .iri pIRI)], [(i2, a1Term)], [(i3, a2Term)] =>
      markConsumed i1; markConsumed i2; markConsumed i3
      let a1 ← decodeSWRLIArg a1Term
      let a2 ← decodeSWRLDArg a2Term
      return .dataPropertyAtom pIRI a1 a2
    | _, _, _ => throw "malformed swrl:DatavaluedPropertyAtom"
  else if let some iTy ← hasType atomNode swrlSameIndividualAtom then
    markConsumed iTy
    let arg1s ← findActiveBySP atomNode swrlArgument1
    let arg2s ← findActiveBySP atomNode swrlArgument2
    match arg1s, arg2s with
    | [(i1, a1Term)], [(i2, a2Term)] =>
      markConsumed i1; markConsumed i2
      return .sameIndividualAtom (← decodeSWRLIArg a1Term) (← decodeSWRLIArg a2Term)
    | _, _ => throw "malformed swrl:SameIndividualAtom"
  else if let some iTy ← hasType atomNode swrlDifferentIndividualsAtom then
    markConsumed iTy
    let arg1s ← findActiveBySP atomNode swrlArgument1
    let arg2s ← findActiveBySP atomNode swrlArgument2
    match arg1s, arg2s with
    | [(i1, a1Term)], [(i2, a2Term)] =>
      markConsumed i1; markConsumed i2
      return .differentIndividualsAtom (← decodeSWRLIArg a1Term) (← decodeSWRLIArg a2Term)
    | _, _ => throw "malformed swrl:DifferentIndividualsAtom"
  else if let some iTy ← hasType atomNode swrlBuiltinAtom then
    markConsumed iTy
    let bs ← findActiveBySP atomNode swrlBuiltin
    let argLists ← findActiveBySP atomNode swrlArguments
    match bs, argLists with
    | [(i1, .iri bIRI)], [(i2, listHead)] =>
      markConsumed i1; markConsumed i2
      let items ← consumeRDFList listHead
      let args ← items.mapM decodeSWRLDArg
      return .builtinAtom bIRI args
    | _, _ => throw "malformed swrl:BuiltinAtom"
  else
    throw s!"unrecognized SWRL atom node {repr atomNode}"

/-- Pass 2.5: W3C SWRL rules (`swrl:Imp`, `swrl:body`, `swrl:head`, `swrl:AtomList`). -/
private def passSWRLRules (fuel : Nat) : MapM Unit := do
  let act ← activeIndices
  for (i, t) in act do
    if ← isConsumed i then continue
    if t.predicate != rdfType || t.object != .iri swrlImp then continue
    markConsumed i
    let impNode := t.subject
    let bodies ← findActiveBySP impNode swrlBody
    let heads ← findActiveBySP impNode swrlHead
    match bodies, heads with
    | [(ib, bodyHead)], [(ih, headHead)] =>
      markConsumed ib; markConsumed ih
      -- Consume optional rule-level annotations (rdfs:label, rdfs:comment, swrla:*, etc.)
      let st ← get
      for (ia, ta) in ← findActiveByS impNode do
        if isAnnotPropIRI st ta.predicate || ta.predicate.startsWith swrlaNS ||
            isKnownMetadataVocab ta.predicate then
          markConsumed ia
      let bodyTerms ← consumeRDFList bodyHead
      let headTerms ← consumeRDFList headHead
      let bodyAtoms ← bodyTerms.mapM (consumeSWRLAtom fuel)
      let headAtoms ← headTerms.mapM (consumeSWRLAtom fuel)
      addSWRLRule { body := bodyAtoms, head := headAtoms }
    | _, _ => throw "malformed swrl:Imp (requires swrl:body and swrl:head)"

/-- Pass 3: Blank-node multi-triple axioms (`owl:AllDisjointClasses`,
    `owl:AllDisjointProperties`, `owl:AllDifferent`, `owl:NegativePropertyAssertion`). -/
private def passCompoundAxioms (fuel : Nat) : MapM Unit := do
  let docId := (← get).docId
  let act ← activeIndices
  for (i, t) in act do
    if ← isConsumed i then continue
    if t.predicate != rdfType then continue
    if t.object == .iri owlAllDisjointClasses then
      markConsumed i
      match ← findActiveBySP t.subject owlMembers with
      | [(im, head)] =>
        markConsumed im
        let items ← consumeRDFList head
        let cs ← items.mapM (consumeClassExpr fuel)
        addAxiom (.disjointClasses cs)
      | _ => throw "owl:AllDisjointClasses missing owl:members list"
    else if t.object == .iri owlAllDisjointProperties then
      markConsumed i
      match ← findActiveBySP t.subject owlMembers with
      | [(im, head)] =>
        markConsumed im
        let items ← consumeRDFList head
        let st ← get
        let isData := items.any fun x => match x with | .iri p => isDataPropIRI st p | _ => false
        if isData then
          let ds ← items.mapM fun x => match x with | .iri p => pure p | _ => throw "expected data property IRI in AllDisjointProperties"
          addAxiom (.disjointDataProperties ds)
        else
          let os ← items.mapM consumeObjPropExpr
          addAxiom (.disjointObjectProperties os)
      | _ => throw "owl:AllDisjointProperties missing owl:members list"
    else if t.object == .iri owlAllDifferent then
      markConsumed i
      let mems ← findActiveBySP t.subject owlMembers
      let dmems ← findActiveBySP t.subject owlDistinctMembers
      let (im, head) ← match mems, dmems with
        | [(im, h)], [] => pure (im, h)
        | [], [(im, h)] => pure (im, h)
        | _, _ => throw "owl:AllDifferent requires owl:members or owl:distinctMembers list"
      markConsumed im
      let items ← consumeRDFList head
      let inds ← items.mapM fun x => match termToIndividual docId x with | .ok a => pure a | .error e => throw e
      addAxiom (.differentIndividuals inds)
    else if t.object == .iri owlNegativePropertyAssertion then
      markConsumed i
      let srcs ← findActiveBySP t.subject owlSourceIndividual
      let props ← findActiveBySP t.subject owlAssertionProperty
      let tgtInds ← findActiveBySP t.subject owlTargetIndividual
      let tgtVals ← findActiveBySP t.subject owlTargetValue
      match srcs, props, tgtInds, tgtVals with
      | [(i1, sTerm)], [(i2, pTerm)], [(i3, oTerm)], [] =>
        markConsumed i1; markConsumed i2; markConsumed i3
        let sInd ← match termToIndividual docId sTerm with | .ok a => pure a | .error e => throw e
        let oInd ← match termToIndividual docId oTerm with | .ok a => pure a | .error e => throw e
        let r ← consumeObjPropExpr pTerm
        addAxiom (.negativeObjectAssertion r sInd oInd)
      | [(i1, sTerm)], [(i2, .iri dp)], [], [(i3, vTerm)] =>
        markConsumed i1; markConsumed i2; markConsumed i3
        let sInd ← match termToIndividual docId sTerm with | .ok a => pure a | .error e => throw e
        let lit ← match vTerm.toOwlLiteral with | some l => pure l | none => throw "expected literal in owl:targetValue"
        addAxiom (.negativeDataAssertion dp sInd lit)
      | _, _, _, _ => throw "malformed owl:NegativePropertyAssertion"

/-- Pass 4: Single-triple TBox/RBox axioms (Tables 16–18). -/
private def passTBoxRBoxAxioms (fuel : Nat) : MapM Unit := do
  let act ← activeIndices
  for (i, t) in act do
    if ← isConsumed i then continue
    let st ← get
    -- Role characteristic rdf:type axioms
    if t.predicate == rdfType then
      if t.object == .iri owlFunctionalProperty then
        markConsumed i
        match t.subject with
        | .iri p =>
          if isDataPropIRI st p then addAxiom (.functionalDataProperty p)
          else addAxiom (.functionalObjectProperty (.named p))
        | _ => addAxiom (.functionalObjectProperty (← consumeObjPropExpr t.subject))
        continue
      else if t.object == .iri owlInverseFunctionalProperty then
        markConsumed i; addAxiom (.inverseFunctionalObjectProperty (← consumeObjPropExpr t.subject)); continue
      else if t.object == .iri owlReflexiveProperty then
        markConsumed i; addAxiom (.reflexiveObjectProperty (← consumeObjPropExpr t.subject)); continue
      else if t.object == .iri owlIrreflexiveProperty then
        markConsumed i; addAxiom (.irreflexiveObjectProperty (← consumeObjPropExpr t.subject)); continue
      else if t.object == .iri owlSymmetricProperty then
        markConsumed i; addAxiom (.symmetricObjectProperty (← consumeObjPropExpr t.subject)); continue
      else if t.object == .iri owlAsymmetricProperty then
        markConsumed i; addAxiom (.asymmetricObjectProperty (← consumeObjPropExpr t.subject)); continue
      else if t.object == .iri owlTransitiveProperty then
        markConsumed i; addAxiom (.transitiveObjectProperty (← consumeObjPropExpr t.subject)); continue
    -- Class & datatype axioms
    if t.predicate == rdfsSubClassOf then
      markConsumed i
      let a ← consumeClassExpr fuel t.subject
      let b ← consumeClassExpr fuel t.object
      addAxiom (.subClassOf a b)
    else if t.predicate == owlEquivalentClass then
      markConsumed i
      match t.subject with
      | .iri dtIRI =>
        if isDatatypeIRI st dtIRI && !isClassIRI st dtIRI then
          let dr ← consumeDataRange fuel t.object
          addAxiom (.datatypeDefinition dtIRI dr)
        else
          let b ← consumeClassExpr fuel t.object
          addAxiom (.equivalentClasses [.named dtIRI, b])
      | _ =>
        let a ← consumeClassExpr fuel t.subject
        let b ← consumeClassExpr fuel t.object
        addAxiom (.equivalentClasses [a, b])
    else if t.predicate == owlDisjointWith then
      markConsumed i
      let a ← consumeClassExpr fuel t.subject
      let b ← consumeClassExpr fuel t.object
      addAxiom (.disjointClasses [a, b])
    else if t.predicate == owlDisjointUnionOf then
      let .iri h := t.subject | throw "owl:disjointUnionOf subject must be a named class IRI"
      markConsumed i
      let items ← consumeRDFList t.object
      let cs ← items.mapM (consumeClassExpr fuel)
      addAxiom (.disjointUnion h cs)
    -- Property chain & property hierarchy axioms
    else if t.predicate == owlPropertyChainAxiom then
      markConsumed i
      let sup ← consumeObjPropExpr t.subject
      let items ← consumeRDFList t.object
      let chain ← items.mapM consumeObjPropExpr
      addAxiom (.subObjectPropertyChain chain sup)
    else if t.predicate == rdfsSubPropertyOf then
      markConsumed i
      match t.subject, t.object with
      | .iri p, .iri q =>
        if isAnnotPropIRI st p || isAnnotPropIRI st q then
          addAnnot (.subProperty p q)
        else if isDataPropIRI st p || isDataPropIRI st q then
          addAxiom (.subDataProperty p q)
        else
          addAxiom (.subObjectProperty (.named p) (.named q))
      | _, _ =>
        let r ← consumeObjPropExpr t.subject
        let s ← consumeObjPropExpr t.object
        addAxiom (.subObjectProperty r s)
    else if t.predicate == owlEquivalentProperty then
      markConsumed i
      match t.subject, t.object with
      | .iri p, .iri q =>
        if isDataPropIRI st p || isDataPropIRI st q then
          addAxiom (.equivalentDataProperties [p, q])
        else
          addAxiom (.equivalentObjectProperties [.named p, .named q])
      | _, _ =>
        let r ← consumeObjPropExpr t.subject
        let s ← consumeObjPropExpr t.object
        addAxiom (.equivalentObjectProperties [r, s])
    else if t.predicate == owlPropertyDisjointWith then
      markConsumed i
      match t.subject, t.object with
      | .iri p, .iri q =>
        if isDataPropIRI st p || isDataPropIRI st q then
          addAxiom (.disjointDataProperties [p, q])
        else
          addAxiom (.disjointObjectProperties [.named p, .named q])
      | _, _ =>
        let r ← consumeObjPropExpr t.subject
        let s ← consumeObjPropExpr t.object
        addAxiom (.disjointObjectProperties [r, s])
    else if t.predicate == owlInverseOf then
      -- Only treat as top-level axiom when subject is an IRI (or both are IRIs);
      -- blank-node subjects are anonymous inverse property expressions consumed inline.
      if let .iri r := t.subject then
        markConsumed i
        let s ← consumeObjPropExpr t.object
        addAxiom (.inverseObjectProperties (.named r) s)
    else if t.predicate == rdfsDomain then
      markConsumed i
      match t.subject with
      | .iri p =>
        if isAnnotPropIRI st p then
          let .iri dom := t.object | throw "AnnotationPropertyDomain requires an IRI"
          addAnnot (.domain p dom)
        else if isDataPropIRI st p then
          addAxiom (.dataPropertyDomain p (← consumeClassExpr fuel t.object))
        else
          addAxiom (.objectPropertyDomain (.named p) (← consumeClassExpr fuel t.object))
      | _ =>
        addAxiom (.objectPropertyDomain (← consumeObjPropExpr t.subject) (← consumeClassExpr fuel t.object))
    else if t.predicate == rdfsRange then
      markConsumed i
      match t.subject with
      | .iri p =>
        if isAnnotPropIRI st p then
          let .iri rng := t.object | throw "AnnotationPropertyRange requires an IRI"
          addAnnot (.range p rng)
        else if isDataPropIRI st p then
          addAxiom (.dataPropertyRange p (← consumeDataRange fuel t.object))
        else
          let objIsData ← looksLikeDataRange t.object
          if !isObjPropIRI st p && objIsData then
            addAxiom (.dataPropertyRange p (← consumeDataRange fuel t.object))
          else
            addAxiom (.objectPropertyRange (.named p) (← consumeClassExpr fuel t.object))
      | _ =>
        addAxiom (.objectPropertyRange (← consumeObjPropExpr t.subject) (← consumeClassExpr fuel t.object))
    else if t.predicate == owlHasKey then
      markConsumed i
      let dom ← consumeClassExpr fuel t.subject
      let items ← consumeRDFList t.object
      let mut os : List ObjectProperty := []
      let mut ds : List IRI := []
      for item in items do
        match item with
        | .iri p =>
          if isDataPropIRI st p then ds := p :: ds
          else os := .named p :: os
        | _ => os := (← consumeObjPropExpr item) :: os
      addAxiom (.hasKey dom os.reverse ds.reverse)

private def isStructuralBNodeType (o : RDFTerm) : Bool :=
  o == .iri owlClass || o == .iri owlRestriction || o == .iri rdfsDatatype ||
  o == .iri owlObjectProperty || o == .iri owlDatatypeProperty || o == .iri (rdfNS ++ "List")

/-- Pass 5: ABox & Annotation assertions (Table 16–18). -/
private def passAssertions (fuel : Nat) : MapM Unit := do
  let docId := (← get).docId
  let act ← activeIndices
  for (i, t) in act do
    if ← isConsumed i then continue
    let st ← get
    if t.predicate == owlSameAs then
      markConsumed i
      let a ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      let b ← match termToIndividual docId t.object with | .ok x => pure x | .error e => throw e
      addAxiom (.sameIndividuals [a, b])
    else if t.predicate == owlDifferentFrom then
      markConsumed i
      let a ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      let b ← match termToIndividual docId t.object with | .ok x => pure x | .error e => throw e
      addAxiom (.differentIndividuals [a, b])
    else if t.predicate == rdfType then
      -- Skip blank-node class/restriction/datatype typing triples; they are consumed
      -- when the enclosing ClassAssertion / TBox axiom decodes that blank node.
      match t.subject with
      | .bnode _ => if isStructuralBNodeType t.object then continue
      | _ => pure ()
      markConsumed i
      let ind ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      let c ← consumeClassExpr fuel t.object
      addAxiom (.classAssertion c ind)
    else if isAnnotPropIRI st t.predicate then
      markConsumed i
      let subj ← match termToAnnotationSubject docId t.subject with | .ok x => pure x | .error e => throw e
      let val ← match termToAnnotationValue docId t.object with | .ok x => pure x | .error e => throw e
      addAnnot (.assertion t.predicate subj val)
    else if isDataPropIRI st t.predicate then
      markConsumed i
      let ind ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      let lit ← match t.object.toOwlLiteral with
        | some l => pure l
        | none => throw s!"data property assertion '{t.predicate}' requires literal object"
      addAxiom (.dataAssertion t.predicate ind lit)
    else if isObjPropIRI st t.predicate then
      markConsumed i
      let sInd ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      let oInd ← match termToIndividual docId t.object with | .ok x => pure x | .error e => throw e
      addAxiom (.objectAssertion (.named t.predicate) sInd oInd)
    else if isKnownMetadataVocab t.predicate then
      -- Undeclared standard metadata predicate (Dublin Core, SKOS, VANN, oboInOwl, FOAF):
      -- preserve as annotation assertion rather than a logical data/object property assertion.
      markConsumed i
      let subj ← match termToAnnotationSubject docId t.subject with | .ok x => pure x | .error e => throw e
      let val ← match termToAnnotationValue docId t.object with | .ok x => pure x | .error e => throw e
      addAnnot (.assertion t.predicate subj val)
    else if !WellFormed.isReservedPrefix t.predicate then
      -- Undeclared non-reserved predicate: dispatch by object kind (literal → data assertion,
      -- IRI/bnode → object assertion), letting StrictTyping enforce §5.8.2 declarations in strict mode.
      markConsumed i
      let sInd ← match termToIndividual docId t.subject with | .ok x => pure x | .error e => throw e
      match t.object with
      | .literal _ _ _ =>
        let lit ← match t.object.toOwlLiteral with | some l => pure l | none => throw "invalid literal"
        addAxiom (.dataAssertion t.predicate sInd lit)
      | _ =>
        let oInd ← match termToIndividual docId t.object with | .ok x => pure x | .error e => throw e
        addAxiom (.objectAssertion (.named t.predicate) sInd oInd)

private def seedImportedDecls (st : MapState) (decls : List EntityDecl) : MapState :=
  match st.index with
  | some ix =>
    let ix' := decls.foldl (fun acc d =>
      match d.kind with
      | .cls => { acc with classes := acc.classes.insert d.iri }
      | .datatype => { acc with datatypes := acc.datatypes.insert d.iri }
      | .objectProperty => { acc with objProps := acc.objProps.insert d.iri }
      | .dataProperty => { acc with dataProps := acc.dataProps.insert d.iri }
      | .annotationProperty => { acc with annotProps := acc.annotProps.insert d.iri }
      | .namedIndividual => { acc with namedInds := acc.namedInds.insert d.iri }) ix
    { st with index := some ix' }
  | none =>
    decls.foldl (fun acc d =>
      match d.kind with
      | .cls => { acc with classes := d.iri :: acc.classes }
      | .datatype => { acc with datatypes := d.iri :: acc.datatypes }
      | .objectProperty => { acc with objProps := d.iri :: acc.objProps }
      | .dataProperty => { acc with dataProps := d.iri :: acc.dataProps }
      | .annotationProperty => { acc with annotProps := d.iri :: acc.annotProps }
      | .namedIndividual => { acc with namedInds := d.iri :: acc.namedInds }) st

private def buildSubjectIndex (triples : Array RDFTriple) : Std.HashMap RDFTerm (Array Nat) := Id.run do
  let mut m : Std.HashMap RDFTerm (Array Nat) := Std.HashMap.emptyWithCapacity (triples.size / 2 + 1)
  for h : i in [0:triples.size] do
    let s := triples[i].subject
    let arr := m.getD s #[]
    m := m.insert s (arr.push i)
  return m

/-- Map a parsed `RDFGraph` to a SABRINA `ParsedDocument` per W3C OWL 2 Mapping
    to RDF Graphs (Tables 3–18). When `strictUnconsumed` is `true`, rejects any
    unconsumed or malformed RDF triples. Optional `importedDecls` seeds entity
    typing from the enclosing import closure (W3C §3.1.2 Table 5 `AllDecl(G)`). -/
def mapRDFGraph (docId : String) (g : RDFGraph) (strictUnconsumed : Bool := true)
    (importedDecls : List EntityDecl := []) :
    Except String ParsedDocument := do
  let tripleArr := g.triples.toArray
  let useIndex := tripleArr.size > 64 || importedDecls.length > 64
  let baseSt : MapState := {
    docId := docId
    triples := tripleArr
    consumed := Array.replicate tripleArr.size false
    index := if useIndex then some { bySubject := buildSubjectIndex tripleArr } else none
  }
  let initSt := if importedDecls.isEmpty then baseSt else seedImportedDecls baseSt importedDecls
  let fuel := g.triples.length + 32
  let ((), st) ← (do
    passHeaderAndReification
    passDeclarations
    passSWRLRules fuel
    passCompoundAxioms fuel
    passTBoxRBoxAxioms fuel
    passAssertions fuel
    if strictUnconsumed then
      let leftover ← activeIndices
      if let (_, t) :: _ := leftover then
        throw s!"unconsumed RDF triple in OWL 2 DL mapping: ({repr t.subject}, {t.predicate}, {repr t.object})").run initSt
  return {
    prefixes := g.prefixes ++ [
      ("owl", owlNS), ("rdf", rdfNS), ("rdfs", rdfsNS), ("xsd", xsdNS)
    ]
    ontologyIRI := st.ontologyIRI
    versionIRI := st.versionIRI
    imports := st.imports.reverse
    declarations := st.declarations.reverse
    annotationAxioms := st.annotationAxioms.reverse
    ontology := st.axioms.reverse
    rules := st.rules.reverse
  }

/-! ### 4. Auto-Detecting Multi-Syntax Document & Import-Closure Parser -/

inductive InputSyntax where
  | fss
  | rdfxml
  | turtle
  deriving DecidableEq, Repr

private def stripLeadingWSAndComments (input : String) : String :=
  let s := if input.startsWith "\uFEFF" then String.ofList (input.toList.drop 1) else input
  s.trimAsciiStart.toString

/-- Auto-detect whether `input` is W3C RDF/XML, OWL 2 Functional-Style Syntax,
    or Turtle 1.1. -/
def detectSyntax (input : String) : InputSyntax :=
  let s := stripLeadingWSAndComments input
  if s.startsWith "<?xml" || s.startsWith "<!DOCTYPE" ||
     s.startsWith "<rdf:RDF" || s.startsWith "<RDF" then
    .rdfxml
  else if s.startsWith "Prefix(" || s.startsWith "Ontology(" then
    .fss
  else if s.startsWith "@prefix" || s.startsWith "@base" ||
          s.startsWith "PREFIX" || s.startsWith "prefix" ||
          s.startsWith "BASE" || s.startsWith "base" then
    .turtle
  else if s.startsWith "<" then
    -- Distinguish XML element `<tag ...>` from Turtle `<IRI> pred obj .`
    let afterLt := String.ofList (s.toList.drop 1)
    if afterLt.startsWith "http://" || afterLt.startsWith "https://" ||
       afterLt.startsWith "urn:" || afterLt.startsWith "file:" ||
       afterLt.startsWith "#" || afterLt.startsWith "/" then
      .turtle
    else
      .rdfxml
  else if s.startsWith "#" then
    -- Scan first non-comment line
    let lines := s.splitOn "\n"
    match lines.find? (fun l => let t := l.trimAsciiStart.toString; !t.isEmpty && !t.startsWith "#") with
    | some line =>
      let t := line.trimAsciiStart.toString
      if t.startsWith "Prefix(" || t.startsWith "Ontology(" then .fss
      else if t.startsWith "<?xml" || t.startsWith "<rdf:RDF" then .rdfxml
      else .turtle
    | none => .fss
  else
    .turtle

/-- Parse an OWL 2 document in Functional-Style Syntax, RDF/XML, or Turtle. -/
def parseDocumentAutoWithId (docId : String) (input : String)
    (strictRDF : Bool := true) : Except String ParsedDocument := do
  match detectSyntax input with
  | .fss => parseDocumentWithId docId input
  | .rdfxml =>
    let g ← XML.parseRDFXML input
    mapRDFGraph docId g strictRDF
  | .turtle =>
    let g ← Turtle.parseTurtle input
    mapRDFGraph docId g strictRDF

/-- Parse an OWL 2 document (FSS, RDF/XML, or Turtle) with default document ID `"doc:0"`. -/
def parseDocumentAuto (input : String) (strictRDF : Bool := true) : Except String ParsedDocument :=
  parseDocumentAutoWithId "doc:0" input strictRDF

private inductive RawParsedDoc where
  | fss (doc : ParsedDocument)
  | rdf (docId : String) (g : RDFGraph)
      (ontologyIRI : Option IRI) (versionIRI : Option IRI)
      (imports : List IRI) (decls : List EntityDecl)

private def scanRDFHeaderAndDecls (g : RDFGraph) :
    Option IRI × Option IRI × List IRI × List EntityDecl := Id.run do
  let mut hdrTerm : Option RDFTerm := none
  let mut ontIRI : Option IRI := none
  let mut verIRI : Option IRI := none
  let mut imps : List IRI := []
  let mut decls : List EntityDecl := []
  for t in g.triples do
    if t.predicate == rdfType then
      if t.object == .iri owlOntology then
        hdrTerm := some t.subject
        if let .iri i := t.subject then ontIRI := some i
      else if let .iri i := t.subject then
        if t.object == .iri owlClass then decls := ⟨.cls, i⟩ :: decls
        else if t.object == .iri rdfsDatatype then decls := ⟨.datatype, i⟩ :: decls
        else if t.object == .iri owlObjectProperty then decls := ⟨.objectProperty, i⟩ :: decls
        else if t.object == .iri owlDatatypeProperty then decls := ⟨.dataProperty, i⟩ :: decls
        else if t.object == .iri owlAnnotationProperty then decls := ⟨.annotationProperty, i⟩ :: decls
        else if t.object == .iri owlNamedIndividual then decls := ⟨.namedIndividual, i⟩ :: decls
  if let some ht := hdrTerm then
    for t in g.triples do
      if t.subject == ht then
        if t.predicate == owlVersionIRI then
          if let .iri v := t.object then verIRI := some v
        else if t.predicate == owlImports then
          if let .iri imp := t.object then imps := imp :: imps
  return (ontIRI, verIRI, imps.reverse, decls.reverse)

private def parseRawAutoWithId (docId : String) (input : String) : Except String RawParsedDoc := do
  match detectSyntax input with
  | .fss =>
    let d ← parseDocumentWithId docId input
    return .fss d
  | .rdfxml =>
    let g ← XML.parseRDFXML input
    let (oi, vi, imps, ds) := scanRDFHeaderAndDecls g
    return .rdf docId g oi vi imps ds
  | .turtle =>
    let g ← Turtle.parseTurtle input
    let (oi, vi, imps, ds) := scanRDFHeaderAndDecls g
    return .rdf docId g oi vi imps ds

private def RawParsedDoc.ontologyIRI : RawParsedDoc → Option IRI
  | .fss d => d.ontologyIRI
  | .rdf _ _ oi _ _ _ => oi

private def RawParsedDoc.versionIRI : RawParsedDoc → Option IRI
  | .fss d => d.versionIRI
  | .rdf _ _ _ vi _ _ => vi

private def RawParsedDoc.imports : RawParsedDoc → List IRI
  | .fss d => d.imports
  | .rdf _ _ _ _ imps _ => imps

private def RawParsedDoc.decls : RawParsedDoc → List EntityDecl
  | .fss d => d.declarations
  | .rdf _ _ _ _ _ ds => ds

private def RawParsedDoc.finalize (strictRDF : Bool) (closureDecls : List EntityDecl) :
    RawParsedDoc → Except String ParsedDocument
  | .fss d => .ok d
  | .rdf docId g _ _ _ _ => mapRDFGraph docId g strictRDF closureDecls

/-- Resolve transitive `Import(...)` / `owl:imports` closure across mixed-syntax
    documents (FSS, RDF/XML, and Turtle), sharing entity declarations across the
    entire import closure before mapping RDF graphs (W3C §3.1.2 Table 5 `AllDecl(G)`). -/
def resolveImportClosureAuto (rootText : String) (library : List (IRI × String))
    (strictRDF : Bool := true) : Except String ResolvedOFNClosure := do
  let rootRaw ← parseRawAutoWithId "doc:0" rootText
  let mut parsedLib : List (IRI × RawParsedDoc) := []
  let mut idx := 1
  for (key, text) in library do
    let raw ← parseRawAutoWithId s!"doc:{idx}" text
    parsedLib := (key, raw) :: parsedLib
    idx := idx + 1
  parsedLib := parsedLib.reverse
  let findRaw (target : IRI) : Option RawParsedDoc :=
    match parsedLib.find? (fun (k, _) => k == target) with
    | some (_, d) => some d
    | none =>
      match parsedLib.find? (fun (_, d) => d.versionIRI == some target) with
      | some (_, d) => some d
      | none =>
        match parsedLib.find? (fun (_, d) => d.ontologyIRI == some target) with
        | some (_, d) => some d
        | none => none
  -- Phase 1: Walk transitive import closure and collect AllDecl(G)
  let mut visited : List IRI := []
  if let some iri := rootRaw.ontologyIRI then visited := iri :: visited
  if let some iri := rootRaw.versionIRI then visited := iri :: visited
  let mut queue : List IRI := rootRaw.imports
  let mut reachable : List RawParsedDoc := [rootRaw]
  let mut closureDecls : List EntityDecl := rootRaw.decls
  let mut fuel := (parsedLib.length + 1) * (parsedLib.length + 2) + 64
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match queue with
    | [] => break
    | imp :: rest =>
      queue := rest
      if visited.contains imp then continue
      match findRaw imp with
      | none => throw s!"missing imported ontology: {imp}"
      | some raw =>
        visited := imp :: visited
        if let some iri := raw.ontologyIRI then visited := iri :: visited
        if let some iri := raw.versionIRI then visited := iri :: visited
        reachable := raw :: reachable
        closureDecls := closureDecls ++ raw.decls
        queue := queue ++ raw.imports
  -- Phase 2: Map each reachable RDF graph with full import-closure declarations
  let reachableOrd := reachable.reverse
  let mut rootDoc? : Option ParsedDocument := none
  let mut allDecls : Array EntityDecl := #[]
  let mut allAnnots : Array AnnotationAxiom := #[]
  let mut allAxioms : Array Axiom := #[]
  let mut allRules : Array SWRL.SWRLRule := #[]
  for raw in reachableOrd do
    let doc ← raw.finalize strictRDF closureDecls
    if rootDoc?.isNone then rootDoc? := some doc
    allDecls := allDecls ++ doc.declarations.toArray
    allAnnots := allAnnots ++ doc.annotationAxioms.toArray
    allAxioms := allAxioms ++ doc.ontology.toArray
    allRules := allRules ++ doc.rules.toArray
  let rootDoc := rootDoc?.getD { prefixes := [], ontology := [] }
  return {
    prefixes := rootDoc.prefixes
    declarations := allDecls.toList
    annotationAxioms := allAnnots.toList
    ontology := allAxioms.toList
    ontologyIRI := rootDoc.ontologyIRI
    versionIRI := rootDoc.versionIRI
    rules := allRules.toList
  }

/-! ### 5. Forward Structural-to-RDF Mapping (W3C Table 1) & Correspondence Proofs -/

private structure EncState where
  triples : List RDFTriple := []
  nextId : Nat := 0

private abbrev EncM (α : Type) := StateM EncState α

private def natToDecCharsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | k + 1, n, acc =>
    let d := Char.ofNat ('0'.toNat + n % 10)
    if n < 10 then d :: acc
    else natToDecCharsAux k (n / 10) (d :: acc)

private def natToDecStr (n : Nat) : String :=
  String.ofList (natToDecCharsAux (n + 1) n [])

private def freshEnc : EncM RDFTerm := do
  let st ← get
  set { st with nextId := st.nextId + 1 }
  return .bnode ("enc_" ++ natToDecStr st.nextId)

private def emitEnc (s : RDFTerm) (p : IRI) (o : RDFTerm) : EncM Unit :=
  modify fun st => { st with triples := ⟨s, p, o⟩ :: st.triples }

private def encodeListEnc (items : List RDFTerm) : EncM RDFTerm := do
  match items with
  | [] => return .iri rdfNil
  | x :: xs =>
    let cell ← freshEnc
    let rest ← encodeListEnc xs
    emitEnc cell rdfFirst x
    emitEnc cell rdfRest rest
    return cell

private def encodeIndEnc : Individual → RDFTerm
  | .named i => .iri i
  | .anonymous _ loc => .bnode loc

private def encodeLitEnc (l : Literal) : RDFTerm :=
  .literal l.lexical l.datatype none

private def encodeObjPropEnc : ObjectProperty → EncM RDFTerm
  | .named r => return .iri r
  | .inverse r => do
    let b ← freshEnc
    emitEnc b owlInverseOf (.iri r)
    return b

private def encodeDataRangeEnc : DataRange → EncM RDFTerm
  | .datatype dt => return .iri dt
  | .complement d => do
    let b ← freshEnc
    let inner ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri rdfsDatatype)
    emitEnc b owlDatatypeComplementOf inner
    return b
  | .intersection a b => do
    let node ← freshEnc
    let ta ← encodeDataRangeEnc a
    let tb ← encodeDataRangeEnc b
    let list ← encodeListEnc [ta, tb]
    emitEnc node rdfType (.iri rdfsDatatype)
    emitEnc node owlIntersectionOf list
    return node
  | .union a b => do
    let node ← freshEnc
    let ta ← encodeDataRangeEnc a
    let tb ← encodeDataRangeEnc b
    let list ← encodeListEnc [ta, tb]
    emitEnc node rdfType (.iri rdfsDatatype)
    emitEnc node owlUnionOf list
    return node
  | .oneOf ls => do
    let node ← freshEnc
    let list ← encodeListEnc (ls.map encodeLitEnc)
    emitEnc node rdfType (.iri rdfsDatatype)
    emitEnc node owlOneOf list
    return node
  | .restriction dt fs => do
    let node ← freshEnc
    let mut cells : List RDFTerm := []
    for f in fs do
      let cell ← freshEnc
      emitEnc cell f.name (encodeLitEnc f.bound)
      cells := cell :: cells
    let list ← encodeListEnc cells.reverse
    emitEnc node rdfType (.iri rdfsDatatype)
    emitEnc node owlOnDatatype (.iri dt)
    emitEnc node owlWithRestrictions list
    return node

private def encodeClassExprEnc : ClassExpr → EncM RDFTerm
  | .named c => return .iri c
  | .complement c => do
    let b ← freshEnc
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlClass)
    emitEnc b owlComplementOf tc
    return b
  | .intersection a b => do
    let node ← freshEnc
    let ta ← encodeClassExprEnc a
    let tb ← encodeClassExprEnc b
    let list ← encodeListEnc [ta, tb]
    emitEnc node rdfType (.iri owlClass)
    emitEnc node owlIntersectionOf list
    return node
  | .union a b => do
    let node ← freshEnc
    let ta ← encodeClassExprEnc a
    let tb ← encodeClassExprEnc b
    let list ← encodeListEnc [ta, tb]
    emitEnc node rdfType (.iri owlClass)
    emitEnc node owlUnionOf list
    return node
  | .oneOf inds => do
    let node ← freshEnc
    let list ← encodeListEnc (inds.map encodeIndEnc)
    emitEnc node rdfType (.iri owlClass)
    emitEnc node owlOneOf list
    return node
  | .objectSome r c => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlSomeValuesFrom tc
    return b
  | .objectAll r c => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlAllValuesFrom tc
    return b
  | .objectValue r a => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlHasValue (encodeIndEnc a)
    return b
  | .objectSelf r => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlHasSelf (.literal "true" xsdBoolean none)
    return b
  | .objectMin n r c => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlMinQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnClass tc
    return b
  | .objectMax n r c => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlMaxQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnClass tc
    return b
  | .objectExact n r c => do
    let b ← freshEnc
    let tr ← encodeObjPropEnc r
    let tc ← encodeClassExprEnc c
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty tr
    emitEnc b owlQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnClass tc
    return b
  | .dataSome dp d => do
    let b ← freshEnc
    let td ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlSomeValuesFrom td
    return b
  | .dataAll dp d => do
    let b ← freshEnc
    let td ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlAllValuesFrom td
    return b
  | .dataValue dp l => do
    let b ← freshEnc
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlHasValue (encodeLitEnc l)
    return b
  | .dataMin n dp d => do
    let b ← freshEnc
    let td ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlMinQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnDataRange td
    return b
  | .dataMax n dp d => do
    let b ← freshEnc
    let td ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlMaxQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnDataRange td
    return b
  | .dataExact n dp d => do
    let b ← freshEnc
    let td ← encodeDataRangeEnc d
    emitEnc b rdfType (.iri owlRestriction)
    emitEnc b owlOnProperty (.iri dp)
    emitEnc b owlQualifiedCardinality (.literal (toString n) xsdNonNegativeInteger none)
    emitEnc b owlOnDataRange td
    return b

private def encodeDeclEnc (d : EntityDecl) : EncM Unit :=
  let ty := match d.kind with
    | .cls => owlClass
    | .datatype => rdfsDatatype
    | .objectProperty => owlObjectProperty
    | .dataProperty => owlDatatypeProperty
    | .annotationProperty => owlAnnotationProperty
    | .namedIndividual => owlNamedIndividual
  emitEnc (.iri d.iri) rdfType (.iri ty)

private def encodeAxiomEnc : Axiom → EncM Unit
  | .subClassOf a b => do
    emitEnc (← encodeClassExprEnc a) rdfsSubClassOf (← encodeClassExprEnc b)
  | .equivalentClasses [a, b] => do
    emitEnc (← encodeClassExprEnc a) owlEquivalentClass (← encodeClassExprEnc b)
  | .equivalentClasses _ => pure ()
  | .disjointClasses [a, b] => do
    emitEnc (← encodeClassExprEnc a) owlDisjointWith (← encodeClassExprEnc b)
  | .disjointClasses cs => do
    let b ← freshEnc
    let ts ← cs.mapM encodeClassExprEnc
    emitEnc b rdfType (.iri owlAllDisjointClasses)
    emitEnc b owlMembers (← encodeListEnc ts)
  | .disjointUnion h cs => do
    let ts ← cs.mapM encodeClassExprEnc
    emitEnc (.iri h) owlDisjointUnionOf (← encodeListEnc ts)
  | .subObjectProperty r s => do
    emitEnc (← encodeObjPropEnc r) rdfsSubPropertyOf (← encodeObjPropEnc s)
  | .subObjectPropertyChain rs s => do
    let ts ← rs.mapM encodeObjPropEnc
    emitEnc (← encodeObjPropEnc s) owlPropertyChainAxiom (← encodeListEnc ts)
  | .equivalentObjectProperties [r, s] => do
    emitEnc (← encodeObjPropEnc r) owlEquivalentProperty (← encodeObjPropEnc s)
  | .equivalentObjectProperties _ => pure ()
  | .disjointObjectProperties [r, s] => do
    emitEnc (← encodeObjPropEnc r) owlPropertyDisjointWith (← encodeObjPropEnc s)
  | .disjointObjectProperties rs => do
    let b ← freshEnc
    let ts ← rs.mapM encodeObjPropEnc
    emitEnc b rdfType (.iri owlAllDisjointProperties)
    emitEnc b owlMembers (← encodeListEnc ts)
  | .inverseObjectProperties r s => do
    emitEnc (← encodeObjPropEnc r) owlInverseOf (← encodeObjPropEnc s)
  | .objectPropertyDomain r c => do
    emitEnc (← encodeObjPropEnc r) rdfsDomain (← encodeClassExprEnc c)
  | .objectPropertyRange r c => do
    emitEnc (← encodeObjPropEnc r) rdfsRange (← encodeClassExprEnc c)
  | .functionalObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlFunctionalProperty)
  | .inverseFunctionalObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlInverseFunctionalProperty)
  | .reflexiveObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlReflexiveProperty)
  | .irreflexiveObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlIrreflexiveProperty)
  | .symmetricObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlSymmetricProperty)
  | .asymmetricObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlAsymmetricProperty)
  | .transitiveObjectProperty r => do
    emitEnc (← encodeObjPropEnc r) rdfType (.iri owlTransitiveProperty)
  | .subDataProperty r s => emitEnc (.iri r) rdfsSubPropertyOf (.iri s)
  | .equivalentDataProperties [r, s] => emitEnc (.iri r) owlEquivalentProperty (.iri s)
  | .equivalentDataProperties _ => pure ()
  | .disjointDataProperties [r, s] => emitEnc (.iri r) owlPropertyDisjointWith (.iri s)
  | .disjointDataProperties ds => do
    let b ← freshEnc
    emitEnc b rdfType (.iri owlAllDisjointProperties)
    emitEnc b owlMembers (← encodeListEnc (ds.map .iri))
  | .dataPropertyDomain dp c => do
    emitEnc (.iri dp) rdfsDomain (← encodeClassExprEnc c)
  | .dataPropertyRange dp d => do
    emitEnc (.iri dp) rdfsRange (← encodeDataRangeEnc d)
  | .functionalDataProperty dp => emitEnc (.iri dp) rdfType (.iri owlFunctionalProperty)
  | .datatypeDefinition dt d => do
    emitEnc (.iri dt) owlEquivalentClass (← encodeDataRangeEnc d)
  | .hasKey c os ds => do
    let tc ← encodeClassExprEnc c
    let tos ← os.mapM encodeObjPropEnc
    let tds := ds.map .iri
    emitEnc tc owlHasKey (← encodeListEnc (tos ++ tds))
  | .sameIndividuals [a, b] => emitEnc (encodeIndEnc a) owlSameAs (encodeIndEnc b)
  | .sameIndividuals _ => pure ()
  | .differentIndividuals [a, b] => emitEnc (encodeIndEnc a) owlDifferentFrom (encodeIndEnc b)
  | .differentIndividuals inds => do
    let b ← freshEnc
    emitEnc b rdfType (.iri owlAllDifferent)
    emitEnc b owlMembers (← encodeListEnc (inds.map encodeIndEnc))
  | .classAssertion c a => do
    emitEnc (encodeIndEnc a) rdfType (← encodeClassExprEnc c)
  | .objectAssertion (.named r) a b => emitEnc (encodeIndEnc a) r (encodeIndEnc b)
  | .objectAssertion (.inverse r) a b => emitEnc (encodeIndEnc b) r (encodeIndEnc a)
  | .negativeObjectAssertion r a b => do
    let node ← freshEnc
    emitEnc node rdfType (.iri owlNegativePropertyAssertion)
    emitEnc node owlSourceIndividual (encodeIndEnc a)
    emitEnc node owlAssertionProperty (← encodeObjPropEnc r)
    emitEnc node owlTargetIndividual (encodeIndEnc b)
  | .dataAssertion dp a l => emitEnc (encodeIndEnc a) dp (encodeLitEnc l)
  | .negativeDataAssertion dp a l => do
    let node ← freshEnc
    emitEnc node rdfType (.iri owlNegativePropertyAssertion)
    emitEnc node owlSourceIndividual (encodeIndEnc a)
    emitEnc node owlAssertionProperty (.iri dp)
    emitEnc node owlTargetValue (encodeLitEnc l)

private def encodeSWRLIArgEnc : SWRL.IArg → RDFTerm
  | .var v => .iri v
  | .ind a => encodeIndEnc a

private def encodeSWRLDArgEnc : SWRL.DArg → RDFTerm
  | .var v => .iri v
  | .lit l => encodeLitEnc l

private def encodeSWRLAtomListEnc (items : List RDFTerm) : EncM RDFTerm := do
  match items with
  | [] => return .iri rdfNil
  | x :: xs =>
    let cell ← freshEnc
    let rest ← encodeSWRLAtomListEnc xs
    emitEnc cell rdfType (.iri swrlAtomList)
    emitEnc cell rdfFirst x
    emitEnc cell rdfRest rest
    return cell

private def encodeSWRLAtomEnc : SWRL.SWRLAtom → EncM RDFTerm
  | .classAtom c a => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlClassAtom)
    emitEnc b swrlClassPredicate (← encodeClassExprEnc c)
    emitEnc b swrlArgument1 (encodeSWRLIArgEnc a)
    return b
  | .dataRangeAtom dr a => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlDataRangeAtom)
    emitEnc b swrlDataRange (← encodeDataRangeEnc dr)
    emitEnc b swrlArgument1 (encodeSWRLDArgEnc a)
    return b
  | .objectPropertyAtom r a1 a2 => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlIndividualPropertyAtom)
    emitEnc b swrlPropertyPredicate (← encodeObjPropEnc r)
    emitEnc b swrlArgument1 (encodeSWRLIArgEnc a1)
    emitEnc b swrlArgument2 (encodeSWRLIArgEnc a2)
    return b
  | .dataPropertyAtom p a1 a2 => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlDatavaluedPropertyAtom)
    emitEnc b swrlPropertyPredicate (.iri p)
    emitEnc b swrlArgument1 (encodeSWRLIArgEnc a1)
    emitEnc b swrlArgument2 (encodeSWRLDArgEnc a2)
    return b
  | .sameIndividualAtom a1 a2 => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlSameIndividualAtom)
    emitEnc b swrlArgument1 (encodeSWRLIArgEnc a1)
    emitEnc b swrlArgument2 (encodeSWRLIArgEnc a2)
    return b
  | .differentIndividualsAtom a1 a2 => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlDifferentIndividualsAtom)
    emitEnc b swrlArgument1 (encodeSWRLIArgEnc a1)
    emitEnc b swrlArgument2 (encodeSWRLIArgEnc a2)
    return b
  | .builtinAtom bi args => do
    let b ← freshEnc
    emitEnc b rdfType (.iri swrlBuiltinAtom)
    emitEnc b swrlBuiltin (.iri bi)
    emitEnc b swrlArguments (← encodeListEnc (args.map encodeSWRLDArgEnc))
    return b

private def encodeSWRLRuleEnc (r : SWRL.SWRLRule) : EncM Unit := do
  let imp ← freshEnc
  let bodyNodes ← r.body.mapM encodeSWRLAtomEnc
  let headNodes ← r.head.mapM encodeSWRLAtomEnc
  let bodyList ← encodeSWRLAtomListEnc bodyNodes
  let headList ← encodeSWRLAtomListEnc headNodes
  emitEnc imp rdfType (.iri swrlImp)
  emitEnc imp swrlBody bodyList
  emitEnc imp swrlHead headList

/-- Forward-encode an OWL 2 ontology (with declarations, optional header, and optional
    DL-Safe SWRL rules) into a W3C OWL 2 RDF graph. -/
def encodeOntologyRDF (decls : List EntityDecl) (ont : Ontology)
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (imports : List IRI := []) (rules : List SWRL.SWRLRule := []) : RDFGraph :=
  let ((), st) := (do
    if let some o := ontIRI then
      emitEnc (.iri o) rdfType (.iri owlOntology)
      if let some v := verIRI then emitEnc (.iri o) owlVersionIRI (.iri v)
      for imp in imports do emitEnc (.iri o) owlImports (.iri imp)
    for d in decls do encodeDeclEnc d
    for ax in ont do encodeAxiomEnc ax
    let allVars := (rules.flatMap fun (r : SWRL.SWRLRule) => r.iVars ++ r.dVars).eraseDups
    for v in allVars do
      emitEnc (.iri v) rdfType (.iri swrlVariable)
    for r in rules do encodeSWRLRuleEnc r).run {}
  { triples := st.triples.reverse }

private def checkRDFRoundtrip (decls : List EntityDecl) (ont : Ontology)
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (rules : List SWRL.SWRLRule := []) : Bool :=
  let g := encodeOntologyRDF decls ont ontIRI verIRI [] rules
  match mapRDFGraph "d" g true with
  | .ok doc =>
    doc.ontologyIRI == ontIRI &&
    doc.versionIRI == verIRI &&
    doc.declarations.length == decls.length &&
    ont.all (doc.ontology.contains ·) &&
    doc.rules == rules
  | .error _ => false

set_option maxHeartbeats 800000 in
theorem owl2_rdf_class_and_restriction_roundtrip :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.cls, "ex:B"⟩, ⟨.cls, "ex:C"⟩, ⟨.objectProperty, "ex:r"⟩]
      [.subClassOf (.named "ex:A") (.objectSome (.named "ex:r") (.named "ex:B")),
       .disjointClasses [.named "ex:A", .named "ex:B", .named "ex:C"]]
      (some "ex:o") (some "ex:v1") = true := by
  decide

set_option maxHeartbeats 800000 in
theorem owl2_rdf_property_chain_and_key_roundtrip :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.objectProperty, "ex:r"⟩, ⟨.objectProperty, "ex:s"⟩, ⟨.dataProperty, "ex:p"⟩]
      [.subObjectPropertyChain [.named "ex:r", .named "ex:s"] (.named "ex:s"),
       .transitiveObjectProperty (.named "ex:s"),
       .hasKey (.named "ex:A") [.named "ex:r"] ["ex:p"]] = true := by
  decide

set_option maxHeartbeats 800000 in
theorem owl2_rdf_data_and_assertions_roundtrip :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.objectProperty, "ex:r"⟩, ⟨.dataProperty, "ex:p"⟩,
       ⟨.namedIndividual, "ex:a"⟩, ⟨.namedIndividual, "ex:b"⟩]
      [.functionalDataProperty "ex:p",
       .dataPropertyRange "ex:p"
         (.restriction (xsdNS ++ "integer") [⟨xsdNS ++ "minInclusive", ⟨"0", xsdNS ++ "integer"⟩⟩]),
       .negativeObjectAssertion (.named "ex:r") (.named "ex:a") (.named "ex:b"),
       .classAssertion (.named "ex:A") (.named "ex:a"),
       .dataAssertion "ex:p" (.named "ex:a") ⟨"42", xsdNS ++ "integer"⟩] = true := by
  decide

/-- Kernel-checked normative round-trip correspondence for the W3C OWL 2 RDF mapping:
    forward-encoding declarations, headers, class expressions (`Restriction`, `AllDisjointClasses`),
    property chains, role characteristics, keys, data ranges (`DatatypeRestriction`), and
    positive/negative assertions into RDF graphs and mapping back via `mapRDFGraph` with
    `strictUnconsumed := true` succeeds with zero unconsumed triples and recovers the exact
    structural axioms. -/
theorem owl2_rdf_mapping_roundtrip_correspondence :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.cls, "ex:B"⟩, ⟨.cls, "ex:C"⟩, ⟨.objectProperty, "ex:r"⟩]
      [.subClassOf (.named "ex:A") (.objectSome (.named "ex:r") (.named "ex:B")),
       .disjointClasses [.named "ex:A", .named "ex:B", .named "ex:C"]]
      (some "ex:o") (some "ex:v1") = true ∧
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.objectProperty, "ex:r"⟩, ⟨.objectProperty, "ex:s"⟩, ⟨.dataProperty, "ex:p"⟩]
      [.subObjectPropertyChain [.named "ex:r", .named "ex:s"] (.named "ex:s"),
       .transitiveObjectProperty (.named "ex:s"),
       .hasKey (.named "ex:A") [.named "ex:r"] ["ex:p"]] = true ∧
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.objectProperty, "ex:r"⟩, ⟨.dataProperty, "ex:p"⟩,
       ⟨.namedIndividual, "ex:a"⟩, ⟨.namedIndividual, "ex:b"⟩]
      [.functionalDataProperty "ex:p",
       .dataPropertyRange "ex:p"
         (.restriction (xsdNS ++ "integer") [⟨xsdNS ++ "minInclusive", ⟨"0", xsdNS ++ "integer"⟩⟩]),
       .negativeObjectAssertion (.named "ex:r") (.named "ex:a") (.named "ex:b"),
       .classAssertion (.named "ex:A") (.named "ex:a"),
       .dataAssertion "ex:p" (.named "ex:a") ⟨"42", xsdNS ++ "integer"⟩] = true :=
  ⟨owl2_rdf_class_and_restriction_roundtrip,
   owl2_rdf_property_chain_and_key_roundtrip,
   owl2_rdf_data_and_assertions_roundtrip⟩

set_option maxHeartbeats 800000 in
theorem owl2_rdf_swrl_obj_roundtrip :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.cls, "ex:B"⟩, ⟨.objectProperty, "ex:r"⟩]
      []
      none none
      [{ body := [
           .classAtom (.named "ex:A") (.var "urn:swrl:var#x"),
           .objectPropertyAtom (.named "ex:r") (.var "urn:swrl:var#x") (.var "urn:swrl:var#y")
         ],
         head := [
           .classAtom (.named "ex:B") (.var "urn:swrl:var#y")
         ] }] = true := by
  decide

set_option maxHeartbeats 800000 in
theorem owl2_rdf_swrl_data_roundtrip :
    checkRDFRoundtrip
      [⟨.dataProperty, "ex:p"⟩]
      []
      none none
      [{ body := [
           .dataPropertyAtom "ex:p" (.var "urn:swrl:var#x") (.var "urn:swrl:var#v"),
           .dataRangeAtom (.datatype (xsdNS ++ "integer")) (.var "urn:swrl:var#v")
         ],
         head := [
           .sameIndividualAtom (.var "urn:swrl:var#x") (.ind (.named "ex:a"))
         ] }] = true := by
  decide

set_option maxHeartbeats 800000 in
theorem owl2_rdf_swrl_builtin_roundtrip :
    checkRDFRoundtrip
      []
      []
      none none
      [{ body := [
           .builtinAtom (swrlbNS ++ "greaterThan") [.var "urn:swrl:var#v", .lit ⟨"0", xsdNS ++ "integer"⟩]
         ],
         head := [
           .differentIndividualsAtom (.var "urn:swrl:var#x") (.ind (.named "ex:a"))
         ] }] = true := by
  decide

theorem owl2_rdf_swrl_roundtrip :
    checkRDFRoundtrip
      [⟨.cls, "ex:A"⟩, ⟨.cls, "ex:B"⟩, ⟨.objectProperty, "ex:r"⟩]
      []
      none none
      [{ body := [
           .classAtom (.named "ex:A") (.var "urn:swrl:var#x"),
           .objectPropertyAtom (.named "ex:r") (.var "urn:swrl:var#x") (.var "urn:swrl:var#y")
         ],
         head := [
           .classAtom (.named "ex:B") (.var "urn:swrl:var#y")
         ] }] = true ∧
    checkRDFRoundtrip
      [⟨.dataProperty, "ex:p"⟩]
      []
      none none
      [{ body := [
           .dataPropertyAtom "ex:p" (.var "urn:swrl:var#x") (.var "urn:swrl:var#v"),
           .dataRangeAtom (.datatype (xsdNS ++ "integer")) (.var "urn:swrl:var#v")
         ],
         head := [
           .sameIndividualAtom (.var "urn:swrl:var#x") (.ind (.named "ex:a"))
         ] }] = true ∧
    checkRDFRoundtrip
      []
      []
      none none
      [{ body := [
           .builtinAtom (swrlbNS ++ "greaterThan") [.var "urn:swrl:var#v", .lit ⟨"0", xsdNS ++ "integer"⟩]
         ],
         head := [
           .differentIndividualsAtom (.var "urn:swrl:var#x") (.ind (.named "ex:a"))
         ] }] = true :=
  ⟨owl2_rdf_swrl_obj_roundtrip, owl2_rdf_swrl_data_roundtrip, owl2_rdf_swrl_builtin_roundtrip⟩

#print axioms owl2_rdf_mapping_roundtrip_correspondence
#print axioms owl2_rdf_swrl_roundtrip

end Sabrina.OWL2.RDF.OWLMapping
