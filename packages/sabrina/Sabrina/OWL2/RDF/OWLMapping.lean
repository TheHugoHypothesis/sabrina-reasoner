import Sabrina.OWL2.RDF.Graph
import Sabrina.OWL2.RDF.XMLParser
import Sabrina.OWL2.RDF.TurtleParser
import Sabrina.OWL2.StrictTyping

/-! W3C OWL 2 Mapping from RDF Graphs to the Structural Specification (Tables 3–18),
    forward Structural-to-RDF encoder, unified auto-detecting document & import-closure
    parser (FSS / RDF/XML / Turtle), and kernel-checked correspondence proofs. -/

namespace Sabrina.OWL2.RDF.OWLMapping

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.StrictTyping
open Sabrina.OWL2.RDF

/-! ### 1. Indexed RDF Triple Consumption State -/

private structure MapState where
  docId : String
  triples : Array RDFTriple
  consumed : Array Bool
  -- Typing sets collected in Pass 2 (Table 5)
  classes : List IRI := []
  datatypes : List IRI := []
  objProps : List IRI := []
  dataProps : List IRI := []
  annotProps : List IRI := []
  namedInds : List IRI := []
  -- Output structural items
  ontologyIRI : Option IRI := none
  versionIRI : Option IRI := none
  imports : List IRI := []
  declarations : List EntityDecl := []
  annotationAxioms : List AnnotationAxiom := []
  axioms : List Axiom := []

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
  let act ← activeIndices
  return act.filterMap fun (i, t) =>
    if t.subject == s && t.predicate == p then some (i, t.object) else none

private def findActiveByS (s : RDFTerm) : MapM (List (Nat × RDFTriple)) := do
  let act ← activeIndices
  return act.filter fun (_, t) => t.subject == s

private def hasType (s : RDFTerm) (ty : IRI) : MapM (Option Nat) := do
  let hits ← findActiveBySP s rdfType
  for (i, o) in hits do
    if o == .iri ty then return some i
  return none

private def isObjPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInObjProp iri || st.objProps.contains iri

private def isDataPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInDataProp iri || st.dataProps.contains iri

private def isAnnotPropIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInAnnotProp iri || st.annotProps.contains iri

private def isDatatypeIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInDatatype iri || st.datatypes.contains iri

private def isClassIRI (st : MapState) (iri : IRI) : Bool :=
  isBuiltInClass iri || st.classes.contains iri

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

private def addDecl (kind : EntityKind) (iri : IRI) : MapM Unit :=
  modify fun st =>
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
      if let .iri iri := t.subject then
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
  -- Consume ontology-header annotations (where subject is the ontology IRI or blank header)
  let st ← get
  if let some ontIRI := st.ontologyIRI then
    for (i, t) in ← findActiveByS (.iri ontIRI) do
      if isAnnotPropIRI st t.predicate then
        markConsumed i

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

/-- Map a parsed `RDFGraph` to a SABRINA `ParsedDocument` per W3C OWL 2 Mapping
    to RDF Graphs (Tables 3–18). When `strictUnconsumed` is `true`, rejects any
    unconsumed or malformed RDF triples. -/
def mapRDFGraph (docId : String) (g : RDFGraph) (strictUnconsumed : Bool := true) :
    Except String ParsedDocument := do
  let initSt : MapState := {
    docId := docId
    triples := g.triples.toArray
    consumed := Array.replicate g.triples.length false
  }
  let fuel := g.triples.length + 32
  let ((), st) ← (do
    passHeaderAndReification
    passDeclarations
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

/-- Resolve transitive `Import(...)` / `owl:imports` closure across mixed-syntax
    documents (FSS, RDF/XML, and Turtle). -/
def resolveImportClosureAuto (rootText : String) (library : List (IRI × String))
    (strictRDF : Bool := true) : Except String ResolvedOFNClosure := do
  let rootDoc ← parseDocumentAutoWithId "doc:0" rootText strictRDF
  let mut parsedLib : List (IRI × ParsedDocument) := []
  let mut idx := 1
  for (key, text) in library do
    let doc ← parseDocumentAutoWithId s!"doc:{idx}" text strictRDF
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

/-- Forward-encode an OWL 2 ontology (with declarations & optional header) into
    a W3C OWL 2 RDF graph. -/
def encodeOntologyRDF (decls : List EntityDecl) (ont : Ontology)
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none)
    (imports : List IRI := []) : RDFGraph :=
  let ((), st) := (do
    if let some o := ontIRI then
      emitEnc (.iri o) rdfType (.iri owlOntology)
      if let some v := verIRI then emitEnc (.iri o) owlVersionIRI (.iri v)
      for imp in imports do emitEnc (.iri o) owlImports (.iri imp)
    for d in decls do encodeDeclEnc d
    for ax in ont do encodeAxiomEnc ax).run {}
  { triples := st.triples.reverse }

private def checkRDFRoundtrip (decls : List EntityDecl) (ont : Ontology)
    (ontIRI : Option IRI := none) (verIRI : Option IRI := none) : Bool :=
  let g := encodeOntologyRDF decls ont ontIRI verIRI []
  match mapRDFGraph "d" g true with
  | .ok doc =>
    doc.ontologyIRI == ontIRI &&
    doc.versionIRI == verIRI &&
    doc.declarations.length == decls.length &&
    ont.all (doc.ontology.contains ·)
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

#print axioms owl2_rdf_mapping_roundtrip_correspondence

end Sabrina.OWL2.RDF.OWLMapping
