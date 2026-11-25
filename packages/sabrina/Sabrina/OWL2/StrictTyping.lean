import Sabrina.OWL2.StrictOWL2DL

/-! W3C OWL 2 DL §5.8.1–§5.8.2 Entity Declaration Typing, Reserved-Vocabulary,
    and Punning Validator.

Enforces the exact typing constraints of W3C OWL 2 Structural Specification §5.8.2:
1. Reserved vocabulary (§5.8.1): declarations may not bind reserved `owl:`/`rdf:`/
   `rdfs:`/`xsd:` IRIs except to their standard built-in entity kind (`owl:Thing` as
   Class, `owl:topObjectProperty` as ObjectProperty, `rdfs:label` as AnnotationProperty,
   etc.). Named individuals may never use reserved vocabulary.
2. Property disjointness (§5.8.2): no IRI may be typed as more than one of
   `ObjectProperty`, `DataProperty`, or `AnnotationProperty`.
3. Class/Datatype disjointness (§5.8.2): no IRI may be typed as both `Class`
   and `Datatype`.
4. Legal punning (§5.8.2): `Class` + `NamedIndividual`, `Class` + property,
   `Datatype` + `NamedIndividual`, `Datatype` + property, and `NamedIndividual` +
   property are explicitly permitted.
5. Mandatory declaration completeness (§5.8.2): every non-built-in `Class`,
   `Datatype`, `ObjectProperty`, `DataProperty`, and `AnnotationProperty` occurring
   in the import closure must have a matching `Declaration(...)`. Per W3C §5.8.2,
   `NamedIndividual` declarations are optional.

Provides kernel-checked equivalence theorems (`checkTyping_iff`,
`diagnoseTyping_isNone_iff`, `checkStrictTypedOWL2DL_iff`,
`decideStrictTypedOWL2DLReal_iff`) using only standard Lean core axioms. -/

namespace Sabrina.OWL2.StrictTyping

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.FunctionalSyntax
open Sabrina.OWL2.WellFormed
open Sabrina.OWL2.StrictOWL2DL

/-! ### 1. W3C OWL 2 Built-In Entities (§5.8.1 & Table 2) -/

def isBuiltInClass (iri : IRI) : Bool :=
  iri == thing || iri == nothing

def isBuiltInDatatype (iri : IRI) : Bool :=
  iri == literalDatatype || supportedDatatype iri

def isBuiltInObjProp (iri : IRI) : Bool :=
  iri == topObjectProperty || iri == bottomObjectProperty

def isBuiltInDataProp (iri : IRI) : Bool :=
  iri == topDataProperty || iri == bottomDataProperty

def builtInAnnotProps : List IRI := [
  "http://www.w3.org/2000/01/rdf-schema#label",
  "http://www.w3.org/2000/01/rdf-schema#comment",
  "http://www.w3.org/2000/01/rdf-schema#seeAlso",
  "http://www.w3.org/2000/01/rdf-schema#isDefinedBy",
  "http://www.w3.org/2002/07/owl#deprecated",
  "http://www.w3.org/2002/07/owl#versionInfo",
  "http://www.w3.org/2002/07/owl#priorVersion",
  "http://www.w3.org/2002/07/owl#backwardCompatibleWith",
  "http://www.w3.org/2002/07/owl#incompatibleWith"
]

def isBuiltInAnnotProp (iri : IRI) : Bool :=
  builtInAnnotProps.contains iri

/-- Check that a single `Declaration(kind(iri))` respects W3C §5.8.1 reserved
vocabulary rules. -/
def checkValidDecl (d : EntityDecl) : Bool :=
  !d.iri.isEmpty &&
  match d.kind with
  | .cls => isBuiltInClass d.iri || !isReservedPrefix d.iri
  | .datatype => isBuiltInDatatype d.iri || !isReservedPrefix d.iri
  | .objectProperty => isBuiltInObjProp d.iri || !isReservedPrefix d.iri
  | .dataProperty => isBuiltInDataProp d.iri || !isReservedPrefix d.iri
  | .annotationProperty => isBuiltInAnnotProp d.iri || !isReservedPrefix d.iri
  | .namedIndividual => !isReservedPrefix d.iri

/-! ### 2. Entity Occurrence Extraction across Logical & Annotation Axioms -/

def dataRangeDatatypes : DataRange → List IRI
  | .datatype t => [t]
  | .complement r => dataRangeDatatypes r
  | .intersection a b | .union a b => dataRangeDatatypes a ++ dataRangeDatatypes b
  | .oneOf ls => ls.map (·.datatype)
  | .restriction t fs => t :: fs.map (·.bound.datatype)

def classClasses : ClassExpr → List IRI
  | .named c => [c]
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classClasses c
  | .intersection a b | .union a b => classClasses a ++ classClasses b
  | _ => []

def classDatatypes : ClassExpr → List IRI
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classDatatypes c
  | .intersection a b | .union a b => classDatatypes a ++ classDatatypes b
  | .dataSome _ d | .dataAll _ d
  | .dataMin _ _ d | .dataMax _ _ d | .dataExact _ _ d => dataRangeDatatypes d
  | .dataValue _ l => [l.datatype]
  | _ => []

def objPropIRI : ObjectProperty → IRI
  | .named r | .inverse r => r

def classObjProps : ClassExpr → List IRI
  | .complement c => classObjProps c
  | .intersection a b | .union a b => classObjProps a ++ classObjProps b
  | .objectSome r c | .objectAll r c
  | .objectMin _ r c | .objectMax _ r c | .objectExact _ r c =>
    objPropIRI r :: classObjProps c
  | .objectValue r _ | .objectSelf r => [objPropIRI r]
  | _ => []

def classDataProps : ClassExpr → List IRI
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classDataProps c
  | .intersection a b | .union a b => classDataProps a ++ classDataProps b
  | .dataSome dp _ | .dataAll dp _ | .dataValue dp _
  | .dataMin _ dp _ | .dataMax _ dp _ | .dataExact _ dp _ => [dp]
  | _ => []

def axiomClasses : Axiom → List IRI
  | .subClassOf a b => classClasses a ++ classClasses b
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap classClasses
  | .disjointUnion h cs => h :: cs.flatMap classClasses
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ | .classAssertion c _ => classClasses c
  | _ => []

def axiomDatatypes : Axiom → List IRI
  | .subClassOf a b => classDatatypes a ++ classDatatypes b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classDatatypes
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ | .classAssertion c _ => classDatatypes c
  | .dataPropertyRange _ d => dataRangeDatatypes d
  | .datatypeDefinition dt d => dt :: dataRangeDatatypes d
  | .dataAssertion _ _ l | .negativeDataAssertion _ _ l => [l.datatype]
  | _ => []

def axiomObjProps : Axiom → List IRI
  | .subClassOf a b => classObjProps a ++ classObjProps b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classObjProps
  | .subObjectProperty r s | .inverseObjectProperties r s => [objPropIRI r, objPropIRI s]
  | .subObjectPropertyChain rs h => objPropIRI h :: rs.map objPropIRI
  | .equivalentObjectProperties rs | .disjointObjectProperties rs => rs.map objPropIRI
  | .objectPropertyDomain r c | .objectPropertyRange r c => objPropIRI r :: classObjProps c
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .reflexiveObjectProperty r | .irreflexiveObjectProperty r
  | .symmetricObjectProperty r | .asymmetricObjectProperty r
  | .transitiveObjectProperty r => [objPropIRI r]
  | .dataPropertyDomain _ c | .classAssertion c _ => classObjProps c
  | .hasKey c rs _ => rs.map objPropIRI ++ classObjProps c
  | .objectAssertion r _ _ | .negativeObjectAssertion r _ _ => [objPropIRI r]
  | _ => []

def axiomDataProps : Axiom → List IRI
  | .subClassOf a b => classDataProps a ++ classDataProps b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classDataProps
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .classAssertion c _ =>
    classDataProps c
  | .subDataProperty r s => [r, s]
  | .equivalentDataProperties ds | .disjointDataProperties ds => ds
  | .dataPropertyDomain dp c => dp :: classDataProps c
  | .dataPropertyRange dp _ | .functionalDataProperty dp => [dp]
  | .hasKey c _ ds => ds ++ classDataProps c
  | .dataAssertion dp _ _ | .negativeDataAssertion dp _ _ => [dp]
  | _ => []

def annotAxiomProps : AnnotationAxiom → List IRI
  | .assertion p _ _ => [p]
  | .subProperty sub sup => [sub, sup]
  | .domain p _ | .range p _ => [p]

def annotAxiomDatatypes : AnnotationAxiom → List IRI
  | .assertion _ _ (.literal l) => [l.datatype]
  | _ => []

def declaredKind (decls : List EntityDecl) (k : EntityKind) : List IRI :=
  decls.filterMap fun d => if d.kind == k then some d.iri else none

/-! ### 3. W3C §5.8.2 Typing & Punning Specification and Executable Validator -/

def allClasses (decls : List EntityDecl) (ont : Ontology) : List IRI :=
  declaredKind decls .cls ++ ont.flatMap axiomClasses

def allDatatypes (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology) : List IRI :=
  declaredKind decls .datatype ++ ont.flatMap axiomDatatypes ++ annots.flatMap annotAxiomDatatypes

def allObjProps (decls : List EntityDecl) (ont : Ontology) : List IRI :=
  declaredKind decls .objectProperty ++ ont.flatMap axiomObjProps

def allDataProps (decls : List EntityDecl) (ont : Ontology) : List IRI :=
  declaredKind decls .dataProperty ++ ont.flatMap axiomDataProps

def allAnnotProps (decls : List EntityDecl) (annots : List AnnotationAxiom) : List IRI :=
  declaredKind decls .annotationProperty ++ annots.flatMap annotAxiomProps

def listsDisjoint (xs ys : List IRI) : Bool :=
  xs.all fun x => !ys.contains x

/-- Propositional specification of W3C OWL 2 DL §5.8.1–§5.8.2 entity declaration
typing and punning validity across an import closure. -/
def TypingValid (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology) : Prop :=
  (∀ d ∈ decls, checkValidDecl d = true) ∧
  -- Punning disjointness (§5.8.2): Class vs Datatype, and pairwise property kinds
  listsDisjoint (allClasses decls ont) (allDatatypes decls annots ont) = true ∧
  listsDisjoint (allObjProps decls ont) (allDataProps decls ont) = true ∧
  listsDisjoint (allObjProps decls ont) (allAnnotProps decls annots) = true ∧
  listsDisjoint (allDataProps decls ont) (allAnnotProps decls annots) = true ∧
  -- Mandatory declarations for all non-built-in entities (individuals are optional per §5.8.2)
  (∀ c ∈ ont.flatMap axiomClasses, isBuiltInClass c = true ∨ (declaredKind decls .cls).contains c = true) ∧
  (∀ dt ∈ ont.flatMap axiomDatatypes, isBuiltInDatatype dt = true ∨ (declaredKind decls .datatype).contains dt = true) ∧
  (∀ r ∈ ont.flatMap axiomObjProps, isBuiltInObjProp r = true ∨ (declaredKind decls .objectProperty).contains r = true) ∧
  (∀ dp ∈ ont.flatMap axiomDataProps, isBuiltInDataProp dp = true ∨ (declaredKind decls .dataProperty).contains dp = true) ∧
  (∀ ap ∈ annots.flatMap annotAxiomProps, isBuiltInAnnotProp ap = true ∨ (declaredKind decls .annotationProperty).contains ap = true)

/-- Executable validator for `TypingValid`. -/
def checkTyping (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology) : Bool :=
  let declCls := declaredKind decls .cls
  let declDt := declaredKind decls .datatype
  let declObj := declaredKind decls .objectProperty
  let declData := declaredKind decls .dataProperty
  let declAnn := declaredKind decls .annotationProperty
  decls.all checkValidDecl &&
  listsDisjoint (allClasses decls ont) (allDatatypes decls annots ont) &&
  listsDisjoint (allObjProps decls ont) (allDataProps decls ont) &&
  listsDisjoint (allObjProps decls ont) (allAnnotProps decls annots) &&
  listsDisjoint (allDataProps decls ont) (allAnnotProps decls annots) &&
  (ont.flatMap axiomClasses).all (fun c => isBuiltInClass c || declCls.contains c) &&
  (ont.flatMap axiomDatatypes).all (fun dt => isBuiltInDatatype dt || declDt.contains dt) &&
  (ont.flatMap axiomObjProps).all (fun r => isBuiltInObjProp r || declObj.contains r) &&
  (ont.flatMap axiomDataProps).all (fun dp => isBuiltInDataProp dp || declData.contains dp) &&
  (annots.flatMap annotAxiomProps).all (fun ap => isBuiltInAnnotProp ap || declAnn.contains ap)

theorem checkTyping_iff (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology) :
    checkTyping decls annots ont = true ↔ TypingValid decls annots ont := by
  unfold checkTyping TypingValid
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, and_assoc]

/-- Diagnostic W3C §5.8.1–§5.8.2 typing and punning checker returning a clear
error message on violation, or `none` iff `TypingValid decls annots ont`. -/
def diagnoseTyping (decls : List EntityDecl) (annots : List AnnotationAxiom) (ont : Ontology) :
    Option String :=
  let declCls := declaredKind decls .cls
  let declDt := declaredKind decls .datatype
  let declObj := declaredKind decls .objectProperty
  let declData := declaredKind decls .dataProperty
  let declAnn := declaredKind decls .annotationProperty
  if !decls.all checkValidDecl then
    some "W3C OWL 2 DL §5.8.1 violation: invalid or reserved-vocabulary entity declaration"
  else if !listsDisjoint (allClasses decls ont) (allDatatypes decls annots ont) then
    some "W3C OWL 2 DL §5.8.2 punning violation: IRI used as both Class and Datatype"
  else if !listsDisjoint (allObjProps decls ont) (allDataProps decls ont) then
    some "W3C OWL 2 DL §5.8.2 punning violation: IRI used as both ObjectProperty and DataProperty"
  else if !listsDisjoint (allObjProps decls ont) (allAnnotProps decls annots) then
    some "W3C OWL 2 DL §5.8.2 punning violation: IRI used as both ObjectProperty and AnnotationProperty"
  else if !listsDisjoint (allDataProps decls ont) (allAnnotProps decls annots) then
    some "W3C OWL 2 DL §5.8.2 punning violation: IRI used as both DataProperty and AnnotationProperty"
  else if !(ont.flatMap axiomClasses).all (fun c => isBuiltInClass c || declCls.contains c) then
    some "W3C OWL 2 DL §5.8.2 violation: undeclared Class IRI"
  else if !(ont.flatMap axiomDatatypes).all (fun dt => isBuiltInDatatype dt || declDt.contains dt) then
    some "W3C OWL 2 DL §5.8.2 violation: undeclared Datatype IRI"
  else if !(ont.flatMap axiomObjProps).all (fun r => isBuiltInObjProp r || declObj.contains r) then
    some "W3C OWL 2 DL §5.8.2 violation: undeclared ObjectProperty IRI"
  else if !(ont.flatMap axiomDataProps).all (fun dp => isBuiltInDataProp dp || declData.contains dp) then
    some "W3C OWL 2 DL §5.8.2 violation: undeclared DataProperty IRI"
  else if !(annots.flatMap annotAxiomProps).all (fun ap => isBuiltInAnnotProp ap || declAnn.contains ap) then
    some "W3C OWL 2 DL §5.8.2 violation: undeclared AnnotationProperty IRI"
  else
    none

private theorem ite_not_isNone (b : Bool) (msg : String) (k : Option String) :
    (if !b then some msg else k).isNone = (b && k.isNone) := by
  cases b <;> rfl

theorem diagnoseTyping_isNone_iff (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) :
    (diagnoseTyping decls annots ont).isNone = true ↔ TypingValid decls annots ont := by
  rw [← checkTyping_iff]
  unfold diagnoseTyping checkTyping
  simp only [ite_not_isNone, Option.isNone_none, Bool.and_true, Bool.and_assoc]

/-! ### 4. Combined Strict W3C OWL 2 DL (Typing + §11.1–§11.2) -/

/-- Full W3C OWL 2 DL conformance predicate combining §5.8.1–§5.8.2 entity typing &
punning with §11.1–§11.2 global axiom-closure restrictions. -/
def StrictTypedOWL2DL (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) : Prop :=
  TypingValid decls annots ont ∧ StrictOWL2DLOntology ont

def checkStrictTypedOWL2DL (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) : Bool :=
  checkTyping decls annots ont && checkStrictOWL2DL ont

theorem checkStrictTypedOWL2DL_iff (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) :
    checkStrictTypedOWL2DL decls annots ont = true ↔ StrictTypedOWL2DL decls annots ont := by
  unfold checkStrictTypedOWL2DL StrictTypedOWL2DL
  rw [Bool.and_eq_true, checkTyping_iff, checkStrictOWL2DL_iff]

def diagnoseStrictTypedOWL2DL (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) : Option String :=
  match diagnoseTyping decls annots ont with
  | some err => some err
  | none => diagnoseStrictOWL2DL ont

theorem diagnoseStrictTypedOWL2DL_isNone_iff (decls : List EntityDecl)
    (annots : List AnnotationAxiom) (ont : Ontology) :
    (diagnoseStrictTypedOWL2DL decls annots ont).isNone = true ↔
      StrictTypedOWL2DL decls annots ont := by
  unfold diagnoseStrictTypedOWL2DL StrictTypedOWL2DL
  cases h : diagnoseTyping decls annots ont with
  | some err =>
    simp only [Option.isNone_some, Bool.false_eq_true, false_iff, not_and]
    intro ht
    have hnone := (diagnoseTyping_isNone_iff decls annots ont).mpr ht
    rw [h] at hnone
    cases hnone
  | none =>
    have ht : TypingValid decls annots ont :=
      (diagnoseTyping_isNone_iff decls annots ont).mp (by rw [h]; rfl)
    simp only [diagnoseStrictOWL2DL_isNone_iff]
    exact ⟨fun hs => ⟨ht, hs⟩, fun ⟨_, hs⟩ => hs⟩

/-- Strict typed query validation: checks closure typing + §11.2, and ensures
entities occurring in `qAx` are declared and free of punning conflicts against
the closure declarations. -/
def diagnoseStrictTypedOWL2DLQuery (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) (qAx : Axiom) : Option String :=
  match diagnoseTyping decls annots (qAx :: ont) with
  | some err => some err
  | none => diagnoseStrictOWL2DLQuery ont qAx

/-- Total fuel-free decision procedure for every strictly typed, §11.2-conformant
W3C OWL 2 DL ontology over Dedekind-cut `realDatatypeMap`. -/
def decideStrictTypedOWL2DLReal (decls : List EntityDecl) (annots : List AnnotationAxiom)
    (ont : Ontology) (h : StrictTypedOWL2DL decls annots ont) : Bool :=
  decideStrictOWL2DLReal ont h.2

theorem decideStrictTypedOWL2DLReal_iff {decls : List EntityDecl}
    {annots : List AnnotationAxiom} {ont : Ontology}
    (h : StrictTypedOWL2DL decls annots ont) :
    decideStrictTypedOWL2DLReal decls annots ont h = true ↔
      Satisfiable realDatatypeMap ont :=
  decideStrictOWL2DLReal_iff h.2

#print axioms checkTyping_iff
#print axioms diagnoseTyping_isNone_iff
#print axioms checkStrictTypedOWL2DL_iff
#print axioms diagnoseStrictTypedOWL2DL_isNone_iff
#print axioms decideStrictTypedOWL2DLReal_iff

end Sabrina.OWL2.StrictTyping
