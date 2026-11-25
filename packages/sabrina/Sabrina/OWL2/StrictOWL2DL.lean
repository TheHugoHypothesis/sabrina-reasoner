import Sabrina.OWL2.WellFormed
import Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLDecision

/-! Strict W3C OWL 2 DL §11.1–§11.2 Global Restriction Validator (`--strict-owl2dl`).

Enforces every global OWL 2 DL axiom-closure restriction beyond the permissive
Direct-Semantics extensions:
1. Structural arities, reserved-vocabulary discipline, valid literals/facets,
   and acyclic non-builtin `DatatypeDefinition`s (`WellFormed.checkAxiom`, `normalizeWithDefs`).
2. Strict `owl:topDataProperty` restriction (§11.2): `owl:topDataProperty` may only
   occur in the superproperty position of `SubDataPropertyOf` (and in class expressions /
   assertions); it is forbidden as subproperty in `SubDataPropertyOf`, and forbidden in
   `EquivalentDataProperties`, `DisjointDataProperties`, `DataPropertyDomain`,
   `DataPropertyRange`, and `FunctionalDataProperty`.
3. Strict anonymous-individual restrictions (§11.2):
   - No anonymous individuals in `ObjectOneOf`, `ObjectHasValue`, `SameIndividual`,
     `DifferentIndividuals`, `NegativeObjectPropertyAssertion`, or
     `NegativeDataPropertyAssertion`.
   - The undirected multigraph of `ObjectPropertyAssertion`s between anonymous individuals
     must be a simple forest (no self-loops, no parallel edges, no cycles), and each
     connected component may be linked to named individuals by at most one assertion.
4. Strict W3C XSD 1.1 `xsd:pattern` syntactic validity (`parseCompleteRegex`).
5. Strict simple-role and dependency-acyclic / regular role-hierarchy restrictions
   (`AcyclicOWL2DLInput`), normatively rejecting rankless/non-regular hierarchies
   instead of invoking non-DL fallbacks.

Every ontology admitted by `StrictOWL2DLOntology` is totally decidable (fuel-free,
rank-free) over Dedekind-cut `realDatatypeMap` via `decideStrictOWL2DLReal_iff`. -/

namespace Sabrina.OWL2.StrictOWL2DL

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Normalize
open Sabrina.OWL2.WellFormed
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.RoleHierarchy.Unified
open Sabrina.OWL2.SROIQD.Termination.WiderData

/-! ### 1. W3C §11.2 `owl:topDataProperty` Restriction -/

/-- W3C OWL 2 Structural Specification §11.2 restriction on `owl:topDataProperty`
in data property axioms: permitted only in the superproperty position of
`SubDataPropertyOf`. -/
def checkTopDataPropertyAxiom : Axiom → Bool
  | .subDataProperty r _ => r != topDataProperty
  | .equivalentDataProperties rs | .disjointDataProperties rs =>
    rs.all (· != topDataProperty)
  | .dataPropertyDomain dp _ | .dataPropertyRange dp _ | .functionalDataProperty dp =>
    dp != topDataProperty
  | _ => true

/-! ### 2. W3C §11.2 Anonymous Individual Restrictions -/

def isNamedInd : Individual → Bool
  | .named _ => true
  | .anonymous _ _ => false

/-- Check that a class expression contains no anonymous individuals in
`ObjectOneOf` or `ObjectHasValue` (W3C OWL 2 §11.2). -/
def checkNoForbiddenAnonClass : ClassExpr → Bool
  | .named _ | .objectSelf _ | .dataSome _ _ | .dataAll _ _
  | .dataValue _ _ | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => true
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => checkNoForbiddenAnonClass c
  | .intersection a b | .union a b => checkNoForbiddenAnonClass a && checkNoForbiddenAnonClass b
  | .oneOf inds => inds.all isNamedInd
  | .objectValue _ a => isNamedInd a

/-- Check that an axiom obeys the W3C §11.2 prohibition on anonymous individuals
in `SameIndividual`, `DifferentIndividuals`, negative assertions, `ObjectOneOf`,
and `ObjectHasValue`. -/
def checkNoForbiddenAnonAxiom : Axiom → Bool
  | .subClassOf a b => checkNoForbiddenAnonClass a && checkNoForbiddenAnonClass b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.all checkNoForbiddenAnonClass
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ => checkNoForbiddenAnonClass c
  | .sameIndividuals inds | .differentIndividuals inds => inds.all isNamedInd
  | .classAssertion c _ => checkNoForbiddenAnonClass c
  | .negativeObjectAssertion _ a b => isNamedInd a && isNamedInd b
  | .negativeDataAssertion _ a _ => isNamedInd a
  | _ => true

private abbrev AnonId := String × String

/-- Merge an undirected edge `(u, v)` into a list of disjoint connected components.
Returns `none` on self-loops, parallel edges, or cycles. -/
private def addForestEdge (comps : List (List AnonId)) (u v : AnonId) :
    Option (List (List AnonId)) :=
  if u == v then none
  else
    let cu := comps.find? (·.contains u)
    let cv := comps.find? (·.contains v)
    match cu, cv with
    | none, none => some ([u, v] :: comps)
    | some c1, none =>
      let rest := comps.filter (fun c => !c.contains u)
      some ((v :: c1) :: rest)
    | none, some c2 =>
      let rest := comps.filter (fun c => !c.contains v)
      some ((u :: c2) :: rest)
    | some c1, some c2 =>
      if c1.contains v then none
      else
        let rest := comps.filter (fun c => !c.contains u && !c.contains v)
        some ((c1 ++ c2) :: rest)

private def buildAnonForest : List (AnonId × AnonId) → List (List AnonId) →
    Option (List (List AnonId))
  | [], comps => some comps
  | (u, v) :: rest, comps =>
    match addForestEdge comps u v with
    | some comps' => buildAnonForest rest comps'
    | none => none

private def anonObjEdges (o : Ontology) : List (AnonId × AnonId) :=
  o.filterMap fun
    | .objectAssertion _ (.anonymous d1 l1) (.anonymous d2 l2) => some ((d1, l1), (d2, l2))
    | _ => none

private def namedToAnonLinks (o : Ontology) : List AnonId :=
  o.filterMap fun
    | .objectAssertion _ (.named _) (.anonymous d l) => some (d, l)
    | .objectAssertion _ (.anonymous d l) (.named _) => some (d, l)
    | _ => none

/-- W3C §11.2 forest and single-named-root restriction on anonymous individuals
in `ObjectPropertyAssertion` axioms:
1. Anonymous-to-anonymous assertions form a simple forest (no self-loops, no
   parallel edges, no cycles).
2. Each connected component of anonymous individuals is attached to named
   individuals by at most one assertion. -/
def checkAnonForest (o : Ontology) : Bool :=
  let edges := anonObjEdges o
  let links := namedToAnonLinks o
  match buildAnonForest edges [] with
  | none => false
  | some comps =>
    let edgeNodes := comps.flatten
    let isolated := (links.filter fun u => !edgeNodes.contains u).eraseDups
    let allComps := comps ++ isolated.map fun u => [u]
    allComps.all fun comp =>
      (links.filter fun u => comp.contains u).length ≤ 1

/-! ### 3. Strict W3C XSD 1.1 `xsd:pattern` Syntactic Validity -/

def checkValidPatternFacet (f : Facet) : Bool :=
  if f.name == xsd "pattern" then
    match decodeLiteral f.bound with
    | some (.plainLiteral pat "") => (parseCompleteRegex pat).isSome
    | _ => false
  else true

def checkValidPatternsDataRange : DataRange → Bool
  | .datatype _ | .oneOf _ => true
  | .complement r => checkValidPatternsDataRange r
  | .intersection a b | .union a b =>
    checkValidPatternsDataRange a && checkValidPatternsDataRange b
  | .restriction _ fs => fs.all checkValidPatternFacet

def checkValidPatternsClass : ClassExpr → Bool
  | .named _ | .oneOf _ | .objectValue _ _ | .objectSelf _ | .dataValue _ _ => true
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => checkValidPatternsClass c
  | .intersection a b | .union a b => checkValidPatternsClass a && checkValidPatternsClass b
  | .dataSome _ d | .dataAll _ d | .dataMin _ _ d | .dataMax _ _ d | .dataExact _ _ d =>
    checkValidPatternsDataRange d

def checkValidPatternsAxiom : Axiom → Bool
  | .subClassOf a b => checkValidPatternsClass a && checkValidPatternsClass b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.all checkValidPatternsClass
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ | .classAssertion c _ =>
    checkValidPatternsClass c
  | .dataPropertyRange _ d | .datatypeDefinition _ d =>
    checkValidPatternsDataRange d
  | _ => true

/-! ### 4. Combined Strict W3C OWL 2 DL §11.1–§11.2 Specification & Validator -/

/-- Propositional specification of a strictly W3C OWL 2 DL conformant ontology
(§11.1–§11.2 global restrictions + valid XSD 1.1 patterns + unified regular/acyclic
role hierarchy admission). -/
def StrictOWL2DLOntology (o : Ontology) : Prop :=
  ∃ (defs : DatatypeDefs) (p : Problem),
    normalizeWithDefs o = some (defs, p) ∧
    p.root = .top ∧
    (∀ ax ∈ o, checkAxiom defs ax = true) ∧
    (∀ ax ∈ o, checkTopDataPropertyAxiom ax = true) ∧
    (∀ ax ∈ o, checkNoForbiddenAnonAxiom ax = true) ∧
    checkAnonForest o = true ∧
    (∀ ax ∈ o, checkValidPatternsAxiom ax = true) ∧
    AcyclicOWL2DLInput p

/-- Executable validator for `StrictOWL2DLOntology`. -/
def checkStrictOWL2DL (o : Ontology) : Bool :=
  match normalizeWithDefs o with
  | none => false
  | some (defs, p) =>
    (p.root == .top) &&
    o.all (checkAxiom defs) &&
    o.all checkTopDataPropertyAxiom &&
    o.all checkNoForbiddenAnonAxiom &&
    checkAnonForest o &&
    o.all checkValidPatternsAxiom &&
    checkAcyclicOWL2DLInput p

/-- Soundness and completeness of `checkStrictOWL2DL` with respect to `StrictOWL2DLOntology`. -/
theorem checkStrictOWL2DL_iff (o : Ontology) :
    checkStrictOWL2DL o = true ↔ StrictOWL2DLOntology o := by
  unfold checkStrictOWL2DL StrictOWL2DLOntology
  cases h : normalizeWithDefs o with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, _, hnorm, _⟩
    cases hnorm
  | some pair =>
    rcases pair with ⟨defs, p⟩
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, checkAcyclicOWL2DLInput_iff]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨hroot, hax⟩, htop⟩, hanon⟩, hfor⟩, hpat⟩, hacyc⟩
      exact ⟨defs, p, rfl, hroot, hax, htop, hanon, hfor, hpat, hacyc⟩
    · rintro ⟨defs', p', hnorm, hroot, hax, htop, hanon, hfor, hpat, hacyc⟩
      cases hnorm
      exact ⟨⟨⟨⟨⟨⟨hroot, hax⟩, htop⟩, hanon⟩, hfor⟩, hpat⟩, hacyc⟩

/-- Diagnostic strict W3C OWL 2 DL §11.1–§11.2 validator returning a human-readable
violation reason on rejection, or `none` iff `StrictOWL2DLOntology o` holds. -/
def diagnoseStrictOWL2DL (o : Ontology) : Option String :=
  match normalizeWithDefs o with
  | none =>
    some "W3C OWL 2 DL §11.2 violation: cyclic/duplicate DatatypeDefinition or unsupported normalized construct"
  | some (defs, p) =>
    if !(p.root == .top) then
      some "W3C OWL 2 DL violation: normalized ontology root is not owl:Thing"
    else if !o.all (checkAxiom defs) then
      some "W3C OWL 2 DL §5/§11 violation: invalid reserved vocabulary, arity, literal, facet, or HasKey structure"
    else if !o.all checkTopDataPropertyAxiom then
      some "W3C OWL 2 DL §11.2 violation: owl:topDataProperty is only allowed as the superproperty of SubDataPropertyOf"
    else if !o.all checkNoForbiddenAnonAxiom then
      some "W3C OWL 2 DL §11.2 violation: anonymous individual used in forbidden axiom or class expression (ObjectOneOf, ObjectHasValue, SameIndividual, DifferentIndividuals, or NegativePropertyAssertion)"
    else if !checkAnonForest o then
      some "W3C OWL 2 DL §11.2 violation: anonymous individuals in ObjectPropertyAssertion do not form a simple forest with at most one named-individual link per component"
    else if !o.all checkValidPatternsAxiom then
      some "W3C OWL 2 DL / XSD 1.1 violation: malformed xsd:pattern regular expression"
    else if !p.checkSimpleWithTop then
      some "W3C OWL 2 DL §11.2 violation: non-simple object property (or owl:topObjectProperty) used where a simple role is required"
    else if !p.chains.all (fun c => decide (2 ≤ c.body.length)) then
      some "W3C OWL 2 DL §11.2 violation: property chain must have length at least 2"
    else if !(Sabrina.RoleChains.findRank (ordinaryRules p.rules) (ordinaryChains p.chains)).isSome then
      some "W3C OWL 2 DL §11.2 violation: role hierarchy is not regular (cyclic strict property-chain dependency)"
    else if !checkAcyclicOWL2DLInput p then
      some "W3C OWL 2 DL §11 violation: unsupported class, literal, or data range construct"
    else
      none

private theorem ite_not_isNone (b : Bool) (msg : String) (k : Option String) :
    (if !b then some msg else k).isNone = (b && k.isNone) := by
  cases b <;> rfl

theorem diagnoseStrictOWL2DL_isNone_iff (o : Ontology) :
    (diagnoseStrictOWL2DL o).isNone = true ↔ StrictOWL2DLOntology o := by
  rw [← checkStrictOWL2DL_iff]
  unfold diagnoseStrictOWL2DL checkStrictOWL2DL
  cases h : normalizeWithDefs o with
  | none => simp
  | some pair =>
    rcases pair with ⟨defs, p⟩
    simp only [ite_not_isNone, Option.isNone_none, Bool.and_true]
    have htail :
        (p.checkSimpleWithTop &&
          (p.chains.all (fun c => decide (2 ≤ c.body.length)) &&
            ((Sabrina.RoleChains.findRank (ordinaryRules p.rules) (ordinaryChains p.chains)).isSome &&
              checkAcyclicOWL2DLInput p))) = checkAcyclicOWL2DLInput p := by
      unfold checkAcyclicOWL2DLInput
      cases p.allConcepts.all Concept.coreClasses <;>
      cases p.allDataLiterals.all (fun l => (decodeLiteral l).isSome) <;>
      cases p.allDataRanges.all isWiderDataRange <;>
      cases p.checkSimpleWithTop <;>
      cases p.chains.all (fun c => decide (2 ≤ c.body.length)) <;>
      cases (Sabrina.RoleChains.findRank (ordinaryRules p.rules) (ordinaryChains p.chains)).isSome <;>
      rfl
    rw [htail]
    simp only [Bool.and_assoc]

/-- Strict W3C OWL 2 DL query axiom validation (checks structural validity,
`owl:topDataProperty`, anonymous-individual prohibitions, and XSD 1.1 patterns). -/
def diagnoseStrictOWL2DLQuery (o : Ontology) (qAx : Axiom) : Option String :=
  match diagnoseStrictOWL2DL o with
  | some err => some err
  | none =>
    match normalizeWithDefs o with
    | none => some "W3C OWL 2 DL §11.2 violation: ontology normalization failed"
    | some (defs, _) =>
      if !checkAxiom defs qAx then
        some "W3C OWL 2 DL §5/§11 violation in query: invalid reserved vocabulary, arity, literal, or facet"
      else if !checkTopDataPropertyAxiom qAx then
        some "W3C OWL 2 DL §11.2 violation in query: disallowed owl:topDataProperty position"
      else if !checkNoForbiddenAnonAxiom qAx then
        some "W3C OWL 2 DL §11.2 violation in query: anonymous individual in forbidden position"
      else if !checkValidPatternsAxiom qAx then
        some "W3C OWL 2 DL / XSD 1.1 violation in query: malformed xsd:pattern regular expression"
      else
        none

/-! ### 5. Total Fuel-Free Decision Theorem for Strict W3C OWL 2 DL Ontologies -/

theorem decideRealOntology_isSome_of_strict {o : Ontology} (h : StrictOWL2DLOntology o) :
    (decideRealOntology? o).isSome = true := by
  obtain ⟨_, _, hnorm, hroot, _, _, _, _, _, hacyc⟩ := h
  exact decideRealOntology_isSome_of_acyclic hnorm hroot hacyc

/-- Total, fuel-free, rank-free satisfiability decision procedure for every
ontology passing `StrictOWL2DLOntology` over the Dedekind-cut `realDatatypeMap`. -/
def decideStrictOWL2DLReal (o : Ontology) (h : StrictOWL2DLOntology o) : Bool :=
  (decideRealOntology? o).get (decideRealOntology_isSome_of_strict h)

theorem decideStrictOWL2DLReal_iff {o : Ontology} (h : StrictOWL2DLOntology o) :
    decideStrictOWL2DLReal o h = true ↔ Satisfiable realDatatypeMap o :=
  decideRealOntology_iff (Option.some_get (decideRealOntology_isSome_of_strict h)).symm

#print axioms checkStrictOWL2DL_iff
#print axioms diagnoseStrictOWL2DL_isNone_iff
#print axioms decideStrictOWL2DLReal_iff

end Sabrina.OWL2.StrictOWL2DL
