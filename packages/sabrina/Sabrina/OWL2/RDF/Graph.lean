import Sabrina.OWL2.Syntax
import Sabrina.OWL2.FunctionalSyntax

/-! W3C RDF 1.1 Graph data model, standard OWL 2 / RDF / RDFS / XSD vocabulary
    IRIs, RFC 3986 relative IRI resolution, and verified RDF list helpers. -/

namespace Sabrina.OWL2.RDF

open Sabrina.OWL2
open Sabrina.OWL2.FunctionalSyntax

/-- An RDF 1.1 term: IRI, blank node identifier, or typed/language-tagged literal. -/
inductive RDFTerm where
  | iri (val : IRI)
  | bnode (id : String)
  | literal (lexical : String) (datatype : IRI) (lang : Option String := none)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- An RDF 1.1 triple `(subject, predicate, object)`. -/
structure RDFTriple where
  subject : RDFTerm
  predicate : IRI
  object : RDFTerm
  deriving DecidableEq, Repr, Inhabited

/-- A parsed RDF 1.1 graph together with prefix bindings and optional base IRI. -/
structure RDFGraph where
  triples : List RDFTriple := []
  prefixes : PrefixMap := []
  baseIRI : Option IRI := none
  deriving Repr

/-! ### Standard W3C RDF / RDFS / OWL / XSD Namespace & Vocabulary IRIs -/

def rdfNS  : IRI := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdfsNS : IRI := "http://www.w3.org/2000/01/rdf-schema#"
def owlNS  : IRI := "http://www.w3.org/2002/07/owl#"
def xsdNS  : IRI := "http://www.w3.org/2001/XMLSchema#"

def rdfType         : IRI := rdfNS ++ "type"
def rdfFirst        : IRI := rdfNS ++ "first"
def rdfRest         : IRI := rdfNS ++ "rest"
def rdfNil          : IRI := rdfNS ++ "nil"
def rdfPlainLiteral : IRI := rdfNS ++ "PlainLiteral"
def rdfLangString   : IRI := rdfNS ++ "langString"
def rdfXMLLiteral   : IRI := rdfNS ++ "XMLLiteral"

def rdfsSubClassOf    : IRI := rdfsNS ++ "subClassOf"
def rdfsSubPropertyOf : IRI := rdfsNS ++ "subPropertyOf"
def rdfsDomain        : IRI := rdfsNS ++ "domain"
def rdfsRange         : IRI := rdfsNS ++ "range"
def rdfsDatatype      : IRI := rdfsNS ++ "Datatype"
def rdfsLiteral       : IRI := rdfsNS ++ "Literal"
def rdfsLabel         : IRI := rdfsNS ++ "label"
def rdfsComment       : IRI := rdfsNS ++ "comment"
def rdfsSeeAlso       : IRI := rdfsNS ++ "seeAlso"
def rdfsIsDefinedBy   : IRI := rdfsNS ++ "isDefinedBy"

def xsdString             : IRI := xsdNS ++ "string"
def xsdInteger            : IRI := xsdNS ++ "integer"
def xsdNonNegativeInteger : IRI := xsdNS ++ "nonNegativeInteger"
def xsdDecimal            : IRI := xsdNS ++ "decimal"
def xsdDouble             : IRI := xsdNS ++ "double"
def xsdBoolean            : IRI := xsdNS ++ "boolean"

def owlOntology                  : IRI := owlNS ++ "Ontology"
def owlImports                   : IRI := owlNS ++ "imports"
def owlVersionIRI                : IRI := owlNS ++ "versionIRI"
def owlClass                     : IRI := owlNS ++ "Class"
def owlObjectProperty            : IRI := owlNS ++ "ObjectProperty"
def owlDatatypeProperty          : IRI := owlNS ++ "DatatypeProperty"
def owlAnnotationProperty        : IRI := owlNS ++ "AnnotationProperty"
def owlNamedIndividual           : IRI := owlNS ++ "NamedIndividual"
def owlRestriction               : IRI := owlNS ++ "Restriction"
def owlOnProperty                : IRI := owlNS ++ "onProperty"
def owlSomeValuesFrom            : IRI := owlNS ++ "someValuesFrom"
def owlAllValuesFrom             : IRI := owlNS ++ "allValuesFrom"
def owlHasValue                  : IRI := owlNS ++ "hasValue"
def owlHasSelf                   : IRI := owlNS ++ "hasSelf"
def owlMinCardinality            : IRI := owlNS ++ "minCardinality"
def owlMaxCardinality            : IRI := owlNS ++ "maxCardinality"
def owlCardinality               : IRI := owlNS ++ "cardinality"
def owlMinQualifiedCardinality   : IRI := owlNS ++ "minQualifiedCardinality"
def owlMaxQualifiedCardinality   : IRI := owlNS ++ "maxQualifiedCardinality"
def owlQualifiedCardinality      : IRI := owlNS ++ "qualifiedCardinality"
def owlOnClass                   : IRI := owlNS ++ "onClass"
def owlOnDataRange               : IRI := owlNS ++ "onDataRange"
def owlIntersectionOf            : IRI := owlNS ++ "intersectionOf"
def owlUnionOf                   : IRI := owlNS ++ "unionOf"
def owlComplementOf              : IRI := owlNS ++ "complementOf"
def owlOneOf                     : IRI := owlNS ++ "oneOf"
def owlDatatypeComplementOf      : IRI := owlNS ++ "datatypeComplementOf"
def owlOnDatatype                : IRI := owlNS ++ "onDatatype"
def owlWithRestrictions          : IRI := owlNS ++ "withRestrictions"
def owlInverseOf                 : IRI := owlNS ++ "inverseOf"
def owlPropertyChainAxiom        : IRI := owlNS ++ "propertyChainAxiom"
def owlEquivalentClass           : IRI := owlNS ++ "equivalentClass"
def owlDisjointWith              : IRI := owlNS ++ "disjointWith"
def owlAllDisjointClasses        : IRI := owlNS ++ "AllDisjointClasses"
def owlDisjointUnionOf           : IRI := owlNS ++ "disjointUnionOf"
def owlEquivalentProperty        : IRI := owlNS ++ "equivalentProperty"
def owlPropertyDisjointWith      : IRI := owlNS ++ "propertyDisjointWith"
def owlAllDisjointProperties     : IRI := owlNS ++ "AllDisjointProperties"
def owlFunctionalProperty        : IRI := owlNS ++ "FunctionalProperty"
def owlInverseFunctionalProperty : IRI := owlNS ++ "InverseFunctionalProperty"
def owlReflexiveProperty         : IRI := owlNS ++ "ReflexiveProperty"
def owlIrreflexiveProperty       : IRI := owlNS ++ "IrreflexiveProperty"
def owlSymmetricProperty         : IRI := owlNS ++ "SymmetricProperty"
def owlAsymmetricProperty        : IRI := owlNS ++ "AsymmetricProperty"
def owlTransitiveProperty        : IRI := owlNS ++ "TransitiveProperty"
def owlHasKey                    : IRI := owlNS ++ "hasKey"
def owlSameAs                    : IRI := owlNS ++ "sameAs"
def owlDifferentFrom             : IRI := owlNS ++ "differentFrom"
def owlAllDifferent              : IRI := owlNS ++ "AllDifferent"
def owlMembers                   : IRI := owlNS ++ "members"
def owlDistinctMembers           : IRI := owlNS ++ "distinctMembers"
def owlNegativePropertyAssertion : IRI := owlNS ++ "NegativePropertyAssertion"
def owlSourceIndividual          : IRI := owlNS ++ "sourceIndividual"
def owlAssertionProperty         : IRI := owlNS ++ "assertionProperty"
def owlTargetIndividual          : IRI := owlNS ++ "targetIndividual"
def owlTargetValue               : IRI := owlNS ++ "targetValue"
def owlAxiom                     : IRI := owlNS ++ "Axiom"
def owlAnnotation                : IRI := owlNS ++ "Annotation"
def owlAnnotatedSource           : IRI := owlNS ++ "annotatedSource"
def owlAnnotatedProperty         : IRI := owlNS ++ "annotatedProperty"
def owlAnnotatedTarget           : IRI := owlNS ++ "annotatedTarget"
def owlThing                     : IRI := owlNS ++ "Thing"
def owlNothing                   : IRI := owlNS ++ "Nothing"

def swrlNS                       : IRI := "http://www.w3.org/2003/11/swrl#"
def swrlbNS                      : IRI := "http://www.w3.org/2003/11/swrlb#"
def swrlaNS                      : IRI := "http://swrl.stanford.edu/ontologies/3.3/swrla.owl#"
def swrlImp                      : IRI := swrlNS ++ "Imp"
def swrlBody                     : IRI := swrlNS ++ "body"
def swrlHead                     : IRI := swrlNS ++ "head"
def swrlAtomList                 : IRI := swrlNS ++ "AtomList"
def swrlVariable                 : IRI := swrlNS ++ "Variable"
def swrlClassAtom                : IRI := swrlNS ++ "ClassAtom"
def swrlDataRangeAtom            : IRI := swrlNS ++ "DataRangeAtom"
def swrlIndividualPropertyAtom   : IRI := swrlNS ++ "IndividualPropertyAtom"
def swrlDatavaluedPropertyAtom   : IRI := swrlNS ++ "DatavaluedPropertyAtom"
def swrlSameIndividualAtom       : IRI := swrlNS ++ "SameIndividualAtom"
def swrlDifferentIndividualsAtom : IRI := swrlNS ++ "DifferentIndividualsAtom"
def swrlBuiltinAtom              : IRI := swrlNS ++ "BuiltinAtom"
def swrlClassPredicate           : IRI := swrlNS ++ "classPredicate"
def swrlPropertyPredicate        : IRI := swrlNS ++ "propertyPredicate"
def swrlDataRange                : IRI := swrlNS ++ "dataRange"
def swrlArgument1                : IRI := swrlNS ++ "argument1"
def swrlArgument2                : IRI := swrlNS ++ "argument2"
def swrlBuiltin                  : IRI := swrlNS ++ "builtin"
def swrlArguments                : IRI := swrlNS ++ "arguments"

/-- Convert an `RDFTerm.literal` into a SABRINA OWL 2 `Literal`, mapping
language-tagged RDF 1.1 literals to `rdf:PlainLiteral` (`"lex@lang"`). -/
def RDFTerm.toOwlLiteral : RDFTerm → Option Literal
  | .literal lex dt lang =>
    match lang with
    | some tag =>
      if tag.isEmpty then some ⟨lex, xsdString⟩
      else some ⟨s!"{lex}@{tag}", rdfPlainLiteral⟩
    | none =>
      if dt == rdfLangString then some ⟨lex, rdfPlainLiteral⟩
      else some ⟨lex, dt⟩
  | _ => none

/-! ### RFC 3986 Relative IRI Resolution -/

private def hasScheme (s : String) : Bool :=
  let cs := s.toList
  match cs with
  | [] => false
  | c :: rest =>
    c.isAlpha &&
    let rec go : List Char → Bool
      | [] => false
      | ':' :: _ => true
      | ch :: tl => (ch.isAlphanum || ch == '+' || ch == '-' || ch == '.') && go tl
    go rest

private def stripFragment (s : String) : String :=
  match s.splitOn "#" with
  | h :: _ => h
  | [] => s

private def baseDir (base : String) : String :=
  let noFrag := stripFragment base
  let noQuery := match noFrag.splitOn "?" with | h :: _ => h | [] => noFrag
  let rev := noQuery.toList.reverse
  match rev.dropWhile (· != '/') with
  | [] => noQuery
  | kept => String.ofList kept.reverse

private def schemeAuthority (base : String) : String :=
  match base.splitOn "://" with
  | sch :: rest :: _ =>
    let auth := match rest.splitOn "/" with | a :: _ => a | [] => rest
    s!"{sch}://{auth}"
  | _ => ""

/-- Resolve a possibly relative IRI reference against an optional base IRI per RFC 3986. -/
def resolveIRI (base? : Option IRI) (ref : String) : IRI :=
  if hasScheme ref then ref
  else match base? with
  | none => ref
  | some base =>
    if ref.isEmpty then stripFragment base
    else if ref.startsWith "#" then stripFragment base ++ ref
    else if ref.startsWith "/" then
      let sa := schemeAuthority base
      if sa.isEmpty then ref else sa ++ ref
    else
      baseDir base ++ ref

/-! ### Verified RDF List Encoding & Decoding -/

/-- Encode a list of RDF terms into standard `rdf:first` / `rdf:rest` / `rdf:nil` triples
using fresh blank nodes `mkId idx`. Returns `(headTerm, triples, nextIdx)`. -/
def encodeRDFListWith (mkId : Nat → String) : Nat → List RDFTerm → RDFTerm × List RDFTriple × Nat
  | idx, [] => (.iri rdfNil, [], idx)
  | idx, x :: xs =>
    let node := RDFTerm.bnode (mkId idx)
    let (tailHead, tailTriples, nextIdx) := encodeRDFListWith mkId (idx + 1) xs
    let ts := ⟨node, rdfFirst, x⟩ :: ⟨node, rdfRest, tailHead⟩ :: tailTriples
    (node, ts, nextIdx)

/-- Encode a list of RDF terms using readable blank-node identifiers `pfx ++ toString idx`. -/
def encodeRDFListAux (pfx : String) : Nat → List RDFTerm → RDFTerm × List RDFTriple × Nat :=
  encodeRDFListWith (fun i => s!"{pfx}{i}")

/-- Lookup the unique object for `(subject, predicate)` in a triple list. -/
def findObject (ts : List RDFTriple) (subj : RDFTerm) (pred : IRI) : Option RDFTerm :=
  (ts.find? fun t => t.subject == subj && t.predicate == pred).map (·.object)

/-- Total fuel-bounded decoder for `rdf:first` / `rdf:rest` / `rdf:nil` lists. -/
def parseRDFListAux (ts : List RDFTriple) : Nat → RDFTerm → Option (List RDFTerm)
  | 0, _ => none
  | fuel + 1, node =>
    if node == .iri rdfNil then some []
    else
      match findObject ts node rdfFirst, findObject ts node rdfRest with
      | some head, some rest =>
        (parseRDFListAux ts fuel rest).map (head :: ·)
      | _, _ => none

/-- Decode an RDF list rooted at `node` inside `ts`. -/
def parseRDFList (ts : List RDFTriple) (node : RDFTerm) : Option (List RDFTerm) :=
  parseRDFListAux ts (ts.length + 1) node

private theorem findObject_cons_eq (t : RDFTriple) (ts : List RDFTriple)
    (hs : t.subject = s) (hp : t.predicate = p) :
    findObject (t :: ts) s p = some t.object := by
  simp [findObject, List.find?, hs, hp]

private theorem findObject_cons_ne (t : RDFTriple) (ts : List RDFTriple)
    (h : ¬ (t.subject = s ∧ t.predicate = p)) :
    findObject (t :: ts) s p = findObject ts s p := by
  have hb : (t.subject == s && t.predicate == p) = false := by
    cases h1 : (t.subject == s) <;> cases h2 : (t.predicate == p)
    · rfl
    · rfl
    · rfl
    · exact absurd ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2⟩ h
  simp [findObject, List.find?, hb]

private theorem findObject_append_left (ts1 ts2 : List RDFTriple) (s : RDFTerm) (p : IRI)
    (h : ∀ t ∈ ts1, t.subject ≠ s) :
    findObject (ts1 ++ ts2) s p = findObject ts2 s p := by
  induction ts1 with
  | nil => rfl
  | cons t ts1 ih =>
    rw [List.cons_append, findObject_cons_ne]
    · exact ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    · rintro ⟨heq, _⟩
      exact h t (List.mem_cons_self ..) heq

private theorem parseRDFListAux_encode_prefix (mkId : Nat → String)
    (hinj : ∀ i j, mkId i = mkId j → i = j) (xs : List RDFTerm)
    (idx fuel : Nat) (hfuel : xs.length < fuel)
    (pre suf : List RDFTriple)
    (hpre : ∀ t ∈ pre, ∀ k ≥ idx, t.subject ≠ .bnode (mkId k)) :
    parseRDFListAux (pre ++ (encodeRDFListWith mkId idx xs).2.1 ++ suf) fuel
      (encodeRDFListWith mkId idx xs).1 = some xs := by
  induction xs generalizing idx fuel pre with
  | nil =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp [encodeRDFListWith, parseRDFListAux]
  | cons x xs ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.length_cons] at hfuel
      simp only [encodeRDFListWith]
      have hneNil : (RDFTerm.bnode (mkId idx) == RDFTerm.iri rdfNil) = false := by simp
      simp only [parseRDFListAux, hneNil, Bool.false_eq_true, ↓reduceIte]
      have h1 : findObject (pre ++ (⟨.bnode (mkId idx), rdfFirst, x⟩ ::
          ⟨.bnode (mkId idx), rdfRest, (encodeRDFListWith mkId (idx + 1) xs).1⟩ ::
          (encodeRDFListWith mkId (idx + 1) xs).2.1) ++ suf)
          (.bnode (mkId idx)) rdfFirst = some x := by
        rw [List.append_assoc, findObject_append_left pre _ _ _ (fun t ht => hpre t ht idx (Nat.le_refl _))]
        rw [List.cons_append]
        exact findObject_cons_eq _ _ rfl rfl
      have h2 : findObject (pre ++ (⟨.bnode (mkId idx), rdfFirst, x⟩ ::
          ⟨.bnode (mkId idx), rdfRest, (encodeRDFListWith mkId (idx + 1) xs).1⟩ ::
          (encodeRDFListWith mkId (idx + 1) xs).2.1) ++ suf)
          (.bnode (mkId idx)) rdfRest = some (encodeRDFListWith mkId (idx + 1) xs).1 := by
        rw [List.append_assoc, findObject_append_left pre _ _ _ (fun t ht => hpre t ht idx (Nat.le_refl _))]
        rw [List.cons_append, findObject_cons_ne]
        · rw [List.cons_append]
          exact findObject_cons_eq _ _ rfl rfl
        · intro ⟨_, hp⟩
          exact absurd hp (show rdfFirst ≠ rdfRest by decide)
      rw [h1, h2]
      dsimp only
      let pre' := pre ++ [⟨.bnode (mkId idx), rdfFirst, x⟩,
        ⟨.bnode (mkId idx), rdfRest, (encodeRDFListWith mkId (idx + 1) xs).1⟩]
      have hassoc : pre ++ (⟨.bnode (mkId idx), rdfFirst, x⟩ ::
          ⟨.bnode (mkId idx), rdfRest, (encodeRDFListWith mkId (idx + 1) xs).1⟩ ::
          (encodeRDFListWith mkId (idx + 1) xs).2.1) ++ suf =
          pre' ++ (encodeRDFListWith mkId (idx + 1) xs).2.1 ++ suf := by
        simp [pre', List.append_assoc]
      rw [hassoc]
      have hpre' : ∀ t ∈ pre', ∀ k ≥ idx + 1, t.subject ≠ .bnode (mkId k) := by
        intro t ht k hk
        simp only [pre', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with ht | rfl | rfl
        · exact hpre t ht k (Nat.le_trans (Nat.le_succ _) hk)
        · intro h; injection h with heq; have := hinj idx k heq; omega
        · intro h; injection h with heq; have := hinj idx k heq; omega
      rw [ih (idx + 1) f (by omega) pre' hpre']
      rfl

private theorem encodeRDFListWith_length (mkId : Nat → String) (idx : Nat) (xs : List RDFTerm) :
    (encodeRDFListWith mkId idx xs).2.1.length = 2 * xs.length := by
  induction xs generalizing idx with
  | nil => simp [encodeRDFListWith]
  | cons x xs ih =>
    simp only [encodeRDFListWith, List.length_cons, ih]
    omega

/-- Kernel-checked round-trip theorem: encoding any list of `RDFTerm`s into
`rdf:first`/`rdf:rest`/`rdf:nil` triples with any injective blank-node allocator
and decoding with `parseRDFList` recovers the exact original list. -/
theorem parseRDFList_encodeRDFListWith (mkId : Nat → String)
    (hinj : ∀ i j, mkId i = mkId j → i = j) (idx : Nat) (xs : List RDFTerm) :
    let res := encodeRDFListWith mkId idx xs
    parseRDFList res.2.1 res.1 = some xs := by
  dsimp only [parseRDFList]
  have hlen := encodeRDFListWith_length mkId idx xs
  have h := parseRDFListAux_encode_prefix mkId hinj xs idx
    ((encodeRDFListWith mkId idx xs).2.1.length + 1)
    (by omega) [] [] (by intro t ht; cases ht)
  simpa using h

#print axioms parseRDFList_encodeRDFListWith

end Sabrina.OWL2.RDF
