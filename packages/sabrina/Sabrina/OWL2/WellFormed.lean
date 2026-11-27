import Sabrina.OWL2.Normalize
import Sabrina.OWL2.FunctionalSyntax

/-! Structural well-formedness, reserved-vocabulary discipline, arity checks,
    global OWL 2 DL restriction validator with proved soundness & acceptance
    completeness, and multi-document import-closure flattening theorem with
    document-scoped anonymous individuals. -/

namespace Sabrina.OWL2.WellFormed

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes (datatypeMap supportedDatatype decodeLiteral checkApplicableFacet applicableFacet checkApplicableFacet_iff)
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.Normalize

/-! ### 1. Reserved Vocabulary, Arity, and Structural Typing Discipline (M1 / M3) -/

def isReservedPrefix (s : IRI) : Bool :=
  s.startsWith "http://www.w3.org/2002/07/owl#" ||
  s.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  s.startsWith "http://www.w3.org/2000/01/rdf-schema#" ||
  s.startsWith "http://www.w3.org/2001/XMLSchema#"

def validClassIRI (c : IRI) : Bool :=
  !c.isEmpty && (c == thing || c == nothing || !isReservedPrefix c)

def validObjPropIRI (r : IRI) : Bool :=
  !r.isEmpty && (r == topObjectProperty || r == bottomObjectProperty || !isReservedPrefix r)

def validDataPropIRI (dp : IRI) : Bool :=
  !dp.isEmpty && (dp == topDataProperty || dp == bottomDataProperty || !isReservedPrefix dp)

def validIndividual : Individual → Bool
  | .named a => !a.isEmpty && !isReservedPrefix a
  | .anonymous doc lid => !doc.isEmpty && !lid.isEmpty

def validObjProp : ObjectProperty → Bool
  | .named r | .inverse r => validObjPropIRI r

def checkLiteral (l : Literal) : Bool :=
  (decodeLiteral l).isSome

theorem checkLiteral_iff (l : Literal) :
    checkLiteral l = true ↔ datatypeMap.validLiteral l := by
  unfold checkLiteral DatatypeMap.validLiteral
  cases h : decodeLiteral l with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
    intro v hv
    change decodeLiteral l = some v at hv
    rw [h] at hv; cases hv
  | some v =>
    simp only [Option.isSome_some, true_iff]
    exact ⟨v, h⟩

def checkFacet (t : IRI) (f : Facet) : Bool :=
  match decodeLiteral f.bound with
  | some v => checkApplicableFacet t f.name v
  | none => false

theorem checkFacet_valid_iff (t : IRI) (f : Facet) (ht : supportedDatatype t = true) :
    checkFacet t f = true ↔ datatypeMap.validFacet t f := by
  unfold checkFacet DatatypeMap.validFacet
  cases h : decodeLiteral f.bound with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, v, hv, _⟩
    change decodeLiteral f.bound = some v at hv
    rw [h] at hv; cases hv
  | some v =>
    simp only [checkApplicableFacet_iff]
    constructor
    · intro ha
      exact ⟨ht, v, h, ha⟩
    · rintro ⟨_, v', hv', ha⟩
      change decodeLiteral f.bound = some v' at hv'
      rw [h] at hv'
      cases hv'
      exact ha

def checkDataRange (defs : DatatypeDefs) : DataRange → Bool
  | .datatype t => t == literalDatatype || supportedDatatype t || (defs.lookup t).isSome
  | .complement r => checkDataRange defs r
  | .intersection a b => checkDataRange defs a && checkDataRange defs b
  | .union a b => checkDataRange defs a && checkDataRange defs b
  | .oneOf ls => !ls.isEmpty && ls.all checkLiteral
  | .restriction t fs => supportedDatatype t && !fs.isEmpty && fs.all (checkFacet t)

inductive WellFormedDataRange (defs : DatatypeDefs) : DataRange → Prop where
  | datatype {t : IRI} :
      (t = literalDatatype ∨ supportedDatatype t = true ∨ (defs.lookup t).isSome = true) →
      WellFormedDataRange defs (.datatype t)
  | complement {r : DataRange} :
      WellFormedDataRange defs r → WellFormedDataRange defs (.complement r)
  | intersection {a b : DataRange} :
      WellFormedDataRange defs a → WellFormedDataRange defs b →
      WellFormedDataRange defs (.intersection a b)
  | union {a b : DataRange} :
      WellFormedDataRange defs a → WellFormedDataRange defs b →
      WellFormedDataRange defs (.union a b)
  | oneOf {ls : List Literal} :
      ls ≠ [] → (∀ l ∈ ls, datatypeMap.validLiteral l) →
      WellFormedDataRange defs (.oneOf ls)
  | restriction {t : IRI} {fs : List Facet} :
      supportedDatatype t = true → fs ≠ [] → (∀ f ∈ fs, datatypeMap.validFacet t f) →
      WellFormedDataRange defs (.restriction t fs)

theorem checkDataRange_iff (defs : DatatypeDefs) (d : DataRange) :
    checkDataRange defs d = true ↔ WellFormedDataRange defs d := by
  induction d with
  | datatype t =>
    simp only [checkDataRange, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h
      exact .datatype (h.elim (fun h1 => h1.elim Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr))
    · intro h
      cases h with
      | datatype h => exact h.elim (Or.inl ∘ Or.inl) (fun h2 => h2.elim (Or.inl ∘ Or.inr) Or.inr)
  | complement r ih =>
    simp only [checkDataRange, ih]
    exact ⟨.complement, fun h => by cases h with | complement h => exact h⟩
  | intersection a b iha ihb =>
    simp only [checkDataRange, Bool.and_eq_true, iha, ihb]
    exact ⟨fun ⟨ha, hb⟩ => .intersection ha hb,
           fun h => by cases h with | intersection ha hb => exact ⟨ha, hb⟩⟩
  | union a b iha ihb =>
    simp only [checkDataRange, Bool.and_eq_true, iha, ihb]
    exact ⟨fun ⟨ha, hb⟩ => .union ha hb,
           fun h => by cases h with | union ha hb => exact ⟨ha, hb⟩⟩
  | oneOf ls =>
    simp only [checkDataRange, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true, checkLiteral_iff]
    constructor
    · rintro ⟨hne, hall⟩
      exact .oneOf (by intro e; subst e; cases hne) hall
    · intro h
      cases h with
      | oneOf hne hall =>
        exact ⟨List.isEmpty_eq_false_iff.mpr hne, hall⟩
  | restriction t fs =>
    simp only [checkDataRange, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    constructor
    · rintro ⟨⟨ht, hne⟩, hall⟩
      exact .restriction ht (by intro e; subst e; cases hne)
        fun f hf => (checkFacet_valid_iff t f ht).mp (hall f hf)
    · intro h
      cases h with
      | restriction ht hne hall =>
        exact ⟨⟨ht, List.isEmpty_eq_false_iff.mpr hne⟩,
          fun f hf => (checkFacet_valid_iff t f ht).mpr (hall f hf)⟩

def checkClassExpr (defs : DatatypeDefs) : ClassExpr → Bool
  | .named c => validClassIRI c
  | .complement c => checkClassExpr defs c
  | .intersection a b | .union a b => checkClassExpr defs a && checkClassExpr defs b
  | .oneOf inds => !inds.isEmpty && inds.all validIndividual
  | .objectSome r c | .objectAll r c | .objectMin _ r c | .objectMax _ r c | .objectExact _ r c =>
    validObjProp r && checkClassExpr defs c
  | .objectValue r a => validObjProp r && validIndividual a
  | .objectSelf r => validObjProp r
  | .dataSome dp d | .dataAll dp d | .dataMin _ dp d | .dataMax _ dp d | .dataExact _ dp d =>
    validDataPropIRI dp && checkDataRange defs d
  | .dataValue dp l => validDataPropIRI dp && checkLiteral l

def checkAxiom (defs : DatatypeDefs) : Axiom → Bool
  | .subClassOf a b => checkClassExpr defs a && checkClassExpr defs b
  | .equivalentClasses cs | .disjointClasses cs =>
    decide (cs.length ≥ 2) && cs.all (checkClassExpr defs)
  | .disjointUnion h cs =>
    validClassIRI h && h != thing && h != nothing &&
    decide (cs.length ≥ 2) && cs.all (checkClassExpr defs)
  | .subObjectProperty r s | .inverseObjectProperties r s =>
    validObjProp r && validObjProp s
  | .subObjectPropertyChain rs h =>
    decide (rs.length ≥ 2) && rs.all validObjProp && validObjProp h
  | .equivalentObjectProperties rs | .disjointObjectProperties rs =>
    decide (rs.length ≥ 2) && rs.all validObjProp
  | .objectPropertyDomain r c | .objectPropertyRange r c =>
    validObjProp r && checkClassExpr defs c
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .reflexiveObjectProperty r | .irreflexiveObjectProperty r
  | .symmetricObjectProperty r | .asymmetricObjectProperty r
  | .transitiveObjectProperty r => validObjProp r
  | .subDataProperty r s => validDataPropIRI r && validDataPropIRI s
  | .equivalentDataProperties rs | .disjointDataProperties rs =>
    decide (rs.length ≥ 2) && rs.all validDataPropIRI
  | .dataPropertyDomain dp c => validDataPropIRI dp && checkClassExpr defs c
  | .dataPropertyRange dp d => validDataPropIRI dp && checkDataRange defs d
  | .functionalDataProperty dp => validDataPropIRI dp
  | .datatypeDefinition dt d => !dt.isEmpty && !isReservedPrefix dt && checkDataRange defs d
  | .hasKey c rs ds =>
    checkClassExpr defs c && (!rs.isEmpty || !ds.isEmpty) &&
    rs.all (fun | .named r => validObjPropIRI r | .inverse _ => false) &&
    ds.all validDataPropIRI
  | .sameIndividuals inds | .differentIndividuals inds =>
    decide (inds.length ≥ 2) && inds.all validIndividual
  | .classAssertion c a => checkClassExpr defs c && validIndividual a
  | .objectAssertion r a b | .negativeObjectAssertion r a b =>
    validObjProp r && validIndividual a && validIndividual b
  | .dataAssertion dp a l | .negativeDataAssertion dp a l =>
    validDataPropIRI dp && validIndividual a && checkLiteral l

/-- Global OWL 2 DL well-formedness predicate for an `Ontology`:
    1. Acyclic, duplicate-free, non-builtin `DatatypeDefinition`s,
    2. Reserved-vocabulary, structural typing, and arity validity on all axioms,
    3. Normalization into an `SROIQD.Problem`,
    4. Global simple-role restriction on all counting/self/irreflexive/asymmetric/disjoint roles,
    5. Global regular role-hierarchy restriction (`RoleChains.checkRegular`). -/
def WellFormedOntology (o : Ontology) : Prop :=
  ∃ (defs : DatatypeDefs) (problem : Problem),
    normalizeWithDefs o = some (defs, problem) ∧
    (∀ ax ∈ o, checkAxiom defs ax = true) ∧
    (∀ r ∈ problem.simpleRoles, RoleChains.SimpleRoles.Simple problem.rules problem.chains r) ∧
    RoleChains.checkRegular (RoleChains.inferRank problem.rules problem.chains) problem.rules problem.chains = true

theorem WellFormedOntology.ranked {o : Ontology} (h : WellFormedOntology o) :
    ∃ (defs : DatatypeDefs) (p : Problem),
      normalizeWithDefs o = some (defs, p) ∧
      RoleChains.Ranked (RoleChains.inferRank p.rules p.chains) p.rules p.chains := by
  obtain ⟨defs, p, hnorm, _, _, hreg⟩ := h
  exact ⟨defs, p, hnorm, RoleChains.checkRegular_sound hreg⟩

/-- Executable validator for `WellFormedOntology`. -/
def checkWellFormedOntology (o : Ontology) : Bool :=
  match normalizeWithDefs o with
  | none => false
  | some (defs, p) =>
    o.all (checkAxiom defs) &&
    p.checkSimple &&
    RoleChains.checkInferredRank p.rules p.chains

/-- Validator soundness and acceptance completeness for `WellFormedOntology`. -/
theorem checkWellFormedOntology_iff (o : Ontology) :
    checkWellFormedOntology o = true ↔ WellFormedOntology o := by
  unfold checkWellFormedOntology
  cases h : normalizeWithDefs o with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, _, hnorm, _, _, _⟩
    rw [h] at hnorm; cases hnorm
  | some pair =>
    rcases pair with ⟨defs, p⟩
    simp only [Bool.and_eq_true, List.all_eq_true, Problem.checkSimple_iff]
    constructor
    · rintro ⟨⟨hax, hsim⟩, hreg⟩
      exact ⟨defs, p, h, hax, hsim, hreg⟩
    · rintro ⟨defs', p', hnorm, hax, hsim, hreg⟩
      rw [h] at hnorm
      cases hnorm
      exact ⟨⟨hax, hsim⟩, hreg⟩

/-! ### 2. Multi-Document Import-Closure Flattening with Document-Scoped Anonymous Individuals (M2) -/

/-- Flatten a list of ontology documents in an import closure into a single ontology. -/
def flattenDocs (docs : List Ontology) : Ontology :=
  docs.foldr (· ++ ·) []

theorem flattenDocs_satisfies_iff (i : Interpretation dm) (docs : List Ontology) :
    satisfies i (flattenDocs docs) ↔ ∀ doc ∈ docs, satisfies i doc := by
  induction docs with
  | nil =>
    simp [flattenDocs, satisfies]
  | cons d tail ih =>
    simp only [flattenDocs, List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      exact ⟨fun ax hax => h ax (List.mem_append_left _ hax),
             ih.mp fun ax hax => h ax (List.mem_append_right _ hax)⟩
    · rintro ⟨hd, htail⟩ ax hax
      rcases List.mem_append.mp hax with h1 | h2
      · exact hd ax h1
      · exact ih.mpr htail ax h2

/-- Check that every anonymous individual in `ind` belongs to document scope `docId`. -/
def indInScope (docId : String) : Individual → Bool
  | .named _ => true
  | .anonymous d _ => d == docId

def classInScope (docId : String) : ClassExpr → Bool
  | .named _ | .objectSelf _ | .dataSome _ _ | .dataAll _ _
  | .dataValue _ _ | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => true
  | .complement c | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classInScope docId c
  | .intersection a b | .union a b => classInScope docId a && classInScope docId b
  | .oneOf inds => inds.all (indInScope docId)
  | .objectValue _ a => indInScope docId a

def axiomInScope (docId : String) : Axiom → Bool
  | .subClassOf a b => classInScope docId a && classInScope docId b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.all (classInScope docId)
  | .objectPropertyDomain _ c | .objectPropertyRange _ c
  | .dataPropertyDomain _ c | .hasKey c _ _ => classInScope docId c
  | .sameIndividuals inds | .differentIndividuals inds => inds.all (indInScope docId)
  | .classAssertion c a => classInScope docId c && indInScope docId a
  | .objectAssertion _ a b | .negativeObjectAssertion _ a b =>
    indInScope docId a && indInScope docId b
  | .dataAssertion _ a _ | .negativeDataAssertion _ a _ => indInScope docId a
  | _ => true

def docInScope (docId : String) (o : Ontology) : Bool :=
  o.all (axiomInScope docId)

private theorem ind_withAnonymous_congr {i : Interpretation dm}
    {a1 a2 : String → String → i.Object} {docId : String} {ind : Individual}
    (hsc : indInScope docId ind = true) (hagree : ∀ lid, a1 docId lid = a2 docId lid) :
    (i.withAnonymous a1).individuals ind = (i.withAnonymous a2).individuals ind := by
  cases ind with
  | named _ => rfl
  | anonymous d lid =>
    simp only [indInScope, beq_iff_eq] at hsc
    subst hsc
    exact hagree lid

private theorem dataHolds_withAnonymous_congr {i : Interpretation dm}
    (a1 a2 : String → String → i.Object) (y : i.Data) (d : DataRange) :
    dataHolds (i.withAnonymous a1) y d ↔ dataHolds (i.withAnonymous a2) y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ iha ihb => exact and_congr iha ihb
  | union _ _ iha ihb => exact or_congr iha ihb

private theorem classHolds_withAnonymous_congr {i : Interpretation dm}
    {a1 a2 : String → String → i.Object} {docId : String}
    (hagree : ∀ lid, a1 docId lid = a2 docId lid)
    {c : ClassExpr} (hsc : classInScope docId c = true) (x : i.Object) :
    classHolds (i.withAnonymous a1) x c ↔ classHolds (i.withAnonymous a2) x c := by
  induction c generalizing x with
  | named _ | objectSelf _ | dataValue _ _ => rfl
  | complement body ih => exact not_congr (ih hsc x)
  | intersection a b iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsc
    exact and_congr (iha h1 x) (ihb h2 x)
  | union a b iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsc
    exact or_congr (iha h1 x) (ihb h2 x)
  | oneOf inds =>
    simp only [classHolds]
    constructor
    · rintro ⟨ind, hm, heq⟩
      exact ⟨ind, hm, (ind_withAnonymous_congr (List.all_eq_true.mp hsc ind hm) hagree).symm.trans heq⟩
    · rintro ⟨ind, hm, heq⟩
      exact ⟨ind, hm, (ind_withAnonymous_congr (List.all_eq_true.mp hsc ind hm) hagree).trans heq⟩
  | objectSome r body ih =>
    exact exists_congr fun y => and_congr Iff.rfl (ih hsc y)
  | objectAll r body ih =>
    exact forall_congr' fun y => imp_congr Iff.rfl (ih hsc y)
  | objectValue r ind =>
    simp only [classHolds]
    rw [ind_withAnonymous_congr hsc hagree]
    rfl
  | objectMin n r body ih =>
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mpr (hp y hy).2⟩⟩⟩
  | objectMax n r body ih =>
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mpr (hp y hy).2⟩⟩⟩
  | objectExact n r body ih =>
    have hAt : ∀ k, AtLeast k (fun y => objectHolds (i.withAnonymous a1) r x y ∧ classHolds (i.withAnonymous a1) y body) ↔
        AtLeast k (fun y => objectHolds (i.withAnonymous a2) r x y ∧ classHolds (i.withAnonymous a2) y body) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih hsc y).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withAnonymous_congr a1 a2 y d)
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withAnonymous_congr a1 a2 y d)
  | dataMin n dp d =>
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mpr (hp y hy).2⟩⟩⟩
  | dataMax n dp d =>
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mpr (hp y hy).2⟩⟩⟩
  | dataExact n dp d =>
    have hAt : ∀ k, AtLeast k (fun y => (i.withAnonymous a1).dataProperties dp x y ∧ dataHolds (i.withAnonymous a1) y d) ↔
        AtLeast k (fun y => (i.withAnonymous a2).dataProperties dp x y ∧ dataHolds (i.withAnonymous a2) y d) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous_congr a1 a2 y d).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))

private theorem pairwise_congr_on_mem {α : Type} {xs : List α} {R S : α → α → Prop}
    (h : ∀ a ∈ xs, ∀ b ∈ xs, R a b ↔ S a b) :
    xs.Pairwise R ↔ xs.Pairwise S := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    simp only [List.pairwise_cons]
    refine and_congr (forall_congr' fun b => imp_congr_right fun hb =>
      h a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)) ?_
    exact ih fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

private theorem axiomHolds_withAnonymous_congr {i : Interpretation dm}
    {a1 a2 : String → String → i.Object} {docId : String}
    (hagree : ∀ lid, a1 docId lid = a2 docId lid)
    {ax : Axiom} (hsc : axiomInScope docId ax = true) :
    axiomHolds (i.withAnonymous a1) ax ↔ axiomHolds (i.withAnonymous a2) ax := by
  cases ax with
  | subClassOf a b =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsc
    exact forall_congr' fun x => imp_congr
      (classHolds_withAnonymous_congr hagree h1 x)
      (classHolds_withAnonymous_congr hagree h2 x)
  | equivalentClasses cs =>
    have hall := List.all_eq_true.mp hsc
    exact forall_congr' fun a => imp_congr_right fun ha =>
      forall_congr' fun b => imp_congr_right fun hb =>
        forall_congr' fun x => iff_congr
          (classHolds_withAnonymous_congr hagree (hall a ha) x)
          (classHolds_withAnonymous_congr hagree (hall b hb) x)
  | disjointClasses cs =>
    have hall := List.all_eq_true.mp hsc
    exact pairwise_congr_on_mem fun a ha b hb =>
      forall_congr' fun x => not_congr (and_congr
        (classHolds_withAnonymous_congr hagree (hall a ha) x)
        (classHolds_withAnonymous_congr hagree (hall b hb) x))
  | disjointUnion head cs =>
    have hall := List.all_eq_true.mp hsc
    refine and_congr (forall_congr' fun x => iff_congr Iff.rfl ?_) ?_
    · constructor
      · rintro ⟨c, hc, hcx⟩
        exact ⟨c, hc, (classHolds_withAnonymous_congr hagree (hall c hc) x).mp hcx⟩
      · rintro ⟨c, hc, hcx⟩
        exact ⟨c, hc, (classHolds_withAnonymous_congr hagree (hall c hc) x).mpr hcx⟩
    · exact pairwise_congr_on_mem fun a ha b hb =>
        forall_congr' fun x => not_congr (and_congr
          (classHolds_withAnonymous_congr hagree (hall a ha) x)
          (classHolds_withAnonymous_congr hagree (hall b hb) x))
  | objectPropertyDomain r c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl
      (classHolds_withAnonymous_congr hagree hsc x)
  | objectPropertyRange r c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl
      (classHolds_withAnonymous_congr hagree hsc y)
  | dataPropertyDomain dp c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl
      (classHolds_withAnonymous_congr hagree hsc x)
  | dataPropertyRange dp d =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl
      (dataHolds_withAnonymous_congr a1 a2 y d)
  | datatypeDefinition dt d =>
    exact forall_congr' fun y => iff_congr Iff.rfl (dataHolds_withAnonymous_congr a1 a2 y d)
  | hasKey c rs ds =>
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr (classHolds_withAnonymous_congr hagree hsc x)
        (imp_congr (classHolds_withAnonymous_congr hagree hsc y) Iff.rfl)
  | sameIndividuals inds =>
    have hall := List.all_eq_true.mp hsc
    exact forall_congr' fun a => imp_congr_right fun ha =>
      forall_congr' fun b => imp_congr_right fun hb => by
        rw [ind_withAnonymous_congr (hall a ha) hagree, ind_withAnonymous_congr (hall b hb) hagree]
        exact Iff.rfl
  | differentIndividuals inds =>
    have hall := List.all_eq_true.mp hsc
    exact pairwise_congr_on_mem fun a ha b hb => by
      rw [ind_withAnonymous_congr (hall a ha) hagree, ind_withAnonymous_congr (hall b hb) hagree]
      exact Iff.rfl
  | classAssertion c a =>
    obtain ⟨hc, ha⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [axiomHolds]
    rw [ind_withAnonymous_congr ha hagree]
    exact classHolds_withAnonymous_congr hagree hc _
  | objectAssertion r a b =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [axiomHolds]
    rw [ind_withAnonymous_congr ha hagree, ind_withAnonymous_congr hb hagree]
    rfl
  | negativeObjectAssertion r a b =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsc
    simp only [axiomHolds]
    rw [ind_withAnonymous_congr ha hagree, ind_withAnonymous_congr hb hagree]
    rfl
  | dataAssertion dp a l =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_congr hsc hagree]
    rfl
  | negativeDataAssertion dp a l =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_congr hsc hagree]
    rfl
  | subObjectPropertyChain rs s =>
    have hrp : ∀ (ps : List ObjectProperty) (x y : i.Object),
        rolePath (i.withAnonymous a1) ps x y ↔ rolePath (i.withAnonymous a2) ps x y := fun ps => by
      induction ps with
      | nil => intro _ _; rfl
      | cons r tail ih =>
        intro x y; exact exists_congr fun z => and_congr Iff.rfl (ih z y)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr (hrp rs x y) Iff.rfl
  | _ => rfl

/-- M2 Import-Closure Flattening Theorem:
    Given a list of `(docId, ontology)` documents in an import closure with
    pairwise distinct `docId`s (`(scopedDocs.map Prod.fst).Nodup`) where each
    document's anonymous individuals are scoped to its `docId` (`docInScope`),
    an interpretation `i` models the flattened union ontology
    `flattenDocs (scopedDocs.map Prod.snd)` if and only if `i` models every
    document in the import closure. -/
theorem scopedImports_models_iff (i : Interpretation dm)
    (scopedDocs : List (String × Ontology))
    (hnd : (scopedDocs.map Prod.fst).Nodup)
    (hscoped : ∀ p ∈ scopedDocs, docInScope p.1 p.2 = true) :
    models i (flattenDocs (scopedDocs.map Prod.snd)) ↔
      ∀ p ∈ scopedDocs, models i p.2 := by
  classical
  constructor
  · rintro ⟨assign, hsat⟩ p hp
    have hmem : p.2 ∈ scopedDocs.map Prod.snd := List.mem_map_of_mem hp
    exact ⟨assign, (flattenDocs_satisfies_iff (i.withAnonymous assign) _).mp hsat p.2 hmem⟩
  · intro hall
    induction scopedDocs with
    | nil =>
      obtain ⟨x0⟩ := i.objectNonempty
      exact ⟨fun _ _ => x0, by simp [flattenDocs, satisfies]⟩
    | cons hd tail ih =>
      rcases hd with ⟨docId, doc⟩
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨aDoc, hsatDoc⟩ := hall (docId, doc) (List.mem_cons_self ..)
      obtain ⟨aTail, hsatTail⟩ := ih hnd.2
        (fun p hp => hscoped p (List.mem_cons_of_mem _ hp))
        (fun p hp => hall p (List.mem_cons_of_mem _ hp))
      let aCombined : String → String → i.Object := fun d lid =>
        if d = docId then aDoc d lid else aTail d lid
      refine ⟨aCombined, ?_⟩
      rw [List.map_cons, flattenDocs_satisfies_iff]
      intro d hdMem
      rcases List.mem_cons.mp hdMem with rfl | hdTail
      · intro ax hax
        have hscAx : axiomInScope docId ax = true :=
          List.all_eq_true.mp (hscoped (docId, d) (List.mem_cons_self ..)) ax hax
        exact (axiomHolds_withAnonymous_congr (fun lid => by simp [aCombined]) hscAx).mpr (hsatDoc ax hax)
      · obtain ⟨⟨dId, dOnt⟩, hpMem, rfl⟩ := List.mem_map.mp hdTail
        have hne : dId ≠ docId := by
          intro heq
          subst heq
          exact hnd.1 (List.mem_map.mpr ⟨(dId, dOnt), hpMem, rfl⟩)
        have hsatD : satisfies (i.withAnonymous aTail) dOnt :=
          (flattenDocs_satisfies_iff (i.withAnonymous aTail) _).mp hsatTail dOnt hdTail
        intro ax hax
        have hscAx : axiomInScope dId ax = true :=
          List.all_eq_true.mp (hscoped (dId, dOnt) (List.mem_cons_of_mem _ hpMem)) ax hax
        exact (axiomHolds_withAnonymous_congr (fun lid => by simp [aCombined, hne]) hscAx).mpr (hsatD ax hax)

end Sabrina.OWL2.WellFormed
