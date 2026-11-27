import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQUniversal
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQBridge
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQDecision
import Sabrina.OWL2.SROIQD.Termination.SROIQDecidable

/-! Textbook SRIQ ABox syntax, semantics (without a unique-name assumption),
two-way model preservation to typed OWL 2 ontologies, source-fragment admission
characterization, and fuel-free decision via the cyclic forest solver and finite
grounding for the universal fragment.

Following Horrocks, Kutz, and Sattler (*The Irresistible SRIQ* / *The Even More
Irresistible SROIQ*, Sections 2.1–2.2), individual names are mapped to the
object domain by an arbitrary function `individuals : String → Object` (no
unique-name assumption). Negated role assertions `¬R(a, b)` are supported for
arbitrary (including inverse and composite) roles `R` in both the textbook
semantics and the forest solver; the stricter simplicity predicate
`ABoxAssertion.simpleNegRole` is also recorded for comparison. -/

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank checkRegular findRank)
open Sabrina.OWL2.SROIQD.Termination.BlockedForest
  (decideSROIQBool decideSROIQBool_ontology_iff)

/-! ### 2. Typed OWL 2 translation and two-way model preservation -/

def encodeInd (a : String) : Individual := .named (encodeName a)

def ABoxAssertion.toOWL : ABoxAssertion → Axiom
  | .concept c a => .classAssertion c.toOWL (encodeInd a)
  | .role r a b => .objectAssertion r.toOWL (encodeInd a) (encodeInd b)
  | .negRole r a b => .negativeObjectAssertion r.toOWL (encodeInd a) (encodeInd b)
  | .same a b => .sameIndividuals [encodeInd a, encodeInd b]
  | .different a b => .differentIndividuals [encodeInd a, encodeInd b]

def KnowledgeBase.toOWL (kb : KnowledgeBase) : Ontology :=
  kb.tboxRBox.toOWL ++ kb.abox.map ABoxAssertion.toOWL

theorem TBoxRBox.toKB_toOWL (o : TBoxRBox) : o.toKB.toOWL = o.toOWL := by
  simp [TBoxRBox.toKB, KnowledgeBase.toOWL]

private def Model.toALC' (m : Model) : ALC.Interpretation :=
  ⟨m.Object, m.nonempty, m.classes, m.relations⟩

/-- Forget the data sort and read the translated object and individual signature. -/
def ABoxModel.fromOWL {d : DatatypeMap} (i : Interpretation d) : ABoxModel where
  toModel := Model.fromOWL i
  individuals := GradedBridge.reductNom i

/-- Expand an ABox object model to an OWL 2 interpretation over any datatype map,
preserving the object carrier, all translated relations, and all individual
denotations (including non-injective name assignments). -/
noncomputable def ABoxModel.toOWL (m : ABoxModel) (d : DatatypeMap) : Interpretation d :=
  GradedBridge.extend d m.toModel.toALC' m.individuals

theorem ABoxModel.fromOWL_toOWL (m : ABoxModel) (d : DatatypeMap) :
    ABoxModel.fromOWL (m.toOWL d) = m := by
  rcases m with ⟨m₀, inds⟩
  have hmod : Model.fromOWL (GradedBridge.extend d m₀.toALC' inds) = m₀ := by
    unfold Model.fromOWL
    rw [GradedBridge.reduct_extend d m₀.toALC' inds]
    rfl
  have hind : GradedBridge.reductNom (GradedBridge.extend d m₀.toALC' inds) = inds :=
    GradedBridge.reductNom_extend d m₀.toALC' inds
  exact (ABoxModel.mk.injEq ..).mpr ⟨hmod, heq_of_eq hind⟩

theorem aboxAssertion_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (a : ABoxAssertion) :
    axiomHolds i a.toOWL ↔ (ABoxModel.fromOWL i).holdsABox a := by
  cases a with
  | concept c x =>
    exact holds_fromOWL_iff i c (i.individuals (encodeInd x))
  | role r x y =>
    exact edge_fromOWL_iff i r (i.individuals (encodeInd x)) (i.individuals (encodeInd y))
  | negRole r x y =>
    exact not_congr (edge_fromOWL_iff i r (i.individuals (encodeInd x)) (i.individuals (encodeInd y)))
  | same x y =>
    simp only [ABoxAssertion.toOWL, axiomHolds, ABoxModel.holdsABox, ABoxModel.fromOWL,
      GradedBridge.reductNom, encodeInd, encodeName]
    constructor
    · intro h
      exact h (.named (GradedBridge.symbol x)) (by simp) (.named (GradedBridge.symbol y)) (by simp)
    · intro h u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
  | different x y =>
    simp only [ABoxAssertion.toOWL, axiomHolds, List.pairwise_cons, List.mem_singleton,
      forall_eq, List.Pairwise.nil, and_true, ABoxModel.holdsABox, ABoxModel.fromOWL,
      GradedBridge.reductNom, encodeInd, encodeName]
    exact ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩

theorem kb_models_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (kb : KnowledgeBase) :
    satisfies i kb.toOWL ↔ (ABoxModel.fromOWL i).Models kb := by
  constructor
  · intro h
    refine ⟨(models_fromOWL_iff i kb.tboxRBox).mp ?_, ?_⟩
    · intro ax hax
      exact h ax (List.mem_append_left _ hax)
    · intro a ha
      exact (aboxAssertion_fromOWL_iff i a).mp
        (h _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
  · rintro ⟨htr, hab⟩ ax hax
    rcases List.mem_append.mp hax with h1 | h2
    · exact (models_fromOWL_iff i kb.tboxRBox).mpr htr ax h1
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h2
      exact (aboxAssertion_fromOWL_iff i a).mpr (hab a ha)

theorem kb_satisfiable_toOWL_iff (d : DatatypeMap) (kb : KnowledgeBase) :
    Satisfiable d kb.toOWL ↔ kb.Sat := by
  constructor
  · rintro ⟨i, assign, hi⟩
    exact ⟨_, (kb_models_fromOWL_iff (i.withAnonymous assign) kb).mp hi⟩
  · rintro ⟨m, hm⟩
    refine ⟨m.toOWL d, satisfies_models ((kb_models_fromOWL_iff _ _).mpr ?_)⟩
    rwa [ABoxModel.fromOWL_toOWL]

/-! ### 3. Source-fragment normalization, purity, and admission characterization -/

private theorem encodeName_head (s : String) : (encodeName s).toList.head? = some 'u' := by
  change ("urn:sabrina:graded:" ++ s).toList.head? = some 'u'
  simp

private theorem encodeName_ne_of_head_h (s : String) {iri : IRI}
    (h : iri.toList.head? = some 'h') : encodeName s ≠ iri := by
  intro he
  have hb := congrArg (fun r : IRI => r.toList.head?) he
  rw [encodeName_head, h] at hb
  cases hb

theorem encodeName_isCoreClass (s : String) : isCoreClassIRI (encodeName s) = true := by
  have h1 : encodeName s ≠ thing := encodeName_ne_of_head_h s rfl
  have h2 : encodeName s ≠ nothing := encodeName_ne_of_head_h s rfl
  simp [isCoreClassIRI, h1, h2]

theorem encodeName_isCoreObjProp (s : String) : isCoreObjPropIRI (encodeName s) = true := by
  have h1 : encodeName s ≠ topObjectProperty := encodeName_ne_of_head_h s rfl
  have h2 : encodeName s ≠ bottomObjectProperty := encodeName_ne_of_head_h s rfl
  simp [isCoreObjPropIRI, h1, h2]

private theorem normClassExpr_toOWL_isSROIQ (c : Concept) :
    (Normalize.normClassExpr c.toOWL).isSROIQ = true := by
  induction c with
  | atom name =>
    have h1 : encodeName name ≠ thing := encodeName_ne_of_head_h name rfl
    have h2 : encodeName name ≠ nothing := encodeName_ne_of_head_h name rfl
    simp [Concept.toOWL, Normalize.normClassExpr, h1, h2, SROIQD.Concept.isSROIQ, encodeName_isCoreClass]
  | top =>
    simp [Concept.toOWL, Normalize.normClassExpr, SROIQD.Concept.isSROIQ]
  | bottom =>
    have h : (nothing == thing) = false := by decide
    simp [Concept.toOWL, Normalize.normClassExpr, h, SROIQD.Concept.isSROIQ]
  | neg c ih =>
    simpa [Concept.toOWL, Normalize.normClassExpr, SROIQD.Concept.isSROIQ_dual] using ih
  | conj a b iha ihb | disj a b iha ihb =>
    simp [Concept.toOWL, Normalize.normClassExpr, SROIQD.Concept.isSROIQ, iha, ihb]
  | some r c ih | all r c ih | min _ r c ih | max _ r c ih =>
    cases r <;> simp [Concept.toOWL, Role.toOWL, Normalize.normClassExpr, Normalize.toOriented,
      SROIQD.Concept.isSROIQ, encodeName_isCoreObjProp, ih]
  | self r =>
    cases r <;> simp [Concept.toOWL, Role.toOWL, Normalize.normClassExpr, Normalize.toOriented,
      SROIQD.Concept.isSROIQ, encodeName_isCoreObjProp]

private theorem unfoldClassExpr_toOWL (c : Concept) :
    Normalize.unfoldClassExpr [] c.toOWL = some c.toOWL := by
  induction c with
  | atom _ | top | bottom | self _ => rfl
  | neg _ ih => simp [Concept.toOWL, Normalize.unfoldClassExpr, ih]
  | conj _ _ iha ihb | disj _ _ iha ihb =>
    simp [Concept.toOWL, Normalize.unfoldClassExpr, iha, ihb]
  | some _ _ ih | all _ _ ih | min _ _ _ ih | max _ _ _ ih =>
    simp [Concept.toOWL, Normalize.unfoldClassExpr, ih]

/-- Structural invariant satisfied by every `Problem` produced by normalizing
a translated textbook `KnowledgeBase`: root `⊤`, core object-only SROIQ syntax,
and empty data/key components. -/
structure PureTextbookProblem (p : Problem) : Prop where
  root : p.root = .top
  tbox : ∀ q ∈ p.tbox, q.sub.isSROIQ = true ∧ q.sup.isSROIQ = true
  rules : ∀ rs ∈ p.rules, isCoreObjPropIRI rs.1.1 = true ∧ isCoreObjPropIRI rs.2.1 = true
  chains : ∀ c ∈ p.chains, isCoreObjPropIRI c.head = true ∧ ∀ r ∈ c.bodyNames, isCoreObjPropIRI r = true
  reflexive : ∀ r ∈ p.chars.reflexive, isCoreObjPropIRI r = true
  irreflexive : ∀ r ∈ p.chars.irreflexive, isCoreObjPropIRI r = true
  asymmetric : ∀ r ∈ p.chars.asymmetric, isCoreObjPropIRI r = true
  disjoint : ∀ rs ∈ p.chars.disjoint, isCoreObjPropIRI rs.1.1 = true ∧ isCoreObjPropIRI rs.2.1 = true
  classAssertions : ∀ ac ∈ p.classAssertions, ac.2.isSROIQ = true
  objAssertions : ∀ rab ∈ p.objAssertions, isCoreObjPropIRI rab.1 = true
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, isCoreObjPropIRI rab.1 = true
  keys : p.keys = []
  subData : p.subData = []
  disjointData : p.disjointData = []
  funcData : p.funcData = []
  dataRanges : p.dataRanges = []
  dataAssertions : p.dataAssertions = []
  negDataAssertions : p.negDataAssertions = []

private theorem pureTextbookProblem_empty : PureTextbookProblem {} := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> simp

theorem PureTextbookProblem.isSROIQ_iff {p : Problem} (hp : PureTextbookProblem p) (rank : Rank) :
    p.isSROIQ rank = true ↔ p.checkSimple = true ∧ checkRegular rank p.rules p.chains = true := by
  have hroot : p.root.isSROIQ = true := by rw [hp.root]; rfl
  simp only [Problem.isSROIQ, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff,
    hroot, hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges,
    hp.dataAssertions, hp.negDataAssertions]
  constructor
  · intro h; exact ⟨h.1.2, h.2⟩
  · rintro ⟨hs, hr⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, hp.tbox⟩, hp.rules⟩, hp.chains⟩,
      hp.reflexive⟩, hp.irreflexive⟩, hp.asymmetric⟩, hp.disjoint⟩, hp.classAssertions⟩,
      hp.objAssertions⟩, hp.negObjAssertions⟩, by simp⟩, trivial⟩, trivial⟩, trivial⟩,
      trivial⟩, trivial⟩, trivial⟩, hs⟩, hr⟩

private def IsTextbookAxiom (ax : Axiom) : Prop :=
  (∃ c₁ c₂ : Concept, ax = .subClassOf c₁.toOWL c₂.toOWL) ∨
  (∃ a : Inclusion, ax = a.toOWL) ∨
  (∃ a : RoleAssertion, ax = a.toOWL) ∨
  (∃ a : ABoxAssertion, ax = a.toOWL)

private theorem toOWL_isTextbookAxiom (kb : KnowledgeBase) :
    ∀ ax ∈ kb.toOWL, IsTextbookAxiom ax := by
  intro ax hax
  simp only [KnowledgeBase.toOWL, TBoxRBox.toOWL, List.mem_append, List.mem_map] at hax
  rcases hax with ((⟨gci, _, rfl⟩ | ⟨inc, _, rfl⟩) | ⟨ra, _, rfl⟩) | ⟨ab, _, rfl⟩
  · exact Or.inl ⟨gci.1, gci.2, rfl⟩
  · exact Or.inr (Or.inl ⟨inc, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ra, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ab, rfl⟩))

private theorem collectDefs_of_textbook {o : Ontology} (h : ∀ ax ∈ o, IsTextbookAxiom ax) :
    Normalize.collectDefs o = some [] := by
  induction o with
  | nil => rfl
  | cons ax rest ih =>
    have hrest := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hax := h ax (List.mem_cons_self ..)
    rcases hax with ⟨c₁, c₂, rfl⟩ | ⟨inc, rfl⟩ | ⟨ra, rfl⟩ | ⟨ab, rfl⟩
    · simpa [Normalize.collectDefs] using hrest
    · rcases inc with ⟨f, _ | ⟨r, rs⟩, head⟩ <;>
        simpa [Inclusion.toOWL, Normalize.collectDefs] using hrest
    · cases ra <;> simpa [RoleAssertion.toOWL, Normalize.collectDefs] using hrest
    · cases ab <;> simpa [ABoxAssertion.toOWL, Normalize.collectDefs] using hrest

private theorem unfoldAxiom_of_textbook {ax : Axiom} (h : IsTextbookAxiom ax) :
    Normalize.unfoldAxiom [] ax = some (some ax) := by
  rcases h with ⟨c₁, c₂, rfl⟩ | ⟨inc, rfl⟩ | ⟨ra, rfl⟩ | ⟨ab, rfl⟩
  · simp [Normalize.unfoldAxiom, unfoldClassExpr_toOWL]
  · rcases inc with ⟨f, _ | ⟨r, rs⟩, head⟩ <;> rfl
  · cases ra with
    | localReflexive r =>
      simp [RoleAssertion.toOWL, Normalize.unfoldAxiom, Normalize.unfoldClassExpr]
    | irreflexive _ | symmetric _ | transitive _ | disjoint _ _ => rfl
  · cases ab with
    | concept c a =>
      simp [ABoxAssertion.toOWL, Normalize.unfoldAxiom, unfoldClassExpr_toOWL]
    | role _ _ _ | negRole _ _ _ | same _ _ | different _ _ => rfl

private theorem mapM_unfoldAxiom_of_textbook {o : Ontology} (h : ∀ ax ∈ o, IsTextbookAxiom ax) :
    o.mapM (Normalize.unfoldAxiom []) = some (o.map some) := by
  induction o with
  | nil => rfl
  | cons ax rest ih =>
    have h1 := unfoldAxiom_of_textbook (h ax (List.mem_cons_self ..))
    have h2 := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp [List.mapM_cons, h1, h2]

theorem unfoldOntology_kb_toOWL (kb : KnowledgeBase) :
    Normalize.unfoldOntology kb.toOWL = some ([], kb.toOWL) := by
  have hall := toOWL_isTextbookAxiom kb
  have hcol := collectDefs_of_textbook hall
  have hmap := mapM_unfoldAxiom_of_textbook hall
  have hfm : (kb.toOWL.map some).filterMap id = kb.toOWL := by
    induction kb.toOWL with
    | nil => rfl
    | cons a rest ih => simp [ih]
  simp [Normalize.unfoldOntology, hcol, Normalize.defsAcyclic, hmap, hfm]

private theorem addAxiom_of_textbook {p : Problem} (hp : PureTextbookProblem p)
    {ax : Axiom} (hax : IsTextbookAxiom ax) :
    ∃ p', Normalize.addAxiom p ax = some p' ∧ PureTextbookProblem p' := by
  rcases hax with ⟨c₁, c₂, rfl⟩ | ⟨inc, rfl⟩ | ⟨ra, rfl⟩ | ⟨ab, rfl⟩
  · refine ⟨_, rfl, ⟨hp.root, ?_, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
      hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
      hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
      hp.negDataAssertions⟩⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact ⟨normClassExpr_toOWL_isSROIQ c₁, normClassExpr_toOWL_isSROIQ c₂⟩
    · exact hp.tbox q hmem
  · rcases inc with ⟨first, rest, head⟩
    cases rest with
    | nil =>
      change ∃ p', Normalize.addAxiom p (.subObjectProperty first.toOWL (.named (encodeName head))) = some p' ∧ PureTextbookProblem p'
      simp only [Normalize.addAxiom]
      split
      · exact ⟨p, rfl, hp⟩
      · refine ⟨_, rfl, ⟨hp.root, hp.tbox, ?_, hp.chains, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro rs hrs
        rcases List.mem_cons.mp hrs with rfl | hmem
        · cases first <;> simp [Role.toOWL, Normalize.toOriented, encodeName_isCoreObjProp]
        · exact hp.rules rs hmem
    | cons r rs =>
      let ch : RoleChains.Chain :=
        ⟨((first :: r :: rs).map Role.toOWL).map Normalize.toOriented, encodeName head⟩
      have hadd : Normalize.addAxiom p
          (.subObjectPropertyChain ((first :: r :: rs).map Role.toOWL) (.named (encodeName head))) =
          some { p with chains := ch :: p.chains } := by
        simp only [Normalize.addAxiom, List.length_map, List.length_cons]
        have hlt : ¬ (rs.length + 1 + 1 < 2) := by omega
        simp only [hlt, ↓reduceIte]
        rfl
      refine ⟨{ p with chains := ch :: p.chains }, hadd,
        ⟨hp.root, hp.tbox, hp.rules, ?_, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · refine ⟨encodeName_isCoreObjProp head, ?_⟩
        intro rn hrn
        simp only [ch, RoleChains.Chain.bodyNames, List.mem_map] at hrn
        obtain ⟨orole, ⟨op, ⟨tr, _, rfl⟩, rfl⟩, rfl⟩ := hrn
        cases tr <;> simp [Role.toOWL, Normalize.toOriented, encodeName_isCoreObjProp]
      · exact hp.chains c hmem
  · cases ra with
    | localReflexive r =>
      refine ⟨_, rfl, ⟨hp.root, ?_, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
        hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
        hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
        hp.negDataAssertions⟩⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · cases r <;> simp [Role.toOWL, Normalize.normClassExpr, Normalize.toOriented,
          SROIQD.Concept.isSROIQ, encodeName_isCoreObjProp]
      · exact hp.tbox q hmem
    | irreflexive r =>
      cases r with
      | named name | inverse name =>
        refine ⟨{ p with chars := { p.chars with irreflexive := encodeName name :: p.chars.irreflexive } },
          rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, ?_,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro rn hrn
        rcases List.mem_cons.mp hrn with rfl | hmem
        · exact encodeName_isCoreObjProp name
        · exact hp.irreflexive rn hmem
    | symmetric r =>
      cases r with
      | named name | inverse name =>
        refine ⟨{ p with rules := ((encodeName name, true), (encodeName name, false)) :: p.rules },
          rfl, ⟨hp.root, hp.tbox, ?_, hp.chains, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro rs hrs
        rcases List.mem_cons.mp hrs with rfl | hmem
        · exact ⟨encodeName_isCoreObjProp name, encodeName_isCoreObjProp name⟩
        · exact hp.rules rs hmem
    | transitive r =>
      cases r with
      | named name | inverse name =>
        refine ⟨{ p with chains := RoleChains.Chain.named [encodeName name, encodeName name] (encodeName name) :: p.chains },
          rfl, ⟨hp.root, hp.tbox, hp.rules, ?_, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hmem
        · simp [RoleChains.Chain.named, RoleChains.Chain.bodyNames, encodeName_isCoreObjProp]
        · exact hp.chains c hmem
    | disjoint r s =>
      have hadd : Normalize.addAxiom p (RoleAssertion.disjoint r s).toOWL =
          some { p with chars := { p.chars with
            disjoint := (Normalize.toOriented r.toOWL, Normalize.toOriented s.toOWL) :: p.chars.disjoint } } := rfl
      refine ⟨_, hadd, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
        hp.asymmetric, ?_, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
        hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
        hp.negDataAssertions⟩⟩
      intro pq hpq
      rcases List.mem_cons.mp hpq with rfl | hmem
      · cases r <;> cases s <;>
          simp [Role.toOWL, Normalize.toOriented, encodeName_isCoreObjProp]
      · exact hp.disjoint pq hmem
  · cases ab with
    | concept c a =>
      refine ⟨_, rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
        hp.asymmetric, hp.disjoint, ?_, hp.objAssertions, hp.negObjAssertions,
        hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
        hp.negDataAssertions⟩⟩
      intro ac hac
      rcases List.mem_cons.mp hac with rfl | hmem
      · exact normClassExpr_toOWL_isSROIQ c
      · exact hp.classAssertions ac hmem
    | role r a b =>
      cases r with
      | named name | inverse name =>
        refine ⟨_, rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, ?_, hp.negObjAssertions,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro rab hrab
        rcases List.mem_cons.mp hrab with rfl | hmem
        · exact encodeName_isCoreObjProp name
        · exact hp.objAssertions rab hmem
    | negRole r a b =>
      cases r with
      | named name | inverse name =>
        refine ⟨_, rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
          hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, ?_,
          hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
          hp.negDataAssertions⟩⟩
        intro rab hrab
        rcases List.mem_cons.mp hrab with rfl | hmem
        · exact encodeName_isCoreObjProp name
        · exact hp.negObjAssertions rab hmem
    | same a b =>
      exact ⟨_, rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
        hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
        hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
        hp.negDataAssertions⟩⟩
    | different a b =>
      exact ⟨_, rfl, ⟨hp.root, hp.tbox, hp.rules, hp.chains, hp.reflexive, hp.irreflexive,
        hp.asymmetric, hp.disjoint, hp.classAssertions, hp.objAssertions, hp.negObjAssertions,
        hp.keys, hp.subData, hp.disjointData, hp.funcData, hp.dataRanges, hp.dataAssertions,
        hp.negDataAssertions⟩⟩

private theorem foldlM_addAxiom_of_textbook {o : Ontology} {p : Problem}
    (hp : PureTextbookProblem p) (ho : ∀ ax ∈ o, IsTextbookAxiom ax) :
    ∃ p', o.foldlM Normalize.addAxiom p = some p' ∧ PureTextbookProblem p' := by
  induction o generalizing p with
  | nil => exact ⟨p, rfl, hp⟩
  | cons ax rest ih =>
    obtain ⟨p₁, h1, hp₁⟩ := addAxiom_of_textbook hp (ho ax (List.mem_cons_self ..))
    obtain ⟨p₂, h2, hp₂⟩ := ih hp₁ fun a ha => ho a (List.mem_cons_of_mem _ ha)
    exact ⟨p₂, by simp [List.foldlM_cons, h1, h2], hp₂⟩

/-- Every translated textbook `KnowledgeBase` normalizes unconditionally to a
pure core object-only `Problem` with `p.root = .top`. -/
theorem normalizeWithDefs_kb_toOWL (kb : KnowledgeBase) :
    ∃ p : Problem,
      Normalize.normalizeWithDefs kb.toOWL = some ([], p) ∧
      PureTextbookProblem p := by
  obtain ⟨p, hnorm, hp⟩ :=
    foldlM_addAxiom_of_textbook pureTextbookProblem_empty (toOWL_isTextbookAxiom kb)
  refine ⟨p, ?_, hp⟩
  simp [Normalize.normalizeWithDefs, unfoldOntology_kb_toOWL, Normalize.normalize, hnorm]

/-! ### 4. Fuel-free decision procedure via the cyclic forest solver -/

/-- Source-fragment admission boundary for a textbook `KnowledgeBase`: since
translation and normalization always succeed with `p.root = .top` and pure core
object syntax, admission reduces exactly to normalized simplicity and existence
of a regular rank. -/
def KnowledgeBase.RankAdmitted (kb : KnowledgeBase) : Prop :=
  ∃ (p : Problem) (rank : Rank),
    Normalize.normalizeWithDefs kb.toOWL = some ([], p) ∧
    p.checkSimple = true ∧
    checkRegular rank p.rules p.chains = true

/-- Terminating, fuel-free satisfiability decision for an admitted textbook
SRIQ knowledge base (TBox + RBox + ABox without UNA) via the cyclic forest
solver `decideSROIQBool`. `none` indicates a role hierarchy outside the
numeric-rank / simplicity boundary. -/
def KnowledgeBase.decideRanked? (kb : KnowledgeBase) : Option Bool :=
  (Normalize.normalizeWithDefs kb.toOWL).bind fun (_, p) =>
    (findRank p.rules p.chains).bind fun rank =>
      if h : p.root = .top ∧ p.isSROIQ rank = true then
        some (decideSROIQBool h.2)
      else none

theorem kb_decide_ranked_admitted_iff (kb : KnowledgeBase) :
    kb.decideRanked?.isSome = true ↔ kb.RankAdmitted := by
  obtain ⟨p, hnorm, hp⟩ := normalizeWithDefs_kb_toOWL kb
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    simp only [KnowledgeBase.decideRanked?, hnorm, Option.bind_some, Option.bind_eq_some_iff] at hb
    obtain ⟨rank, _, hb⟩ := hb
    split at hb
    · rename_i hadmit
      have ⟨hsimple, hreg⟩ := (hp.isSROIQ_iff rank).mp hadmit.2
      exact ⟨p, rank, hnorm, hsimple, hreg⟩
    · contradiction
  · rintro ⟨p', rank, hnorm', hsimple, hreg⟩
    rw [hnorm] at hnorm'
    cases hnorm'
    obtain ⟨rank', hfound⟩ := Option.isSome_iff_exists.mp
      (Sabrina.RoleChains.findRank_complete (Sabrina.RoleChains.checkRegular_sound hreg))
    have hreg' : checkRegular rank' p.rules p.chains = true :=
      Sabrina.RoleChains.checkRegular_iff.mpr (Sabrina.RoleChains.findRank_sound hfound)
    have hsroiq' : p.isSROIQ rank' = true := (hp.isSROIQ_iff rank').mpr ⟨hsimple, hreg'⟩
    simp [KnowledgeBase.decideRanked?, hnorm, hfound, hp.root, hsroiq']

theorem kb_decide_ranked_iff {kb : KnowledgeBase} {b : Bool} (h : kb.decideRanked? = some b) :
    b = true ↔ kb.Sat := by
  simp only [KnowledgeBase.decideRanked?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := h
  split at hb
  · rename_i hadmit
    cases hb
    exact (decideSROIQBool_ontology_iff hadmit.2 hnorm hadmit.1).trans
      (kb_satisfiable_toOWL_iff datatypeMap kb)
  · contradiction

/-- Admission is the union of the ranked forest solver and the universal
fragment, whose finite grounding does not require a role rank. -/
def KnowledgeBase.Admitted (kb : KnowledgeBase) : Prop :=
  kb.RankAdmitted ∨ kb.isUniversal = true

/-- Keep existing ranked verdicts and use finite grounding for universal input
outside the ranked fragment. `none` indicates that neither path applies. -/
def KnowledgeBase.decide? (kb : KnowledgeBase) : Option Bool :=
  match kb.decideRanked? with
  | some b => some b
  | none => if h : kb.isUniversal = true then some (kb.decideUniversal h) else none

theorem kb_decide_extends_ranked {kb : KnowledgeBase} {b : Bool} (h : kb.decideRanked? = some b) :
    kb.decide? = some b := by
  simp [KnowledgeBase.decide?, h]

theorem kb_decide_admitted_iff (kb : KnowledgeBase) :
    kb.decide?.isSome = true ↔ kb.Admitted := by
  have hr := kb_decide_ranked_admitted_iff kb
  cases h : kb.decideRanked? with
  | some b =>
    have hadmit := hr.mp (by simp [h])
    simp [KnowledgeBase.decide?, h, KnowledgeBase.Admitted, hadmit]
  | none =>
    have hnot : ¬ kb.RankAdmitted := by
      intro hadmit
      simpa [h] using hr.mpr hadmit
    by_cases hu : kb.isUniversal = true <;> simp [KnowledgeBase.decide?, h, KnowledgeBase.Admitted, hnot, hu]

theorem kb_decide_iff {kb : KnowledgeBase} {b : Bool} (h : kb.decide? = some b) :
    b = true ↔ kb.Sat := by
  cases hr : kb.decideRanked? with
  | some a =>
    simp only [KnowledgeBase.decide?, hr, Option.some.injEq] at h
    subst b
    exact kb_decide_ranked_iff hr
  | none =>
    simp only [KnowledgeBase.decide?, hr] at h
    split at h
    · rename_i hu
      cases h
      exact KnowledgeBase.decideUniversal_iff hu
    · contradiction

theorem kb_decide_unsat_of_some {kb : KnowledgeBase} {b : Bool} (h : kb.decide? = some b) :
    b = false ↔ ¬ kb.Sat := by
  rw [← kb_decide_iff h]
  cases b <;> simp

theorem kb_decide_sat_iff {kb : KnowledgeBase} (h : kb.Admitted) :
    kb.decide? = some true ↔ kb.Sat := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((kb_decide_admitted_iff kb).mpr h)
  rw [← kb_decide_iff hb, hb, Option.some.injEq]

theorem kb_decide_unsat_iff {kb : KnowledgeBase} (h : kb.Admitted) :
    kb.decide? = some false ↔ ¬ kb.Sat := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((kb_decide_admitted_iff kb).mpr h)
  rw [← kb_decide_iff hb, hb, Option.some.injEq]
  cases b <;> simp

/-- The forest-based ABox knowledge-base adapter preserves every verdict of the
earlier TBox/RBox-only `TBoxRBox.decide?` adapter. -/
theorem kb_decide_extends_tboxRBox {o : TBoxRBox} {b : Bool} (h : o.decide? = some b) :
    o.toKB.decide? = some b := by
  have h1 : o.decide?.isSome = true := by simp [h]
  obtain ⟨defs, p, rank, hnorm, _, hsroiq⟩ := (decide_admitted_iff o).mp h1
  obtain ⟨p₀, hnorm₀, _⟩ := normalizeWithDefs_kb_toOWL o.toKB
  rw [TBoxRBox.toKB_toOWL] at hnorm₀
  rw [hnorm] at hnorm₀
  cases hnorm₀
  have hinput := Problem.sriqInput hsroiq
  have hadmit : o.toKB.RankAdmitted :=
    ⟨p, rank, by simpa [TBoxRBox.toKB_toOWL] using hnorm, hinput.simple, hinput.regular⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp ((kb_decide_ranked_admitted_iff o.toKB).mpr hadmit)
  have hiff₁ : b = true ↔ o.Sat := by
    have ha : o.Admitted := (decide_admitted_iff o).mp h1
    cases b with
    | true => exact ⟨fun _ => (decide_sat_iff ha).mp h, fun _ => rfl⟩
    | false => exact ⟨fun hc => Bool.noConfusion hc, fun hs => ((decide_unsat_iff ha).mp h hs).elim⟩
  have hiff₂ : b' = true ↔ o.Sat := (kb_decide_ranked_iff hb').trans o.toKB_sat_iff
  have heq : b' = b := by
    cases b' <;> cases b <;> simp_all
  simpa [heq] using kb_decide_extends_ranked hb'

#print axioms ABoxModel.fromOWL_toOWL
#print axioms kb_satisfiable_toOWL_iff
#print axioms normalizeWithDefs_kb_toOWL
#print axioms kb_decide_admitted_iff
#print axioms kb_decide_iff
#print axioms kb_decide_sat_iff
#print axioms kb_decide_unsat_iff
#print axioms kb_decide_extends_tboxRBox

end Sabrina.OWL2.SROIQD.TextbookSRIQ
