import Sabrina.OWL2.SROIQD.Termination.WeakRegularity
import Sabrina.OWL2.SROIQD.Termination.RegularObjectDecision
import Sabrina.OWL2.SROIQD.Termination.RealDecision
import Sabrina.OWL2.SROIQD.Termination.ExactQueryDecision

/-! Unified combined regular OWL 2 DL admission theorem.

Lifts the rank-independent object admission theorem (`RegularObjectDecision`) across
the full combined solver — covering cyclic GCIs, qualified cardinalities, nominals,
ABoxes, mixed object+data `HasKey`, all 33 OWL 2 DL datatypes and wider exact facets
(Dedekind-cut `owl:real`, `xsd:float`/`xsd:double`/`xsd:dateTime`/`xsd:dateTimeStamp`
order facets, string/URI/binary length facets, `xsd:pattern`, `rdf:langRange`, and
`DataOneOf`), `owl:topObjectProperty` (in class restrictions, unary rules,
characteristics, `HasKey`, assertions, top-headed chains, and chain bodies),
`owl:bottomObjectProperty`, `owl:topDataProperty`, and `owl:bottomDataProperty`.

The caller supplies no numeric rank and no fuel: any input satisfying the
rank-independent regular hierarchy criterion (`RegularOWL2DLHierarchy`, Stefanoni's
head-inverse `WeaklyRegular .head` on the ordinary residual hierarchy) — or the
strictly more general exact mixed-cycle graph criterion (`AcyclicOWL2DLHierarchy`,
`HasAcyclicDependencies`) — is guaranteed to be decided by both the Dedekind-cut
real solver (`decideRealProblem?` / `decideRealOntology?`) and the standard-map
solver (`decideWithWiderDataRanges?`), yielding total `Bool` decision procedures
with kernel-checked soundness and completeness, plus total four-way query entailment. -/

namespace Sabrina.OWL2.RoleHierarchy.Unified

open Sabrina.OWL2
open Sabrina.ALC (OrientedRole RoleTheory roleClosure converse)
open Sabrina.RoleChains (Chain Rank Ranked findRank checkRegular HasAcyclicDependencies)
open Sabrina.RoleChains.SimpleRoles (Reachable Composite Simple builtinRoles)
open Sabrina.OWL2.Datatypes (datatypeMap realDatatypeMap decodeLiteral)
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.BlockedForest
open Sabrina.OWL2.SROIQD.Termination.ExactQuery
open Sabrina.OWL2.RoleHierarchy.Stefanoni

/-! ### 1. Rank-independent OWL 2 DL hierarchy and input specifications -/

/-- Every class literal in `c` uses an ordinary (non-`owl:Thing`, non-`owl:Nothing`) IRI. -/
def _root_.Sabrina.OWL2.SROIQD.Concept.coreClasses : Concept → Bool
  | .top | .bottom | .nom _ _ | .self _ _
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _
  | .dataMin _ _ _ | .dataMax _ _ _ => true
  | .lit a _ => isCoreClassIRI a
  | .conj a b | .disj a b => a.coreClasses && b.coreClasses
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.coreClasses

/-- Ordinary (non-`owl:topObjectProperty`, non-`owl:bottomObjectProperty`) role rules. -/
def ordinaryRules (rules : RoleTheory) : RoleTheory :=
  rules.filter fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1

/-- Ordinary (non-`owl:topObjectProperty`, non-`owl:bottomObjectProperty`) property chains. -/
def ordinaryChains (chains : List Chain) : List Chain :=
  chains.filter fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI

/-- Exact rank-independent graph criterion for full OWL 2 DL role hierarchies:
every chain has length at least 2, and the ordinary residual role hierarchy has
no cycle containing a strict chain dependency. Built-in `owl:topObjectProperty`
and `owl:bottomObjectProperty` rules and chains are handled by verified lowering. -/
def AcyclicOWL2DLHierarchy (rules : RoleTheory) (chains : List Chain) : Prop :=
  (∀ c ∈ chains, 2 ≤ c.body.length) ∧
  HasAcyclicDependencies (ordinaryRules rules) (ordinaryChains chains)

/-- Stefanoni head-inverse weak-regularity criterion for full OWL 2 DL role hierarchies:
every chain has length at least 2, and the ordinary residual role hierarchy satisfies
`WeaklyRegular .head`. -/
def RegularOWL2DLHierarchy (rules : RoleTheory) (chains : List Chain) : Prop :=
  (∀ c ∈ chains, 2 ≤ c.body.length) ∧
  WeaklyRegular .head (compiledBox (ordinaryRules rules) (ordinaryChains chains))

private theorem ordinary_compiledBox (rules : RoleTheory) (chains : List Chain) :
    Ordinary (compiledBox (ordinaryRules rules) (ordinaryChains chains)) := by
  intro a ha
  rcases List.mem_append.mp ha with hr | hc
  · obtain ⟨⟨r, s⟩, hrs, rfl⟩ := List.mem_map.mp hr
    have hf := (List.mem_filter.mp hrs).2
    simp only [Bool.and_eq_true, isCoreObjPropIRI, bne_iff_ne] at hf
    refine ⟨hf.2, ?_⟩
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact hf.1
  · obtain ⟨c, hcM, rfl⟩ := List.mem_map.mp hc
    have hf := (List.mem_filter.mp hcM).2
    simp only [Bool.and_eq_true, List.all_eq_true, isCoreObjPropIRI, bne_iff_ne] at hf
    refine ⟨hf.1, ?_⟩
    intro r hr
    exact hf.2 r.1 (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem RegularOWL2DLHierarchy.toAcyclic {rules : RoleTheory} {chains : List Chain}
    (h : RegularOWL2DLHierarchy rules chains) :
    AcyclicOWL2DLHierarchy rules chains :=
  ⟨h.1, weaklyRegular_hasAcyclicDependencies
    (ordinary_compiledBox rules chains)
    (fun c hc => h.1 c (List.mem_filter.mp hc).1)
    h.2⟩

/-- Rank-independent unified input specification for the combined OWL 2 DL solver
under the exact acyclic-dependency graph criterion. -/
structure AcyclicOWL2DLInput (p : Problem) : Prop where
  coreClasses : ∀ c ∈ p.allConcepts, c.coreClasses = true
  literals : ∀ l ∈ p.allDataLiterals, (decodeLiteral l).isSome = true
  dataRanges : ∀ d ∈ p.allDataRanges, isWiderDataRange d = true
  simple : p.checkSimpleWithTop = true
  acyclic : AcyclicOWL2DLHierarchy p.rules p.chains

/-- Rank-independent unified input specification for the combined OWL 2 DL solver
under Stefanoni's head-inverse weak-regularity criterion, directly generalizing
`RegularObjectInput` across datatypes, facets, built-in properties, and ABoxes. -/
structure RegularOWL2DLInput (p : Problem) : Prop where
  coreClasses : ∀ c ∈ p.allConcepts, c.coreClasses = true
  literals : ∀ l ∈ p.allDataLiterals, (decodeLiteral l).isSome = true
  dataRanges : ∀ d ∈ p.allDataRanges, isWiderDataRange d = true
  simple : p.checkSimpleWithTop = true
  regular : RegularOWL2DLHierarchy p.rules p.chains

theorem RegularOWL2DLInput.toAcyclic {p : Problem} (h : RegularOWL2DLInput p) :
    AcyclicOWL2DLInput p :=
  ⟨h.coreClasses, h.literals, h.dataRanges, h.simple, h.regular.toAcyclic⟩

/-- Executable decision procedure for `AcyclicOWL2DLInput p`. -/
def checkAcyclicOWL2DLInput (p : Problem) : Bool :=
  p.allConcepts.all Concept.coreClasses &&
  p.allDataLiterals.all (fun l => (decodeLiteral l).isSome) &&
  p.allDataRanges.all isWiderDataRange &&
  p.checkSimpleWithTop &&
  p.chains.all (fun c => decide (2 ≤ c.body.length)) &&
  (findRank (ordinaryRules p.rules) (ordinaryChains p.chains)).isSome

theorem checkAcyclicOWL2DLInput_iff (p : Problem) :
    checkAcyclicOWL2DLInput p = true ↔ AcyclicOWL2DLInput p := by
  unfold checkAcyclicOWL2DLInput
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Sabrina.RoleChains.findRank_iff_acyclicDependencies]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, ⟨h5, h6⟩⟩
  · intro h
    exact ⟨⟨⟨⟨⟨h.coreClasses, h.literals⟩, h.dataRanges⟩, h.simple⟩, h.acyclic.1⟩, h.acyclic.2⟩

theorem checkSimple_implies_checkSimpleWithTop {p : Problem} (h : p.checkSimple = true) :
    p.checkSimpleWithTop = true := by
  have hsim := Problem.checkSimple_iff.mp h
  unfold Problem.checkSimpleWithTop
  simp only [h, Bool.true_and, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  intro r hr
  have hsr := hsim r hr
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro heq
    exact hsr r (.refl _) (Or.inl (by rw [heq]; exact List.mem_cons_self ..))
  · apply Bool.eq_false_iff.mpr
    intro hmem
    exact hsr (topObjectProperty, false)
      (Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp (Or.inr (List.contains_iff_mem.mp hmem)))
      (Or.inl (List.mem_cons_self ..))
  · apply Bool.eq_false_iff.mpr
    intro hmem
    exact hsr (topObjectProperty, true)
      (Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp (Or.inr (List.contains_iff_mem.mp hmem)))
      (Or.inl (List.mem_cons_self ..))

private theorem concept_isSROIQ_facts {c : Concept} (h : c.isSROIQ = true) :
    c.coreClasses = true ∧ c.dataLiteralsOf = [] ∧ c.dataRangesOf = [] := by
  induction c with
  | top | bottom | nom _ _ | self _ _ =>
    simp [Concept.coreClasses, Concept.dataLiteralsOf, Concept.dataRangesOf]
  | lit a _ =>
    simp [Concept.isSROIQ] at h
    simp [Concept.coreClasses, Concept.dataLiteralsOf, Concept.dataRangesOf, h]
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQ, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := iha h.1
    obtain ⟨h4, h5, h6⟩ := ihb h.2
    simp [Concept.coreClasses, Concept.dataLiteralsOf, Concept.dataRangesOf, h1, h2, h3, h4, h5, h6]
  | some _ _ ih | all _ _ ih | min _ _ _ ih | max _ _ _ ih =>
    simp only [Concept.isSROIQ, Bool.and_eq_true] at h
    exact ih h.2
  | dataSome _ _ | dataAll _ _ | dataValue _ _ _ | dataMin _ _ _ | dataMax _ _ _ =>
    simp [Concept.isSROIQ] at h

/-- Strict generalization of `RegularObjectInput`: every admitted regular object
problem is automatically a `RegularOWL2DLInput`. -/
theorem RegularObjectInput.toRegularOWL2DLInput {p : Problem} (h : RegularObjectInput p) :
    RegularOWL2DLInput p := by
  have hi := ({p with chains := []} : Problem).sroiqInput h.objects
  have hallC : ∀ c ∈ p.allConcepts, c.isSROIQ = true := by
    intro c hc
    simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | ((ht | hk) | hca)
    · exact hi.root
    · obtain ⟨q, hq, rfl | rfl⟩ := ht
      · exact (hi.tbox q hq).1
      · exact (hi.tbox q hq).2
    · obtain ⟨k, hk, rfl⟩ := hk
      exact (hi.keys k hk).1
    · obtain ⟨ac, hac, rfl⟩ := hca
      exact hi.classAssertions ac hac
  have hordR : ordinaryRules p.rules = p.rules := by
    apply List.filter_eq_self.mpr
    intro rs hrs
    have hm : (⟨[rs.1], rs.2⟩ : PropertyChain) ∈ compiledBox p.rules p.chains :=
      List.mem_append_left _ (List.mem_map.mpr ⟨rs, hrs, rfl⟩)
    obtain ⟨h2, h1⟩ := h.ordinary _ hm
    have h1' := h1 rs.1 (List.mem_cons_self ..)
    simp [isCoreObjPropIRI, h1'.1, h1'.2, h2.1, h2.2]
  have hordC : ordinaryChains p.chains = p.chains := by
    apply List.filter_eq_self.mpr
    intro c hc
    have hm : (⟨c.body, (c.head, false)⟩ : PropertyChain) ∈ compiledBox p.rules p.chains :=
      List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    obtain ⟨hh, hb⟩ := h.ordinary _ hm
    simp only [Bool.and_eq_true, List.all_eq_true, isCoreObjPropIRI, bne_iff_ne]
    refine ⟨hh, fun n hn => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
    exact hb r hr
  refine ⟨fun c hc => (concept_isSROIQ_facts (hallC c hc)).1, ?_, ?_,
    checkSimple_implies_checkSimpleWithTop h.simple, h.lengths, ?_⟩
  · intro l hl
    have hda : p.dataAssertions = [] := hi.dataAssertions
    have hnda : p.negDataAssertions = [] := hi.negDataAssertions
    simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map, hda, hnda, List.not_mem_nil, false_and, exists_false, or_false] at hl
    obtain ⟨c, hc, hlC⟩ := hl
    rw [(concept_isSROIQ_facts (hallC c hc)).2.1] at hlC
    cases hlC
  · intro d hd
    have hdr : p.dataRanges = [] := hi.dataRanges
    simp only [Problem.allDataRanges, List.mem_append, List.mem_flatMap, List.mem_map,
      hdr, List.not_mem_nil, false_and, exists_false, or_false] at hd
    obtain ⟨c, hc, hdC⟩ := hd
    rw [(concept_isSROIQ_facts (hallC c hc)).2.2] at hdC
    cases hdC
  · rw [hordR, hordC]
    exact h.regular

/-! ### 2. Structural preservation through `lowerBottom` -/

def _root_.Sabrina.OWL2.SROIQD.Concept.noBottomObj : Concept → Bool
  | .top | .bottom | .lit _ _ | .nom _ _
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _
  | .dataMin _ _ _ | .dataMax _ _ _ => true
  | .self r _ => r.1 != bottomObjectProperty
  | .conj a b | .disj a b => a.noBottomObj && b.noBottomObj
  | .some r c | .all r c | .min _ r c | .max _ r c =>
    (r.1 != bottomObjectProperty) && c.noBottomObj

private structure NoBottomObj (p : Problem) : Prop where
  concepts : ∀ c ∈ p.allConcepts, c.noBottomObj = true
  rules : ∀ rs ∈ p.rules, rs.1.1 ≠ bottomObjectProperty ∧ rs.2.1 ≠ bottomObjectProperty
  chains : ∀ c ∈ p.chains, c.head ≠ bottomObjectProperty ∧ ∀ r ∈ c.body, r.1 ≠ bottomObjectProperty
  reflexive : ∀ r ∈ p.chars.reflexive, r ≠ bottomObjectProperty
  irreflexive : ∀ r ∈ p.chars.irreflexive, r ≠ bottomObjectProperty
  asymmetric : ∀ r ∈ p.chars.asymmetric, r ≠ bottomObjectProperty
  disjoint : ∀ rs ∈ p.chars.disjoint, rs.1.1 ≠ bottomObjectProperty ∧ rs.2.1 ≠ bottomObjectProperty
  keys : ∀ k ∈ p.keys, ∀ r ∈ k.objProps, r.1 ≠ bottomObjectProperty
  objAssertions : ∀ rab ∈ p.objAssertions, rab.1 ≠ bottomObjectProperty
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, rab.1 ≠ bottomObjectProperty

private theorem concept_lowerBottom_props (c : Concept) :
    (c.coreClasses = true → c.lowerBottom.coreClasses = true) ∧
    c.lowerBottom.noBottomObj = true ∧
    (∀ d ∈ c.lowerBottom.dataRangesOf, d ∈ c.dataRangesOf) ∧
    (∀ l ∈ c.lowerBottom.dataLiteralsOf, l ∈ c.dataLiteralsOf) ∧
    (∀ dp ∈ c.lowerBottom.dataPropsOf, dp ∈ c.dataPropsOf ∧ dp ≠ bottomDataProperty) ∧
    (∀ r ∈ c.lowerBottom.countedRoles, r ∈ c.countedRoles) := by
  induction c with
  | top | bottom | nom _ _ =>
    simp [Concept.lowerBottom, Concept.coreClasses, Concept.noBottomObj,
      Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | lit a b =>
    simp [Concept.lowerBottom, Concept.coreClasses, Concept.noBottomObj,
      Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | self r b =>
    unfold Concept.lowerBottom
    by_cases hr : r.1 = bottomObjectProperty
    · cases b <;> simp [hr, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp [hr, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | conj a b iha ihb | disj a b iha ihb =>
    refine ⟨fun hc => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Concept.coreClasses, Bool.and_eq_true] at hc
      simp [Concept.lowerBottom, Concept.coreClasses, iha.1 hc.1, ihb.1 hc.2]
    · simp [Concept.lowerBottom, Concept.noBottomObj, iha.2.1, ihb.2.1]
    · intro d hd; simp only [Concept.lowerBottom, Concept.dataRangesOf, List.mem_append] at hd ⊢
      exact hd.elim (Or.inl ∘ iha.2.2.1 d) (Or.inr ∘ ihb.2.2.1 d)
    · intro l hl; simp only [Concept.lowerBottom, Concept.dataLiteralsOf, List.mem_append] at hl ⊢
      exact hl.elim (Or.inl ∘ iha.2.2.2.1 l) (Or.inr ∘ ihb.2.2.2.1 l)
    · intro dp hdp; simp only [Concept.lowerBottom, Concept.dataPropsOf, List.mem_append] at hdp ⊢
      exact hdp.elim (fun h => ⟨Or.inl (iha.2.2.2.2.1 dp h).1, (iha.2.2.2.2.1 dp h).2⟩)
                     (fun h => ⟨Or.inr (ihb.2.2.2.2.1 dp h).1, (ihb.2.2.2.2.1 dp h).2⟩)
    · intro r hr; simp only [Concept.lowerBottom, Concept.countedRoles, List.mem_append] at hr ⊢
      exact hr.elim (Or.inl ∘ iha.2.2.2.2.2 r) (Or.inr ∘ ihb.2.2.2.2.2 r)
  | some r c ih | all r c ih =>
    unfold Concept.lowerBottom
    by_cases hr : r.1 = bottomObjectProperty
    · simp [hr, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp only [hr, ↓reduceIte]
      refine ⟨fun hc => ih.1 hc, by simp [hr, Concept.noBottomObj, ih.2.1],
        ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
  | min n r c ih =>
    unfold Concept.lowerBottom
    by_cases hr : r.1 = bottomObjectProperty
    · by_cases hn : n = 0 <;> simp [hr, hn, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp only [hr, ↓reduceIte]
      refine ⟨fun hc => ih.1 hc, by simp [hr, Concept.noBottomObj, ih.2.1],
        ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, fun s hs => ?_⟩
      simp only [Concept.countedRoles, List.mem_cons] at hs ⊢
      exact hs.elim Or.inl (Or.inr ∘ ih.2.2.2.2.2 s)
  | max n r c ih =>
    unfold Concept.lowerBottom
    by_cases hr : r.1 = bottomObjectProperty
    · simp [hr, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp only [hr, ↓reduceIte]
      refine ⟨fun hc => ih.1 hc, by simp [hr, Concept.noBottomObj, ih.2.1],
        ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, fun s hs => ?_⟩
      simp only [Concept.countedRoles, List.mem_cons] at hs ⊢
      exact hs.elim Or.inl (Or.inr ∘ ih.2.2.2.2.2 s)
  | dataSome dp d | dataAll dp d =>
    unfold Concept.lowerBottom
    by_cases hdp : dp = bottomDataProperty
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataValue dp l b =>
    unfold Concept.lowerBottom
    by_cases hdp : dp = bottomDataProperty
    · cases b <;> simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataMin n dp d =>
    unfold Concept.lowerBottom
    by_cases hdp : dp = bottomDataProperty
    · by_cases hn : n = 0 <;> simp [hdp, hn, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataMax n dp d =>
    unfold Concept.lowerBottom
    by_cases hdp : dp = bottomDataProperty
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
    · simp [hdp, Concept.coreClasses, Concept.noBottomObj,
        Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]

private theorem foldr_some_props (rs : List OrientedRole)
    (hnb : ∀ r ∈ rs, r.1 ≠ bottomObjectProperty) :
    (rs.foldr Concept.some .top).coreClasses = true ∧
    (rs.foldr Concept.some .top).noBottomObj = true ∧
    (rs.foldr Concept.some .top).dataRangesOf = [] ∧
    (rs.foldr Concept.some .top).dataLiteralsOf = [] ∧
    (rs.foldr Concept.some .top).dataPropsOf = [] ∧
    (rs.foldr Concept.some .top).countedRoles = [] := by
  induction rs with
  | nil => simp [Concept.coreClasses, Concept.noBottomObj, Concept.dataRangesOf,
      Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | cons r rest ih =>
    have ihr := ih fun s hs => hnb s (List.mem_cons_of_mem _ hs)
    have hnr := hnb r (List.mem_cons_self ..)
    simp [List.foldr_cons, Concept.coreClasses, Concept.noBottomObj, Concept.dataRangesOf,
      Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles, hnr, ihr]

private theorem checkSimpleWithTop_mono {p q : Problem}
    (hsim : p.checkSimpleWithTop = true)
    (hrules : ∀ rs ∈ q.rules, rs ∈ p.rules)
    (hchains : ∀ c ∈ q.chains, 2 ≤ c.body.length → ∃ c0 ∈ p.chains, 2 ≤ c0.body.length ∧ c0.head = c.head)
    (hsimple : ∀ r ∈ q.simpleRoles, r ∈ p.simpleRoles) :
    q.checkSimpleWithTop = true := by
  have hpSim : p.checkSimple = true := (Bool.and_eq_true_iff.mp hsim).1
  have hreachMono : ∀ {a b : OrientedRole}, Reachable q.rules a b → Reachable p.rules a b := by
    intro a b hr
    induction hr with
    | refl => exact .refl _
    | step hs =>
      apply Reachable.step
      rcases List.mem_append.mp hs with h1 | h2
      · exact List.mem_append_left _ (hrules _ h1)
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp h2
        exact List.mem_append_right _ (List.mem_map.mpr ⟨e, hrules _ he, heq⟩)
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  apply checkSimple_implies_checkSimpleWithTop
  rw [Problem.checkSimple_iff] at hpSim ⊢
  intro r hr s hs hc
  apply hpSim r (hsimple r hr) s (hreachMono hs)
  rcases hc with hb | ⟨c, hcm, hlen, hhd⟩
  · exact Or.inl hb
  · obtain ⟨c0, hc0, hl0, hh0⟩ := hchains c hcm hlen
    exact Or.inr ⟨c0, hc0, hl0, hh0.trans hhd⟩

private theorem lowerBottom_rules_subset (p : Problem) :
    ∀ rs ∈ p.lowerBottom.rules,
      rs ∈ p.rules ∧ rs.1.1 ≠ bottomObjectProperty ∧ rs.2.1 ≠ bottomObjectProperty := by
  intro rs hrs
  have hf := List.mem_filter.mp hrs
  refine ⟨hf.1, ?_, ?_⟩
  · intro he
    have : isBottomObj rs.1.1 = true := beq_iff_eq.mpr he
    simp [bottomRule, this] at hf
  · intro he
    have : isBottomObj rs.2.1 = true := beq_iff_eq.mpr he
    by_cases h1 : isBottomObj rs.1.1 = true <;> simp [bottomRule, h1, this] at hf

private theorem lowerBottom_chains_subset (p : Problem) :
    ∀ c ∈ p.lowerBottom.chains,
      c ∈ p.chains ∧ c.head ≠ bottomObjectProperty ∧ ∀ r ∈ c.body, r.1 ≠ bottomObjectProperty := by
  intro c hc
  have hf := List.mem_filter.mp hc
  have hnbBody : ∀ r ∈ c.body, r.1 ≠ bottomObjectProperty := by
    intro r hr he
    have hany : c.body.any (fun x => isBottomObj x.1) = true :=
      List.any_eq_true.mpr ⟨r, hr, beq_iff_eq.mpr he⟩
    simp [bottomChain, hany] at hf
  have hnbHead : c.head ≠ bottomObjectProperty := by
    intro he
    have hh : isBottomObj c.head = true := beq_iff_eq.mpr he
    by_cases hb : c.body.any (fun x => isBottomObj x.1) = true <;> simp [bottomChain, hb, hh] at hf
  exact ⟨hf.1, hnbHead, hnbBody⟩

private theorem lowerBottom_allConcepts_cases (p : Problem) {c : Concept}
    (hc : c ∈ p.lowerBottom.allConcepts) :
    c = .top ∨ c = .bottom ∨
    (∃ c0 ∈ p.allConcepts, c = c0.lowerBottom) ∨
    (∃ rs : OrientedRole, rs.1 ≠ bottomObjectProperty ∧ c = .some rs .top) ∨
    (∃ body : List OrientedRole, (∀ r ∈ body, r.1 ≠ bottomObjectProperty) ∧ c = body.foldr Concept.some .top) ∨
    (∃ dp : IRI, dp ≠ bottomDataProperty ∧ c = .dataSome dp (.datatype literalDatatype)) := by
  simp only [Problem.lowerBottom, Problem.allConcepts, List.mem_cons, List.mem_append,
    List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ((ht | hk) | hca)
  · exact Or.inr (Or.inr (Or.inl ⟨p.root, List.mem_cons_self .., rfl⟩))
  · obtain ⟨q, hq, hqm⟩ := ht
    rcases hq with hmap | hextra
    · obtain ⟨q0, hq0, rfl⟩ := hmap
      rcases hqm with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨q0.sub, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inl rfl⟩)), rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨q0.sup, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inr rfl⟩)), rfl⟩))
    · obtain ⟨ex, hex, rfl⟩ := hextra
      rcases hqm with rfl | rfl
      · rcases hex with ((((h1 | h2) | h3) | h4) | h5) | h6
        · obtain ⟨rs, _, he⟩ := List.mem_filterMap.mp h1
          by_cases hb1 : isBottomObj rs.1.1 = true
          · simp [bottomRule, hb1] at he
          · by_cases hb2 : isBottomObj rs.2.1 = true
            · simp only [bottomRule, hb1, hb2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at he
              subst he
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rs.1, fun h => hb1 (beq_iff_eq.mpr h), rfl⟩)))
            · simp [bottomRule, hb1, hb2] at he
        · obtain ⟨ch, _, he⟩ := List.mem_filterMap.mp h2
          by_cases hbb : ch.body.any (fun r => isBottomObj r.1) = true
          · simp [bottomChain, hbb] at he
          · by_cases hbh : isBottomObj ch.head = true
            · simp only [bottomChain, hbb, hbh, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at he
              subst he
              have hnb : ∀ r ∈ ch.body, r.1 ≠ bottomObjectProperty := fun r hr hEq =>
                hbb (List.any_eq_true.mpr ⟨r, hr, beq_iff_eq.mpr hEq⟩)
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ch.body, hnb, rfl⟩))))
            · simp [bottomChain, hbb, hbh] at he
        · obtain ⟨r, _, he⟩ := List.mem_filterMap.mp h3
          by_cases hbr : isBottomObj r = true
          · simp only [forbidWhen, hbr, ↓reduceIte, Option.some.injEq] at he; subst he; exact Or.inl rfl
          · simp [forbidWhen, hbr] at he
        · obtain ⟨rs, _, he⟩ := List.mem_filterMap.mp h4
          by_cases hb1 : isBottomData rs.1 = true
          · simp [bottomSubData, hb1] at he
          · by_cases hb2 : isBottomData rs.2 = true
            · simp only [bottomSubData, hb1, hb2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at he
              subst he
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rs.1, fun h => hb1 (beq_iff_eq.mpr h), rfl⟩))))
            · simp [bottomSubData, hb1, hb2] at he
        · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp h5
          by_cases hbe : isBottomObj e.1 = true
          · simp only [forbidWhen, hbe, ↓reduceIte, Option.some.injEq] at he; subst he; exact Or.inl rfl
          · simp [forbidWhen, hbe] at he
        · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp h6
          by_cases hbe : isBottomData e.1 = true
          · simp only [forbidWhen, hbe, ↓reduceIte, Option.some.injEq] at he; subst he; exact Or.inl rfl
          · simp [forbidWhen, hbe] at he
      · exact Or.inr (Or.inl rfl)
  · obtain ⟨k, hk, rfl⟩ := hk
    obtain ⟨k0, hk0, rfl⟩ := hk
    exact Or.inr (Or.inr (Or.inl ⟨k0.cls, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, (List.mem_filter.mp hk0).1, rfl⟩)), rfl⟩))
  · obtain ⟨ac, hac, rfl⟩ := hca
    obtain ⟨ac0, hac0, rfl⟩ := hac
    exact Or.inr (Or.inr (Or.inl ⟨ac0.2, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩), rfl⟩))

private theorem lowerBottom_simpleRoles_subset (p : Problem) :
    ∀ r ∈ p.lowerBottom.simpleRoles, r ∈ p.simpleRoles := by
  intro r hr
  simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_map] at hr ⊢
  rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ((concept_lowerBottom_props p.root).2.2.2.2.2 r h1)))))
  · obtain ⟨q, hq, hrq⟩ := h2
    rcases List.mem_append.mp hq with hmap | hextra
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hmap
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hq0,
        hrq.elim (Or.inl ∘ (concept_lowerBottom_props q0.sub).2.2.2.2.2 r)
                 (Or.inr ∘ (concept_lowerBottom_props q0.sup).2.2.2.2.2 r)⟩))))
    · obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hextra
      rcases hrq with hrl | hrr
      · simp only [List.mem_append] at hex
        rcases hex with ((((ha | hb) | hc) | hd) | he) | hf
        · obtain ⟨rs, _, hres⟩ := List.mem_filterMap.mp ha
          by_cases h1 : isBottomObj rs.1.1 = true
          · simp [bottomRule, h1] at hres
          · by_cases h2 : isBottomObj rs.2.1 = true
            · simp only [bottomRule, h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hres
              subst hres; simp [Concept.countedRoles] at hrl
            · simp [bottomRule, h1, h2] at hres
        · obtain ⟨ch, _, hres⟩ := List.mem_filterMap.mp hb
          by_cases h1 : ch.body.any (fun x => isBottomObj x.1) = true
          · simp [bottomChain, h1] at hres
          · by_cases h2 : isBottomObj ch.head = true
            · simp only [bottomChain, h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hres
              subst hres
              have hnb : ∀ x ∈ ch.body, x.1 ≠ bottomObjectProperty := fun x hx heq =>
                h1 (List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr heq⟩)
              rw [(foldr_some_props ch.body hnb).2.2.2.2.2] at hrl
              cases hrl
            · simp [bottomChain, h1, h2] at hres
        · obtain ⟨x, _, hres⟩ := List.mem_filterMap.mp hc
          by_cases h1 : isBottomObj x = true <;> simp [forbidWhen, h1] at hres
          subst hres; simp [Concept.countedRoles] at hrl
        · obtain ⟨rs, _, hres⟩ := List.mem_filterMap.mp hd
          by_cases h1 : isBottomData rs.1 = true
          · simp [bottomSubData, h1] at hres
          · by_cases h2 : isBottomData rs.2 = true
            · simp only [bottomSubData, h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hres
              subst hres; simp [Concept.countedRoles] at hrl
            · simp [bottomSubData, h1, h2] at hres
        · obtain ⟨e, _, hres⟩ := List.mem_filterMap.mp he
          by_cases h1 : isBottomObj e.1 = true <;> simp [forbidWhen, h1] at hres
          subst hres; simp [Concept.countedRoles] at hrl
        · obtain ⟨e, _, hres⟩ := List.mem_filterMap.mp hf
          by_cases h1 : isBottomData e.1 = true <;> simp [forbidWhen, h1] at hres
          subst hres; simp [Concept.countedRoles] at hrl
      · simp [Concept.countedRoles] at hrr
  · obtain ⟨k, hk, hrk⟩ := h3
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, (List.mem_filter.mp hk0).1,
      (concept_lowerBottom_props k0.cls).2.2.2.2.2 r hrk⟩)))
  · obtain ⟨ac, hac, hrac⟩ := h4
    obtain ⟨ac0, hac0, rfl⟩ := List.mem_map.mp hac
    exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0, (concept_lowerBottom_props ac0.2).2.2.2.2.2 r hrac⟩))
  · obtain ⟨n, hn, rfl⟩ := h5
    refine Or.inl (Or.inr ⟨n, ?_, rfl⟩)
    rcases hn with h1 | h2
    · exact Or.inl (List.mem_filter.mp h1).1
    · exact Or.inr (List.mem_filter.mp h2).1
  · obtain ⟨rs, hrs, hrm⟩ := h6
    exact Or.inr ⟨rs, (List.mem_filter.mp hrs).1, hrm⟩

private theorem lowerBottom_noBottomObj (p : Problem) : NoBottomObj p.lowerBottom := by
  refine ⟨?_, fun rs hrs => (lowerBottom_rules_subset p rs hrs).2,
    fun c hc => (lowerBottom_chains_subset p c hc).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, _, rfl⟩ | ⟨rs, hnb, rfl⟩ | ⟨body, hnb, rfl⟩ | ⟨dp, _, rfl⟩
    · rfl
    · rfl
    · exact (concept_lowerBottom_props c0).2.1
    · simp [Concept.noBottomObj, hnb]
    · exact (foldr_some_props body hnb).2.1
    · rfl
  · intro r hr he
    have hf := List.mem_filter.mp hr
    have hbo : isBottomObj r = true := beq_iff_eq.mpr he
    simp [forbidWhen, hbo] at hf
  · intro r hr he
    have hf := List.mem_filter.mp hr
    have hbo : isBottomObj r = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbo] at hf
  · intro r hr he
    have hf := List.mem_filter.mp hr
    have hbo : isBottomObj r = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbo] at hf
  · intro rs hrs
    have hf := List.mem_filter.mp hrs
    constructor <;> intro he
    · have hbo : isBottomObj rs.1.1 = true := beq_iff_eq.mpr he
      simp [reduceUnless, hbo] at hf
    · have hbo : isBottomObj rs.2.1 = true := beq_iff_eq.mpr he
      by_cases h1 : isBottomObj rs.1.1 = true <;> simp [reduceUnless, h1, hbo] at hf
  · intro k hk r hr he
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    have hf := List.mem_filter.mp hk0
    have hany : k0.objProps.any (fun x => isBottomObj x.1) = true :=
      List.any_eq_true.mpr ⟨r, hr, beq_iff_eq.mpr he⟩
    simp [bottomKey, reduceUnless, hany] at hf
  · intro rab hrab he
    have hf := List.mem_filter.mp hrab
    have hbo : isBottomObj rab.1 = true := beq_iff_eq.mpr he
    simp [forbidWhen, hbo] at hf
  · intro rab hrab he
    have hf := List.mem_filter.mp hrab
    have hbo : isBottomObj rab.1 = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbo] at hf

private theorem lowerBottom_noBottomData (p : Problem) :
    ∀ dp ∈ p.lowerBottom.allDataProps, dp ≠ bottomDataProperty := by
  intro dp hdp
  simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hdp
  rcases hdp with (((((((hcM | hdrM) | hsubM) | hdisjM) | hfuncM) | hkeyM) | hdaM) | hndaM)
  · obtain ⟨c, hc, hdpC⟩ := hcM
    rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, _, rfl⟩ | ⟨rs, _, rfl⟩ | ⟨body, hnb, rfl⟩ | ⟨dp0, hnb, rfl⟩
    · simp [Concept.dataPropsOf] at hdpC
    · simp [Concept.dataPropsOf] at hdpC
    · exact ((concept_lowerBottom_props c0).2.2.2.2.1 dp hdpC).2
    · simp [Concept.dataPropsOf] at hdpC
    · rw [(foldr_some_props body hnb).2.2.2.2.1] at hdpC; cases hdpC
    · rw [List.mem_singleton.mp hdpC]; exact hnb
  · obtain ⟨rd, hrd, rfl⟩ := hdrM
    intro he; have hf := List.mem_filter.mp hrd
    have hbd : isBottomData rd.1 = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbd] at hf
  · obtain ⟨rs, hrs, rfl | rfl⟩ := hsubM
    · intro he; have hf := List.mem_filter.mp hrs
      have hbd : isBottomData rs.1 = true := beq_iff_eq.mpr he
      simp [bottomSubData, hbd] at hf
    · intro he; have hf := List.mem_filter.mp hrs
      have hbd : isBottomData rs.2 = true := beq_iff_eq.mpr he
      by_cases hb1 : isBottomData rs.1 = true <;> simp [bottomSubData, hb1, hbd] at hf
  · obtain ⟨rs, hrs, rfl | rfl⟩ := hdisjM
    · intro he; have hf := List.mem_filter.mp hrs
      have hbd : isBottomData rs.1 = true := beq_iff_eq.mpr he
      simp [reduceUnless, hbd] at hf
    · intro he; have hf := List.mem_filter.mp hrs
      have hbd : isBottomData rs.2 = true := beq_iff_eq.mpr he
      by_cases hb1 : isBottomData rs.1 = true <;> simp [reduceUnless, hb1, hbd] at hf
  · intro he; have hf := List.mem_filter.mp hfuncM
    have hbd : isBottomData dp = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbd] at hf
  · obtain ⟨k, hk, hdpK⟩ := hkeyM
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    intro he; have hf := List.mem_filter.mp hk0
    have hany : k0.dataProps.any isBottomData = true :=
      List.any_eq_true.mpr ⟨dp, hdpK, beq_iff_eq.mpr he⟩
    simp [bottomKey, reduceUnless, hany] at hf
  · obtain ⟨dal, hdal, rfl⟩ := hdaM
    intro he; have hf := List.mem_filter.mp hdal
    have hbd : isBottomData dal.1 = true := beq_iff_eq.mpr he
    simp [forbidWhen, hbd] at hf
  · obtain ⟨dal, hdal, rfl⟩ := hndaM
    intro he; have hf := List.mem_filter.mp hdal
    have hbd : isBottomData dal.1 = true := beq_iff_eq.mpr he
    simp [reduceUnless, hbd] at hf

private theorem lowerBottom_ordinary_eq (p : Problem) :
    ordinaryRules p.lowerBottom.rules = ordinaryRules p.rules ∧
    ordinaryChains p.lowerBottom.chains = ordinaryChains p.chains := by
  constructor
  · simp only [ordinaryRules, Problem.lowerBottom, Sabrina.OWL2.SROIQD.retained]
    rw [List.filter_filter]
    apply List.filter_congr
    intro rs _
    by_cases h1 : rs.1.1 = bottomObjectProperty <;> by_cases h2 : rs.2.1 = bottomObjectProperty <;>
      simp [isCoreObjPropIRI, bottomRule, isBottomObj, h1, h2]
  · simp only [ordinaryChains, Problem.lowerBottom, Sabrina.OWL2.SROIQD.retained]
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases hbod : c.body.any (fun r => isBottomObj r.1) = true
    · obtain ⟨r, hr, hrb⟩ := List.any_eq_true.mp hbod
      have hrb' : r.1 = bottomObjectProperty := beq_iff_eq.mp hrb
      have hnotAll : c.bodyNames.all isCoreObjPropIRI = false := by
        apply Bool.eq_false_iff.mpr
        intro hall
        have := List.all_eq_true.mp hall r.1 (List.mem_map.mpr ⟨r, hr, rfl⟩)
        simp [isCoreObjPropIRI, hrb'] at this
      simp [bottomChain, hbod, hnotAll]
    · by_cases hhd : c.head = bottomObjectProperty
      · simp [bottomChain, isBottomObj, hhd, isCoreObjPropIRI]
      · have hbotC : bottomChain c = .keep := by
          unfold bottomChain
          have hbf : (c.body.any fun r => isBottomObj r.1) = false := Bool.eq_false_iff.mpr hbod
          rw [hbf]
          simp [isBottomObj, hhd]
        simp [hbotC]

private theorem lowerBottom_acyclic {p : Problem} (h : AcyclicOWL2DLInput p) :
    AcyclicOWL2DLInput p.lowerBottom := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, hc0, rfl⟩ | ⟨_, _, rfl⟩ | ⟨body, hnb, rfl⟩ | ⟨_, _, rfl⟩
    · rfl
    · rfl
    · exact (concept_lowerBottom_props c0).1 (h.coreClasses c0 hc0)
    · rfl
    · exact (foldr_some_props body hnb).1
    · rfl
  · intro l hl
    apply h.literals l
    simp only [Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map] at hl ⊢
    rcases hl with (hcM | hdaM) | hndaM
    · obtain ⟨c, hc, hlC⟩ := hcM
      rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, hc0, rfl⟩ | ⟨_, _, rfl⟩ | ⟨body, hnb, rfl⟩ | ⟨_, _, rfl⟩
      · simp [Concept.dataLiteralsOf] at hlC
      · simp [Concept.dataLiteralsOf] at hlC
      · exact Or.inl (Or.inl ⟨c0, hc0, (concept_lowerBottom_props c0).2.2.2.1 l hlC⟩)
      · simp [Concept.dataLiteralsOf] at hlC
      · rw [(foldr_some_props body hnb).2.2.2.1] at hlC; cases hlC
      · simp [Concept.dataLiteralsOf] at hlC
    · obtain ⟨dal, hdal, rfl⟩ := hdaM
      exact Or.inl (Or.inr ⟨dal, (List.mem_filter.mp hdal).1, rfl⟩)
    · obtain ⟨dal, hdal, rfl⟩ := hndaM
      exact Or.inr ⟨dal, (List.mem_filter.mp hdal).1, rfl⟩
  · intro d hd
    simp only [Problem.allDataRanges, List.mem_append, List.mem_flatMap, List.mem_map] at hd
    rcases hd with ⟨c, hc, hdC⟩ | ⟨rd, hrd, rfl⟩
    · rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, hc0, rfl⟩ | ⟨_, _, rfl⟩ | ⟨body, hnb, rfl⟩ | ⟨_, _, rfl⟩
      · simp [Concept.dataRangesOf] at hdC
      · simp [Concept.dataRangesOf] at hdC
      · exact h.dataRanges d (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c0, hc0, (concept_lowerBottom_props c0).2.2.1 d hdC⟩))
      · simp [Concept.dataRangesOf] at hdC
      · rw [(foldr_some_props body hnb).2.2.1] at hdC; cases hdC
      · rw [List.mem_singleton.mp hdC]; decide
    · exact h.dataRanges rd.2 (List.mem_append_right _ (List.mem_map.mpr ⟨rd, (List.mem_filter.mp hrd).1, rfl⟩))
  · exact checkSimpleWithTop_mono h.simple
      (fun rs hrs => (lowerBottom_rules_subset p rs hrs).1)
      (fun c hc hlen => ⟨c, (lowerBottom_chains_subset p c hc).1, hlen, rfl⟩)
      (lowerBottom_simpleRoles_subset p)
  · intro c hc
    exact h.acyclic.1 c (lowerBottom_chains_subset p c hc).1
  · rw [(lowerBottom_ordinary_eq p).1, (lowerBottom_ordinary_eq p).2]
    exact h.acyclic.2

/-! ### 3. Structural completeness through `lowerTopData?` -/

private theorem lowerTopDataConcept_exists {c : Concept}
    (h : ∀ d ∈ c.dataRangesOf, isWiderDataRange d = true) :
    ∃ c', lowerTopDataConcept? c = some c' ∧
      (c.coreClasses = true → c'.coreClasses = true) ∧
      (c.noBottomObj = true → c'.noBottomObj = true) ∧
      (∀ d ∈ c'.dataRangesOf, d ∈ c.dataRangesOf) ∧
      (∀ l ∈ c'.dataLiteralsOf, l ∈ c.dataLiteralsOf) ∧
      (∀ dp ∈ c'.dataPropsOf, dp ∈ c.dataPropsOf ∧ dp ≠ topDataProperty) ∧
      (∀ r ∈ c'.countedRoles, r ∈ c.countedRoles) := by
  induction c with
  | top | bottom | lit _ _ | nom _ _ | self _ _ =>
    exact ⟨_, rfl, id, id, fun _ h => h, fun _ h => h, by simp [Concept.dataPropsOf], fun _ h => h⟩
  | conj a b iha ihb =>
    obtain ⟨a', ha', ha1, ha2, had, hal, hap, har⟩ := iha fun d hd => h d (List.mem_append_left _ hd)
    obtain ⟨b', hb', hb1, hb2, hbd, hbl, hbp, hbr⟩ := ihb fun d hd => h d (List.mem_append_right _ hd)
    refine ⟨.conj a' b', by simp [lowerTopDataConcept?, ha', hb'],
      fun hc => by simp only [Concept.coreClasses, Bool.and_eq_true] at hc ⊢; exact ⟨ha1 hc.1, hb1 hc.2⟩,
      fun hc => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hc ⊢; exact ⟨ha2 hc.1, hb2 hc.2⟩,
      fun d hd => by simp only [Concept.dataRangesOf, List.mem_append] at hd ⊢; exact hd.elim (Or.inl ∘ had d) (Or.inr ∘ hbd d),
      fun l hl => by simp only [Concept.dataLiteralsOf, List.mem_append] at hl ⊢; exact hl.elim (Or.inl ∘ hal l) (Or.inr ∘ hbl l),
      fun dp hdp => by
        simp only [Concept.dataPropsOf, List.mem_append] at hdp ⊢
        exact hdp.elim (fun x => ⟨Or.inl (hap dp x).1, (hap dp x).2⟩) (fun x => ⟨Or.inr (hbp dp x).1, (hbp dp x).2⟩),
      fun r hr => by simp only [Concept.countedRoles, List.mem_append] at hr ⊢; exact hr.elim (Or.inl ∘ har r) (Or.inr ∘ hbr r)⟩
  | disj a b iha ihb =>
    obtain ⟨a', ha', ha1, ha2, had, hal, hap, har⟩ := iha fun d hd => h d (List.mem_append_left _ hd)
    obtain ⟨b', hb', hb1, hb2, hbd, hbl, hbp, hbr⟩ := ihb fun d hd => h d (List.mem_append_right _ hd)
    refine ⟨.disj a' b', by simp [lowerTopDataConcept?, ha', hb'],
      fun hc => by simp only [Concept.coreClasses, Bool.and_eq_true] at hc ⊢; exact ⟨ha1 hc.1, hb1 hc.2⟩,
      fun hc => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hc ⊢; exact ⟨ha2 hc.1, hb2 hc.2⟩,
      fun d hd => by simp only [Concept.dataRangesOf, List.mem_append] at hd ⊢; exact hd.elim (Or.inl ∘ had d) (Or.inr ∘ hbd d),
      fun l hl => by simp only [Concept.dataLiteralsOf, List.mem_append] at hl ⊢; exact hl.elim (Or.inl ∘ hal l) (Or.inr ∘ hbl l),
      fun dp hdp => by
        simp only [Concept.dataPropsOf, List.mem_append] at hdp ⊢
        exact hdp.elim (fun x => ⟨Or.inl (hap dp x).1, (hap dp x).2⟩) (fun x => ⟨Or.inr (hbp dp x).1, (hbp dp x).2⟩),
      fun r hr => by simp only [Concept.countedRoles, List.mem_append] at hr ⊢; exact hr.elim (Or.inl ∘ har r) (Or.inr ∘ hbr r)⟩
  | some r c ih =>
    obtain ⟨c', hc', h1, h2, hd, hl, hp, hr⟩ := ih h
    exact ⟨.some r c', by simp [lowerTopDataConcept?, hc'], h1,
      fun hnb => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hnb ⊢; exact ⟨hnb.1, h2 hnb.2⟩,
      hd, hl, hp, hr⟩
  | all r c ih =>
    obtain ⟨c', hc', h1, h2, hd, hl, hp, hr⟩ := ih h
    exact ⟨.all r c', by simp [lowerTopDataConcept?, hc'], h1,
      fun hnb => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hnb ⊢; exact ⟨hnb.1, h2 hnb.2⟩,
      hd, hl, hp, hr⟩
  | min n r c ih =>
    obtain ⟨c', hc', h1, h2, hd, hl, hp, hr⟩ := ih h
    refine ⟨.min n r c', by simp [lowerTopDataConcept?, hc'], h1,
      fun hnb => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hnb ⊢; exact ⟨hnb.1, h2 hnb.2⟩,
      hd, hl, hp, fun s hs => ?_⟩
    simp only [Concept.countedRoles, List.mem_cons] at hs ⊢
    exact hs.elim Or.inl (Or.inr ∘ hr s)
  | max n r c ih =>
    obtain ⟨c', hc', h1, h2, hd, hl, hp, hr⟩ := ih h
    refine ⟨.max n r c', by simp [lowerTopDataConcept?, hc'], h1,
      fun hnb => by simp only [Concept.noBottomObj, Bool.and_eq_true] at hnb ⊢; exact ⟨hnb.1, h2 hnb.2⟩,
      hd, hl, hp, fun s hs => ?_⟩
    simp only [Concept.countedRoles, List.mem_cons] at hs ⊢
    exact hs.elim Or.inl (Or.inr ∘ hr s)
  | dataSome dp d =>
    cases htop : isTopData dp
    · have hne : dp ≠ topDataProperty := fun he => by simp [isTopData, he] at htop
      exact ⟨_, by simp [lowerTopDataConcept?, htop], id, id, fun _ hm => hm, fun _ hm => hm,
        fun x hx => ⟨hx, by rw [List.mem_singleton.mp hx]; exact hne⟩, fun _ hm => hm⟩
    · have hd : isWiderDataRange d = true := h d (List.mem_cons_self ..)
      cases hres : dataRangeHasAtLeast d 1 <;>
        simp [lowerTopDataConcept?, htop, hd, hres, Concept.coreClasses, Concept.noBottomObj,
          Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataAll dp d =>
    cases htop : isTopData dp
    · have hne : dp ≠ topDataProperty := fun he => by simp [isTopData, he] at htop
      exact ⟨_, by simp [lowerTopDataConcept?, htop], id, id, fun _ hm => hm, fun _ hm => hm,
        fun x hx => ⟨hx, by rw [List.mem_singleton.mp hx]; exact hne⟩, fun _ hm => hm⟩
    · have hd : isWiderDataRange d = true := h d (List.mem_cons_self ..)
      cases hres : dataRangeHasAtLeast (.complement d) 1 <;>
        simp [lowerTopDataConcept?, htop, hd, hres, Concept.coreClasses, Concept.noBottomObj,
          Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataMin n dp d =>
    cases htop : isTopData dp
    · have hne : dp ≠ topDataProperty := fun he => by simp [isTopData, he] at htop
      exact ⟨_, by simp [lowerTopDataConcept?, htop], id, id, fun _ hm => hm, fun _ hm => hm,
        fun x hx => ⟨hx, by rw [List.mem_singleton.mp hx]; exact hne⟩, fun _ hm => hm⟩
    · have hd : isWiderDataRange d = true := h d (List.mem_cons_self ..)
      cases hres : dataRangeHasAtLeast d n <;>
        simp [lowerTopDataConcept?, htop, hd, hres, Concept.coreClasses, Concept.noBottomObj,
          Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataMax n dp d =>
    cases htop : isTopData dp
    · have hne : dp ≠ topDataProperty := fun he => by simp [isTopData, he] at htop
      exact ⟨_, by simp [lowerTopDataConcept?, htop], id, id, fun _ hm => hm, fun _ hm => hm,
        fun x hx => ⟨hx, by rw [List.mem_singleton.mp hx]; exact hne⟩, fun _ hm => hm⟩
    · have hd : isWiderDataRange d = true := h d (List.mem_cons_self ..)
      cases hres : dataRangeHasAtLeast d (n + 1) <;>
        simp [lowerTopDataConcept?, htop, hd, hres, Concept.coreClasses, Concept.noBottomObj,
          Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | dataValue dp l b =>
    cases htop : isTopData dp
    · have hne : dp ≠ topDataProperty := fun he => by simp [isTopData, he] at htop
      exact ⟨_, by simp [lowerTopDataConcept?, htop], id, id, fun _ hm => hm, fun _ hm => hm,
        fun x hx => ⟨hx, by rw [List.mem_singleton.mp hx]; exact hne⟩, fun _ hm => hm⟩
    · refine ⟨if b then .top else .bottom, by simp [lowerTopDataConcept?, htop], ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        cases b <;> simp [Concept.coreClasses, Concept.noBottomObj,
          Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]

private theorem mapM_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]⟩

private theorem mapM_option_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons a rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, tail, htail, rfl⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨a, List.mem_cons_self .., hb⟩
    · obtain ⟨x, hx, hfx⟩ := ih htail y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private theorem substUnivDataConcept_invariants (u : List IRI) (c : Concept) :
    (substUnivDataConcept u c).coreClasses = c.coreClasses ∧
    (substUnivDataConcept u c).noBottomObj = c.noBottomObj ∧
    (substUnivDataConcept u c).dataRangesOf = c.dataRangesOf ∧
    (substUnivDataConcept u c).dataLiteralsOf = c.dataLiteralsOf ∧
    (substUnivDataConcept u c).countedRoles = c.countedRoles ∧
    ((∀ dp ∈ c.dataPropsOf, dp ≠ bottomDataProperty) →
      ∀ dp ∈ (substUnivDataConcept u c).dataPropsOf, dp ≠ bottomDataProperty) := by
  have hsu (dp : IRI) (hne : dp ≠ bottomDataProperty) : substUnivData u dp ≠ bottomDataProperty := by
    unfold substUnivData
    by_cases hc : u.contains dp = true
    · simp only [hc, ↓reduceIte]; decide
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hne
  induction c with
  | top | bottom | lit _ _ | nom _ _ | self _ _ =>
    simp [substUnivDataConcept, Concept.coreClasses, Concept.noBottomObj,
      Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.dataPropsOf, Concept.countedRoles]
  | conj a b iha ihb | disj a b iha ihb =>
    refine ⟨by simp [substUnivDataConcept, Concept.coreClasses, iha.1, ihb.1],
      by simp [substUnivDataConcept, Concept.noBottomObj, iha.2.1, ihb.2.1],
      by simp [substUnivDataConcept, Concept.dataRangesOf, iha.2.2.1, ihb.2.2.1],
      by simp [substUnivDataConcept, Concept.dataLiteralsOf, iha.2.2.2.1, ihb.2.2.2.1],
      by simp [substUnivDataConcept, Concept.countedRoles, iha.2.2.2.2.1, ihb.2.2.2.2.1],
      fun h dp hdp => ?_⟩
    simp only [substUnivDataConcept, Concept.dataPropsOf, List.mem_append] at hdp
    exact hdp.elim
      (iha.2.2.2.2.2 (fun x hx => h x (List.mem_append_left _ hx)) dp)
      (ihb.2.2.2.2.2 (fun x hx => h x (List.mem_append_right _ hx)) dp)
  | some _ _ ih | all _ _ ih | min _ _ _ ih | max _ _ _ ih =>
    exact ⟨ih.1, by simp [substUnivDataConcept, Concept.noBottomObj, ih.2.1],
      ih.2.2.1, ih.2.2.2.1, by simp [substUnivDataConcept, Concept.countedRoles, ih.2.2.2.2.1],
      ih.2.2.2.2.2⟩
  | dataSome dp _ | dataAll dp _ | dataValue dp _ _ | dataMin _ dp _ | dataMax _ dp _ =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun h x hx => ?_⟩
    rw [List.mem_singleton.mp hx]
    exact hsu dp (h dp (List.mem_cons_self ..))

private theorem usesTopData_false_noTop {p : Problem} (h : usesTopData p = false) :
    ∀ dp ∈ p.allDataProps, dp ≠ topDataProperty := by
  have hc : ∀ c, hasTopDataConcept c = false → ∀ dp ∈ c.dataPropsOf, dp ≠ topDataProperty := by
    intro c hnc
    induction c with
    | top | bottom | lit _ _ | nom _ _ | self _ _ => intro _ hx; cases hx
    | conj a b iha ihb | disj a b iha ihb =>
      simp only [hasTopDataConcept, Bool.or_eq_false_iff] at hnc
      intro dp hdp
      exact (List.mem_append.mp hdp).elim (iha hnc.1 dp) (ihb hnc.2 dp)
    | some _ _ ih | all _ _ ih | min _ _ _ ih | max _ _ _ ih => exact ih hnc
    | dataSome dp _ | dataAll dp _ | dataValue dp _ _ | dataMin _ dp _ | dataMax _ dp _ =>
      intro x hx he
      rw [List.mem_singleton.mp hx] at he
      subst he
      simp [hasTopDataConcept, isTopData] at hnc
  simp only [usesTopData, Bool.or_eq_false_iff, List.any_eq_false] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hroot, htbox⟩, hsub⟩, hdisj⟩, hfunc⟩, hdr⟩, hkeys⟩, hca⟩, hda⟩, hnda⟩ := h
  intro dp hdp
  simp only [Problem.allDataProps, Problem.allConcepts, List.mem_eraseDups, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hdp
  rcases hdp with (((((((hcM | hdrM) | hsubM) | hdisjM) | hfuncM) | hkeyM) | hdaM) | hndaM)
  · obtain ⟨c, hcMem, hdpC⟩ := hcM
    rcases hcMem with rfl | ((ht | hk) | hcaM)
    · exact hc _ hroot dp hdpC
    · obtain ⟨q, hq, rfl | rfl⟩ := ht
      · exact hc _ (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr (htbox q hq))).1 dp hdpC
      · exact hc _ (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr (htbox q hq))).2 dp hdpC
    · obtain ⟨k, hk', rfl⟩ := hk
      exact hc _ (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr (hkeys k hk'))).1 dp hdpC
    · obtain ⟨ac, hac, rfl⟩ := hcaM
      exact hc _ (Bool.eq_false_iff.mpr (hca ac hac)) dp hdpC
  · obtain ⟨rd, hrd, rfl⟩ := hdrM; intro he; exact hdr rd hrd (by simp [isTopData, he])
  · obtain ⟨rs, hrs, rfl | rfl⟩ := hsubM
    · intro he; exact hsub rs hrs (by simp [isTopData, he])
    · intro he; exact hsub rs hrs (by simp [isTopData, he])
  · obtain ⟨rs, hrs, rfl | rfl⟩ := hdisjM
    · intro he; exact hdisj rs hrs (by simp [isTopData, he])
    · intro he; exact hdisj rs hrs (by simp [isTopData, he])
  · intro he; exact hfunc dp hfuncM (by simp [isTopData, he])
  · obtain ⟨k, hk, hdpK⟩ := hkeyM; intro he
    have hkF := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr (hkeys k hk))
    exact List.any_eq_false.mp hkF.2 dp hdpK (by simp [isTopData, he])
  · obtain ⟨dal, hdal, rfl⟩ := hdaM; intro he; exact hda dal hdal (by simp [isTopData, he])
  · obtain ⟨dal, hdal, rfl⟩ := hndaM; intro he; exact hnda dal hdal (by simp [isTopData, he])

private theorem unsatDataProblem_acyclic :
    AcyclicOWL2DLInput unsatDataProblem ∧ NoBottomObj unsatDataProblem ∧
    (∀ dp ∈ unsatDataProblem.allDataProps, isCoreDataPropIRI dp = true) := by
  have hall : ∀ c ∈ unsatDataProblem.allConcepts, c = .top ∨ c = .bottom := by
    intro c hc
    simp only [unsatDataProblem, Problem.allConcepts, List.mem_cons, List.mem_append,
      List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | ((⟨q, rfl, rfl | rfl⟩ | ⟨_, h, _⟩) | ⟨_, h, _⟩)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · cases h
    · cases h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro c hc; rcases hall c hc with rfl | rfl <;> rfl
  · simp [unsatDataProblem, Problem.allDataLiterals, Problem.allConcepts, Concept.dataLiteralsOf]
  · simp [unsatDataProblem, Problem.allDataRanges, Problem.allConcepts, Concept.dataRangesOf]
  · decide
  · simp [unsatDataProblem]
  · exact ⟨fun _ => [], by simp [unsatDataProblem, ordinaryChains],
      fun x cycle => by
        have h : ∀ {i a b}, Sabrina.RoleChains.DependencyPath
            (Sabrina.RoleChains.weakDependencies (ordinaryRules unsatDataProblem.rules))
            (Sabrina.RoleChains.strictDependencies (ordinaryChains unsatDataProblem.chains) (fun _ => [])) i a b →
            i = false := by
          intro i a b p
          induction p with
          | refl => rfl
          | weak => rfl
          | strict hs => simp [unsatDataProblem, ordinaryChains, Sabrina.RoleChains.strictDependencies] at hs
          | trans _ _ ih1 ih2 => simp [ih1, ih2]
        exact Bool.noConfusion (h cycle)⟩
  · refine ⟨fun c hc => by rcases hall c hc with rfl | rfl <;> rfl,
      by simp [unsatDataProblem], by simp [unsatDataProblem], by simp [unsatDataProblem],
      by simp [unsatDataProblem], by simp [unsatDataProblem], by simp [unsatDataProblem],
      by simp [unsatDataProblem], by simp [unsatDataProblem], by simp [unsatDataProblem]⟩
  · simp [unsatDataProblem, Problem.allDataProps, Problem.allConcepts, Concept.dataPropsOf]

private theorem lowerTopData_exists_of_acyclic {p : Problem}
    (ha : AcyclicOWL2DLInput p) (hnbObj : NoBottomObj p)
    (hnbData : ∀ dp ∈ p.allDataProps, dp ≠ bottomDataProperty) :
    ∃ p', lowerTopData? p = some p' ∧
      AcyclicOWL2DLInput p' ∧ NoBottomObj p' ∧
      (∀ dp ∈ p'.allDataProps, isCoreDataPropIRI dp = true) := by
  unfold lowerTopData?
  cases hu : usesTopData p
  · simp only [Bool.not_false, ↓reduceIte]
    refine ⟨p, rfl, ha, hnbObj, fun dp hdp => ?_⟩
    simp [isCoreDataPropIRI, usesTopData_false_noTop hu dp hdp, hnbData dp hdp]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold collapseUnivDataProps
    dsimp only
    cases hbot : (univDataProps p.subData).contains bottomDataProperty
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let u := univDataProps p.subData
      let pc : Problem :=
        { p with
          tbox := p.tbox.map fun q => ⟨substUnivDataConcept u q.sub, substUnivDataConcept u q.sup⟩
          subData := p.subData.map fun (r, s) => (substUnivData u r, substUnivData u s)
          disjointData := p.disjointData.map fun (r, s) => (substUnivData u r, substUnivData u s)
          funcData := p.funcData.map (substUnivData u)
          dataRanges := p.dataRanges.map fun (r, d) => (substUnivData u r, d)
          keys := p.keys.map fun k => { k with cls := substUnivDataConcept u k.cls, dataProps := k.dataProps.map (substUnivData u) }
          classAssertions := p.classAssertions.map fun (a, c) => (a, substUnivDataConcept u c)
          dataAssertions := p.dataAssertions.map fun (r, a, l) => (substUnivData u r, a, l)
          negDataAssertions := p.negDataAssertions.map fun (r, a, l) => (substUnivData u r, a, l)
          root := substUnivDataConcept u p.root }
      have hpcConcOrig : ∀ c ∈ pc.allConcepts, ∃ c0 ∈ p.allConcepts, c = substUnivDataConcept u c0 := by
        intro c hc
        simp only [pc, Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap,
          List.mem_map, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | ((ht | hk) | hca)
        · exact ⟨p.root, List.mem_cons_self .., rfl⟩
        · obtain ⟨q, ⟨q0, hq0, rfl⟩, rfl | rfl⟩ := ht
          · exact ⟨q0.sub, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inl rfl⟩)), rfl⟩
          · exact ⟨q0.sup, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inr rfl⟩)), rfl⟩
        · obtain ⟨k, ⟨k0, hk0, rfl⟩, rfl⟩ := hk
          exact ⟨k0.cls, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩)), rfl⟩
        · obtain ⟨ac, ⟨ac0, hac0, rfl⟩, rfl⟩ := hca
          exact ⟨ac0.2, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩), rfl⟩
      have hpcDR : ∀ d ∈ pc.allDataRanges, isWiderDataRange d = true := by
        intro d hd
        apply ha.dataRanges d
        simp only [Problem.allDataRanges, List.mem_append, List.mem_flatMap, List.mem_map] at hd ⊢
        rcases hd with ⟨c, hc, hdC⟩ | ⟨rd, hrd, rfl⟩
        · obtain ⟨c0, hc0, rfl⟩ := hpcConcOrig c hc
          exact Or.inl ⟨c0, hc0, by simpa [(substUnivDataConcept_invariants u c0).2.2.1] using hdC⟩
        · obtain ⟨rd0, hrd0, rfl⟩ := List.mem_map.mp hrd
          exact Or.inr ⟨rd0, hrd0, rfl⟩
      have hpcConcDR : ∀ c ∈ pc.allConcepts, ∀ d ∈ c.dataRangesOf, isWiderDataRange d = true :=
        fun c hc d hd => hpcDR d (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hd⟩))
      let topRangeGCIs : List Inclusion :=
        pc.dataRanges.filterMap fun (dp, d) =>
          if isTopData dp then some ⟨.top, .dataAll topDataProperty d⟩ else none
      have htboxIn : ∀ q ∈ pc.tbox ++ topRangeGCIs, ∃ q', lowerInclusion? q = some q' := by
        intro q hq
        rcases List.mem_append.mp hq with h1 | h2
        · obtain ⟨s1, hs1, _⟩ := lowerTopDataConcept_exists (hpcConcDR q.sub (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q, h1, Or.inl rfl⟩))))
          obtain ⟨s2, hs2, _⟩ := lowerTopDataConcept_exists (hpcConcDR q.sup (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q, h1, Or.inr rfl⟩))))
          exact ⟨⟨s1, s2⟩, by simp [lowerInclusion?, hs1, hs2]⟩
        · obtain ⟨⟨dp, d⟩, hrd, he⟩ := List.mem_filterMap.mp h2
          by_cases htd : isTopData dp = true
          · simp only [htd, ↓reduceIte, Option.some.injEq] at he
            subst he
            have hd : isWiderDataRange d = true :=
              hpcDR d (List.mem_append_right _ (List.mem_map.mpr ⟨(dp, d), hrd, rfl⟩))
            obtain ⟨s2, hs2, _⟩ := lowerTopDataConcept_exists (c := .dataAll topDataProperty d)
              (by simpa [Concept.dataRangesOf] using hd)
            refine ⟨⟨.top, s2⟩, ?_⟩
            unfold lowerInclusion?
            change (some Concept.top).bind (fun s1 =>
              (lowerTopDataConcept? (Concept.dataAll topDataProperty d)).map fun s2 => Inclusion.mk s1 s2) = some ⟨.top, s2⟩
            rw [hs2]; rfl
          · simp [htd] at he
      have hkeysIn : ∀ k ∈ pc.keys, ∃ k', lowerKey? k = some k' := by
        intro k hk
        obtain ⟨c', hc', _⟩ := lowerTopDataConcept_exists (hpcConcDR k.cls (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
        exact ⟨{ k with cls := c', dataProps := k.dataProps.filter (!isTopData ·) }, by simp [lowerKey?, hc']⟩
      have hcaIn : ∀ ac ∈ pc.classAssertions, ∃ ac', lowerClassAssertion? ac = some ac' := by
        intro ac hac
        obtain ⟨c', hc', _⟩ := lowerTopDataConcept_exists (hpcConcDR ac.2 (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac, hac, rfl⟩)))
        exact ⟨(ac.1, c'), by simp [lowerClassAssertion?, hc']⟩
      obtain ⟨tbox', htbox'⟩ := mapM_exists lowerInclusion? (pc.tbox ++ topRangeGCIs) htboxIn
      obtain ⟨keys', hkeys'⟩ := mapM_exists lowerKey? pc.keys hkeysIn
      obtain ⟨ca', hca'⟩ := mapM_exists lowerClassAssertion? pc.classAssertions hcaIn
      obtain ⟨root', hroot', _⟩ := lowerTopDataConcept_exists (hpcConcDR pc.root (List.mem_cons_self ..))
      let extraGCIs : List Inclusion :=
        ((pc.disjointData.filterMap fun (r, s) =>
            if isTopData r && isTopData s then some Concept.top
            else if isTopData r then some (Concept.dataSome s (.datatype literalDatatype))
            else if isTopData s then some (Concept.dataSome r (.datatype literalDatatype))
            else none) ++
          (pc.funcData.filterMap fun r => if isTopData r then some Concept.top else none) ++
          (pc.negDataAssertions.filterMap fun (r, _, _) => if isTopData r then some Concept.top else none)).map
          (fun c => ⟨c, .bottom⟩)
      let p' : Problem :=
        { pc with
          tbox := tbox' ++ extraGCIs
          subData := pc.subData.filter fun (r, s) => !isTopData r && !isTopData s
          disjointData := pc.disjointData.filter fun (r, s) => !isTopData r && !isTopData s
          funcData := pc.funcData.filter (!isTopData ·)
          dataRanges := pc.dataRanges.filter fun (dp, _) => !isTopData dp
          keys := keys'
          classAssertions := ca'
          dataAssertions := pc.dataAssertions.filter fun (r, _, _) => !isTopData r
          negDataAssertions := pc.negDataAssertions.filter fun (r, _, _) => !isTopData r
          root := root' }
      have hdir : lowerTopDataDirect? pc = some p' := by
        dsimp only [lowerTopDataDirect?, topRangeGCIs, extraGCIs, p']
        rw [htbox', Option.bind_some, hkeys', Option.bind_some, hca', Option.bind_some, hroot']
        rfl
      have hsuNoBot : ∀ dp, dp ≠ bottomDataProperty → substUnivData u dp ≠ bottomDataProperty := by
        intro dp hne; unfold substUnivData
        by_cases hc : u.contains dp = true
        · simp only [hc, ↓reduceIte]; decide
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hne
      have hpcNoBot : ∀ dp ∈ pc.allDataProps, dp ≠ bottomDataProperty := by
        intro dp hdp
        simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
          List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hdp
        rcases hdp with (((((((hcM | hdrM) | hsubM) | hdisjM) | hfuncM) | hkeyM) | hdaM) | hndaM)
        · obtain ⟨c, hc, hdpC⟩ := hcM
          obtain ⟨c0, hc0, rfl⟩ := hpcConcOrig c hc
          exact (substUnivDataConcept_invariants u c0).2.2.2.2.2
            (fun x hx => hnbData x (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c0, hc0, hx⟩)))))))) dp hdpC
        · obtain ⟨rd, hrd, rfl⟩ := hdrM
          obtain ⟨rd0, hrd0, rfl⟩ := List.mem_map.mp hrd
          exact hsuNoBot rd0.1 (hnbData rd0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rd0, hrd0, rfl⟩))))))))
        · obtain ⟨rs, hrs, rfl | rfl⟩ := hsubM
          · obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
            exact hsuNoBot rs0.1 (hnbData rs0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs0, hrs0, Or.inl rfl⟩)))))))
          · obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
            exact hsuNoBot rs0.2 (hnbData rs0.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs0, hrs0, Or.inr rfl⟩)))))))
        · obtain ⟨rs, hrs, rfl | rfl⟩ := hdisjM
          · obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
            exact hsuNoBot rs0.1 (hnbData rs0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs0, hrs0, Or.inl rfl⟩))))))
          · obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
            exact hsuNoBot rs0.2 (hnbData rs0.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs0, hrs0, Or.inr rfl⟩))))))
        · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hfuncM
          exact hsuNoBot r0 (hnbData r0 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hr0)))))
        · obtain ⟨k, hk, hdpK⟩ := hkeyM
          obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
          obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hdpK
          exact hsuNoBot r0 (hnbData r0 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inr ⟨k0, hk0, hr0⟩))))
        · obtain ⟨dal, hdal, rfl⟩ := hdaM
          obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp hdal
          exact hsuNoBot dal0.1 (hnbData dal0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨dal0, hdal0, rfl⟩)))
        · obtain ⟨dal, hdal, rfl⟩ := hndaM
          obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp hdal
          exact hsuNoBot dal0.1 (hnbData dal0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inr ⟨dal0, hdal0, rfl⟩))
      have hconcOrig : ∀ c' ∈ p'.allConcepts,
          c' = .top ∨ c' = .bottom ∨
          (∃ dp, dp ∈ pc.allDataProps ∧ dp ≠ topDataProperty ∧ c' = .dataSome dp (.datatype literalDatatype)) ∨
          (∃ c0 ∈ pc.allConcepts, lowerTopDataConcept? c0 = some c') := by
        intro c' hc'
        simp only [p', Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap,
          List.mem_map, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | ((ht | hk) | hcaM)
        · exact Or.inr (Or.inr (Or.inr ⟨pc.root, List.mem_cons_self .., hroot'⟩))
        · obtain ⟨q, hq, hqm⟩ := ht
          rcases hq with hq1 | hq2
          · obtain ⟨q0, hq0, hmap⟩ := mapM_option_mem htbox' q hq1
            simp only [lowerInclusion?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hmap
            obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hmap
            rcases List.mem_append.mp hq0 with hqt | hqr
            · rcases hqm with rfl | rfl
              · exact Or.inr (Or.inr (Or.inr ⟨q0.sub, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hqt, Or.inl rfl⟩)), hs1⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨q0.sup, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hqt, Or.inr rfl⟩)), hs2⟩))
            · obtain ⟨⟨dp, d⟩, hrd, he⟩ := List.mem_filterMap.mp hqr
              by_cases htd : isTopData dp = true
              · simp only [htd, ↓reduceIte, Option.some.injEq] at he
                subst he
                rcases hqm with rfl | rfl
                · simp [lowerTopDataConcept?] at hs1; exact Or.inl hs1.symm
                · have hd' := hpcDR d (List.mem_append_right _ (List.mem_map.mpr ⟨(dp, d), hrd, rfl⟩))
                  simp only [lowerTopDataConcept?, isTopData, beq_self_eq_true, ↓reduceIte, hd',
                    Option.some.injEq] at hs2
                  split at hs2
                  · exact Or.inr (Or.inl hs2.symm)
                  · exact Or.inl hs2.symm
              · simp [htd] at he
          · obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hq2
            simp only [List.mem_append] at hex
            rcases hqm with rfl | rfl
            · rcases hex with (h1 | h2) | h3
              · obtain ⟨⟨r, s⟩, hrs, he⟩ := List.mem_filterMap.mp h1
                by_cases h1t : isTopData r = true
                · by_cases h2t : isTopData s = true
                  · simp only [h1t, h2t, Bool.and_self, ↓reduceIte, Option.some.injEq] at he
                    subst he; exact Or.inl rfl
                  · simp only [h1t, h2t, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                      Option.some.injEq] at he
                    subst he
                    refine Or.inr (Or.inr (Or.inl ⟨s, ?_, fun h => h2t (by simp [isTopData, h]), rfl⟩))
                    simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
                    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(r, s), hrs, Or.inr rfl⟩))))
                · by_cases h2t : isTopData s = true
                  · simp only [h1t, h2t, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                      Option.some.injEq] at he
                    subst he
                    refine Or.inr (Or.inr (Or.inl ⟨r, ?_, fun h => h1t (by simp [isTopData, h]), rfl⟩))
                    simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
                    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(r, s), hrs, Or.inl rfl⟩))))
                  · simp [h1t, h2t] at he
              · obtain ⟨r, _, he⟩ := List.mem_filterMap.mp h2
                by_cases h1t : isTopData r = true <;> simp [h1t] at he
                subst he; exact Or.inl rfl
              · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp h3
                by_cases h1t : isTopData e.1 = true <;> simp [h1t] at he
                subst he; exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
        · obtain ⟨k, hk, rfl⟩ := hk
          obtain ⟨k0, hk0, hmap⟩ := mapM_option_mem hkeys' k hk
          obtain ⟨c1, hc1', rfl⟩ := Option.map_eq_some_iff.mp hmap
          exact Or.inr (Or.inr (Or.inr ⟨k0.cls, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩)), hc1'⟩))
        · obtain ⟨ac, hac, rfl⟩ := hcaM
          obtain ⟨ac0, hac0, hmap⟩ := mapM_option_mem hca' ac hac
          obtain ⟨c1, hc1', heq⟩ := Option.map_eq_some_iff.mp hmap
          cases heq
          exact Or.inr (Or.inr (Or.inr ⟨ac0.2, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩), hc1'⟩))
      have hltSpec : ∀ {c0 c1 : Concept}, c0 ∈ pc.allConcepts →
          lowerTopDataConcept? c0 = some c1 →
          (c0.coreClasses = true → c1.coreClasses = true) ∧
          (c0.noBottomObj = true → c1.noBottomObj = true) ∧
          (∀ d ∈ c1.dataRangesOf, d ∈ c0.dataRangesOf) ∧
          (∀ l ∈ c1.dataLiteralsOf, l ∈ c0.dataLiteralsOf) ∧
          (∀ dp ∈ c1.dataPropsOf, dp ∈ c0.dataPropsOf ∧ dp ≠ topDataProperty) ∧
          (∀ r ∈ c1.countedRoles, r ∈ c0.countedRoles) := by
        intro c0 c1 hc0 hl
        obtain ⟨c', hc', hspec⟩ := lowerTopDataConcept_exists (hpcConcDR c0 hc0)
        rw [hl] at hc'; cases hc'; exact hspec
      have hpcSimpleSub : ∀ r ∈ p'.simpleRoles, r ∈ p.simpleRoles := by
        intro r hr
        have hrpc : r ∈ pc.simpleRoles := by
          simp only [p', Problem.simpleRoles, List.mem_eraseDups, List.mem_append,
            List.mem_flatMap, List.mem_map] at hr ⊢
          rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ((hltSpec (List.mem_cons_self ..) hroot').2.2.2.2.2 r h1)))))
          · obtain ⟨q, hq, hrq⟩ := h2
            rcases hq with hq1 | hq2
            · obtain ⟨q0, hq0, hmap⟩ := mapM_option_mem htbox' q hq1
              simp only [lowerInclusion?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hmap
              obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hmap
              rcases List.mem_append.mp hq0 with hqt | hqr
              · rcases hrq with hr1 | hr2
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hqt, Or.inl ((hltSpec (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hqt, Or.inl rfl⟩))) hs1).2.2.2.2.2 r hr1)⟩))))
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hqt, Or.inr ((hltSpec (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hqt, Or.inr rfl⟩))) hs2).2.2.2.2.2 r hr2)⟩))))
              · obtain ⟨⟨dp, d⟩, hrd, he⟩ := List.mem_filterMap.mp hqr
                by_cases htd : isTopData dp = true
                · simp only [htd, ↓reduceIte, Option.some.injEq] at he
                  subst he
                  rcases hrq with hr1 | hr2
                  · simp [lowerTopDataConcept?] at hs1; subst hs1; simp [Concept.countedRoles] at hr1
                  · have hd' := hpcDR d (List.mem_append_right _ (List.mem_map.mpr ⟨(dp, d), hrd, rfl⟩))
                    simp only [lowerTopDataConcept?, isTopData, beq_self_eq_true, ↓reduceIte, hd', Option.some.injEq] at hs2
                    split at hs2 <;> (subst hs2; simp [Concept.countedRoles] at hr2)
                · simp [htd] at he
            · obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hq2
              simp only [List.mem_append] at hex
              rcases hrq with hr1 | hr2
              · rcases hex with (h1 | h2) | h3
                · obtain ⟨⟨a, b⟩, _, he⟩ := List.mem_filterMap.mp h1
                  by_cases h1t : isTopData a = true
                  · by_cases h2t : isTopData b = true <;> simp [h1t, h2t] at he <;> (subst he; simp [Concept.countedRoles] at hr1)
                  · by_cases h2t : isTopData b = true <;> simp [h1t, h2t] at he
                    subst he; simp [Concept.countedRoles] at hr1
                · obtain ⟨a, _, he⟩ := List.mem_filterMap.mp h2
                  by_cases h1t : isTopData a = true <;> simp [h1t] at he
                  subst he; simp [Concept.countedRoles] at hr1
                · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp h3
                  by_cases h1t : isTopData e.1 = true <;> simp [h1t] at he
                  subst he; simp [Concept.countedRoles] at hr1
              · simp [Concept.countedRoles] at hr2
          · obtain ⟨k, hk, hrk⟩ := h3
            obtain ⟨k0, hk0, hmap⟩ := mapM_option_mem hkeys' k hk
            obtain ⟨c1, hc1', rfl⟩ := Option.map_eq_some_iff.mp hmap
            exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, hk0, (hltSpec (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩))) hc1').2.2.2.2.2 r hrk⟩)))
          · obtain ⟨ac, hac, hrac⟩ := h4
            obtain ⟨ac0, hac0, hmap⟩ := mapM_option_mem hca' ac hac
            obtain ⟨c1, hc1', heq⟩ := Option.map_eq_some_iff.mp hmap
            cases heq
            exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0, (hltSpec (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩)) hc1').2.2.2.2.2 r hrac⟩))
          · exact Or.inl (Or.inr h5)
          · exact Or.inr h6
        simp only [pc, Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
          List.mem_map] at hrpc ⊢
        rcases hrpc with ((((h1 | h2) | h3) | h4) | h5) | h6
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (by simpa [(substUnivDataConcept_invariants u p.root).2.2.2.2.1] using h1)))))
        · obtain ⟨q, ⟨q0, hq0, rfl⟩, hrq⟩ := h2
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hq0,
            by simpa [(substUnivDataConcept_invariants u q0.sub).2.2.2.2.1,
                      (substUnivDataConcept_invariants u q0.sup).2.2.2.2.1] using hrq⟩))))
        · obtain ⟨k, ⟨k0, hk0, rfl⟩, hrk⟩ := h3
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, hk0,
            by simpa [(substUnivDataConcept_invariants u k0.cls).2.2.2.2.1] using hrk⟩)))
        · obtain ⟨ac, ⟨ac0, hac0, rfl⟩, hrac⟩ := h4
          exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0,
            by simpa [(substUnivDataConcept_invariants u ac0.2).2.2.2.2.1] using hrac⟩))
        · exact Or.inl (Or.inr h5)
        · exact Or.inr h6
      refine ⟨p', hdir, ⟨?_, ?_, ?_, checkSimpleWithTop_mono ha.simple (fun _ h => h) (fun c hc hl => ⟨c, hc, hl, rfl⟩) hpcSimpleSub, ha.acyclic⟩,
        ⟨?_, hnbObj.rules, hnbObj.chains, hnbObj.reflexive, hnbObj.irreflexive, hnbObj.asymmetric,
          hnbObj.disjoint, ?_, hnbObj.objAssertions, hnbObj.negObjAssertions⟩, ?_⟩
      · intro c' hc'
        rcases hconcOrig c' hc' with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨c0, hc0, hmap⟩
        · rfl
        · rfl
        · rfl
        · obtain ⟨c1, hc1, rfl⟩ := hpcConcOrig c0 hc0
          exact (hltSpec hc0 hmap).1 (by rw [(substUnivDataConcept_invariants u c1).1]; exact ha.coreClasses c1 hc1)
      · intro l hl
        apply ha.literals l
        simp only [p', Problem.allDataLiterals, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
          List.mem_map] at hl ⊢
        rcases hl with (hcM | hdaM) | hndaM
        · obtain ⟨c', hc', hlC⟩ := hcM
          rcases hconcOrig c' hc' with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨c0, hc0, hmap⟩
          · simp [Concept.dataLiteralsOf] at hlC
          · simp [Concept.dataLiteralsOf] at hlC
          · simp [Concept.dataLiteralsOf] at hlC
          · obtain ⟨c1, hc1, rfl⟩ := hpcConcOrig c0 hc0
            exact Or.inl (Or.inl ⟨c1, hc1, by simpa [(substUnivDataConcept_invariants u c1).2.2.2.1] using (hltSpec hc0 hmap).2.2.2.1 l hlC⟩)
        · obtain ⟨dal, hdal, rfl⟩ := hdaM
          obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hdal).1
          exact Or.inl (Or.inr ⟨dal0, hdal0, rfl⟩)
        · obtain ⟨dal, hdal, rfl⟩ := hndaM
          obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hdal).1
          exact Or.inr ⟨dal0, hdal0, rfl⟩
      · intro d hd
        simp only [p', Problem.allDataRanges, List.mem_append, List.mem_flatMap, List.mem_map] at hd
        rcases hd with ⟨c', hc', hdC⟩ | ⟨rd, hrd, rfl⟩
        · rcases hconcOrig c' hc' with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨c0, hc0, hmap⟩
          · simp [Concept.dataRangesOf] at hdC
          · simp [Concept.dataRangesOf] at hdC
          · rw [List.mem_singleton.mp hdC]; decide
          · exact hpcConcDR c0 hc0 d ((hltSpec hc0 hmap).2.2.1 d hdC)
        · exact hpcDR rd.2 (List.mem_append_right _ (List.mem_map.mpr ⟨rd, (List.mem_filter.mp hrd).1, rfl⟩))
      · intro c' hc'
        rcases hconcOrig c' hc' with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨c0, hc0, hmap⟩
        · rfl
        · rfl
        · rfl
        · obtain ⟨c1, hc1, rfl⟩ := hpcConcOrig c0 hc0
          exact (hltSpec hc0 hmap).2.1 (by rw [(substUnivDataConcept_invariants u c1).2.1]; exact hnbObj.concepts c1 hc1)
      · intro k hk r hr
        obtain ⟨k0, hk0, hmap⟩ := mapM_option_mem hkeys' k hk
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hk0
        exact hnbObj.keys k1 hk1 r hr
      · intro dp hdp
        have hcore : dp ≠ topDataProperty ∧ dp ≠ bottomDataProperty := by
          simp only [p', Problem.allDataProps, List.mem_eraseDups, List.mem_append,
            List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hdp
          rcases hdp with (((((((hcM | hdrM) | hsubM) | hdisjM) | hfuncM) | hkeyM) | hdaM) | hndaM)
          · obtain ⟨c', hc', hdpC⟩ := hcM
            rcases hconcOrig c' hc' with rfl | rfl | ⟨dp0, hdp0, hnt, rfl⟩ | ⟨c0, hc0, hmap⟩
            · simp [Concept.dataPropsOf] at hdpC
            · simp [Concept.dataPropsOf] at hdpC
            · rw [List.mem_singleton.mp hdpC]; exact ⟨hnt, hpcNoBot dp0 hdp0⟩
            · have hsp := (hltSpec hc0 hmap).2.2.2.2.1 dp hdpC
              exact ⟨hsp.2, hpcNoBot dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c0, hc0, hsp.1⟩)))))))⟩
          · obtain ⟨rd, hrd, rfl⟩ := hdrM
            have hf := List.mem_filter.mp hrd
            exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot rd.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rd, hf.1, rfl⟩)))))))⟩
          · obtain ⟨rs, hrs, rfl | rfl⟩ := hsubM
            · have hf := List.mem_filter.mp hrs
              exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot rs.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hf.1, Or.inl rfl⟩))))))⟩
            · have hf := List.mem_filter.mp hrs
              exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot rs.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hf.1, Or.inr rfl⟩))))))⟩
          · obtain ⟨rs, hrs, rfl | rfl⟩ := hdisjM
            · have hf := List.mem_filter.mp hrs
              exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot rs.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hf.1, Or.inl rfl⟩)))))⟩
            · have hf := List.mem_filter.mp hrs
              exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot rs.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hf.1, Or.inr rfl⟩)))))⟩
          · have hf := List.mem_filter.mp hfuncM
            exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hf.1))))⟩
          · obtain ⟨k, hk, hdpK⟩ := hkeyM
            obtain ⟨k0, hk0, hmap⟩ := mapM_option_mem hkeys' k hk
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
            have hf := List.mem_filter.mp hdpK
            exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inr ⟨k0, hk0, hf.1⟩)))⟩
          · obtain ⟨dal, hdal, rfl⟩ := hdaM
            have hf := List.mem_filter.mp hdal
            exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot dal.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨dal, hf.1, rfl⟩))⟩
          · obtain ⟨dal, hdal, rfl⟩ := hndaM
            have hf := List.mem_filter.mp hdal
            exact ⟨fun h => by simp [isTopData, h] at hf, hpcNoBot dal.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inr ⟨dal, hf.1, rfl⟩)⟩
        simp [isCoreDataPropIRI, hcore.1, hcore.2]
    · simp only [↓reduceIte]
      exact ⟨unsatDataProblem,
        by simp [lowerTopDataDirect?, unsatDataProblem, lowerInclusion?, lowerTopDataConcept?],
        unsatDataProblem_acyclic⟩

/-! ### 4. Structural completeness through `encodeWiderData` -/

private theorem isWiderExactAtom_of_mem_atoms {d : DataRange} (hd : isWiderDataRange d = true) :
    ∀ a ∈ Sabrina.OWL2.SROIQD.Termination.atomsOfDataRange d, isWiderExactAtom a = true := by
  induction d with
  | complement r ih => exact ih hd
  | intersection a b iha ihb | union a b iha ihb =>
    simp only [isWiderDataRange, Bool.and_eq_true] at hd
    intro x hx
    simp only [Sabrina.OWL2.SROIQD.Termination.atomsOfDataRange, List.mem_eraseDups,
      List.mem_append] at hx
    rcases hx with h1 | h2
    · exact iha hd.1 x h1
    · exact ihb hd.2 x h2
  | datatype _ | oneOf _ | restriction _ _ =>
    intro a ha
    simp only [Sabrina.OWL2.SROIQD.Termination.atomsOfDataRange, List.mem_singleton] at ha
    rw [ha]
    exact hd

private structure EncodedDataReady (p : Problem) : Prop where
  concepts : ∀ c ∈ p.allConcepts, c.coreClasses = true ∧ c.noBottomObj = true ∧
    (∀ dp ∈ c.dataPropsOf, isCoreDataPropIRI dp = true) ∧
    (∀ d ∈ c.dataRangesOf, d.isSROIQD = true) ∧
    (∀ l ∈ c.dataLiteralsOf, (decodeLiteral l).isSome = true)
  noBot : NoBottomObj p
  subData : ∀ rs ∈ p.subData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  disjointData : ∀ rs ∈ p.disjointData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  funcData : ∀ dp ∈ p.funcData, isCoreDataPropIRI dp = true
  dataRanges : ∀ rd ∈ p.dataRanges, isCoreDataPropIRI rd.1 = true ∧ rd.2.isSROIQD = true
  keysData : ∀ k ∈ p.keys, ∀ dp ∈ k.dataProps, isCoreDataPropIRI dp = true
  dataAssertions : ∀ dal ∈ p.dataAssertions, isCoreDataPropIRI dal.1 = true ∧ (decodeLiteral dal.2.2).isSome = true
  negDataAssertions : ∀ dal ∈ p.negDataAssertions, isCoreDataPropIRI dal.1 = true ∧ (decodeLiteral dal.2.2).isSome = true
  simple : p.checkSimpleWithTop = true
  acyclic : AcyclicOWL2DLHierarchy p.rules p.chains

private theorem encodeConcept_invariants (enc : WiderEncoding) (c : Concept) :
    (enc.encodeConcept c).coreClasses = c.coreClasses ∧
    (enc.encodeConcept c).noBottomObj = c.noBottomObj ∧
    (enc.encodeConcept c).dataPropsOf = c.dataPropsOf ∧
    (enc.encodeConcept c).countedRoles = c.countedRoles ∧
    (∀ d ∈ (enc.encodeConcept c).dataRangesOf, d.isSROIQD = true) ∧
    (∀ l ∈ (enc.encodeConcept c).dataLiteralsOf, (decodeLiteral l).isSome = true) := by
  induction c with
  | top | bottom | lit _ _ | nom _ _ | self _ _ =>
    simp [WiderEncoding.encodeConcept, Concept.coreClasses, Concept.noBottomObj,
      Concept.dataPropsOf, Concept.countedRoles, Concept.dataRangesOf, Concept.dataLiteralsOf]
  | conj a b iha ihb | disj a b iha ihb =>
    refine ⟨by simp [WiderEncoding.encodeConcept, Concept.coreClasses, iha.1, ihb.1],
      by simp [WiderEncoding.encodeConcept, Concept.noBottomObj, iha.2.1, ihb.2.1],
      by simp [WiderEncoding.encodeConcept, Concept.dataPropsOf, iha.2.2.1, ihb.2.2.1],
      by simp [WiderEncoding.encodeConcept, Concept.countedRoles, iha.2.2.2.1, ihb.2.2.2.1],
      fun d hd => by
        simp only [WiderEncoding.encodeConcept, Concept.dataRangesOf, List.mem_append] at hd
        exact hd.elim (iha.2.2.2.2.1 d) (ihb.2.2.2.2.1 d),
      fun l hl => by
        simp only [WiderEncoding.encodeConcept, Concept.dataLiteralsOf, List.mem_append] at hl
        exact hl.elim (iha.2.2.2.2.2 l) (ihb.2.2.2.2.2 l)⟩
  | some _ _ ih | all _ _ ih | min _ _ _ ih | max _ _ _ ih =>
    exact ⟨ih.1, by simp [WiderEncoding.encodeConcept, Concept.noBottomObj, ih.2.1],
      ih.2.2.1, by simp [WiderEncoding.encodeConcept, Concept.countedRoles, ih.2.2.2.1],
      ih.2.2.2.2.1, ih.2.2.2.2.2⟩
  | dataSome dp d | dataAll dp d | dataMin _ dp d | dataMax _ dp d =>
    refine ⟨rfl, rfl, rfl, rfl, fun x hx => ?_, by simp [WiderEncoding.encodeConcept, Concept.dataLiteralsOf]⟩
    rw [List.mem_singleton.mp hx]
    exact encodeDataRange_isSROIQD enc d
  | dataValue dp l b =>
    refine ⟨rfl, rfl, rfl, rfl, by simp [WiderEncoding.encodeConcept, Concept.dataRangesOf], fun x hx => ?_⟩
    rw [List.mem_singleton.mp hx]
    exact encodeLiteral_isSome enc l

private theorem encodeWiderData_exists_of_core {p : Problem}
    (ha : AcyclicOWL2DLInput p) (hnbObj : NoBottomObj p)
    (hcoreDP : ∀ dp ∈ p.allDataProps, isCoreDataPropIRI dp = true) :
    ∃ q, encodeWiderData p = some q ∧ EncodedDataReady q := by
  have hcond :
      (p.allDataProps.all (fun dp => dp != topDataProperty && dp != bottomDataProperty) &&
       p.allDataLiterals.all (fun l => (decodeLiteral l).isSome) &&
       widerAtomsAdmissible (.oneOf p.allDataLiterals :: p.allDataAtoms)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, widerAtomsAdmissible, List.mem_cons]
    refine ⟨⟨fun dp hdp => Bool.and_eq_true_iff.mp (hcoreDP dp hdp), ha.literals⟩, fun a ha' => ?_⟩
    rcases ha' with rfl | haMem
    · simp only [isWiderExactAtom, legacy_isWiderExactAtom, Bool.or_eq_true]
      exact Or.inl (Or.inl (List.all_eq_true.mpr ha.literals))
    · obtain ⟨d, hd, hda⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp haMem)
      exact isWiderExactAtom_of_mem_atoms (ha.dataRanges d hd) a hda
  have hbuild : ∃ enc, buildWiderEncoding p = some enc := by
    unfold buildWiderEncoding
    dsimp only
    rw [hcond]
    exact ⟨_, rfl⟩
  obtain ⟨enc, henc⟩ := hbuild
  refine ⟨enc.encodeProblem p, by simp [encodeWiderData, henc], ?_⟩
  have hconcOrig : ∀ c ∈ (enc.encodeProblem p).allConcepts, ∃ c0 ∈ p.allConcepts, c = enc.encodeConcept c0 := by
    intro c hc
    simp only [WiderEncoding.encodeProblem, Problem.allConcepts, List.mem_cons, List.mem_append,
      List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | ((ht | hk) | hca)
    · exact ⟨p.root, List.mem_cons_self .., rfl⟩
    · obtain ⟨q, ⟨q0, hq0, rfl⟩, rfl | rfl⟩ := ht
      · exact ⟨q0.sub, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inl rfl⟩)), rfl⟩
      · exact ⟨q0.sup, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inr rfl⟩)), rfl⟩
    · obtain ⟨k, ⟨k0, hk0, rfl⟩, rfl⟩ := hk
      exact ⟨k0.cls, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩)), rfl⟩
    · obtain ⟨ac, ⟨ac0, hac0, rfl⟩, rfl⟩ := hca
      exact ⟨ac0.2, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩), rfl⟩
  have hsimpleSub : ∀ r ∈ (enc.encodeProblem p).simpleRoles, r ∈ p.simpleRoles := by
    intro r hr
    simp only [WiderEncoding.encodeProblem, Problem.simpleRoles, List.mem_eraseDups, List.mem_append,
      List.mem_flatMap, List.mem_map] at hr ⊢
    rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (by simpa [(encodeConcept_invariants enc p.root).2.2.2.1] using h1)))))
    · obtain ⟨q, ⟨q0, hq0, rfl⟩, hrq⟩ := h2
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hq0,
        by simpa [(encodeConcept_invariants enc q0.sub).2.2.2.1, (encodeConcept_invariants enc q0.sup).2.2.2.1] using hrq⟩))))
    · obtain ⟨k, ⟨k0, hk0, rfl⟩, hrk⟩ := h3
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, hk0, by simpa [(encodeConcept_invariants enc k0.cls).2.2.2.1] using hrk⟩)))
    · obtain ⟨ac, ⟨ac0, hac0, rfl⟩, hrac⟩ := h4
      exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0, by simpa [(encodeConcept_invariants enc ac0.2).2.2.2.1] using hrac⟩))
    · exact Or.inl (Or.inr h5)
    · exact Or.inr h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    checkSimpleWithTop_mono ha.simple (fun _ h => h) (fun c hc hl => ⟨c, hc, hl, rfl⟩) hsimpleSub,
    ha.acyclic⟩
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := hconcOrig c hc
    have hi := encodeConcept_invariants enc c0
    exact ⟨by rw [hi.1]; exact ha.coreClasses c0 hc0,
      by rw [hi.2.1]; exact hnbObj.concepts c0 hc0,
      fun dp hdp => hcoreDP dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c0, hc0, by simpa [hi.2.2.1] using hdp⟩))))))),
      hi.2.2.2.2.1, hi.2.2.2.2.2⟩
  · refine ⟨fun c hc => ?_, hnbObj.rules, hnbObj.chains, hnbObj.reflexive, hnbObj.irreflexive,
      hnbObj.asymmetric, hnbObj.disjoint, ?_, hnbObj.objAssertions, hnbObj.negObjAssertions⟩
    · obtain ⟨c0, hc0, rfl⟩ := hconcOrig c hc
      rw [(encodeConcept_invariants enc c0).2.1]; exact hnbObj.concepts c0 hc0
    · intro k hk r hr
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
      exact hnbObj.keys k0 hk0 r hr
  · intro rs hrs
    exact ⟨hcoreDP rs.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hrs, Or.inl rfl⟩)))))),
           hcoreDP rs.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hrs, Or.inr rfl⟩))))))⟩
  · intro rs hrs
    exact ⟨hcoreDP rs.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hrs, Or.inl rfl⟩))))),
           hcoreDP rs.2 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rs, hrs, Or.inr rfl⟩)))))⟩
  · intro dp hdp
    exact hcoreDP dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hdp))))
  · intro rd hrd
    rcases List.mem_append.mp hrd with h1 | h2
    · obtain ⟨rd0, hrd0, rfl⟩ := List.mem_map.mp h1
      exact ⟨hcoreDP rd0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rd0, hrd0, rfl⟩))))))),
             encodeDataRange_isSROIQD enc rd0.2⟩
    · obtain ⟨dp, hdp, rfl⟩ := List.mem_map.mp h2
      exact ⟨hcoreDP dp hdp, allSlotsDR_isSROIQD enc.totalSlots⟩
  · intro k hk dp hdp
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    exact hcoreDP dp (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl (Or.inr ⟨k0, hk0, hdp⟩)))
  · intro dal hdal
    obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp hdal
    exact ⟨hcoreDP dal0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨dal0, hdal0, rfl⟩)),
           encodeLiteral_isSome enc dal0.2.2⟩
  · intro dal hdal
    obtain ⟨dal0, hdal0, rfl⟩ := List.mem_map.mp hdal
    exact ⟨hcoreDP dal0.1 (by simp only [Problem.allDataProps, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inr ⟨dal0, hdal0, rfl⟩),
           encodeLiteral_isSome enc dal0.2.2⟩

/-! ### 5. Preservation of regularity and admission through `lowerAllTopRoleAxioms` -/

private theorem reachable_univ_closed {p : Problem} {a b : OrientedRole}
    (hr : Reachable p.rules a b) (ha : a.1 ∈ univRoles p) : b.1 ∈ univRoles p := by
  induction hr with
  | refl => exact ha
  | step hs =>
    rcases List.mem_append.mp hs with h1 | h2
    · exact univRoles_closed_rules h1 ha
    · obtain ⟨e, he, heq⟩ := List.mem_map.mp h2
      have h1 : e.1.1 = _ := congrArg (fun x => x.1.1) heq
      have h2' : e.2.1 = _ := congrArg (fun x => x.2.1) heq
      rw [← h2']
      exact univRoles_closed_rules he (h1.symm ▸ ha)
  | trans _ _ ih1 ih2 => exact ih2 (ih1 ha)

private theorem reachable_split_ordinary {rules : RoleTheory}
    (hnb : ∀ rs ∈ rules, rs.1.1 ≠ bottomObjectProperty ∧ rs.2.1 ≠ bottomObjectProperty)
    {a b : OrientedRole} (hr : Reachable rules a b) :
    Reachable (ordinaryRules rules) a b ∨
    ∃ o : Bool, Reachable rules (topObjectProperty, o) b := by
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @step r s hs =>
    rcases List.mem_append.mp hs with h1 | h2
    · by_cases ht1 : r.1 = topObjectProperty
      · exact Or.inr ⟨r.2, .step (by rw [← ht1]; exact hs)⟩
      · by_cases ht2 : s.1 = topObjectProperty
        · exact Or.inr ⟨s.2, by rw [← ht2]; exact .refl _⟩
        · have hnb' := hnb (r, s) h1
          have hord : (r, s) ∈ ordinaryRules rules :=
            List.mem_filter.mpr ⟨h1, by simp [isCoreObjPropIRI, ht1, ht2, hnb'.1, hnb'.2]⟩
          exact Or.inl (.step (List.mem_append_left _ hord))
    · obtain ⟨⟨r0, s0⟩, hmem, heq⟩ := List.mem_map.mp h2
      have hr0 : r0.1 = r.1 := congrArg (fun x => x.1.1) heq
      have hs0 : s0.1 = s.1 := congrArg (fun x => x.2.1) heq
      by_cases ht1 : r.1 = topObjectProperty
      · exact Or.inr ⟨r.2, .step (by rw [← ht1]; exact hs)⟩
      · by_cases ht2 : s.1 = topObjectProperty
        · exact Or.inr ⟨s.2, by rw [← ht2]; exact .refl _⟩
        · have hnb' := hnb (r0, s0) hmem
          have hord : (r0, s0) ∈ ordinaryRules rules := by
            refine List.mem_filter.mpr ⟨hmem, ?_⟩
            simp only [Bool.and_eq_true, isCoreObjPropIRI, bne_iff_ne]
            exact ⟨⟨hr0 ▸ ht1, hnb'.1⟩, ⟨hs0 ▸ ht2, hnb'.2⟩⟩
          exact Or.inl (.step (List.mem_append_right _ (List.mem_map.mpr ⟨(r0, s0), hord, heq⟩)))
  | @trans x y z h1 h2 ih1 ih2 =>
    rcases ih2 with h2o | h2t
    · rcases ih1 with h1o | ⟨o, h1t⟩
      · exact Or.inl (h1o.trans h2o)
      · exact Or.inr ⟨o, h1t.trans h2⟩
    · exact Or.inr h2t

private theorem rank_le_of_reachable_ordinary {rank : Rank} {rules : RoleTheory} {chains : List Chain}
    (hr : Ranked rank rules chains) {a b : OrientedRole} (hp : Reachable rules a b) :
    rank a.1 ≤ rank b.1 := by
  rcases Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mpr hp with rfl | hmem
  · exact Nat.le_refl _
  · exact hr.respectsClosure hmem

private theorem concept_isSROIQDWithTop_of_ready {c : Concept}
    (hcore : c.coreClasses = true)
    (hnb : c.noBottomObj = true)
    (hdp : ∀ dp ∈ c.dataPropsOf, isCoreDataPropIRI dp = true)
    (hdr : ∀ d ∈ c.dataRangesOf, d.isSROIQD = true)
    (hlit : ∀ l ∈ c.dataLiteralsOf, (decodeLiteral l).isSome = true)
    (hcnt : ∀ r ∈ c.countedRoles, r.1 ≠ topObjectProperty) :
    c.isSROIQDWithTop = true := by
  induction c with
  | top | bottom | nom _ _ => rfl
  | lit a _ => exact hcore
  | self r _ =>
    simp only [Concept.noBottomObj, bne_iff_ne] at hnb
    have hnt := hcnt r (List.mem_cons_self ..)
    simp [Concept.isSROIQDWithTop, isCoreObjPropIRI, hnt, hnb]
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.coreClasses, Concept.noBottomObj, Bool.and_eq_true] at hcore hnb
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨iha hcore.1 hnb.1 (fun x hx => hdp x (List.mem_append_left _ hx))
             (fun x hx => hdr x (List.mem_append_left _ hx))
             (fun x hx => hlit x (List.mem_append_left _ hx))
             (fun x hx => hcnt x (List.mem_append_left _ hx)),
           ihb hcore.2 hnb.2 (fun x hx => hdp x (List.mem_append_right _ hx))
             (fun x hx => hdr x (List.mem_append_right _ hx))
             (fun x hx => hlit x (List.mem_append_right _ hx))
             (fun x hx => hcnt x (List.mem_append_right _ hx))⟩
  | some r c ih | all r c ih =>
    simp only [Concept.noBottomObj, Bool.and_eq_true, bne_iff_ne] at hnb
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
    refine ⟨?_, ih hcore hnb.2 hdp hdr hlit hcnt⟩
    by_cases ht : r.1 = topObjectProperty
    · simp [isObjPropOrTop, ht]
    · simp [isObjPropOrTop, isCoreObjPropIRI, ht, hnb.1]
  | min n r c ih | max n r c ih =>
    simp only [Concept.noBottomObj, Bool.and_eq_true, bne_iff_ne] at hnb
    have hnt := hcnt r (List.mem_cons_self ..)
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨by simp [isCoreObjPropIRI, hnt, hnb.1],
           ih hcore hnb.2 hdp hdr hlit (fun x hx => hcnt x (List.mem_cons_of_mem _ hx))⟩
  | dataSome dp d | dataAll dp d | dataMin _ dp d | dataMax _ dp d =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨hdp dp (List.mem_cons_self ..), hdr d (List.mem_cons_self ..)⟩
  | dataValue dp l _ =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨hdp dp (List.mem_cons_self ..), hlit l (List.mem_cons_self ..)⟩

private theorem canonUniv_concept_invariants (U : List IRI) (c : Concept) :
    (c.canonUniv U).coreClasses = c.coreClasses ∧
    (c.noBottomObj = true → (c.canonUniv U).noBottomObj = true) ∧
    (c.canonUniv U).dataPropsOf = c.dataPropsOf ∧
    (c.canonUniv U).dataRangesOf = c.dataRangesOf ∧
    (c.canonUniv U).dataLiteralsOf = c.dataLiteralsOf ∧
    ((∀ r ∈ c.countedRoles, r.1 ∉ U) → (c.canonUniv U).countedRoles = c.countedRoles) := by
  have hcuNb (r : IRI) (hnb : r ≠ bottomObjectProperty) : canonUniv U r ≠ bottomObjectProperty := by
    unfold canonUniv
    by_cases hc : U.contains r = true
    · simp only [hc, ↓reduceIte]; decide
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hnb
  induction c with
  | top | bottom | lit _ _ | nom _ _
  | dataSome _ _ | dataAll _ _ | dataValue _ _ _ | dataMin _ _ _ | dataMax _ _ _ =>
    simp [Concept.canonUniv, Concept.coreClasses, Concept.noBottomObj, Concept.dataPropsOf,
      Concept.dataRangesOf, Concept.dataLiteralsOf, Concept.countedRoles]
  | self r b =>
    refine ⟨rfl, fun hnb => ?_, rfl, rfl, rfl, fun hnu => ?_⟩
    · simp only [Concept.canonUniv, canonUnivOriented, Concept.noBottomObj, bne_iff_ne] at hnb ⊢
      exact hcuNb r.1 hnb
    · have hr : r.1 ∉ U := hnu r (List.mem_cons_self ..)
      simp [Concept.canonUniv, Concept.countedRoles, canonUnivOriented, canonUniv, hr]
  | conj a b iha ihb | disj a b iha ihb =>
    refine ⟨by simp [Concept.canonUniv, Concept.coreClasses, iha.1, ihb.1],
      fun hnb => by
        simp only [Concept.canonUniv, Concept.noBottomObj, Bool.and_eq_true] at hnb ⊢
        exact ⟨iha.2.1 hnb.1, ihb.2.1 hnb.2⟩,
      by simp [Concept.canonUniv, Concept.dataPropsOf, iha.2.2.1, ihb.2.2.1],
      by simp [Concept.canonUniv, Concept.dataRangesOf, iha.2.2.2.1, ihb.2.2.2.1],
      by simp [Concept.canonUniv, Concept.dataLiteralsOf, iha.2.2.2.2.1, ihb.2.2.2.2.1],
      fun hnu => by
        simp only [Concept.canonUniv, Concept.countedRoles]
        rw [iha.2.2.2.2.2 (fun r hr => hnu r (List.mem_append_left _ hr)),
            ihb.2.2.2.2.2 (fun r hr => hnu r (List.mem_append_right _ hr))]⟩
  | some r c ih | all r c ih =>
    refine ⟨ih.1, fun hnb => ?_, ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
    simp only [Concept.canonUniv, canonUnivOriented, Concept.noBottomObj, Bool.and_eq_true, bne_iff_ne] at hnb ⊢
    exact ⟨hcuNb r.1 hnb.1, ih.2.1 hnb.2⟩
  | min n r c ih | max n r c ih =>
    refine ⟨ih.1, fun hnb => ?_, ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, fun hnu => ?_⟩
    · simp only [Concept.canonUniv, canonUnivOriented, Concept.noBottomObj, Bool.and_eq_true, bne_iff_ne] at hnb ⊢
      exact ⟨hcuNb r.1 hnb.1, ih.2.1 hnb.2⟩
    · have hr : r.1 ∉ U := hnu r (List.mem_cons_self ..)
      have hcf : U.contains r.1 = false := Bool.eq_false_iff.mpr fun hm => hr (List.contains_iff_mem.mp hm)
      simp only [Concept.canonUniv, Concept.countedRoles, canonUnivOriented, canonUniv, hcf,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih.2.2.2.2.2 (fun s hs => hnu s (List.mem_cons_of_mem _ hs))]

private theorem lowerBottom_eq_of_ready {p : Problem} (hr : EncodedDataReady p) :
    EncodedDataReady p.lowerBottom := by
  have hnb := lowerBottom_noBottomObj p
  refine ⟨?_, hnb,
    fun rs hrs => hr.subData rs (List.mem_filter.mp hrs).1,
    fun rs hrs => hr.disjointData rs (List.mem_filter.mp hrs).1,
    fun dp hdp => hr.funcData dp (List.mem_filter.mp hdp).1,
    fun rd hrd => hr.dataRanges rd (List.mem_filter.mp hrd).1,
    fun k hk dp hdp => by
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
      exact hr.keysData k0 (List.mem_filter.mp hk0).1 dp hdp,
    fun dal hdal => hr.dataAssertions dal (List.mem_filter.mp hdal).1,
    fun dal hdal => hr.negDataAssertions dal (List.mem_filter.mp hdal).1,
    checkSimpleWithTop_mono hr.simple
      (fun rs hrs => (lowerBottom_rules_subset p rs hrs).1)
      (fun c hc hlen => ⟨c, (lowerBottom_chains_subset p c hc).1, hlen, rfl⟩)
      (lowerBottom_simpleRoles_subset p),
    fun c hc => hr.acyclic.1 c (lowerBottom_chains_subset p c hc).1,
    by rw [(lowerBottom_ordinary_eq p).1, (lowerBottom_ordinary_eq p).2]; exact hr.acyclic.2⟩
  intro c hc
  rcases lowerBottom_allConcepts_cases p hc with rfl | rfl | ⟨c0, hc0, rfl⟩ | ⟨rs, hnbR, rfl⟩ | ⟨body, hnbB, rfl⟩ | ⟨dp, hnbD, rfl⟩
  · simp [Concept.coreClasses, Concept.noBottomObj, Concept.dataPropsOf, Concept.dataRangesOf, Concept.dataLiteralsOf]
  · simp [Concept.coreClasses, Concept.noBottomObj, Concept.dataPropsOf, Concept.dataRangesOf, Concept.dataLiteralsOf]
  · have hc0' := hr.concepts c0 hc0
    have hlb := concept_lowerBottom_props c0
    exact ⟨hlb.1 hc0'.1, hlb.2.1,
      fun dp hdp => hc0'.2.2.1 dp (hlb.2.2.2.2.1 dp hdp).1,
      fun d hd => hc0'.2.2.2.1 d (hlb.2.2.1 d hd),
      fun l hl => hc0'.2.2.2.2 l (hlb.2.2.2.1 l hl)⟩
  · simp [Concept.coreClasses, Concept.noBottomObj, Concept.dataPropsOf, Concept.dataRangesOf, Concept.dataLiteralsOf, hnbR]
  · have hfp := foldr_some_props body hnbB
    exact ⟨hfp.1, hfp.2.1, by simp [hfp.2.2.2.2.1], by simp [hfp.2.2.1], by simp [hfp.2.2.2.1]⟩
  · simp only [Problem.lowerBottom, Problem.allConcepts, List.mem_cons, List.mem_append,
      List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hc
    have hdpCore : isCoreDataPropIRI dp = true := by
      have hfromSub : ∃ c0 ∈ p.allConcepts, Concept.dataSome dp (.datatype literalDatatype) = c0.lowerBottom := by
        rcases hc with heq | ((ht | hk) | hca)
        · exact ⟨p.root, List.mem_cons_self .., heq⟩
        · obtain ⟨q, hq, hqm⟩ := ht
          rcases hq with hmap | hextra
          · obtain ⟨q0, hq0, rfl⟩ := hmap
            rcases hqm with heq | heq
            · exact ⟨q0.sub, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inl rfl⟩)), heq⟩
            · exact ⟨q0.sup, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨q0, hq0, Or.inr rfl⟩)), heq⟩
          · obtain ⟨ex, hex, rfl⟩ := hextra
            rcases hqm with heq | heq
            · rcases hex with ((((h1 | h2) | h3) | h4) | h5) | h6
              · obtain ⟨rs, _, hres⟩ := List.mem_filterMap.mp h1
                by_cases hb1 : isBottomObj rs.1.1 = true
                · simp [bottomRule, hb1] at hres
                · by_cases hb2 : isBottomObj rs.2.1 = true
                  · simp only [bottomRule, hb1, hb2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hres
                    rw [← hres] at heq; cases heq
                  · simp [bottomRule, hb1, hb2] at hres
              · obtain ⟨ch, hch, hres⟩ := List.mem_filterMap.mp h2
                exact (hr.noBot.chains ch hch).1 (by
                  by_cases hb1 : ch.body.any (fun x => isBottomObj x.1) = true
                  · simp [bottomChain, hb1] at hres
                  · by_cases hb2 : isBottomObj ch.head = true
                    · exact beq_iff_eq.mp hb2
                    · simp [bottomChain, hb1, hb2] at hres) |>.elim
              · obtain ⟨r, hrM, hres⟩ := List.mem_filterMap.mp h3
                exact (hr.noBot.reflexive r hrM (by
                  by_cases hb1 : isBottomObj r = true
                  · exact beq_iff_eq.mp hb1
                  · simp [forbidWhen, hb1] at hres)).elim
              · obtain ⟨rs, hrsM, hres⟩ := List.mem_filterMap.mp h4
                have hnb2 : isBottomData rs.2 = false :=
                  beq_false_of_ne (bne_iff_ne.mp (Bool.and_eq_true_iff.mp (hr.subData rs hrsM).2).2)
                by_cases hb1 : isBottomData rs.1 = true
                · simp [bottomSubData, hb1] at hres
                · simp [bottomSubData, hb1, hnb2] at hres
              · obtain ⟨e, heM, hres⟩ := List.mem_filterMap.mp h5
                exact (hr.noBot.objAssertions e heM (by
                  by_cases hb1 : isBottomObj e.1 = true
                  · exact beq_iff_eq.mp hb1
                  · simp [forbidWhen, hb1] at hres)).elim
              · obtain ⟨e, heM, hres⟩ := List.mem_filterMap.mp h6
                have hnb1 : isBottomData e.1 = false :=
                  beq_false_of_ne (bne_iff_ne.mp (Bool.and_eq_true_iff.mp (hr.dataAssertions e heM).1).2)
                simp [forbidWhen, hnb1] at hres
            · cases heq
        · obtain ⟨k, hk, heq⟩ := hk
          obtain ⟨k0, hk0, rfl⟩ := hk
          exact ⟨k0.cls, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, (List.mem_filter.mp hk0).1, rfl⟩)), heq.symm⟩
        · obtain ⟨ac, hac, heq⟩ := hca
          obtain ⟨ac0, hac0, rfl⟩ := hac
          exact ⟨ac0.2, by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩), heq.symm⟩
      obtain ⟨c0, hc0, heq⟩ := hfromSub
      have hdp0 : dp ∈ c0.lowerBottom.dataPropsOf := by rw [← heq]; exact List.mem_cons_self ..
      exact (hr.concepts c0 hc0).2.2.1 dp ((concept_lowerBottom_props c0).2.2.2.2.1 dp hdp0).1
    refine ⟨rfl, rfl, fun x hx => by rw [List.mem_singleton.mp hx]; exact hdpCore,
      fun d hd => by rw [List.mem_singleton.mp hd]; decide, by simp [Concept.dataLiteralsOf]⟩

private theorem lowerAllTopRoleAxioms_admitted {q : Problem} (hr : EncodedDataReady q) :
    ∃ rank : Rank, q.lowerAllTopRoleAxioms.isSROIQDWithTop rank = true := by
  have hr0 : EncodedDataReady q.lowerBottom := lowerBottom_eq_of_ready hr
  let q0 := q.lowerBottom
  let q1 := q0.lowerChainAliases
  have hq1_rules : q1.rules = q0.rules := rfl
  have hq1_chainLen : ∀ c ∈ q1.chains, 2 ≤ c.body.length := by
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    simpa [Problem.lowerChainAliases, replaceChainAliases] using hr0.acyclic.1 c0 hc0
  have hq1_sim : q1.checkSimpleWithTop = true := by
    refine checkSimpleWithTop_mono hr0.simple (fun _ h => h) ?_ (fun _ h => h)
    intro c hc _
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    exact ⟨c0, hc0, hr0.acyclic.1 c0 hc0, rfl⟩
  have hq1_simBool : q1.checkSimple = true := (Bool.and_eq_true_iff.mp hq1_sim).1
  -- Case split on whether collapseUnivRoles detects bottomObjectProperty ∈ univRoles q1
  unfold Problem.lowerAllTopRoleAxioms
  change ∃ rank : Rank,
    q1.collapseUnivRoles.lowerTopRoleAxioms.lowerTopChains.lowerChainAliases.isSROIQDWithTop rank = true
  unfold Problem.collapseUnivRoles
  dsimp only
  cases hbotU : (univRoles q1).contains bottomObjectProperty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let U := univRoles q1
    let q2 : Problem :=
      { q1 with
        tbox := q1.tbox.map fun inc => ⟨inc.sub.canonUniv U, inc.sup.canonUniv U⟩
        rules := q1.rules.map fun rs => (canonUnivOriented U rs.1, canonUnivOriented U rs.2)
        chains := q1.chains.map fun c => ⟨c.body.map (canonUnivOriented U), canonUniv U c.head⟩
        chars := {
          reflexive := q1.chars.reflexive.map (canonUniv U)
          irreflexive := q1.chars.irreflexive.map (canonUniv U)
          asymmetric := q1.chars.asymmetric.map (canonUniv U)
          disjoint := q1.chars.disjoint.map fun rs => (canonUnivOriented U rs.1, canonUnivOriented U rs.2) }
        keys := q1.keys.map fun k =>
          { k with cls := k.cls.canonUniv U, objProps := k.objProps.map (canonUnivOriented U) }
        classAssertions := q1.classAssertions.map fun (a, c) => (a, c.canonUniv U)
        objAssertions := q1.objAssertions.map fun (r, a, b) => (canonUniv U r, a, b)
        negObjAssertions := q1.negObjAssertions.map fun (r, a, b) => (canonUniv U r, a, b)
        root := q1.root.canonUniv U }
    let q3 := q2.lowerTopRoleAxioms
    -- Simple roles of q1 are never in U (and never topObjectProperty or bottomObjectProperty)
    have hsimNotU : ∀ r ∈ q1.simpleRoles, r.1 ∉ U := by
      intro r hrM hmemU
      have hsimR := Problem.checkSimple_iff.mp hq1_simBool r hrM
      exact univRoles_nonSimple hq1_chainLen r.1 hmemU r.2 hsimR
    have hsimNotTop : ∀ r ∈ q1.simpleRoles, r.1 ≠ topObjectProperty :=
      fun r hrM hEq => hsimNotU r hrM (hEq ▸ top_mem_univRoles q1)
    have hcuEq : ∀ r : OrientedRole, r.1 ∉ U → canonUnivOriented U r = r := by
      intro r hnu
      rcases r with ⟨n, b⟩
      simp [canonUnivOriented, canonUniv, hnu]
    have hcuNb : ∀ r : IRI, r ≠ bottomObjectProperty → canonUniv U r ≠ bottomObjectProperty := by
      intro r hnb
      unfold canonUniv
      split
      · decide
      · exact hnb
    have hconcCntNotU : ∀ c ∈ q1.allConcepts, ∀ r ∈ c.countedRoles, r.1 ∉ U := by
      intro c hc r hrC
      apply hsimNotU r
      simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
        List.not_mem_nil, or_false] at hc
      simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
      rcases hc with rfl | ((ht | hk) | hca)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hrC))))
      · obtain ⟨inc, hinc, rfl | rfl⟩ := ht
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨inc, hinc, Or.inl hrC⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨inc, hinc, Or.inr hrC⟩))))
      · obtain ⟨k, hk, rfl⟩ := hk
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, hrC⟩)))
      · obtain ⟨ac, hac, rfl⟩ := hca
        exact Or.inl (Or.inl (Or.inr ⟨ac, hac, hrC⟩))
    have hcanonReady : ∀ c ∈ q1.allConcepts, (c.canonUniv U).isSROIQDWithTop = true := by
      intro c hc
      have hc0 : c ∈ q0.allConcepts := hc
      have hrc := hr0.concepts c hc0
      have hci := canonUniv_concept_invariants U c
      have hcntNotU := hconcCntNotU c hc
      apply concept_isSROIQDWithTop_of_ready
      · rw [hci.1]; exact hrc.1
      · exact hci.2.1 hrc.2.1
      · rw [hci.2.2.1]; exact hrc.2.2.1
      · rw [hci.2.2.2.1]; exact hrc.2.2.2.1
      · rw [hci.2.2.2.2.1]; exact hrc.2.2.2.2
      · intro r hrC
        rw [hci.2.2.2.2.2 hcntNotU] at hrC
        intro heq
        exact hcntNotU r hrC (heq ▸ top_mem_univRoles q1)
    -- Rules of q3 are all ordinary rules of q0
    have hq3_rules : ∀ rs ∈ q3.rules, rs ∈ ordinaryRules q0.rules ∧
        isCoreObjPropIRI rs.1.1 = true ∧ isCoreObjPropIRI rs.2.1 = true := by
      intro rs hrs
      have hf := List.mem_filter.mp hrs
      obtain ⟨⟨r, s⟩, hrs0, rfl⟩ := List.mem_map.mp hf.1
      have hsNotTop : canonUniv U s.1 ≠ topObjectProperty := by
        intro he; simp [topDiscardWhen, isTopObj, canonUnivOriented, he] at hf
      have hsNotU : s.1 ∉ U := fun hm => hsNotTop (by simp [canonUniv, hm])
      have hrNotU : r.1 ∉ U := fun hm => hsNotU (univRoles_closed_rules hrs0 hm)
      have hrNotTop : r.1 ≠ topObjectProperty := fun he => hrNotU (he ▸ top_mem_univRoles q1)
      have hsNotTop' : s.1 ≠ topObjectProperty := fun he => hsNotU (he ▸ top_mem_univRoles q1)
      have hnb := hr0.noBot.rules (r, s) hrs0
      have heq1 : canonUnivOriented U r = r := hcuEq r hrNotU
      have heq2 : canonUnivOriented U s = s := hcuEq s hsNotU
      rw [heq1, heq2]
      have hcore1 : isCoreObjPropIRI r.1 = true := by simp [isCoreObjPropIRI, hrNotTop, hnb.1]
      have hcore2 : isCoreObjPropIRI s.1 = true := by simp [isCoreObjPropIRI, hsNotTop', hnb.2]
      exact ⟨List.mem_filter.mpr ⟨hrs0, by simp [hcore1, hcore2]⟩, hcore1, hcore2⟩
    -- Rank on ordinary rules and chains of q0
    obtain ⟨ordRank, hOrdRank⟩ := Sabrina.RoleChains.exists_ranked_iff_acyclicDependencies.mpr hr0.acyclic.2
    -- Every non-top-body chain of q3 is literally in ordinaryChains q0.chains!
    have hq3_chains_core : ∀ c ∈ q3.chains,
        isCoreObjPropIRI c.head = true ∧ 2 ≤ c.body.length ∧
        (∀ r ∈ c.body, isObjPropOrTop r.1 = true) ∧
        (hasTopInBody c = false → c ∈ ordinaryChains q0.chains) ∧
        (∃ c0 ∈ q1.chains, 2 ≤ c0.body.length ∧ c0.head = c.head) := by
      intro c hc
      have hf := List.mem_filter.mp hc
      obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hf.1
      have hhNotTop : canonUniv U c1.head ≠ topObjectProperty := by
        intro he; simp [topDiscardWhen, isTopObj, he] at hf
      have hhNotU : c1.head ∉ U := fun hm => hhNotTop (by simp [canonUniv, hm])
      have hhNotTop' : c1.head ≠ topObjectProperty := fun he => hhNotU (he ▸ top_mem_univRoles q1)
      have hhEq : canonUniv U c1.head = c1.head := by
        simp [canonUniv, hhNotU]
      obtain ⟨c0, hc0, hc1Eq⟩ := List.mem_map.mp hc1
      have hh0 : c1.head = c0.head := by rw [← hc1Eq]; rfl
      have hnb0 := hr0.noBot.chains c0 hc0
      have hhNb : c1.head ≠ bottomObjectProperty := hh0 ▸ hnb0.1
      have hheadCore : isCoreObjPropIRI (canonUniv U c1.head) = true := by
        rw [hhEq]; simp [isCoreObjPropIRI, hhNotTop', hhNb]
      have hbodyLen : 2 ≤ (c1.body.map (canonUnivOriented U)).length := by
        simpa using hq1_chainLen c1 hc1
      have hbodyNb1 : ∀ r ∈ c1.body, r.1 ≠ bottomObjectProperty := by
        intro r hr
        rw [← hc1Eq] at hr
        simp only [replaceChainAliases, List.mem_map] at hr
        obtain ⟨r0, hr0M, rfl⟩ := hr
        unfold replaceAlias
        split
        · exact hnb0.1
        · exact hnb0.2 r0 hr0M
      have hbodyOrTop : ∀ r ∈ c1.body.map (canonUnivOriented U), isObjPropOrTop r.1 = true := by
        intro r hr
        obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr
        by_cases ht : canonUniv U r1.1 = topObjectProperty
        · simp [canonUnivOriented, isObjPropOrTop, ht]
        · simp [canonUnivOriented, isObjPropOrTop, isCoreObjPropIRI, ht, hcuNb r1.1 (hbodyNb1 r1 hr1)]
      refine ⟨hheadCore, hbodyLen, hbodyOrTop, ?_, ⟨c1, hc1, hq1_chainLen c1 hc1, hhEq.symm⟩⟩
      intro hnoTop
      have hnoU1 : ∀ r ∈ c1.body, r.1 ∉ U := by
        intro r hr hmemU
        have htopR : (canonUnivOriented U r).1 = topObjectProperty := by
          simp [canonUnivOriented, canonUniv, hmemU]
        have hany : (c1.body.map (canonUnivOriented U)).any (fun x => x.1 == topObjectProperty) = true :=
          List.any_eq_true.mpr ⟨canonUnivOriented U r, List.mem_map.mpr ⟨r, hr, rfl⟩, beq_iff_eq.mpr htopR⟩
        change (c1.body.map (canonUnivOriented U)).any (fun x => x.1 == topObjectProperty) = false at hnoTop
        rw [hany] at hnoTop; cases hnoTop
      have hmapId : c1.body.map (canonUnivOriented U) = c1.body := by
        simpa only [List.map_id] using List.map_congr_left (g := id) fun r hr => hcuEq r (hnoU1 r hr)
      -- Show c0 has no topObjectProperty in its body (otherwise it would survive alias replacement since c0.head ∉ U)
      have hc0Ord : c0 ∈ ordinaryChains q0.chains := by
        refine List.mem_filter.mpr ⟨hc0, ?_⟩
        simp only [Bool.and_eq_true, List.all_eq_true, isCoreObjPropIRI, bne_iff_ne]
        refine ⟨⟨hh0 ▸ hhNotTop', hnb0.1⟩, fun n hn => ?_⟩
        obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp hn
        refine ⟨?_, hnb0.2 r0 hr0M⟩
        intro htop0
        have hr0U : r0.1 ∈ U := htop0 ▸ top_mem_univRoles q1
        -- Either replaceAlias kept r0 (contradicting hnoU1) or replaced r0 with (c0.head, false) (forcing c0.head ∈ U)
        by_cases hrep : ((roleClosure q0.rules).contains (r0, (c0.head, false)) &&
            (roleClosure q0.rules).contains ((c0.head, false), r0)) = true
        · have hrc1 : (r0, (c0.head, false)) ∈ roleClosure q0.rules :=
            List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hrep).1
          have hreach : Reachable q1.rules r0 (c0.head, false) :=
            Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp (Or.inr hrc1)
          exact hhNotU (hh0.symm ▸ reachable_univ_closed hreach hr0U)
        · have hr0Mem : r0 ∈ c1.body := by
            rw [← hc1Eq]
            simp only [replaceChainAliases, List.mem_map]
            refine ⟨r0, hr0M, ?_⟩
            unfold replaceAlias
            simp only [hrep, Bool.false_eq_true, ↓reduceIte]
          exact hnoU1 r0 hr0Mem hr0U
      -- Since c0 ∈ ordinaryChains q0.chains and ordRank ranks ordinary chains, alias replacement is identity on c0!
      have hc1Eq0 : c1 = c0 := by
        rw [← hc1Eq]
        cases c0 with
        | mk body0 head0 =>
          simp only [replaceChainAliases]
          dsimp only at hh0 hhNotU hc0Ord ⊢
          congr 1
          have hletter : ∀ r ∈ body0, replaceAlias (roleClosure q0.rules) (head0, false) r = r := by
            intro r hr0M
            unfold replaceAlias
            split
            · rename_i hcl
              simp only [Bool.and_eq_true, List.contains_iff_mem] at hcl
              exact Classical.byContradiction fun hne => by
                have hreachBack : Reachable q0.rules (head0, false) r :=
                  Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp (Or.inr hcl.2)
                have hreachFwd : Reachable q0.rules r (head0, false) :=
                  Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp (Or.inr hcl.1)
                rcases reachable_split_ordinary hr0.noBot.rules hreachBack with hordBack | ⟨o, htopR⟩
                · have hle := rank_le_of_reachable_ordinary hOrdRank hordBack
                  obtain ⟨rest, hshape, hlt⟩ := Sabrina.RoleChains.chainShape_iff.mpr (hOrdRank.2 ⟨body0, head0⟩ hc0Ord).2
                  dsimp only at hshape hlt
                  have hmemRest : r ∈ rest := by
                    cases hshape with
                    | plain => exact hr0M
                    | left =>
                      rcases List.mem_cons.mp hr0M with hEq | hm
                      · exact (hne hEq.symm).elim
                      · exact hm
                    | right =>
                      rcases List.mem_append.mp hr0M with hm | hm
                      · exact hm
                      · exact (hne (List.mem_singleton.mp hm).symm).elim
                    | transitive =>
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0M
                      rcases hr0M with hEq | hEq <;> exact (hne hEq.symm).elim
                  exact Nat.not_le_of_lt (hlt r hmemRest) hle
                · have htopHead : Reachable q1.rules (topObjectProperty, o) (head0, false) :=
                    htopR.trans hreachFwd
                  exact hhNotU (hh0.symm ▸ reachable_univ_closed htopHead (top_mem_univRoles q1))
            · rfl
          simpa only [List.map_id] using List.map_congr_left (g := id) hletter
      have hcEq : ({ body := c1.body.map (canonUnivOriented U), head := canonUniv U c1.head } : Chain) = c0 := by
        rw [hmapId, hhEq, hc1Eq0]
      rw [hcEq]
      exact hc0Ord
    -- Show q3 satisfies TopChainInv!
    have hq3_inv : TopChainInv q3 := by
      have hq3_simpleSub : ∀ r ∈ q3.simpleRoles, r ∈ q1.simpleRoles := by
        intro r hr
        simp only [q3, Problem.lowerTopRoleAxioms, Problem.simpleRoles, List.mem_eraseDups,
          List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
          List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
        rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
        · rw [(canonUniv_concept_invariants U q1.root).2.2.2.2.2 (hconcCntNotU q1.root (List.mem_cons_self ..))] at h1
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))
        · obtain ⟨inc, hinc, hrinc⟩ := h2
          rcases hinc with hq2t | hextra
          · obtain ⟨inc0, hinc0, rfl⟩ := List.mem_map.mp hq2t
            rcases hrinc with hsub | hsup
            · rw [(canonUniv_concept_invariants U inc0.sub).2.2.2.2.2
                (hconcCntNotU inc0.sub (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨inc0, hinc0, Or.inl rfl⟩))))] at hsub
              exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨inc0, hinc0, Or.inl hsub⟩))))
            · rw [(canonUniv_concept_invariants U inc0.sup).2.2.2.2.2
                (hconcCntNotU inc0.sup (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨inc0, hinc0, Or.inr rfl⟩))))] at hsup
              exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨inc0, hinc0, Or.inr hsup⟩))))
          · obtain ⟨ex, hex, rfl⟩ := hextra
            rcases hrinc with hrl | hrr
            · rcases hex with ((ha | hb) | hc) | hd
              · obtain ⟨x, _, he⟩ := List.mem_filterMap.mp ha
                by_cases ht : isTopObj x = true <;> simp [topForbidWhen, ht] at he
                subst he; simp [Concept.countedRoles] at hrl
              · obtain ⟨x, _, he⟩ := List.mem_filterMap.mp hb
                by_cases ht : isTopObj x = true <;> simp [topForbidWhen, ht] at he
                subst he; simp [Concept.countedRoles] at hrl
              · obtain ⟨rs, _, he⟩ := List.mem_filterMap.mp hc
                by_cases ht1 : isTopObj rs.1.1 = true
                · by_cases ht2 : isTopObj rs.2.1 = true <;> simp [topDisjRed, ht1, ht2] at he <;> (subst he; simp [Concept.countedRoles] at hrl)
                · by_cases ht2 : isTopObj rs.2.1 = true <;> simp [topDisjRed, ht1, ht2] at he
                  subst he; simp [Concept.countedRoles] at hrl
              · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp hd
                by_cases ht : isTopObj e.1 = true <;> simp [topForbidWhen, ht] at he
                subst he; simp [Concept.countedRoles] at hrl
            · simp [Concept.countedRoles] at hrr
        · obtain ⟨k, hk, hrk⟩ := h3
          obtain ⟨k1, hk1, rfl⟩ := hk
          obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk1
          rw [(canonUniv_concept_invariants U k0.cls).2.2.2.2.2
            (hconcCntNotU k0.cls (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩))))] at hrk
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, hk0, hrk⟩)))
        · obtain ⟨ac, hac, hrac⟩ := h4
          obtain ⟨ac0, hac0, rfl⟩ := List.mem_map.mp hac
          rw [(canonUniv_concept_invariants U ac0.2).2.2.2.2.2
            (hconcCntNotU ac0.2 (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩)))] at hrac
          exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0, hrac⟩))
        · obtain ⟨n, hn, rfl⟩ := h5
          rcases hn with hir | has
          · obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hir).1
            have hnu := hsimNotU (r0, false) (by simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨r0, Or.inl hr0M, rfl⟩))
            have heq : (canonUniv U r0, false) = (r0, false) := hcuEq (r0, false) hnu
            rw [heq]
            exact Or.inl (Or.inr ⟨r0, Or.inl hr0M, rfl⟩)
          · obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp (List.mem_filter.mp has).1
            have hnu := hsimNotU (r0, false) (by simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨r0, Or.inr hr0M, rfl⟩))
            have heq : (canonUniv U r0, false) = (r0, false) := hcuEq (r0, false) hnu
            rw [heq]
            exact Or.inl (Or.inr ⟨r0, Or.inr hr0M, rfl⟩)
        · obtain ⟨rs, hrs, hrm⟩ := h6
          obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hrs).1
          rcases hrm with rfl | rfl
          · have hnu := hsimNotU rs0.1 (by simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr ⟨rs0, hrs0, Or.inl rfl⟩)
            rw [hcuEq rs0.1 hnu]; exact Or.inr ⟨rs0, hrs0, Or.inl rfl⟩
          · have hnu := hsimNotU rs0.2 (by simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr ⟨rs0, hrs0, Or.inr rfl⟩)
            rw [hcuEq rs0.2 hnu]; exact Or.inr ⟨rs0, hrs0, Or.inr rfl⟩
      refine ⟨hcanonReady q1.root (List.mem_cons_self ..), ?_, fun rs hrs => (hq3_rules rs hrs).2,
        fun c hc => ⟨(hq3_chains_core c hc).1, (hq3_chains_core c hc).2.1, (hq3_chains_core c hc).2.2.1⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hr0.subData, hr0.disjointData, hr0.funcData, hr0.dataRanges,
        hr0.dataAssertions, hr0.negDataAssertions, ?_, ?_⟩
      · intro inc hinc
        rcases List.mem_append.mp hinc with hq2t | hextra
        · obtain ⟨inc0, hinc0, rfl⟩ := List.mem_map.mp hq2t
          exact ⟨hcanonReady inc0.sub (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨inc0, hinc0, Or.inl rfl⟩))),
                 hcanonReady inc0.sup (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false]; exact Or.inr (Or.inl (Or.inl ⟨inc0, hinc0, Or.inr rfl⟩)))⟩
        · obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hextra
          refine ⟨?_, rfl⟩
          simp only [List.mem_append] at hex
          rcases hex with ((ha | hb) | hc) | hd
          · obtain ⟨x, _, he⟩ := List.mem_filterMap.mp ha
            by_cases ht : isTopObj x = true <;> simp [topForbidWhen, ht] at he; subst he; rfl
          · obtain ⟨x, _, he⟩ := List.mem_filterMap.mp hb
            by_cases ht : isTopObj x = true <;> simp [topForbidWhen, ht] at he; subst he; rfl
          · obtain ⟨rs, hrs, he⟩ := List.mem_filterMap.mp hc
            obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hrs
            have hnb0 := hr0.noBot.disjoint rs0 hrs0
            by_cases ht1 : isTopObj (canonUniv U rs0.1.1) = true
            · by_cases ht2 : isTopObj (canonUniv U rs0.2.1) = true
              · simp [topDisjRed, canonUnivOriented, ht1, ht2] at he; subst he; rfl
              · simp [topDisjRed, canonUnivOriented, ht1, ht2] at he; subst he
                simp [Concept.isSROIQDWithTop, isObjPropOrTop, isCoreObjPropIRI,
                  hcuNb rs0.2.1 hnb0.2]
                exact (Classical.em _).symm
            · by_cases ht2 : isTopObj (canonUniv U rs0.2.1) = true
              · simp [topDisjRed, canonUnivOriented, ht1, ht2] at he; subst he
                simp [Concept.isSROIQDWithTop, isObjPropOrTop, isCoreObjPropIRI,
                  hcuNb rs0.1.1 hnb0.1]
                exact (Classical.em _).symm
              · simp [topDisjRed, canonUnivOriented, ht1, ht2] at he
          · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp hd
            by_cases ht : isTopObj e.1 = true <;> simp [topForbidWhen, ht] at he; subst he; rfl
      · intro r hr
        have hf := List.mem_filter.mp hr
        obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U r0 ≠ topObjectProperty := fun he => by simp [topDiscardWhen, isTopObj, he] at hf
        simp [isCoreObjPropIRI, hnt, hcuNb r0 (hr0.noBot.reflexive r0 hr0M)]
      · intro r hr
        have hf := List.mem_filter.mp hr
        obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U r0 ≠ topObjectProperty := fun he => by simp [topForbidWhen, isTopObj, he] at hf
        simp [isCoreObjPropIRI, hnt, hcuNb r0 (hr0.noBot.irreflexive r0 hr0M)]
      · intro r hr
        have hf := List.mem_filter.mp hr
        obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U r0 ≠ topObjectProperty := fun he => by simp [topForbidWhen, isTopObj, he] at hf
        simp [isCoreObjPropIRI, hnt, hcuNb r0 (hr0.noBot.asymmetric r0 hr0M)]
      · intro rs hrs
        have hf := List.mem_filter.mp hrs
        obtain ⟨rs0, hrs0, rfl⟩ := List.mem_map.mp hf.1
        have hnb0 := hr0.noBot.disjoint rs0 hrs0
        have hnt1 : canonUniv U rs0.1.1 ≠ topObjectProperty := fun he => by
          by_cases ht2 : canonUniv U rs0.2.1 = topObjectProperty <;>
            simp [topDisjRed, isTopObj, canonUnivOriented, he, ht2] at hf
        have hnt2 : canonUniv U rs0.2.1 ≠ topObjectProperty := fun he => by
          by_cases ht1 : canonUniv U rs0.1.1 = topObjectProperty <;>
            simp [topDisjRed, isTopObj, canonUnivOriented, ht1, he] at hf
        exact ⟨by simp [canonUnivOriented, isCoreObjPropIRI, hnt1, hcuNb rs0.1.1 hnb0.1],
               by simp [canonUnivOriented, isCoreObjPropIRI, hnt2, hcuNb rs0.2.1 hnb0.2]⟩
      · intro ac hac
        obtain ⟨ac0, hac0, rfl⟩ := List.mem_map.mp hac
        exact hcanonReady ac0.2 (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inr ⟨ac0, hac0, rfl⟩))
      · intro rab hrab
        have hf := List.mem_filter.mp hrab
        obtain ⟨rab0, hrab0, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U rab0.1 ≠ topObjectProperty := fun he => by simp [topDiscardWhen, isTopObj, he] at hf
        simp [isCoreObjPropIRI, hnt, hcuNb rab0.1 (hr0.noBot.objAssertions rab0 hrab0)]
      · intro rab hrab
        have hf := List.mem_filter.mp hrab
        obtain ⟨rab0, hrab0, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U rab0.1 ≠ topObjectProperty := fun he => by simp [topForbidWhen, isTopObj, he] at hf
        simp [isCoreObjPropIRI, hnt, hcuNb rab0.1 (hr0.noBot.negObjAssertions rab0 hrab0)]
      · intro k hk
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hk
        obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk1
        refine ⟨hcanonReady k0.cls (by simp only [Problem.allConcepts, List.mem_cons, List.mem_append, List.mem_map]; exact Or.inr (Or.inl (Or.inr ⟨k0, hk0, rfl⟩))),
          fun r hr => ?_, hr0.keysData k0 hk0⟩
        have hf := List.mem_filter.mp hr
        obtain ⟨r0, hr0M, rfl⟩ := List.mem_map.mp hf.1
        have hnt : canonUniv U r0.1 ≠ topObjectProperty := fun he => by simp [isTopObj, canonUnivOriented, he] at hf
        simp [canonUnivOriented, isCoreObjPropIRI, hnt, hcuNb r0.1 (hr0.noBot.keys k0 hk0 r0 hr0M)]
      · exact (Bool.and_eq_true_iff.mp (checkSimpleWithTop_mono hq1_sim
          (fun rs hrs => (List.mem_filter.mp (hq3_rules rs hrs).1).1)
          (fun c hc _ => (hq3_chains_core c hc).2.2.2.2)
          hq3_simpleSub)).1
      · refine ⟨ordRank, fun r s hrs => hOrdRank.1 r s (hq3_rules (r, s) hrs).1, ?_⟩
        intro c hc
        have hf := List.mem_filter.mp hc
        have hnoTop : hasTopInBody c = false := by
          cases ht : hasTopInBody c
          · rfl
          · simp [ht] at hf
        exact hOrdRank.2 c ((hq3_chains_core c hf.1).2.2.2.1 hnoTop)
    -- Apply TopChainInv preservation through lowerTopChains!
    have hq4_inv : TopChainInv q3.lowerTopChains := Problem.lowerTopChains_inv hq3_inv
    have hq4_noTop := Problem.lowerTopChains_noTopInBody q3
    have hfilterEq : (q3.lowerTopChains.chains.filter fun c => !hasTopInBody c) = q3.lowerTopChains.chains :=
      List.filter_eq_self.mpr fun c hc => by simp [hq4_noTop c hc]
    obtain ⟨rank4, hrank4⟩ := hq4_inv.ranked
    rw [hfilterEq] at hrank4
    have haliasEq : q3.lowerTopChains.lowerChainAliases = q3.lowerTopChains :=
      Problem.lowerChainAliases_eq_of_ranked hrank4
    rw [haliasEq]
    refine ⟨rank4, ?_⟩
    simp only [Problem.isSROIQDWithTop, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq4_inv.root, hq4_inv.tbox⟩, hq4_inv.rules⟩, ?_⟩,
      hq4_inv.reflexive⟩, hq4_inv.irreflexive⟩, hq4_inv.asymmetric⟩, hq4_inv.disjoint⟩,
      hq4_inv.classAssertions⟩, hq4_inv.objAssertions⟩, hq4_inv.negObjAssertions⟩,
      fun k hk => ⟨⟨(hq4_inv.keys k hk).1, (hq4_inv.keys k hk).2.1⟩, (hq4_inv.keys k hk).2.2⟩⟩,
      hq4_inv.subData⟩, hq4_inv.disjointData⟩, hq4_inv.funcData⟩, hq4_inv.dataRanges⟩,
      hq4_inv.dataAssertions⟩, hq4_inv.negDataAssertions⟩, hq4_inv.simple⟩,
      Sabrina.RoleChains.checkRegular_iff.mpr hrank4⟩
    intro c hc
    refine ⟨(hq4_inv.chains c hc).1, fun n hn => ?_⟩
    obtain ⟨r, hrM, rfl⟩ := List.mem_map.mp hn
    have hnt : r.1 ≠ topObjectProperty := fun he => by
      have hany : c.body.any (fun x => x.1 == topObjectProperty) = true :=
        List.any_eq_true.mpr ⟨r, hrM, beq_iff_eq.mpr he⟩
      have hntC := hq4_noTop c hc
      change c.body.any (fun x => x.1 == topObjectProperty) = false at hntC
      rw [hany] at hntC; cases hntC
    have hor := (hq4_inv.chains c hc).2.2 r hrM
    simp only [isObjPropOrTop, Bool.or_eq_true, beq_iff_eq] at hor
    exact hor.elim id (fun h => (hnt h).elim)
  · -- bottomObjectProperty ∈ univRoles q1: collapses directly to { root := .bottom }!
    simp only [↓reduceIte]
    refine ⟨fun _ => 0, ?_⟩
    have htr : ({ root := .bottom } : Problem).lowerTopRoleAxioms = { root := .bottom } := rfl
    have htc : ({ root := .bottom } : Problem).lowerTopChains = { root := .bottom } := by
      unfold Problem.lowerTopChains; rfl
    have hla : ({ root := .bottom } : Problem).lowerChainAliases = { root := .bottom } := rfl
    rw [htr, htc, hla]
    decide

private theorem isSROIQDWithTop_change_rank {p : Problem} {r1 r2 : Rank}
    (h1 : p.isSROIQDWithTop r1 = true)
    (h2 : checkRegular r2 p.rules p.chains = true) :
    p.isSROIQDWithTop r2 = true := by
  simp only [Problem.isSROIQDWithTop, Bool.and_eq_true] at h1 ⊢
  exact ⟨h1.1, h2⟩

/-! ### 6. Total combined OWL 2 DL decision theorems (Dedekind-cut `owl:real` and `datatypeMap`) -/

/-- Every `AcyclicOWL2DLInput` is guaranteed to be decided by `decideRealProblem?`
(never returning `none`). -/
theorem decideRealProblem_isSome_of_acyclic {p : Problem} (h : AcyclicOWL2DLInput p) :
    (decideRealProblem? p).isSome = true := by
  have hlbA := lowerBottom_acyclic h
  have hlbNbO := lowerBottom_noBottomObj p
  have hlbNbD := lowerBottom_noBottomData p
  obtain ⟨p1, hp1, hp1A, hp1NbO, hp1CoreDP⟩ := lowerTopData_exists_of_acyclic hlbA hlbNbO hlbNbD
  obtain ⟨q, hq, hqReady⟩ := encodeWiderData_exists_of_core hp1A hp1NbO hp1CoreDP
  obtain ⟨rank0, hrank0⟩ := lowerAllTopRoleAxioms_admitted hqReady
  have hreg0 : Ranked rank0 q.lowerAllTopRoleAxioms.rules q.lowerAllTopRoleAxioms.chains :=
    Sabrina.RoleChains.checkRegular_iff.mp (Bool.and_eq_true_iff.mp hrank0).2
  have hfind : (findRank q.lowerAllTopRoleAxioms.rules q.lowerAllTopRoleAxioms.chains).isSome = true :=
    Sabrina.RoleChains.findRank_iff.mpr ⟨rank0, hreg0⟩
  obtain ⟨rank, hrank⟩ := Option.isSome_iff_exists.mp hfind
  have hadm : q.lowerAllTopRoleAxioms.isSROIQDWithTop rank = true :=
    isSROIQDWithTop_change_rank hrank0
      (Sabrina.RoleChains.checkRegular_iff.mpr (Sabrina.RoleChains.findRank_sound hrank))
  unfold decideRealProblem?
  simp [hp1, hq, hrank, hadm]

theorem decideRealProblem_isSome_of_regular {p : Problem} (h : RegularOWL2DLInput p) :
    (decideRealProblem? p).isSome = true :=
  decideRealProblem_isSome_of_acyclic h.toAcyclic

/-- Total, fuel-free, rank-free decision procedure for the unified acyclic OWL 2 DL
fragment over the Dedekind-cut real datatype map (`realDatatypeMap`). -/
def decideAcyclicOWL2DLReal (p : Problem) (h : AcyclicOWL2DLInput p) : Bool :=
  (decideRealProblem? p).get (decideRealProblem_isSome_of_acyclic h)

theorem decideAcyclicOWL2DLReal_iff {p : Problem} (h : AcyclicOWL2DLInput p) :
    decideAcyclicOWL2DLReal p h = true ↔ p.SatWith realDatatypeMap :=
  decideRealProblem_iff (Option.some_get (decideRealProblem_isSome_of_acyclic h)).symm

/-- Total, fuel-free, rank-free decision procedure for full regular OWL 2 DL
(Stefanoni's head-inverse weak-regularity criterion on the ordinary residual hierarchy)
over the Dedekind-cut real datatype map (`realDatatypeMap`). -/
def decideRegularOWL2DLReal (p : Problem) (h : RegularOWL2DLInput p) : Bool :=
  decideAcyclicOWL2DLReal p h.toAcyclic

theorem decideRegularOWL2DLReal_iff {p : Problem} (h : RegularOWL2DLInput p) :
    decideRegularOWL2DLReal p h = true ↔ p.SatWith realDatatypeMap :=
  decideAcyclicOWL2DLReal_iff h.toAcyclic

theorem decideRealOntology_isSome_of_acyclic {o : Ontology} {defs : Normalize.DatatypeDefs} {p : Problem}
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : AcyclicOWL2DLInput p) :
    (decideRealOntology? o).isSome = true := by
  unfold decideRealOntology?
  simp only [hnorm, Option.bind_some, hroot, h.simple, and_self, ↓reduceIte]
  exact decideRealProblem_isSome_of_acyclic h

theorem decideRealOntology_isSome_of_regular {o : Ontology} {defs : Normalize.DatatypeDefs} {p : Problem}
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : RegularOWL2DLInput p) :
    (decideRealOntology? o).isSome = true :=
  decideRealOntology_isSome_of_acyclic hnorm hroot h.toAcyclic

theorem decideRegularOWL2DLReal_ontology_iff {o : Ontology} {defs : Normalize.DatatypeDefs} {p : Problem}
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : RegularOWL2DLInput p) :
    decideRegularOWL2DLReal p h = true ↔ Satisfiable realDatatypeMap o := by
  have hget := decideRealOntology_iff (Option.some_get (decideRealOntology_isSome_of_regular hnorm hroot h)).symm
  have heq : (decideRealOntology? o).get (decideRealOntology_isSome_of_regular hnorm hroot h) =
      decideRegularOWL2DLReal p h := by
    simp only [decideRegularOWL2DLReal, decideAcyclicOWL2DLReal, decideRealOntology?, hnorm,
      Option.bind_some, hroot, h.simple, and_self, ↓reduceIte]
  exact heq ▸ hget

/-- Total, fuel-free, rank-free decision procedure for full regular OWL 2 DL
over the standard `datatypeMap` (proved via equisatisfiability of `encodeWiderData`
between `datatypeMap` and `realDatatypeMap`). -/
def decideRegularOWL2DL (p : Problem) (h : RegularOWL2DLInput p) : Bool :=
  decideRegularOWL2DLReal p h

theorem decideRegularOWL2DL_iff {p : Problem} (h : RegularOWL2DLInput p) :
    decideRegularOWL2DL p h = true ↔ p.Sat := by
  have hlbA := lowerBottom_acyclic h.toAcyclic
  have hlbNbO := lowerBottom_noBottomObj p
  have hlbNbD := lowerBottom_noBottomData p
  obtain ⟨p1, hp1, hp1A, hp1NbO, hp1CoreDP⟩ := lowerTopData_exists_of_acyclic hlbA hlbNbO hlbNbD
  obtain ⟨q, hq, _⟩ := encodeWiderData_exists_of_core hp1A hp1NbO hp1CoreDP
  have hreal := decideRegularOWL2DLReal_iff h
  have heqSat : p.SatWith realDatatypeMap ↔ p.Sat :=
    (p.lowerBottom_satWith_iff.symm.trans
      ((lowerTopData_real_sat_iff hp1).symm.trans
        ((encodeWiderData_symbolic_real_iff hq).symm.trans
          ((lowerTopData_sat_iff hp1).trans p.lowerBottom_sat_iff))))
  exact hreal.trans heqSat

theorem decideRegularOWL2DL_ontology_iff {o : Ontology} {defs : Normalize.DatatypeDefs} {p : Problem}
    (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : RegularOWL2DLInput p) :
    decideRegularOWL2DL p h = true ↔ Satisfiable datatypeMap o :=
  (decideRegularOWL2DL_iff h).trans
    ((Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)).symm

/-- Every regular OWL 2 DL ontology is also guaranteed to be decided by the live
`decideWithWiderDataRanges?` adapter (never returning `none`). -/
theorem decideWithWiderDataRanges_isSome_of_acyclic {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : AcyclicOWL2DLInput p) :
    (decideWithWiderDataRanges? o).isSome = true := by
  have hreal : (decideWiderProblem? p).isSome = true := decideRealProblem_isSome_of_acyclic h
  have hranked : (decideRankedWithWiderDataRanges? o).isSome = true := by
    unfold decideRankedWithWiderDataRanges?
    simp only [hnorm, Option.bind_some, hroot, h.simple, and_self, ↓reduceIte]
    cases hfast : (findRank p.lowerAllTopRoleAxioms.rules p.lowerAllTopRoleAxioms.chains).bind (fun rank =>
      if h : p.lowerAllTopRoleAxioms.isSROIQDWithTop rank = true then
        Option.some (decideSROIQDWithTopBool h)
      else none) with
    | some b => simp
    | none => simpa using hreal
  cases hr : decideRankedWithWiderDataRanges? o with
  | none => rw [hr] at hranked; cases hranked
  | some b => simp [decideWithWiderDataRanges?, hr]

theorem decideWithWiderDataRanges_isSome_of_regular {o : Ontology} {defs : Normalize.DatatypeDefs}
    {p : Problem} (hnorm : Normalize.normalizeWithDefs o = some (defs, p)) (hroot : p.root = .top)
    (h : RegularOWL2DLInput p) :
    (decideWithWiderDataRanges? o).isSome = true :=
  decideWithWiderDataRanges_isSome_of_acyclic hnorm hroot h.toAcyclic

/-! ### 7. Total four-way query entailment for regular OWL 2 DL -/

/-- Every anonymous-free supported query over a regular OWL 2 DL ontology whose
positive and negated query extensions remain in `AcyclicOWL2DLInput` is guaranteed
to be decided by `decideRealQuery?` (never returning `none`). -/
theorem decideRealQuery_isSome_of_acyclic {o : Ontology} {qAx negAx : Axiom}
    (hneg : negateQueryAxiom qAx = some negAx)
    {defs0 defs1 defs2 : Normalize.DatatypeDefs} {p0 p1 p2 : Problem}
    (hn0 : Normalize.normalizeWithDefs o = some (defs0, p0)) (hr0 : p0.root = .top) (ha0 : AcyclicOWL2DLInput p0)
    (hn1 : Normalize.normalizeWithDefs (qAx :: o) = some (defs1, p1)) (hr1 : p1.root = .top) (ha1 : AcyclicOWL2DLInput p1)
    (hn2 : Normalize.normalizeWithDefs (negAx :: o) = some (defs2, p2)) (hr2 : p2.root = .top) (ha2 : AcyclicOWL2DLInput p2) :
    (decideRealQuery? o qAx).isSome = true := by
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp (decideRealOntology_isSome_of_acyclic hn0 hr0 ha0)
  obtain ⟨b1, hb1⟩ := Option.isSome_iff_exists.mp (decideRealOntology_isSome_of_acyclic hn1 hr1 ha1)
  obtain ⟨b2, hb2⟩ := Option.isSome_iff_exists.mp (decideRealOntology_isSome_of_acyclic hn2 hr2 ha2)
  unfold decideRealQuery? classifyQueryWith
  cases b0 with
  | false => simp [hneg, hb0]
  | true =>
    cases b2 with
    | false => simp [hneg, hb0, hb2]
    | true =>
      cases b1 with
      | true => simp [hneg, hb0, hb1, hb2]
      | false => simp [hneg, hb0, hb1, hb2]

theorem decideRealQuery_isSome_of_regular {o : Ontology} {qAx negAx : Axiom}
    (hneg : negateQueryAxiom qAx = some negAx)
    {defs0 defs1 defs2 : Normalize.DatatypeDefs} {p0 p1 p2 : Problem}
    (hn0 : Normalize.normalizeWithDefs o = some (defs0, p0)) (hr0 : p0.root = .top) (ha0 : RegularOWL2DLInput p0)
    (hn1 : Normalize.normalizeWithDefs (qAx :: o) = some (defs1, p1)) (hr1 : p1.root = .top) (ha1 : RegularOWL2DLInput p1)
    (hn2 : Normalize.normalizeWithDefs (negAx :: o) = some (defs2, p2)) (hr2 : p2.root = .top) (ha2 : RegularOWL2DLInput p2) :
    (decideRealQuery? o qAx).isSome = true :=
  decideRealQuery_isSome_of_acyclic hneg hn0 hr0 ha0.toAcyclic hn1 hr1 ha1.toAcyclic hn2 hr2 ha2.toAcyclic

/-- Total four-way query verdict for regular OWL 2 DL over Dedekind-cut `realDatatypeMap`. -/
def decideRegularOWL2DLQuery {o : Ontology} {qAx negAx : Axiom}
    (hneg : negateQueryAxiom qAx = some negAx)
    {defs0 defs1 defs2 : Normalize.DatatypeDefs} {p0 p1 p2 : Problem}
    (hn0 : Normalize.normalizeWithDefs o = some (defs0, p0)) (hr0 : p0.root = .top) (ha0 : RegularOWL2DLInput p0)
    (hn1 : Normalize.normalizeWithDefs (qAx :: o) = some (defs1, p1)) (hr1 : p1.root = .top) (ha1 : RegularOWL2DLInput p1)
    (hn2 : Normalize.normalizeWithDefs (negAx :: o) = some (defs2, p2)) (hr2 : p2.root = .top) (ha2 : RegularOWL2DLInput p2) :
    Sabrina.ALC.InclusionVerdict :=
  (decideRealQuery? o qAx).get (decideRealQuery_isSome_of_regular hneg hn0 hr0 ha0 hn1 hr1 ha1 hn2 hr2 ha2)

theorem decideRegularOWL2DLQuery_sound {o : Ontology} {qAx negAx : Axiom}
    (hneg : negateQueryAxiom qAx = some negAx)
    {defs0 defs1 defs2 : Normalize.DatatypeDefs} {p0 p1 p2 : Problem}
    (hn0 : Normalize.normalizeWithDefs o = some (defs0, p0)) (hr0 : p0.root = .top) (ha0 : RegularOWL2DLInput p0)
    (hn1 : Normalize.normalizeWithDefs (qAx :: o) = some (defs1, p1)) (hr1 : p1.root = .top) (ha1 : RegularOWL2DLInput p1)
    (hn2 : Normalize.normalizeWithDefs (negAx :: o) = some (defs2, p2)) (hr2 : p2.root = .top) (ha2 : RegularOWL2DLInput p2) :
    queryVerdictClaimWith realDatatypeMap o qAx
      (decideRegularOWL2DLQuery hneg hn0 hr0 ha0 hn1 hr1 ha1 hn2 hr2 ha2) :=
  decideRealQuery_sound (Option.some_get (decideRealQuery_isSome_of_regular hneg hn0 hr0 ha0 hn1 hr1 ha1 hn2 hr2 ha2)).symm

#print axioms RegularOWL2DLHierarchy.toAcyclic
#print axioms RegularObjectInput.toRegularOWL2DLInput
#print axioms checkAcyclicOWL2DLInput_iff
#print axioms decideRealProblem_isSome_of_acyclic
#print axioms decideRealProblem_isSome_of_regular
#print axioms decideAcyclicOWL2DLReal_iff
#print axioms decideRegularOWL2DLReal_iff
#print axioms decideRegularOWL2DLReal_ontology_iff
#print axioms decideRegularOWL2DL_iff
#print axioms decideRegularOWL2DL_ontology_iff
#print axioms decideWithWiderDataRanges_isSome_of_acyclic
#print axioms decideWithWiderDataRanges_isSome_of_regular
#print axioms decideRealQuery_isSome_of_regular
#print axioms decideRegularOWL2DLQuery_sound

end Sabrina.OWL2.RoleHierarchy.Unified
