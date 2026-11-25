import Sabrina.OWL2.SROIQD.Termination.Automata
import Sabrina.OWL2.SROIQD.Termination.DataCSP

/-!
Forest representation, pairwise blocking, finite closure, and saturation
conditions for full cyclic `SROIQ(D)` (TBox, RBox with regular role chains,
inverse roles, qualified number restrictions, nominals, ABoxes, concrete
datatypes, and mixed object+data `HasKey` axioms).
-/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole converse)
open Sabrina.RoleChains (Rank checkRegular)
open Sabrina.OWL2.Datatypes (datatypeMap decodeLiteral)

def Concept.isSROIQ : Concept → Bool
  | .top | .bottom => true
  | .lit a _ => isCoreClassIRI a
  | .nom _ _ => true
  | .self r _ => isCoreObjPropIRI r.1
  | .conj a b | .disj a b => a.isSROIQ && b.isSROIQ
  | .some r c | .all r c | .min _ r c | .max _ r c => isCoreObjPropIRI r.1 && c.isSROIQ
  | _ => false

theorem Concept.isSROIQ_dual (c : Concept) : c.dual.isSROIQ = c.isSROIQ := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQ]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQ]
  | _ => simp_all [Concept.dual, Concept.isSROIQ]

theorem Concept.isSROIQ_implies_isSROIQD {c : Concept} (h : c.isSROIQ = true) :
    c.isSROIQD = true := by
  induction c <;> simp_all [Concept.isSROIQ, Concept.isSROIQD]

/-- Full object-only `SROIQ` fragment: arbitrary TBox, regular role hierarchy
and role chains, simple counted/characteristic roles, nominals, ABox assertions,
and object-property `HasKey` axioms. -/
def Problem.isSROIQ (p : Problem) (rank : Rank) : Bool :=
  p.root.isSROIQ &&
  p.tbox.all (fun q => q.sub.isSROIQ && q.sup.isSROIQ) &&
  p.rules.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.chains.all (fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI) &&
  p.chars.reflexive.all isCoreObjPropIRI &&
  p.chars.irreflexive.all isCoreObjPropIRI &&
  p.chars.asymmetric.all isCoreObjPropIRI &&
  p.chars.disjoint.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.classAssertions.all (fun (_, c) => c.isSROIQ) &&
  p.objAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.negObjAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.keys.all (fun k => k.cls.isSROIQ && k.objProps.all (fun r => isCoreObjPropIRI r.1) && k.dataProps.isEmpty) &&
  p.subData.isEmpty && p.disjointData.isEmpty && p.funcData.isEmpty && p.dataRanges.isEmpty &&
  p.dataAssertions.isEmpty && p.negDataAssertions.isEmpty &&
  p.checkSimple && checkRegular rank p.rules p.chains

/-- Full `SROIQ(D)` fragment including concrete datatypes (`dataSome`, `dataAll`,
`dataValue`, `dataMin`, `dataMax`), global data property axioms (`subData`,
`disjointData`, `funcData`, `dataRanges`), data ABox assertions, and mixed
object + data `HasKey` axioms. -/
def Problem.isSROIQD (p : Problem) (rank : Rank) : Bool :=
  p.root.isSROIQD &&
  p.tbox.all (fun q => q.sub.isSROIQD && q.sup.isSROIQD) &&
  p.rules.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.chains.all (fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI) &&
  p.chars.reflexive.all isCoreObjPropIRI &&
  p.chars.irreflexive.all isCoreObjPropIRI &&
  p.chars.asymmetric.all isCoreObjPropIRI &&
  p.chars.disjoint.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.classAssertions.all (fun (_, c) => c.isSROIQD) &&
  p.objAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.negObjAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.keys.all (fun k => k.cls.isSROIQD && k.objProps.all (fun r => isCoreObjPropIRI r.1) && k.dataProps.all isCoreDataPropIRI) &&
  p.subData.all (fun (r, s) => isCoreDataPropIRI r && isCoreDataPropIRI s) &&
  p.disjointData.all (fun (r, s) => isCoreDataPropIRI r && isCoreDataPropIRI s) &&
  p.funcData.all isCoreDataPropIRI &&
  p.dataRanges.all (fun (r, d) => isCoreDataPropIRI r && d.isSROIQD) &&
  p.dataAssertions.all (fun (r, _, l) => isCoreDataPropIRI r && (decodeLiteral l).isSome) &&
  p.negDataAssertions.all (fun (r, _, l) => isCoreDataPropIRI r && (decodeLiteral l).isSome) &&
  p.checkSimple && checkRegular rank p.rules p.chains

structure Problem.SROIQInput (rank : Rank) (p : Problem) : Prop where
  root : p.root.isSROIQ = true
  tbox : ∀ q ∈ p.tbox, q.sub.isSROIQ = true ∧ q.sup.isSROIQ = true
  rules : ∀ q ∈ p.rules, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  chains : ∀ c ∈ p.chains, isCoreObjPropIRI c.head = true ∧ ∀ r ∈ c.bodyNames, isCoreObjPropIRI r = true
  reflexive : ∀ r ∈ p.chars.reflexive, isCoreObjPropIRI r = true
  irreflexive : ∀ r ∈ p.chars.irreflexive, isCoreObjPropIRI r = true
  asymmetric : ∀ r ∈ p.chars.asymmetric, isCoreObjPropIRI r = true
  disjoint : ∀ q ∈ p.chars.disjoint, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  classAssertions : ∀ ac ∈ p.classAssertions, ac.2.isSROIQ = true
  objAssertions : ∀ rab ∈ p.objAssertions, isCoreObjPropIRI rab.1 = true
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, isCoreObjPropIRI rab.1 = true
  keys : ∀ k ∈ p.keys, k.cls.isSROIQ = true ∧ (∀ r ∈ k.objProps, isCoreObjPropIRI r.1 = true) ∧ k.dataProps = []
  subData : p.subData = []
  disjointData : p.disjointData = []
  funcData : p.funcData = []
  dataRanges : p.dataRanges = []
  dataAssertions : p.dataAssertions = []
  negDataAssertions : p.negDataAssertions = []
  simple : p.checkSimple = true
  regular : checkRegular rank p.rules p.chains = true

structure Problem.SROIQDInput (rank : Rank) (p : Problem) : Prop where
  root : p.root.isSROIQD = true
  tbox : ∀ q ∈ p.tbox, q.sub.isSROIQD = true ∧ q.sup.isSROIQD = true
  rules : ∀ q ∈ p.rules, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  chains : ∀ c ∈ p.chains, isCoreObjPropIRI c.head = true ∧ ∀ r ∈ c.bodyNames, isCoreObjPropIRI r = true
  reflexive : ∀ r ∈ p.chars.reflexive, isCoreObjPropIRI r = true
  irreflexive : ∀ r ∈ p.chars.irreflexive, isCoreObjPropIRI r = true
  asymmetric : ∀ r ∈ p.chars.asymmetric, isCoreObjPropIRI r = true
  disjoint : ∀ q ∈ p.chars.disjoint, isCoreObjPropIRI q.1.1 = true ∧ isCoreObjPropIRI q.2.1 = true
  classAssertions : ∀ ac ∈ p.classAssertions, ac.2.isSROIQD = true
  objAssertions : ∀ rab ∈ p.objAssertions, isCoreObjPropIRI rab.1 = true
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, isCoreObjPropIRI rab.1 = true
  keys : ∀ k ∈ p.keys, k.cls.isSROIQD = true ∧
    (∀ r ∈ k.objProps, isCoreObjPropIRI r.1 = true) ∧
    (∀ dp ∈ k.dataProps, isCoreDataPropIRI dp = true)
  subData : ∀ rs ∈ p.subData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  disjointData : ∀ rs ∈ p.disjointData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  funcData : ∀ dp ∈ p.funcData, isCoreDataPropIRI dp = true
  dataRanges : ∀ rd ∈ p.dataRanges, isCoreDataPropIRI rd.1 = true ∧ rd.2.isSROIQD = true
  dataAssertions : ∀ dal ∈ p.dataAssertions, isCoreDataPropIRI dal.1 = true ∧ (decodeLiteral dal.2.2).isSome = true
  negDataAssertions : ∀ dal ∈ p.negDataAssertions, isCoreDataPropIRI dal.1 = true ∧ (decodeLiteral dal.2.2).isSome = true
  simple : p.checkSimple = true
  regular : checkRegular rank p.rules p.chains = true

theorem Problem.sroiqInput {p : Problem} {rank : Rank} (h : p.isSROIQ rank = true) :
    p.SROIQInput rank := by
  simp only [Problem.isSROIQ, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  grind [Problem.SROIQInput.mk]

theorem Problem.sroiqdInput {p : Problem} {rank : Rank} (h : p.isSROIQD rank = true) :
    p.SROIQDInput rank := by
  simp only [Problem.isSROIQD, Bool.and_eq_true, List.all_eq_true] at h
  grind [Problem.SROIQDInput.mk]

theorem Problem.SROIQInput.toSROIQDInput {p : Problem} {rank : Rank} (hi : p.SROIQInput rank) :
    p.SROIQDInput rank where
  root := Concept.isSROIQ_implies_isSROIQD hi.root
  tbox q hq := ⟨Concept.isSROIQ_implies_isSROIQD (hi.tbox q hq).1,
    Concept.isSROIQ_implies_isSROIQD (hi.tbox q hq).2⟩
  rules := hi.rules
  chains := hi.chains
  reflexive := hi.reflexive
  irreflexive := hi.irreflexive
  asymmetric := hi.asymmetric
  disjoint := hi.disjoint
  classAssertions ac hac := Concept.isSROIQ_implies_isSROIQD (hi.classAssertions ac hac)
  objAssertions := hi.objAssertions
  negObjAssertions := hi.negObjAssertions
  keys k hk := ⟨Concept.isSROIQ_implies_isSROIQD (hi.keys k hk).1, (hi.keys k hk).2.1,
    by rw [(hi.keys k hk).2.2]; simp⟩
  subData := by rw [hi.subData]; simp
  disjointData := by rw [hi.disjointData]; simp
  funcData := by rw [hi.funcData]; simp
  dataRanges := by rw [hi.dataRanges]; simp
  dataAssertions := by rw [hi.dataAssertions]; simp
  negDataAssertions := by rw [hi.negDataAssertions]; simp
  simple := hi.simple
  regular := hi.regular

theorem Problem.isSROIQ_implies_isSROIQD {p : Problem} {rank : Rank}
    (h : p.isSROIQ rank = true) : p.isSROIQD rank = true := by
  have hi := (p.sroiqInput h).toSROIQDInput
  simp only [Problem.isSROIQD, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi.root, ?_⟩, ?_⟩, ?_⟩, hi.reflexive⟩, hi.irreflexive⟩,
    hi.asymmetric⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hi.funcData⟩, ?_⟩, ?_⟩, ?_⟩,
    hi.simple⟩, hi.regular⟩
  · intro q hq; exact hi.tbox q hq
  · intro q hq; exact hi.rules q hq
  · intro c hc; exact hi.chains c hc
  · intro q hq; exact hi.disjoint q hq
  · intro ac hac; exact hi.classAssertions ac hac
  · intro rab hrab; exact hi.objAssertions rab hrab
  · intro rab hrab; exact hi.negObjAssertions rab hrab
  · intro k hk; exact ⟨⟨(hi.keys k hk).1, (hi.keys k hk).2.1⟩, (hi.keys k hk).2.2⟩
  · intro rs hrs; exact hi.subData rs hrs
  · intro rs hrs; exact hi.disjointData rs hrs
  · intro rd hrd; exact hi.dataRanges rd hrd
  · intro dal hdal; exact hi.dataAssertions dal hdal
  · intro dal hdal; exact hi.negDataAssertions dal hdal

namespace Termination

open Sabrina.RoleChains.TransitivePaths (converse_converse)

/-! ### Finite `SROIQ` concept, guard, and role alphabets -/

/-- Seeds for `SROIQ(D)` include all base seeds, universal negated-nominal
constraints for negative object assertions and `HasKey` object properties
(enabling exact NFA guard reasoning even for composite/role-chain properties),
and data value concepts for positive and negative ABox data assertions. -/
def sroiqSeeds (p : Problem) : List Concept :=
  seeds p ++
    p.negObjAssertions.map (fun (r, _, b) => .all (r, false) (.nom b false)) ++
    (p.keys.flatMap (fun k => k.objProps.flatMap fun r =>
      p.nominals.map fun a => .all r (.nom (.named a) false)) ++
     p.dataAssertions.map (fun (r, _, l) => .dataValue r l true) ++
     p.negDataAssertions.map (fun (r, _, l) => .dataValue r l false))

def sroiqClos (p : Problem) : List Concept :=
  (.top :: .bottom :: (sroiqSeeds p).flatMap paired).eraseDups

theorem sroiqClos_nodup (p : Problem) : (sroiqClos p).Nodup := nodup_eraseDups_list _

theorem bottom_mem_sroiqClos (p : Problem) : Concept.bottom ∈ sroiqClos p := by
  simp [sroiqClos]

theorem paired_subset_sroiqClos {p : Problem} {c : Concept} (h : c ∈ sroiqSeeds p) :
    paired c ⊆ sroiqClos p := by
  intro d hd
  simp only [sroiqClos, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
  exact .inr (.inr ⟨c, h, hd⟩)

theorem sroiqSeed_mem_clos {p : Problem} {c : Concept} (h : c ∈ sroiqSeeds p) :
    c ∈ sroiqClos p := paired_subset_sroiqClos h (self_mem_paired c)

theorem sroiqSeed_dual_mem_clos {p : Problem} {c : Concept} (h : c ∈ sroiqSeeds p) :
    c.dual ∈ sroiqClos p := paired_subset_sroiqClos h (dual_mem_paired c)

theorem sroiqClos_operands {p : Problem} {c d : Concept} (hc : c ∈ sroiqClos p)
    (hd : d ∈ operands c) : d ∈ sroiqClos p := by
  simp only [sroiqClos, List.mem_eraseDups, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | ⟨a, ha, hc⟩
  · simp [operands] at hd
  · simp [operands] at hd
  · rcases paired_operands hc hd with rfl | h
    · exact bottom_mem_sroiqClos p
    · exact paired_subset_sroiqClos ha h

theorem base_seed_mem_sroiqSeeds {p : Problem} {c : Concept} (h : c ∈ seeds p) :
    c ∈ sroiqSeeds p :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem paired_isSROIQD {c d : Concept} (hc : c.isSROIQD = true) (hd : d ∈ paired c) :
    d.isSROIQD = true := by
  induction c with
  | conj a b ia ib | disj a b ia ib =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    simp only [paired, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | ha) | hb
    · exact Bool.and_eq_true_iff.mpr hc
    · rw [Concept.isSROIQD_dual]; exact Bool.and_eq_true_iff.mpr hc
    · exact ia hc.1 ha
    · exact ib hc.2 hb
  | some r a ia | all r a ia | min _ r a ia | max _ r a ia =>
    simp only [Concept.isSROIQD, Bool.and_eq_true] at hc
    simp only [paired, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | rfl) | ha
    · exact Bool.and_eq_true_iff.mpr hc
    · rw [Concept.isSROIQD_dual]; exact Bool.and_eq_true_iff.mpr hc
    · exact ia hc.2 ha
  | _ =>
    simp only [paired, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hc
    · rw [Concept.isSROIQD_dual]; exact hc

theorem sroiqSeeds_isSROIQD {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    {c : Concept} (hc : c ∈ sroiqSeeds p) : c.isSROIQD = true := by
  simp only [sroiqSeeds, seeds, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.mem_map] at hc
  rcases hc with (((((rfl | ⟨q, hq, hq'⟩) | ⟨ac, hac, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨a, _, rfl⟩) |
      ⟨⟨r, a, b⟩, hrab, rfl⟩) |
      ((⟨k, hk, r, hr, a, _, rfl⟩ | ⟨⟨dp, a, l⟩, hdal, rfl⟩) | ⟨⟨dp, a, l⟩, hndal, rfl⟩)
  · exact hi.root
  · rcases hq' with rfl | rfl | hnil
    · exact (hi.tbox q hq).1
    · exact (hi.tbox q hq).2
    · cases hnil
  · exact hi.classAssertions ac hac
  · exact (hi.keys k hk).1
  · rfl
  · simp [Concept.isSROIQD, hi.negObjAssertions (r, a, b) hrab]
  · simp [Concept.isSROIQD, (hi.keys k hk).2.1 r hr]
  · simp [Concept.isSROIQD, hi.dataAssertions (dp, a, l) hdal]
  · simp [Concept.isSROIQD, hi.negDataAssertions (dp, a, l) hndal]

theorem sroiqClos_isSROIQD {rank : Rank} {p : Problem} (hi : p.SROIQDInput rank)
    {c : Concept} (hc : c ∈ sroiqClos p) : c.isSROIQD = true := by
  simp only [sroiqClos, List.mem_eraseDups, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | ⟨s, hs, hcs⟩
  · rfl
  · rfl
  · exact paired_isSROIQD (sroiqSeeds_isSROIQD hi hs) hcs

def sroiqGuards (rank : Rank) (p : Problem) : List Guard :=
  ((sroiqClos p).flatMap fun
    | .all r c => guardStates rank p r c
    | _ => []).eraseDups

theorem sroiq_initial_guard_mem {rank : Rank} {p : Problem} {r : OrientedRole} {c : Concept}
    (h : .all r c ∈ sroiqClos p) :
    (⟨roleLanguage rank p r, c⟩ : Guard) ∈ sroiqGuards rank p := by
  simp only [sroiqGuards, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.all r c, h, List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩⟩

theorem sroiq_guards_closed {rank : Rank} {p : Problem} {g : Guard}
    (hg : g ∈ sroiqGuards rank p) (r : OrientedRole) :
    g.advance r ⊆ sroiqGuards rank p := by
  simp only [sroiqGuards, List.mem_eraseDups, List.mem_flatMap] at hg
  obtain ⟨c, hc, hg⟩ := hg
  cases c <;> try (simp at hg; done)
  rename_i role filler
  obtain ⟨state, hs, rfl⟩ := List.mem_map.mp hg
  intro q hq
  obtain ⟨qState, hnext, rfl⟩ := List.mem_map.mp hq
  simp only [sroiqGuards, List.mem_eraseDups, List.mem_flatMap]
  refine ⟨.all role filler, hc, List.mem_map.mpr ⟨qState, List.mem_cons_of_mem _ ?_, rfl⟩⟩
  rcases List.mem_cons.mp hs with rfl | h
  · exact (roleLanguage rank p role).derivative_subset r hnext
  · exact Sabrina.RoleChains.PathRegex.residuals_closed h r hnext

theorem sroiq_guard_filler_mem {rank : Rank} {p : Problem} {g : Guard}
    (hg : g ∈ sroiqGuards rank p) : g.filler ∈ sroiqClos p := by
  simp only [sroiqGuards, List.mem_eraseDups, List.mem_flatMap] at hg
  obtain ⟨c, hc, hg⟩ := hg
  cases c <;> try (simp at hg; done)
  rename_i role filler
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hg
  exact sroiqClos_operands hc (by simp [operands])

def sroiqConceptRoles : Concept → List IRI
  | .some r _ | .all r _ | .min _ r _ | .max _ r _ | .self r _ => [r.1]
  | _ => []

def sroiqRoleNames (p : Problem) : List IRI :=
  ((sroiqClos p).flatMap sroiqConceptRoles ++
    p.rules.flatMap (fun (r, s) => [r.1, s.1]) ++
    p.chains.flatMap (fun c => c.head :: c.bodyNames) ++
    p.chars.reflexive ++ p.chars.irreflexive ++ p.chars.asymmetric ++
    p.chars.disjoint.flatMap (fun (r, s) => [r.1, s.1]) ++
    p.objAssertions.map Prod.fst ++
    p.negObjAssertions.map Prod.fst ++
    p.keys.flatMap (fun k => k.objProps.map Prod.fst)).eraseDups

def sroiqConceptDataProps : Concept → List IRI
  | .dataSome dp _ | .dataAll dp _ | .dataValue dp _ _ | .dataMin _ dp _ | .dataMax _ dp _ => [dp]
  | _ => []

def sroiqDataProps (p : Problem) : List IRI :=
  ((sroiqClos p).flatMap sroiqConceptDataProps ++
    p.subData.flatMap (fun (r, s) => [r, s]) ++
    p.disjointData.flatMap (fun (r, s) => [r, s]) ++
    p.funcData ++
    p.dataRanges.map Prod.fst ++
    p.dataAssertions.map Prod.fst ++
    p.negDataAssertions.map Prod.fst ++
    p.keys.flatMap KeyAxiom.dataProps).eraseDups

theorem key_dataProp_mem_sroiqDataProps {p : Problem} {k : KeyAxiom} (hk : k ∈ p.keys)
    {dp : IRI} (hdp : dp ∈ k.dataProps) : dp ∈ sroiqDataProps p := by
  simp only [sroiqDataProps, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  exact .inr ⟨k, hk, hdp⟩

def sroiqAlphabet (rank : Rank) (p : Problem) : List (Concept ⊕ Guard) :=
  (sroiqClos p).map Sum.inl ++ (sroiqGuards rank p).map Sum.inr

/-- Pairwise-blocking depth horizon for `SROIQ` (depends only on `sroiqClos`,
`sroiqGuards`, and `sroiqRoleNames`, never on the dynamic number of roots). -/
def sroiqMaxDepth (rank : Rank) (p : Problem) : Nat :=
  2 ^ (2 * (sroiqAlphabet rank p).length + 2 * (sroiqRoleNames p).length)

/-! ### Nominal-rooted blocked forest -/

/-- A finite forest of rooted trees in parent-before-child index order.
- Root nodes (`isRoot x = true`) represent the designated root `0`, named/anonymous
  ABox individuals (nominal level `0`), and NN-rule-generated nominal nodes
  (nominal level `≥ 1`). Root nodes are never blocked and may have arbitrary
  directed edges (`rootEdges`) between distinct roots.
- Blockable nodes (`isRoot x = false`) form rooted trees hanging off root nodes.
  Each blockable node stores its tree edge to `parent x` (`down`/`up`), its
  self-loops (`loops`), and any non-child edges to root nodes (`toRoot`). -/
structure BlockedForest where
  size : Nat
  isRoot : Fin (size + 1) → Bool
  root0 : isRoot 0 = true
  nomLevel : Fin (size + 1) → Nat
  parent : Fin (size + 1) → Fin (size + 1)
  parent_lt : ∀ x, isRoot x = false → (parent x).val < x.val
  labels : Fin (size + 1) → List Concept
  guardLabels : Fin (size + 1) → List Guard
  down : Fin (size + 1) → List IRI
  up : Fin (size + 1) → List IRI
  loops : Fin (size + 1) → List IRI
  rootEdges : List (IRI × Fin (size + 1) × Fin (size + 1))
  rootEdges_valid : ∀ e ∈ rootEdges, isRoot e.2.1 = true ∧ isRoot e.2.2 = true ∧ e.2.1 ≠ e.2.2
  toRoot : Fin (size + 1) → List (OrientedRole × Fin (size + 1))
  toRoot_valid : ∀ x e, e ∈ toRoot x → isRoot x = false ∧ isRoot e.2 = true ∧ parent x ≠ e.2
  noms : List (IRI × Fin (size + 1))
  noms_valid : ∀ q ∈ noms, isRoot q.2 = true
  anons : List ((String × String) × Fin (size + 1))
  anons_valid : ∀ q ∈ anons, isRoot q.2 = true
  unequal : List (Fin (size + 1) × Fin (size + 1))
  nnBounds : List (Fin (size + 1) × OrientedRole × Concept × List (Fin (size + 1)))
  nnBounds_valid : ∀ entry ∈ nnBounds,
    isRoot entry.1 = true ∧ ∀ o ∈ entry.2.2.2, isRoot o = true ∧ nomLevel o ≤ nomLevel entry.1 + 1
  blockedBy : Fin (size + 1) → Option (Fin (size + 1))
  keyDisjoint : List (Fin (size + 1) × Fin (size + 1) × IRI) := []
  keyDisjoint_valid : ∀ e ∈ keyDisjoint, isRoot e.1 = true ∧ isRoot e.2.1 = true := by
    intro _ h; cases h

namespace BlockedForest

abbrev Node (b : BlockedForest) := Fin (b.size + 1)

def Child (b : BlockedForest) (x y : b.Node) : Prop :=
  b.isRoot y = false ∧ b.parent y = x

theorem child_lt {b : BlockedForest} {x y : b.Node} (h : b.Child x y) : x.val < y.val :=
  h.2 ▸ b.parent_lt y h.1

theorem child_not_root {b : BlockedForest} {x y : b.Node} (h : b.Child x y) : b.isRoot y = false :=
  h.1

inductive Anc (b : BlockedForest) : b.Node → b.Node → Prop where
  | parent {x y} : b.Child x y → Anc b x y
  | step {a x y} : Anc b a x → b.Child x y → Anc b a y

theorem Anc.lt {b : BlockedForest} {x y : b.Node} (h : b.Anc x y) : x.val < y.val := by
  induction h with
  | parent h => exact child_lt h
  | step _ h ih => exact Nat.lt_trans ih (child_lt h)

theorem Anc.not_root_right {b : BlockedForest} {x y : b.Node} (h : b.Anc x y) :
    b.isRoot y = false := by
  cases h with
  | parent hc => exact hc.1
  | step _ hc => exact hc.1

theorem Anc.child_iff {b : BlockedForest} {a x y : b.Node} (h : b.Child x y) :
    b.Anc a y ↔ a = x ∨ b.Anc a x := by
  constructor
  · intro ha
    cases ha with
    | parent hv => exact .inl (hv.2.symm.trans h.2)
    | step hu hv => exact .inr (hv.2.symm.trans h.2 ▸ hu)
  · rintro (rfl | ha)
    · exact .parent h
    · exact .step ha h

theorem Anc.trans {b : BlockedForest} {x y z : b.Node} (h : b.Anc x y) (h' : b.Anc y z) :
    b.Anc x z := by
  induction h' with
  | parent hc => exact .step h hc
  | step _ hc ih => exact .step ih hc

/-- Strict ancestors of `x` up to its tree root (empty for root nodes). -/
def ancestors (b : BlockedForest) (x : b.Node) : List b.Node :=
  if _h : b.isRoot x = true then [] else b.parent x :: b.ancestors (b.parent x)
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

theorem mem_ancestors {b : BlockedForest} {x a : b.Node} :
    a ∈ b.ancestors x ↔ b.Anc a x := by
  rw [ancestors]
  split
  · rename_i hr
    exact ⟨fun h => (List.not_mem_nil h).elim, fun h => by
      have hf := h.not_root_right; rw [hr] at hf; cases hf⟩
  · rename_i hnr
    have hf : b.isRoot x = false := Bool.eq_false_iff.mpr hnr
    exact List.mem_cons.trans
      ((or_congr Iff.rfl (mem_ancestors (x := b.parent x))).trans
        (Anc.child_iff ⟨hf, rfl⟩).symm)
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

def depth (b : BlockedForest) (x : b.Node) : Nat := (b.ancestors x).length

theorem depth_root {b : BlockedForest} {x : b.Node} (hr : b.isRoot x = true) :
    b.depth x = 0 := by
  unfold depth; rw [ancestors, dite_eq_left hr]; rfl

theorem depth_child {b : BlockedForest} {x y : b.Node} (h : b.Child x y) :
    b.depth y = b.depth x + 1 := by
  unfold depth; rw [ancestors]
  have hnr : ¬ (b.isRoot y = true) := by simp [h.1]
  rw [dite_eq_right hnr, h.2]
  rfl

theorem Anc.depth_lt {b : BlockedForest} {a x : b.Node} (h : b.Anc a x) :
    b.depth a < b.depth x := by
  induction h with
  | parent hc => rw [depth_child hc]; omega
  | step _ hc ih => rw [depth_child hc]; omega

theorem depth_eq_zero_iff {b : BlockedForest} {x : b.Node} :
    b.depth x = 0 ↔ b.isRoot x = true := by
  cases hr : b.isRoot x with
  | true => exact ⟨fun _ => rfl, fun _ => depth_root hr⟩
  | false =>
    have hc : b.Child (b.parent x) x := ⟨hr, rfl⟩
    rw [depth_child hc]
    simp

/-! ### Blocking predicates -/

def DirectlyBlocked (b : BlockedForest) (x : b.Node) : Prop := (b.blockedBy x).isSome

def IndirectlyBlocked (b : BlockedForest) (x : b.Node) : Prop :=
  ∃ a, b.Anc a x ∧ b.DirectlyBlocked a

def Unblocked (b : BlockedForest) (x : b.Node) : Prop :=
  b.blockedBy x = none ∧ ¬ b.IndirectlyBlocked x

def target (b : BlockedForest) (x : b.Node) : b.Node := (b.blockedBy x).getD x

/-! ### Disjoint edge geometry -/

def Down (b : BlockedForest) (r : OrientedRole) (y : b.Node) : Prop :=
  r.1 ∈ if r.2 then b.up y else b.down y

def RootEdge (b : BlockedForest) (r : OrientedRole) (x y : b.Node) : Prop :=
  if r.2 then (r.1, y, x) ∈ b.rootEdges else (r.1, x, y) ∈ b.rootEdges

def Edge (b : BlockedForest) (r : OrientedRole) (x y : b.Node) : Prop :=
  (x = y ∧ r.1 ∈ b.loops x) ∨
  (b.isRoot x = true ∧ b.isRoot y = true ∧ b.RootEdge r x y) ∨
  (b.Child x y ∧ b.Down r y) ∨
  (b.Child y x ∧ b.Down (converse r) x) ∨
  (r, y) ∈ b.toRoot x ∨
  (converse r, x) ∈ b.toRoot y

theorem rootEdge_converse (b : BlockedForest) (r : OrientedRole) (x y : b.Node) :
    b.RootEdge (converse r) y x ↔ b.RootEdge r x y := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

theorem edge_converse (b : BlockedForest) (r : OrientedRole) (x y : b.Node) :
    b.Edge (converse r) y x ↔ b.Edge r x y := by
  simp only [Edge, converse_converse, rootEdge_converse]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨hy, hx, h⟩ | h | h | h | h)
    · exact .inl ⟨rfl, h⟩
    · exact .inr (.inl ⟨hx, hy, h⟩)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inr (.inr h))))
    · exact .inr (.inr (.inr (.inr (.inl h))))
  · rintro (⟨rfl, h⟩ | ⟨hx, hy, h⟩ | h | h | h | h)
    · exact .inl ⟨rfl, h⟩
    · exact .inr (.inl ⟨hy, hx, h⟩)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inr (.inr h))))
    · exact .inr (.inr (.inr (.inr (.inl h))))

theorem edge_loop_iff (b : BlockedForest) (r : OrientedRole) (x : b.Node) :
    b.Edge r x x ↔ r.1 ∈ b.loops x := by
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | h)
    · exact h
    · exfalso
      rcases r with ⟨r, _ | _⟩
      · exact (b.rootEdges_valid _ h).2.2 rfl
      · exact (b.rootEdges_valid _ h).2.2 rfl
    · exact (Nat.lt_irrefl _ (child_lt h)).elim
    · exact (Nat.lt_irrefl _ (child_lt h)).elim
    · have ⟨h1, h2, _⟩ := b.toRoot_valid x _ h
      rw [h1] at h2; cases h2
    · have ⟨h1, h2, _⟩ := b.toRoot_valid x _ h
      rw [h1] at h2; cases h2
  · exact fun h => .inl ⟨rfl, h⟩

theorem edge_child_iff {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (h : b.Child x y) : b.Edge r x y ↔ b.Down r y := by
  have hlt := child_lt h
  constructor
  · rintro (⟨rfl, _⟩ | ⟨_, hy, _⟩ | ⟨_, hd⟩ | ⟨hrev, _⟩ | htr | htr)
    · exact (Nat.lt_irrefl _ hlt).elim
    · rw [h.1] at hy; cases hy
    · exact hd
    · exact (Nat.lt_asymm hlt (child_lt hrev)).elim
    · have ⟨_, hy, _⟩ := b.toRoot_valid x _ htr
      rw [h.1] at hy; cases hy
    · exact ((b.toRoot_valid y _ htr).2.2 h.2).elim
  · exact fun hd => .inr (.inr (.inl ⟨h, hd⟩))

theorem edge_root_iff {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (hx : b.isRoot x = true) (hy : b.isRoot y = true) (hne : x ≠ y) :
    b.Edge r x y ↔ b.RootEdge r x y := by
  constructor
  · rintro (⟨heq, _⟩ | ⟨_, _, hre⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr)
    · exact (hne heq).elim
    · exact hre
    · rw [hc.1] at hy; cases hy
    · rw [hc.1] at hx; cases hx
    · have h1 := (b.toRoot_valid x _ htr).1; rw [h1] at hx; cases hx
    · have h1 := (b.toRoot_valid y _ htr).1; rw [h1] at hy; cases hy
  · exact fun hre => .inr (.inl ⟨hx, hy, hre⟩)

theorem edge_toRoot_iff {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (hx : b.isRoot x = false) (hy : b.isRoot y = true) (hnp : b.parent x ≠ y) :
    b.Edge r x y ↔ (r, y) ∈ b.toRoot x := by
  constructor
  · rintro (⟨rfl, _⟩ | ⟨hxr, _, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr)
    · rw [hx] at hy; cases hy
    · rw [hx] at hxr; cases hxr
    · rw [hc.1] at hy; cases hy
    · exact (hnp hc.2).elim
    · exact htr
    · have h1 := (b.toRoot_valid y _ htr).1; rw [h1] at hy; cases hy
  · exact fun htr => .inr (.inr (.inr (.inr (.inl htr))))

/-! ### Pairwise blocking and validity -/

structure PairMatch (b : BlockedForest) (x y : b.Node) : Prop where
  parentLabels : ∀ c, c ∈ b.labels (b.parent x) ↔ c ∈ b.labels (b.parent y)
  labels : ∀ c, c ∈ b.labels x ↔ c ∈ b.labels y
  parentGuards : ∀ g, g ∈ b.guardLabels (b.parent x) ↔ g ∈ b.guardLabels (b.parent y)
  guards : ∀ g, g ∈ b.guardLabels x ↔ g ∈ b.guardLabels y
  roles : ∀ r, b.Down r x ↔ b.Down r y

structure BlockingValid (b : BlockedForest) : Prop where
  blocker : ∀ x y, b.blockedBy x = some y →
    b.Anc y x ∧ b.isRoot y = false ∧ b.Unblocked y ∧ ¬ b.IndirectlyBlocked x ∧ b.PairMatch x y

theorem root_unblocked {b : BlockedForest} (hw : b.BlockingValid) {x : b.Node}
    (hr : b.isRoot x = true) : b.Unblocked x := by
  constructor
  · cases e : b.blockedBy x with
    | none => rfl
    | some y =>
      have hf := (hw.blocker x y e).1.not_root_right
      rw [hr] at hf; cases hf
  · rintro ⟨a, ha, _⟩
    have hf := ha.not_root_right
    rw [hr] at hf; cases hf

theorem child_of_root_unblocked {b : BlockedForest} (hw : b.BlockingValid) {r c : b.Node}
    (hr : b.isRoot r = true) (hc : b.Child r c) : b.Unblocked c := by
  have noBlockAnc : ∀ a, b.Anc a c → b.isRoot a = true := by
    intro a ha
    rcases (Anc.child_iff hc).mp ha with rfl | h
    · exact hr
    · have hf := h.not_root_right; rw [hr] at hf; cases hf
  constructor
  · cases e : b.blockedBy c with
    | none => rfl
    | some y =>
      have ⟨hanc, hnr, _⟩ := hw.blocker c y e
      have ht := noBlockAnc y hanc
      rw [hnr] at ht; cases ht
  · rintro ⟨a, ha, hdb⟩
    have ht := noBlockAnc a ha
    have hu := root_unblocked hw ht
    simp [DirectlyBlocked, hu.1] at hdb

theorem target_of_unblocked {b : BlockedForest} {x : b.Node} (h : b.Unblocked x) :
    b.target x = x := by simp [target, h.1]

theorem target_match {b : BlockedForest} {x : b.Node} (hw : b.BlockingValid) :
    b.PairMatch x (b.target x) := by
  cases e : b.blockedBy x with
  | none =>
    simp only [target, e, Option.getD_none]
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | some y => simpa [target, e] using (hw.blocker x y e).2.2.2.2

theorem target_not_root {b : BlockedForest} (hw : b.BlockingValid) {x : b.Node}
    (hx : b.isRoot x = false) : b.isRoot (b.target x) = false := by
  cases e : b.blockedBy x with
  | none => simpa [target, e] using hx
  | some y => simpa [target, e] using (hw.blocker x y e).2.1

theorem child_target_unblocked {b : BlockedForest} (hw : b.BlockingValid) {x y : b.Node}
    (hx : b.Unblocked x) (hy : b.Child x y) : b.Unblocked (b.target y) := by
  cases e : b.blockedBy y with
  | some z => simpa [target, e] using (hw.blocker y z e).2.2.1
  | none =>
    rw [show b.target y = y by simp [target, e]]
    refine ⟨e, ?_⟩
    rintro ⟨a, ha, hb⟩
    rcases (Anc.child_iff hy).mp ha with rfl | h
    · simp [DirectlyBlocked, hx.1] at hb
    · exact hx.2 ⟨a, h, hb⟩

/-! ### Individual lookup, semantics, and alphabet bounds -/

def indNode (b : BlockedForest) : Individual → Option b.Node
  | .named a => b.noms.lookup a
  | .anonymous doc lid => b.anons.lookup (doc, lid)

def isNamedRoot (b : BlockedForest) (x : b.Node) : Bool :=
  b.noms.any (fun q => q.2 == x)

def BoundTo (b : BlockedForest) (ind : Individual) (x : b.Node) : Prop :=
  match ind with
  | .named a => (a, x) ∈ b.noms
  | .anonymous doc lid => ((doc, lid), x) ∈ b.anons

theorem BoundTo.isRoot {b : BlockedForest} {ind : Individual} {x : b.Node}
    (h : b.BoundTo ind x) : b.isRoot x = true := by
  cases ind with
  | named a => exact b.noms_valid (a, x) h
  | anonymous doc lid => exact b.anons_valid ((doc, lid), x) h

structure BindingsValid (b : BlockedForest) (p : Problem) : Prop where
  nomComplete : ∀ a ∈ p.nominals, ∃ r, (a, r) ∈ b.noms
  anonComplete : ∀ k ∈ p.anons, ∃ r, (k, r) ∈ b.anons
  nomFunctional : ∀ a r₁ r₂, (a, r₁) ∈ b.noms → (a, r₂) ∈ b.noms → r₁ = r₂
  anonFunctional : ∀ k r₁ r₂, (k, r₁) ∈ b.anons → (k, r₂) ∈ b.anons → r₁ = r₂

theorem BindingsValid.ind_unique {b : BlockedForest} {p : Problem} (hb : b.BindingsValid p)
    {ind : Individual} {r₁ r₂ : b.Node} (h1 : b.BoundTo ind r₁) (h2 : b.BoundTo ind r₂) :
    r₁ = r₂ := by
  cases ind with
  | named a => exact hb.nomFunctional a r₁ r₂ h1 h2
  | anonymous doc lid => exact hb.anonFunctional (doc, lid) r₁ r₂ h1 h2

structure Realizes (b : BlockedForest) (i : Interpretation datatypeMap)
    (env : b.Node → i.Object) : Prop where
  labels : ∀ x c, c ∈ b.labels x → holds i (env x) c
  edges : ∀ r x y, b.Edge r x y → holdsOriented i r (env x) (env y)
  guards : ∀ x g, g ∈ b.guardLabels x → g.Holds i (env x)
  unequal : ∀ x y, (x, y) ∈ b.unequal → env x ≠ env y
  noms : ∀ a x, (a, x) ∈ b.noms → env x = i.individuals (.named a)
  anons : ∀ k x, (k, x) ∈ b.anons → env x = i.individuals (.anonymous k.1 k.2)
  nnBounds : ∀ entry ∈ b.nnBounds, ∀ z : i.Object,
    holdsOriented i entry.2.1 (env entry.1) z → holds i z entry.2.2.1 →
      ∃ o ∈ entry.2.2.2, z = env o
  keyDisjoint : ∀ e ∈ b.keyDisjoint, ∀ y : i.Data,
    ¬ (i.dataProperties e.2.2 (env e.1) y ∧ i.dataProperties e.2.2 (env e.2.1) y)

def Sat (b : BlockedForest) (p : Problem) : Prop :=
  ∃ i : Interpretation datatypeMap, p.Models i ∧ ∃ env, b.Realizes i env

def envNat (b : BlockedForest) {α : Type} (env : b.Node → α) (k : Nat) : α :=
  if h : k < b.size + 1 then env ⟨k, h⟩ else env 0

theorem envNat_val (b : BlockedForest) {α : Type} (env : b.Node → α) (x : b.Node) :
    b.envNat env x.val = env x := by
  unfold envNat; rw [dite_eq_left x.isLt]

def rootSubjects (b : BlockedForest) : List (Nat × List Concept) :=
  ((List.finRange (b.size + 1)).filter b.isRoot).map fun r => (r.val, b.labels r)

theorem mem_rootSubjects_of_isRoot {b : BlockedForest} {r : b.Node} (hr : b.isRoot r = true) :
    (r.val, b.labels r) ∈ b.rootSubjects :=
  List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨List.mem_finRange r, hr⟩, rfl⟩

def rootDataCSP (b : BlockedForest) (p : Problem) : DataCSP :=
  mkSubjectsDataCSP p b.rootSubjects (b.keyDisjoint.map fun (r₁, r₂, dp) => (r₁.val, r₂.val, dp))

def nodeDataCSP (b : BlockedForest) (p : Problem) (x : b.Node) : DataCSP :=
  mkSubjectsDataCSP p [(x.val, b.labels x)] []

def LabelsWithin (b : BlockedForest) (p : Problem) : Prop :=
  ∀ x, b.labels x ⊆ sroiqClos p

def GuardsWithin (b : BlockedForest) (rank : Rank) (p : Problem) : Prop :=
  ∀ x, b.guardLabels x ⊆ sroiqGuards rank p

def RolesWithin (b : BlockedForest) (p : Problem) : Prop :=
  (∀ x, b.down x ⊆ sroiqRoleNames p ∧ b.up x ⊆ sroiqRoleNames p ∧ b.loops x ⊆ sroiqRoleNames p) ∧
  (∀ e ∈ b.rootEdges, e.1 ∈ sroiqRoleNames p) ∧
  (∀ x e, e ∈ b.toRoot x → e.1.1 ∈ sroiqRoleNames p)

structure Within (b : BlockedForest) (rank : Rank) (p : Problem) : Prop where
  labels : b.LabelsWithin p
  guards : b.GuardsWithin rank p
  roles : b.RolesWithin p

theorem rootDataCSP_isSROIQD {b : BlockedForest} {rank : Rank} {p : Problem}
    (hi : p.SROIQDInput rank) (hw : b.LabelsWithin p) :
    (b.rootDataCSP p).isSROIQD = true := by
  apply mkSubjectsDataCSP_isSROIQD (fun rd hrd => (hi.dataRanges rd hrd).2)
  rintro sl hsl c hc
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hsl
  exact sroiqClos_isSROIQD hi (hw r hc)

theorem nodeDataCSP_isSROIQD {b : BlockedForest} {rank : Rank} {p : Problem}
    (hi : p.SROIQDInput rank) (hw : b.LabelsWithin p) (x : b.Node) :
    (b.nodeDataCSP p x).isSROIQD = true := by
  apply mkSubjectsDataCSP_isSROIQD (fun rd hrd => (hi.dataRanges rd hrd).2)
  rintro sl hsl c hc
  rw [List.mem_singleton] at hsl
  subst hsl
  exact sroiqClos_isSROIQD hi (hw x hc)

theorem rootDataCSP_realizes {b : BlockedForest} {p : Problem}
    {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hm : p.Models i) (hr : b.Realizes i env) :
    (b.rootDataCSP p).Realizes i (b.envNat env) := by
  apply mkSubjectsDataCSP_realizes_of_models hm
  · rintro sl hsl c hc
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hsl
    rw [b.envNat_val env r]
    exact hr.labels r c hc
  · rintro kd hkd y
    obtain ⟨⟨r₁, r₂, dp⟩, he, rfl⟩ := List.mem_map.mp hkd
    rw [b.envNat_val env r₁, b.envNat_val env r₂]
    exact hr.keyDisjoint (r₁, r₂, dp) he y

theorem nodeDataCSP_realizes {b : BlockedForest} {p : Problem}
    {i : Interpretation datatypeMap} {env : b.Node → i.Object}
    (hm : p.Models i) (hr : b.Realizes i env) (x : b.Node) :
    (b.nodeDataCSP p x).Realizes i (b.envNat env) := by
  apply mkSubjectsDataCSP_realizes_of_models hm
  · rintro sl hsl c hc
    rw [List.mem_singleton] at hsl
    subst hsl
    rw [b.envNat_val env x]
    exact hr.labels x c hc
  · rintro kd hkd; cases hkd

/-! ### Clash-freedom and full `SROIQ(D)` saturation -/

structure BlockedClashFree (b : BlockedForest) (p : Problem) : Prop where
  bottom : ∀ x, .bottom ∉ b.labels x
  literal : ∀ x a, .lit a true ∈ b.labels x → .lit a false ∉ b.labels x
  unequal : ∀ x, (x, x) ∉ b.unequal
  nomNeg : ∀ x ind, .nom ind false ∈ b.labels x → ¬ b.BoundTo ind x
  irreflexive : ∀ r ∈ p.chars.irreflexive, ∀ x, ¬ b.Edge (r, false) x x
  asymmetric : ∀ r ∈ p.chars.asymmetric, ∀ x y, b.Edge (r, false) x y → ¬ b.Edge (r, false) y x
  disjoint : ∀ q ∈ p.chars.disjoint, ∀ x y, ¬ (b.Edge q.1 x y ∧ b.Edge q.2 x y)
  selfNeg : ∀ x r, .self r false ∈ b.labels x → ¬ b.Edge r x x
  rootData : (solveDataCSP (b.rootDataCSP p)).isSome = true
  nodeData : ∀ x, b.Unblocked x → b.isRoot x = false →
    (solveDataCSP (b.nodeDataCSP p x)).isSome = true

/-- Complete saturation for a blocked `SROIQ(D)` forest.
In addition to the `SRIQ` conditions:
- All ABox assertions (`classAssertions`, `objAssertions`, `negObjAssertions`,
  `sameInds`, `diffInds`, `dataAssertions`, `negDataAssertions`) are represented
  on the bound root nodes;
- Positive nominals are merged (`nomPos`);
- For root nodes, witnesses for `some`/`min` are unblocked, and non-child
  blockable qualified neighbors of a root upper bound are eliminated by the
  NN-rule (`nnEliminated`);
- For `HasKey`, named roots are split on `k.cls` and on key object-property
  edges vs universal negated-nominal guards, and matching named roots are either
  merged (`x = y`) or separated on a key data property (`(x, y, dp) ∈ b.keyDisjoint`). -/
structure BlockedSaturated (b : BlockedForest) (rank : Rank) (p : Problem) : Prop where
  blocking : b.BlockingValid
  bindings : b.BindingsValid p
  root : p.root ∈ b.labels 0
  classAssertions : ∀ ac ∈ p.classAssertions, ∀ r, b.BoundTo ac.1 r → ac.2 ∈ b.labels r
  objAssertions : ∀ rab ∈ p.objAssertions, ∀ r₁ r₂,
    b.BoundTo rab.2.1 r₁ → b.BoundTo rab.2.2 r₂ → b.Edge (rab.1, false) r₁ r₂
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, ∀ r₁,
    b.BoundTo rab.2.1 r₁ → .all (rab.1, false) (.nom rab.2.2 false) ∈ b.labels r₁
  sameInds : ∀ ab ∈ p.sameInds, ∀ r₁ r₂, b.BoundTo ab.1 r₁ → b.BoundTo ab.2 r₂ → r₁ = r₂
  diffInds : ∀ ab ∈ p.diffInds, ∀ r₁, b.BoundTo ab.1 r₁ → .nom ab.2 false ∈ b.labels r₁
  dataAssertions : ∀ dal ∈ p.dataAssertions, ∀ r, b.BoundTo dal.2.1 r →
    .dataValue dal.1 dal.2.2 true ∈ b.labels r
  negDataAssertions : ∀ dal ∈ p.negDataAssertions, ∀ r, b.BoundTo dal.2.1 r →
    .dataValue dal.1 dal.2.2 false ∈ b.labels r
  nomPos : ∀ x, b.Unblocked x → ∀ ind r, .nom ind true ∈ b.labels x → b.BoundTo ind r → x = r
  conj : ∀ x, b.Unblocked x → ∀ a c, .conj a c ∈ b.labels x → a ∈ b.labels x ∧ c ∈ b.labels x
  disj : ∀ x, b.Unblocked x → ∀ a c, .disj a c ∈ b.labels x → a ∈ b.labels x ∨ c ∈ b.labels x
  some : ∀ x, b.Unblocked x → ∀ r c, .some r c ∈ b.labels x →
    ∃ y, (b.isRoot x = true → b.Unblocked y) ∧ b.Edge r x y ∧ c ∈ b.labels y
  min : ∀ x, b.Unblocked x → ∀ n r c, .min n r c ∈ b.labels x →
    AtLeast n (fun y => (b.isRoot x = true → b.Unblocked y) ∧ b.Edge r x y ∧ c ∈ b.labels y)
  maxQual : ∀ x, b.Unblocked x → ∀ n r c, .max n r c ∈ b.labels x → ∀ y, b.Edge r x y →
    c ∈ b.labels y ∨ c.dual ∈ b.labels y
  nnEliminated : ∀ x, b.isRoot x = true → ∀ n r c, .max n r c ∈ b.labels x →
    ∀ y, b.Unblocked y → b.isRoot y = false → b.parent y ≠ x →
      b.Edge r x y → c ∉ b.labels y
  maxBound : ∀ x, b.Unblocked x → ∀ n r c, .max n r c ∈ b.labels x →
    ¬ AtLeast (n + 1) (fun y =>
      (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧ b.Edge r x y ∧ c ∈ b.labels y)
  selfPos : ∀ x, b.Unblocked x → ∀ r, .self r true ∈ b.labels x → b.Edge r x x
  tbox : ∀ q ∈ p.tbox, ∀ x, b.Unblocked x → q.sub.dual ∈ b.labels x ∨ q.sup ∈ b.labels x
  rules : ∀ q ∈ p.rules, ∀ x y, b.Edge q.1 x y → b.Edge q.2 x y
  reflexive : ∀ r ∈ p.chars.reflexive, ∀ x, b.Edge (r, false) x x
  guardStart : ∀ x, b.Unblocked x → ∀ r c, .all r c ∈ b.labels x →
    (⟨roleLanguage rank p r, c⟩ : Guard) ∈ b.guardLabels x
  guardStep : ∀ x y r, b.Edge r x y → ∀ g ∈ b.guardLabels x, ∀ k ∈ g.advance r,
    k ∈ b.guardLabels y
  guardAccept : ∀ x, ∀ g ∈ b.guardLabels x, g.state.nullable = true → g.filler ∈ b.labels x
  keyCls : ∀ k ∈ p.keys, ∀ x, b.isNamedRoot x = true →
    k.cls ∈ b.labels x ∨ k.cls.dual ∈ b.labels x
  keyObjSplit : ∀ k ∈ p.keys, ∀ r ∈ k.objProps, ∀ x, b.isNamedRoot x = true →
    ∀ a z, (a, z) ∈ b.noms →
      b.Edge r x z ∨ .all r (.nom (.named a) false) ∈ b.labels x
  keyMerge : ∀ k ∈ p.keys, ∀ x y, b.isNamedRoot x = true → b.isNamedRoot y = true →
    k.cls ∈ b.labels x → k.cls ∈ b.labels y →
    (∀ r ∈ k.objProps, ∃ z, b.isNamedRoot z = true ∧ b.Edge r x z ∧ b.Edge r y z) →
    x = y ∨ ∃ dp ∈ k.dataProps, (x, y, dp) ∈ b.keyDisjoint

/-! ### Pairwise blocking recomputation and depth bound -/

private def sameMembers {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private theorem sameMembers_iff {α : Type} [DecidableEq α] {xs ys : List α} :
    sameMembers xs ys = true ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  simp only [sameMembers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨a, b⟩ x => ⟨a x, b x⟩, fun h => ⟨fun x => (h x).mp, fun x => (h x).mpr⟩⟩

def comparePair (b : BlockedForest) (x y : b.Node) : Bool :=
  sameMembers (b.labels (b.parent x)) (b.labels (b.parent y)) &&
    sameMembers (b.labels x) (b.labels y) &&
    sameMembers (b.guardLabels (b.parent x)) (b.guardLabels (b.parent y)) &&
    sameMembers (b.guardLabels x) (b.guardLabels y) &&
    sameMembers (b.down x) (b.down y) && sameMembers (b.up x) (b.up y)

theorem comparePair_iff {b : BlockedForest} {x y : b.Node} :
    b.comparePair x y = true ↔ b.PairMatch x y := by
  simp only [comparePair, Bool.and_eq_true, sameMembers_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, c⟩, d⟩, e⟩, f⟩, g⟩
    refine ⟨a, c, d, e, ?_⟩
    rintro ⟨r, _ | _⟩
    · exact f r
    · exact g r
  · intro h
    exact ⟨⟨⟨⟨⟨h.parentLabels, h.labels⟩, h.parentGuards⟩, h.guards⟩,
      fun r => h.roles (r, false)⟩, fun r => h.roles (r, true)⟩

private def candidate (b : BlockedForest) (x : b.Node) : Option b.Node :=
  (b.ancestors x).find? (fun a => !b.isRoot a && b.comparePair x a)

private theorem candidate_some {b : BlockedForest} {x a : b.Node}
    (h : b.candidate x = some a) :
    b.Anc a x ∧ b.isRoot a = false ∧ b.PairMatch x a := by
  have hc : (!b.isRoot a && b.comparePair x a) = true :=
    List.find?_some (p := fun n => !b.isRoot n && b.comparePair x n) h
  simp only [Bool.and_eq_true, Bool.not_eq_true', comparePair_iff] at hc
  exact ⟨mem_ancestors.mp (List.mem_of_find?_eq_some h), hc⟩

private theorem candidate_none {b : BlockedForest} {x a : b.Node}
    (h : b.candidate x = none) (ha : b.Anc a x) (hn : b.isRoot a = false) :
    ¬ b.PairMatch x a := by
  have ht := List.find?_eq_none.mp h a (mem_ancestors.mpr ha)
  intro hm
  simp [hn, comparePair_iff.mpr hm] at ht

private def hasCandidate (b : BlockedForest) (x : b.Node) : Bool :=
  (b.candidate x).isSome

private def hasEarlier (b : BlockedForest) (x : b.Node) : Bool :=
  (b.ancestors x).any b.hasCandidate

private theorem earlier_iff {b : BlockedForest} {x : b.Node} :
    b.hasEarlier x = true ↔ ∃ a, b.Anc a x ∧ b.hasCandidate a = true := by
  simp only [hasEarlier, List.any_eq_true, mem_ancestors]

private theorem earlier_false {b : BlockedForest} {x : b.Node}
    (h : b.hasEarlier x = false) {a : b.Node} (ha : b.Anc a x) :
    b.candidate a = none := by
  cases e : b.candidate a with
  | none => rfl
  | some y =>
    have ht := earlier_iff.mpr ⟨a, ha, by simp [hasCandidate, e]⟩
    rw [h] at ht; cases ht

def reblock (b : BlockedForest) : BlockedForest :=
  { b with blockedBy := fun x => if b.hasEarlier x then none else b.candidate x }

private theorem anc_from_reblock {b : BlockedForest} {x a : b.Node}
    (h : b.reblock.Anc a x) : b.Anc a x :=
  match h with
  | .parent hc => .parent hc
  | .step ha hc => .step (anc_from_reblock ha) hc
termination_by structural h

private theorem anc_to_reblock {b : BlockedForest} {x a : b.Node}
    (h : b.Anc a x) : b.reblock.Anc a x :=
  match h with
  | .parent hc => .parent hc
  | .step ha hc => .step (anc_to_reblock ha) hc
termination_by structural h

theorem same_anc_reblock {b : BlockedForest} {x a : b.Node} :
    b.reblock.Anc a x ↔ b.Anc a x :=
  ⟨anc_from_reblock, anc_to_reblock⟩

theorem reblock_valid (b : BlockedForest) : b.reblock.BlockingValid := by
  constructor
  intro x y he
  change (if b.hasEarlier x then none else b.candidate x) = some y at he
  cases hb : b.hasEarlier x with
  | true => simp [hb] at he
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at he
    have ⟨ha, hn, hm⟩ := candidate_some he
    have noAt (a : b.Node) (ha : b.Anc a x) : b.reblock.blockedBy a = none := by
      change (if b.hasEarlier a then none else b.candidate a) = none
      simp [earlier_false hb ha]
    have noAnc (a : b.Node) (h : ∀ z, b.Anc z a → b.Anc z x) :
        ¬ b.reblock.IndirectlyBlocked a := by
      rintro ⟨z, hz, hb⟩
      simp [DirectlyBlocked, noAt z (h z (same_anc_reblock.mp hz))] at hb
    refine ⟨same_anc_reblock.mpr ha, hn, ⟨noAt y ha, noAnc y (fun _ hz => hz.trans ha)⟩,
      noAnc x (fun _ hz => hz), ?_⟩
    exact ⟨hm.parentLabels, hm.labels, hm.parentGuards, hm.guards, hm.roles⟩

private theorem candidate_exists_front {b : BlockedForest} {x : b.Node}
    (h : b.hasCandidate x = true) :
    ∃ a, (a = x ∨ b.Anc a x) ∧ b.reblock.DirectlyBlocked a := by
  cases he : b.hasEarlier x with
  | false => exact ⟨x, .inl rfl, by simpa [DirectlyBlocked, reblock, he, hasCandidate] using h⟩
  | true =>
    obtain ⟨a, ha, hh⟩ := earlier_iff.mp he
    obtain ⟨z, hz, hd⟩ := candidate_exists_front hh
    exact ⟨z, .inr (hz.elim (· ▸ ha) (·.trans ha)), hd⟩
termination_by x.val
decreasing_by exact ha.lt

theorem unblocked_avoids_pair {b : BlockedForest} {x a : b.Node}
    (hu : b.reblock.Unblocked x) (ha : b.Anc a x) (hn : b.isRoot a = false) :
    ¬ b.PairMatch x a := by
  cases h : b.candidate x with
  | none => exact candidate_none h ha hn
  | some z =>
    obtain ⟨y, hy, hd⟩ := candidate_exists_front (x := x) (by simp [hasCandidate, h])
    rcases hy with rfl | hy
    · simp [DirectlyBlocked, hu.1] at hd
    · exact (hu.2 ⟨y, same_anc_reblock.mpr hy, hd⟩).elim

theorem unblocked_ancestor {b : BlockedForest} {x a : b.Node}
    (hx : b.Unblocked x) (ha : b.Anc a x) : b.Unblocked a := by
  constructor
  · cases h : b.blockedBy a with
    | none => rfl
    | some y => exact (hx.2 ⟨a, ha, by simp [DirectlyBlocked, h]⟩).elim
  · rintro ⟨z, hz, hb⟩
    exact hx.2 ⟨z, hz.trans ha, hb⟩

private inductive ForestPairToken where
  | parent (label : Concept ⊕ Guard)
  | child (label : Concept ⊕ Guard)
  | down (role : IRI)
  | up (role : IRI)
  deriving DecidableEq

private def forestPairAlphabet (rank : Rank) (p : Problem) : List ForestPairToken :=
  (sroiqAlphabet rank p).map .parent ++ (sroiqAlphabet rank p).map .child ++
    (sroiqRoleNames p).map .down ++ (sroiqRoleNames p).map .up

private def observed (b : BlockedForest) (x : b.Node) : ForestPairToken → Bool
  | .parent (.inl c) => (b.labels (b.parent x)).contains c
  | .parent (.inr g) => (b.guardLabels (b.parent x)).contains g
  | .child (.inl c) => (b.labels x).contains c
  | .child (.inr g) => (b.guardLabels x).contains g
  | .down r => (b.down x).contains r
  | .up r => (b.up x).contains r

private def signature (b : BlockedForest) (rank : Rank) (p : Problem) (x : b.Node) :
    List ForestPairToken :=
  (forestPairAlphabet rank p).filter (b.observed x)

private theorem observed_in_alphabet {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x : b.Node} {t : ForestPairToken}
    (h : b.observed x t = true) : t ∈ forestPairAlphabet rank p := by
  cases t with
  | parent label =>
    apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ?_)))
    cases label with
    | inl c => exact List.mem_append_left _ (List.mem_map_of_mem (hw.labels _ (List.contains_iff_mem.mp h)))
    | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (hw.guards _ (List.contains_iff_mem.mp h)))
  | child label =>
    apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ?_)))
    cases label with
    | inl c => exact List.mem_append_left _ (List.mem_map_of_mem (hw.labels _ (List.contains_iff_mem.mp h)))
    | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (hw.guards _ (List.contains_iff_mem.mp h)))
  | down r =>
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem ((hw.roles.1 x).1 (List.contains_iff_mem.mp h))))
  | up r =>
    exact List.mem_append_right _ (List.mem_map_of_mem ((hw.roles.1 x).2.1 (List.contains_iff_mem.mp h)))

private theorem signature_iff {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x : b.Node} {t : ForestPairToken} :
    t ∈ b.signature rank p x ↔ b.observed x t = true :=
  ⟨fun h => (List.mem_filter.mp h).2, fun h => List.mem_filter.mpr ⟨observed_in_alphabet hw h, h⟩⟩

private theorem signature_eq_match {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x y : b.Node} (he : b.signature rank p x = b.signature rank p y) :
    b.PairMatch x y := by
  have matchAt (t : ForestPairToken) : b.observed x t = true ↔ b.observed y t = true :=
    (signature_iff hw).symm.trans (he ▸ signature_iff hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c; simpa only [observed, List.contains_iff_mem] using matchAt (.parent (.inl c))
  · intro c; simpa only [observed, List.contains_iff_mem] using matchAt (.child (.inl c))
  · intro g; simpa only [observed, List.contains_iff_mem] using matchAt (.parent (.inr g))
  · intro g; simpa only [observed, List.contains_iff_mem] using matchAt (.child (.inr g))
  · rintro ⟨r, _ | _⟩
    · change r ∈ b.down x ↔ r ∈ b.down y
      simpa only [observed, List.contains_iff_mem] using matchAt (.down r)
    · change r ∈ b.up x ↔ r ∈ b.up y
      simpa only [observed, List.contains_iff_mem] using matchAt (.up r)

private def nonrootPath (b : BlockedForest) (x : b.Node) : List b.Node :=
  if _h : b.isRoot x = true then [] else x :: b.nonrootPath (b.parent x)
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

private theorem nonroot_length {b : BlockedForest} (x : b.Node) :
    (b.nonrootPath x).length = b.depth x := by
  rw [nonrootPath, depth, ancestors]
  split
  · rfl
  · simp only [List.length_cons]
    exact congrArg Nat.succ (nonroot_length (b.parent x))
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

private theorem mem_nonrootPath {b : BlockedForest} {x a : b.Node}
    (h : a ∈ b.nonrootPath x) :
    b.isRoot a = false ∧ (a = x ∨ b.Anc a x) := by
  rw [nonrootPath] at h
  split at h
  · exact (List.not_mem_nil h).elim
  · rename_i hnr
    have hf : b.isRoot x = false := Bool.eq_false_iff.mpr hnr
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨hf, .inl rfl⟩
    · have ⟨hn, ha⟩ := mem_nonrootPath h
      exact ⟨hn, .inr ((Anc.child_iff ⟨hf, rfl⟩).mpr ha)⟩
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

private theorem distinct_signatures {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) (x : b.Node) (hu : b.reblock.Unblocked x) :
    ((b.nonrootPath x).map (b.signature rank p)).Nodup := by
  rw [nonrootPath]
  split
  · simp
  · rename_i hnr
    have hf : b.isRoot x = false := Bool.eq_false_iff.mpr hnr
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨y, hy, he⟩ := List.mem_map.mp h
      have ⟨hyn, hyp⟩ := mem_nonrootPath hy
      have hanc : b.Anc y x := (Anc.child_iff ⟨hf, rfl⟩).mpr hyp
      exact unblocked_avoids_pair hu hanc hyn (signature_eq_match hw he.symm)
    · exact distinct_signatures hw (b.parent x)
        (unblocked_ancestor hu (anc_to_reblock (.parent ⟨hf, rfl⟩)))
termination_by x.val
decreasing_by exact b.parent_lt x (Bool.eq_false_iff.mpr ‹_›)

theorem unblocked_depth_le {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x : b.Node} (hu : b.reblock.Unblocked x) :
    b.depth x ≤ sroiqMaxDepth rank p := by
  have hsubset : (b.nonrootPath x).map (b.signature rank p) ⊆ subsets (forestPairAlphabet rank p) := by
    intro row hm
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
    exact filter_mem_subsets _ _
  have hle := (distinct_signatures hw x hu).length_le_of_subset hsubset
  rw [List.length_map, nonroot_length, subsets_length] at hle
  have sizes : (forestPairAlphabet rank p).length =
      2 * (sroiqAlphabet rank p).length + 2 * (sroiqRoleNames p).length := by
    simp only [forestPairAlphabet, List.length_append, List.length_map]
    omega
  rwa [sizes] at hle

#print axioms reblock_valid
#print axioms unblocked_depth_le

end BlockedForest
end Termination
end Sabrina.OWL2.SROIQD
