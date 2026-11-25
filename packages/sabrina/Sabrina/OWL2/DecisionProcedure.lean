import Sabrina.OWL2.Normalize
import Sabrina.OWL2.RankedBridge

/-! M9 — Terminating Verified Search & Total Decision Procedures:
    1. Well-founded budget-free tableau search (`TerminatingRuleSet`, `decideBranch`)
       with proved fairness, exhaustiveness, well-founded termination, and
       both-direction model/refutation completeness composed with source `Ontology`
       normalization.
    2. Concrete well-founded fixed-point pruning (`pruneWF`) with explicit
       strictly decreasing measure `pool.length`, proving budget-free termination
       of type elimination.
    3. Total, budget-free OWL 2 Direct Semantics decision procedures for Ranked
       `ALCHI` + Regular Role Chains (`decideRanked`, `decideRankedOntology`,
       `decideRankedInclusion`) with proved totality and both-direction
       equivalence across all four query verdicts (`entailed`, `refuted`,
       `independent`, `inconsistent`). -/

namespace Sabrina.OWL2.DecisionProcedure

open Sabrina.OWL2 Sabrina.OWL2.SROIQD Sabrina.OWL2.Normalize Sabrina.OWL2.Datatypes
open Sabrina.ALC (OrientedRole RoleTheory InclusionVerdict Row Certificate)
open Sabrina.RoleChains (Chain Rank Ranked checkRegular checkRegular_sound)

/-! ### 1. Well-Founded Budget-Free Tableau Decision Engine -/

/-- Executable output of a terminating, budget-free tableau decision procedure:
    either an open saturated branch witnessing satisfiability, or a finite
    closed-tableau depth witnessing unsatisfiability. Never returns `UNKNOWN`. -/
inductive TableauDecision where
  | sat (openBranch : Branch)
  | unsat (depth : Nat)
  deriving Repr

/-- A well-founded, fair, sound tableau rule selector for `p : Problem`:
    - `measure` provides a strictly decreasing well-founded metric on branches;
    - `step` selects a sound `Transition p s` whenever any rule applies;
    - `decreases` certifies strict measure decrease on every child branch;
    - `fair` certifies that when no rule applies, `s` is clash-free and fully
      saturated (`SROIQDSaturated p`). -/
structure TerminatingRuleSet (p : Problem) where
  measure : Branch → Nat
  step : (s : Branch) → Option (Transition p s)
  decreases : ∀ s t, step s = some t → ∀ b ∈ t.branches, measure b < measure s
  fair : ∀ s, step s = none → s.CoreClashFree ∧ s.SROIQDSaturated p

private def decideList {p : Problem} (rs : TerminatingRuleSet p) (bound : Nat)
    (recCall : ∀ b, rs.measure b < bound → TableauDecision) :
    (bs : List Branch) → (∀ b ∈ bs, rs.measure b < bound) → TableauDecision
  | [], _ => .unsat 1
  | b :: rest, hlt =>
    match recCall b (hlt b (List.mem_cons_self ..)) with
    | .sat openB => .sat openB
    | .unsat d1 =>
      match decideList rs bound recCall rest (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) with
      | .sat openB => .sat openB
      | .unsat d2 => .unsat (max (d1 + 1) d2)

/-- Total, fuel-free, well-founded recursive tableau search over any
    `TerminatingRuleSet p`. Terminates unconditionally by `rs.measure s`. -/
def decideBranch {p : Problem} (rs : TerminatingRuleSet p) (s : Branch) : TableauDecision :=
  match hstep : rs.step s with
  | none => .sat s
  | some t =>
    decideList rs (rs.measure s)
      (fun b _ => decideBranch rs b)
      t.branches
      (fun b hb => rs.decreases s t hstep b hb)
termination_by rs.measure s

/-- Every `TerminatingRuleSet p` yields a budget-independent `SROIQDDerivation p s`
    for every branch `s`, proved by well-founded induction on `rs.measure s`. -/
theorem terminatingRuleSet_derivation {p : Problem} (rs : TerminatingRuleSet p) (s : Branch) :
    SROIQDDerivation p s := by
  cases hstep : rs.step s with
  | none =>
    obtain ⟨hcf, hsat⟩ := rs.fair s hstep
    exact .saturated hcf hsat
  | some t =>
    refine .step t fun b hb => ?_
    have _ : rs.measure b < rs.measure s := rs.decreases s t hstep b hb
    exact terminatingRuleSet_derivation rs b
termination_by rs.measure s

private theorem decideList_spec {p : Problem} (rs : TerminatingRuleSet p) (bound : Nat)
    (recCall : ∀ b, rs.measure b < bound → TableauDecision)
    (hspec : ∀ b (hb : rs.measure b < bound),
      match recCall b hb with
      | .sat openB => openB.CoreClashFree ∧ openB.SROIQDSaturated p
      | .unsat _ => CoreRefutation p b)
    (bs : List Branch) (hlt : ∀ b ∈ bs, rs.measure b < bound) :
    match decideList rs bound recCall bs hlt with
    | .sat openB => openB.CoreClashFree ∧ openB.SROIQDSaturated p
    | .unsat _ => ∀ b ∈ bs, CoreRefutation p b := by
  induction bs with
  | nil =>
    simp [decideList]
  | cons b rest ih =>
    simp only [decideList]
    have hbSpec := hspec b (hlt b (List.mem_cons_self ..))
    cases h1 : recCall b (hlt b (List.mem_cons_self ..)) with
    | sat openB =>
      rw [h1] at hbSpec
      exact hbSpec
    | unsat d1 =>
      rw [h1] at hbSpec
      have hrest := ih (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      cases h2 : decideList rs bound recCall rest (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) with
      | sat openB =>
        rw [h2] at hrest
        exact hrest
      | unsat d2 =>
        rw [h2] at hrest
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hbSpec
        · exact hrest x hx'

private theorem decideBranch_none {p : Problem} (rs : TerminatingRuleSet p) (s : Branch)
    (h : rs.step s = none) : decideBranch rs s = .sat s := by
  rw [decideBranch]; split <;> simp_all

private theorem decideBranch_some {p : Problem} (rs : TerminatingRuleSet p) (s : Branch)
    (t : Transition p s) (h : rs.step s = some t) :
    decideBranch rs s = decideList rs (rs.measure s)
      (fun b _ => decideBranch rs b) t.branches
      (fun b hb => rs.decreases s t h b hb) := by
  rw [decideBranch]; split
  · simp_all
  · rename_i t' ht'
    have heq : t' = t := Option.some.inj (ht'.symm.trans h)
    subst heq; rfl

/-- Soundness & exhaustiveness of `decideBranch`:
    - `.sat openB` always returns a clash-free, fully saturated branch;
    - `.unsat _` always certifies a finite closed refutation `CoreRefutation p s`. -/
theorem decideBranch_spec {p : Problem} (rs : TerminatingRuleSet p) (s : Branch) :
    match decideBranch rs s with
    | .sat openB => openB.CoreClashFree ∧ openB.SROIQDSaturated p
    | .unsat _ => CoreRefutation p s := by
  cases hstep : rs.step s with
  | none =>
    rw [decideBranch_none rs s hstep]
    exact rs.fair s hstep
  | some t =>
    rw [decideBranch_some rs s t hstep]
    have hl := decideList_spec rs (rs.measure s)
      (fun b _ => decideBranch rs b)
      (fun b hb => by
        have _ : rs.measure b < rs.measure s := hb
        exact decideBranch_spec rs b)
      t.branches
      (fun b hb => rs.decreases s t hstep b hb)
    cases hd : decideList rs (rs.measure s) (fun b _ => decideBranch rs b) t.branches
        (fun b hb => rs.decreases s t hstep b hb) with
    | sat openB =>
      rw [hd] at hl
      exact hl
    | unsat d =>
      rw [hd] at hl
      exact .step t hl
termination_by rs.measure s

/-- Both-direction satisfiability equivalence for `decideBranch` on any ordinary
    `SROIQ(D)` problem `p` with initial branch `s0`. -/
theorem decideBranch_sat_iff {p : Problem} {s0 : Branch} (rs : TerminatingRuleSet p)
    (hord : p.isOrdinary = true) (hinit : initial p = some s0) :
    (∃ openB, decideBranch rs s0 = .sat openB) ↔ p.Sat := by
  have hspec := decideBranch_spec rs s0
  cases hd : decideBranch rs s0 with
  | sat openB =>
    rw [hd] at hspec
    exact ⟨fun _ => sroiqd_saturated_sat hord hspec.1 hspec.2, fun _ => ⟨openB, rfl⟩⟩
  | unsat d =>
    rw [hd] at hspec
    constructor
    · rintro ⟨_, he⟩; cases he
    · intro hsat; exact (coreRefutation_sound hspec (initial_sat hinit hsat)).elim

/-- Both-direction unsatisfiability equivalence for `decideBranch` on any ordinary
    `SROIQ(D)` problem `p` with initial branch `s0`. -/
theorem decideBranch_unsat_iff {p : Problem} {s0 : Branch} (rs : TerminatingRuleSet p)
    (hord : p.isOrdinary = true) (hinit : initial p = some s0) :
    (∃ d, decideBranch rs s0 = .unsat d) ↔ ¬ p.Sat := by
  have hspec := decideBranch_spec rs s0
  cases hd : decideBranch rs s0 with
  | sat openB =>
    rw [hd] at hspec
    constructor
    · rintro ⟨_, he⟩; cases he
    · intro hunsat; exact (hunsat (sroiqd_saturated_sat hord hspec.1 hspec.2)).elim
  | unsat d =>
    rw [hd] at hspec
    exact ⟨fun _ hsat => coreRefutation_sound hspec (initial_sat hinit hsat), fun _ => ⟨d, rfl⟩⟩

/-- End-to-end M9 decision-procedure equivalence for a normalized source OWL 2 DL
    `Ontology` `o`: `decideBranch` returns `.sat` iff `o` is satisfiable under
    OWL 2 Direct Semantics, and `.unsat` iff `o` is unsatisfiable. -/
theorem decideBranch_ontology_iff {o : Ontology} {defs : DatatypeDefs}
    {p : Problem} {s0 : Branch} (rs : TerminatingRuleSet p)
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hroot : p.root = .top)
    (hord : p.isOrdinary = true)
    (hinit : initial p = some s0) :
    ((∃ openB, decideBranch rs s0 = .sat openB) ↔ Satisfiable datatypeMap o) ∧
    ((∃ d, decideBranch rs s0 = .unsat d) ↔ ¬ Satisfiable datatypeMap o) := by
  have hsatIff : Satisfiable datatypeMap o ↔ p.Sat :=
    (normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)
  exact ⟨(decideBranch_sat_iff rs hord hinit).trans hsatIff.symm,
         (decideBranch_unsat_iff rs hord hinit).trans (not_congr hsatIff).symm⟩

/-! ### 2. Concrete Well-Founded Fixed-Point Termination (`pruneWF`) -/

private theorem prune_length_lt_of_ne (cs : List Sabrina.ALC.Concept)
    (edge : String → Row → Row → Bool) (pool : List Row)
    (hne : Sabrina.ALC.prune cs pool edge ≠ pool) :
    (Sabrina.ALC.prune cs pool edge).length < pool.length := by
  have hsub : (Sabrina.ALC.prune cs pool edge).Sublist pool := List.filter_sublist
  have hlenNe : (Sabrina.ALC.prune cs pool edge).length ≠ pool.length :=
    fun he => hne (hsub.eq_of_length he)
  exact Nat.lt_of_le_of_ne hsub.length_le hlenNe

/-- Budget-free, well-founded recursive type-elimination fixed point, terminating
    directly by `pool.length` without any step/round budget. -/
def pruneWF (cs : List Sabrina.ALC.Concept) (edge : String → Row → Row → Bool) (pool : List Row) : List Row :=
  let next := Sabrina.ALC.prune cs pool edge
  if h : next = pool then pool
  else
    have _ : next.length < pool.length := prune_length_lt_of_ne cs edge pool h
    pruneWF cs edge next
termination_by pool.length

theorem pruneWF_fixed (cs : List Sabrina.ALC.Concept) (edge : String → Row → Row → Bool) (pool : List Row) :
    Sabrina.ALC.prune cs (pruneWF cs edge pool) edge = pruneWF cs edge pool := by
  rw [pruneWF]
  split
  · rename_i he; exact he
  · rename_i hne
    have _ : (Sabrina.ALC.prune cs pool edge).length < pool.length :=
      prune_length_lt_of_ne cs edge pool hne
    exact pruneWF_fixed cs edge (Sabrina.ALC.prune cs pool edge)
termination_by pool.length

theorem pruneWF_eq_pruneRoundsWith (cs : List Sabrina.ALC.Concept) (edge : String → Row → Row → Bool)
    (rounds : Nat) (pool : List Row) (hsize : pool.length ≤ rounds) :
    pruneWF cs edge pool = Sabrina.ALC.pruneRoundsWith cs edge rounds pool := by
  induction rounds generalizing pool with
  | zero =>
    have hn : pool = [] := List.eq_nil_iff_length_eq_zero.mpr (Nat.eq_zero_of_le_zero hsize)
    subst hn
    rw [pruneWF]
    simp [Sabrina.ALC.prune, Sabrina.ALC.pruneRoundsWith]
  | succ n ih =>
    rw [pruneWF]
    by_cases h : Sabrina.ALC.prune cs pool edge = pool
    · simp [Sabrina.ALC.pruneRoundsWith, h]
    · have hlt := prune_length_lt_of_ne cs edge pool h
      simp only [h, ↓reduceDIte, Sabrina.ALC.pruneRoundsWith, ↓reduceIte]
      exact ih (Sabrina.ALC.prune cs pool edge) (by omega)

/-! ### 3. Concrete Total, Budget-Free OWL 2 Direct Semantics Decision Procedures (Ranked `ALCHI` + Regular Role Chains) -/

/-- A validated Ranked `ALCHI` + Regular Role Chain input with checked rank witness. -/
structure RankedInput where
  rules : RoleTheory
  chains : List Chain
  tbox : Sabrina.ALC.TBox
  rank : Rank
  regular : checkRegular rank rules chains = true

/-- The OWL 2 Direct Semantics `Ontology` denoted by a `RankedInput`. -/
def RankedInput.toOntology (inp : RankedInput) : Ontology :=
  RankedBridge.ontology inp.rules inp.chains inp.tbox

/-- The OWL 2 Direct Semantics query axiom for `q : Sabrina.ALC.Inclusion`. -/
def rankedQueryAxiom (q : Sabrina.ALC.Inclusion) : Axiom :=
  GradedBridge.inclusion (RankedBridge.gradedInclusion q)

/-- Budget-free, total, executable decision procedure for concept satisfiability
    over a `RankedInput`. -/
def decideRankedConcept (inp : RankedInput) (root : Sabrina.ALC.Concept) : Certificate :=
  Sabrina.RoleChains.RankedPaths.search inp.rank inp.rules inp.chains inp.tbox root

/-- Budget-free, total, executable decision procedure for ontology consistency
    over a `RankedInput`. -/
def decideRankedOntology (inp : RankedInput) : Certificate :=
  decideRankedConcept inp .top

/-- Every certificate returned by `decideRankedConcept` passes the verified checker. -/
theorem decideRankedConcept_checked (inp : RankedInput) (root : Sabrina.ALC.Concept) :
    Sabrina.RoleChains.RankedPaths.check inp.rank inp.rules inp.chains inp.tbox root
      (decideRankedConcept inp root) = true :=
  Sabrina.RoleChains.RankedPaths.search_checked inp.rank inp.rules inp.chains inp.tbox root

private theorem gradedConcept_withAnonymous (i : Interpretation datatypeMap)
    (assign : String → String → i.Object) (c : Sabrina.Graded.Concept) (x : i.Object) :
    classHolds (i.withAnonymous assign) x (GradedBridge.concept c) ↔
      classHolds i x (GradedBridge.concept c) :=
  (GradedBridge.concept_iff (i.withAnonymous assign) c x).trans
    (GradedBridge.concept_iff i c x).symm

private theorem gradedInclusion_withAnonymous (i : Interpretation datatypeMap)
    (assign : String → String → i.Object) (q : Sabrina.Graded.Inclusion) :
    axiomHolds (i.withAnonymous assign) (GradedBridge.inclusion q) ↔
      axiomHolds i (GradedBridge.inclusion q) :=
  forall_congr' fun x => imp_congr
    (gradedConcept_withAnonymous i assign q.sub x)
    (gradedConcept_withAnonymous i assign q.sup x)

private theorem rankedOntology_sat_iff (inp : RankedInput) :
    RankedBridge.conceptSat datatypeMap inp.rules inp.chains inp.tbox .top ↔
      Satisfiable datatypeMap inp.toOntology := by
  constructor
  · rintro ⟨i, hm, _, _⟩
    exact ⟨i, hm⟩
  · rintro ⟨i, hm⟩
    obtain ⟨x⟩ := i.objectNonempty
    exact ⟨i, hm, x, i.thingExt x⟩

/-- Both-direction OWL 2 Direct Semantics equivalence and totality for
    `decideRankedOntology` (model iff satisfiable; refutation iff unsatisfiable). -/
theorem decideRankedOntology_sat_iff (inp : RankedInput) :
    (∃ pool, decideRankedOntology inp = .model pool) ↔
      Satisfiable datatypeMap inp.toOntology :=
  (RankedBridge.search_model_iff datatypeMap (checkRegular_sound inp.regular) inp.tbox .top).trans
    (rankedOntology_sat_iff inp)

theorem decideRankedOntology_unsat_iff (inp : RankedInput) :
    (∃ rounds, decideRankedOntology inp = .refutation rounds) ↔
      ¬ Satisfiable datatypeMap inp.toOntology :=
  (RankedBridge.search_refutation_iff datatypeMap (checkRegular_sound inp.regular) inp.tbox .top).trans
    (not_congr (rankedOntology_sat_iff inp))

/-- Total, budget-free, executable 4-verdict decision procedure for OWL 2
    subsumption queries over Ranked `ALCHI` + Regular Role Chains. -/
def decideRankedInclusion (inp : RankedInput) (q : Sabrina.ALC.Inclusion) : InclusionVerdict :=
  let counter := decideRankedConcept inp (.conj q.sub (.neg q.sup))
  let incl := Sabrina.RoleChains.RankedPaths.search inp.rank inp.rules inp.chains (q :: inp.tbox) .top
  match counter, incl with
  | .refutation _, .model _ => .entailed
  | .model _, .refutation _ => .refuted
  | .model _, .model _ => .independent
  | .refutation _, .refutation _ => .inconsistent

private theorem ranked_entails_iff (inp : RankedInput) (q : Sabrina.ALC.Inclusion) :
    Entails datatypeMap inp.toOntology [rankedQueryAxiom q] ↔
      ¬ RankedBridge.conceptSat datatypeMap inp.rules inp.chains inp.tbox (.conj q.sub (.neg q.sup)) := by
  constructor
  · rintro hent ⟨i, hm, x, hsub, hdual⟩
    obtain ⟨assign, hqSat⟩ := hent i hm
    have hqAx : axiomHolds (i.withAnonymous assign) (rankedQueryAxiom q) :=
      hqSat _ (List.mem_singleton_self _)
    have hqI : axiomHolds i (rankedQueryAxiom q) :=
      (gradedInclusion_withAnonymous i assign (RankedBridge.gradedInclusion q)).mp hqAx
    have hsup : classHolds i x (GradedBridge.concept (RankedBridge.gradedConcept q.sup)) :=
      hqI x hsub
    have hnotSup : ¬ classHolds i x (GradedBridge.concept (RankedBridge.gradedConcept q.sup)) := by
      have h1 := (GradedBridge.concept_iff i (RankedBridge.gradedConcept q.sup).dual x).mp hdual
      have h2 := (Sabrina.Graded.holds_dual (GradedBridge.reduct i) (GradedBridge.reductNom i) x
        (RankedBridge.gradedConcept q.sup)).mp h1
      exact fun hs => h2 ((GradedBridge.concept_iff i (RankedBridge.gradedConcept q.sup) x).mp hs)
    exact hnotSup hsup
  · intro hno i hm
    refine ⟨fun _ _ => Classical.choice i.objectNonempty, fun ax hax => ?_⟩
    rw [List.mem_singleton.mp hax]
    refine (gradedInclusion_withAnonymous i _ (RankedBridge.gradedInclusion q)).mpr ?_
    intro x hsub
    apply Classical.byContradiction
    intro hnotSup
    have hdual : classHolds i x (GradedBridge.concept (RankedBridge.gradedConcept q.sup).dual) := by
      apply (GradedBridge.concept_iff i (RankedBridge.gradedConcept q.sup).dual x).mpr
      apply (Sabrina.Graded.holds_dual (GradedBridge.reduct i) (GradedBridge.reductNom i) x
        (RankedBridge.gradedConcept q.sup)).mpr
      exact fun hs => hnotSup ((GradedBridge.concept_iff i (RankedBridge.gradedConcept q.sup) x).mpr hs)
    exact hno ⟨i, hm, x, hsub, hdual⟩

private theorem ranked_withQuery_sat_iff (inp : RankedInput) (q : Sabrina.ALC.Inclusion) :
    RankedBridge.conceptSat datatypeMap inp.rules inp.chains (q :: inp.tbox) .top ↔
      Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) := by
  have hmem : ∀ (i : Interpretation datatypeMap),
      models i (RankedBridge.ontology inp.rules inp.chains (q :: inp.tbox)) ↔
      models i (rankedQueryAxiom q :: inp.toOntology) := fun i => by
    constructor <;> rintro ⟨assign, hsat⟩ <;> refine ⟨assign, fun ax hax => ?_⟩
    · rcases List.mem_cons.mp hax with rfl | hmem
      · apply hsat
        simp [RankedBridge.ontology, GradedBridge.ontology, rankedQueryAxiom]
      · apply hsat
        simp only [RankedBridge.ontology, GradedBridge.ontology, RankedInput.toOntology,
          List.mem_append, List.map_cons, List.mem_cons] at hmem ⊢
        rcases hmem with ((h1 | h2) | h3) | h4
        · exact Or.inl (Or.inl (Or.inl h1))
        · exact Or.inl (Or.inl (Or.inr h2))
        · exact Or.inl (Or.inr h3)
        · exact Or.inr (Or.inr h4)
    · simp only [RankedBridge.ontology, GradedBridge.ontology, List.mem_append,
        List.map_cons, List.mem_cons] at hax
      rcases hax with ((h1 | h2) | h3) | (rfl | h4)
      · exact hsat ax (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1))))
      · exact hsat ax (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h2))))
      · exact hsat ax (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h3)))
      · exact hsat _ (List.mem_cons_self ..)
      · exact hsat ax (List.mem_cons_of_mem _ (List.mem_append_right _ h4))
  constructor
  · rintro ⟨i, hm, _, _⟩; exact ⟨i, (hmem i).mp hm⟩
  · rintro ⟨i, hm⟩
    obtain ⟨x⟩ := i.objectNonempty
    exact ⟨i, (hmem i).mpr hm, x, i.thingExt x⟩

/-- Exact four-verdict soundness and completeness theorem for the total,
    budget-free decision procedure `decideRankedInclusion` over OWL 2 Direct
    Semantics (`Satisfiable datatypeMap` and `Entails datatypeMap`). -/
theorem decideRankedInclusion_iff (inp : RankedInput) (q : Sabrina.ALC.Inclusion) :
    (decideRankedInclusion inp q = .entailed ↔
      Satisfiable datatypeMap inp.toOntology ∧
      Entails datatypeMap inp.toOntology [rankedQueryAxiom q]) ∧
    (decideRankedInclusion inp q = .refuted ↔
      Satisfiable datatypeMap inp.toOntology ∧
      ¬ Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology)) ∧
    (decideRankedInclusion inp q = .independent ↔
      ¬ Entails datatypeMap inp.toOntology [rankedQueryAxiom q] ∧
      Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology)) ∧
    (decideRankedInclusion inp q = .inconsistent ↔
      ¬ Satisfiable datatypeMap inp.toOntology) := by
  have hreg := checkRegular_sound inp.regular
  have hcMod := RankedBridge.search_model_iff datatypeMap hreg inp.tbox (.conj q.sub (.neg q.sup))
  have hcRef := RankedBridge.search_refutation_iff datatypeMap hreg inp.tbox (.conj q.sub (.neg q.sup))
  have hiMod := RankedBridge.search_model_iff datatypeMap hreg (q :: inp.tbox) .top
  have hiRef := RankedBridge.search_refutation_iff datatypeMap hreg (q :: inp.tbox) .top
  have hent := ranked_entails_iff inp q
  have hqsat := ranked_withQuery_sat_iff inp q
  have hsubSat : Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) →
      Satisfiable datatypeMap inp.toOntology := fun ⟨i, assign, hsat⟩ =>
    ⟨i, assign, fun ax hax => hsat ax (List.mem_cons_of_mem _ hax)⟩
  have hsatOfCounter : RankedBridge.conceptSat datatypeMap inp.rules inp.chains inp.tbox (.conj q.sub (.neg q.sup)) →
      Satisfiable datatypeMap inp.toOntology := fun ⟨i, hm, _, _⟩ => ⟨i, hm⟩
  have hunsatImpl : ¬ Satisfiable datatypeMap inp.toOntology →
      Entails datatypeMap inp.toOntology [rankedQueryAxiom q] ∧
      ¬ Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) := fun hno =>
    ⟨fun i hm => (hno ⟨i, hm⟩).elim, fun hs => hno (hsubSat hs)⟩
  have hentSat : Satisfiable datatypeMap inp.toOntology →
      Entails datatypeMap inp.toOntology [rankedQueryAxiom q] →
      Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) := by
    rintro ⟨i, hm⟩ he
    obtain ⟨assign, hsatO⟩ := hm
    obtain ⟨assign', hsatQ⟩ := he i ⟨assign, hsatO⟩
    have hqI := (gradedInclusion_withAnonymous i assign' (RankedBridge.gradedInclusion q)).mp
      (hsatQ _ (List.mem_singleton_self _))
    have hqA := (gradedInclusion_withAnonymous i assign (RankedBridge.gradedInclusion q)).mpr hqI
    exact ⟨i, assign, fun ax hax => (List.mem_cons.mp hax).elim (fun e => e ▸ hqA) (hsatO ax)⟩
  cases h1 : decideRankedConcept inp (.conj q.sub (.neg q.sup)) with
  | model cpool =>
    have hcsat : RankedBridge.conceptSat datatypeMap inp.rules inp.chains inp.tbox (.conj q.sub (.neg q.sup)) :=
      hcMod.mp ⟨cpool, h1⟩
    have hontSat : Satisfiable datatypeMap inp.toOntology := hsatOfCounter hcsat
    have hnotEnt : ¬ Entails datatypeMap inp.toOntology [rankedQueryAxiom q] := fun he => hent.mp he hcsat
    cases h2 : Sabrina.RoleChains.RankedPaths.search inp.rank inp.rules inp.chains (q :: inp.tbox) .top with
    | model ipool =>
      have hisat : Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) :=
        hqsat.mp (hiMod.mp ⟨ipool, h2⟩)
      simp [decideRankedInclusion, h1, h2, hontSat, hnotEnt, hisat]
    | refutation irounds =>
      have hiunsat : ¬ Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) :=
        fun hs => hiRef.mp ⟨irounds, h2⟩ (hqsat.mpr hs)
      simp [decideRankedInclusion, h1, h2, hontSat, hnotEnt, hiunsat]
  | refutation crounds =>
    have hEnt : Entails datatypeMap inp.toOntology [rankedQueryAxiom q] :=
      hent.mpr (hcRef.mp ⟨crounds, h1⟩)
    cases h2 : Sabrina.RoleChains.RankedPaths.search inp.rank inp.rules inp.chains (q :: inp.tbox) .top with
    | model ipool =>
      have hisat : Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) :=
        hqsat.mp (hiMod.mp ⟨ipool, h2⟩)
      have hontSat : Satisfiable datatypeMap inp.toOntology := hsubSat hisat
      simp [decideRankedInclusion, h1, h2, hontSat, hEnt, hisat]
    | refutation irounds =>
      have hiunsat : ¬ Satisfiable datatypeMap (rankedQueryAxiom q :: inp.toOntology) :=
        fun hs => hiRef.mp ⟨irounds, h2⟩ (hqsat.mpr hs)
      have hontUnsat : ¬ Satisfiable datatypeMap inp.toOntology :=
        fun hs => hiunsat (hentSat hs hEnt)
      simp [decideRankedInclusion, h1, h2, hontUnsat, hEnt, hiunsat]

end Sabrina.OWL2.DecisionProcedure
