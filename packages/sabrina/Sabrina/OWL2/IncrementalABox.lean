import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.DirectSemantics
import Sabrina.OWL2.EL
import Sabrina.OWL2.Datatypes

/-! Kernel-verified Incremental ABox Inference over EL++ TBoxes/RBoxes.

    Separates one-time TBox/RBox compilation and saturation (`CompiledEL`) from
    mutable ABox state (`IncrementalABoxState`), supporting:
      * Incremental ABox assertion (`assertFact`) propagating only new facts
        against the pre-saturated TBox/RBox in polynomial time.
      * Incremental ABox retraction (`retractId`) via justification-tracked
        Delete-and-Rederive (DRed): invalidates ONLY derived proofs whose
        provenance set references the retracted assertion ID, then re-derives
        any facts still supported by surviving assertions.
      * Kernel-checked soundness and incremental preservation theorems
        (0 `sorry`, strictly standard Lean core axioms):
        - `checkABoxProof_sound`
        - `checkABoxProof_mono_add`
        - `checkABoxProof_retract_preserve`
        - `checkABoxModel_sound` -/

namespace Sabrina.OWL2.IncrementalABox

open Sabrina.OWL2 Sabrina.OWL2.EL

/-! ### Ground ABox Facts, Goals, and Provenance-Tracked Proof Certificates -/

inductive ABoxFact where
  | cls (c a : IRI)
  | obj (r a b : IRI)
  | negObj (r a b : IRI)
  deriving DecidableEq, Repr

def ABoxFact.toAxiom : ABoxFact → Axiom
  | .cls c a => .classAssertion (.named c) (.named a)
  | .obj r a b => .objectAssertion (.named r) (.named a) (.named b)
  | .negObj r a b => .negativeObjectAssertion (.named r) (.named a) (.named b)

abbrev TaggedFact := Nat × ABoxFact

def aboxOntology (abox : List TaggedFact) : Ontology :=
  abox.map (fun tf => tf.2.toAxiom)

inductive ABoxGoal where
  | inst (c a : IRI)
  | edge (r a b : IRI)
  | clash
  deriving DecidableEq, Repr

def aboxGoalHolds {d : DatatypeMap} (i : Interpretation d) : ABoxGoal → Prop
  | .inst c a => i.classes c (i.individuals (.named a))
  | .edge r a b => i.objectProperties r (i.individuals (.named a)) (i.individuals (.named b))
  | .clash => False

inductive ABoxProof where
  | givenCls (id : Nat) (c a : IRI)
  | givenObj (id : Nat) (r a b : IRI)
  | topInst (a : IRI)
  | botClash (a : IRI) (pBot : ABoxProof)
  | negObjClash (id : Nat) (r a b : IRI) (pEdge : ABoxProof)
  | tboxSub (c1 c2 a : IRI) (pTBox : ELProof) (pInst : ABoxProof)
  | sub1Step (c1 c2 a : IRI) (p : ABoxProof)
  | sub2Step (c1 c2 c3 a : IRI) (p1 p2 : ABoxProof)
  | existLStep (r c1 c2 a b : IRI) (pEdge pCls : ABoxProof)
  | roleSubStep (r s a b : IRI) (p : ABoxProof)
  | roleChainStep (r1 r2 s a b c : IRI) (p1 p2 : ABoxProof)
  | roleReflStep (r a : IRI)
  deriving DecidableEq, Repr

/-- Exact provenance check: returns `true` iff `pf` depends on ABox assertion `targetId`. -/
def ABoxProof.usesId (targetId : Nat) : ABoxProof → Bool
  | .givenCls id _ _ => id == targetId
  | .givenObj id _ _ _ => id == targetId
  | .topInst _ | .roleReflStep _ _ => false
  | .botClash _ p | .tboxSub _ _ _ _ p | .sub1Step _ _ _ p | .roleSubStep _ _ _ _ p => p.usesId targetId
  | .negObjClash id _ _ _ p => id == targetId || p.usesId targetId
  | .sub2Step _ _ _ _ p1 p2 | .existLStep _ _ _ _ _ p1 p2 | .roleChainStep _ _ _ _ _ _ p1 p2 =>
    p1.usesId targetId || p2.usesId targetId

def ABoxProof.size : ABoxProof → Nat
  | .givenCls _ _ _ | .givenObj _ _ _ _ | .topInst _ | .roleReflStep _ _ => 1
  | .botClash _ p | .negObjClash _ _ _ _ p | .tboxSub _ _ _ _ p
  | .sub1Step _ _ _ p | .roleSubStep _ _ _ _ p => 1 + p.size
  | .sub2Step _ _ _ _ p1 p2 | .existLStep _ _ _ _ _ p1 p2 | .roleChainStep _ _ _ _ _ _ p1 p2 =>
    1 + p1.size + p2.size

def checkABoxProof (tbox : List ELAxiom) (abox : List TaggedFact) : ABoxProof → ABoxGoal → Bool
  | .givenCls id c a, g =>
    decide (g = .inst c a) && abox.contains (id, .cls c a)
  | .givenObj id r a b, g =>
    decide (g = .edge r a b) && abox.contains (id, .obj r a b)
  | .topInst a, g =>
    decide (g = .inst thing a)
  | .botClash a pBot, g =>
    decide (g = .clash) && checkABoxProof tbox abox pBot (.inst nothing a)
  | .negObjClash id r a b pEdge, g =>
    decide (g = .clash) && abox.contains (id, .negObj r a b) && checkABoxProof tbox abox pEdge (.edge r a b)
  | .tboxSub c1 c2 a pTBox pInst, g =>
    decide (g = .inst c2 a) && checkELProof tbox pTBox (.sub c1 c2) && checkABoxProof tbox abox pInst (.inst c1 a)
  | .sub1Step c1 c2 a p, g =>
    decide (g = .inst c2 a) && tbox.contains (.sub1 c1 c2) && checkABoxProof tbox abox p (.inst c1 a)
  | .sub2Step c1 c2 c3 a p1 p2, g =>
    decide (g = .inst c3 a) && tbox.contains (.sub2 c1 c2 c3) &&
      checkABoxProof tbox abox p1 (.inst c1 a) && checkABoxProof tbox abox p2 (.inst c2 a)
  | .existLStep r c1 c2 a b pEdge pCls, g =>
    decide (g = .inst c2 a) && tbox.contains (.existL r c1 c2) &&
      checkABoxProof tbox abox pEdge (.edge r a b) && checkABoxProof tbox abox pCls (.inst c1 b)
  | .roleSubStep r s a b p, g =>
    decide (g = .edge s a b) && tbox.contains (.roleSub r s) && checkABoxProof tbox abox p (.edge r a b)
  | .roleChainStep r1 r2 s a b c p1 p2, g =>
    decide (g = .edge s a c) && tbox.contains (.roleChain r1 r2 s) &&
      checkABoxProof tbox abox p1 (.edge r1 a b) && checkABoxProof tbox abox p2 (.edge r2 b c)
  | .roleReflStep r a, g =>
    decide (g = .edge r a a) && tbox.contains (.roleRefl r)

/-! ### Kernel Soundness & Incremental Monotonicity / Retraction Theorems -/

theorem checkABoxProof_sound {d : DatatypeMap} {tbox : List ELAxiom} {abox : List TaggedFact}
    {pf : ABoxProof} {g : ABoxGoal}
    (hchk : checkABoxProof tbox abox pf g = true)
    {i : Interpretation d}
    (htbox : satisfies i (elOntology tbox))
    (habox : satisfies i (aboxOntology abox)) :
    aboxGoalHolds i g := by
  induction pf generalizing g with
  | givenCls id c a =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨rfl, hmem⟩ := hchk
    exact habox (ABoxFact.cls c a).toAxiom (List.mem_map_of_mem (f := fun tf : TaggedFact => tf.2.toAxiom) hmem)
  | givenObj id r a b =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨rfl, hmem⟩ := hchk
    exact habox (ABoxFact.obj r a b).toAxiom (List.mem_map_of_mem (f := fun tf : TaggedFact => tf.2.toAxiom) hmem)
  | topInst a =>
    simp only [checkABoxProof, decide_eq_true_eq] at hchk; subst hchk
    exact i.thingExt _
  | botClash a pBot ih =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨rfl, h1⟩ := hchk
    exact i.nothingExt _ (ih h1)
  | negObjClash id r a b pEdge ih =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hchk
    have hneg := habox (ABoxFact.negObj r a b).toAxiom (List.mem_map_of_mem (f := fun tf : TaggedFact => tf.2.toAxiom) hmem)
    exact hneg (ih h1)
  | tboxSub c1 c2 a pTBox pInst ih =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨rfl, htb⟩, h1⟩ := hchk
    exact checkELProof_sound htb htbox _ (ih h1)
  | sub1Step c1 c2 a p ih =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hchk
    exact htbox (ELAxiom.sub1 c1 c2).toAxiom (List.mem_map_of_mem hmem) _ (ih h1)
  | sub2Step c1 c2 c3 a p1 p2 ih1 ih2 =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hchk
    exact htbox (ELAxiom.sub2 c1 c2 c3).toAxiom (List.mem_map_of_mem hmem) _ ⟨ih1 h1, ih2 h2⟩
  | existLStep r c1 c2 a b pEdge pCls ih1 ih2 =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hchk
    exact htbox (ELAxiom.existL r c1 c2).toAxiom (List.mem_map_of_mem hmem) _ ⟨_, ih1 h1, ih2 h2⟩
  | roleSubStep r s a b p ih =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hchk
    exact htbox (ELAxiom.roleSub r s).toAxiom (List.mem_map_of_mem hmem) _ _ (ih h1)
  | roleChainStep r1 r2 s a b c p1 p2 ih1 ih2 =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hchk
    exact htbox (ELAxiom.roleChain r1 r2 s).toAxiom (List.mem_map_of_mem hmem) _ _ ⟨_, ih1 h1, _, ih2 h2, rfl⟩
  | roleReflStep r a =>
    simp only [checkABoxProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
    obtain ⟨rfl, hmem⟩ := hchk
    exact htbox (ELAxiom.roleRefl r).toAxiom (List.mem_map_of_mem hmem) _

theorem checkABoxProof_entails_cls {d : DatatypeMap} {tbox : List ELAxiom} {abox : List TaggedFact}
    {pf : ABoxProof} {c a : IRI}
    (hchk : checkABoxProof tbox abox pf (.inst c a) = true) :
    Entails d (elOntology tbox ++ aboxOntology abox) [.classAssertion (.named c) (.named a)] := by
  intro i ⟨assign, hsat⟩
  refine ⟨assign, fun q hq => ?_⟩
  rcases List.mem_singleton.mp hq with rfl
  exact checkABoxProof_sound hchk
    (fun ax hax => hsat ax (List.mem_append_left _ hax))
    (fun ax hax => hsat ax (List.mem_append_right _ hax))

theorem checkABoxProof_entails_obj {d : DatatypeMap} {tbox : List ELAxiom} {abox : List TaggedFact}
    {pf : ABoxProof} {r a b : IRI}
    (hchk : checkABoxProof tbox abox pf (.edge r a b) = true) :
    Entails d (elOntology tbox ++ aboxOntology abox) [.objectAssertion (.named r) (.named a) (.named b)] := by
  intro i ⟨assign, hsat⟩
  refine ⟨assign, fun q hq => ?_⟩
  rcases List.mem_singleton.mp hq with rfl
  exact checkABoxProof_sound hchk
    (fun ax hax => hsat ax (List.mem_append_left _ hax))
    (fun ax hax => hsat ax (List.mem_append_right _ hax))

theorem checkABoxProof_inconsistent {d : DatatypeMap} {tbox : List ELAxiom} {abox : List TaggedFact}
    {pf : ABoxProof}
    (hchk : checkABoxProof tbox abox pf .clash = true) :
    ¬ Satisfiable d (elOntology tbox ++ aboxOntology abox) := by
  rintro ⟨i, assign, hsat⟩
  exact checkABoxProof_sound hchk
    (fun ax hax => hsat ax (List.mem_append_left _ hax))
    (fun ax hax => hsat ax (List.mem_append_right _ hax))

/-- **Incremental Addition Monotonicity**: adding a new ABox assertion never
    invalidates any previously checked `ABoxProof`. -/
theorem checkABoxProof_mono_add {tbox : List ELAxiom} {abox : List TaggedFact}
    {tf : TaggedFact} {pf : ABoxProof} {g : ABoxGoal}
    (hchk : checkABoxProof tbox abox pf g = true) :
    checkABoxProof tbox (tf :: abox) pf g = true := by
  induction pf generalizing g with
  | givenCls id c a =>
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem] at hchk ⊢
    exact ⟨hchk.1, List.mem_cons_of_mem _ hchk.2⟩
  | givenObj id r a b =>
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem] at hchk ⊢
    exact ⟨hchk.1, List.mem_cons_of_mem _ hchk.2⟩
  | topInst a | roleReflStep r a => exact hchk
  | botClash a p ih =>
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨hchk.1, ih hchk.2⟩
  | negObjClash id r a b p ih =>
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem] at hchk ⊢
    exact ⟨⟨hchk.1.1, List.mem_cons_of_mem _ hchk.1.2⟩, ih hchk.2⟩
  | tboxSub c1 c2 a pT pI ih | sub1Step c1 c2 a pI ih | roleSubStep r s a b pI ih =>
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨hchk.1, ih hchk.2⟩
  | sub2Step _ _ _ _ p1 p2 ih1 ih2 | existLStep _ _ _ _ _ p1 p2 ih1 ih2
  | roleChainStep _ _ _ _ _ _ p1 p2 ih1 ih2 =>
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨⟨hchk.1.1, ih1 hchk.1.2⟩, ih2 hchk.2⟩

/-- **Incremental DRed Retraction Preservation**: retracting assertion `targetId`
    from `abox` preserves EVERY previously checked `ABoxProof` that does not
    depend on `targetId` (`pf.usesId targetId = false`). -/
theorem checkABoxProof_retract_preserve {tbox : List ELAxiom} {abox : List TaggedFact}
    {targetId : Nat} {pf : ABoxProof} {g : ABoxGoal}
    (hchk : checkABoxProof tbox abox pf g = true)
    (hunused : pf.usesId targetId = false) :
    checkABoxProof tbox (abox.filter fun tf => tf.1 != targetId) pf g = true := by
  induction pf generalizing g with
  | givenCls id c a =>
    simp only [ABoxProof.usesId, beq_eq_false_iff_ne] at hunused
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem, List.mem_filter, bne_iff_ne] at hchk ⊢
    exact ⟨hchk.1, hchk.2, hunused⟩
  | givenObj id r a b =>
    simp only [ABoxProof.usesId, beq_eq_false_iff_ne] at hunused
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem, List.mem_filter, bne_iff_ne] at hchk ⊢
    exact ⟨hchk.1, hchk.2, hunused⟩
  | topInst a | roleReflStep r a => exact hchk
  | botClash a p ih =>
    simp only [ABoxProof.usesId] at hunused
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨hchk.1, ih hchk.2 hunused⟩
  | negObjClash id r a b p ih =>
    simp only [ABoxProof.usesId, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hunused
    simp only [checkABoxProof, Bool.and_eq_true, List.contains_iff_mem, List.mem_filter, bne_iff_ne] at hchk ⊢
    exact ⟨⟨hchk.1.1, hchk.1.2, hunused.1⟩, ih hchk.2 hunused.2⟩
  | tboxSub c1 c2 a pT pI ih | sub1Step c1 c2 a pI ih | roleSubStep r s a b pI ih =>
    simp only [ABoxProof.usesId] at hunused
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨hchk.1, ih hchk.2 hunused⟩
  | sub2Step _ _ _ _ p1 p2 ih1 ih2 | existLStep _ _ _ _ _ p1 p2 ih1 ih2
  | roleChainStep _ _ _ _ _ _ p1 p2 ih1 ih2 =>
    simp only [ABoxProof.usesId, Bool.or_eq_false_iff] at hunused
    simp only [checkABoxProof, Bool.and_eq_true] at hchk ⊢
    exact ⟨⟨hchk.1.1, ih1 hchk.1.2 hunused.1⟩, ih2 hchk.2 hunused.2⟩

/-! ### Kernel-Checked Finite Model for EL++ TBox + Ground ABox (`ABoxModel`) -/

structure ABoxModel where
  base : ELModel
  indMap : List (IRI × IRI)   -- named individual IRI ↦ node IRI in base.nodes
  deriving DecidableEq, Repr

def ABoxModel.resolveInd (m : ABoxModel) (a : IRI) : Option IRI :=
  (m.indMap.find? fun p => p.1 == a).map Prod.snd

def ABoxModel.checkFact (m : ABoxModel) : ABoxFact → Bool
  | .cls c a => match m.resolveInd a with
    | some u => m.base.nodes.contains u && m.base.hasCls c u
    | none => false
  | .obj r a b => match m.resolveInd a, m.resolveInd b with
    | some u, some v => m.base.nodes.contains u && m.base.nodes.contains v && m.base.hasEdge r u v
    | _, _ => false
  | .negObj r a b => match m.resolveInd a, m.resolveInd b with
    | some u, some v => m.base.nodes.contains u && m.base.nodes.contains v && !m.base.hasEdge r u v
    | _, _ => false

def checkABoxModel (tbox : List ELAxiom) (abox : List TaggedFact) (m : ABoxModel) : Bool :=
  checkELModel tbox m.base && abox.all (fun tf => m.checkFact tf.2)

def ABoxModel.toInterpretation (m : ABoxModel) (hne : m.base.nodes ≠ []) :
    Interpretation Datatypes.datatypeMap :=
  let baseI := m.base.toInterpretation hne
  let fallback : { u : IRI // u ∈ m.base.nodes } := baseI.individuals (.named "")
  { baseI with
    individuals := fun
      | .named a =>
        match m.resolveInd a with
        | some u => if hmem : u ∈ m.base.nodes then ⟨u, hmem⟩ else fallback
        | none => fallback
      | .anonymous _ _ => fallback
    namedIndividual := fun _ => trivial }

private theorem aboxModel_ind_val (m : ABoxModel) (hne : m.base.nodes ≠ []) {a u : IRI}
    (hres : m.resolveInd a = some u) (hmem : u ∈ m.base.nodes) :
    ((m.toInterpretation hne).individuals (.named a)).val = u := by
  change (match m.resolveInd a with
    | some u => if hmem : u ∈ m.base.nodes then (⟨u, hmem⟩ : { w : IRI // w ∈ m.base.nodes }) else _
    | none => _).val = u
  simp [hres, hmem]

private theorem aboxModel_elAxiom_eq (m : ABoxModel) (hne : m.base.nodes ≠ []) (ea : ELAxiom) :
    axiomHolds (m.toInterpretation hne) ea.toAxiom =
    axiomHolds (m.base.toInterpretation hne) ea.toAxiom := by
  cases ea <;> rfl

theorem checkABoxModel_sound {tbox : List ELAxiom} {abox : List TaggedFact} {m : ABoxModel}
    (hchk : checkABoxModel tbox abox m = true) :
    ∃ hne : m.base.nodes ≠ [],
      satisfies (m.toInterpretation hne) (elOntology tbox ++ aboxOntology abox) := by
  simp only [checkABoxModel, Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hne, htb⟩ := checkELModel_sound hchk.1
  refine ⟨hne, fun ax hax => ?_⟩
  rcases List.mem_append.mp hax with h1 | h2
  · obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp h1
    rw [aboxModel_elAxiom_eq]
    exact htb ea.toAxiom (List.mem_map_of_mem hea)
  · obtain ⟨tf, htf, rfl⟩ := List.mem_map.mp h2
    have hfact := hchk.2 tf htf
    cases h : tf.2 with
    | cls c a =>
      rw [h] at hfact
      simp only [ABoxModel.checkFact] at hfact
      cases hres : m.resolveInd a with
      | none => simp [hres] at hfact
      | some u =>
        simp only [hres, Bool.and_eq_true, List.contains_iff_mem] at hfact
        change m.base.hasCls c ((m.toInterpretation hne).individuals (.named a)).val = true
        rw [aboxModel_ind_val m hne hres hfact.1]
        exact hfact.2
    | obj r a b =>
      rw [h] at hfact
      simp only [ABoxModel.checkFact] at hfact
      cases hres1 : m.resolveInd a with
      | none => simp [hres1] at hfact
      | some u =>
        cases hres2 : m.resolveInd b with
        | none => simp [hres1, hres2] at hfact
        | some v =>
          simp only [hres1, hres2, Bool.and_eq_true, List.contains_iff_mem] at hfact
          change m.base.hasEdge r ((m.toInterpretation hne).individuals (.named a)).val
            ((m.toInterpretation hne).individuals (.named b)).val = true
          rw [aboxModel_ind_val m hne hres1 hfact.1.1, aboxModel_ind_val m hne hres2 hfact.1.2]
          exact hfact.2
    | negObj r a b =>
      rw [h] at hfact
      simp only [ABoxModel.checkFact] at hfact
      cases hres1 : m.resolveInd a with
      | none => simp [hres1] at hfact
      | some u =>
        cases hres2 : m.resolveInd b with
        | none => simp [hres1, hres2] at hfact
        | some v =>
          simp only [hres1, hres2, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hfact
          change ¬ (m.base.hasEdge r ((m.toInterpretation hne).individuals (.named a)).val
            ((m.toInterpretation hne).individuals (.named b)).val = true)
          rw [aboxModel_ind_val m hne hres1 hfact.1.1, aboxModel_ind_val m hne hres2 hfact.1.2]
          simp [hfact.2]

theorem checkABoxModel_counter_cls {tbox : List ELAxiom} {abox : List TaggedFact} {m : ABoxModel}
    {c a u : IRI}
    (hchk : checkABoxModel tbox abox m = true)
    (hres : m.resolveInd a = some u) (hu : u ∈ m.base.nodes) (hc : m.base.hasCls c u = false) :
    ¬ Entails Datatypes.datatypeMap (elOntology tbox ++ aboxOntology abox)
        [.classAssertion (.named c) (.named a)] := by
  obtain ⟨hne, hsat⟩ := checkABoxModel_sound hchk
  intro hent
  obtain ⟨assign, hq⟩ := hent (m.toInterpretation hne) (satisfies_models hsat)
  have hmem := hq (.classAssertion (.named c) (.named a)) (List.mem_singleton_self _)
  change m.base.hasCls c ((m.toInterpretation hne).individuals (.named a)).val = true at hmem
  rw [aboxModel_ind_val m hne hres hu, hc] at hmem
  exact Bool.false_ne_true hmem

/-! ### Compiled EL++ TBox Snapshot & Live Incremental DRed Engine -/

structure CompiledEL where
  tbox : List ELAxiom
  tboxSat : ELSaturation
  tboxSubByA : Std.HashMap IRI (List (IRI × ELProof))
  sub1ByA : Std.HashMap IRI (List IRI)
  sub2ByA1 : Std.HashMap IRI (List (IRI × IRI))
  sub2ByA2 : Std.HashMap IRI (List (IRI × IRI))
  existLByRA : Std.HashMap (IRI × IRI) (List IRI)
  roleSubByR : Std.HashMap IRI (List IRI)
  chainByR1 : Std.HashMap IRI (List (IRI × IRI))
  chainByR2 : Std.HashMap IRI (List (IRI × IRI))
  reflRoles : List IRI

/-- One-time TBox+RBox compilation and polynomial EL++ saturation. -/
def compileEL (tbox : List ELAxiom) : CompiledEL := Id.run do
  let tboxSat := saturateEL tbox []
  let mut tboxSubByA : Std.HashMap IRI (List (IRI × ELProof)) := {}
  for ((a, b), pf) in tboxSat.subProofs.toList do
    if a != b && b != thing then
      tboxSubByA := tboxSubByA.insert a ((b, pf) :: tboxSubByA.getD a [])
  let mut sub1ByA : Std.HashMap IRI (List IRI) := {}
  let mut sub2ByA1 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut sub2ByA2 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut existLByRA : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut roleSubByR : Std.HashMap IRI (List IRI) := {}
  let mut chainByR1 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut chainByR2 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut reflRoles : List IRI := []
  for ax in tbox do
    match ax with
    | .sub1 a b => sub1ByA := sub1ByA.insert a (b :: sub1ByA.getD a [])
    | .sub2 a1 a2 b =>
      sub2ByA1 := sub2ByA1.insert a1 ((a2, b) :: sub2ByA1.getD a1 [])
      sub2ByA2 := sub2ByA2.insert a2 ((a1, b) :: sub2ByA2.getD a2 [])
    | .existL r a b => existLByRA := existLByRA.insert (r, a) (b :: existLByRA.getD (r, a) [])
    | .roleSub r s => roleSubByR := roleSubByR.insert r (s :: roleSubByR.getD r [])
    | .roleChain r1 r2 s =>
      chainByR1 := chainByR1.insert r1 ((r2, s) :: chainByR1.getD r1 [])
      chainByR2 := chainByR2.insert r2 ((r1, s) :: chainByR2.getD r2 [])
    | .roleRefl r => reflRoles := r :: reflRoles
    | .existR _ _ _ => pure ()
  return {
    tbox, tboxSat, tboxSubByA, sub1ByA, sub2ByA1, sub2ByA2,
    existLByRA, roleSubByR, chainByR1, chainByR2, reflRoles
  }

structure IncrementalState where
  compiled : CompiledEL
  activeFacts : List TaggedFact := []
  individuals : Std.HashSet IRI := {}
  derivedCls : Std.HashMap (IRI × IRI) ABoxProof := {}        -- (a, c) ↦ proof of inst c a
  derivedRel : Std.HashMap (IRI × IRI × IRI) ABoxProof := {}  -- (r, a, b) ↦ proof of edge r a b
  negObjs : Std.HashMap (IRI × IRI × IRI) Nat := {}           -- (r, a, b) ↦ assertion id
  clashProof : Option ABoxProof := none

def IncrementalState.init (compiled : CompiledEL) : IncrementalState :=
  { compiled }

/-- Propagate a queue of newly inserted class/edge seeds incrementally against
    `st.compiled` and existing derived facts, returning updated state and count
    of newly derived facts. -/
private def propagateDelta (st : IncrementalState)
    (initCls : Array (IRI × IRI)) (initRel : Array (IRI × IRI × IRI)) :
    IncrementalState × Nat := Id.run do
  let c := st.compiled
  let mut derivedCls := st.derivedCls
  let mut derivedRel := st.derivedRel
  let mut clashProof := st.clashProof
  let mut clsQueue := initCls
  let mut relQueue := initRel
  let mut newCount : Nat := 0

  -- Build lightweight local adjacency over current derivedRel & derivedCls for fast joins
  let mut incomingRel : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut outgoingByR : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut incomingByR : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut clsByInd : Std.HashMap IRI (List IRI) := {}
  for ((r, a, b), _) in derivedRel.toList do
    incomingRel := incomingRel.insert b ((r, a) :: incomingRel.getD b [])
    outgoingByR := outgoingByR.insert (r, a) (b :: outgoingByR.getD (r, a) [])
    incomingByR := incomingByR.insert (r, b) (a :: incomingByR.getD (r, b) [])
  for ((a, cl), _) in derivedCls.toList do
    clsByInd := clsByInd.insert a (cl :: clsByInd.getD a [])

  let mut ci : Nat := 0
  let mut ri : Nat := 0
  while ci < clsQueue.size || ri < relQueue.size do
    while ci < clsQueue.size do
      let (a, cl) := clsQueue[ci]!
      ci := ci + 1
      let some pCl := derivedCls.get? (a, cl) | continue
      if cl == nothing && clashProof.isNone then
        clashProof := some (.botClash a pCl)
      -- 1. Pre-saturated TBox consequences (includes existR+existL+roleChain TBox chains in O(1)!)
      for (sup, pTBox) in c.tboxSubByA.getD cl [] do
        if !derivedCls.contains (a, sup) then
          derivedCls := derivedCls.insert (a, sup) (.tboxSub cl sup a pTBox pCl)
          clsByInd := clsByInd.insert a (sup :: clsByInd.getD a [])
          clsQueue := clsQueue.push (a, sup)
          newCount := newCount + 1
      -- 2. Direct sub1
      for sup in c.sub1ByA.getD cl [] do
        if !derivedCls.contains (a, sup) then
          derivedCls := derivedCls.insert (a, sup) (.sub1Step cl sup a pCl)
          clsByInd := clsByInd.insert a (sup :: clsByInd.getD a [])
          clsQueue := clsQueue.push (a, sup)
          newCount := newCount + 1
      -- 3. Conjunctions (sub2)
      for (c2, sup) in c.sub2ByA1.getD cl [] do
        if let some p2 := derivedCls.get? (a, c2) then
          if !derivedCls.contains (a, sup) then
            derivedCls := derivedCls.insert (a, sup) (.sub2Step cl c2 sup a pCl p2)
            clsByInd := clsByInd.insert a (sup :: clsByInd.getD a [])
            clsQueue := clsQueue.push (a, sup)
            newCount := newCount + 1
      for (c1, sup) in c.sub2ByA2.getD cl [] do
        if let some p1 := derivedCls.get? (a, c1) then
          if !derivedCls.contains (a, sup) then
            derivedCls := derivedCls.insert (a, sup) (.sub2Step c1 cl sup a p1 pCl)
            clsByInd := clsByInd.insert a (sup :: clsByInd.getD a [])
            clsQueue := clsQueue.push (a, sup)
            newCount := newCount + 1
      -- 4. Existential LHS triggered by new class fact on target `a`
      for (r, src) in incomingRel.getD a [] do
        if let some pEdge := derivedRel.get? (r, src, a) then
          for sup in c.existLByRA.getD (r, cl) [] do
            if !derivedCls.contains (src, sup) then
              derivedCls := derivedCls.insert (src, sup) (.existLStep r cl sup src a pEdge pCl)
              clsByInd := clsByInd.insert src (sup :: clsByInd.getD src [])
              clsQueue := clsQueue.push (src, sup)
              newCount := newCount + 1
    while ri < relQueue.size do
      let (r, a, b) := relQueue[ri]!
      ri := ri + 1
      let some pEdge := derivedRel.get? (r, a, b) | continue
      if let some negId := st.negObjs.get? (r, a, b) then
        if clashProof.isNone then
          clashProof := some (.negObjClash negId r a b pEdge)
      -- 5. Existential LHS triggered by new edge (r, a, b)
      for cl in clsByInd.getD b [] do
        if let some pCl := derivedCls.get? (b, cl) then
          for sup in c.existLByRA.getD (r, cl) [] do
            if !derivedCls.contains (a, sup) then
              derivedCls := derivedCls.insert (a, sup) (.existLStep r cl sup a b pEdge pCl)
              clsByInd := clsByInd.insert a (sup :: clsByInd.getD a [])
              clsQueue := clsQueue.push (a, sup)
              newCount := newCount + 1
      -- 6. Subrole
      for s in c.roleSubByR.getD r [] do
        if !derivedRel.contains (s, a, b) then
          derivedRel := derivedRel.insert (s, a, b) (.roleSubStep r s a b pEdge)
          incomingRel := incomingRel.insert b ((s, a) :: incomingRel.getD b [])
          outgoingByR := outgoingByR.insert (s, a) (b :: outgoingByR.getD (s, a) [])
          incomingByR := incomingByR.insert (s, b) (a :: incomingByR.getD (s, b) [])
          relQueue := relQueue.push (s, a, b)
          newCount := newCount + 1
      -- 7. Role chains (left and right legs)
      for (r2, s) in c.chainByR1.getD r [] do
        for dst in outgoingByR.getD (r2, b) [] do
          if let some p2 := derivedRel.get? (r2, b, dst) then
            if !derivedRel.contains (s, a, dst) then
              derivedRel := derivedRel.insert (s, a, dst) (.roleChainStep r r2 s a b dst pEdge p2)
              incomingRel := incomingRel.insert dst ((s, a) :: incomingRel.getD dst [])
              outgoingByR := outgoingByR.insert (s, a) (dst :: outgoingByR.getD (s, a) [])
              incomingByR := incomingByR.insert (s, dst) (a :: incomingByR.getD (s, dst) [])
              relQueue := relQueue.push (s, a, dst)
              newCount := newCount + 1
      for (r1, s) in c.chainByR2.getD r [] do
        for src in incomingByR.getD (r1, a) [] do
          if let some p1 := derivedRel.get? (r1, src, a) then
            if !derivedRel.contains (s, src, b) then
              derivedRel := derivedRel.insert (s, src, b) (.roleChainStep r1 r s src a b p1 pEdge)
              incomingRel := incomingRel.insert b ((s, src) :: incomingRel.getD b [])
              outgoingByR := outgoingByR.insert (s, src) (b :: outgoingByR.getD (s, src) [])
              incomingByR := incomingByR.insert (s, b) (src :: incomingByR.getD (s, b) [])
              relQueue := relQueue.push (s, src, b)
              newCount := newCount + 1
  return ({ st with derivedCls, derivedRel, clashProof }, newCount)

private def registerIndividual (st : IncrementalState) (a : IRI)
    (clsQ : Array (IRI × IRI)) (relQ : Array (IRI × IRI × IRI)) :
    IncrementalState × Array (IRI × IRI) × Array (IRI × IRI × IRI) := Id.run do
  if st.individuals.contains a then return (st, clsQ, relQ)
  let mut individuals := st.individuals.insert a
  let mut derivedCls := st.derivedCls
  let mut derivedRel := st.derivedRel
  let mut cq := clsQ
  let mut rq := relQ
  if !derivedCls.contains (a, thing) then
    derivedCls := derivedCls.insert (a, thing) (.topInst a)
    cq := cq.push (a, thing)
  for r in st.compiled.reflRoles do
    if !derivedRel.contains (r, a, a) then
      derivedRel := derivedRel.insert (r, a, a) (.roleReflStep r a)
      rq := rq.push (r, a, a)
  return ({ st with individuals, derivedCls, derivedRel }, cq, rq)

/-- Incrementally assert a tagged ground ABox fact without re-compiling the TBox.
    Returns `(newState, newlyDerivedCount)`. -/
def IncrementalState.assertFact (st : IncrementalState) (id : Nat) (f : ABoxFact) :
    IncrementalState × Nat := Id.run do
  let mut st' := { st with activeFacts := (id, f) :: st.activeFacts }
  let mut cq : Array (IRI × IRI) := #[]
  let mut rq : Array (IRI × IRI × IRI) := #[]
  match f with
  | .cls c a =>
    let (s1, c1, r1) := registerIndividual st' a cq rq
    st' := s1; cq := c1; rq := r1
    if !st'.derivedCls.contains (a, c) then
      st' := { st' with derivedCls := st'.derivedCls.insert (a, c) (.givenCls id c a) }
      cq := cq.push (a, c)
  | .obj r a b =>
    let (s1, c1, r1) := registerIndividual st' a cq rq
    let (s2, c2, r2) := registerIndividual s1 b c1 r1
    st' := s2; cq := c2; rq := r2
    if !st'.derivedRel.contains (r, a, b) then
      st' := { st' with derivedRel := st'.derivedRel.insert (r, a, b) (.givenObj id r a b) }
      rq := rq.push (r, a, b)
  | .negObj r a b =>
    let (s1, c1, r1) := registerIndividual st' a cq rq
    let (s2, c2, r2) := registerIndividual s1 b c1 r1
    st' := { s2 with negObjs := s2.negObjs.insert (r, a, b) id }; cq := c2; rq := r2
    if let some pEdge := st'.derivedRel.get? (r, a, b) then
      if st'.clashProof.isNone then
        st' := { st' with clashProof := some (.negObjClash id r a b pEdge) }
  return propagateDelta st' cq rq

/-- Incrementally retract assertion `targetId` using Delete-and-Rederive (DRed):
    1. **Delete**: remove ONLY derived facts whose `ABoxProof` uses `targetId`
       (all unaffected derivations remain formally valid by `checkABoxProof_retract_preserve`).
    2. **Rederive**: seed from surviving active facts & surviving neighbors to
       re-derive any invalidated fact that still has an alternative support path.
    Returns `(newState, invalidatedCount, rederivedCount)`. -/
def IncrementalState.retractId (st : IncrementalState) (targetId : Nat) :
    IncrementalState × Nat × Nat := Id.run do
  let remaining := st.activeFacts.filter fun tf => tf.1 != targetId
  -- 1. Delete phase: keep all proofs with `!(pf.usesId targetId)`
  let mut keptCls : Std.HashMap (IRI × IRI) ABoxProof := {}
  let mut invalidated : Nat := 0
  for (k, pf) in st.derivedCls.toList do
    if pf.usesId targetId then
      invalidated := invalidated + 1
    else
      keptCls := keptCls.insert k pf
  let mut keptRel : Std.HashMap (IRI × IRI × IRI) ABoxProof := {}
  for (k, pf) in st.derivedRel.toList do
    if pf.usesId targetId then
      invalidated := invalidated + 1
    else
      keptRel := keptRel.insert k pf
  let mut keptNeg : Std.HashMap (IRI × IRI × IRI) Nat := {}
  for (fid, f) in remaining do
    if let .negObj r a b := f then
      keptNeg := keptNeg.insert (r, a, b) fid
  let keptClash := match st.clashProof with
    | some pf => if pf.usesId targetId then none else some pf
    | none => none
  -- 2. Rederive phase: re-seed from remaining base assertions & surviving facts
  let mut cq : Array (IRI × IRI) := #[]
  let mut rq : Array (IRI × IRI × IRI) := #[]
  let mut derivedCls := keptCls
  let mut derivedRel := keptRel
  let mut clashProof := keptClash
  for (fid, f) in remaining do
    match f with
    | .cls c a =>
      if !derivedCls.contains (a, c) then
        derivedCls := derivedCls.insert (a, c) (.givenCls fid c a)
      cq := cq.push (a, c)
    | .obj r a b =>
      if !derivedRel.contains (r, a, b) then
        derivedRel := derivedRel.insert (r, a, b) (.givenObj fid r a b)
      rq := rq.push (r, a, b)
    | .negObj r a b =>
      if let some pEdge := derivedRel.get? (r, a, b) then
        if clashProof.isNone then
          clashProof := some (.negObjClash fid r a b pEdge)
  -- Also enqueue surviving derived facts so multi-hop alternatives re-trigger
  for (k, _) in keptCls.toList do cq := cq.push k
  for (k, _) in keptRel.toList do rq := rq.push k
  let stMid : IncrementalState := {
    st with
    activeFacts := remaining
    derivedCls := derivedCls
    derivedRel := derivedRel
    negObjs := keptNeg
    clashProof := clashProof
  }
  let (stFinal, rederived) := propagateDelta stMid cq rq
  -- Also check if any surviving bot/negObj clash exists after rederivation
  let mut finalClash := stFinal.clashProof
  if finalClash.isNone then
    for ((a, c), pf) in stFinal.derivedCls.toList do
      if c == nothing then finalClash := some (.botClash a pf)
    for ((r, a, b), nid) in stFinal.negObjs.toList do
      if let some pEdge := stFinal.derivedRel.get? (r, a, b) then
        finalClash := some (.negObjClash nid r a b pEdge)
  return ({ stFinal with clashProof := finalClash }, invalidated, rederived)

/-- Extract a finite canonical `ABoxModel` from a consistent `IncrementalState`
    by combining the individual nodes (with their derived classes/edges) and
    any needed existential witness nodes from `st.compiled.tboxSat`. -/
def IncrementalState.extractModel (st : IncrementalState) (extraInds : List IRI := []) : ABoxModel := Id.run do
  let indPrefix := "urn:sabrina:ind:"
  let mut nodes : List IRI := []
  let mut nodeSet : Std.HashSet IRI := {}
  let mut indMap : List (IRI × IRI) := []
  let mut clsFacts : List (IRI × IRI) := []
  let mut edges : List (IRI × IRI × IRI) := []
  let mut neededTBoxNodes : Array IRI := #[]
  let mut seenTBox : Std.HashSet IRI := {}

  let allInds := (st.individuals.toList ++ extraInds).eraseDups
  let inds := if allInds.isEmpty then ["urn:sabrina:default-ind"] else allInds
  for a in inds do
    let nodeId := s!"{indPrefix}{a}"
    indMap := (a, nodeId) :: indMap
    if !nodeSet.contains nodeId then
      nodeSet := nodeSet.insert nodeId
      nodes := nodeId :: nodes
    for ((a', c), _) in st.derivedCls.toList do
      if a' == a && c != thing && c != nothing then
        clsFacts := (c, nodeId) :: clsFacts
    -- Satisfy existR obligations on individual `a` via TBox canonical witnesses
    for ax in st.compiled.tbox do
      if let .existR src r dst := ax then
        let holds := src == thing || st.derivedCls.contains (a, src)
        if holds && !st.compiled.tboxSat.subProofs.contains (dst, nothing) then
          edges := (r, nodeId, dst) :: edges
          if !seenTBox.contains dst then
            seenTBox := seenTBox.insert dst
            neededTBoxNodes := neededTBoxNodes.push dst
    for r in st.compiled.reflRoles do
      edges := (r, nodeId, nodeId) :: edges
  for ((r, a, b), _) in st.derivedRel.toList do
    edges := (r, s!"{indPrefix}{a}", s!"{indPrefix}{b}") :: edges

  -- BFS closure of needed TBox witness nodes
  let mut adj : Std.HashMap IRI (List IRI) := {}
  for ((_, u, v), _) in st.compiled.tboxSat.relProofs.toList do
    if !st.compiled.tboxSat.subProofs.contains (v, nothing) then
      adj := adj.insert u (v :: adj.getD u [])
  let mut qi : Nat := 0
  while qi < neededTBoxNodes.size do
    let u := neededTBoxNodes[qi]!
    qi := qi + 1
    if !nodeSet.contains u then
      nodeSet := nodeSet.insert u
      nodes := u :: nodes
    for v in adj.getD u [] do
      if !seenTBox.contains v then
        seenTBox := seenTBox.insert v
        neededTBoxNodes := neededTBoxNodes.push v
  for u in neededTBoxNodes do
    for ((u', c), _) in st.compiled.tboxSat.subProofs.toList do
      if u' == u && c != thing && c != nothing then
        clsFacts := (c, u) :: clsFacts
    for ((r, u', v), _) in st.compiled.tboxSat.relProofs.toList do
      if u' == u && nodeSet.contains v then
        edges := (r, u, v) :: edges

  -- Close roleSub & roleChain on edges involving individual nodes
  let mut edgeSet : Std.HashSet (IRI × IRI × IRI) := {}
  let mut edgeQueue : Array (IRI × IRI × IRI) := #[]
  for e in edges do
    if !edgeSet.contains e then
      edgeSet := edgeSet.insert e
      edgeQueue := edgeQueue.push e
  let mut ei : Nat := 0
  while ei < edgeQueue.size do
    let (r, u, v) := edgeQueue[ei]!
    ei := ei + 1
    for s in st.compiled.roleSubByR.getD r [] do
      if !edgeSet.contains (s, u, v) then
        edgeSet := edgeSet.insert (s, u, v)
        edgeQueue := edgeQueue.push (s, u, v)
    for (r2, s) in st.compiled.chainByR1.getD r [] do
      for (r', v', w) in edgeQueue do
        if r' == r2 && v' == v && !edgeSet.contains (s, u, w) then
          edgeSet := edgeSet.insert (s, u, w)
          edgeQueue := edgeQueue.push (s, u, w)
    for (r1, s) in st.compiled.chainByR2.getD r [] do
      for (r', x, u') in edgeQueue do
        if r' == r1 && u' == u && !edgeSet.contains (s, x, v) then
          edgeSet := edgeSet.insert (s, x, v)
          edgeQueue := edgeQueue.push (s, x, v)

  return {
    base := { nodes := nodes.reverse, clsFacts := clsFacts.eraseDups, edges := edgeQueue.toList }
    indMap := indMap.reverse
  }

/-- Kernel-checked consistency query on the live incremental ABox state. -/
def IncrementalState.checkConsistency (st : IncrementalState) : Option (Sum ABoxModel ABoxProof) :=
  if let some pf := st.clashProof then
    if checkABoxProof st.compiled.tbox st.activeFacts pf .clash then some (.inr pf) else none
  else if let some pf := st.compiled.tboxSat.subProofs.get? (thing, nothing) then
    let a := st.individuals.toList.headD "urn:sabrina:default-ind"
    let aboxPf := ABoxProof.botClash a (.tboxSub thing nothing a pf (.topInst a))
    if checkABoxProof st.compiled.tbox st.activeFacts aboxPf .clash then some (.inr aboxPf) else none
  else
    let m := st.extractModel
    if checkABoxModel st.compiled.tbox st.activeFacts m then some (.inl m) else none

/-- Kernel-checked `ClassAssertion(c, a)` entailment query on the live incremental state. -/
def IncrementalState.queryClassAssertion (st : IncrementalState) (c a : IRI) :
    Option (Sum (Sum ABoxProof ABoxProof) ABoxModel) :=
  -- Sum.inl (.inl pf) = INCONSISTENT, Sum.inl (.inr pf) = ENTAILED, Sum.inr m = NOT ENTAILED (countermodel)
  if let some pf := st.clashProof then
    if checkABoxProof st.compiled.tbox st.activeFacts pf .clash then some (.inl (.inl pf)) else none
  else if c == thing then
    let pf := ABoxProof.topInst a
    if checkABoxProof st.compiled.tbox st.activeFacts pf (.inst c a) then some (.inl (.inr pf)) else none
  else if let some pf := st.derivedCls.get? (a, c) then
    if checkABoxProof st.compiled.tbox st.activeFacts pf (.inst c a) then some (.inl (.inr pf)) else none
  else
    let m := st.extractModel [a]
    match m.resolveInd a with
    | some u =>
      if checkABoxModel st.compiled.tbox st.activeFacts m &&
         m.base.nodes.contains u && !m.base.hasCls c u then
        some (.inr m)
      else none
    | none => none

end Sabrina.OWL2.IncrementalABox
