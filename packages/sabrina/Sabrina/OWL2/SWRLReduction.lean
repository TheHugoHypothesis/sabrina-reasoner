import Sabrina.OWL2.SWRL
import Sabrina.OWL2.SWRLBuiltins
import Sabrina.OWL2.SROIQD.Search
import Sabrina.OWL2.SROIQD.Termination.RealDecision
import Sabrina.OWL2.Classification

/-!
Kernel-verified reduction of DL-Safe SWRL rules to OWL 2 DL (`Sabrina.OWL2.Ontology`),
together with:
1. Local data-variable roll-up (`rollupLocalDataVars`) folding local `dataPropertyAtom` +
   `dataRangeAtom` + facet-reducible `swrlb:*` built-ins into `ClassExpr.dataSome`.
2. Nominal-guarded single-variable rule encoding (`encodeUnaryRule`) avoiding $O(|\mathcal{N}_I|)$
   grounding blowup on unary rules.
3. Exact ground-rule encoding (`encodeGroundRule`, `groundRuleAll`, `groundAllRules`) with
   kernel-proved equisatisfiability and entailment preservation (`groundAllRules_sat_iff`,
   `groundAllRules_entails_iff`, `decideRealWithSWRL_iff`) over both `datatypeMap` and
   Dedekind-cut `realDatatypeMap`.
4. Safe concrete-value grounding for functional `swrlb:*` arithmetic/string built-ins.
5. Verified lazy CEGAR grounding loop (`decideWithSWRLFast?`) backed by `SROIQD.propose` +
   `checkEvidence` with exact `decideRealOntology?` fallback.
-/

namespace Sabrina.OWL2.SWRL

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination.WiderData

/-! ### 1. Exact Ground-Atom and Ground-Rule Encoding into OWL 2 DL -/

/-- Encode a ground non-builtin SWRL atom as a global OWL 2 `ClassExpr` via
    `owl:topObjectProperty` (`U`) and nominals `{a}`:
    for any interpretation `i` and any `w : i.Object`, `classHolds i w ce ↔ atomHolds ... a`. -/
def encodeGroundAtom : SWRLAtom → Option ClassExpr
  | .classAtom c (.ind x) =>
    some (.objectSome (.named topObjectProperty) (.intersection (.oneOf [x]) c))
  | .objectPropertyAtom r (.ind x) (.ind y) =>
    some (.objectSome (.named topObjectProperty) (.intersection (.oneOf [x]) (.objectValue r y)))
  | .dataPropertyAtom p (.ind x) (.lit l) =>
    some (.objectSome (.named topObjectProperty) (.intersection (.oneOf [x]) (.dataValue p l)))
  | .sameIndividualAtom (.ind x) (.ind y) =>
    some (.objectSome (.named topObjectProperty) (.intersection (.oneOf [x]) (.oneOf [y])))
  | .differentIndividualsAtom (.ind x) (.ind y) =>
    some (.objectSome (.named topObjectProperty) (.intersection (.oneOf [x]) (.complement (.oneOf [y]))))
  | _ => none

theorem encodeGroundAtom_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (σI : IRI → i.Object) (σD : IRI → i.Data)
    (w : i.Object) {a : SWRLAtom} {ce : ClassExpr}
    (h : encodeGroundAtom a = some ce) :
    classHolds i w ce ↔ atomHolds bSem i σI σD a := by
  cases a with
  | classAtom c arg =>
    cases arg with
    | var _ => simp [encodeGroundAtom] at h
    | ind x =>
      simp only [encodeGroundAtom, Option.some.injEq] at h; subst h
      simp only [classHolds, objectHolds, i.topObjectExt, true_and, List.mem_singleton, exists_eq_left,
        atomHolds, evalIArg]
      exact ⟨fun ⟨y, hy, hc⟩ => hy ▸ hc, fun hc => ⟨i.individuals x, rfl, hc⟩⟩
  | objectPropertyAtom r a1 a2 =>
    cases a1 with
    | var _ => simp [encodeGroundAtom] at h
    | ind x =>
      cases a2 with
      | var _ => simp [encodeGroundAtom] at h
      | ind y =>
        simp only [encodeGroundAtom, Option.some.injEq] at h; subst h
        simp only [classHolds, objectHolds, i.topObjectExt, true_and, List.mem_singleton, exists_eq_left,
          atomHolds, evalIArg]
        exact ⟨fun ⟨z, hz, hr⟩ => hz ▸ hr, fun hr => ⟨i.individuals x, rfl, hr⟩⟩
  | dataPropertyAtom p a1 a2 =>
    cases a1 with
    | var _ => simp [encodeGroundAtom] at h
    | ind x =>
      cases a2 with
      | var _ => simp [encodeGroundAtom] at h
      | lit l =>
        simp only [encodeGroundAtom, Option.some.injEq] at h; subst h
        simp only [classHolds, objectHolds, i.topObjectExt, true_and, List.mem_singleton, exists_eq_left,
          atomHolds, evalIArg, evalDArg]
        exact ⟨fun ⟨z, hz, hp⟩ => hz ▸ hp, fun hp => ⟨i.individuals x, rfl, hp⟩⟩
  | sameIndividualAtom a1 a2 =>
    cases a1 with
    | var _ => simp [encodeGroundAtom] at h
    | ind x =>
      cases a2 with
      | var _ => simp [encodeGroundAtom] at h
      | ind y =>
        simp only [encodeGroundAtom, Option.some.injEq] at h; subst h
        simp only [classHolds, objectHolds, i.topObjectExt, true_and, List.mem_singleton, exists_eq_left,
          atomHolds, evalIArg]
        exact ⟨fun ⟨z, hz1, hz2⟩ => hz1.trans hz2.symm, fun heq => ⟨i.individuals x, rfl, heq.symm⟩⟩
  | differentIndividualsAtom a1 a2 =>
    cases a1 with
    | var _ => simp [encodeGroundAtom] at h
    | ind x =>
      cases a2 with
      | var _ => simp [encodeGroundAtom] at h
      | ind y =>
        simp only [encodeGroundAtom, Option.some.injEq] at h; subst h
        simp only [classHolds, objectHolds, i.topObjectExt, true_and, List.mem_singleton, exists_eq_left,
          atomHolds, evalIArg]
        exact ⟨fun ⟨z, hz1, hz2⟩ hxy => hz2 (hxy.symm.trans hz1),
               fun hne => ⟨i.individuals x, rfl, fun hyx => hne hyx.symm⟩⟩
  | dataRangeAtom _ _ => simp [encodeGroundAtom] at h
  | builtinAtom _ _ => simp [encodeGroundAtom] at h

/-- Encode a ground SWRL rule `B₁ ∧ … ∧ Bₘ → H₁ ∧ … ∧ Hₖ` as `k` OWL 2 `SubClassOf` axioms
    `owl:Thing ⊑ (¬enc(B₁) ⊔ … ⊔ ¬enc(Bₘ) ⊔ enc(Hⱼ))`. -/
def encodeGroundRule (gr : SWRLRule) : Option (List Axiom) := do
  let bodyCEs ← gr.body.mapM encodeGroundAtom
  let headCEs ← gr.head.mapM encodeGroundAtom
  let negBody := bodyCEs.map ClassExpr.complement
  return headCEs.map fun hce =>
    .subClassOf (.named thing) (ClassExpr.unite (negBody ++ [hce]))

private theorem mem_mapM_some {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
    (∀ x ∈ xs, ∃ y ∈ ys, f x = some y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, f x = some y) := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨(fun _ hx => nomatch hx), (fun _ hy => nomatch hy)⟩
  | cons x rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfx : f x with
    | none => rw [hfx] at h; cases h
    | some y =>
      rw [hfx] at h
      cases hrest : rest.mapM f with
      | none => rw [hrest] at h; cases h
      | some ys' =>
        rw [hrest] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨hfwd, hbwd⟩ := ih hrest
        constructor
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact ⟨y, List.mem_cons_self .., hfx⟩
          · obtain ⟨b, hb, hfb⟩ := hfwd a ha'
            exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ⟨x, List.mem_cons_self .., hfx⟩
          · obtain ⟨a, ha, hfa⟩ := hbwd b hb'
            exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

theorem encodeGroundRule_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (σI : IRI → i.Object) (σD : IRI → i.Data)
    {gr : SWRLRule} {axs : List Axiom} (h : encodeGroundRule gr = some axs) :
    satisfies i axs ↔
      ((∀ b ∈ gr.body, atomHolds bSem i σI σD b) →
       (∀ a ∈ gr.head, atomHolds bSem i σI σD a)) := by
  classical
  unfold encodeGroundRule at h
  simp only [bind, Option.bind, pure] at h
  cases hbM : gr.body.mapM encodeGroundAtom with
  | none => rw [hbM] at h; cases h
  | some bodyCEs =>
    rw [hbM] at h
    cases hhM : gr.head.mapM encodeGroundAtom with
    | none => rw [hhM] at h; cases h
    | some headCEs =>
      rw [hhM] at h
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hbFwd, hbBwd⟩ := mem_mapM_some hbM
      obtain ⟨hhFwd, hhBwd⟩ := mem_mapM_some hhM
      constructor
      · intro hsat hbody a ha
        obtain ⟨hce, hhceMem, hEncA⟩ := hhFwd a ha
        obtain ⟨w0⟩ := i.objectNonempty
        have hax := hsat (.subClassOf (.named thing) (ClassExpr.unite (bodyCEs.map ClassExpr.complement ++ [hce])))
          (List.mem_map_of_mem hhceMem)
        have hholds : classHolds i w0 (ClassExpr.unite (bodyCEs.map ClassExpr.complement ++ [hce])) :=
          hax w0 (i.thingExt w0)
        rw [classHolds_unite] at hholds
        obtain ⟨c, hcMem, hcHolds⟩ := hholds
        rcases List.mem_append.mp hcMem with hneg | hpos
        · obtain ⟨bce, hbceMem, rfl⟩ := List.mem_map.mp hneg
          obtain ⟨b, hbMem, hEncB⟩ := hbBwd bce hbceMem
          have hbTrue : classHolds i w0 bce :=
            (encodeGroundAtom_holds_iff bSem i σI σD w0 hEncB).mpr (hbody b hbMem)
          exact (hcHolds hbTrue).elim
        · have hEq : c = hce := List.mem_singleton.mp hpos
          subst hEq
          exact (encodeGroundAtom_holds_iff bSem i σI σD w0 hEncA).mp hcHolds
      · intro himp ax hax
        obtain ⟨hce, hhceMem, rfl⟩ := List.mem_map.mp hax
        intro w _
        rw [classHolds_unite]
        by_cases hAllBody : ∀ b ∈ gr.body, atomHolds bSem i σI σD b
        · obtain ⟨a, haMem, hEncA⟩ := hhBwd hce hhceMem
          refine ⟨hce, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          exact (encodeGroundAtom_holds_iff bSem i σI σD w hEncA).mpr (himp hAllBody a haMem)
        · have hExists : ∃ b ∈ gr.body, ¬ atomHolds bSem i σI σD b :=
            Classical.byContradiction fun hno =>
              hAllBody fun b hb => Classical.byContradiction fun hbf => hno ⟨b, hb, hbf⟩
          obtain ⟨b, hbMem, hbFalse⟩ := hExists
          obtain ⟨bce, hbceMem, hEncB⟩ := hbFwd b hbMem
          refine ⟨.complement bce, List.mem_append_left _ (List.mem_map_of_mem hbceMem), ?_⟩
          intro hc
          exact hbFalse ((encodeGroundAtom_holds_iff bSem i σI σD w hEncB).mp hc)

/-! ### 2. Exhaustive Named-Individual Grounding (Exact Completeness) -/

/-- Enumerate all total assignments from `vars` to `namedInds`. -/
def allVarAssignments (namedInds : List IRI) : List IRI → List (List (IRI × IRI))
  | [] => [[]]
  | v :: rest =>
    let tail := allVarAssignments namedInds rest
    namedInds.flatMap fun a => tail.map fun env => (v, a) :: env

private theorem allVarAssignments_mem_bound {namedInds vars : List IRI}
    {env : List (IRI × IRI)} (h : env ∈ allVarAssignments namedInds vars) :
    ∀ v ∈ vars, ∃ a ∈ namedInds, env.lookup v = some a := by
  induction vars generalizing env with
  | nil => intro _ hv; cases hv
  | cons v rest ih =>
    simp only [allVarAssignments, List.mem_flatMap] at h
    obtain ⟨a, ha, h2⟩ := h
    obtain ⟨env', henv', rfl⟩ := List.mem_map.mp h2
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ⟨a, ha, by simp [List.lookup]⟩
    · by_cases hwv : w = v
      · subst hwv; exact ⟨a, ha, by simp [List.lookup]⟩
      · have hne : (w == v) = false := beq_false_of_ne hwv
        obtain ⟨b, hb, hlk⟩ := ih henv' w hw'
        exact ⟨b, hb, by simp [List.lookup, hne, hlk]⟩

private theorem allVarAssignments_complete {dm : DatatypeMap} (i : Interpretation dm)
    {namedInds vars : List IRI} (hnd : vars.Nodup)
    (σI : IRI → i.Object)
    (hBound : ∀ v ∈ vars, ∃ a ∈ namedInds, σI v = i.individuals (.named a)) :
    ∃ env ∈ allVarAssignments namedInds vars,
      ∀ v ∈ vars, ∃ a ∈ namedInds, env.lookup v = some a ∧ σI v = i.individuals (.named a) := by
  induction vars with
  | nil => exact ⟨[], List.mem_singleton_self _, fun _ hv => by cases hv⟩
  | cons v rest ih =>
    obtain ⟨hvNot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨a, ha, hσv⟩ := hBound v (List.mem_cons_self ..)
    obtain ⟨env', henv', hrest⟩ := ih hnd' (fun w hw => hBound w (List.mem_cons_of_mem _ hw))
    refine ⟨(v, a) :: env', List.mem_flatMap.mpr ⟨a, ha, List.mem_map_of_mem henv'⟩, ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ⟨a, ha, by simp [List.lookup], hσv⟩
    · have hne : w ≠ v := fun heq => hvNot (heq ▸ hw')
      have hbeq : (w == v) = false := beq_false_of_ne hne
      obtain ⟨b, hb, hlk, hσw⟩ := hrest w hw'
      exact ⟨b, hb, by simp [List.lookup, hbeq, hlk], hσw⟩

private theorem evalIArg_eq_of_agree {dm : DatatypeMap} (i : Interpretation dm)
    {σ₁ σ₂ : IRI → i.Object} {a : IArg}
    (h : ∀ v ∈ a.vars, σ₁ v = σ₂ v) :
    evalIArg i σ₁ a = evalIArg i σ₂ a := by
  cases a with
  | ind _ => rfl
  | var v => exact h v (List.mem_cons_self ..)

private theorem atomHolds_iVars_congr {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) {σI₁ σI₂ : IRI → i.Object} {σD : IRI → i.Data} {a : SWRLAtom}
    (h : ∀ v ∈ a.iVars, σI₁ v = σI₂ v) :
    atomHolds bSem i σI₁ σD a ↔ atomHolds bSem i σI₂ σD a := by
  cases a with
  | classAtom c x =>
    simp only [atomHolds]
    rw [evalIArg_eq_of_agree i h]
  | dataRangeAtom d x => rfl
  | objectPropertyAtom r x y =>
    simp only [atomHolds]
    rw [evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_left _ hv))),
        evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_right _ hv)))]
  | dataPropertyAtom p x y =>
    simp only [atomHolds]
    rw [evalIArg_eq_of_agree i h]
  | sameIndividualAtom x y =>
    simp only [atomHolds]
    rw [evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_left _ hv))),
        evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_right _ hv)))]
  | differentIndividualsAtom x y =>
    simp only [atomHolds]
    rw [evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_left _ hv))),
        evalIArg_eq_of_agree i (fun v hv => h v (List.mem_eraseDups.mpr (List.mem_append_right _ hv)))]
  | builtinAtom b args => rfl

private theorem lookup_map_named' (envI : List (IRI × IRI)) (v x : IRI)
    (h : envI.lookup v = some x) :
    (envI.map fun (w, a) => (w, Individual.named a)).lookup v = some (.named x) := by
  induction envI with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨k, val⟩
    simp only [List.lookup, List.map_cons] at h ⊢
    cases hvk : (v == k) with
    | true => simp only [hvk] at h ⊢; cases h; rfl
    | false => simp only [hvk] at h ⊢; exact ih h

private theorem iVars_mem_of_body {r : SWRLRule} {a : SWRLAtom} (ha : a ∈ r.body)
    {v : IRI} (hv : v ∈ a.iVars) : v ∈ r.iVars :=
  List.mem_eraseDups.mpr (List.mem_append_left _
    (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨a, ha, hv⟩)))

private theorem iVars_mem_of_head {r : SWRLRule} {a : SWRLAtom} (ha : a ∈ r.head)
    {v : IRI} (hv : v ∈ a.iVars) : v ∈ r.iVars :=
  List.mem_eraseDups.mpr (List.mem_append_right _
    (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨a, ha, hv⟩)))

/-- Ground a single data-variable-free DL-safe rule over all assignments to `namedInds`
    and encode each ground instance into OWL 2 DL axioms. -/
def groundRuleAll (namedInds : List IRI) (r : SWRLRule) : Option (List Axiom) := do
  let envs := allVarAssignments namedInds r.iVars
  let axLists ← envs.mapM fun env =>
    encodeGroundRule (r.subst (env.map fun (v, a) => (v, .named a)) [])
  return axLists.flatten

theorem groundRuleAll_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r : SWRLRule} {axs : List Axiom}
    (h : groundRuleAll namedInds r = some axs) :
    satisfies i axs ↔ satisfiesDLSafeRule bSem namedInds i r := by
  unfold groundRuleAll at h
  simp only [bind, Option.bind, pure] at h
  cases hM : (allVarAssignments namedInds r.iVars).mapM
      (fun env => encodeGroundRule (r.subst (env.map fun (v, a) => (v, .named a)) [])) with
  | none => rw [hM] at h; cases h
  | some axLists =>
    rw [hM] at h; simp only [Option.some.injEq] at h; subst h
    obtain ⟨hFwd, hBwd⟩ := mem_mapM_some hM
    constructor
    · intro hsat σI σD hBound hbody a ha
      have hnd : r.iVars.Nodup := nodup_eraseDups_list _
      obtain ⟨env, henvMem, hEnvSpec⟩ := allVarAssignments_complete i hnd σI hBound
      obtain ⟨gAxs, hgAxsMem, hEnc⟩ := hFwd env henvMem
      have hgsat : satisfies i gAxs := fun ax hax =>
        hsat ax (List.mem_flatten.mpr ⟨gAxs, hgAxsMem, hax⟩)
      let envI' := env.map fun (v, x) => (v, Individual.named x)
      have hAgree : ∀ v ∈ r.iVars, applyEnvI i envI' σI v = σI v := by
        intro v hv
        obtain ⟨x, _, hlk, hσ⟩ := hEnvSpec v hv
        simp [applyEnvI, envI', lookup_map_named' env v x hlk, hσ]
      have hSubBody : ∀ b ∈ (r.subst envI' []).body, atomHolds bSem i σI σD b := by
        intro b hb
        obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
        rw [atomHolds_subst_iff]
        have hEqD : applyEnvD i [] σD = σD := by funext v; rfl
        rw [hEqD]
        exact (atomHolds_iVars_congr bSem i fun v hv => hAgree v (iVars_mem_of_body hb₀ hv)).mpr (hbody b₀ hb₀)
      have hSubHead := (encodeGroundRule_holds_iff bSem i σI σD hEnc).mp hgsat hSubBody
      have haSub := hSubHead (a.subst envI' []) (List.mem_map_of_mem ha)
      rw [atomHolds_subst_iff] at haSub
      have hEqD : applyEnvD i [] σD = σD := by funext v; rfl
      rw [hEqD] at haSub
      exact (atomHolds_iVars_congr bSem i fun v hv => hAgree v (iVars_mem_of_head ha hv)).mp haSub
    · intro hr ax hax
      obtain ⟨gAxs, hgAxsMem, haxIn⟩ := List.mem_flatten.mp hax
      obtain ⟨env, henvMem, hEnc⟩ := hBwd gAxs hgAxsMem
      obtain ⟨w0⟩ := i.objectNonempty
      -- Any dummy `σD` works since `encodeGroundRule` succeeded (so `gr` has no data vars)
      have hEmptyD : ∃ y0 : i.Data, True := by
        -- Use literalValue of an arbitrary literal to witness `i.Data`
        exact ⟨i.literalValue ⟨"0", xsd "integer"⟩, trivial⟩
      obtain ⟨y0, _⟩ := hEmptyD
      have hImp := satisfiesDLSafeRule_ground_instance bSem hr env []
        (allVarAssignments_mem_bound henvMem) (fun _ => w0) (fun _ => y0)
      exact (encodeGroundRule_holds_iff bSem i (fun _ => w0) (fun _ => y0) hEnc).mpr hImp ax haxIn

/-! ### 3. Nominal-Guarded Single-Variable Fast Encoding (Zero Grounding Blowup) -/

/-- Encode a unary SWRL atom whose only individual variable is `v` directly as a `ClassExpr`. -/
def encodeUnaryAtom (v : IRI) : SWRLAtom → Option ClassExpr
  | .classAtom c (.var w) => if w == v then some c else none
  | .classAtom c (.ind x) => encodeGroundAtom (.classAtom c (.ind x))
  | .objectPropertyAtom r (.var w) (.ind y) =>
    if w == v then some (.objectValue r y) else none
  | .objectPropertyAtom r (.ind x) (.var w) =>
    if w == v then some (.objectValue r.converse x) else none
  | .objectPropertyAtom r (.var w1) (.var w2) =>
    if w1 == v && w2 == v then some (.objectSelf r) else none
  | .objectPropertyAtom r (.ind x) (.ind y) =>
    encodeGroundAtom (.objectPropertyAtom r (.ind x) (.ind y))
  | .dataPropertyAtom p (.var w) (.lit l) =>
    if w == v then some (.dataValue p l) else none
  | .dataPropertyAtom p (.ind x) (.lit l) =>
    encodeGroundAtom (.dataPropertyAtom p (.ind x) (.lit l))
  | .sameIndividualAtom (.var w) (.ind y) =>
    if w == v then some (.oneOf [y]) else none
  | .sameIndividualAtom (.ind x) (.var w) =>
    if w == v then some (.oneOf [x]) else none
  | .sameIndividualAtom (.var w1) (.var w2) =>
    if w1 == v && w2 == v then some (.named thing) else none
  | .sameIndividualAtom (.ind x) (.ind y) =>
    encodeGroundAtom (.sameIndividualAtom (.ind x) (.ind y))
  | .differentIndividualsAtom (.var w) (.ind y) =>
    if w == v then some (.complement (.oneOf [y])) else none
  | .differentIndividualsAtom (.ind x) (.var w) =>
    if w == v then some (.complement (.oneOf [x])) else none
  | .differentIndividualsAtom (.var w1) (.var w2) =>
    if w1 == v && w2 == v then some (.named nothing) else none
  | .differentIndividualsAtom (.ind x) (.ind y) =>
    encodeGroundAtom (.differentIndividualsAtom (.ind x) (.ind y))
  | _ => none

private theorem objectHolds_converse {dm : DatatypeMap} (i : Interpretation dm)
    (r : ObjectProperty) (x y : i.Object) :
    objectHolds i r.converse x y ↔ objectHolds i r y x := by
  cases r <;> rfl

theorem encodeUnaryAtom_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (v : IRI) (σI : IRI → i.Object) (σD : IRI → i.Data)
    {a : SWRLAtom} {ce : ClassExpr} (h : encodeUnaryAtom v a = some ce) :
    classHolds i (σI v) ce ↔ atomHolds bSem i σI σD a := by
  cases a with
  | classAtom c arg =>
    cases arg with
    | var w =>
      simp only [encodeUnaryAtom] at h
      split at h
      · rename_i hw; have hEq := beq_iff_eq.mp hw; subst hEq
        cases h; rfl
      · cases h
    | ind x => exact encodeGroundAtom_holds_iff bSem i σI σD (σI v) h
  | objectPropertyAtom r a1 a2 =>
    cases a1 with
    | var w1 =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hw
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; rfl
        · cases h
      | ind y =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e1 := beq_iff_eq.mp hw; subst e1; cases h; rfl
        · cases h
    | ind x =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e2 := beq_iff_eq.mp hw; subst e2; cases h
          exact objectHolds_converse i r (σI w2) (i.individuals x)
        · cases h
      | ind y => exact encodeGroundAtom_holds_iff bSem i σI σD (σI v) h
  | dataPropertyAtom p a1 a2 =>
    cases a1 with
    | var w =>
      cases a2 with
      | var _ => simp [encodeUnaryAtom] at h
      | lit l =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e1 := beq_iff_eq.mp hw; subst e1; cases h; rfl
        · cases h
    | ind x =>
      cases a2 with
      | var _ => simp [encodeUnaryAtom] at h
      | lit l => exact encodeGroundAtom_holds_iff bSem i σI σD (σI v) h
  | sameIndividualAtom a1 a2 =>
    cases a1 with
    | var w1 =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hw
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; simp [classHolds, i.thingExt, atomHolds, evalIArg]
        · cases h
      | ind y =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e1 := beq_iff_eq.mp hw; subst e1; cases h
          simp [classHolds, atomHolds, evalIArg, eq_comm]
        · cases h
    | ind x =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e2 := beq_iff_eq.mp hw; subst e2; cases h
          simp [classHolds, atomHolds, evalIArg]
        · cases h
      | ind y => exact encodeGroundAtom_holds_iff bSem i σI σD (σI v) h
  | differentIndividualsAtom a1 a2 =>
    cases a1 with
    | var w1 =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hw
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; simp [classHolds, i.nothingExt, atomHolds, evalIArg]
        · cases h
      | ind y =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e1 := beq_iff_eq.mp hw; subst e1; cases h
          simp [classHolds, atomHolds, evalIArg, ne_comm]
        · cases h
    | ind x =>
      cases a2 with
      | var w2 =>
        simp only [encodeUnaryAtom] at h
        split at h
        · rename_i hw; have e2 := beq_iff_eq.mp hw; subst e2; cases h
          simp [classHolds, atomHolds, evalIArg]
        · cases h
      | ind y => exact encodeGroundAtom_holds_iff bSem i σI σD (σI v) h
  | dataRangeAtom _ _ => simp [encodeUnaryAtom] at h
  | builtinAtom _ _ => simp [encodeUnaryAtom] at h

/-- Encode a single-variable DL-safe rule `r` (with `r.iVars = [v]`) as ONE nominal-guarded
    `SubClassOf` axiom per head atom: `(oneOf(namedInds) ⊓ B₁ ⊓ … ⊓ Bₘ) ⊑ Hⱼ`. -/
def encodeUnaryRule (namedInds : List IRI) (r : SWRLRule) : Option (List Axiom) :=
  match r.iVars with
  | [v] => do
    let bodyCEs ← r.body.mapM (encodeUnaryAtom v)
    let headCEs ← r.head.mapM (encodeUnaryAtom v)
    let guard := ClassExpr.oneOf (namedInds.map Individual.named)
    let lhs := ClassExpr.intersect (guard :: bodyCEs)
    return headCEs.map fun hce => .subClassOf lhs hce
  | _ => none

theorem encodeUnaryRule_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r : SWRLRule} {axs : List Axiom}
    (h : encodeUnaryRule namedInds r = some axs) :
    satisfies i axs ↔ satisfiesDLSafeRule bSem namedInds i r := by
  unfold encodeUnaryRule at h
  cases hvars : r.iVars with
  | nil => rw [hvars] at h; cases h
  | cons v rest =>
    cases rest with
    | cons _ _ => rw [hvars] at h; cases h
    | nil =>
      rw [hvars] at h
      simp only [bind, Option.bind, pure] at h
      cases hbM : r.body.mapM (encodeUnaryAtom v) with
      | none => rw [hbM] at h; cases h
      | some bodyCEs =>
        rw [hbM] at h
        cases hhM : r.head.mapM (encodeUnaryAtom v) with
        | none => rw [hhM] at h; cases h
        | some headCEs =>
          rw [hhM] at h; simp only [Option.some.injEq] at h; subst h
          obtain ⟨hbFwd, hbBwd⟩ := mem_mapM_some hbM
          obtain ⟨hhFwd, hhBwd⟩ := mem_mapM_some hhM
          constructor
          · intro hsat σI σD hBound hbody a ha
            obtain ⟨hce, hhceMem, hEncA⟩ := hhFwd a ha
            have hax := hsat (.subClassOf (ClassExpr.intersect (.oneOf (namedInds.map Individual.named) :: bodyCEs)) hce)
              (List.mem_map_of_mem hhceMem)
            have hLhs : classHolds i (σI v) (ClassExpr.intersect (.oneOf (namedInds.map Individual.named) :: bodyCEs)) := by
              rw [classHolds_intersect]
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hc'
              · obtain ⟨ind, hindMem, hσv⟩ := hBound v (by rw [hvars]; exact List.mem_cons_self ..)
                exact ⟨.named ind, List.mem_map_of_mem hindMem, hσv.symm⟩
              · obtain ⟨b, hbMem, hEncB⟩ := hbBwd c hc'
                exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncB).mpr (hbody b hbMem)
            exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncA).mp (hax (σI v) hLhs)
          · intro hr ax hax
            obtain ⟨hce, hhceMem, rfl⟩ := List.mem_map.mp hax
            intro x hx
            rw [classHolds_intersect] at hx
            have hGuard := hx (.oneOf (namedInds.map Individual.named)) (List.mem_cons_self ..)
            obtain ⟨ind', hind'Mem, hind'Eq⟩ := hGuard
            obtain ⟨aName, haNameMem, rfl⟩ := List.mem_map.mp hind'Mem
            let σI : IRI → i.Object := fun _ => x
            let σD : IRI → i.Data := fun _ => i.literalValue ⟨"0", xsd "integer"⟩
            obtain ⟨aHead, haHeadMem, hEncA⟩ := hhBwd hce hhceMem
            have hHeadHolds := hr σI σD
              (fun w hw => by
                rw [hvars] at hw
                have := List.mem_singleton.mp hw; subst this
                exact ⟨aName, haNameMem, hind'Eq.symm⟩)
              (fun b hb => by
                obtain ⟨bce, hbceMem, hEncB⟩ := hbFwd b hb
                exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncB).mp
                  (hx bce (List.mem_cons_of_mem _ hbceMem)))
              aHead haHeadMem
            exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncA).mpr hHeadHolds

/-! ### 3.5 Direct Single-Individual Ground Encoding & Tree-Shaped Individual Roll-Up -/

/-- Encode a ground SWRL atom directly relative to a single anchor individual `x`
    without introducing `owl:topObjectProperty`. -/
def encodeAtomAt (x : Individual) : SWRLAtom → Option ClassExpr
  | .classAtom c (.ind y) => if y == x then some c else none
  | .objectPropertyAtom r (.ind y) (.ind z) =>
    if y == x && z == x then some (.objectSelf r)
    else if y == x then some (.objectValue r z)
    else if z == x then some (.objectValue r.converse y)
    else none
  | .dataPropertyAtom p (.ind y) (.lit l) =>
    if y == x then some (.dataValue p l) else none
  | .sameIndividualAtom (.ind y) (.ind z) =>
    if y == x && z == x then some (.named thing)
    else if y == x then some (.oneOf [z])
    else if z == x then some (.oneOf [y])
    else none
  | .differentIndividualsAtom (.ind y) (.ind z) =>
    if y == x && z == x then some (.named nothing)
    else if y == x then some (.complement (.oneOf [z]))
    else if z == x then some (.complement (.oneOf [y]))
    else none
  | _ => none

theorem encodeAtomAt_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (x : Individual) (σI : IRI → i.Object) (σD : IRI → i.Data)
    {a : SWRLAtom} {ce : ClassExpr} (h : encodeAtomAt x a = some ce) :
    classHolds i (i.individuals x) ce ↔ atomHolds bSem i σI σD a := by
  cases a with
  | classAtom c arg =>
    cases arg with
    | var _ => simp [encodeAtomAt] at h
    | ind y =>
      simp only [encodeAtomAt] at h
      split at h
      · rename_i hy; have e := beq_iff_eq.mp hy; subst e; cases h; rfl
      · cases h
  | objectPropertyAtom r a1 a2 =>
    cases a1 with
    | var _ => simp [encodeAtomAt] at h
    | ind y =>
      cases a2 with
      | var _ => simp [encodeAtomAt] at h
      | ind z =>
        simp only [encodeAtomAt] at h
        split at h
        · rename_i hyz
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hyz
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; rfl
        · split at h
          · rename_i hy; have e := beq_iff_eq.mp hy; subst e; cases h; rfl
          · split at h
            · rename_i hz; have e := beq_iff_eq.mp hz; subst e; cases h
              exact objectHolds_converse i r (i.individuals z) (i.individuals y)
            · cases h
  | dataPropertyAtom p a1 a2 =>
    cases a1 with
    | var _ => simp [encodeAtomAt] at h
    | ind y =>
      cases a2 with
      | var _ => simp [encodeAtomAt] at h
      | lit l =>
        simp only [encodeAtomAt] at h
        split at h
        · rename_i hy; have e := beq_iff_eq.mp hy; subst e; cases h; rfl
        · cases h
  | sameIndividualAtom a1 a2 =>
    cases a1 with
    | var _ => simp [encodeAtomAt] at h
    | ind y =>
      cases a2 with
      | var _ => simp [encodeAtomAt] at h
      | ind z =>
        simp only [encodeAtomAt] at h
        split at h
        · rename_i hyz
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hyz
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; simp [classHolds, i.thingExt, atomHolds, evalIArg]
        · split at h
          · rename_i hy; have e := beq_iff_eq.mp hy; subst e; cases h
            simp [classHolds, atomHolds, evalIArg, eq_comm]
          · split at h
            · rename_i hz; have e := beq_iff_eq.mp hz; subst e; cases h
              simp [classHolds, atomHolds, evalIArg]
            · cases h
  | differentIndividualsAtom a1 a2 =>
    cases a1 with
    | var _ => simp [encodeAtomAt] at h
    | ind y =>
      cases a2 with
      | var _ => simp [encodeAtomAt] at h
      | ind z =>
        simp only [encodeAtomAt] at h
        split at h
        · rename_i hyz
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hyz
          have e1 := beq_iff_eq.mp h1; have e2 := beq_iff_eq.mp h2
          subst e1; subst e2; cases h; simp [classHolds, i.nothingExt, atomHolds, evalIArg]
        · split at h
          · rename_i hy; have e := beq_iff_eq.mp hy; subst e; cases h
            simp [classHolds, atomHolds, evalIArg, ne_comm]
          · split at h
            · rename_i hz; have e := beq_iff_eq.mp hz; subst e; cases h
              simp [classHolds, atomHolds, evalIArg]
            · cases h
  | dataRangeAtom _ _ => simp [encodeAtomAt] at h
  | builtinAtom _ _ => simp [encodeAtomAt] at h

private def firstGroundInd? : List SWRLAtom → Option Individual
  | [] => none
  | .classAtom _ (.ind x) :: _ => some x
  | .objectPropertyAtom _ (.ind x) _ :: _ => some x
  | .dataPropertyAtom _ (.ind x) _ :: _ => some x
  | .sameIndividualAtom (.ind x) _ :: _ => some x
  | .differentIndividualsAtom (.ind x) _ :: _ => some x
  | _ :: rest => firstGroundInd? rest

/-- Encode a ground SWRL rule whose atoms all touch a single anchor individual `x`
    directly as `SubClassOf({x} ⊓ B₁ ⊓ … ⊓ Bₘ, Hⱼ)` without `owl:topObjectProperty`. -/
def encodeSingleIndGroundRule (gr : SWRLRule) : Option (List Axiom) := do
  let x ← firstGroundInd? (gr.body ++ gr.head)
  let bodyCEs ← gr.body.mapM (encodeAtomAt x)
  let headCEs ← gr.head.mapM (encodeAtomAt x)
  let lhs := ClassExpr.intersect (.oneOf [x] :: bodyCEs)
  return headCEs.map fun hce => .subClassOf lhs hce

theorem encodeSingleIndGroundRule_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (σI : IRI → i.Object) (σD : IRI → i.Data)
    {gr : SWRLRule} {axs : List Axiom} (h : encodeSingleIndGroundRule gr = some axs) :
    satisfies i axs ↔
      ((∀ b ∈ gr.body, atomHolds bSem i σI σD b) →
       (∀ a ∈ gr.head, atomHolds bSem i σI σD a)) := by
  unfold encodeSingleIndGroundRule at h
  simp only [bind, Option.bind, pure] at h
  cases hx : firstGroundInd? (gr.body ++ gr.head) with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h; dsimp only at h
    cases hbM : gr.body.mapM (encodeAtomAt x) with
    | none => rw [hbM] at h; cases h
    | some bodyCEs =>
      rw [hbM] at h; dsimp only at h
      cases hhM : gr.head.mapM (encodeAtomAt x) with
      | none => rw [hhM] at h; cases h
      | some headCEs =>
        rw [hhM] at h; dsimp only at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hbFwd, hbBwd⟩ := mem_mapM_some hbM
        obtain ⟨hhFwd, hhBwd⟩ := mem_mapM_some hhM
        constructor
        · intro hsat hbody a ha
          obtain ⟨hce, hhceMem, hEncA⟩ := hhFwd a ha
          have hax := hsat (.subClassOf (ClassExpr.intersect (.oneOf [x] :: bodyCEs)) hce)
            (List.mem_map_of_mem hhceMem)
          have hLhs : classHolds i (i.individuals x) (ClassExpr.intersect (.oneOf [x] :: bodyCEs)) := by
            rw [classHolds_intersect]
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc'
            · exact ⟨x, List.mem_singleton_self _, rfl⟩
            · obtain ⟨b, hbMem, hEncB⟩ := hbBwd c hc'
              exact (encodeAtomAt_holds_iff bSem i x σI σD hEncB).mpr (hbody b hbMem)
          exact (encodeAtomAt_holds_iff bSem i x σI σD hEncA).mp (hax (i.individuals x) hLhs)
        · intro himp ax hax
          obtain ⟨hce, hhceMem, rfl⟩ := List.mem_map.mp hax
          intro w hw
          rw [classHolds_intersect] at hw
          have hGuard := hw (.oneOf [x]) (List.mem_cons_self ..)
          obtain ⟨y, hyMem, hyEq⟩ := hGuard
          rw [List.mem_singleton.mp hyMem] at hyEq
          have hwx : w = i.individuals x := hyEq.symm
          subst hwx
          obtain ⟨aHead, haHeadMem, hEncA⟩ := hhBwd hce hhceMem
          have hBody : ∀ b ∈ gr.body, atomHolds bSem i σI σD b := fun b hb => by
            obtain ⟨bce, hbceMem, hEncB⟩ := hbFwd b hb
            exact (encodeAtomAt_holds_iff bSem i x σI σD hEncB).mp (hw bce (List.mem_cons_of_mem _ hbceMem))
          exact (encodeAtomAt_holds_iff bSem i x σI σD hEncA).mpr (himp hBody aHead haHeadMem)

/-- Extract the first linking `objectPropertyAtom` connecting `iv` to a distinct `IArg`,
    returning `(rel, anchor, remainingAtoms)`. -/
private def extractFirstIndLink (iv : IRI) :
    List SWRLAtom → Option (ObjectProperty × IArg × List SWRLAtom)
  | [] => none
  | a :: rest =>
    match a with
    | .objectPropertyAtom rel anchor (.var w) =>
      if w == iv && anchor != .var iv then some (rel, anchor, rest)
      else (extractFirstIndLink iv rest).map fun (r', anc, tl) => (r', anc, a :: tl)
    | .objectPropertyAtom rel (.var w) anchor =>
      if w == iv && anchor != .var iv then some (rel.converse, anchor, rest)
      else (extractFirstIndLink iv rest).map fun (r', anc, tl) => (r', anc, a :: tl)
    | _ => (extractFirstIndLink iv rest).map fun (r', anc, tl) => (r', anc, a :: tl)

private theorem extractFirstIndLink_spec {iv : IRI} {xs rest : List SWRLAtom}
    {rel : ObjectProperty} {anchor : IArg}
    (h : extractFirstIndLink iv xs = some (rel, anchor, rest)) :
    anchor ≠ .var iv ∧
    (∃ linkAtom ∈ xs,
      (linkAtom = .objectPropertyAtom rel anchor (.var iv) ∨
       ∃ rel0, rel = rel0.converse ∧ linkAtom = .objectPropertyAtom rel0 (.var iv) anchor) ∧
      (∀ a ∈ rest, a ∈ xs) ∧
      (∀ a ∈ xs, a = linkAtom ∨ a ∈ rest)) := by
  induction xs generalizing rest with
  | nil => simp [extractFirstIndLink] at h
  | cons a tl ih =>
    simp only [extractFirstIndLink] at h
    cases a with
    | objectPropertyAtom r0 a1 a2 =>
      cases a2 with
      | var w2 =>
        dsimp only at h
        split at h
        · rename_i hc
          obtain ⟨hw, hne⟩ := Bool.and_eq_true_iff.mp hc
          have ew := beq_iff_eq.mp hw; subst ew
          cases h
          refine ⟨by intro heq; simp [heq] at hne,
            .objectPropertyAtom rel anchor (.var w2), List.mem_cons_self .., Or.inl rfl,
            fun b hb => List.mem_cons_of_mem _ hb,
            fun b hb => (List.mem_cons.mp hb).imp id id⟩
        · cases htl : extractFirstIndLink iv tl with
          | none => rw [htl] at h; cases h
          | some res =>
            rcases res with ⟨r', anc, tl'⟩
            rw [htl] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨hane, lk, hlkMem, hlkForm, hsub, hcov⟩ := ih htl
            refine ⟨hane, lk, List.mem_cons_of_mem _ hlkMem, hlkForm,
              fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ List.mem_cons_self ..) (fun h2 => List.mem_cons_of_mem _ (hsub b h2)),
              fun b hb => (List.mem_cons.mp hb).elim (fun e => Or.inr (e ▸ List.mem_cons_self ..))
                (fun h2 => (hcov b h2).elim Or.inl (fun h3 => Or.inr (List.mem_cons_of_mem _ h3)))⟩
      | ind y2 =>
        cases a1 with
        | var w1 =>
          dsimp only at h
          split at h
          · rename_i hc
            obtain ⟨hw, hne⟩ := Bool.and_eq_true_iff.mp hc
            have ew := beq_iff_eq.mp hw; subst ew
            cases h
            refine ⟨by intro heq; simp [heq] at hne,
              .objectPropertyAtom r0 (.var w1) (.ind y2), List.mem_cons_self ..,
              Or.inr ⟨r0, rfl, rfl⟩,
              fun b hb => List.mem_cons_of_mem _ hb,
              fun b hb => (List.mem_cons.mp hb).imp id id⟩
          · cases htl : extractFirstIndLink iv tl with
            | none => rw [htl] at h; cases h
            | some res =>
              rcases res with ⟨r', anc, tl'⟩
              rw [htl] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              obtain ⟨hane, lk, hlkMem, hlkForm, hsub, hcov⟩ := ih htl
              refine ⟨hane, lk, List.mem_cons_of_mem _ hlkMem, hlkForm,
                fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ List.mem_cons_self ..) (fun h2 => List.mem_cons_of_mem _ (hsub b h2)),
                fun b hb => (List.mem_cons.mp hb).elim (fun e => Or.inr (e ▸ List.mem_cons_self ..))
                  (fun h2 => (hcov b h2).elim Or.inl (fun h3 => Or.inr (List.mem_cons_of_mem _ h3)))⟩
        | ind _ =>
          cases htl : extractFirstIndLink iv tl with
          | none => rw [htl] at h; cases h
          | some res =>
            rcases res with ⟨r', anc, tl'⟩
            rw [htl] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨hane, lk, hlkMem, hlkForm, hsub, hcov⟩ := ih htl
            refine ⟨hane, lk, List.mem_cons_of_mem _ hlkMem, hlkForm,
              fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ List.mem_cons_self ..) (fun h2 => List.mem_cons_of_mem _ (hsub b h2)),
              fun b hb => (List.mem_cons.mp hb).elim (fun e => Or.inr (e ▸ List.mem_cons_self ..))
                (fun h2 => (hcov b h2).elim Or.inl (fun h3 => Or.inr (List.mem_cons_of_mem _ h3)))⟩
    | _ =>
      cases htl : extractFirstIndLink iv tl with
      | none => rw [htl] at h; cases h
      | some res =>
        rcases res with ⟨r', anc, tl'⟩
        rw [htl] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hane, lk, hlkMem, hlkForm, hsub, hcov⟩ := ih htl
        refine ⟨hane, lk, List.mem_cons_of_mem _ hlkMem, hlkForm,
          fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ List.mem_cons_self ..) (fun h2 => List.mem_cons_of_mem _ (hsub b h2)),
          fun b hb => (List.mem_cons.mp hb).elim (fun e => Or.inr (e ▸ List.mem_cons_self ..))
            (fun h2 => (hcov b h2).elim Or.inl (fun h3 => Or.inr (List.mem_cons_of_mem _ h3)))⟩

private theorem encodeUnaryAtom_iVars_sub {v : IRI} {a : SWRLAtom} {ce : ClassExpr}
    (h : encodeUnaryAtom v a = some ce) : ∀ w ∈ a.iVars, w = v := by
  cases a with
  | classAtom c arg =>
    cases arg with
    | ind _ => intro _ hw; cases hw
    | var w =>
      simp only [encodeUnaryAtom] at h; split at h
      · rename_i hEq; intro u hu
        have := List.mem_singleton.mp hu; subst this; exact beq_iff_eq.mp hEq
      · cases h
  | objectPropertyAtom r a1 a2 =>
    cases a1 <;> cases a2
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i hc; obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
        intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.mem_eraseDups, List.mem_append, List.mem_singleton] at hu
        exact hu.elim (fun e => e ▸ beq_iff_eq.mp h1) (fun e => e ▸ beq_iff_eq.mp h2)
      · cases h
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i h1; intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.append_nil, List.mem_eraseDups, List.mem_singleton] at hu
        exact hu ▸ beq_iff_eq.mp h1
      · cases h
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i h2; intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.nil_append, List.mem_eraseDups, List.mem_singleton] at hu
        exact hu ▸ beq_iff_eq.mp h2
      · cases h
    · intro _ hw; simp [SWRLAtom.iVars, IArg.vars] at hw
  | dataPropertyAtom p a1 a2 =>
    cases a1 <;> cases a2
    · simp [encodeUnaryAtom] at h
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i h1; intro u hu
        have := List.mem_singleton.mp hu; subst this; exact beq_iff_eq.mp h1
      · cases h
    · simp [encodeUnaryAtom] at h
    · intro _ hw; cases hw
  | sameIndividualAtom a1 a2 | differentIndividualsAtom a1 a2 =>
    cases a1 <;> cases a2
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i hc; obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
        intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.mem_eraseDups, List.mem_append, List.mem_singleton] at hu
        exact hu.elim (fun e => e ▸ beq_iff_eq.mp h1) (fun e => e ▸ beq_iff_eq.mp h2)
      · cases h
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i h1; intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.append_nil, List.mem_eraseDups, List.mem_singleton] at hu
        exact hu ▸ beq_iff_eq.mp h1
      · cases h
    · simp only [encodeUnaryAtom] at h; split at h
      · rename_i h2; intro u hu
        simp only [SWRLAtom.iVars, IArg.vars, List.nil_append, List.mem_eraseDups, List.mem_singleton] at hu
        exact hu ▸ beq_iff_eq.mp h2
      · cases h
    · intro _ hw; simp [SWRLAtom.iVars, IArg.vars] at hw
  | dataRangeAtom _ _ => simp [encodeUnaryAtom] at h
  | builtinAtom _ _ => simp [encodeUnaryAtom] at h

/-- Roll up a body-only individual variable `iv` linked via an `objectPropertyAtom` into a
    nominal-guarded existential restriction `∃rel.(oneOf(namedInds) ⊓ C₁ ⊓ … ⊓ Cₖ)` on the
    anchor argument, eliminating `iv` without grounding blowup. -/
def rollupOneIndVar (namedInds : List IRI) (r : SWRLRule) (iv : IRI) : Option SWRLRule :=
  if r.headIVars.contains iv then none
  else
    let mentioning := r.body.filter fun a => a.iVars.contains iv
    let others := r.body.filter fun a => !a.iVars.contains iv
    match extractFirstIndLink iv mentioning with
    | none => none
    | some (rel, anchor, restMent) =>
      match restMent.mapM (encodeUnaryAtom iv) with
      | none => none
      | some ces =>
        let guard := ClassExpr.oneOf (namedInds.map Individual.named)
        let filler := ClassExpr.intersect (guard :: ces)
        some { r with body := .classAtom (.objectSome rel filler) anchor :: others }

/-- Kernel-verified equivalence of DL-safe body-only individual-variable roll-up. -/
theorem rollupOneIndVar_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r r' : SWRLRule} {iv : IRI}
    (h : rollupOneIndVar namedInds r iv = some r') :
    satisfiesDLSafeRule bSem namedInds i r' ↔ satisfiesDLSafeRule bSem namedInds i r := by
  unfold rollupOneIndVar at h
  split at h
  · cases h
  · rename_i hNotHead
    dsimp only at h
    let mentioning := r.body.filter (fun a => a.iVars.contains iv)
    let others := r.body.filter (fun a => !a.iVars.contains iv)
    change (match extractFirstIndLink iv mentioning with
      | none => none
      | some (rel, anchor, restMent) =>
        match restMent.mapM (encodeUnaryAtom iv) with
        | none => none
        | some ces =>
          some { r with body := .classAtom (.objectSome rel (ClassExpr.intersect (.oneOf (namedInds.map Individual.named) :: ces))) anchor :: others }) = some r' at h
    cases hlk : extractFirstIndLink iv mentioning with
    | none => rw [hlk] at h; cases h
    | some res =>
      rcases res with ⟨rel, anchor, restMent⟩
      rw [hlk] at h; dsimp only at h
      cases hces : restMent.mapM (encodeUnaryAtom iv) with
      | none => rw [hces] at h; cases h
      | some ces =>
        rw [hces] at h; dsimp only at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hAncNe, linkAtom, hLinkMent, hLinkForm, hRestSub, hMentCov⟩ := extractFirstIndLink_spec hlk
        have hLinkBody : linkAtom ∈ r.body := (List.mem_filter.mp hLinkMent).1
        obtain ⟨hCeFwd, hCeBwd⟩ := mem_mapM_some hces
        have hIVarsSub : ∀ v, v ∈ ({ body := SWRLAtom.classAtom (.objectSome rel (ClassExpr.intersect (.oneOf (namedInds.map Individual.named) :: ces))) anchor :: others, head := r.head } : SWRLRule).iVars → v ∈ r.iVars := by
          intro v hv
          simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars,
            List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons] at hv ⊢
          rcases hv with ⟨a, rfl | haOth, hva⟩ | hhd
          · left
            refine ⟨linkAtom, hLinkBody, ?_⟩
            rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
            · exact List.mem_eraseDups.mpr (List.mem_append_left _ hva)
            · exact List.mem_eraseDups.mpr (List.mem_append_right _ hva)
          · left; exact ⟨a, (List.mem_filter.mp haOth).1, hva⟩
          · right; exact hhd
        have hIVarsBack : ∀ v ∈ r.iVars, v = iv ∨ v ∈ ({ body := SWRLAtom.classAtom (.objectSome rel (ClassExpr.intersect (.oneOf (namedInds.map Individual.named) :: ces))) anchor :: others, head := r.head } : SWRLRule).iVars := by
          intro v hv
          by_cases hviv : v = iv
          · exact Or.inl hviv
          · right
            simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars,
              List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons] at hv ⊢
            rcases hv with ⟨a, haBody, hva⟩ | hhd
            · by_cases hcont : a.iVars.contains iv
              · have haMent : a ∈ mentioning := List.mem_filter.mpr ⟨haBody, hcont⟩
                rcases hMentCov a haMent with rfl | haRest
                · left
                  refine ⟨_, Or.inl rfl, ?_⟩
                  rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
                  · simp only [SWRLAtom.iVars, List.mem_eraseDups, List.mem_append, IArg.vars, List.mem_singleton] at hva
                    exact hva.elim id (fun e => absurd e hviv)
                  · simp only [SWRLAtom.iVars, List.mem_eraseDups, List.mem_append, IArg.vars, List.mem_singleton] at hva
                    exact hva.elim (fun e => absurd e hviv) id
                · obtain ⟨ce, _, hEnc⟩ := hCeFwd a haRest
                  exact absurd (encodeUnaryAtom_iVars_sub hEnc v hva) hviv
              · left
                have hnotb : (!a.iVars.contains iv) = true := by
                  cases hc : a.iVars.contains iv
                  · rfl
                  · exact absurd hc hcont
                exact ⟨a, Or.inr (List.mem_filter.mpr ⟨haBody, hnotb⟩), hva⟩
            · right; exact hhd
        have hIvInR : iv ∈ r.iVars := by
          refine iVars_mem_of_body hLinkBody ?_
          rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
          · exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_singleton_self _))
          · exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_singleton_self _))
        constructor
        · intro hr' σI σD hBound hbody a ha
          refine hr' σI σD (fun v hv => hBound v (hIVarsSub v hv)) ?_ a ha
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hbOth
          · simp only [atomHolds, classHolds]
            refine ⟨σI iv, ?_, ?_⟩
            · have hLkH := hbody linkAtom hLinkBody
              rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
              · exact hLkH
              · exact (objectHolds_converse i rel0 (evalIArg i σI anchor) (σI iv)).mpr hLkH
            · rw [classHolds_intersect]
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hc'
              · obtain ⟨ind, hindMem, hσiv⟩ := hBound iv hIvInR
                exact ⟨.named ind, List.mem_map_of_mem hindMem, hσiv.symm⟩
              · obtain ⟨a0, ha0Rest, hEnc⟩ := hCeBwd c hc'
                have ha0Body : a0 ∈ r.body := (List.mem_filter.mp (hRestSub a0 ha0Rest)).1
                exact (encodeUnaryAtom_holds_iff bSem i iv σI σD hEnc).mpr (hbody a0 ha0Body)
          · exact hbody b (List.mem_filter.mp hbOth).1
        · intro hr σI σD hBound' hbody' a ha
          have hEx := hbody' _ (List.mem_cons_self ..)
          simp only [atomHolds, classHolds] at hEx
          obtain ⟨y, hrel, hyFill⟩ := hEx
          rw [classHolds_intersect] at hyFill
          have hGuard := hyFill (.oneOf (namedInds.map Individual.named)) (List.mem_cons_self ..)
          obtain ⟨ind', hind'Mem, hind'Eq⟩ := hGuard
          obtain ⟨aName, haNameMem, rfl⟩ := List.mem_map.mp hind'Mem
          let σI' : IRI → i.Object := fun w => if w == iv then y else σI w
          have hσI'iv : σI' iv = y := by simp [σI']
          have hAncEq : evalIArg i σI' anchor = evalIArg i σI anchor := by
            cases anchor with
            | ind _ => rfl
            | var u =>
              have hne : u ≠ iv := fun e => hAncNe (e ▸ rfl)
              simp [evalIArg, σI', hne]
          have hBound : ∀ v ∈ r.iVars, ∃ x ∈ namedInds, σI' v = i.individuals (.named x) := by
            intro v hv
            rcases hIVarsBack v hv with rfl | hv'
            · exact ⟨aName, haNameMem, hσI'iv.trans hind'Eq.symm⟩
            · by_cases hviv : v = iv
              · subst hviv; exact ⟨aName, haNameMem, hσI'iv.trans hind'Eq.symm⟩
              · obtain ⟨x, hxMem, hxEq⟩ := hBound' v hv'
                exact ⟨x, hxMem, by simp [σI', hviv, hxEq]⟩
          have hHeadAgree : ∀ v ∈ a.iVars, σI' v = σI v := fun v hv => by
            have hne : v ≠ iv := by
              intro heq; subst heq
              have hmem : v ∈ r.headIVars :=
                List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨a, ha, hv⟩)
              exact hNotHead (List.contains_iff_mem.mpr hmem)
            simp [σI', hne]
          have hBody' : ∀ b ∈ r.body, atomHolds bSem i σI' σD b := by
            intro b hb
            by_cases hcont : b.iVars.contains iv
            · have hbMent : b ∈ mentioning := List.mem_filter.mpr ⟨hb, hcont⟩
              rcases hMentCov b hbMent with rfl | hbRest
              · rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
                · simp only [atomHolds]; rw [hAncEq]; simp only [evalIArg, hσI'iv]; exact hrel
                · simp only [atomHolds]; rw [hAncEq]; simp only [evalIArg, hσI'iv]
                  exact (objectHolds_converse i rel0 (evalIArg i σI anchor) y).mp hrel
              · obtain ⟨ce, hceMem, hEnc⟩ := hCeFwd b hbRest
                exact (encodeUnaryAtom_holds_iff bSem i iv σI' σD hEnc).mp
                  (hσI'iv.symm ▸ hyFill ce (List.mem_cons_of_mem _ hceMem))
            · have hnotb : (!b.iVars.contains iv) = true := by
                cases hc : b.iVars.contains iv
                · rfl
                · exact absurd hc hcont
              have hbOth : b ∈ others := List.mem_filter.mpr ⟨hb, hnotb⟩
              have hAgreeB : ∀ v ∈ b.iVars, σI' v = σI v := fun v hv => by
                have hne : v ≠ iv := fun heq => hcont (List.contains_iff_mem.mpr (heq ▸ hv))
                simp [σI', hne]
              exact (atomHolds_iVars_congr bSem i hAgreeB).mpr (hbody' b (List.mem_cons_of_mem _ hbOth))
          exact (atomHolds_iVars_congr bSem i hHeadAgree).mp (hr σI' σD hBound hBody' a ha)

/-- Iteratively roll up all eliminable body-only individual variables in `r`. -/
def rollupLocalIndVars (namedInds : List IRI) (r : SWRLRule) : SWRLRule :=
  r.bodyIVars.foldl (fun cur iv => (rollupOneIndVar namedInds cur iv).getD cur) r

theorem rollupLocalIndVars_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} (r : SWRLRule) :
    satisfiesDLSafeRule bSem namedInds i (rollupLocalIndVars namedInds r) ↔
      satisfiesDLSafeRule bSem namedInds i r := by
  unfold rollupLocalIndVars
  have hfold : ∀ (vars : List IRI) (cur : SWRLRule),
      satisfiesDLSafeRule bSem namedInds i
        (vars.foldl (fun c iv => (rollupOneIndVar namedInds c iv).getD c) cur) ↔
      satisfiesDLSafeRule bSem namedInds i cur := by
    intro vars
    induction vars with
    | nil => intro cur; exact Iff.rfl
    | cons v rest ih =>
      intro cur
      simp only [List.foldl_cons]
      refine (ih _).trans ?_
      cases hstep : rollupOneIndVar namedInds cur v with
      | none => exact Iff.rfl
      | some cur' => exact rollupOneIndVar_holds_iff bSem hstep
  exact hfold r.bodyIVars r

private theorem satisfiesDLSafeRule_subst_one_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r : SWRLRule} {v : IRI} (hv : v ∈ r.iVars) :
    (∀ a ∈ namedInds, satisfiesDLSafeRule bSem namedInds i (r.subst [(v, .named a)] [])) ↔
      satisfiesDLSafeRule bSem namedInds i r := by
  have hEqD : ∀ σD : IRI → i.Data, applyEnvD i [] σD = σD := fun _ => by funext w; rfl
  constructor
  · intro hall σI σD hBound hbody hAtom hMem
    obtain ⟨a, haMem, hσv⟩ := hBound v hv
    have hAgree : ∀ w, applyEnvI i [(v, .named a)] σI w = σI w := fun w => by
      simp only [applyEnvI, List.lookup]
      cases hwk : (w == v) with
      | true => have e := beq_iff_eq.mp hwk; subst e; exact hσv.symm
      | false => rfl
    have hSubVars : ∀ w ∈ (r.subst [(v, .named a)] []).iVars, w ∈ r.iVars := by
      intro w hw
      simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars, SWRLRule.subst,
        List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map] at hw ⊢
      have hAtomVar : ∀ (at0 : SWRLAtom), w ∈ (at0.subst [(v, .named a)] []).iVars → w ∈ at0.iVars := by
        intro at0 hat
        have hIArg : ∀ (x : IArg), w ∈ (x.subst [(v, .named a)]).vars → w ∈ x.vars := fun x hx => by
          cases x with
          | ind _ => cases hx
          | var u =>
            simp only [IArg.subst, List.lookup] at hx
            cases huv : (u == v)
            · simp [huv] at hx; exact hx
            · simp [huv, IArg.vars] at hx
        cases at0 with
        | classAtom _ x => exact hIArg x hat
        | dataRangeAtom _ _ => cases hat
        | objectPropertyAtom _ x y | sameIndividualAtom x y | differentIndividualsAtom x y =>
          simp only [SWRLAtom.subst, SWRLAtom.iVars, List.mem_eraseDups, List.mem_append] at hat ⊢
          exact hat.elim (fun h1 => Or.inl (hIArg x h1)) (fun h2 => Or.inr (hIArg y h2))
        | dataPropertyAtom _ x _ => exact hIArg x hat
        | builtinAtom _ _ => cases hat
      rcases hw with ⟨_, ⟨b0, hb0, rfl⟩, hwb⟩ | ⟨_, ⟨a0, ha0, rfl⟩, hwa⟩
      · exact Or.inl ⟨b0, hb0, hAtomVar b0 hwb⟩
      · exact Or.inr ⟨a0, ha0, hAtomVar a0 hwa⟩
    have hSubBody : ∀ b ∈ (r.subst [(v, .named a)] []).body, atomHolds bSem i σI σD b := by
      intro b hb
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      rw [atomHolds_subst_iff, hEqD]
      exact (atomHolds_iVars_congr bSem i fun w _ => hAgree w).mpr (hbody b0 hb0)
    have hRes := hall a haMem σI σD (fun w hw => hBound w (hSubVars w hw)) hSubBody
      (hAtom.subst [(v, .named a)] []) (List.mem_map_of_mem hMem)
    rw [atomHolds_subst_iff, hEqD] at hRes
    exact (atomHolds_iVars_congr bSem i fun w _ => hAgree w).mp hRes
  · intro hr a haMem σI σD hBound hbody hAtom hMem
    obtain ⟨a0, ha0Mem, rfl⟩ := List.mem_map.mp hMem
    rw [atomHolds_subst_iff, hEqD]
    let σI' := applyEnvI i [(v, .named a)] σI
    have hBound' : ∀ w ∈ r.iVars, ∃ x ∈ namedInds, σI' w = i.individuals (.named x) := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv; exact ⟨a, haMem, by simp [σI', applyEnvI, List.lookup]⟩
      · have hwSub : w ∈ (r.subst [(v, .named a)] []).iVars := by
          have hIArg : ∀ (x : IArg), w ∈ x.vars → w ∈ (x.subst [(v, .named a)]).vars := fun x hx => by
            cases x with
            | ind _ => cases hx
            | var u =>
              have huw : w = u := List.mem_singleton.mp hx; subst huw
              simp [IArg.subst, List.lookup, beq_false_of_ne hwv, IArg.vars]
          have hAtomVar : ∀ (at0 : SWRLAtom), w ∈ at0.iVars → w ∈ (at0.subst [(v, .named a)] []).iVars := by
            intro at0 hat
            cases at0 with
            | classAtom _ x => exact hIArg x hat
            | dataRangeAtom _ _ => cases hat
            | objectPropertyAtom _ x y | sameIndividualAtom x y | differentIndividualsAtom x y =>
              simp only [SWRLAtom.subst, SWRLAtom.iVars, List.mem_eraseDups, List.mem_append] at hat ⊢
              exact hat.elim (fun h1 => Or.inl (hIArg x h1)) (fun h2 => Or.inr (hIArg y h2))
            | dataPropertyAtom _ x _ => exact hIArg x hat
            | builtinAtom _ _ => cases hat
          simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars, SWRLRule.subst,
            List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map] at hw ⊢
          rcases hw with ⟨b0, hb0, hwb⟩ | ⟨a0', ha0', hwa⟩
          · exact Or.inl ⟨b0.subst [(v, .named a)] [], ⟨b0, hb0, rfl⟩, hAtomVar b0 hwb⟩
          · exact Or.inr ⟨a0'.subst [(v, .named a)] [], ⟨a0', ha0', rfl⟩, hAtomVar a0' hwa⟩
        obtain ⟨x, hxMem, hxEq⟩ := hBound w hwSub
        exact ⟨x, hxMem, by simp [σI', applyEnvI, List.lookup, beq_false_of_ne hwv, hxEq]⟩
    have hBody' : ∀ b ∈ r.body, atomHolds bSem i σI' σD b := fun b hb => by
      have h1 := hbody (b.subst [(v, .named a)] []) (List.mem_map_of_mem hb)
      rw [atomHolds_subst_iff, hEqD] at h1
      exact h1
    exact hr σI' σD hBound' hBody' a0 ha0Mem

/-! ### 4. Unified Exact Encoding for Data-Variable-Free DL-Safe Rules -/

/-- Recursive tree-rolling + partial-grounding encoder for any data-variable-free DL-safe rule:
    - Iteratively rolls up body-only individual variables into nominal-guarded `∃r.(oneOf(N) ⊓ …)`.
    - Encodes 0-variable rules via `encodeSingleIndGroundRule` (no `topObjectProperty`) or `encodeGroundRule`.
    - Encodes 1-variable rules via `encodeUnaryRule` (1 axiom per head atom, $O(1)$ in $|N_I|$).
    - For $\ge 2$ variables, instantiates the trailing variable over `namedInds` and recurses so
      tree/chain/diamond rules collapse to linear $O(|N_I|)$ ordinary OWL 2 axioms. -/
def encodeRuleSmartAux (namedInds : List IRI) : Nat → SWRLRule → Option (List Axiom)
  | 0, r => groundRuleAll namedInds r
  | fuel + 1, r =>
    let r' := rollupLocalIndVars namedInds r
    match r'.iVars with
    | [] =>
      match encodeSingleIndGroundRule r' with
      | some axs => some axs
      | none => encodeGroundRule r'
    | [_] =>
      match encodeUnaryRule namedInds r' with
      | some axs => some axs
      | none => groundRuleAll namedInds r'
    | vs =>
      match vs.getLast? with
      | none => groundRuleAll namedInds r'
      | some v =>
        (namedInds.mapM fun a =>
          encodeRuleSmartAux namedInds fuel (r'.subst [(v, .named a)] [])).map List.flatten

private theorem getLast?_mem {α : Type} {xs : List α} {x : α} (h : xs.getLast? = some x) :
    x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a tl ih =>
    cases tl with
    | nil => simp at h; subst h; exact List.mem_cons_self ..
    | cons b tl' =>
      simp only [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem encodeRuleSmartAux_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} :
    ∀ (fuel : Nat) {r : SWRLRule} {axs : List Axiom},
      encodeRuleSmartAux namedInds fuel r = some axs →
      (satisfies i axs ↔ satisfiesDLSafeRule bSem namedInds i r)
  | 0, _, _, h => groundRuleAll_holds_iff bSem h
  | fuel + 1, r, axs, h => by
    unfold encodeRuleSmartAux at h
    dsimp only at h
    let r' := rollupLocalIndVars namedInds r
    have hRoll := rollupLocalIndVars_holds_iff bSem (namedInds := namedInds) (i := i) r
    suffices satisfies i axs ↔ satisfiesDLSafeRule bSem namedInds i r' from this.trans hRoll
    change (match r'.iVars with
      | [] => match encodeSingleIndGroundRule r' with | some axs => some axs | none => encodeGroundRule r'
      | [_] => match encodeUnaryRule namedInds r' with | some axs => some axs | none => groundRuleAll namedInds r'
      | vs => match vs.getLast? with
        | none => groundRuleAll namedInds r'
        | some v => (namedInds.mapM fun a => encodeRuleSmartAux namedInds fuel (r'.subst [(v, .named a)] [])).map List.flatten) = some axs at h
    cases hvars : r'.iVars with
    | nil =>
      rw [hvars] at h
      cases hs : encodeSingleIndGroundRule r' with
      | some sAxs =>
        rw [hs] at h; cases h
        constructor
        · intro hsat σI σD _ hbody a ha
          exact (encodeSingleIndGroundRule_holds_iff bSem i σI σD hs).mp hsat hbody a ha
        · intro hr
          obtain ⟨w0⟩ := i.objectNonempty
          let y0 : i.Data := i.literalValue ⟨"0", xsd "integer"⟩
          exact (encodeSingleIndGroundRule_holds_iff bSem i (fun _ => w0) (fun _ => y0) hs).mpr
            (hr (fun _ => w0) (fun _ => y0) (fun v hv => by rw [hvars] at hv; cases hv))
      | none =>
        rw [hs] at h
        constructor
        · intro hsat σI σD _ hbody a ha
          exact (encodeGroundRule_holds_iff bSem i σI σD h).mp hsat hbody a ha
        · intro hr
          obtain ⟨w0⟩ := i.objectNonempty
          let y0 : i.Data := i.literalValue ⟨"0", xsd "integer"⟩
          exact (encodeGroundRule_holds_iff bSem i (fun _ => w0) (fun _ => y0) h).mpr
            (hr (fun _ => w0) (fun _ => y0) (fun v hv => by rw [hvars] at hv; cases hv))
    | cons v1 tl =>
      cases tl with
      | nil =>
        rw [hvars] at h
        cases hu : encodeUnaryRule namedInds r' with
        | some uAxs => rw [hu] at h; cases h; exact encodeUnaryRule_holds_iff bSem hu
        | none => rw [hu] at h; exact groundRuleAll_holds_iff bSem h
      | cons v2 tl2 =>
        rw [hvars] at h; dsimp only at h
        cases hlast : (v1 :: v2 :: tl2).getLast? with
        | none => rw [hlast] at h; dsimp only at h; exact groundRuleAll_holds_iff bSem h
        | some v =>
          rw [hlast] at h; dsimp only at h
          have hvMem : v ∈ r'.iVars := by rw [hvars]; exact getLast?_mem hlast
          cases hM : namedInds.mapM (fun a => encodeRuleSmartAux namedInds fuel (r'.subst [(v, .named a)] [])) with
          | none => rw [hM] at h; cases h
          | some axLists =>
            rw [hM] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            obtain ⟨hFwd, hBwd⟩ := mem_mapM_some hM
            rw [← satisfiesDLSafeRule_subst_one_iff bSem hvMem]
            constructor
            · intro hsat a ha
              obtain ⟨rAxs, hrAxsMem, hRec⟩ := hFwd a ha
              exact (encodeRuleSmartAux_holds_iff bSem fuel hRec).mp fun ax hax =>
                hsat ax (List.mem_flatten.mpr ⟨rAxs, hrAxsMem, hax⟩)
            · intro hall ax hax
              obtain ⟨rAxs, hrAxsMem, haxIn⟩ := List.mem_flatten.mp hax
              obtain ⟨a, haMem, hRec⟩ := hBwd rAxs hrAxsMem
              exact (encodeRuleSmartAux_holds_iff bSem fuel hRec).mpr (hall a haMem) ax haxIn

/-- Encode a data-variable-free DL-safe rule using tree-shaped individual roll-up,
    nominal-guarded unary encoding, direct single-individual grounding, and recursive
    partial grounding (with exact `topObjectProperty` fallback for disconnected ground rules). -/
def encodeDLSafeRule (namedInds : List IRI) (r : SWRLRule) : Option (List Axiom) :=
  encodeRuleSmartAux namedInds (r.iVars.length + 1) r

theorem encodeDLSafeRule_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r : SWRLRule} {axs : List Axiom}
    (h : encodeDLSafeRule namedInds r = some axs) :
    satisfies i axs ↔ satisfiesDLSafeRule bSem namedInds i r :=
  encodeRuleSmartAux_holds_iff bSem (r.iVars.length + 1) h

/-- Encode a list of data-variable-free DL-safe rules into OWL 2 DL axioms. -/
def groundAllRules (namedInds : List IRI) (rules : List SWRLRule) : Option (List Axiom) :=
  (rules.mapM (encodeDLSafeRule namedInds)).map List.flatten

theorem groundAllRules_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {rules : List SWRLRule} {axs : List Axiom}
    (h : groundAllRules namedInds rules = some axs) :
    satisfies i axs ↔ ∀ r ∈ rules, satisfiesDLSafeRule bSem namedInds i r := by
  unfold groundAllRules at h
  cases hM : rules.mapM (encodeDLSafeRule namedInds) with
  | none => rw [hM] at h; cases h
  | some axLists =>
    rw [hM] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    obtain ⟨hFwd, hBwd⟩ := mem_mapM_some hM
    constructor
    · intro hsat r hr
      obtain ⟨rAxs, hrAxsMem, hEnc⟩ := hFwd r hr
      exact (encodeDLSafeRule_holds_iff bSem hEnc).mp fun ax hax =>
        hsat ax (List.mem_flatten.mpr ⟨rAxs, hrAxsMem, hax⟩)
    · intro hall ax hax
      obtain ⟨rAxs, hrAxsMem, haxIn⟩ := List.mem_flatten.mp hax
      obtain ⟨r, hrMem, hEnc⟩ := hBwd rAxs hrAxsMem
      exact (encodeDLSafeRule_holds_iff bSem hEnc).mpr (hall r hrMem) ax haxIn

/-- Headline equisatisfiability theorem for DL-Safe SWRL reduction to OWL 2 DL. -/
theorem groundAllRules_sat_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {o : Ontology} {rules : List SWRLRule} {ruleAxs : List Axiom}
    (h : groundAllRules namedInds rules = some ruleAxs) :
    Satisfiable dm (o ++ ruleAxs) ↔ SatisfiableWithRules dm bSem namedInds o rules := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    refine ⟨i, assign, fun ax hax => hsat ax (List.mem_append_left _ hax), ?_⟩
    exact (groundAllRules_holds_iff bSem h).mp fun ax hax => hsat ax (List.mem_append_right _ hax)
  · rintro ⟨i, assign, hsatO, hsatR⟩
    refine ⟨i, assign, fun ax hax => ?_⟩
    rcases List.mem_append.mp hax with h1 | h2
    · exact hsatO ax h1
    · exact (groundAllRules_holds_iff bSem h).mpr hsatR ax h2

/-- Headline entailment-preservation theorem for DL-Safe SWRL reduction to OWL 2 DL. -/
theorem groundAllRules_entails_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {o q : Ontology} {rules : List SWRLRule} {ruleAxs : List Axiom}
    (h : groundAllRules namedInds rules = some ruleAxs) :
    Entails dm (o ++ ruleAxs) q ↔ EntailsWithRules dm bSem namedInds o rules q := by
  have hmod : ∀ i : Interpretation dm,
      models i (o ++ ruleAxs) ↔ modelsWithRules bSem namedInds i o rules := fun i => by
    constructor
    · rintro ⟨assign, hsat⟩
      exact ⟨assign, fun ax hax => hsat ax (List.mem_append_left _ hax),
        (groundAllRules_holds_iff bSem h).mp fun ax hax => hsat ax (List.mem_append_right _ hax)⟩
    · rintro ⟨assign, hsatO, hsatR⟩
      exact ⟨assign, fun ax hax => (List.mem_append.mp hax).elim (hsatO ax)
        ((groundAllRules_holds_iff bSem h).mpr hsatR ax)⟩
  constructor
  · intro hent i hmodR; exact hent i ((hmod i).mpr hmodR)
  · intro hent i hmodO; exact hent i ((hmod i).mp hmodO)

/-! ### 5. Local Data-Variable Roll-Up (`rollupLocalDataVars`) -/

/-- Extract a data-range constraint on data variable `dv` from a body atom, if it constrains
    only `dv` (`dataRangeAtom dr (.var dv)` or a facet-reducible `builtinAtom`). -/
def extractDVarConstraint (dv : IRI) : SWRLAtom → Option DataRange
  | .dataRangeAtom dr (.var w) => if w == dv then some dr else none
  | .builtinAtom b args =>
    match builtinToDataRange? b args with
    | some (w, dr) => if w == dv then some dr else none
    | none => none
  | _ => none

/-- Combine rolled-up data-range constraints on a single local data variable. -/
def rollupDataRange : List DataRange → DataRange
  | [] => .datatype literalDatatype
  | [d] => d
  | ds => DataRange.intersect ds

/-- Attempt to roll up a single local data variable `dv` in `r`:
    succeeds when `dv` does not occur in `r.head`, occurs in exactly one
    `dataPropertyAtom p arg1 (.var dv)` in `r.body`, and every other body atom
    mentioning `dv` is a `dataRangeAtom` or facet-reducible built-in on `dv`. -/
def rollupOneDataVar (r : SWRLRule) (dv : IRI) : Option SWRLRule :=
  if r.headDVars.contains dv then none
  else
    let mentioning := r.body.filter fun a => a.dVars.contains dv
    let others := r.body.filter fun a => !a.dVars.contains dv
    let dpAtoms := mentioning.filterMap fun
      | .dataPropertyAtom p arg1 (.var w) => if w == dv then some (p, arg1) else none
      | _ => none
    let nonDpAtoms := mentioning.filter fun
      | .dataPropertyAtom _ _ (.var w) => !(w == dv)
      | _ => true
    match dpAtoms with
    | [(p, arg1)] =>
      match nonDpAtoms.mapM (extractDVarConstraint dv) with
      | some drs =>
        some { r with body := .classAtom (.dataSome p (rollupDataRange drs)) arg1 :: others }
      | none => none
    | _ => none

/-- Iteratively roll up all local data variables in `r` into existential data restrictions. -/
def rollupLocalDataVars (r : SWRLRule) : SWRLRule :=
  r.bodyDVars.foldl (fun cur dv => (rollupOneDataVar cur dv).getD cur) r

private theorem evalDArg_eq_of_agree {dm : DatatypeMap} (i : Interpretation dm)
    {σ₁ σ₂ : IRI → i.Data} {a : DArg}
    (h : ∀ v ∈ a.vars, σ₁ v = σ₂ v) :
    evalDArg i σ₁ a = evalDArg i σ₂ a := by
  cases a with
  | lit _ => rfl
  | var v => exact h v (List.mem_cons_self ..)

private theorem atomHolds_dVars_congr {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) {σI : IRI → i.Object} {σD₁ σD₂ : IRI → i.Data} {a : SWRLAtom}
    (h : ∀ v ∈ a.dVars, σD₁ v = σD₂ v) :
    atomHolds bSem i σI σD₁ a ↔ atomHolds bSem i σI σD₂ a := by
  cases a with
  | classAtom _ _ => rfl
  | dataRangeAtom dr x =>
    simp only [atomHolds]; rw [evalDArg_eq_of_agree i h]
  | objectPropertyAtom _ _ _ => rfl
  | dataPropertyAtom p x y =>
    simp only [atomHolds]; rw [evalDArg_eq_of_agree i h]
  | sameIndividualAtom _ _ => rfl
  | differentIndividualsAtom _ _ => rfl
  | builtinAtom b args =>
    simp only [atomHolds]
    have hmap : args.map (evalDArg i σD₁) = args.map (evalDArg i σD₂) := by
      apply List.map_congr_left
      intro arg harg
      exact evalDArg_eq_of_agree i fun v hv =>
        h v (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨arg, harg, hv⟩))
    rw [hmap]

private theorem dataHolds_intersect_iff {dm : DatatypeMap} (i : Interpretation dm) (y : i.Data)
    (drs : List DataRange) :
    dataHolds i y (DataRange.intersect drs) ↔ ∀ d ∈ drs, dataHolds i y d := by
  induction drs with
  | nil => simp [DataRange.intersect, dataHolds, i.literalDatatypeExt]
  | cons d rest ih =>
    simp only [DataRange.intersect, List.foldr_cons, dataHolds, List.mem_cons]
    change (dataHolds i y d ∧ dataHolds i y (DataRange.intersect rest)) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hd, hrest⟩ x (rfl | hx)
      · exact hd
      · exact hrest x hx
    · intro hall
      exact ⟨hall d (Or.inl rfl), fun x hx => hall x (Or.inr hx)⟩

private theorem rollupDataRange_holds_iff {dm : DatatypeMap} (i : Interpretation dm) (y : i.Data)
    (drs : List DataRange) :
    dataHolds i y (rollupDataRange drs) ↔ ∀ d ∈ drs, dataHolds i y d := by
  cases drs with
  | nil => simp [rollupDataRange, dataHolds, i.literalDatatypeExt]
  | cons d tl =>
    cases tl with
    | nil => simp [rollupDataRange]
    | cons d2 tl2 =>
      simpa [rollupDataRange] using dataHolds_intersect_iff i y (d :: d2 :: tl2)

private theorem extractDVarConstraint_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (dv : IRI) (σI : IRI → i.Object) (σD : IRI → i.Data)
    (hBuiltin : ∀ b args w dr, builtinToDataRange? b args = some (w, dr) →
      (atomHolds bSem i σI σD (.builtinAtom b args) ↔ dataHolds i (σD w) dr))
    {a : SWRLAtom} {dr : DataRange} (h : extractDVarConstraint dv a = some dr) :
    atomHolds bSem i σI σD a ↔ dataHolds i (σD dv) dr := by
  cases a with
  | dataRangeAtom d arg =>
    cases arg with
    | lit _ => simp [extractDVarConstraint] at h
    | var w =>
      simp only [extractDVarConstraint] at h
      split at h
      · rename_i hw; have e := beq_iff_eq.mp hw; subst e; cases h; rfl
      · cases h
  | builtinAtom b args =>
    cases hb : builtinToDataRange? b args with
    | none => simp [extractDVarConstraint, hb] at h
    | some p =>
      rcases p with ⟨w, d⟩
      simp only [extractDVarConstraint, hb] at h
      split at h
      · rename_i hw; have e := beq_iff_eq.mp hw; subst e; cases h
        exact hBuiltin b args w dr hb
      · cases h
  | classAtom _ _ | objectPropertyAtom _ _ _ | dataPropertyAtom _ _ _
  | sameIndividualAtom _ _ | differentIndividualsAtom _ _ =>
    simp [extractDVarConstraint] at h

/-- Kernel-verified semantic equivalence of local data-variable roll-up:
    whenever `rollupOneDataVar r dv = some r'` (and any rolled-up built-in matches its
    data-range lowering in `i`), `r'` has the exact same DL-safe semantics as `r`. -/
theorem rollupOneDataVar_holds_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r r' : SWRLRule} {dv : IRI}
    (hBuiltin : ∀ σI σD b args w dr, builtinToDataRange? b args = some (w, dr) →
      (atomHolds bSem i σI σD (.builtinAtom b args) ↔ dataHolds i (σD w) dr))
    (h : rollupOneDataVar r dv = some r') :
    satisfiesDLSafeRule bSem namedInds i r' ↔ satisfiesDLSafeRule bSem namedInds i r := by
  unfold rollupOneDataVar at h
  split at h
  · cases h
  · rename_i hNotHead
    dsimp only at h
    let mentioning := r.body.filter (fun a => a.dVars.contains dv)
    let others := r.body.filter (fun a => !a.dVars.contains dv)
    let dpAtoms := mentioning.filterMap (fun
      | .dataPropertyAtom p arg1 (.var w) => if w == dv then some (p, arg1) else none
      | _ => none)
    let nonDpAtoms := mentioning.filter (fun
      | .dataPropertyAtom _ _ (.var w) => !(w == dv)
      | _ => true)
    change (match dpAtoms with
      | [(p, arg1)] =>
        match nonDpAtoms.mapM (extractDVarConstraint dv) with
        | some drs =>
          some { r with body := .classAtom (.dataSome p (rollupDataRange drs)) arg1 :: others }
        | none => none
      | _ => none) = some r' at h
    cases hdp : dpAtoms with
    | nil => rw [hdp] at h; cases h
    | cons pa rest =>
      cases rest with
      | cons _ _ => rw [hdp] at h; cases h
      | nil =>
        rcases pa with ⟨p, arg1⟩
        rw [hdp] at h
        cases hdrs : nonDpAtoms.mapM (extractDVarConstraint dv) with
        | none => rw [hdrs] at h; cases h
        | some drs =>
          rw [hdrs] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hDrFwd, hDrBwd⟩ := mem_mapM_some hdrs
          have hDpMem : SWRLAtom.dataPropertyAtom p arg1 (.var dv) ∈ r.body := by
            have h1 : (p, arg1) ∈ dpAtoms := by rw [hdp]; exact List.mem_cons_self ..
            obtain ⟨a, haMent, hfa⟩ := List.mem_filterMap.mp h1
            have haBody := (List.mem_filter.mp haMent).1
            cases a with
            | dataPropertyAtom p' arg1' arg2' =>
              cases arg2' with
              | lit _ => simp at hfa
              | var w =>
                simp only at hfa
                split at hfa
                · rename_i hw; have e := beq_iff_eq.mp hw; subst e
                  cases hfa; exact haBody
                · cases hfa
            | _ => simp at hfa
          have hDpUnique : ∀ a ∈ mentioning,
              (match a with | .dataPropertyAtom _ _ (.var w) => w == dv | _ => false) = true →
              a = .dataPropertyAtom p arg1 (.var dv) := by
            intro a haMent hmatch
            cases a with
            | dataPropertyAtom p' arg1' arg2' =>
              cases arg2' with
              | lit _ => simp at hmatch
              | var w =>
                have hw := beq_iff_eq.mp hmatch; subst hw
                have hin : (p', arg1') ∈ dpAtoms :=
                  List.mem_filterMap.mpr ⟨.dataPropertyAtom p' arg1' (.var w), haMent, by simp⟩
                rw [hdp] at hin
                have heq := List.mem_singleton.mp hin
                cases heq; rfl
            | _ => simp at hmatch
          have hIVarsEq : ∀ v, v ∈ ({ body := SWRLAtom.classAtom (.dataSome p (rollupDataRange drs)) arg1 :: others, head := r.head } : SWRLRule).iVars ↔ v ∈ r.iVars := by
            intro v
            simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars,
              List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons]
            constructor
            · rintro (⟨a, rfl | haOth, hv⟩ | hhd)
              · left
                refine ⟨.dataPropertyAtom p arg1 (.var dv), hDpMem, hv⟩
              · left
                exact ⟨a, (List.mem_filter.mp haOth).1, hv⟩
              · right; exact hhd
            · rintro (⟨a, haBody, hv⟩ | hhd)
              · by_cases hcont : a.dVars.contains dv
                · have haMent : a ∈ mentioning := List.mem_filter.mpr ⟨haBody, hcont⟩
                  cases hm : (match a with | .dataPropertyAtom _ _ (.var w) => w == dv | _ => false) with
                  | true =>
                    have haEq := hDpUnique a haMent hm
                    subst haEq
                    left; exact ⟨_, Or.inl rfl, hv⟩
                  | false =>
                    have haNonDp : a ∈ nonDpAtoms := by
                      refine List.mem_filter.mpr ⟨haMent, ?_⟩
                      cases a with
                      | dataPropertyAtom _ _ arg2 =>
                        cases arg2 with
                        | lit _ => rfl
                        | var w => simp at hm; simp [hm]
                      | _ => rfl
                    obtain ⟨d, _, hExt⟩ := hDrFwd a haNonDp
                    cases a with
                    | dataRangeAtom _ _ => simp [SWRLAtom.iVars] at hv
                    | builtinAtom _ _ => simp [SWRLAtom.iVars] at hv
                    | _ => simp [extractDVarConstraint] at hExt
                · left
                  have hnotb : (!a.dVars.contains dv) = true := by
                    cases hc : a.dVars.contains dv
                    · rfl
                    · exact absurd hc hcont
                  exact ⟨a, Or.inr (List.mem_filter.mpr ⟨haBody, hnotb⟩), hv⟩
              · right; exact hhd
          constructor
          · intro hr' σI σD hBound hbody a ha
            have hBound' : ∀ v ∈ ({ body := SWRLAtom.classAtom (.dataSome p (rollupDataRange drs)) arg1 :: others, head := r.head } : SWRLRule).iVars,
                ∃ x ∈ namedInds, σI v = i.individuals (.named x) :=
              fun v hv => hBound v ((hIVarsEq v).mp hv)
            refine hr' σI σD hBound' ?_ a ha
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hbOth
            · simp only [atomHolds, classHolds]
              refine ⟨σD dv, hbody _ hDpMem, (rollupDataRange_holds_iff i (σD dv) drs).mpr fun d hd => ?_⟩
              obtain ⟨a0, ha0NonDp, hExt⟩ := hDrBwd d hd
              have ha0Body : a0 ∈ r.body := (List.mem_filter.mp (List.mem_filter.mp ha0NonDp).1).1
              exact (extractDVarConstraint_holds_iff bSem i dv σI σD (hBuiltin σI σD) hExt).mp (hbody a0 ha0Body)
            · exact hbody b (List.mem_filter.mp hbOth).1
          · intro hr σI σD hBound' hbody' a ha
            have hBound : ∀ v ∈ r.iVars, ∃ x ∈ namedInds, σI v = i.individuals (.named x) :=
              fun v hv => hBound' v ((hIVarsEq v).mpr hv)
            have hEx := hbody' _ (List.mem_cons_self ..)
            simp only [atomHolds, classHolds] at hEx
            obtain ⟨y, hpy, hydr⟩ := hEx
            have hydrs := (rollupDataRange_holds_iff i y drs).mp hydr
            let σD' : IRI → i.Data := fun w => if w == dv then y else σD w
            have hσD'dv : σD' dv = y := by simp [σD']
            have hHeadAgree : ∀ v ∈ a.dVars, σD' v = σD v := fun v hv => by
              have hne : v ≠ dv := by
                intro heq; subst heq
                have hmem : v ∈ r.headDVars :=
                  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨a, ha, hv⟩)
                exact hNotHead (List.contains_iff_mem.mpr hmem)
              simp [σD', hne]
            have hBody' : ∀ b ∈ r.body, atomHolds bSem i σI σD' b := by
              intro b hb
              by_cases hcont : b.dVars.contains dv
              · have hbMent : b ∈ mentioning := List.mem_filter.mpr ⟨hb, hcont⟩
                cases hm : (match b with | .dataPropertyAtom _ _ (.var w) => w == dv | _ => false) with
                | true =>
                  have hbEq := hDpUnique b hbMent hm
                  subst hbEq
                  simp [atomHolds, evalDArg, hσD'dv, hpy]
                | false =>
                  have hbNonDp : b ∈ nonDpAtoms := by
                    refine List.mem_filter.mpr ⟨hbMent, ?_⟩
                    cases b with
                    | dataPropertyAtom _ _ arg2 =>
                      cases arg2 with
                      | lit _ => rfl
                      | var w => simp at hm; simp [hm]
                    | _ => rfl
                  obtain ⟨d, hdMem, hExt⟩ := hDrFwd b hbNonDp
                  exact (extractDVarConstraint_holds_iff bSem i dv σI σD' (hBuiltin σI σD') hExt).mpr
                    (hσD'dv ▸ hydrs d hdMem)
              · have hnotb : (!b.dVars.contains dv) = true := by
                  cases hc : b.dVars.contains dv
                  · rfl
                  · exact absurd hc hcont
                have hbOth : b ∈ others := List.mem_filter.mpr ⟨hb, hnotb⟩
                have hAgreeB : ∀ v ∈ b.dVars, σD' v = σD v := fun v hv => by
                  have hne : v ≠ dv := fun heq => hcont (List.contains_iff_mem.mpr (heq ▸ hv))
                  simp [σD', hne]
                exact (atomHolds_dVars_congr bSem i hAgreeB).mpr (hbody' b (List.mem_cons_of_mem _ hbOth))
            exact (atomHolds_dVars_congr bSem i hHeadAgree).mp (hr σI σD' hBound hBody' a ha)

/-! ### 6. Safe Concrete-Value Grounding for Functional `swrlb:*` Built-ins -/

private def evalDataRangeOnLit (dr : DataRange) (l : Literal) : Option Bool :=
  match decodeLiteral l with
  | none => none
  | some v => some (go dr v)
where
  go : DataRange → Value → Bool
  | .datatype t, v => if t == literalDatatype then true else checkValue t v
  | .complement d, v => !go d v
  | .intersection a b, v => go a v && go b v
  | .union a b, v => go a v || go b v
  | .oneOf ls, v =>
    match ls.mapM decodeLiteral with
    | some vs => vs.contains v
    | none => false
  | .restriction t fs, v =>
    checkValue t v && fs.all fun f =>
      match decodeLiteral f.bound with
      | some bv => checkFacet t f.name bv v
      | none => false

private def evalDArgWithEnv (envD : List (IRI × Literal)) : DArg → Option Value
  | .lit l => decodeLiteral l
  | .var v => (envD.lookup v).bind decodeLiteral

/-- Propagate functional `swrlb:*` built-ins and check ground predicate built-ins
    under a partial data-variable binding `envD`.
    Returns `some (envD', remainingBody)` if consistent, or `none` if a built-in is refuted. -/
private def propagateBuiltinsAux :
    Nat → List (IRI × Literal) → List SWRLAtom → Option (List (IRI × Literal) × List SWRLAtom)
  | 0, envD, body => some (envD, body)
  | fuel + 1, envD, body => Id.run do
    let mut curEnv := envD
    let mut changed := false
    let mut kept : List SWRLAtom := []
    for a in body do
      match a with
      | .builtinAtom b args =>
        if !isSupportedBuiltin b then
          kept := a :: kept
        else
          match args.mapM (evalDArgWithEnv curEnv) with
          | some vals =>
            -- All arguments are bound: evaluate the built-in predicate directly
            if evalBuiltinRel b vals then
              changed := true
            else
              return none
          | none =>
            -- Check if functional built-in with unbound output `args[0]` and all inputs bound
            match args with
            | .var outVar :: inArgs =>
              if isFunctionalBuiltin b && (curEnv.lookup outVar).isNone then
                match inArgs.mapM (evalDArgWithEnv curEnv) with
                | some inVals =>
                  match evalBuiltinOutput? b inVals with
                  | some outVal =>
                    match valueToLiteral? outVal with
                    | some outLit =>
                      if decodeLiteral outLit == some outVal then
                        curEnv := (outVar, outLit) :: curEnv
                        changed := true
                      else
                        kept := a :: kept
                    | none => kept := a :: kept
                  | none => return none
                | none => kept := a :: kept
              else
                kept := a :: kept
            | _ => kept := a :: kept
      | .dataRangeAtom dr arg =>
        match arg.subst curEnv with
        | .lit l =>
          match evalDataRangeOnLit dr l with
          | some true => changed := true
          | some false => return none
          | none => kept := a :: kept
        | .var _ => kept := a :: kept
      | _ => kept := a :: kept
    if changed then
      propagateBuiltinsAux fuel curEnv kept.reverse
    else
      return some (curEnv, kept.reverse)

/-- Extract concrete `(subject, prop, literal)` facts asserted in an ontology. -/
private def extractABoxDataFacts (o : Ontology) : List (IRI × IRI × Literal) :=
  o.filterMap fun
    | .dataAssertion p (.named a) l => some (a, p, l)
    | _ => none

/-- Ground a rule containing concrete-value-safe `swrlb:*` built-ins or shared data variables
    against the named individuals and known ABox data assertions/literals. -/
def groundRuleWithDataBuiltins (o : Ontology) (namedInds : List IRI) (r : SWRLRule) :
    Except String (List Axiom) := do
  -- Reject unsupported built-ins immediately
  for a in r.body do
    if let .builtinAtom b _ := a then
      if !isSupportedBuiltin b then
        throw s!"unsupported SWRL built-in '{b}'"
  let dataFacts := extractABoxDataFacts o
  let allLits := collectKnownLiterals o [r]
  let envsI := allVarAssignments namedInds r.iVars
  let mut outAxs : List Axiom := []
  for envI in envsI do
    let envI' := envI.map fun (v, x) => (v, Individual.named x)
    let rI := r.subst envI' []
    -- Collect candidate literal bindings for each non-builtin body data variable
    let srcDVars := rI.bodyNonBuiltinDVars
    let candLists : List (IRI × List Literal) := srcDVars.map fun dv =>
      let dpHits := rI.body.filterMap fun
        | .dataPropertyAtom p (.ind (.named subj)) (.var w) =>
          if w == dv then some (subj, p) else none
        | _ => none
      let matchedLits :=
        if dpHits.isEmpty then allLits
        else
          (dpHits.flatMap fun (subj, p) =>
            dataFacts.filterMap fun (s, p', l) =>
              if s == subj && p' == p then some l else none).eraseDups
      (dv, matchedLits)
    -- Cartesian product over candidate literal bindings for source data variables
    let mut dEnvs : List (List (IRI × Literal)) := [[]]
    for (dv, lits) in candLists do
      dEnvs := lits.flatMap fun l => dEnvs.map fun e => (dv, l) :: e
    for envD in dEnvs do
      match propagateBuiltinsAux (rI.body.length + 2) envD rI.body with
      | none => pure () -- built-in refuted for this binding; rule holds vacuously
      | some (envD', remBody) =>
        let gr : SWRLRule := {
          body := remBody.map (SWRLAtom.subst [] envD'),
          head := rI.head.map (SWRLAtom.subst [] envD')
        }
        if !gr.dVars.isEmpty || gr.hasBuiltins then
          throw "SWRL rule contains data variables or functional built-ins not bound by ground ABox data values"
        match encodeSingleIndGroundRule gr <|> encodeGroundRule gr with
        | some axs => outAxs := outAxs ++ axs
        | none => throw "failed to encode grounded SWRL rule into OWL 2 DL"
  return outAxs

/-- Lower a list of DL-safe SWRL rules into OWL 2 DL axioms:
    1. Validate DL-safety (`diagnoseDLSafeRules`).
    2. Roll up local data variables and facet-reducible `swrlb:*` built-ins (`rollupLocalDataVars`).
    3. Encode data-variable-free rules via `encodeDLSafeRule` (nominal-guarded unary or exact grounding).
    4. Ground remaining built-in/shared-data-variable rules safely via `groundRuleWithDataBuiltins`. -/
def lowerSWRLRules (o : Ontology) (namedInds : List IRI) (rules : List SWRLRule) :
    Except String (List Axiom) := do
  if let some err := diagnoseDLSafeRules rules then
    throw err
  let mut out : List Axiom := []
  for r in rules do
    let r' := rollupLocalDataVars r
    if !r'.hasDVars && !r'.hasBuiltins then
      match encodeDLSafeRule namedInds r' with
      | some axs => out := out ++ axs
      | none => throw "failed to encode DL-safe SWRL rule into OWL 2 DL"
    else
      let axs ← groundRuleWithDataBuiltins o namedInds r'
      out := out ++ axs
  return out

/-! ### 7. Verified Exact Decision & Lazy CEGAR Loop -/

/-- Exact, kernel-verified decision procedure for OWL 2 DL + data-variable-free DL-Safe SWRL
    under Dedekind-cut `realDatatypeMap`. -/
def decideRealWithSWRL? (o : Ontology) (namedInds : List IRI) (rules : List SWRLRule) : Option Bool :=
  (groundAllRules namedInds rules).bind fun ruleAxs =>
    decideRealOntology? (o ++ ruleAxs)

theorem decideRealWithSWRL_iff {o : Ontology} {namedInds : List IRI} {rules : List SWRLRule}
    {ans : Bool} (h : decideRealWithSWRL? o namedInds rules = some ans) :
    ans = true ↔ SatisfiableWithRules realDatatypeMap realBuiltinSem namedInds o rules := by
  simp only [decideRealWithSWRL?, Option.bind_eq_some_iff] at h
  obtain ⟨ruleAxs, hG, hDec⟩ := h
  exact (decideRealOntology_iff hDec).trans (groundAllRules_sat_iff realBuiltinSem hG)

/-- Evaluate an OWL 2 `ClassExpr` at world `w` in a finite `SROIQDModel`. -/
private def evalClassExprInModel (m : SROIQDModel) (w : m.graph.World) : ClassExpr → Option Bool
  | .named c =>
    if c == thing then some true
    else if c == nothing then some false
    else some (m.graph.atom c w)
  | .complement c => (evalClassExprInModel m w c).map (!·)
  | .intersection a b => do
    return (← evalClassExprInModel m w a) && (← evalClassExprInModel m w b)
  | .union a b => do
    return (← evalClassExprInModel m w a) || (← evalClassExprInModel m w b)
  | .oneOf inds => some (inds.any fun ind => m.indVal ind == w)
  | .objectValue (.named r) ind =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r w (m.indVal ind))
  | .objectValue (.inverse r) ind =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r (m.indVal ind) w)
  | .objectSelf (.named r) =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r w w)
  | .objectSelf (.inverse r) =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r w w)
  | .dataValue dp l =>
    if dp == topDataProperty then some true
    else if dp == bottomDataProperty then some false
    else (decodeLiteral l).map fun v => m.hasDataEdge dp w v
  | .dataSome dp dr =>
    if dp == topDataProperty || dp == bottomDataProperty then none
    else (DataRanges.compile dr).map fun c => (m.dataValues dp w).any c.holds
  | _ => none

/-- Evaluate whether a ground SWRL atom holds in a finite `SROIQDModel`. -/
private def evalGroundAtomInModel (m : SROIQDModel) : SWRLAtom → Option Bool
  | .classAtom c (.ind x) => evalClassExprInModel m (m.indVal x) c
  | .objectPropertyAtom (.named r) (.ind x) (.ind y) =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r (m.indVal x) (m.indVal y))
  | .objectPropertyAtom (.inverse r) (.ind x) (.ind y) =>
    if r == topObjectProperty then some true
    else if r == bottomObjectProperty then some false
    else some (m.graph.edge r (m.indVal y) (m.indVal x))
  | .dataPropertyAtom p (.ind x) (.lit l) =>
    if p == topDataProperty then some true
    else if p == bottomDataProperty then some false
    else (decodeLiteral l).map fun v => m.hasDataEdge p (m.indVal x) v
  | .sameIndividualAtom (.ind x) (.ind y) =>
    some (m.indVal x == m.indVal y)
  | .differentIndividualsAtom (.ind x) (.ind y) =>
    some (m.indVal x != m.indVal y)
  | _ => none

/-- Find a violated ground instance of a multi-variable SWRL rule in a verified finite model `m`.
    Returns `some (some gr)` if a violated ground instance `gr` is found,
    `some none` if all groundings are verified satisfied in `m`, or `none` if uncertain. -/
private def findViolatedGroundRule (m : SROIQDModel) (namedInds : List IRI)
    (rules : List SWRLRule) : Option (Option SWRLRule) := Id.run do
  for r in rules do
    let envs := allVarAssignments namedInds r.iVars
    for env in envs do
      let gr := r.subst (env.map fun (v, a) => (v, Individual.named a)) []
      let mut bodyAllTrue := true
      let mut bodyUncertain := false
      for b in gr.body do
        match evalGroundAtomInModel m b with
        | some false => bodyAllTrue := false; break
        | some true => pure ()
        | none => bodyUncertain := true
      if !bodyAllTrue then continue
      if bodyUncertain then return none
      for h in gr.head do
        match evalGroundAtomInModel m h with
        | some true => pure ()
        | some false => return some (some gr)
        | none => return none
  return some none

/-- Replace occurrences of a specific named individual `ind` with a fresh variable `v` in an `IArg`. -/
private def abstractIndIArg (ind v : IRI) : IArg → IArg
  | .ind (.named x) => if x == ind then .var v else .ind (.named x)
  | a => a

private def abstractIndAtom (ind v : IRI) : SWRLAtom → SWRLAtom
  | .classAtom c a => .classAtom c (abstractIndIArg ind v a)
  | .objectPropertyAtom r a1 a2 => .objectPropertyAtom r (abstractIndIArg ind v a1) (abstractIndIArg ind v a2)
  | .dataPropertyAtom p a1 a2 => .dataPropertyAtom p (abstractIndIArg ind v a1) a2
  | .sameIndividualAtom a1 a2 => .sameIndividualAtom (abstractIndIArg ind v a1) (abstractIndIArg ind v a2)
  | .differentIndividualsAtom a1 a2 => .differentIndividualsAtom (abstractIndIArg ind v a1) (abstractIndIArg ind v a2)
  | a => a

/-- Fold a connected ground SWRL rule into a `topObjectProperty`-free single-anchor axiom
    by rolling up body-only ground individuals via singleton nominal guards `{a}` before
    applying `encodeSingleIndGroundRule`, falling back to `encodeGroundRule` if disconnected. -/
private def encodeGroundRuleSmart (gr : SWRLRule) : Option (List Axiom) :=
  match encodeSingleIndGroundRule gr with
  | some axs => some axs
  | none =>
    let headInds := (gr.head.flatMap SWRLAtom.namedIndividuals).eraseDups
    let bodyOnlyInds := ((gr.body.flatMap SWRLAtom.namedIndividuals).eraseDups).filter fun a =>
      !headInds.contains a
    let folded := bodyOnlyInds.foldl (fun cur a =>
      let v := "urn:swrl:ground#" ++ a
      let absRule : SWRLRule := {
        body := cur.body.map (abstractIndAtom a v),
        head := cur.head
      }
      match rollupOneIndVar [a] absRule v with
      | some rolled => rolled
      | none => cur) gr
    encodeSingleIndGroundRule folded <|> encodeGroundRule gr

/-- Fast verified CEGAR consistency solver for OWL 2 DL + DL-Safe SWRL rules:
    - Small rules (≤ 8 named individuals and compact unary/rolled-up form) are lowered directly.
    - Larger ABoxes (`namedInds.length > 8`) or multi-variable rules are instantiated lazily via
      verified CEGAR only when violated by a kernel-verified countermodel `m`, falling back to
      exact smart encoding + `fastConsistencyCheck` if limits are reached (preserving soundness,
      completeness, and termination). -/
def decideWithSWRLFast? (o : Ontology) (namedInds : List IRI) (rules : List SWRLRule) :
    Except String (Option Bool) := do
  if rules.isEmpty then
    return Classification.fastConsistencyCheck o
  if let some err := diagnoseDLSafeRules rules then
    throw err
  let rolled := rules.map rollupLocalDataVars
  let mut staticAxs : List Axiom := []
  let mut lazyRules : List SWRLRule := []
  for r in rolled do
    if !r.hasDVars && !r.hasBuiltins then
      if namedInds.length > 8 && !r.iVars.isEmpty then
        -- Use verified lazy CEGAR on larger ABoxes to avoid large `oneOf(N)` GCI branching
        lazyRules := lazyRules ++ [r]
      else
        let rInd := rollupLocalIndVars namedInds r
        match encodeUnaryRule namedInds rInd with
        | some axs => staticAxs := staticAxs ++ axs
        | none =>
          let estSize := namedInds.length ^ rInd.iVars.length
          if rInd.iVars.isEmpty || estSize ≤ 64 then
            match encodeDLSafeRule namedInds rInd with
            | some axs => staticAxs := staticAxs ++ axs
            | none => throw "failed to encode DL-safe SWRL rule"
          else
            lazyRules := lazyRules ++ [rInd]
    else
      let axs ← groundRuleWithDataBuiltins o namedInds r
      staticAxs := staticAxs ++ axs
  let baseOnt := o ++ staticAxs
  if lazyRules.isEmpty then
    return Classification.fastConsistencyCheck baseOnt
  -- Verified lazy CEGAR loop for larger ABoxes / multi-variable rules
  let mut activeAxs : List Axiom := []
  let maxRounds := 32
  for _ in List.range maxRounds do
    let curOnt := baseOnt ++ activeAxs
    match Normalize.normalizeWithDefs curOnt with
    | some (_, p) =>
      -- Only trust finite `datatypeMap` countermodels when `owl:real` / built-in data props aren't in play
      let hasRealOrBuiltIn :=
        p.allDataAtoms.any (fun | .datatype t | .restriction t _ => t == owlReal | _ => false) ||
        p.allDataProps.any (fun dp => dp == topDataProperty || dp == bottomDataProperty)
      if hasRealOrBuiltIn then break
      let limits := SROIQD.Limits.forProblem p
      match SROIQD.propose p limits with
      | some ev =>
        if p.checkSimple && SROIQD.checkEvidence p limits.worlds ev then
          if !ev.isModel then
            -- Sound UNSAT: every axiom in `activeAxs` is a proved consequence of `lazyRules`
            return some false
          else
            match ev with
            | .model m =>
              match findViolatedGroundRule m namedInds lazyRules with
              | some none => return some true -- Verified model satisfies all SWRL rules!
              | some (some gr) =>
                match encodeGroundRuleSmart gr with
                | some gAxs => activeAxs := activeAxs ++ gAxs
                | none => break
              | none => break
            | .refutation _ => return some false
        else break
      | none => break
    | none => break
  -- Fallback: smart exact encoding + fast/exact decision (guarantees completeness & termination)
  let mut fullAxs : List Axiom := []
  for r in lazyRules do
    match encodeDLSafeRule namedInds r with
    | some axs => fullAxs := fullAxs ++ axs
    | none => throw "failed to encode DL-safe SWRL rule"
  return Classification.fastConsistencyCheck (baseOnt ++ fullAxs)

#print axioms encodeGroundAtom_holds_iff
#print axioms encodeGroundRule_holds_iff
#print axioms encodeSingleIndGroundRule_holds_iff
#print axioms encodeUnaryRule_holds_iff
#print axioms rollupOneIndVar_holds_iff
#print axioms rollupLocalIndVars_holds_iff
#print axioms groundRuleAll_holds_iff
#print axioms encodeDLSafeRule_holds_iff
#print axioms groundAllRules_holds_iff
#print axioms groundAllRules_sat_iff
#print axioms groundAllRules_entails_iff
#print axioms rollupOneDataVar_holds_iff
#print axioms decideRealWithSWRL_iff

end Sabrina.OWL2.SWRL
