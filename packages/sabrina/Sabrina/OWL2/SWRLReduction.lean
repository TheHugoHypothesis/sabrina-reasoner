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

/-! ### 4b. Nominal-Anchored & Auxiliary-Guard DL-Safe Encoding (Motik–Sattler–Studer) -/

/-- `guard` holds on every named individual in `namedInds` (sufficient for rule soundness). -/
def GuardCovers {dm : DatatypeMap} (namedInds : List IRI) (i : Interpretation dm)
    (guard : ClassExpr) : Prop :=
  ∀ a ∈ namedInds, classHolds i (i.individuals (.named a)) guard

/-- `guard` holds on an object iff it interprets some named individual in `namedInds`. -/
def GuardExact {dm : DatatypeMap} (namedInds : List IRI) (i : Interpretation dm)
    (guard : ClassExpr) : Prop :=
  ∀ x, classHolds i x guard ↔ ∃ a ∈ namedInds, x = i.individuals (.named a)

theorem GuardExact.covers {dm : DatatypeMap} {namedInds : List IRI} {i : Interpretation dm}
    {guard : ClassExpr} (h : GuardExact namedInds i guard) :
    GuardCovers namedInds i guard :=
  fun a ha => (h (i.individuals (.named a))).mpr ⟨a, ha, rfl⟩

/-- Encode a single-variable DL-safe rule `r` (`r.iVars = [v]`) using an explicit domain guard `guard`. -/
def encodeUnaryRuleWithGuard (guard : ClassExpr) (r : SWRLRule) : Option (List Axiom) :=
  match r.iVars with
  | [v] => do
    let bodyCEs ← r.body.mapM (encodeUnaryAtom v)
    let headCEs ← r.head.mapM (encodeUnaryAtom v)
    let lhs := ClassExpr.intersect (guard :: bodyCEs)
    return headCEs.map fun hce => .subClassOf lhs hce
  | _ => none

theorem encodeUnaryRuleWithGuard_sound {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r : SWRLRule} {axs : List Axiom}
    (hCov : GuardCovers namedInds i guard)
    (h : encodeUnaryRuleWithGuard guard r = some axs)
    (hsat : satisfies i axs) :
    satisfiesDLSafeRule bSem namedInds i r := by
  unfold encodeUnaryRuleWithGuard at h
  cases hvars : r.iVars with
  | nil => rw [hvars] at h; cases h
  | cons v rest =>
    cases rest with
    | cons _ _ => rw [hvars] at h; cases h
    | nil =>
      rw [hvars] at h; simp only [bind, Option.bind, pure] at h
      cases hbM : r.body.mapM (encodeUnaryAtom v) with
      | none => rw [hbM] at h; cases h
      | some bodyCEs =>
        rw [hbM] at h
        cases hhM : r.head.mapM (encodeUnaryAtom v) with
        | none => rw [hhM] at h; cases h
        | some headCEs =>
          rw [hhM] at h; simp only [Option.some.injEq] at h; subst h
          obtain ⟨_, hbBwd⟩ := mem_mapM_some hbM
          obtain ⟨hhFwd, _⟩ := mem_mapM_some hhM
          intro σI σD hBound hbody a ha
          obtain ⟨hce, hhceMem, hEncA⟩ := hhFwd a ha
          have hax := hsat (.subClassOf (ClassExpr.intersect (guard :: bodyCEs)) hce)
            (List.mem_map_of_mem hhceMem)
          have hLhs : classHolds i (σI v) (ClassExpr.intersect (guard :: bodyCEs)) := by
            rw [classHolds_intersect]
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc'
            · obtain ⟨ind, hindMem, hσv⟩ := hBound v (by rw [hvars]; exact List.mem_cons_self ..)
              exact hσv.symm ▸ hCov ind hindMem
            · obtain ⟨b, hbMem, hEncB⟩ := hbBwd c hc'
              exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncB).mpr (hbody b hbMem)
          exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncA).mp (hax (σI v) hLhs)

theorem encodeUnaryRuleWithGuard_complete {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r : SWRLRule} {axs : List Axiom}
    (hEx : GuardExact namedInds i guard)
    (h : encodeUnaryRuleWithGuard guard r = some axs)
    (hr : satisfiesDLSafeRule bSem namedInds i r) :
    satisfies i axs := by
  unfold encodeUnaryRuleWithGuard at h
  cases hvars : r.iVars with
  | nil => rw [hvars] at h; cases h
  | cons v rest =>
    cases rest with
    | cons _ _ => rw [hvars] at h; cases h
    | nil =>
      rw [hvars] at h; simp only [bind, Option.bind, pure] at h
      cases hbM : r.body.mapM (encodeUnaryAtom v) with
      | none => rw [hbM] at h; cases h
      | some bodyCEs =>
        rw [hbM] at h
        cases hhM : r.head.mapM (encodeUnaryAtom v) with
        | none => rw [hhM] at h; cases h
        | some headCEs =>
          rw [hhM] at h; simp only [Option.some.injEq] at h; subst h
          obtain ⟨hbFwd, _⟩ := mem_mapM_some hbM
          obtain ⟨_, hhBwd⟩ := mem_mapM_some hhM
          intro ax hax
          obtain ⟨hce, hhceMem, rfl⟩ := List.mem_map.mp hax
          intro x hx
          rw [classHolds_intersect] at hx
          obtain ⟨aName, haNameMem, hind'Eq⟩ := (hEx x).mp (hx guard (List.mem_cons_self ..))
          let σI : IRI → i.Object := fun _ => x
          let σD : IRI → i.Data := fun _ => i.literalValue ⟨"0", xsd "integer"⟩
          obtain ⟨aHead, haHeadMem, hEncA⟩ := hhBwd hce hhceMem
          have hHeadHolds := hr σI σD
            (fun w hw => by
              rw [hvars] at hw
              have := List.mem_singleton.mp hw; subst this
              exact ⟨aName, haNameMem, hind'Eq⟩)
            (fun b hb => by
              obtain ⟨bce, hbceMem, hEncB⟩ := hbFwd b hb
              exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncB).mp
                (hx bce (List.mem_cons_of_mem _ hbceMem)))
            aHead haHeadMem
          exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncA).mpr hHeadHolds

/-- Nominal-anchored encoding for a single-variable rule `r` (`r.iVars = [v]`) whose body
    links `v` to a concrete individual `a` via an object property `rel`. Ground body atoms
    touching `a` are folded directly into the nominal anchor `{a} ⊓ anchorBody`, emitting
    `SubClassOf({a} ⊓ anchorBody, ObjectAllValuesFrom(rel, ¬(guard ⊓ varBody) ⊔ hce))`
    without `owl:topObjectProperty`. -/
def encodeAnchoredUnaryRuleWithGuard (guard : ClassExpr) (r : SWRLRule) : Option (List Axiom) :=
  match r.iVars with
  | [v] =>
    match extractFirstIndLink v r.body with
    | some (rel, .ind a, rest) => do
      let isAnchor := fun b : SWRLAtom => b.iVars.isEmpty && (encodeAtomAt a b).isSome
      let anchorBody := rest.filter isAnchor
      let varBody := rest.filter (fun b => !isAnchor b)
      let anchorCEs ← anchorBody.mapM (encodeAtomAt a)
      let varCEs ← varBody.mapM (encodeUnaryAtom v)
      let headCEs ← r.head.mapM (encodeUnaryAtom v)
      let lhs := ClassExpr.intersect (.oneOf [a] :: anchorCEs)
      let varCond := ClassExpr.intersect (guard :: varCEs)
      return headCEs.map fun hce =>
        .subClassOf lhs (.objectAll rel (.union (.complement varCond) hce))
    | _ => none
  | _ => none

theorem encodeAnchoredUnaryRuleWithGuard_sound {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r : SWRLRule} {axs : List Axiom}
    (hCov : GuardCovers namedInds i guard)
    (h : encodeAnchoredUnaryRuleWithGuard guard r = some axs)
    (hsat : satisfies i axs) :
    satisfiesDLSafeRule bSem namedInds i r := by
  unfold encodeAnchoredUnaryRuleWithGuard at h
  cases hvars : r.iVars with
  | nil => rw [hvars] at h; cases h
  | cons v restVars =>
    cases restVars with
    | cons _ _ => rw [hvars] at h; cases h
    | nil =>
      rw [hvars] at h; dsimp only at h
      cases hlk : extractFirstIndLink v r.body with
      | none => rw [hlk] at h; cases h
      | some res =>
        rcases res with ⟨rel, anchor, rest⟩
        cases anchor with
        | var _ => rw [hlk] at h; cases h
        | ind a =>
          rw [hlk] at h; simp only [bind, Option.bind, pure] at h
          let isAnchor := fun b : SWRLAtom => b.iVars.isEmpty && (encodeAtomAt a b).isSome
          cases haM : (rest.filter isAnchor).mapM (encodeAtomAt a) with
          | none => rw [haM] at h; cases h
          | some anchorCEs =>
            rw [haM] at h; dsimp only at h
            cases hvM : (rest.filter fun b => !isAnchor b).mapM (encodeUnaryAtom v) with
            | none => rw [hvM] at h; cases h
            | some varCEs =>
              rw [hvM] at h; dsimp only at h
              cases hhM : r.head.mapM (encodeUnaryAtom v) with
              | none => rw [hhM] at h; cases h
              | some headCEs =>
                rw [hhM] at h; simp only [Option.some.injEq] at h; subst h
                obtain ⟨_, linkAtom, hLinkBody, hLinkForm, hRestSub, _⟩ := extractFirstIndLink_spec hlk
                obtain ⟨_, haBwd⟩ := mem_mapM_some haM
                obtain ⟨_, hvBwd⟩ := mem_mapM_some hvM
                obtain ⟨hhFwd, _⟩ := mem_mapM_some hhM
                intro σI σD hBound hbody aHead haHead
                obtain ⟨hce, hhceMem, hEncH⟩ := hhFwd aHead haHead
                have hax := hsat
                  (.subClassOf (ClassExpr.intersect (.oneOf [a] :: anchorCEs))
                    (.objectAll rel (.union (.complement (ClassExpr.intersect (guard :: varCEs))) hce)))
                  (List.mem_map_of_mem hhceMem)
                have hLhs : classHolds i (i.individuals a) (ClassExpr.intersect (.oneOf [a] :: anchorCEs)) := by
                  rw [classHolds_intersect]
                  intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc'
                  · exact ⟨a, List.mem_singleton_self _, rfl⟩
                  · obtain ⟨b, hbMem, hEncB⟩ := haBwd c hc'
                    have hbBody : b ∈ r.body := hRestSub b (List.mem_filter.mp hbMem).1
                    exact (encodeAtomAt_holds_iff bSem i a σI σD hEncB).mpr (hbody b hbBody)
                have hRel : objectHolds i rel (i.individuals a) (σI v) := by
                  have hLk := hbody linkAtom hLinkBody
                  rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
                  · exact hLk
                  · exact (objectHolds_converse i rel0 (i.individuals a) (σI v)).mpr hLk
                have hVarCond : classHolds i (σI v) (ClassExpr.intersect (guard :: varCEs)) := by
                  rw [classHolds_intersect]
                  intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc'
                  · obtain ⟨ind, hindMem, hσv⟩ := hBound v (by rw [hvars]; exact List.mem_cons_self ..)
                    exact hσv.symm ▸ hCov ind hindMem
                  · obtain ⟨b, hbMem, hEncB⟩ := hvBwd c hc'
                    have hbBody : b ∈ r.body := hRestSub b (List.mem_filter.mp hbMem).1
                    exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncB).mpr (hbody b hbBody)
                have hDisj := hax (i.individuals a) hLhs (σI v) hRel
                have hHce : classHolds i (σI v) hce := hDisj.resolve_left (fun hNot => hNot hVarCond)
                exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncH).mp hHce

theorem encodeAnchoredUnaryRuleWithGuard_complete {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r : SWRLRule} {axs : List Axiom}
    (hEx : GuardExact namedInds i guard)
    (h : encodeAnchoredUnaryRuleWithGuard guard r = some axs)
    (hr : satisfiesDLSafeRule bSem namedInds i r) :
    satisfies i axs := by
  unfold encodeAnchoredUnaryRuleWithGuard at h
  cases hvars : r.iVars with
  | nil => rw [hvars] at h; cases h
  | cons v restVars =>
    cases restVars with
    | cons _ _ => rw [hvars] at h; cases h
    | nil =>
      rw [hvars] at h; dsimp only at h
      cases hlk : extractFirstIndLink v r.body with
      | none => rw [hlk] at h; cases h
      | some res =>
        rcases res with ⟨rel, anchor, rest⟩
        cases anchor with
        | var _ => rw [hlk] at h; cases h
        | ind a =>
          rw [hlk] at h; simp only [bind, Option.bind, pure] at h
          let isAnchor := fun b : SWRLAtom => b.iVars.isEmpty && (encodeAtomAt a b).isSome
          cases haM : (rest.filter isAnchor).mapM (encodeAtomAt a) with
          | none => rw [haM] at h; cases h
          | some anchorCEs =>
            rw [haM] at h; dsimp only at h
            cases hvM : (rest.filter fun b => !isAnchor b).mapM (encodeUnaryAtom v) with
            | none => rw [hvM] at h; cases h
            | some varCEs =>
              rw [hvM] at h; dsimp only at h
              cases hhM : r.head.mapM (encodeUnaryAtom v) with
              | none => rw [hhM] at h; cases h
              | some headCEs =>
                rw [hhM] at h; simp only [Option.some.injEq] at h; subst h
                obtain ⟨_, linkAtom, _, hLinkForm, _, hBodyCov⟩ := extractFirstIndLink_spec hlk
                obtain ⟨haFwd, _⟩ := mem_mapM_some haM
                obtain ⟨hvFwd, _⟩ := mem_mapM_some hvM
                obtain ⟨_, hhBwd⟩ := mem_mapM_some hhM
                intro ax hax
                obtain ⟨hce, hhceMem, rfl⟩ := List.mem_map.mp hax
                intro y hy x hrel
                rw [classHolds_intersect] at hy
                obtain ⟨a', ha'Mem, hyEq⟩ := hy (.oneOf [a]) (List.mem_cons_self ..)
                have ha'Eq : a' = a := List.mem_singleton.mp ha'Mem
                subst a'
                classical
                by_cases hvc : classHolds i x (ClassExpr.intersect (guard :: varCEs))
                · right
                  rw [classHolds_intersect] at hvc
                  obtain ⟨aName, haNameMem, hxEq⟩ := (hEx x).mp (hvc guard (List.mem_cons_self ..))
                  let σI : IRI → i.Object := fun _ => x
                  let σD : IRI → i.Data := fun _ => i.literalValue ⟨"0", xsd "integer"⟩
                  obtain ⟨aHead, haHeadMem, hEncH⟩ := hhBwd hce hhceMem
                  have hHeadHolds := hr σI σD
                    (fun w hw => by
                      rw [hvars] at hw
                      have := List.mem_singleton.mp hw; subst this
                      exact ⟨aName, haNameMem, hxEq⟩)
                    (fun b hb => by
                      rcases hBodyCov b hb with rfl | hbRest
                      · rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
                        · simp only [atomHolds, evalIArg]; exact hyEq ▸ hrel
                        · simp only [atomHolds, evalIArg]
                          exact (objectHolds_converse i rel0 (i.individuals a) x).mp (hyEq ▸ hrel)
                      · cases hia : isAnchor b with
                        | true =>
                          obtain ⟨ace, haceMem, hEncA⟩ := haFwd b (List.mem_filter.mpr ⟨hbRest, hia⟩)
                          exact (encodeAtomAt_holds_iff bSem i a σI σD hEncA).mp
                            (hyEq ▸ hy ace (List.mem_cons_of_mem _ haceMem))
                        | false =>
                          have hnot : (!isAnchor b) = true := by simp [hia]
                          obtain ⟨vce, hvceMem, hEncV⟩ := hvFwd b (List.mem_filter.mpr ⟨hbRest, hnot⟩)
                          exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncV).mp
                            (hvc vce (List.mem_cons_of_mem _ hvceMem)))
                    aHead haHeadMem
                  exact (encodeUnaryAtom_holds_iff bSem i v σI σD hEncH).mpr hHeadHolds
                · exact Or.inl hvc

/-- Roll up a body-only individual variable `iv` using an explicit domain guard `guard`. -/
def rollupOneIndVarWithGuard (guard : ClassExpr) (r : SWRLRule) (iv : IRI) : Option SWRLRule :=
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
        let filler := ClassExpr.intersect (guard :: ces)
        some { r with body := .classAtom (.objectSome rel filler) anchor :: others }

theorem rollupOneIndVarWithGuard_sound {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r r' : SWRLRule} {iv : IRI}
    (hCov : GuardCovers namedInds i guard)
    (h : rollupOneIndVarWithGuard guard r iv = some r')
    (hr' : satisfiesDLSafeRule bSem namedInds i r') :
    satisfiesDLSafeRule bSem namedInds i r := by
  unfold rollupOneIndVarWithGuard at h
  split at h
  · cases h
  · dsimp only at h
    let mentioning := r.body.filter (fun a => a.iVars.contains iv)
    let others := r.body.filter (fun a => !a.iVars.contains iv)
    cases hlk : extractFirstIndLink iv mentioning with
    | none => rw [hlk] at h; cases h
    | some res =>
      rcases res with ⟨rel, anchor, restMent⟩
      rw [hlk] at h; dsimp only at h
      cases hces : restMent.mapM (encodeUnaryAtom iv) with
      | none => rw [hces] at h; cases h
      | some ces =>
        rw [hces] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨_, linkAtom, hLinkMent, hLinkForm, hRestSub, _⟩ := extractFirstIndLink_spec hlk
        have hLinkBody : linkAtom ∈ r.body := (List.mem_filter.mp hLinkMent).1
        obtain ⟨_, hCeBwd⟩ := mem_mapM_some hces
        have hIVarsSub : ∀ v, v ∈ ({ body := SWRLAtom.classAtom (.objectSome rel (ClassExpr.intersect (guard :: ces))) anchor :: others, head := r.head } : SWRLRule).iVars → v ∈ r.iVars := by
          intro v hv
          simp only [SWRLRule.iVars, SWRLRule.bodyIVars, SWRLRule.headIVars,
            List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_cons] at hv ⊢
          rcases hv with ⟨a, rfl | haOth, hva⟩ | hhd
          · left; refine ⟨linkAtom, hLinkBody, ?_⟩
            rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
            · exact List.mem_eraseDups.mpr (List.mem_append_left _ hva)
            · exact List.mem_eraseDups.mpr (List.mem_append_right _ hva)
          · left; exact ⟨a, (List.mem_filter.mp haOth).1, hva⟩
          · right; exact hhd
        have hIvInR : iv ∈ r.iVars := by
          refine iVars_mem_of_body hLinkBody ?_
          rcases hLinkForm with rfl | ⟨rel0, rfl, rfl⟩
          · exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_singleton_self _))
          · exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_singleton_self _))
        intro σI σD hBound hbody a ha
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
              exact hσiv.symm ▸ hCov ind hindMem
            · obtain ⟨a0, ha0Rest, hEnc⟩ := hCeBwd c hc'
              have ha0Body : a0 ∈ r.body := (List.mem_filter.mp (hRestSub a0 ha0Rest)).1
              exact (encodeUnaryAtom_holds_iff bSem i iv σI σD hEnc).mpr (hbody a0 ha0Body)
        · exact hbody b (List.mem_filter.mp hbOth).1

theorem rollupOneIndVarWithGuard_complete {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr} {r r' : SWRLRule} {iv : IRI}
    (hEx : GuardExact namedInds i guard)
    (h : rollupOneIndVarWithGuard guard r iv = some r')
    (hr : satisfiesDLSafeRule bSem namedInds i r) :
    satisfiesDLSafeRule bSem namedInds i r' := by
  unfold rollupOneIndVarWithGuard at h
  split at h
  · cases h
  · rename_i hNotHead
    dsimp only at h
    let mentioning := r.body.filter (fun a => a.iVars.contains iv)
    let others := r.body.filter (fun a => !a.iVars.contains iv)
    cases hlk : extractFirstIndLink iv mentioning with
    | none => rw [hlk] at h; cases h
    | some res =>
      rcases res with ⟨rel, anchor, restMent⟩
      rw [hlk] at h; dsimp only at h
      cases hces : restMent.mapM (encodeUnaryAtom iv) with
      | none => rw [hces] at h; cases h
      | some ces =>
        rw [hces] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hAncNe, linkAtom, _, hLinkForm, _, hMentCov⟩ := extractFirstIndLink_spec hlk
        obtain ⟨hCeFwd, _⟩ := mem_mapM_some hces
        have hIVarsBack : ∀ v ∈ r.iVars, v = iv ∨ v ∈ ({ body := SWRLAtom.classAtom (.objectSome rel (ClassExpr.intersect (guard :: ces))) anchor :: others, head := r.head } : SWRLRule).iVars := by
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
                · left; refine ⟨_, Or.inl rfl, ?_⟩
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
        intro σI σD hBound' hbody' a ha
        have hExAtom := hbody' _ (List.mem_cons_self ..)
        simp only [atomHolds, classHolds] at hExAtom
        obtain ⟨y, hrel, hyFill⟩ := hExAtom
        rw [classHolds_intersect] at hyFill
        obtain ⟨aName, haNameMem, hind'Eq⟩ := (hEx y).mp (hyFill guard (List.mem_cons_self ..))
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
          · exact ⟨aName, haNameMem, hσI'iv.trans hind'Eq⟩
          · by_cases hviv : v = iv
            · subst hviv; exact ⟨aName, haNameMem, hσI'iv.trans hind'Eq⟩
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

def rollupLocalIndVarsWithGuard (guard : ClassExpr) (r : SWRLRule) : SWRLRule :=
  r.bodyIVars.foldl (fun cur iv => (rollupOneIndVarWithGuard guard cur iv).getD cur) r

theorem rollupLocalIndVarsWithGuard_sound {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr}
    (hCov : GuardCovers namedInds i guard) (r : SWRLRule)
    (hr' : satisfiesDLSafeRule bSem namedInds i (rollupLocalIndVarsWithGuard guard r)) :
    satisfiesDLSafeRule bSem namedInds i r := by
  unfold rollupLocalIndVarsWithGuard at hr'
  have hfold : ∀ (vars : List IRI) (cur : SWRLRule),
      satisfiesDLSafeRule bSem namedInds i
        (vars.foldl (fun c iv => (rollupOneIndVarWithGuard guard c iv).getD c) cur) →
      satisfiesDLSafeRule bSem namedInds i cur := by
    intro vars
    induction vars with
    | nil => intro cur h; exact h
    | cons v rest ih =>
      intro cur h
      rw [List.foldl_cons] at h
      have h1 := ih _ h
      cases hstep : rollupOneIndVarWithGuard guard cur v with
      | none => simpa [hstep] using h1
      | some next =>
        simp only [hstep, Option.getD_some] at h1
        exact rollupOneIndVarWithGuard_sound bSem hCov hstep h1
  exact hfold r.bodyIVars r hr'

theorem rollupLocalIndVarsWithGuard_complete {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr}
    (hEx : GuardExact namedInds i guard) (r : SWRLRule)
    (hr : satisfiesDLSafeRule bSem namedInds i r) :
    satisfiesDLSafeRule bSem namedInds i (rollupLocalIndVarsWithGuard guard r) := by
  unfold rollupLocalIndVarsWithGuard
  have hfold : ∀ (vars : List IRI) (cur : SWRLRule),
      satisfiesDLSafeRule bSem namedInds i cur →
      satisfiesDLSafeRule bSem namedInds i
        (vars.foldl (fun c iv => (rollupOneIndVarWithGuard guard c iv).getD c) cur) := by
    intro vars
    induction vars with
    | nil => intro cur h; exact h
    | cons v rest ih =>
      intro cur h
      rw [List.foldl_cons]
      apply ih
      cases hstep : rollupOneIndVarWithGuard guard cur v with
      | none => simpa [hstep] using h
      | some next =>
        simp only [hstep, Option.getD_some]
        exact rollupOneIndVarWithGuard_complete bSem hEx hstep h
  exact hfold r.bodyIVars r hr

/-- Guard-parameterized smart encoder preferring nominal-anchored unary axioms
    (`encodeAnchoredUnaryRuleWithGuard`, zero `owl:topObjectProperty`) before general
    unary and recursive partial grounding. -/
def encodeRuleSmartAuxWithGuard (namedInds : List IRI) (guard : ClassExpr) :
    Nat → SWRLRule → Option (List Axiom)
  | 0, r => groundRuleAll namedInds r
  | fuel + 1, r =>
    let r' := rollupLocalIndVarsWithGuard guard r
    match r'.iVars with
    | [] =>
      match encodeSingleIndGroundRule r' with
      | some axs => some axs
      | none => encodeGroundRule r'
    | [_] =>
      match encodeAnchoredUnaryRuleWithGuard guard r' with
      | some axs => some axs
      | none =>
        match encodeUnaryRuleWithGuard guard r' with
        | some axs => some axs
        | none => groundRuleAll namedInds r'
    | vs =>
      match vs.getLast? with
      | none => groundRuleAll namedInds r'
      | some v =>
        (namedInds.mapM fun a =>
          encodeRuleSmartAuxWithGuard namedInds guard fuel (r'.subst [(v, .named a)] [])).map List.flatten

theorem encodeRuleSmartAuxWithGuard_sound {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr}
    (hCov : GuardCovers namedInds i guard) :
    ∀ (fuel : Nat) {r : SWRLRule} {axs : List Axiom},
      encodeRuleSmartAuxWithGuard namedInds guard fuel r = some axs →
      satisfies i axs →
      satisfiesDLSafeRule bSem namedInds i r
  | 0, _, _, h, hsat => (groundRuleAll_holds_iff bSem h).mp hsat
  | fuel + 1, r, axs, h, hsat => by
    unfold encodeRuleSmartAuxWithGuard at h
    dsimp only at h
    let r' := rollupLocalIndVarsWithGuard guard r
    suffices satisfiesDLSafeRule bSem namedInds i r' from
      rollupLocalIndVarsWithGuard_sound bSem hCov r this
    cases hvars : r'.iVars with
    | nil =>
      rw [hvars] at h
      cases hs : encodeSingleIndGroundRule r' with
      | some sAxs =>
        rw [hs] at h; cases h
        intro σI σD _ hbody a ha
        exact (encodeSingleIndGroundRule_holds_iff bSem i σI σD hs).mp hsat hbody a ha
      | none =>
        rw [hs] at h
        intro σI σD _ hbody a ha
        exact (encodeGroundRule_holds_iff bSem i σI σD h).mp hsat hbody a ha
    | cons v1 tl =>
      cases tl with
      | nil =>
        rw [hvars] at h
        cases ha : encodeAnchoredUnaryRuleWithGuard guard r' with
        | some aAxs => rw [ha] at h; cases h; exact encodeAnchoredUnaryRuleWithGuard_sound bSem hCov ha hsat
        | none =>
          rw [ha] at h
          cases hu : encodeUnaryRuleWithGuard guard r' with
          | some uAxs => rw [hu] at h; cases h; exact encodeUnaryRuleWithGuard_sound bSem hCov hu hsat
          | none => rw [hu] at h; exact (groundRuleAll_holds_iff bSem h).mp hsat
      | cons v2 tl2 =>
        rw [hvars] at h; dsimp only at h
        cases hlast : (v1 :: v2 :: tl2).getLast? with
        | none => rw [hlast] at h; dsimp only at h; exact (groundRuleAll_holds_iff bSem h).mp hsat
        | some v =>
          rw [hlast] at h; dsimp only at h
          have hvMem : v ∈ r'.iVars := by rw [hvars]; exact getLast?_mem hlast
          cases hM : namedInds.mapM (fun a => encodeRuleSmartAuxWithGuard namedInds guard fuel (r'.subst [(v, .named a)] [])) with
          | none => rw [hM] at h; cases h
          | some axLists =>
            rw [hM] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            obtain ⟨hFwd, _⟩ := mem_mapM_some hM
            rw [← satisfiesDLSafeRule_subst_one_iff bSem hvMem]
            intro a ha
            obtain ⟨rAxs, hrAxsMem, hRec⟩ := hFwd a ha
            exact encodeRuleSmartAuxWithGuard_sound bSem hCov fuel hRec fun ax hax =>
              hsat ax (List.mem_flatten.mpr ⟨rAxs, hrAxsMem, hax⟩)

theorem encodeRuleSmartAuxWithGuard_complete {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {guard : ClassExpr}
    (hEx : GuardExact namedInds i guard) :
    ∀ (fuel : Nat) {r : SWRLRule} {axs : List Axiom},
      encodeRuleSmartAuxWithGuard namedInds guard fuel r = some axs →
      satisfiesDLSafeRule bSem namedInds i r →
      satisfies i axs
  | 0, _, _, h, hr => (groundRuleAll_holds_iff bSem h).mpr hr
  | fuel + 1, r, axs, h, hr => by
    unfold encodeRuleSmartAuxWithGuard at h
    dsimp only at h
    let r' := rollupLocalIndVarsWithGuard guard r
    have hr' : satisfiesDLSafeRule bSem namedInds i r' :=
      rollupLocalIndVarsWithGuard_complete bSem hEx r hr
    cases hvars : r'.iVars with
    | nil =>
      rw [hvars] at h
      obtain ⟨w0⟩ := i.objectNonempty
      let y0 : i.Data := i.literalValue ⟨"0", xsd "integer"⟩
      cases hs : encodeSingleIndGroundRule r' with
      | some sAxs =>
        rw [hs] at h; cases h
        exact (encodeSingleIndGroundRule_holds_iff bSem i (fun _ => w0) (fun _ => y0) hs).mpr
          (hr' (fun _ => w0) (fun _ => y0) (fun v hv => by rw [hvars] at hv; cases hv))
      | none =>
        rw [hs] at h
        exact (encodeGroundRule_holds_iff bSem i (fun _ => w0) (fun _ => y0) h).mpr
          (hr' (fun _ => w0) (fun _ => y0) (fun v hv => by rw [hvars] at hv; cases hv))
    | cons v1 tl =>
      cases tl with
      | nil =>
        rw [hvars] at h
        cases ha : encodeAnchoredUnaryRuleWithGuard guard r' with
        | some aAxs => rw [ha] at h; cases h; exact encodeAnchoredUnaryRuleWithGuard_complete bSem hEx ha hr'
        | none =>
          rw [ha] at h
          cases hu : encodeUnaryRuleWithGuard guard r' with
          | some uAxs => rw [hu] at h; cases h; exact encodeUnaryRuleWithGuard_complete bSem hEx hu hr'
          | none => rw [hu] at h; exact (groundRuleAll_holds_iff bSem h).mpr hr'
      | cons v2 tl2 =>
        rw [hvars] at h; dsimp only at h
        cases hlast : (v1 :: v2 :: tl2).getLast? with
        | none => rw [hlast] at h; dsimp only at h; exact (groundRuleAll_holds_iff bSem h).mpr hr'
        | some v =>
          rw [hlast] at h; dsimp only at h
          have hvMem : v ∈ r'.iVars := by rw [hvars]; exact getLast?_mem hlast
          cases hM : namedInds.mapM (fun a => encodeRuleSmartAuxWithGuard namedInds guard fuel (r'.subst [(v, .named a)] [])) with
          | none => rw [hM] at h; cases h
          | some axLists =>
            rw [hM] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            obtain ⟨_, hBwd⟩ := mem_mapM_some hM
            have hall := (satisfiesDLSafeRule_subst_one_iff bSem hvMem).mpr hr'
            intro ax hax
            obtain ⟨rAxs, hrAxsMem, haxIn⟩ := List.mem_flatten.mp hax
            obtain ⟨a, haMem, hRec⟩ := hBwd rAxs hrAxsMem
            exact encodeRuleSmartAuxWithGuard_complete bSem hEx fuel hRec (hall a haMem) ax haxIn

def encodeDLSafeRuleWithGuard (namedInds : List IRI) (guard : ClassExpr) (r : SWRLRule) :
    Option (List Axiom) :=
  encodeRuleSmartAuxWithGuard namedInds guard (r.iVars.length + 1) r

def groundAllRulesWithGuard (namedInds : List IRI) (guard : ClassExpr) (rules : List SWRLRule) :
    Option (List Axiom) :=
  (rules.mapM (encodeDLSafeRuleWithGuard namedInds guard)).map List.flatten

/-- ABox guard assertions `ClassAssertion(guardCls, a)` for each named individual `a ∈ namedInds`. -/
def dlSafeGuardAssertions (guardCls : IRI) (namedInds : List IRI) : List Axiom :=
  namedInds.map fun a => .classAssertion (.named guardCls) (.named a)

/-- Check whether class IRI `g` occurs anywhere inside a `ClassExpr`. -/
def classExprHasClass (g : IRI) : ClassExpr → Bool
  | .named c => c == g
  | .complement c => classExprHasClass g c
  | .intersection a b | .union a b => classExprHasClass g a || classExprHasClass g b
  | .oneOf _ => false
  | .objectSome _ c | .objectAll _ c
  | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c => classExprHasClass g c
  | .objectValue _ _ | .objectSelf _ => false
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _
  | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => false

def axiomHasClass (g : IRI) : Axiom → Bool
  | .subClassOf a b => classExprHasClass g a || classExprHasClass g b
  | .equivalentClasses cs | .disjointClasses cs => cs.any (classExprHasClass g)
  | .disjointUnion c cs => (c == g) || cs.any (classExprHasClass g)
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c =>
    classExprHasClass g c
  | .hasKey c _ _ | .classAssertion c _ => classExprHasClass g c
  | _ => false

def ontologyHasClass (g : IRI) (o : Ontology) : Bool :=
  o.any (axiomHasClass g)

def atomHasClass (g : IRI) : SWRLAtom → Bool
  | .classAtom c _ => classExprHasClass g c
  | _ => false

def ruleHasClass (g : IRI) (r : SWRLRule) : Bool :=
  r.body.any (atomHasClass g) || r.head.any (atomHasClass g)

def rulesHaveClass (g : IRI) (rules : List SWRLRule) : Bool :=
  rules.any (ruleHasClass g)

/-- Pick a fresh auxiliary class IRI not occurring in `o`, `rules`, or `extra`. -/
def freshGuardClass (o : Ontology) (rules : List SWRLRule) (extra : List IRI := []) : IRI :=
  let base := "urn:sabrina:swrl:O"
  let rec go : Nat → Nat → IRI
    | 0, k => s!"{base}_{k}"
    | fuel + 1, k =>
      let cand := if k == 0 then base else s!"{base}_{k}"
      if cand != thing && cand != nothing &&
          !ontologyHasClass cand o && !rulesHaveClass cand rules && !extra.contains cand then
        cand
      else go fuel (k + 1)
  go (o.length + rules.length + extra.length + 4) 0

private def withClassExt {dm : DatatypeMap} (i : Interpretation dm) (g : IRI)
    (hNeThing : g ≠ thing) (hNeNothing : g ≠ nothing) (ext : i.Object → Prop) : Interpretation dm :=
  { i with
    classes := fun c x => if c == g then ext x else i.classes c x
    thingExt := fun x => by simp [beq_false_of_ne hNeThing.symm, i.thingExt x]
    nothingExt := fun x => by simp [beq_false_of_ne hNeNothing.symm, i.nothingExt x] }

private theorem objectHolds_withClassExt {dm : DatatypeMap} (i : Interpretation dm)
    {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (r : ObjectProperty) (x y : i.Object) :
    objectHolds (withClassExt i g hT hN ext) r x y = objectHolds i r x y := by
  cases r <;> rfl

private theorem rolePath_withClassExt {dm : DatatypeMap} (i : Interpretation dm)
    {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop) :
    ∀ (rs : List ObjectProperty) (x y : i.Object),
      rolePath (withClassExt i g hT hN ext) rs x y ↔ rolePath i rs x y
  | [], _, _ => Iff.rfl
  | [r], x, y => by simp only [rolePath, objectHolds_withClassExt]; exact Iff.rfl
  | r :: r2 :: rs, x, y => by
    simp only [rolePath, objectHolds_withClassExt]
    exact exists_congr fun z => and_congr_right fun _ => rolePath_withClassExt i hT hN ext (r2 :: rs) z y

private theorem dataHolds_withClassExt {dm : DatatypeMap} (i : Interpretation dm)
    {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (dr : DataRange) :
    ∀ y, dataHolds (withClassExt i g hT hN ext) y dr ↔ dataHolds i y dr := by
  induction dr with
  | datatype _ => intro _; exact Iff.rfl
  | complement d ih => intro y; simp [dataHolds, ih y]
  | intersection a b iha ihb => intro y; simp [dataHolds, iha y, ihb y]
  | union a b iha ihb => intro y; simp [dataHolds, iha y, ihb y]
  | oneOf _ => intro _; exact Iff.rfl
  | restriction _ _ => intro _; exact Iff.rfl

private theorem classHolds_withClassExt_of_unused {dm : DatatypeMap} (i : Interpretation dm)
    {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (c : ClassExpr) (hUnused : classExprHasClass g c = false) :
    ∀ x, classHolds (withClassExt i g hT hN ext) x c ↔ classHolds i x c := by
  induction c with
  | named a =>
    intro x
    simp only [classExprHasClass, beq_eq_false_iff_ne] at hUnused
    simp [classHolds, withClassExt, beq_false_of_ne hUnused]
  | complement a ih =>
    intro x; simp only [classExprHasClass] at hUnused
    simp [classHolds, ih hUnused x]
  | intersection a b iha ihb =>
    intro x
    simp only [classExprHasClass, Bool.or_eq_false_iff] at hUnused
    simp [classHolds, iha hUnused.1 x, ihb hUnused.2 x]
  | union a b iha ihb =>
    intro x
    simp only [classExprHasClass, Bool.or_eq_false_iff] at hUnused
    simp [classHolds, iha hUnused.1 x, ihb hUnused.2 x]
  | oneOf _ => intro _; rfl
  | objectSome _ a ih | objectAll _ a ih =>
    intro x; simp only [classExprHasClass] at hUnused
    simp only [classHolds, withClassExt, objectHolds]
    constructor
    · intro h; first | (obtain ⟨y, hr, hy⟩ := h; exact ⟨y, hr, (ih hUnused y).mp hy⟩) | (intro y hr; exact (ih hUnused y).mp (h y hr))
    · intro h; first | (obtain ⟨y, hr, hy⟩ := h; exact ⟨y, hr, (ih hUnused y).mpr hy⟩) | (intro y hr; exact (ih hUnused y).mpr (h y hr))
  | objectMin _ r a ih | objectMax _ r a ih | objectExact _ r a ih =>
    intro x; simp only [classExprHasClass] at hUnused
    have hPred : (fun y => objectHolds (withClassExt i g hT hN ext) r x y ∧
        classHolds (withClassExt i g hT hN ext) y a) =
        (fun y => objectHolds i r x y ∧ classHolds i y a) := by
      funext y
      exact propext ⟨fun ⟨h1, h2⟩ => ⟨objectHolds_withClassExt i hT hN ext r x y ▸ h1, (ih hUnused y).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨(objectHolds_withClassExt i hT hN ext r x y).symm ▸ h1, (ih hUnused y).mpr h2⟩⟩
    simp only [classHolds, hPred]
    exact Iff.rfl
  | dataSome p dr | dataAll p dr =>
    intro x
    simp only [classHolds, withClassExt]
    first
    | exact exists_congr fun y => and_congr_right fun _ => dataHolds_withClassExt i hT hN ext dr y
    | exact forall_congr' fun y => imp_congr_right fun _ => dataHolds_withClassExt i hT hN ext dr y
  | dataMin _ p dr | dataMax _ p dr | dataExact _ p dr =>
    intro x
    have hPred : (fun y => (withClassExt i g hT hN ext).dataProperties p x y ∧
        dataHolds (withClassExt i g hT hN ext) y dr) =
        (fun y => i.dataProperties p x y ∧ dataHolds i y dr) := by
      funext y
      exact propext (and_congr_right fun _ => dataHolds_withClassExt i hT hN ext dr y)
    simp only [classHolds, hPred]
    exact Iff.rfl
  | objectValue _ _ | objectSelf _ | dataValue _ _ => intro _; rfl

private theorem axiomHolds_withClassExt_of_unused {dm : DatatypeMap} (i : Interpretation dm)
    {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (ax : Axiom) (hUnused : axiomHasClass g ax = false) :
    axiomHolds (withClassExt i g hT hN ext) ax ↔ axiomHolds i ax := by
  cases ax with
  | subClassOf a b =>
    simp only [axiomHasClass, Bool.or_eq_false_iff] at hUnused
    simp only [axiomHolds]
    constructor <;> intro h x hx
    · exact (classHolds_withClassExt_of_unused i hT hN ext b hUnused.2 x).mp
        (h x ((classHolds_withClassExt_of_unused i hT hN ext a hUnused.1 x).mpr hx))
    · exact (classHolds_withClassExt_of_unused i hT hN ext b hUnused.2 x).mpr
        (h x ((classHolds_withClassExt_of_unused i hT hN ext a hUnused.1 x).mp hx))
  | equivalentClasses cs =>
    simp only [axiomHasClass, List.any_eq_false] at hUnused
    simp only [axiomHolds]
    constructor <;> intro h c1 hc1 c2 hc2 x
    · have h1 := classHolds_withClassExt_of_unused i hT hN ext c1 (Bool.eq_false_iff.mpr (hUnused c1 hc1)) x
      have h2 := classHolds_withClassExt_of_unused i hT hN ext c2 (Bool.eq_false_iff.mpr (hUnused c2 hc2)) x
      exact h1.symm.trans ((h c1 hc1 c2 hc2 x).trans h2)
    · have h1 := classHolds_withClassExt_of_unused i hT hN ext c1 (Bool.eq_false_iff.mpr (hUnused c1 hc1)) x
      have h2 := classHolds_withClassExt_of_unused i hT hN ext c2 (Bool.eq_false_iff.mpr (hUnused c2 hc2)) x
      exact h1.trans ((h c1 hc1 c2 hc2 x).trans h2.symm)
  | disjointClasses cs =>
    simp only [axiomHasClass, List.any_eq_false] at hUnused
    simp only [axiomHolds]
    constructor <;> intro h
    · exact List.Pairwise.imp_of_mem (fun {p q} hp hq hpq x ⟨h1, h2⟩ => hpq x
        ⟨(classHolds_withClassExt_of_unused i hT hN ext p (Bool.eq_false_iff.mpr (hUnused p hp)) x).mpr h1,
         (classHolds_withClassExt_of_unused i hT hN ext q (Bool.eq_false_iff.mpr (hUnused q hq)) x).mpr h2⟩) h
    · exact List.Pairwise.imp_of_mem (fun {p q} hp hq hpq x ⟨h1, h2⟩ => hpq x
        ⟨(classHolds_withClassExt_of_unused i hT hN ext p (Bool.eq_false_iff.mpr (hUnused p hp)) x).mp h1,
         (classHolds_withClassExt_of_unused i hT hN ext q (Bool.eq_false_iff.mpr (hUnused q hq)) x).mp h2⟩) h
  | disjointUnion c cs =>
    simp only [axiomHasClass, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.any_eq_false] at hUnused
    simp only [axiomHolds, withClassExt, beq_false_of_ne hUnused.1]
    constructor <;> rintro ⟨hcov, hdisj⟩
    · refine ⟨fun x => ?_, List.Pairwise.imp_of_mem (fun {p q} hp hq hpq x ⟨h1, h2⟩ => hpq x
        ⟨(classHolds_withClassExt_of_unused i hT hN ext p (Bool.eq_false_iff.mpr (hUnused.2 p hp)) x).mpr h1,
         (classHolds_withClassExt_of_unused i hT hN ext q (Bool.eq_false_iff.mpr (hUnused.2 q hq)) x).mpr h2⟩) hdisj⟩
      constructor
      · intro hx; obtain ⟨d, hd, hdx⟩ := (hcov x).mp hx
        exact ⟨d, hd, (classHolds_withClassExt_of_unused i hT hN ext d (Bool.eq_false_iff.mpr (hUnused.2 d hd)) x).mp hdx⟩
      · rintro ⟨d, hd, hdx⟩
        exact (hcov x).mpr ⟨d, hd, (classHolds_withClassExt_of_unused i hT hN ext d (Bool.eq_false_iff.mpr (hUnused.2 d hd)) x).mpr hdx⟩
    · refine ⟨fun x => ?_, List.Pairwise.imp_of_mem (fun {p q} hp hq hpq x ⟨h1, h2⟩ => hpq x
        ⟨(classHolds_withClassExt_of_unused i hT hN ext p (Bool.eq_false_iff.mpr (hUnused.2 p hp)) x).mp h1,
         (classHolds_withClassExt_of_unused i hT hN ext q (Bool.eq_false_iff.mpr (hUnused.2 q hq)) x).mp h2⟩) hdisj⟩
      constructor
      · intro hx; obtain ⟨d, hd, hdx⟩ := (hcov x).mp hx
        exact ⟨d, hd, (classHolds_withClassExt_of_unused i hT hN ext d (Bool.eq_false_iff.mpr (hUnused.2 d hd)) x).mpr hdx⟩
      · rintro ⟨d, hd, hdx⟩
        exact (hcov x).mpr ⟨d, hd, (classHolds_withClassExt_of_unused i hT hN ext d (Bool.eq_false_iff.mpr (hUnused.2 d hd)) x).mp hdx⟩
  | objectPropertyDomain _ c | objectPropertyRange _ c | dataPropertyDomain _ c =>
    simp only [axiomHasClass] at hUnused
    simp only [axiomHolds, withClassExt, objectHolds]
    constructor <;> intro h x y hr
    · exact (classHolds_withClassExt_of_unused i hT hN ext c hUnused _).mp (h x y hr)
    · exact (classHolds_withClassExt_of_unused i hT hN ext c hUnused _).mpr (h x y hr)
  | hasKey c _ _ =>
    simp only [axiomHasClass] at hUnused
    simp only [axiomHolds, withClassExt, objectHolds]
    constructor <;> intro h x y hx hy hnx hny hobj hdata
    · exact h x y ((classHolds_withClassExt_of_unused i hT hN ext c hUnused x).mpr hx)
        ((classHolds_withClassExt_of_unused i hT hN ext c hUnused y).mpr hy) hnx hny hobj hdata
    · exact h x y ((classHolds_withClassExt_of_unused i hT hN ext c hUnused x).mp hx)
        ((classHolds_withClassExt_of_unused i hT hN ext c hUnused y).mp hy) hnx hny hobj hdata
  | classAssertion c a =>
    simp only [axiomHasClass] at hUnused
    exact classHolds_withClassExt_of_unused i hT hN ext c hUnused (i.individuals a)
  | subObjectPropertyChain body sup =>
    simp only [axiomHolds, objectHolds_withClassExt]
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr_left (rolePath_withClassExt i hT hN ext body x y)
  | dataPropertyRange p dr =>
    simp only [axiomHolds, withClassExt]
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr_right fun _ => dataHolds_withClassExt i hT hN ext dr y
  | datatypeDefinition dt dr =>
    simp only [axiomHolds, withClassExt]
    exact forall_congr' fun y => iff_congr Iff.rfl (dataHolds_withClassExt i hT hN ext dr y)
  | subObjectProperty _ _ | equivalentObjectProperties _
  | disjointObjectProperties _ | inverseObjectProperties _ _ | functionalObjectProperty _
  | inverseFunctionalObjectProperty _ | reflexiveObjectProperty _ | irreflexiveObjectProperty _
  | symmetricObjectProperty _ | asymmetricObjectProperty _ | transitiveObjectProperty _
  | subDataProperty _ _ | equivalentDataProperties _ | disjointDataProperties _
  | functionalDataProperty _
  | sameIndividuals _ | differentIndividuals _ | objectAssertion _ _ _
  | negativeObjectAssertion _ _ _ | dataAssertion _ _ _ | negativeDataAssertion _ _ _ =>
    exact Iff.rfl

private theorem atomHolds_withClassExt_of_unused {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) {g : IRI} (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (hBSem : ∀ b vs, bSem (withClassExt i g hT hN ext) b vs ↔ bSem i b vs)
    (σI : IRI → i.Object) (σD : IRI → i.Data)
    (a : SWRLAtom) (hUnused : atomHasClass g a = false) :
    atomHolds bSem (withClassExt i g hT hN ext) σI σD a ↔ atomHolds bSem i σI σD a := by
  cases a with
  | classAtom c x =>
    simp only [atomHasClass] at hUnused
    exact classHolds_withClassExt_of_unused i hT hN ext c hUnused (evalIArg i σI x)
  | dataRangeAtom dr x =>
    exact dataHolds_withClassExt i hT hN ext dr (evalDArg i σD x)
  | builtinAtom b args => exact hBSem b _
  | objectPropertyAtom _ _ _ | dataPropertyAtom _ _ _
  | sameIndividualAtom _ _ | differentIndividualsAtom _ _ => exact Iff.rfl

/-- Headline equisatisfiability theorem for Motik–Sattler–Studer auxiliary-guard DL-Safe SWRL
    reduction (eliminates `ObjectOneOf(namedInds)` copies and `owl:topObjectProperty`). -/
theorem groundAllRulesWithGuard_sat_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (hBSemExt : ∀ (i : Interpretation dm) (g : IRI) (hT : g ≠ thing) (hN : g ≠ nothing)
      (ext : i.Object → Prop) (b : IRI) (vs : List i.Data),
      bSem (withClassExt i g hT hN ext) b vs ↔ bSem i b vs)
    {namedInds : List IRI} {o : Ontology} {rules : List SWRLRule} {guardCls : IRI}
    {ruleAxs : List Axiom}
    (hT : guardCls ≠ thing) (hN : guardCls ≠ nothing)
    (hUnusedO : ontologyHasClass guardCls o = false)
    (hUnusedR : rulesHaveClass guardCls rules = false)
    (hG : groundAllRulesWithGuard namedInds (.named guardCls) rules = some ruleAxs) :
    Satisfiable dm (o ++ dlSafeGuardAssertions guardCls namedInds ++ ruleAxs) ↔
      SatisfiableWithRules dm bSem namedInds o rules := by
  unfold groundAllRulesWithGuard at hG
  cases hM : rules.mapM (encodeDLSafeRuleWithGuard namedInds (.named guardCls)) with
  | none => rw [hM] at hG; cases hG
  | some axLists =>
    rw [hM] at hG; simp only [Option.map_some, Option.some.injEq] at hG; subst hG
    obtain ⟨hFwd, hBwd⟩ := mem_mapM_some hM
    constructor
    · rintro ⟨i, assign, hsat⟩
      let j := i.withAnonymous assign
      have hCov : GuardCovers namedInds j (.named guardCls) := fun a ha =>
        hsat (.classAssertion (.named guardCls) (.named a))
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
      refine ⟨i, assign, fun ax hax => hsat ax (List.mem_append_left _ (List.mem_append_left _ hax)), fun r hr => ?_⟩
      obtain ⟨rAxs, hrAxsMem, hEnc⟩ := hFwd r hr
      exact encodeRuleSmartAuxWithGuard_sound bSem hCov (r.iVars.length + 1) hEnc fun ax hax =>
        hsat ax (List.mem_append_right _ (List.mem_flatten.mpr ⟨rAxs, hrAxsMem, hax⟩))
    · rintro ⟨i, assign, hsatO, hsatR⟩
      let ext : i.Object → Prop := fun x => ∃ a ∈ namedInds, x = i.individuals (.named a)
      let i' := withClassExt i guardCls hT hN ext
      have hEx : GuardExact namedInds (i'.withAnonymous assign) (.named guardCls) := by
        intro x
        simp [classHolds, Interpretation.withAnonymous, withClassExt, ext, i']
      refine ⟨i', assign, fun ax hax => ?_⟩
      rcases List.mem_append.mp hax with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · have hUnAx : axiomHasClass guardCls ax = false := by
            simp only [ontologyHasClass, List.any_eq_false] at hUnusedO
            exact Bool.eq_false_iff.mpr (hUnusedO ax h1)
          exact (axiomHolds_withClassExt_of_unused (i.withAnonymous assign) hT hN ext ax hUnAx).mpr (hsatO ax h1)
        · obtain ⟨a, haMem, rfl⟩ := List.mem_map.mp h2
          exact hEx.covers a haMem
      · obtain ⟨rAxs, hrAxsMem, haxIn⟩ := List.mem_flatten.mp h3
        obtain ⟨r, hrMem, hEnc⟩ := hBwd rAxs hrAxsMem
        have hUnR : ruleHasClass guardCls r = false := by
          simp only [rulesHaveClass, List.any_eq_false] at hUnusedR
          exact Bool.eq_false_iff.mpr (hUnusedR r hrMem)
        simp only [ruleHasClass, Bool.or_eq_false_iff, List.any_eq_false] at hUnR
        have hsatR' : satisfiesDLSafeRule bSem namedInds (i'.withAnonymous assign) r := by
          intro σI σD hBound hbody a ha
          have hUnA : atomHasClass guardCls a = false := Bool.eq_false_iff.mpr (hUnR.2 a ha)
          refine (atomHolds_withClassExt_of_unused bSem (i.withAnonymous assign) hT hN ext
            (hBSemExt (i.withAnonymous assign) guardCls hT hN ext) σI σD a hUnA).mpr ?_
          exact hsatR r hrMem σI σD hBound (fun b hb =>
            have hUnB : atomHasClass guardCls b = false := Bool.eq_false_iff.mpr (hUnR.1 b hb)
            (atomHolds_withClassExt_of_unused bSem (i.withAnonymous assign) hT hN ext
              (hBSemExt (i.withAnonymous assign) guardCls hT hN ext) σI σD b hUnB).mp (hbody b hb)) a ha
        exact encodeRuleSmartAuxWithGuard_complete bSem hEx (r.iVars.length + 1) hEnc hsatR' ax haxIn

/-- Headline entailment-preservation theorem for Motik–Sattler–Studer auxiliary-guard DL-Safe SWRL
    reduction for any query `q` not mentioning `guardCls`. -/
theorem groundAllRulesWithGuard_entails_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (hBSemExt : ∀ (i : Interpretation dm) (g : IRI) (hT : g ≠ thing) (hN : g ≠ nothing)
      (ext : i.Object → Prop) (b : IRI) (vs : List i.Data),
      bSem (withClassExt i g hT hN ext) b vs ↔ bSem i b vs)
    {namedInds : List IRI} {o q : Ontology} {rules : List SWRLRule} {guardCls : IRI}
    {ruleAxs : List Axiom}
    (hT : guardCls ≠ thing) (hN : guardCls ≠ nothing)
    (hUnusedO : ontologyHasClass guardCls o = false)
    (hUnusedR : rulesHaveClass guardCls rules = false)
    (hUnusedQ : ontologyHasClass guardCls q = false)
    (hG : groundAllRulesWithGuard namedInds (.named guardCls) rules = some ruleAxs) :
    Entails dm (o ++ dlSafeGuardAssertions guardCls namedInds ++ ruleAxs) q ↔
      EntailsWithRules dm bSem namedInds o rules q := by
  unfold groundAllRulesWithGuard at hG
  cases hM : rules.mapM (encodeDLSafeRuleWithGuard namedInds (.named guardCls)) with
  | none => rw [hM] at hG; cases hG
  | some axLists =>
    rw [hM] at hG; simp only [Option.map_some, Option.some.injEq] at hG; subst hG
    obtain ⟨hFwd, hBwd⟩ := mem_mapM_some hM
    constructor
    · intro hent i ⟨assign, hsatO, hsatR⟩
      let ext : i.Object → Prop := fun x => ∃ a ∈ namedInds, x = i.individuals (.named a)
      let i' := withClassExt i guardCls hT hN ext
      have hEx : GuardExact namedInds (i'.withAnonymous assign) (.named guardCls) := by
        intro x
        simp [classHolds, Interpretation.withAnonymous, withClassExt, ext, i']
      have hMod' : models i' (o ++ dlSafeGuardAssertions guardCls namedInds ++ axLists.flatten) := by
        refine ⟨assign, fun ax hax => ?_⟩
        rcases List.mem_append.mp hax with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · have hUnAx : axiomHasClass guardCls ax = false := by
              simp only [ontologyHasClass, List.any_eq_false] at hUnusedO
              exact Bool.eq_false_iff.mpr (hUnusedO ax h1)
            exact (axiomHolds_withClassExt_of_unused (i.withAnonymous assign) hT hN ext ax hUnAx).mpr (hsatO ax h1)
          · obtain ⟨a, haMem, rfl⟩ := List.mem_map.mp h2
            exact hEx.covers a haMem
        · obtain ⟨rAxs, hrAxsMem, haxIn⟩ := List.mem_flatten.mp h3
          obtain ⟨r, hrMem, hEnc⟩ := hBwd rAxs hrAxsMem
          have hUnR : ruleHasClass guardCls r = false := by
            simp only [rulesHaveClass, List.any_eq_false] at hUnusedR
            exact Bool.eq_false_iff.mpr (hUnusedR r hrMem)
          simp only [ruleHasClass, Bool.or_eq_false_iff, List.any_eq_false] at hUnR
          have hsatR' : satisfiesDLSafeRule bSem namedInds (i'.withAnonymous assign) r := by
            intro σI σD hBound hbody a ha
            have hUnA : atomHasClass guardCls a = false := Bool.eq_false_iff.mpr (hUnR.2 a ha)
            refine (atomHolds_withClassExt_of_unused bSem (i.withAnonymous assign) hT hN ext
              (hBSemExt (i.withAnonymous assign) guardCls hT hN ext) σI σD a hUnA).mpr ?_
            exact hsatR r hrMem σI σD hBound (fun b hb =>
              have hUnB : atomHasClass guardCls b = false := Bool.eq_false_iff.mpr (hUnR.1 b hb)
              (atomHolds_withClassExt_of_unused bSem (i.withAnonymous assign) hT hN ext
                (hBSemExt (i.withAnonymous assign) guardCls hT hN ext) σI σD b hUnB).mp (hbody b hb)) a ha
          exact encodeRuleSmartAuxWithGuard_complete bSem hEx (r.iVars.length + 1) hEnc hsatR' ax haxIn
      obtain ⟨assignQ, hsatQ'⟩ := hent i' hMod'
      refine ⟨assignQ, fun ax hax => ?_⟩
      have hUnQ : axiomHasClass guardCls ax = false := by
        simp only [ontologyHasClass, List.any_eq_false] at hUnusedQ
        exact Bool.eq_false_iff.mpr (hUnusedQ ax hax)
      exact (axiomHolds_withClassExt_of_unused (i.withAnonymous assignQ) hT hN ext ax hUnQ).mp (hsatQ' ax hax)
    · intro hent i ⟨assign, hsat⟩
      let j := i.withAnonymous assign
      have hCov : GuardCovers namedInds j (.named guardCls) := fun a ha =>
        hsat (.classAssertion (.named guardCls) (.named a))
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
      refine hent i ⟨assign, fun ax hax => hsat ax (List.mem_append_left _ (List.mem_append_left _ hax)), fun r hr => ?_⟩
      obtain ⟨rAxs, hrAxsMem, hEnc⟩ := hFwd r hr
      exact encodeRuleSmartAuxWithGuard_sound bSem hCov (r.iVars.length + 1) hEnc fun ax hax =>
        hsat ax (List.mem_append_right _ (List.mem_flatten.mpr ⟨rAxs, hrAxsMem, hax⟩))

private theorem realBuiltinSem_withClassExt (i : Interpretation realDatatypeMap)
    (g : IRI) (hT : g ≠ thing) (hN : g ≠ nothing) (ext : i.Object → Prop)
    (b : IRI) (vs : List i.Data) :
    realBuiltinSem (withClassExt i g hT hN ext) b vs ↔ realBuiltinSem i b vs :=
  realBuiltinSem_classes_irrel i _ _ _ b vs

/-- Real-map specialization of `groundAllRulesWithGuard_sat_iff`. -/
theorem groundAllRulesWithGuard_real_sat_iff
    {namedInds : List IRI} {o : Ontology} {rules : List SWRLRule} {guardCls : IRI}
    {ruleAxs : List Axiom}
    (hT : guardCls ≠ thing) (hN : guardCls ≠ nothing)
    (hUnusedO : ontologyHasClass guardCls o = false)
    (hUnusedR : rulesHaveClass guardCls rules = false)
    (hG : groundAllRulesWithGuard namedInds (.named guardCls) rules = some ruleAxs) :
    Satisfiable realDatatypeMap (o ++ dlSafeGuardAssertions guardCls namedInds ++ ruleAxs) ↔
      SatisfiableWithRules realDatatypeMap realBuiltinSem namedInds o rules :=
  groundAllRulesWithGuard_sat_iff realBuiltinSem realBuiltinSem_withClassExt hT hN hUnusedO hUnusedR hG

/-- Real-map specialization of `groundAllRulesWithGuard_entails_iff`. -/
theorem groundAllRulesWithGuard_real_entails_iff
    {namedInds : List IRI} {o q : Ontology} {rules : List SWRLRule} {guardCls : IRI}
    {ruleAxs : List Axiom}
    (hT : guardCls ≠ thing) (hN : guardCls ≠ nothing)
    (hUnusedO : ontologyHasClass guardCls o = false)
    (hUnusedR : rulesHaveClass guardCls rules = false)
    (hUnusedQ : ontologyHasClass guardCls q = false)
    (hG : groundAllRulesWithGuard namedInds (.named guardCls) rules = some ruleAxs) :
    Entails realDatatypeMap (o ++ dlSafeGuardAssertions guardCls namedInds ++ ruleAxs) q ↔
      EntailsWithRules realDatatypeMap realBuiltinSem namedInds o rules q :=
  groundAllRulesWithGuard_entails_iff realBuiltinSem realBuiltinSem_withClassExt hT hN hUnusedO hUnusedR hUnusedQ hG

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

/-- Real-map specialization of the local roll-up theorem. -/
theorem rollupOneDataVar_real_holds_iff {namedInds : List IRI} {i : Interpretation realDatatypeMap}
    {r r' : SWRLRule} {dv : IRI} (h : rollupOneDataVar r dv = some r') :
    satisfiesDLSafeRule realBuiltinSem namedInds i r' ↔
      satisfiesDLSafeRule realBuiltinSem namedInds i r :=
  rollupOneDataVar_holds_iff realBuiltinSem
    (fun σI σD _ _ _ _ hr => builtinToDataRange_real_iff i σI σD hr) h

theorem rollupLocalDataVars_real_holds_iff (namedInds : List IRI)
    (i : Interpretation realDatatypeMap) (r : SWRLRule) :
    satisfiesDLSafeRule realBuiltinSem namedInds i (rollupLocalDataVars r) ↔
      satisfiesDLSafeRule realBuiltinSem namedInds i r := by
  unfold rollupLocalDataVars
  generalize r.bodyDVars = variables
  induction variables generalizing r with
  | nil => rfl
  | cons v rest ih =>
    rw [List.foldl_cons, ih]
    cases h : rollupOneDataVar r v with
    | none => rfl
    | some _ => exact rollupOneDataVar_real_holds_iff h

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

private def evalDArgWithEnv (envD : List (IRI × Literal)) : DArg → Option BuiltinValue
  | .lit l => decodeBuiltinLiteral? l
  | .var v => (envD.lookup v).bind decodeBuiltinLiteral?

/-- Propagate functional `swrlb:*` built-ins and check ground predicate built-ins
    under a partial data-variable binding `envD`.
    Returns `some (envD', remainingBody)` if consistent, or `none` if a built-in is refuted. -/
private def propagateBuiltinsAux :
    Nat → List (IRI × Literal) → List SWRLAtom →
      Except String (Option (List (IRI × Literal) × List SWRLAtom))
  | 0, envD, body => .ok (some (envD, body))
  | fuel + 1, envD, body => do
    let mut curEnv := envD
    let mut changed := false
    let mut kept : List SWRLAtom := []
    for a in body do
      match a with
      | .builtinAtom b args =>
        if !isSupportedConcreteBuiltin b then
          kept := a :: kept
        else
          match args.mapM (evalDArgWithEnv curEnv) with
          | some vals =>
            -- All arguments are bound: evaluate the built-in predicate directly
            if requireConcreteBuiltinOutput b && (evalConcreteBuiltinOutput? b vals.tail).isNone then
              throw s!"SWRL built-in '{b}' is outside the supported exact concrete-value fragment"
            if evalConcreteBuiltinRel b vals then
              changed := true
            else
              return none
          | none =>
            -- Check if functional built-in with unbound output `args[0]` and all inputs bound
            match args with
            | .var outVar :: inArgs =>
              if isConcreteFunctionalBuiltin b && (curEnv.lookup outVar).isNone then
                match inArgs.mapM (evalDArgWithEnv curEnv) with
                | some inVals =>
                  match evalConcreteBuiltinOutput? b inVals with
                  | some outVal =>
                    match builtinValueToLiteral? outVal with
                    | some outLit =>
                      if decodeBuiltinLiteral? outLit == some outVal then
                        curEnv := (outVar, outLit) :: curEnv
                        changed := true
                      else
                        kept := a :: kept
                    | none => kept := a :: kept
                  | none =>
                    if requireConcreteBuiltinOutput b then
                      throw s!"SWRL built-in '{b}' is outside the supported exact concrete-value fragment"
                    return none
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

/-- Literal candidates are tracked by property. Ground rule bodies still test
    each concrete assertion, so an alias or a potential rule head only adds
    candidates and never asserts a new fact on its own. -/
private abbrev DataCandidates := List (IRI × Literal)

private def dataCandidateSeed (o : Ontology) : DataCandidates :=
  o.flatMap fun a =>
    (Profile.axiomSig a).data.flatMap fun p => (axiomLiterals a).map (p, ·)

private def dataPropertyClosure (o : Ontology) : List (IRI × IRI) :=
  Sabrina.ALCH.closeIndexed (o.flatMap fun
    | .subDataProperty p q => [(p, q)]
    | .equivalentDataProperties ps => ps.flatMap fun p => ps.map (p, ·)
    | _ => [])

private def sourceProperties (r : SWRLRule) (dv : IRI) : List IRI :=
  (r.body.filterMap fun
    | .dataPropertyAtom p _ (.var v) =>
      if v == dv && p != topDataProperty then some p else none
    | _ => none).eraseDups

private def headDataCandidates (r : SWRLRule) : DataCandidates :=
  r.head.filterMap fun
    | .dataPropertyAtom p _ (.lit l) => some (p, l)
    | _ => none

private def expandDataCandidates (sub : List (IRI × IRI)) (facts : DataCandidates) :
    DataCandidates :=
  (facts.flatMap fun (p, l) => (p, l) ::
    (sub.filterMap fun (q, r) => if q == p then some (r, l) else none)).eraseDups

/-- Ground only body-variable bindings with a finite concrete data-property
    source. The source signatures are tested before enumerating individuals. -/
private def groundConcreteRule (facts : DataCandidates) (namedInds : List IRI)
    (r : SWRLRule) : Except String (List Axiom × DataCandidates) := do
  for a in r.body do
    if let .builtinAtom b _ := a then
      if !isSupportedConcreteBuiltin b then throw s!"unsupported SWRL built-in '{b}'"
  let mut envsD : List (List (IRI × Literal)) := [[]]
  for dv in r.bodyNonBuiltinDVars do
    let p :: ps := sourceProperties r dv | throw s!"SWRL data variable '{dv}' needs a finite concrete data-property source"
    let lits := (facts.filterMap fun (q, l) =>
      if p == q && ps.all (fun prop => facts.any fun (target, other) =>
        prop == target && decodeLiteral l == decodeLiteral other) then some l else none).eraseDups
    if lits.isEmpty then return ([], [])
    envsD := lits.flatMap fun l => envsD.map fun env => (dv, l) :: env
  let mut outAxs := []
  let mut outFacts := []
  for envI in allVarAssignments namedInds r.iVars do
    let rI := r.subst (envI.map fun (v, x) => (v, Individual.named x)) []
    for envD in envsD do
      match ← propagateBuiltinsAux (rI.body.length + 2) envD rI.body with
      | none => pure ()
      | some (env, remBody) =>
        let gr : SWRLRule := ⟨remBody.map (SWRLAtom.subst [] env), rI.head.map (SWRLAtom.subst [] env)⟩
        if !gr.dVars.isEmpty || gr.hasBuiltins then
          throw "SWRL rule contains data variables or functional built-ins not bound by concrete data values"
        if (gr.body ++ gr.head).any (fun
          | .dataPropertyAtom _ _ (.lit l) => (decodeLiteral l).isNone
          | _ => false) then
          throw "SWRL data property uses a value outside the supported OWL 2 datatype map"
        match encodeSingleIndGroundRule gr <|> encodeGroundRule gr with
        | some axs =>
          outAxs := outAxs ++ axs
          outFacts := outFacts ++ headDataCandidates gr
        | none => throw "failed to encode grounded SWRL rule into OWL 2 DL"
  return (outAxs.eraseDups, outFacts.eraseDups)

def groundRuleWithDataBuiltins (o : Ontology) (namedInds : List IRI) (r : SWRLRule) :
    Except String (List Axiom) := do
  let facts := expandDataCandidates (dataPropertyClosure o) (dataCandidateSeed o)
  return (← groundConcreteRule facts namedInds r).1

private def needsConcreteGrounding (r : SWRLRule) : Bool := r.hasDVars || r.hasBuiltins

private def groundConcreteRules (o : Ontology) (namedInds : List IRI)
    (rules : List (SWRLRule × SWRLRule)) (seedHeads : DataCandidates) :
    Except String (List (Axiom × SWRLRule)) := do
  if rules.isEmpty then return []
  let sub := dataPropertyClosure o
  let inputs := rules.map fun (original, r) =>
    (original, r, (r.bodyNonBuiltinDVars.flatMap (sourceProperties r)).eraseDups)
  let needed := (inputs.flatMap fun (_, _, props) => props).eraseDups
  let keep := fun (p, _) => needed.contains p
  let mut facts := (expandDataCandidates sub (dataCandidateSeed o ++ seedHeads)).filter keep
  let mut pending := inputs
  let mut lowered := []
  -- Reject an unbounded or excessively long value-generating chain explicitly.
  for _ in [:rules.length + 64] do
    let mut newFacts := []
    for (original, r, _) in pending do
      let (axs, outputs) ← groundConcreteRule facts namedInds r
      lowered := lowered ++ axs.map (·, original)
      newFacts := newFacts ++ outputs
    let delta := (expandDataCandidates sub newFacts).filter fun fact =>
      keep fact && !facts.contains fact
    if delta.isEmpty then return lowered.eraseDups
    facts := facts ++ delta
    let changed := (delta.map Prod.fst).eraseDups
    pending := inputs.filter fun (_, _, props) => props.any changed.contains
  throw "SWRL concrete-value grounding did not reach a finite fixpoint within the configured round bound"

/-- Lower the rule set together so functional outputs can become candidate
    inputs of later rules. Uses Motik–Sattler–Studer auxiliary-guard encoding
    (`groundAllRulesWithGuard`) when `namedInds.length > 8` to avoid repeated
    `ObjectOneOf(namedInds)` AST blowups and `owl:topObjectProperty`.
    Returns `(guardCls?, guardAssertions, loweredRuleProvenance)`. -/
def lowerSWRLRulesGuardedWithProvenance (o : Ontology) (namedInds : List IRI)
    (rules : List SWRLRule) (extraForbidden : List IRI := []) :
    Except String (Option IRI × List Axiom × List (Axiom × SWRLRule)) := do
  if let some err := diagnoseDLSafeRules rules then throw err
  let rolled := rules.map fun r => (r, rollupLocalDataVars r)
  let (concrete, static) := rolled.partition (fun (_, r) => needsConcreteGrounding r)
  let useAuxGuard := namedInds.length > 8 && static.any (fun (_, r) => !r.iVars.isEmpty)
  let guardCls? : Option IRI :=
    if useAuxGuard then some (freshGuardClass o rules extraForbidden) else none
  let guardExpr : ClassExpr :=
    match guardCls? with
    | some g => .named g
    | none => .oneOf (namedInds.map Individual.named)
  let guardAxs : List Axiom :=
    match guardCls? with
    | some g => dlSafeGuardAssertions g namedInds
    | none => []
  let staticAxs ← static.flatMapM fun (original, r) => do
    let some axs := encodeDLSafeRuleWithGuard namedInds guardExpr r
      | throw "failed to encode DL-safe SWRL rule into OWL 2 DL"
    return axs.map (·, original)
  let more ← groundConcreteRules o namedInds concrete (static.flatMap fun (_, r) => headDataCandidates r)
  return (guardCls?, guardAxs, staticAxs ++ more)

/-- Lower the rule set together so functional outputs can become candidate
    inputs of later rules. Retain the source rule for explanation rendering. -/
def lowerSWRLRulesWithProvenance (o : Ontology) (namedInds : List IRI)
    (rules : List SWRLRule) : Except String (List (Axiom × SWRLRule)) := do
  if let some err := diagnoseDLSafeRules rules then throw err
  let rolled := rules.map fun r => (r, rollupLocalDataVars r)
  let (concrete, static) := rolled.partition (fun (_, r) => needsConcreteGrounding r)
  let guardExpr := ClassExpr.oneOf (namedInds.map Individual.named)
  let staticAxs ← static.flatMapM fun (original, r) => do
    let some axs := encodeDLSafeRuleWithGuard namedInds guardExpr r
      | throw "failed to encode DL-safe SWRL rule into OWL 2 DL"
    return axs.map (·, original)
  let more ← groundConcreteRules o namedInds concrete (static.flatMap fun (_, r) => headDataCandidates r)
  return staticAxs ++ more

def lowerSWRLRules (o : Ontology) (namedInds : List IRI) (rules : List SWRLRule) :
    Except String (List Axiom) :=
  (lowerSWRLRulesWithProvenance o namedInds rules).map (List.map Prod.fst)

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

/-- Narrow candidate individuals for variable `v` using unary `ClassAtom` and
    `ObjectPropertyAtom` edge incidence in `m`, avoiding $O(|I|^k)$ Cartesian enumeration. -/
private def candidateIndsForVar (m : SROIQDModel) (namedInds : List IRI)
    (body : List SWRLAtom) (v : IRI) : List IRI :=
  let hasOut (p : IRI) (w : m.graph.World) : Bool :=
    p == topObjectProperty || (p != bottomObjectProperty &&
      m.graph.edges.any fun (ep, src, _) => ep == p && src == w)
  let hasIn (p : IRI) (w : m.graph.World) : Bool :=
    p == topObjectProperty || (p != bottomObjectProperty &&
      m.graph.edges.any fun (ep, _, dst) => ep == p && dst == w)
  namedInds.filter fun a =>
    let w := m.indVal (.named a)
    body.all fun atom =>
      match atom with
      | .classAtom c (.var u) =>
        if u == v then evalClassExprInModel m w c != some false else true
      | .objectPropertyAtom (.named p) (.var u1) (.var u2) =>
        (if u1 == v then hasOut p w else true) && (if u2 == v then hasIn p w else true)
      | .objectPropertyAtom (.inverse p) (.var u1) (.var u2) =>
        (if u1 == v then hasIn p w else true) && (if u2 == v then hasOut p w else true)
      | .objectPropertyAtom (.named p) (.var u) (.ind b) =>
        if u == v then
          p == topObjectProperty || (p != bottomObjectProperty && m.graph.edge p w (m.indVal b))
        else true
      | .objectPropertyAtom (.named p) (.ind b) (.var u) =>
        if u == v then
          p == topObjectProperty || (p != bottomObjectProperty && m.graph.edge p (m.indVal b) w)
        else true
      | .objectPropertyAtom (.inverse p) (.var u) (.ind b) =>
        if u == v then
          p == topObjectProperty || (p != bottomObjectProperty && m.graph.edge p (m.indVal b) w)
        else true
      | .objectPropertyAtom (.inverse p) (.ind b) (.var u) =>
        if u == v then
          p == topObjectProperty || (p != bottomObjectProperty && m.graph.edge p w (m.indVal b))
        else true
      | _ => true

private def filteredVarAssignments (m : SROIQDModel) (namedInds : List IRI)
    (body : List SWRLAtom) : List IRI → List (List (IRI × IRI))
  | [] => [[]]
  | v :: vs =>
    let cands := candidateIndsForVar m namedInds body v
    if cands.isEmpty then []
    else
      let rest := filteredVarAssignments m namedInds body vs
      cands.flatMap fun a => rest.map fun env => (v, a) :: env

/-- Find violated ground instances of multi-variable SWRL rules in a verified finite model `m`
    (batched up to `maxBatch` per CEGAR round).
    Returns `some []` if all groundings are verified satisfied in `m`,
    `some grs` (non-empty) if violated ground instances are found, or `none` if uncertain. -/
private def findViolatedGroundRules (m : SROIQDModel) (namedInds : List IRI)
    (rules : List SWRLRule) (maxBatch : Nat := 64) : Option (List SWRLRule) := Id.run do
  let mut violated : List SWRLRule := []
  for r in rules do
    let envs := filteredVarAssignments m namedInds r.body r.iVars
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
        | some false =>
          violated := gr :: violated
          if violated.length ≥ maxBatch then return some violated.reverse
          break
        | none => return none
  return some violated.reverse

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
  let rolled := rules.map fun r => (r, rollupLocalDataVars r)
  let (concrete, static) := rolled.partition (fun (_, r) => needsConcreteGrounding r)
  let grounded ← groundConcreteRules o namedInds concrete (static.flatMap fun (_, r) => headDataCandidates r)
  let mut staticAxs := grounded.map Prod.fst
  let mut lazyRules : List SWRLRule := []
  for (_, r) in static do
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
              match findViolatedGroundRules m namedInds lazyRules with
              | some [] => return some true -- Verified model satisfies all SWRL rules!
              | some grs =>
                let mut addedAny := false
                for gr in grs do
                  match encodeGroundRuleSmart gr with
                  | some gAxs =>
                    activeAxs := activeAxs ++ gAxs
                    addedAny := true
                  | none => pure ()
                if !addedAny then break
              | none => break
            | .refutation _ => return some false
        else break
      | none => break
    | none => break
  -- Fallback: guarded nominal-anchored exact encoding + fast/exact decision
  -- (guarantees completeness & termination without `ObjectOneOf(namedInds)` blowup)
  let useAuxGuard := namedInds.length > 8
  let guardCls? := if useAuxGuard then some (freshGuardClass baseOnt lazyRules) else none
  let guardExpr : ClassExpr := match guardCls? with
    | some g => .named g
    | none => .oneOf (namedInds.map Individual.named)
  let mut fullAxs : List Axiom := match guardCls? with
    | some g => dlSafeGuardAssertions g namedInds
    | none => []
  for r in lazyRules do
    match encodeDLSafeRuleWithGuard namedInds guardExpr r with
    | some axs => fullAxs := fullAxs ++ axs
    | none => throw "failed to encode DL-safe SWRL rule"
  return Classification.fastConsistencyCheck (baseOnt ++ fullAxs)

#print axioms encodeGroundAtom_holds_iff
#print axioms encodeGroundRule_holds_iff
#print axioms encodeSingleIndGroundRule_holds_iff
#print axioms encodeUnaryRule_holds_iff
#print axioms encodeAnchoredUnaryRuleWithGuard_sound
#print axioms encodeAnchoredUnaryRuleWithGuard_complete
#print axioms rollupOneIndVar_holds_iff
#print axioms rollupLocalIndVars_holds_iff
#print axioms groundRuleAll_holds_iff
#print axioms encodeDLSafeRule_holds_iff
#print axioms groundAllRules_holds_iff
#print axioms groundAllRules_sat_iff
#print axioms groundAllRules_entails_iff
#print axioms groundAllRulesWithGuard_real_sat_iff
#print axioms groundAllRulesWithGuard_real_entails_iff
#print axioms rollupOneDataVar_holds_iff
#print axioms rollupLocalDataVars_real_holds_iff
#print axioms decideRealWithSWRL_iff

end Sabrina.OWL2.SWRL
