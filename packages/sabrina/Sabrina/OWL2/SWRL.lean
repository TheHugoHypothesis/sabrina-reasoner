import Sabrina.OWL2.DirectSemantics
import Sabrina.OWL2.Datatypes
import Sabrina.OWL2.Datatypes.RealDatatype

/-!
Core syntax, OWL 2 Direct Semantics (Motik–Sattler–Studer DL-safe semantics),
substitution lemmas, signature extraction, and DL-safety validation for SWRL rules.

Keeping SWRL in an orthogonal module (rather than extending `Sabrina.OWL2.Axiom`)
preserves full backward compatibility with downstream packages while enabling exact,
kernel-verified reductions to `Sabrina.OWL2.Ontology`.
-/

namespace Sabrina.OWL2.SWRL

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes

/-! ### 1. W3C SWRL / SWRLB Namespace Constants -/

def swrlNS : String := "http://www.w3.org/2003/11/swrl#"
def swrlbNS : String := "http://www.w3.org/2003/11/swrlb#"

def swrl (name : String) : IRI := swrlNS ++ name
def swrlb (name : String) : IRI := swrlbNS ++ name

/-! ### 2. SWRL Abstract Syntax -/

/-- Individual-valued argument in a SWRL atom (variable or OWL 2 individual). -/
inductive IArg where
  | var (name : IRI)
  | ind (value : Individual)
  deriving DecidableEq, Repr

/-- Data-valued argument in a SWRL atom (variable or OWL 2 literal). -/
inductive DArg where
  | var (name : IRI)
  | lit (value : Literal)
  deriving DecidableEq, Repr

/-- The 7 W3C OWL 2 / SWRL atom kinds. -/
inductive SWRLAtom where
  | classAtom (cls : ClassExpr) (arg : IArg)
  | dataRangeAtom (range : DataRange) (arg : DArg)
  | objectPropertyAtom (prop : ObjectProperty) (arg1 arg2 : IArg)
  | dataPropertyAtom (prop : IRI) (arg1 : IArg) (arg2 : DArg)
  | sameIndividualAtom (arg1 arg2 : IArg)
  | differentIndividualsAtom (arg1 arg2 : IArg)
  | builtinAtom (builtin : IRI) (args : List DArg)
  deriving DecidableEq, Repr

/-- A DL-safe SWRL rule `body → head` (conjunction of body atoms implies conjunction of head atoms). -/
structure SWRLRule where
  body : List SWRLAtom
  head : List SWRLAtom
  deriving DecidableEq, Repr

/-! ### 3. Variable, Individual, and Literal Extraction -/

def IArg.vars : IArg → List IRI
  | .var v => [v]
  | .ind _ => []

def DArg.vars : DArg → List IRI
  | .var v => [v]
  | .lit _ => []

def IArg.namedIndividuals : IArg → List IRI
  | .ind (.named a) => [a]
  | _ => []

def DArg.literals : DArg → List Literal
  | .lit l => [l]
  | .var _ => []

def SWRLAtom.iVars : SWRLAtom → List IRI
  | .classAtom _ a => a.vars
  | .dataRangeAtom _ _ => []
  | .objectPropertyAtom _ a b => (a.vars ++ b.vars).eraseDups
  | .dataPropertyAtom _ a _ => a.vars
  | .sameIndividualAtom a b => (a.vars ++ b.vars).eraseDups
  | .differentIndividualsAtom a b => (a.vars ++ b.vars).eraseDups
  | .builtinAtom _ _ => []

def SWRLAtom.dVars : SWRLAtom → List IRI
  | .classAtom _ _ => []
  | .dataRangeAtom _ a => a.vars
  | .objectPropertyAtom _ _ _ => []
  | .dataPropertyAtom _ _ b => b.vars
  | .sameIndividualAtom _ _ => []
  | .differentIndividualsAtom _ _ => []
  | .builtinAtom _ args => (args.flatMap DArg.vars).eraseDups

def SWRLAtom.isBuiltin : SWRLAtom → Bool
  | .builtinAtom _ _ => true
  | _ => false

def SWRLAtom.isGround (a : SWRLAtom) : Bool :=
  a.iVars.isEmpty && a.dVars.isEmpty

def SWRLAtom.literals : SWRLAtom → List Literal
  | .dataRangeAtom _ a => a.literals
  | .dataPropertyAtom _ _ b => b.literals
  | .builtinAtom _ args => (args.flatMap DArg.literals).eraseDups
  | _ => []

def classExprNamedInds : ClassExpr → List IRI
  | .named _ | .objectSelf _ | .dataSome _ _ | .dataAll _ _
  | .dataValue _ _ | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => []
  | .complement c => classExprNamedInds c
  | .intersection a b | .union a b => classExprNamedInds a ++ classExprNamedInds b
  | .oneOf inds => inds.filterMap fun | .named a => some a | _ => none
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c
  | .objectMax _ _ c | .objectExact _ _ c => classExprNamedInds c
  | .objectValue _ (.named a) => [a]
  | .objectValue _ (.anonymous _ _) => []

def SWRLAtom.namedIndividuals : SWRLAtom → List IRI
  | .classAtom c a => (classExprNamedInds c ++ a.namedIndividuals).eraseDups
  | .dataRangeAtom _ _ => []
  | .objectPropertyAtom _ a b => (a.namedIndividuals ++ b.namedIndividuals).eraseDups
  | .dataPropertyAtom _ a _ => a.namedIndividuals
  | .sameIndividualAtom a b => (a.namedIndividuals ++ b.namedIndividuals).eraseDups
  | .differentIndividualsAtom a b => (a.namedIndividuals ++ b.namedIndividuals).eraseDups
  | .builtinAtom _ _ => []

def SWRLRule.bodyIVars (r : SWRLRule) : List IRI :=
  (r.body.flatMap SWRLAtom.iVars).eraseDups

def SWRLRule.headIVars (r : SWRLRule) : List IRI :=
  (r.head.flatMap SWRLAtom.iVars).eraseDups

def SWRLRule.iVars (r : SWRLRule) : List IRI :=
  (r.bodyIVars ++ r.headIVars).eraseDups

def SWRLRule.bodyDVars (r : SWRLRule) : List IRI :=
  (r.body.flatMap SWRLAtom.dVars).eraseDups

def SWRLRule.headDVars (r : SWRLRule) : List IRI :=
  (r.head.flatMap SWRLAtom.dVars).eraseDups

def SWRLRule.dVars (r : SWRLRule) : List IRI :=
  (r.bodyDVars ++ r.headDVars).eraseDups

def SWRLRule.bodyNonBuiltinDVars (r : SWRLRule) : List IRI :=
  ((r.body.filter fun a => !a.isBuiltin).flatMap SWRLAtom.dVars).eraseDups

def SWRLRule.namedIndividuals (r : SWRLRule) : List IRI :=
  ((r.body ++ r.head).flatMap SWRLAtom.namedIndividuals).eraseDups

def SWRLRule.literals (r : SWRLRule) : List Literal :=
  ((r.body ++ r.head).flatMap SWRLAtom.literals).eraseDups

def SWRLRule.hasBuiltins (r : SWRLRule) : Bool :=
  (r.body ++ r.head).any SWRLAtom.isBuiltin

def SWRLRule.hasDVars (r : SWRLRule) : Bool :=
  !r.dVars.isEmpty

def axiomNamedInds : Axiom → List IRI
  | .subClassOf a b => classExprNamedInds a ++ classExprNamedInds b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classExprNamedInds
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c
  | .hasKey c _ _ => classExprNamedInds c
  | .sameIndividuals inds | .differentIndividuals inds =>
    inds.filterMap fun | .named a => some a | _ => none
  | .classAssertion c (.named a) => a :: classExprNamedInds c
  | .classAssertion c (.anonymous _ _) => classExprNamedInds c
  | .objectAssertion _ a b | .negativeObjectAssertion _ a b =>
    [a, b].filterMap fun | .named x => some x | _ => none
  | .dataAssertion _ (.named a) _ | .negativeDataAssertion _ (.named a) _ => [a]
  | _ => []

def collectNamedIndividuals (o : Ontology) (rules : List SWRLRule := [])
    (extraNamedInds : List IRI := []) : List IRI :=
  ((o.flatMap axiomNamedInds) ++ (rules.flatMap SWRLRule.namedIndividuals) ++ extraNamedInds).eraseDups

def classExprLiterals : ClassExpr → List Literal
  | .complement c => classExprLiterals c
  | .intersection a b | .union a b => classExprLiterals a ++ classExprLiterals b
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c
  | .objectMax _ _ c | .objectExact _ _ c => classExprLiterals c
  | .dataValue _ l => [l]
  | _ => []

def axiomLiterals : Axiom → List Literal
  | .subClassOf a b => classExprLiterals a ++ classExprLiterals b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
    cs.flatMap classExprLiterals
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c
  | .hasKey c _ _ => classExprLiterals c
  | .classAssertion c _ => classExprLiterals c
  | .dataAssertion _ _ l | .negativeDataAssertion _ _ l => [l]
  | _ => []

def collectKnownLiterals (o : Ontology) (rules : List SWRLRule := []) : List Literal :=
  ((o.flatMap axiomLiterals) ++ (rules.flatMap SWRLRule.literals)).eraseDups

/-! ### 4. Substitution on SWRL Terms, Atoms, and Rules -/

def IArg.subst (envI : List (IRI × Individual)) : IArg → IArg
  | .var v => match envI.lookup v with | some a => .ind a | none => .var v
  | .ind a => .ind a

def DArg.subst (envD : List (IRI × Literal)) : DArg → DArg
  | .var v => match envD.lookup v with | some l => .lit l | none => .var v
  | .lit l => .lit l

def SWRLAtom.subst (envI : List (IRI × Individual)) (envD : List (IRI × Literal)) :
    SWRLAtom → SWRLAtom
  | .classAtom c a => .classAtom c (a.subst envI)
  | .dataRangeAtom d a => .dataRangeAtom d (a.subst envD)
  | .objectPropertyAtom r a b => .objectPropertyAtom r (a.subst envI) (b.subst envI)
  | .dataPropertyAtom p a b => .dataPropertyAtom p (a.subst envI) (b.subst envD)
  | .sameIndividualAtom a b => .sameIndividualAtom (a.subst envI) (b.subst envI)
  | .differentIndividualsAtom a b => .differentIndividualsAtom (a.subst envI) (b.subst envI)
  | .builtinAtom b args => .builtinAtom b (args.map (DArg.subst envD))

def SWRLRule.subst (envI : List (IRI × Individual)) (envD : List (IRI × Literal))
    (r : SWRLRule) : SWRLRule :=
  { body := r.body.map (SWRLAtom.subst envI envD),
    head := r.head.map (SWRLAtom.subst envI envD) }

/-! ### 5. Direct Semantics for DL-Safe SWRL Rules -/

/-- Semantics of SWRL built-in predicates parameterized by a `DatatypeMap`. -/
abbrev BuiltinSemantics (dm : DatatypeMap) :=
  (i : Interpretation dm) → IRI → List i.Data → Prop

/-- Trivial empty built-in semantics (for built-in-free rules). -/
def noBuiltinSem (dm : DatatypeMap) : BuiltinSemantics dm :=
  fun _ _ _ => False

def evalIArg {dm : DatatypeMap} (i : Interpretation dm) (σI : IRI → i.Object) :
    IArg → i.Object
  | .var v => σI v
  | .ind a => i.individuals a

def evalDArg {dm : DatatypeMap} (i : Interpretation dm) (σD : IRI → i.Data) :
    DArg → i.Data
  | .var v => σD v
  | .lit l => i.literalValue l

def atomHolds {dm : DatatypeMap} (bSem : BuiltinSemantics dm) (i : Interpretation dm)
    (σI : IRI → i.Object) (σD : IRI → i.Data) : SWRLAtom → Prop
  | .classAtom c a => classHolds i (evalIArg i σI a) c
  | .dataRangeAtom d a => dataHolds i (evalDArg i σD a) d
  | .objectPropertyAtom r a b => objectHolds i r (evalIArg i σI a) (evalIArg i σI b)
  | .dataPropertyAtom p a b => i.dataProperties p (evalIArg i σI a) (evalDArg i σD b)
  | .sameIndividualAtom a b => evalIArg i σI a = evalIArg i σI b
  | .differentIndividualsAtom a b => evalIArg i σI a ≠ evalIArg i σI b
  | .builtinAtom b args => bSem i b (args.map (evalDArg i σD))

/-- DL-safe rule satisfaction (Motik–Sattler–Studer 2005):
    every individual variable in `r` is bound only to interpretations of
    explicitly named individuals in `namedInds`. -/
def satisfiesDLSafeRule {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (i : Interpretation dm) (r : SWRLRule) : Prop :=
  ∀ (σI : IRI → i.Object) (σD : IRI → i.Data),
    (∀ v ∈ r.iVars, ∃ a ∈ namedInds, σI v = i.individuals (.named a)) →
    (∀ a ∈ r.body, atomHolds bSem i σI σD a) →
    (∀ a ∈ r.head, atomHolds bSem i σI σD a)

def modelsWithRules {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (i : Interpretation dm) (o : Ontology)
    (rules : List SWRLRule) : Prop :=
  ∃ assign : String → String → i.Object,
    satisfies (i.withAnonymous assign) o ∧
    ∀ r ∈ rules, satisfiesDLSafeRule bSem namedInds (i.withAnonymous assign) r

def SatisfiableWithRules (dm : DatatypeMap) (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (o : Ontology) (rules : List SWRLRule) : Prop :=
  ∃ i : Interpretation dm, modelsWithRules bSem namedInds i o rules

def EntailsWithRules (dm : DatatypeMap) (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (o : Ontology) (rules : List SWRLRule) (q : Ontology) : Prop :=
  ∀ i : Interpretation dm, modelsWithRules bSem namedInds i o rules → models i q

/-! ### 6. Fundamental Semantic Lemmas -/

theorem modelsWithRules_nil_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (i : Interpretation dm) (o : Ontology) :
    modelsWithRules bSem namedInds i o [] ↔ models i o := by
  simp [modelsWithRules, models]

theorem satisfiableWithRules_nil_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (o : Ontology) :
    SatisfiableWithRules dm bSem namedInds o [] ↔ Satisfiable dm o := by
  simp [SatisfiableWithRules, Satisfiable, modelsWithRules_nil_iff]

theorem entailsWithRules_nil_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (namedInds : List IRI) (o q : Ontology) :
    EntailsWithRules dm bSem namedInds o [] q ↔ Entails dm o q := by
  simp [EntailsWithRules, Entails, modelsWithRules_nil_iff]

def applyEnvI {dm : DatatypeMap} (i : Interpretation dm) (envI : List (IRI × Individual))
    (σI : IRI → i.Object) (v : IRI) : i.Object :=
  match envI.lookup v with
  | some a => i.individuals a
  | none => σI v

def applyEnvD {dm : DatatypeMap} (i : Interpretation dm) (envD : List (IRI × Literal))
    (σD : IRI → i.Data) (v : IRI) : i.Data :=
  match envD.lookup v with
  | some l => i.literalValue l
  | none => σD v

theorem evalIArg_subst {dm : DatatypeMap} (i : Interpretation dm)
    (envI : List (IRI × Individual)) (σI : IRI → i.Object) (a : IArg) :
    evalIArg i σI (a.subst envI) = evalIArg i (applyEnvI i envI σI) a := by
  cases a with
  | ind _ => rfl
  | var v =>
    simp only [IArg.subst, applyEnvI, evalIArg]
    cases envI.lookup v <;> rfl

theorem evalDArg_subst {dm : DatatypeMap} (i : Interpretation dm)
    (envD : List (IRI × Literal)) (σD : IRI → i.Data) (a : DArg) :
    evalDArg i σD (a.subst envD) = evalDArg i (applyEnvD i envD σD) a := by
  cases a with
  | lit _ => rfl
  | var v =>
    simp only [DArg.subst, applyEnvD, evalDArg]
    cases envD.lookup v <;> rfl

theorem atomHolds_subst_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (envI : List (IRI × Individual)) (envD : List (IRI × Literal))
    (σI : IRI → i.Object) (σD : IRI → i.Data) (a : SWRLAtom) :
    atomHolds bSem i σI σD (a.subst envI envD) ↔
      atomHolds bSem i (applyEnvI i envI σI) (applyEnvD i envD σD) a := by
  cases a with
  | classAtom c x => simp [SWRLAtom.subst, atomHolds, evalIArg_subst]
  | dataRangeAtom d x => simp [SWRLAtom.subst, atomHolds, evalDArg_subst]
  | objectPropertyAtom r x y => simp [SWRLAtom.subst, atomHolds, evalIArg_subst]
  | dataPropertyAtom p x y => simp [SWRLAtom.subst, atomHolds, evalIArg_subst, evalDArg_subst]
  | sameIndividualAtom x y => simp [SWRLAtom.subst, atomHolds, evalIArg_subst]
  | differentIndividualsAtom x y => simp [SWRLAtom.subst, atomHolds, evalIArg_subst]
  | builtinAtom b args =>
    simp only [SWRLAtom.subst, atomHolds, List.map_map]
    have hEq : (evalDArg i σD ∘ DArg.subst envD) = evalDArg i (applyEnvD i envD σD) := by
      funext x; exact evalDArg_subst i envD σD x
    rw [hEq]

private theorem eraseDups_cons_ne_nil {α : Type} [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    (a :: xs).eraseDups ≠ [] := fun h => by
  have hm : a ∈ (a :: xs).eraseDups := List.mem_eraseDups.mpr (List.mem_cons_self ..)
  rw [h] at hm; cases hm

/-- If `a` has no individual variables and no data variables, `atomHolds` is
    independent of the variable assignments `σI` and `σD`. -/
theorem atomHolds_ground_irrel {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (i : Interpretation dm) (σI₁ σI₂ : IRI → i.Object) (σD₁ σD₂ : IRI → i.Data)
    {a : SWRLAtom} (hg : a.isGround = true) :
    atomHolds bSem i σI₁ σD₁ a ↔ atomHolds bSem i σI₂ σD₂ a := by
  obtain ⟨hi, hd⟩ := Bool.and_eq_true_iff.mp hg
  have hiNil : a.iVars = [] := List.isEmpty_iff.mp hi
  have hdNil : a.dVars = [] := List.isEmpty_iff.mp hd
  cases a with
  | classAtom c x =>
    cases x with
    | var _ => simp [SWRLAtom.iVars, IArg.vars] at hiNil
    | ind _ => rfl
  | dataRangeAtom d x =>
    cases x with
    | var _ => simp [SWRLAtom.dVars, DArg.vars] at hdNil
    | lit _ => rfl
  | objectPropertyAtom r x y =>
    cases x with
    | var v => exact (eraseDups_cons_ne_nil v _ (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
    | ind _ =>
      cases y with
      | var v => exact (eraseDups_cons_ne_nil v [] (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
      | ind _ => rfl
  | dataPropertyAtom p x y =>
    cases x with
    | var _ => simp [SWRLAtom.iVars, IArg.vars] at hiNil
    | ind _ =>
      cases y with
      | var _ => simp [SWRLAtom.dVars, DArg.vars] at hdNil
      | lit _ => rfl
  | sameIndividualAtom x y =>
    cases x with
    | var v => exact (eraseDups_cons_ne_nil v _ (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
    | ind _ =>
      cases y with
      | var v => exact (eraseDups_cons_ne_nil v [] (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
      | ind _ => rfl
  | differentIndividualsAtom x y =>
    cases x with
    | var v => exact (eraseDups_cons_ne_nil v _ (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
    | ind _ =>
      cases y with
      | var v => exact (eraseDups_cons_ne_nil v [] (by simpa [SWRLAtom.iVars, IArg.vars] using hiNil)).elim
      | ind _ => rfl
  | builtinAtom b args =>
    have hmap : args.map (evalDArg i σD₁) = args.map (evalDArg i σD₂) := by
      apply List.map_congr_left
      intro x hx
      cases x with
      | lit _ => rfl
      | var v =>
        have hmem : v ∈ (args.flatMap DArg.vars).eraseDups :=
          List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨.var v, hx, List.mem_cons_self ..⟩)
        rw [SWRLAtom.dVars] at hdNil
        rw [hdNil] at hmem; cases hmem
    simp [atomHolds, hmap]

private theorem lookup_map_named (envI : List (IRI × IRI)) (v x : IRI)
    (h : envI.lookup v = some x) :
    (envI.map fun (w, a) => (w, Individual.named a)).lookup v = some (.named x) := by
  induction envI with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨k, val⟩
    simp only [List.lookup, List.map_cons] at h ⊢
    cases hvk : (v == k) with
    | true =>
      simp only [hvk] at h ⊢
      cases h; rfl
    | false =>
      simp only [hvk] at h ⊢
      exact ih h

/-- Any named-individual grounding of a DL-safe rule is a semantic consequence of
    `satisfiesDLSafeRule`. -/
theorem satisfiesDLSafeRule_ground_instance {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    {namedInds : List IRI} {i : Interpretation dm} {r : SWRLRule}
    (hr : satisfiesDLSafeRule bSem namedInds i r)
    (envI : List (IRI × IRI)) (envD : List (IRI × Literal))
    (hBound : ∀ v ∈ r.iVars, ∃ a ∈ namedInds, envI.lookup v = some a)
    (σI : IRI → i.Object) (σD : IRI → i.Data) :
    (∀ a ∈ (r.subst (envI.map fun (v, x) => (v, .named x)) envD).body,
      atomHolds bSem i σI σD a) →
    (∀ a ∈ (r.subst (envI.map fun (v, x) => (v, .named x)) envD).head,
      atomHolds bSem i σI σD a) := by
  intro hbody a ha
  let envI' := envI.map fun (v, x) => (v, Individual.named x)
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
  rw [atomHolds_subst_iff]
  apply hr (applyEnvI i envI' σI) (applyEnvD i envD σD)
  · intro v hv
    obtain ⟨x, hxMem, hlk⟩ := hBound v hv
    exact ⟨x, hxMem, by simp [applyEnvI, envI', lookup_map_named envI v x hlk]⟩
  · intro b hb
    exact (atomHolds_subst_iff bSem i envI' envD σI σD b).mp
      (hbody (b.subst envI' envD) (List.mem_map_of_mem hb))
  · exact ha₀

/-! ### 7. DL-Safety & Well-Formedness Validation -/

/-- Validate that a rule satisfies W3C DL-safety (every individual variable in the head
    occurs in the body, every data variable in the head occurs in the body, and built-ins
    do not appear in the rule head). Returns `none` when valid, or an error message. -/
def diagnoseDLSafeRule (r : SWRLRule) : Option String :=
  if r.head.isEmpty then
    some "SWRL rule has empty head"
  else if r.head.any SWRLAtom.isBuiltin then
    some "SWRL built-in atoms are not permitted in rule heads"
  else
    let bIVars := r.bodyIVars
    let bDVars := r.bodyDVars
    match r.headIVars.find? (fun v => !bIVars.contains v) with
    | some v => some s!"SWRL rule is not DL-safe: head individual variable '{v}' does not appear in body"
    | none =>
      match r.headDVars.find? (fun v => !bDVars.contains v) with
      | some v => some s!"SWRL rule is not DL-safe: head data variable '{v}' does not appear in body"
      | none => none

def checkDLSafeRule (r : SWRLRule) : Bool :=
  (diagnoseDLSafeRule r).isNone

def diagnoseDLSafeRules (rules : List SWRLRule) : Option String :=
  rules.findSome? diagnoseDLSafeRule

#print axioms modelsWithRules_nil_iff
#print axioms atomHolds_subst_iff
#print axioms atomHolds_ground_irrel
#print axioms satisfiesDLSafeRule_ground_instance

end Sabrina.OWL2.SWRL
