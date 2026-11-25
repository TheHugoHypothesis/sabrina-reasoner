import Sabrina.OWL2.SROIQD.Search

/-! M4 — Recursive Boolean/quantified core (`ALCHI`) with budget-independent
    tableau saturation, canonical model construction from open saturated
    branches, and refutation completeness. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole RoleTheory)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)

/-! ### 1. Formal Core Fragment Boundary (`ALCHI`) -/

def isCoreClassIRI (r : IRI) : Bool := r != thing && r != nothing
def isCoreObjPropIRI (r : IRI) : Bool := r != topObjectProperty && r != bottomObjectProperty

private theorem coreClassIRI_ne {r : IRI} (h : isCoreClassIRI r = true) :
    r ≠ thing ∧ r ≠ nothing := by
  simp only [isCoreClassIRI, Bool.and_eq_true, bne_iff_ne] at h; exact h

private theorem coreObjPropIRI_ne {r : IRI} (h : isCoreObjPropIRI r = true) :
    r ≠ topObjectProperty ∧ r ≠ bottomObjectProperty := by
  simp only [isCoreObjPropIRI, Bool.and_eq_true, bne_iff_ne] at h; exact h

/-- Formal boundary of the recursive Boolean/quantified core fragment (`ALCHI`):
    `⊤`, `⊥`, signed atomic classes, conjunction, disjunction, existential
    restrictions `∃R.C`, and universal restrictions `∀R.C` over oriented roles
    (`R` or `R⁻`). -/
def Concept.isCore : Concept → Bool
  | .top | .bottom => true
  | .lit p _ => isCoreClassIRI p
  | .conj a b | .disj a b => a.isCore && b.isCore
  | .some r c | .all r c => isCoreObjPropIRI r.1 && c.isCore
  | _ => false

theorem Concept.isCore_dual (c : Concept) : c.dual.isCore = c.isCore := by
  induction c with
  | min n _ _ | dataMin n _ _ => cases n <;> rfl
  | _ => simp_all [Concept.dual, Concept.isCore]

/-- A `Problem` belongs to the recursive core fragment (`ALCHI`) when its root
    concept and TBox inclusions use core concepts, its role hierarchy uses
    ordinary object properties, and non-core extensions (role chains, role
    characteristics, cardinality/nominals/keys/datatypes/ABox) are empty. -/
def Problem.isCore (p : Problem) : Bool :=
  p.root.isCore &&
  p.tbox.all (fun q => q.sub.isCore && q.sup.isCore) &&
  p.rules.all (fun (r, t) => isCoreObjPropIRI r.1 && isCoreObjPropIRI t.1) &&
  p.chains.isEmpty &&
  p.chars.reflexive.isEmpty &&
  p.chars.irreflexive.isEmpty &&
  p.chars.asymmetric.isEmpty &&
  p.chars.disjoint.isEmpty &&
  p.subData.isEmpty &&
  p.disjointData.isEmpty &&
  p.funcData.isEmpty &&
  p.dataRanges.isEmpty &&
  p.keys.isEmpty &&
  p.classAssertions.isEmpty &&
  p.objAssertions.isEmpty &&
  p.negObjAssertions.isEmpty &&
  p.sameInds.isEmpty &&
  p.diffInds.isEmpty &&
  p.dataAssertions.isEmpty &&
  p.negDataAssertions.isEmpty

/-! ### 2. Budget-Independent Clash & Saturation Predicates -/

/-- A tableau branch is clash-free for the core fragment if no node is labeled
    with `⊥` and no node carries both `(x, A)` and `(x, ¬A)`. -/
structure Branch.CoreClashFree (s : Branch) : Prop where
  noBottom : ∀ x, (x, .bottom) ∉ s.labels
  noLitClash : ∀ x p, (x, .lit p true) ∈ s.labels → (x, .lit p false) ∉ s.labels

/-- Budget-independent tableau saturation for a core `Problem`:
    all Boolean connectives, existential witnesses, universal propagations,
    oriented role-hierarchy inclusions, and TBox GCIs are saturated across the
    branch without depending on any `maxNodes` or step budget. -/
structure Branch.CoreSaturated (p : Problem) (s : Branch) : Prop where
  root : (0, p.root) ∈ s.labels
  conj : ∀ x a b, (x, .conj a b) ∈ s.labels → (x, a) ∈ s.labels ∧ (x, b) ∈ s.labels
  disj : ∀ x a b, (x, .disj a b) ∈ s.labels → (x, a) ∈ s.labels ∨ (x, b) ∈ s.labels
  some : ∀ x r c, (x, .some r c) ∈ s.labels → ∃ y, s.edge r x y = true ∧ (y, c) ∈ s.labels
  all : ∀ x r c, (x, .all r c) ∈ s.labels → ∀ y, s.edge r x y = true → (y, c) ∈ s.labels
  rules : ∀ r t, (r, t) ∈ p.rules → ∀ x y, s.edge r x y = true → s.edge t x y = true
  tbox : ∀ q ∈ p.tbox, ∀ x ∈ s.support, (x, q.sub.dual) ∈ s.labels ∨ (x, q.sup) ∈ s.labels

/-! ### 3. Canonical Interpretation from an Open Saturated Tableau Branch -/

/-- Canonical OWL 2 Direct Semantics interpretation constructed from the active
    support of a tableau branch `s`. -/
abbrev Branch.toCoreInterpretation (s : Branch) (h0 : 0 ∈ s.support) :
    Interpretation datatypeMap where
  Object := {x : Nat // x ∈ s.support}
  objectNonempty := ⟨⟨0, h0⟩⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes r x :=
    if r = thing then True
    else if r = nothing then False
    else (x.val, .lit r true) ∈ s.labels
  objectProperties r x y :=
    if r = topObjectProperty then True
    else if r = bottomObjectProperty then False
    else (r, x.val, y.val) ∈ s.edges
  dataProperties r _ _ :=
    if r = topDataProperty then True else False
  individuals _ := ⟨0, h0⟩
  datatypes t y := t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = y
  literalValue l := decodeLiteral l
  lexicalAgreement := fun _ _ h => h
  named _ := True
  namedIndividual _ := trivial
  thingExt := by simp
  nothingExt := by
    have h : nothing ≠ thing := by decide
    simp [h]
  topObjectExt := by simp
  bottomObjectExt := by
    have h : bottomObjectProperty ≠ topObjectProperty := by decide
    simp [h]
  topDataExt := by simp
  bottomDataExt := by
    have h : bottomDataProperty ≠ topDataProperty := by decide
    simp [h]
  literalDatatypeExt := by simp
  datatypeAgreement := by
    intro t ht y
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp [hn]; exact Iff.rfl

private theorem holdsOriented_toCoreInterpretation (s : Branch) (h0 : 0 ∈ s.support)
    {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    (x y : {n : Nat // n ∈ s.support}) :
    holdsOriented (s.toCoreInterpretation h0) r x y ↔ s.edge r x.val y.val = true := by
  have ⟨hne1, hne2⟩ := coreObjPropIRI_ne hr
  rcases r with ⟨rn, _ | _⟩
  · simp [holdsOriented, Branch.edge, hne1, hne2]
  · simp [holdsOriented, Branch.edge, hne1, hne2]

/-- Truth lemma for open saturated tableau branches: every core concept label
    `(x, c) ∈ s.labels` holds at `x` in the canonical interpretation
    `s.toCoreInterpretation`. -/
theorem core_saturated_holds {p : Problem} {s : Branch}
    (hcf : s.CoreClashFree) (hsat : s.CoreSaturated p)
    (x : {n : Nat // n ∈ s.support}) {c : Concept}
    (hcore : c.isCore = true) (hl : (x.val, c) ∈ s.labels) :
    holds (s.toCoreInterpretation (Branch.label_support hsat.root)) x c := by
  let h0 := Branch.label_support hsat.root
  induction c generalizing x with
  | top => trivial
  | bottom => exact False.elim (hcf.noBottom x.val hl)
  | lit name sign =>
    simp only [Concept.isCore] at hcore
    have ⟨hne1, hne2⟩ := coreClassIRI_ne hcore
    cases sign with
    | true =>
      simp only [holds, hne1, hne2, ↓reduceIte]
      exact hl
    | false =>
      simp only [holds, hne1, hne2, ↓reduceIte]
      exact fun hpos => hcf.noLitClash x.val name hpos hl
  | conj a b iha ihb =>
    simp only [Concept.isCore, Bool.and_eq_true] at hcore
    obtain ⟨hla, hlb⟩ := hsat.conj x.val a b hl
    exact ⟨iha x hcore.1 hla, ihb x hcore.2 hlb⟩
  | disj a b iha ihb =>
    simp only [Concept.isCore, Bool.and_eq_true] at hcore
    rcases hsat.disj x.val a b hl with hla | hlb
    · exact Or.inl (iha x hcore.1 hla)
    · exact Or.inr (ihb x hcore.2 hlb)
  | some r body ih =>
    simp only [Concept.isCore, Bool.and_eq_true] at hcore
    obtain ⟨y, hedge, hly⟩ := hsat.some x.val r body hl
    have hy : y ∈ s.support := Branch.label_support hly
    exact ⟨⟨y, hy⟩,
      (holdsOriented_toCoreInterpretation s h0 hcore.1 x ⟨y, hy⟩).mpr hedge,
      ih ⟨y, hy⟩ hcore.2 hly⟩
  | all r body ih =>
    simp only [Concept.isCore, Bool.and_eq_true] at hcore
    intro y hxy
    have hedge : s.edge r x.val y.val = true :=
      (holdsOriented_toCoreInterpretation s h0 hcore.1 x y).mp hxy
    exact ih y hcore.2 (hsat.all x.val r body hl y.val hedge)
  | nom _ _ | self _ _ | min _ _ _ | max _ _ _
  | dataSome _ _ | dataAll _ _ | dataValue _ _ _ | dataMin _ _ _ | dataMax _ _ _ =>
    simp [Concept.isCore] at hcore

/-- Model construction theorem for M4: every open (`CoreClashFree`),
    saturated (`CoreSaturated`) tableau branch for a core problem `p` yields a
    genuine OWL 2 Direct Semantics model of `p`. -/
theorem core_saturated_sat {p : Problem} {s : Branch}
    (hp : p.isCore = true) (hcf : s.CoreClashFree) (hsat : s.CoreSaturated p) :
    p.Sat := by
  simp only [Problem.isCore, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hp
  rcases hp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hrootC, htboxC⟩, hrulesC⟩, hchains⟩, hrefl⟩, hirrefl⟩,
    hasym⟩, hdisj⟩, hsubD⟩, hdisjD⟩, hfuncD⟩, hdr⟩, hkeys⟩, hca⟩, hoa⟩, hnoa⟩,
    hsame⟩, hdiff⟩, hda⟩, hnda⟩
  let h0 : 0 ∈ s.support := Branch.label_support hsat.root
  let i := s.toCoreInterpretation h0
  refine ⟨i, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨0, h0⟩, core_saturated_holds hcf hsat ⟨0, h0⟩ hrootC hsat.root⟩
  · -- tbox
    intro q hq x hsub
    have ⟨hsubC, hsupC⟩ := htboxC q hq
    rcases hsat.tbox q hq x.val x.property with hdual | hsup
    · have hdualC : q.sub.dual.isCore = true := (Concept.isCore_dual q.sub).trans hsubC
      have hnot := (holds_dual i x q.sub).mp (core_saturated_holds hcf hsat x hdualC hdual)
      exact False.elim (hnot hsub)
    · exact core_saturated_holds hcf hsat x hsupC hsup
  · -- rules
    intro ⟨r, t⟩ hrt x y hxy
    have ⟨hrC, htC⟩ := hrulesC (r, t) hrt
    have hedge := (holdsOriented_toCoreInterpretation s h0 hrC x y).mp hxy
    exact (holdsOriented_toCoreInterpretation s h0 htC x y).mpr (hsat.rules r t hrt x.val y.val hedge)
  · intro c hc; exact False.elim (List.not_mem_nil (hchains ▸ hc))
  · intro r hr; exact False.elim (List.not_mem_nil (hrefl ▸ hr))
  · intro r hr; exact False.elim (List.not_mem_nil (hirrefl ▸ hr))
  · intro r hr; exact False.elim (List.not_mem_nil (hasym ▸ hr))
  · intro rs hrs; exact False.elim (List.not_mem_nil (hdisj ▸ hrs))
  · intro rs hrs; exact False.elim (List.not_mem_nil (hsubD ▸ hrs))
  · intro rs hrs; exact False.elim (List.not_mem_nil (hdisjD ▸ hrs))
  · intro dp hdp; exact False.elim (List.not_mem_nil (hfuncD ▸ hdp))
  · intro dr hdr'; exact False.elim (List.not_mem_nil (hdr ▸ hdr'))
  · intro k hk; exact False.elim (List.not_mem_nil (hkeys ▸ hk))
  · intro ac hac; exact False.elim (List.not_mem_nil (hca ▸ hac))
  · intro rab hrab; exact False.elim (List.not_mem_nil (hoa ▸ hrab))
  · intro rab hrab; exact False.elim (List.not_mem_nil (hnoa ▸ hrab))
  · intro ab hab; exact False.elim (List.not_mem_nil (hsame ▸ hab))
  · intro ab hab; exact False.elim (List.not_mem_nil (hdiff ▸ hab))
  · intro ral hral; exact False.elim (List.not_mem_nil (hda ▸ hral))
  · intro ral hral; exact False.elim (List.not_mem_nil (hnda ▸ hral))

/-- Contrapositive of model construction: no unsatisfiable core problem can have
    a clash-free saturated branch. -/
theorem core_unsat_clashes {p : Problem} {s : Branch}
    (hp : p.isCore = true) (hunsat : ¬ p.Sat) (hsat : s.CoreSaturated p) :
    ¬ s.CoreClashFree :=
  fun hcf => hunsat (core_saturated_sat hp hcf hsat)

/-! ### 4. Budget-Independent Tableau Derivation & Refutation Completeness -/

/-- Budget-independent inductive tableau derivation tree from branch `s`:
    every branch either reaches an open saturated state or expands via a
    satisfiability-preserving `Transition p s`. -/
inductive CoreDerivation (p : Problem) : Branch → Prop where
  | step {s : Branch} (t : Transition p s) :
      (∀ b ∈ t.branches, CoreDerivation p b) → CoreDerivation p s
  | saturated {s : Branch} :
      s.CoreClashFree → s.CoreSaturated p → CoreDerivation p s

/-- Budget-independent finite tableau refutation tree from branch `s`:
    every branch closes via satisfiability-preserving transitions. -/
inductive CoreRefutation (p : Problem) : Branch → Prop where
  | step {s : Branch} (t : Transition p s) :
      (∀ b ∈ t.branches, CoreRefutation p b) → CoreRefutation p s

/-- Soundness of `CoreRefutation`: if a branch has a closed refutation tree,
    it is unsatisfiable. -/
theorem coreRefutation_sound {p : Problem} {s : Branch}
    (href : CoreRefutation p s) : ¬ s.Sat p := by
  induction href with
  | step t _ ih =>
    intro hsat
    obtain ⟨b, hb, hsatB⟩ := t.preserves hsat
    exact ih b hb hsatB

/-- Every bounded `checkClosed` certificate induces a budget-independent
    `CoreRefutation`. -/
theorem checkClosed_to_coreRefutation {p : Problem} {maxNodes depth : Nat} {s : Branch}
    (h : checkClosed p maxNodes depth s = true) : CoreRefutation p s := by
  induction depth generalizing s with
  | zero => cases h
  | succ d ih =>
    simp only [checkClosed] at h
    split at h
    · contradiction
    · rename_i t _
      exact .step t fun b hb => ih (List.all_eq_true.mp h b hb)

/-- Complete dichotomy for any budget-independent core tableau derivation:
    either `p` is satisfiable (`p.Sat`) or `s` has a finite closed tableau
    refutation (`CoreRefutation p s`). -/
theorem coreDerivation_dichotomy {p : Problem} {s : Branch}
    (hp : p.isCore = true) (hd : CoreDerivation p s) :
    p.Sat ∨ CoreRefutation p s := by
  induction hd with
  | saturated hcf hsat =>
    exact Or.inl (core_saturated_sat hp hcf hsat)
  | step t _ ih =>
    by_cases hsat : p.Sat
    · exact Or.inl hsat
    · exact Or.inr (.step t fun b hb => (ih b hb).resolve_left hsat)

/-- Refutation completeness for the core tableau calculus: for any unsatisfiable
    core problem `p` (`¬ p.Sat`), every saturated tableau derivation from `s`
    yields a closed tableau refutation `CoreRefutation p s`. -/
theorem coreDerivation_refutation_complete {p : Problem} {s : Branch}
    (hp : p.isCore = true) (hd : CoreDerivation p s) (hunsat : ¬ p.Sat) :
    CoreRefutation p s :=
  (coreDerivation_dichotomy hp hd).resolve_left hunsat

/-- Exact equivalence between unsatisfiability (`¬ p.Sat`) and existence of a
    closed tableau refutation from the initial branch of a core problem. -/
theorem coreDerivation_unsat_iff_refutation {p : Problem} {s0 : Branch}
    (hp : p.isCore = true) (hinit : initial p = some s0) (hd : CoreDerivation p s0) :
    ¬ p.Sat ↔ CoreRefutation p s0 :=
  ⟨coreDerivation_refutation_complete hp hd,
   fun href hsat => coreRefutation_sound href (initial_sat hinit hsat)⟩

/-! ### 5. M5 / M6 / M7 / M8 — Full `SROIQ(D)` Saturation, Model Construction & Refutation Completeness -/

def isCoreDataPropIRI (r : IRI) : Bool := r != topDataProperty && r != bottomDataProperty

/-- A `Concept` uses ordinary (non-top/bottom) class, object-property, and
    data-property IRIs in its restrictions (while allowing `.top` and `.bottom`
    concept constructors and all 16 `SROIQ(D)` concept forms). -/
def Concept.isOrdinary : Concept → Bool
  | .top | .bottom | .nom _ _ => true
  | .lit p _ => isCoreClassIRI p
  | .self r _ => isCoreObjPropIRI r.1
  | .conj a b | .disj a b => a.isOrdinary && b.isOrdinary
  | .some r c | .all r c | .min _ r c | .max _ r c => isCoreObjPropIRI r.1 && c.isOrdinary
  | .dataSome dp _ | .dataAll dp _ | .dataValue dp _ _ | .dataMin _ dp _ | .dataMax _ dp _ =>
    isCoreDataPropIRI dp

theorem Concept.isOrdinary_dual (c : Concept) : c.dual.isOrdinary = c.isOrdinary := by
  induction c with
  | min n _ _ | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.isOrdinary]
  | _ => simp_all [Concept.dual, Concept.isOrdinary]

/-- A full `SROIQ(D)` `Problem` uses ordinary IRIs in its concept restrictions
    and role hierarchy. -/
def Problem.isOrdinary (p : Problem) : Bool :=
  p.root.isOrdinary &&
  p.tbox.all (fun q => q.sub.isOrdinary && q.sup.isOrdinary) &&
  p.rules.all (fun (r, t) => isCoreObjPropIRI r.1 && isCoreObjPropIRI t.1) &&
  p.classAssertions.all (fun (_, c) => c.isOrdinary)

private theorem lookup_mem_pairs {α β : Type} [BEq α] [LawfulBEq α]
    {xs : List (α × β)} {a : α} {b : β} (h : xs.lookup a = some b) : (a, b) ∈ xs := by
  induction xs with
  | nil => simp [List.lookup] at h
  | cons hd tail ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.lookup] at h
    cases hb : (a == k) with
    | true =>
      simp only [hb, Option.some.injEq] at h
      have hk := beq_iff_eq.mp hb; subst hk h
      exact List.mem_cons_self ..
    | false =>
      simp only [hb] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem nom_lookup_in_support {s : Branch} {a : IRI} {k : Nat}
    (h : s.noms.lookup a = some k) : k ∈ s.support := by
  have hmem : (a, k) ∈ s.noms := lookup_mem_pairs h
  simp only [Branch.support, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hmem)))))

private theorem anon_lookup_in_support {s : Branch} {id : String × String} {k : Nat}
    (h : s.anons.lookup id = some k) : k ∈ s.support := by
  have hmem : (id, k) ∈ s.anons := lookup_mem_pairs h
  simp only [Branch.support, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hmem))))

/-- Resolve an `Individual` (named or document-scoped anonymous) to its active
    node in `s.support`. -/
def Branch.indNode (s : Branch) (h0 : 0 ∈ s.support) : Individual → {x : Nat // x ∈ s.support}
  | .named a =>
    match h : s.noms.lookup a with
    | some k => ⟨k, nom_lookup_in_support h⟩
    | none => ⟨0, h0⟩
  | .anonymous doc lid =>
    match h : s.anons.lookup (doc, lid) with
    | some k => ⟨k, anon_lookup_in_support h⟩
    | none => ⟨0, h0⟩

/-- Canonical OWL 2 Direct Semantics interpretation constructed from an open
    saturated full-`SROIQ(D)` tableau branch `s`, including nominals, anonymous
    individuals (excluded from `named` unless merged with a named individual),
    oriented roles, and 33-datatype data edges. -/
abbrev Branch.toSROIQDInterpretation (s : Branch) (h0 : 0 ∈ s.support) :
    Interpretation datatypeMap where
  Object := {x : Nat // x ∈ s.support}
  objectNonempty := ⟨⟨0, h0⟩⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes r x :=
    if r = thing then True
    else if r = nothing then False
    else (x.val, .lit r true) ∈ s.labels
  objectProperties r x y :=
    if r = topObjectProperty then True
    else if r = bottomObjectProperty then False
    else (r, x.val, y.val) ∈ s.edges
  dataProperties r x y :=
    if r = topDataProperty then True
    else if r = bottomDataProperty then False
    else ∃ v, y = some v ∧ (r, x.val, v) ∈ s.dataEdges
  individuals := s.indNode h0
  datatypes t y := t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = y
  literalValue l := decodeLiteral l
  lexicalAgreement := fun _ _ h => h
  named x := x.val = 0 ∨ ∃ a, s.noms.lookup a = some x.val
  namedIndividual a := by
    simp only [Branch.indNode]
    split
    · rename_i k hk; exact Or.inr ⟨a, hk⟩
    · exact Or.inl rfl
  thingExt := by simp
  nothingExt := by
    have h : nothing ≠ thing := by decide
    simp [h]
  topObjectExt := by simp
  bottomObjectExt := by
    have h : bottomObjectProperty ≠ topObjectProperty := by decide
    simp [h]
  topDataExt := by simp
  bottomDataExt := by
    have h : bottomDataProperty ≠ topDataProperty := by decide
    simp [h]
  literalDatatypeExt := by simp
  datatypeAgreement := by
    intro t ht y
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp [hn]; exact Iff.rfl

private theorem holdsOriented_toSROIQDInterpretation (s : Branch) (h0 : 0 ∈ s.support)
    {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    (x y : {n : Nat // n ∈ s.support}) :
    holdsOriented (s.toSROIQDInterpretation h0) r x y ↔ s.edge r x.val y.val = true := by
  have ⟨hne1, hne2⟩ := coreObjPropIRI_ne hr
  rcases r with ⟨rn, _ | _⟩
  · simp [holdsOriented, Branch.edge, hne1, hne2]
  · simp [holdsOriented, Branch.edge, hne1, hne2]

/-- Budget-independent saturation for a full `SROIQ(D)` `Problem`: covers
    Boolean connectives, existential/universal quantifiers, `ObjectHasSelf`,
    nominals (`ObjectOneOf` / `ObjectHasValue`), qualified cardinality (`min` /
    `max` with qualifier splitting and upper-bound merging), data restrictions
    (`dataSome`, `dataAll`, `dataValue`, `dataMin`, `dataMax`), role hierarchy
    and chains, role characteristics, data property axioms, mixed `HasKey`,
    TBox GCIs, and ABox assertions. -/
structure Branch.SROIQDSaturated (p : Problem) (s : Branch) : Prop where
  root : (0, p.root) ∈ s.labels
  conj : ∀ x a b, (x, .conj a b) ∈ s.labels → (x, a) ∈ s.labels ∧ (x, b) ∈ s.labels
  disj : ∀ x a b, (x, .disj a b) ∈ s.labels → (x, a) ∈ s.labels ∨ (x, b) ∈ s.labels
  some : ∀ x r c, (x, .some r c) ∈ s.labels → ∃ y, s.edge r x y = true ∧ (y, c) ∈ s.labels
  all : ∀ x r c, (x, .all r c) ∈ s.labels → ∀ y, s.edge r x y = true → (y, c) ∈ s.labels
  selfPos : ∀ x r, (x, .self r true) ∈ s.labels → s.edge r x x = true
  selfNeg : ∀ x r, (x, .self r false) ∈ s.labels → s.edge r x x = false
  nomPos : ∀ (x : {n : Nat // n ∈ s.support}) ind,
    (x.val, .nom ind true) ∈ s.labels → x = s.indNode (Branch.label_support root) ind
  nomNeg : ∀ (x : {n : Nat // n ∈ s.support}) ind,
    (x.val, .nom ind false) ∈ s.labels → x ≠ s.indNode (Branch.label_support root) ind
  min : ∀ (x : {n : Nat // n ∈ s.support}) n r c,
    (x.val, .min n r c) ∈ s.labels →
    AtLeast n (fun y : {k : Nat // k ∈ s.support} => s.edge r x.val y.val = true ∧ (y.val, c) ∈ s.labels)
  maxQual : ∀ (x y : {n : Nat // n ∈ s.support}) n r c,
    (x.val, .max n r c) ∈ s.labels → s.edge r x.val y.val = true →
    (y.val, c) ∈ s.labels ∨ (y.val, c.dual) ∈ s.labels
  maxBound : ∀ (x : {n : Nat // n ∈ s.support}) n r c,
    (x.val, .max n r c) ∈ s.labels →
    ¬ AtLeast (n + 1) (fun y : {k : Nat // k ∈ s.support} => s.edge r x.val y.val = true ∧ (y.val, c) ∈ s.labels)
  dataSome : ∀ (x : {n : Nat // n ∈ s.support}) dp d,
    (x.val, .dataSome dp d) ∈ s.labels →
    ∃ y, (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y ∧
      dataHolds (s.toSROIQDInterpretation (Branch.label_support root)) y d
  dataAll : ∀ (x : {n : Nat // n ∈ s.support}) dp d,
    (x.val, .dataAll dp d) ∈ s.labels →
    ∀ y, (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y →
      dataHolds (s.toSROIQDInterpretation (Branch.label_support root)) y d
  dataValuePos : ∀ (x : {n : Nat // n ∈ s.support}) dp l,
    (x.val, .dataValue dp l true) ∈ s.labels →
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x
      ((s.toSROIQDInterpretation (Branch.label_support root)).literalValue l)
  dataValueNeg : ∀ (x : {n : Nat // n ∈ s.support}) dp l,
    (x.val, .dataValue dp l false) ∈ s.labels →
    ¬ (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x
      ((s.toSROIQDInterpretation (Branch.label_support root)).literalValue l)
  dataMin : ∀ (x : {n : Nat // n ∈ s.support}) n dp d,
    (x.val, .dataMin n dp d) ∈ s.labels →
    AtLeast n (fun y => (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y ∧
      dataHolds (s.toSROIQDInterpretation (Branch.label_support root)) y d)
  dataMax : ∀ (x : {n : Nat // n ∈ s.support}) n dp d,
    (x.val, .dataMax n dp d) ∈ s.labels →
    ¬ AtLeast (n + 1) (fun y => (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y ∧
      dataHolds (s.toSROIQDInterpretation (Branch.label_support root)) y d)
  rules : ∀ r t, (r, t) ∈ p.rules → ∀ x y, s.edge r x y = true → s.edge t x y = true
  chains : ∀ c ∈ p.chains, ∀ x y,
    objPath (s.toSROIQDInterpretation (Branch.label_support root)) c.body x y →
    (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties c.head x y
  reflexive : ∀ r ∈ p.chars.reflexive, ∀ x,
    (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties r x x
  irreflexive : ∀ r ∈ p.chars.irreflexive, ∀ x,
    ¬ (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties r x x
  asymmetric : ∀ r ∈ p.chars.asymmetric, ∀ x y,
    (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties r x y →
    ¬ (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties r y x
  disjoint : ∀ rs ∈ p.chars.disjoint, ∀ x y,
    ¬ (holdsOriented (s.toSROIQDInterpretation (Branch.label_support root)) rs.1 x y ∧
       holdsOriented (s.toSROIQDInterpretation (Branch.label_support root)) rs.2 x y)
  subData : ∀ rs ∈ p.subData, ∀ x y,
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties rs.1 x y →
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties rs.2 x y
  disjointData : ∀ rs ∈ p.disjointData, ∀ x y,
    ¬ ((s.toSROIQDInterpretation (Branch.label_support root)).dataProperties rs.1 x y ∧
       (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties rs.2 x y)
  funcData : ∀ dp ∈ p.funcData, ∀ x y1 y2,
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y1 →
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x y2 → y1 = y2
  dataRanges : ∀ dr ∈ p.dataRanges, ∀ x y,
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dr.1 x y →
    dataHolds (s.toSROIQDInterpretation (Branch.label_support root)) y dr.2
  keys : ∀ k ∈ p.keys, ∀ x y,
    holds (s.toSROIQDInterpretation (Branch.label_support root)) x k.cls →
    holds (s.toSROIQDInterpretation (Branch.label_support root)) y k.cls →
    (s.toSROIQDInterpretation (Branch.label_support root)).named x →
    (s.toSROIQDInterpretation (Branch.label_support root)).named y →
    (∀ r ∈ k.objProps, ∃ z, (s.toSROIQDInterpretation (Branch.label_support root)).named z ∧
      holdsOriented (s.toSROIQDInterpretation (Branch.label_support root)) r x z ∧
      holdsOriented (s.toSROIQDInterpretation (Branch.label_support root)) r y z) →
    (∀ dp ∈ k.dataProps, ∃ z,
      (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp x z ∧
      (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties dp y z) →
    x = y
  tbox : ∀ q ∈ p.tbox, ∀ x ∈ s.support, (x, q.sub.dual) ∈ s.labels ∨ (x, q.sup) ∈ s.labels
  classAssertions : ∀ ac ∈ p.classAssertions,
    ((s.indNode (Branch.label_support root) ac.1).val, ac.2) ∈ s.labels
  objAssertions : ∀ rab ∈ p.objAssertions,
    (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties rab.1
      (s.indNode (Branch.label_support root) rab.2.1)
      (s.indNode (Branch.label_support root) rab.2.2)
  negObjAssertions : ∀ rab ∈ p.negObjAssertions,
    ¬ (s.toSROIQDInterpretation (Branch.label_support root)).objectProperties rab.1
      (s.indNode (Branch.label_support root) rab.2.1)
      (s.indNode (Branch.label_support root) rab.2.2)
  sameInds : ∀ ab ∈ p.sameInds,
    s.indNode (Branch.label_support root) ab.1 = s.indNode (Branch.label_support root) ab.2
  diffInds : ∀ ab ∈ p.diffInds,
    s.indNode (Branch.label_support root) ab.1 ≠ s.indNode (Branch.label_support root) ab.2
  dataAssertions : ∀ ral ∈ p.dataAssertions,
    (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties ral.1
      (s.indNode (Branch.label_support root) ral.2.1)
      ((s.toSROIQDInterpretation (Branch.label_support root)).literalValue ral.2.2)
  negDataAssertions : ∀ ral ∈ p.negDataAssertions,
    ¬ (s.toSROIQDInterpretation (Branch.label_support root)).dataProperties ral.1
      (s.indNode (Branch.label_support root) ral.2.1)
      ((s.toSROIQDInterpretation (Branch.label_support root)).literalValue ral.2.2)

/-- Simultaneous positive and dual Truth Lemma across all 16 `SROIQ(D)` concept
    constructors for an open (`CoreClashFree`), saturated (`SROIQDSaturated`)
    tableau branch `s`. -/
theorem sroiqd_saturated_holds_pair {p : Problem} {s : Branch}
    (hcf : s.CoreClashFree) (hsat : s.SROIQDSaturated p)
    {c : Concept} (hord : c.isOrdinary = true) :
    (∀ x : {n : Nat // n ∈ s.support},
      (x.val, c) ∈ s.labels →
      holds (s.toSROIQDInterpretation (Branch.label_support hsat.root)) x c) ∧
    (∀ x : {n : Nat // n ∈ s.support},
      (x.val, c.dual) ∈ s.labels →
      ¬ holds (s.toSROIQDInterpretation (Branch.label_support hsat.root)) x c) := by
  let h0 := Branch.label_support hsat.root
  let i := s.toSROIQDInterpretation h0
  induction c with
  | top =>
    exact ⟨fun _ _ => trivial, fun x hl _ => hcf.noBottom x.val hl⟩
  | bottom =>
    exact ⟨fun x hl => False.elim (hcf.noBottom x.val hl), fun _ _ h => h⟩
  | lit name sign =>
    simp only [Concept.isOrdinary] at hord
    have ⟨hne1, hne2⟩ := coreClassIRI_ne hord
    cases sign with
    | true =>
      refine ⟨fun x hl => ?_, fun x hl hpos => ?_⟩
      · simp only [holds, hne1, hne2, ↓reduceIte]; exact hl
      · simp only [holds, hne1, hne2, ↓reduceIte] at hpos
        exact hcf.noLitClash x.val name hpos hl
    | false =>
      refine ⟨fun x hl hpos => ?_, fun x hl hneg => ?_⟩
      · simp only [hne1, hne2, ↓reduceIte] at hpos
        exact hcf.noLitClash x.val name hpos hl
      · apply hneg
        simp only [hne1, hne2, ↓reduceIte]; exact hl
  | nom ind sign =>
    cases sign with
    | true =>
      exact ⟨fun x hl => hsat.nomPos x ind hl, fun x hl hpos => hsat.nomNeg x ind hl hpos⟩
    | false =>
      exact ⟨fun x hl => hsat.nomNeg x ind hl, fun x hl hneg => hneg (hsat.nomPos x ind hl)⟩
  | self r sign =>
    simp only [Concept.isOrdinary] at hord
    cases sign with
    | true =>
      refine ⟨fun x hl => ?_, fun x hl hpos => ?_⟩
      · exact (holdsOriented_toSROIQDInterpretation s h0 hord x x).mpr (hsat.selfPos x.val r hl)
      · have he := (holdsOriented_toSROIQDInterpretation s h0 hord x x).mp hpos
        rw [hsat.selfNeg x.val r hl] at he; cases he
    | false =>
      refine ⟨fun x hl hpos => ?_, fun x hl hneg => ?_⟩
      · have he := (holdsOriented_toSROIQDInterpretation s h0 hord x x).mp hpos
        rw [hsat.selfNeg x.val r hl] at he; cases he
      · exact hneg ((holdsOriented_toSROIQDInterpretation s h0 hord x x).mpr (hsat.selfPos x.val r hl))
  | conj a b iha ihb =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨ha1, ha2⟩ := iha hord.1
    have ⟨hb1, hb2⟩ := ihb hord.2
    refine ⟨fun x hl => ?_, fun x hl ⟨ha, hb⟩ => ?_⟩
    · obtain ⟨hla, hlb⟩ := hsat.conj x.val a b hl
      exact ⟨ha1 x hla, hb1 x hlb⟩
    · rcases hsat.disj x.val a.dual b.dual hl with hla | hlb
      · exact ha2 x hla ha
      · exact hb2 x hlb hb
  | disj a b iha ihb =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨ha1, ha2⟩ := iha hord.1
    have ⟨hb1, hb2⟩ := ihb hord.2
    refine ⟨fun x hl => ?_, fun x hl hdisj => ?_⟩
    · rcases hsat.disj x.val a b hl with hla | hlb
      · exact Or.inl (ha1 x hla)
      · exact Or.inr (hb1 x hlb)
    · obtain ⟨hla, hlb⟩ := hsat.conj x.val a.dual b.dual hl
      rcases hdisj with ha | hb
      · exact ha2 x hla ha
      · exact hb2 x hlb hb
  | some r body ih =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨hb1, hb2⟩ := ih hord.2
    refine ⟨fun x hl => ?_, fun x hl ⟨y, hxy, hy⟩ => ?_⟩
    · obtain ⟨y, hedge, hly⟩ := hsat.some x.val r body hl
      have hy : y ∈ s.support := Branch.label_support hly
      exact ⟨⟨y, hy⟩,
        (holdsOriented_toSROIQDInterpretation s h0 hord.1 x ⟨y, hy⟩).mpr hedge,
        hb1 ⟨y, hy⟩ hly⟩
    · have hedge := (holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mp hxy
      exact hb2 y (hsat.all x.val r body.dual hl y.val hedge) hy
  | all r body ih =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨hb1, hb2⟩ := ih hord.2
    refine ⟨fun x hl y hxy => ?_, fun x hl hall => ?_⟩
    · have hedge := (holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mp hxy
      exact hb1 y (hsat.all x.val r body hl y.val hedge)
    · obtain ⟨y, hedge, hly⟩ := hsat.some x.val r body.dual hl
      have hy : y ∈ s.support := Branch.label_support hly
      have hxy := (holdsOriented_toSROIQDInterpretation s h0 hord.1 x ⟨y, hy⟩).mpr hedge
      exact hb2 ⟨y, hy⟩ hly (hall ⟨y, hy⟩ hxy)
  | min n r body ih =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨hb1, hb2⟩ := ih hord.2
    refine ⟨fun x hl => ?_, fun x hl hmin => ?_⟩
    · obtain ⟨ys, hlen, hnd, hq⟩ := hsat.min x n r body hl
      refine ⟨ys, hlen, hnd, fun y hy => ?_⟩
      have ⟨he, hly⟩ := hq y hy
      exact ⟨(holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mpr he, hb1 y hly⟩
    · cases n with
      | zero =>
        obtain ⟨hbot, _⟩ := hsat.conj x.val .bottom (.min 0 r body) hl
        exact hcf.noBottom x.val hbot
      | succ m =>
        obtain ⟨ys, hlen, hnd, hq⟩ := hmin
        apply hsat.maxBound x m r body hl
        refine ⟨ys, hlen, hnd, fun y hy => ?_⟩
        have ⟨hxy, hyb⟩ := hq y hy
        have hedge := (holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mp hxy
        rcases hsat.maxQual x y m r body hl hedge with hly | hldual
        · exact ⟨hedge, hly⟩
        · exact False.elim (hb2 y hldual hyb)
  | max n r body ih =>
    simp only [Concept.isOrdinary, Bool.and_eq_true] at hord
    have ⟨hb1, hb2⟩ := ih hord.2
    refine ⟨fun x hl ⟨ys, hlen, hnd, hq⟩ => ?_, fun x hl hmax => ?_⟩
    · apply hsat.maxBound x n r body hl
      refine ⟨ys, hlen, hnd, fun y hy => ?_⟩
      have ⟨hxy, hyb⟩ := hq y hy
      have hedge := (holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mp hxy
      rcases hsat.maxQual x y n r body hl hedge with hly | hldual
      · exact ⟨hedge, hly⟩
      · exact False.elim (hb2 y hldual hyb)
    · obtain ⟨ys, hlen, hnd, hq⟩ := hsat.min x (n + 1) r body hl
      apply hmax
      refine ⟨ys, hlen, hnd, fun y hy => ?_⟩
      have ⟨he, hly⟩ := hq y hy
      exact ⟨(holdsOriented_toSROIQDInterpretation s h0 hord.1 x y).mpr he, hb1 y hly⟩
  | dataSome dp d =>
    refine ⟨fun x hl => hsat.dataSome x dp d hl, fun x hl ⟨y, hxy, hyd⟩ => ?_⟩
    exact hsat.dataAll x dp (.complement d) hl y hxy hyd
  | dataAll dp d =>
    refine ⟨fun x hl => hsat.dataAll x dp d hl, fun x hl hall => ?_⟩
    obtain ⟨y, hxy, hnot⟩ := hsat.dataSome x dp (.complement d) hl
    exact hnot (hall y hxy)
  | dataValue dp l sign =>
    cases sign with
    | true =>
      exact ⟨fun x hl => hsat.dataValuePos x dp l hl,
             fun x hl hpos => hsat.dataValueNeg x dp l hl hpos⟩
    | false =>
      exact ⟨fun x hl => hsat.dataValueNeg x dp l hl,
             fun x hl hneg => hneg (hsat.dataValuePos x dp l hl)⟩
  | dataMin n dp d =>
    refine ⟨fun x hl => hsat.dataMin x n dp d hl, fun x hl hmin => ?_⟩
    cases n with
    | zero =>
      obtain ⟨hbot, _⟩ := hsat.conj x.val .bottom (.dataMin 0 dp d) hl
      exact hcf.noBottom x.val hbot
    | succ m =>
      exact hsat.dataMax x m dp d hl hmin
  | dataMax n dp d =>
    refine ⟨fun x hl => hsat.dataMax x n dp d hl,
            fun x hl hmax => hmax (hsat.dataMin x (n + 1) dp d hl)⟩

/-- Positive Truth Lemma across all 16 `SROIQ(D)` concept constructors. -/
theorem sroiqd_saturated_holds {p : Problem} {s : Branch}
    (hcf : s.CoreClashFree) (hsat : s.SROIQDSaturated p)
    (x : {n : Nat // n ∈ s.support}) {c : Concept}
    (hord : c.isOrdinary = true) (hl : (x.val, c) ∈ s.labels) :
    holds (s.toSROIQDInterpretation (Branch.label_support hsat.root)) x c :=
  (sroiqd_saturated_holds_pair hcf hsat hord).1 x hl

/-- Full `SROIQ(D)` Model Construction Theorem (M5 / M6 / M7 / M8):
    every open (`CoreClashFree`), saturated (`SROIQDSaturated`) tableau branch
    for an ordinary `SROIQ(D)` problem `p` constructs a genuine OWL 2 Direct
    Semantics model of `p`. -/
theorem sroiqd_saturated_sat {p : Problem} {s : Branch}
    (hp : p.isOrdinary = true) (hcf : s.CoreClashFree) (hsat : s.SROIQDSaturated p) :
    p.Sat := by
  simp only [Problem.isOrdinary, Bool.and_eq_true, List.all_eq_true] at hp
  rcases hp with ⟨⟨⟨hrootO, htboxO⟩, hrulesO⟩, hcaO⟩
  let h0 : 0 ∈ s.support := Branch.label_support hsat.root
  let i := s.toSROIQDInterpretation h0
  refine ⟨i, ⟨?_, ?_, hsat.chains, hsat.reflexive, hsat.irreflexive, hsat.asymmetric,
    hsat.disjoint, hsat.subData, hsat.disjointData, hsat.funcData, hsat.dataRanges,
    hsat.keys, ?_, hsat.objAssertions, hsat.negObjAssertions, hsat.sameInds,
    hsat.diffInds, hsat.dataAssertions, hsat.negDataAssertions⟩,
    ⟨0, h0⟩, sroiqd_saturated_holds hcf hsat ⟨0, h0⟩ hrootO hsat.root⟩
  · -- tbox
    intro q hq x hsub
    have ⟨hsubO, hsupO⟩ := htboxO q hq
    rcases hsat.tbox q hq x.val x.property with hdual | hsup
    · exact False.elim ((sroiqd_saturated_holds_pair hcf hsat hsubO).2 x hdual hsub)
    · exact sroiqd_saturated_holds hcf hsat x hsupO hsup
  · -- rules
    intro ⟨r, t⟩ hrt x y hxy
    have ⟨hrO, htO⟩ := hrulesO (r, t) hrt
    have hedge := (holdsOriented_toSROIQDInterpretation s h0 hrO x y).mp hxy
    exact (holdsOriented_toSROIQDInterpretation s h0 htO x y).mpr
      (hsat.rules r t hrt x.val y.val hedge)
  · -- classAssertions
    intro ⟨a, c⟩ hac
    exact sroiqd_saturated_holds hcf hsat (s.indNode h0 a) (hcaO (a, c) hac)
      (hsat.classAssertions (a, c) hac)

/-- Budget-independent inductive tableau derivation tree for full `SROIQ(D)`. -/
inductive SROIQDDerivation (p : Problem) : Branch → Prop where
  | step {s : Branch} (t : Transition p s) :
      (∀ b ∈ t.branches, SROIQDDerivation p b) → SROIQDDerivation p s
  | saturated {s : Branch} :
      s.CoreClashFree → s.SROIQDSaturated p → SROIQDDerivation p s

/-- Complete model-or-refutation dichotomy for any budget-independent full
    `SROIQ(D)` tableau derivation. -/
theorem sroiqdDerivation_dichotomy {p : Problem} {s : Branch}
    (hp : p.isOrdinary = true) (hd : SROIQDDerivation p s) :
    p.Sat ∨ CoreRefutation p s := by
  induction hd with
  | saturated hcf hsat =>
    exact Or.inl (sroiqd_saturated_sat hp hcf hsat)
  | step t _ ih =>
    by_cases hsat : p.Sat
    · exact Or.inl hsat
    · exact Or.inr (.step t fun b hb => (ih b hb).resolve_left hsat)

/-- Refutation completeness for the full `SROIQ(D)` tableau calculus (M8):
    every unsatisfiable `SROIQ(D)` problem (`¬ p.Sat`) with a saturated
    tableau derivation from `s` produces a closed finite refutation tree
    `CoreRefutation p s`. -/
theorem sroiqdDerivation_refutation_complete {p : Problem} {s : Branch}
    (hp : p.isOrdinary = true) (hd : SROIQDDerivation p s) (hunsat : ¬ p.Sat) :
    CoreRefutation p s :=
  (sroiqdDerivation_dichotomy hp hd).resolve_left hunsat

/-- Exact equivalence between unsatisfiability (`¬ p.Sat`) and existence of a
    closed tableau refutation from the initial branch of a full `SROIQ(D)` problem. -/
theorem sroiqdDerivation_unsat_iff_refutation {p : Problem} {s0 : Branch}
    (hp : p.isOrdinary = true) (hinit : initial p = some s0) (hd : SROIQDDerivation p s0) :
    ¬ p.Sat ↔ CoreRefutation p s0 :=
  ⟨sroiqdDerivation_refutation_complete hp hd,
   fun href hsat => coreRefutation_sound href (initial_sat hinit hsat)⟩

end Sabrina.OWL2.SROIQD
