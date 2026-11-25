import Sabrina.OWL2.SROIQD.Termination.ChainAliases
import Sabrina.OWL2.SROIQD.Termination.TopChainNormalization

/-! Verified elimination of universal-role restrictions `∃ owl:topObjectProperty.C`
and `∀ owl:topObjectProperty.C` (including nested occurrences and the inverse
`(owl:topObjectProperty)⁻`) from normalized `SROIQ(D)` problems.

Each innermost universal-role restriction is branched exhaustively over its global
truth value across the entire object domain and replaced by `⊤` or `⊥`:
- `∃ U.C = true`  adds `⊤ ⊑ ∃w.C` for a provably fresh ordinary role `w`,
- `∃ U.C = false` adds `C ⊑ ⊥`,
- `∀ U.C = true`  adds `⊤ ⊑ C`,
- `∀ U.C = false` adds `⊤ ⊑ ∃w.C.dual` for a provably fresh ordinary role `w`.

Expanding a model with a fresh universal role `w` leaves every existing class,
relation, datatype, and named individual (`i.named` / `i.individuals`) intact,
preserving `HasKey` semantics and all other axioms. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank checkRegular findRank)

/-! ### 1. Universal-role semantics and innermost-first concept replacement -/

private theorem topRole_holds (i : Interpretation datatypeMap)
    (r : OrientedRole) (hr : r.1 = topObjectProperty) (x y : i.Object) :
    holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩
  · change i.objectProperties name x y
    rw [show name = topObjectProperty from hr]
    exact i.topObjectExt x y
  · change i.objectProperties name y x
    rw [show name = topObjectProperty from hr]
    exact i.topObjectExt y x

def boolConcept (b : Bool) : Concept :=
  if b then .top else .bottom

private theorem holds_boolConcept (i : Interpretation datatypeMap) (x : i.Object) (b : Bool) :
    holds i x (boolConcept b) ↔ b = true := by
  cases b <;> simp [boolConcept, holds]

def topRestrictHolds (i : Interpretation datatypeMap) (isSome : Bool) (target : Concept) : Prop :=
  if isSome then ∃ y, holds i y target else ∀ y, holds i y target

private def orOpt {α : Type} : Option α → Option α → Option α
  | Option.some x, _ => Option.some x
  | none, b => b

private theorem orOpt_eq_none {α : Type} {a b : Option α} :
    orOpt a b = none ↔ a = none ∧ b = none := by
  cases a <;> simp [orOpt]

private theorem orOpt_eq_some {α : Type} {a b : Option α} {x : α} :
    orOpt a b = Option.some x ↔ a = Option.some x ∨ (a = none ∧ b = Option.some x) := by
  cases a <;> simp [orOpt]

def Concept.topRestrictCount : Concept → Nat
  | .conj a b | .disj a b => a.topRestrictCount + b.topRestrictCount
  | .some r c | .all r c =>
    (if r.1 == topObjectProperty then 1 else 0) + c.topRestrictCount
  | .min _ _ c | .max _ _ c => c.topRestrictCount
  | _ => 0

theorem Concept.topRestrictCount_dual (c : Concept) :
    c.dual.topRestrictCount = c.topRestrictCount := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.topRestrictCount]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.topRestrictCount]
  | _ => simp_all [Concept.dual, Concept.topRestrictCount]

/-- Locate an innermost universal-role restriction `(isSome, filler)` inside a concept.
Because recursion descends into fillers before matching an outer restriction, any
returned `filler` satisfies `filler.topRestrictCount = 0`. -/
def Concept.findInnermostTop : Concept → Option (Bool × Concept)
  | .conj a b | .disj a b => orOpt a.findInnermostTop b.findInnermostTop
  | .some r c =>
    orOpt c.findInnermostTop (if r.1 == topObjectProperty then Option.some (true, c) else none)
  | .all r c =>
    orOpt c.findInnermostTop (if r.1 == topObjectProperty then Option.some (false, c) else none)
  | .min _ _ c | .max _ _ c => c.findInnermostTop
  | _ => none

theorem Concept.findInnermostTop_none_iff (c : Concept) :
    c.findInnermostTop = none ↔ c.topRestrictCount = 0 := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop, Concept.topRestrictCount]
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.findInnermostTop, Concept.topRestrictCount, orOpt_eq_none,
      Nat.add_eq_zero_iff, iha, ihb]
  | some r c ih | all r c ih =>
    simp only [Concept.findInnermostTop, Concept.topRestrictCount, orOpt_eq_none, ih]
    by_cases hr : r.1 == topObjectProperty <;> simp [hr]
  | min n r c ih | max n r c ih =>
    simpa [Concept.findInnermostTop, Concept.topRestrictCount] using ih

theorem Concept.findInnermostTop_target_zero {c : Concept} {isSome : Bool} {target : Concept}
    (h : c.findInnermostTop = Option.some (isSome, target)) :
    target.topRestrictCount = 0 := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop] at h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    rcases h with ha | ⟨_, hb⟩
    · exact iha ha
    · exact ihb hb
  | some r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    rcases h with hc | ⟨hnone, hself⟩
    · exact ih hc
    · by_cases hr : r.1 == topObjectProperty
      · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
        rw [← hself.2]
        exact (Concept.findInnermostTop_none_iff c).mp hnone
      · simp [hr] at hself
  | all r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    rcases h with hc | ⟨hnone, hself⟩
    · exact ih hc
    · by_cases hr : r.1 == topObjectProperty
      · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
        rw [← hself.2]
        exact (Concept.findInnermostTop_none_iff c).mp hnone
      · simp [hr] at hself
  | min n r c ih | max n r c ih =>
    exact ih h

/-- Replace every occurrence of the universal-role restriction `(isSome, target)`
(in either forward or inverse orientation) with `boolConcept val`. -/
def Concept.replaceTop : Concept → Bool → Concept → Bool → Concept
  | .conj a b, isSome, target, val =>
    .conj (a.replaceTop isSome target val) (b.replaceTop isSome target val)
  | .disj a b, isSome, target, val =>
    .disj (a.replaceTop isSome target val) (b.replaceTop isSome target val)
  | .some r c, isSome, target, val =>
    if r.1 == topObjectProperty && isSome && c == target then boolConcept val
    else .some r (c.replaceTop isSome target val)
  | .all r c, isSome, target, val =>
    if r.1 == topObjectProperty && !isSome && c == target then boolConcept val
    else .all r (c.replaceTop isSome target val)
  | .min n r c, isSome, target, val => .min n r (c.replaceTop isSome target val)
  | .max n r c, isSome, target, val => .max n r (c.replaceTop isSome target val)
  | c, _, _, _ => c

private theorem atLeast_congr {α : Type} {p q : α → Prop} (h : ∀ x, p x ↔ q x) (n : Nat) :
    AtLeast n p ↔ AtLeast n q := by
  simp only [AtLeast, h]

theorem holds_replaceTop_iff (i : Interpretation datatypeMap)
    {isSome : Bool} {target : Concept} {val : Bool}
    (htruth : topRestrictHolds i isSome target ↔ val = true)
    (x : i.Object) (c : Concept) :
    holds i x (c.replaceTop isSome target val) ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => rfl
  | conj a b iha ihb => exact and_congr (iha x) (ihb x)
  | disj a b iha ihb => exact or_congr (iha x) (ihb x)
  | some r c ih =>
    unfold Concept.replaceTop
    split
    · rename_i hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨hr, his⟩, hc⟩ := hm
      subst his; subst hc
      rw [holds_boolConcept, ← htruth]
      simp only [topRestrictHolds, ↓reduceIte, holds]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, topRole_holds i r hr x y, hy⟩,
             fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩
    · simp only [holds]
      exact exists_congr fun y => and_congr Iff.rfl (ih y)
  | all r c ih =>
    unfold Concept.replaceTop
    split
    · rename_i hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
      obtain ⟨⟨hr, his⟩, hc⟩ := hm
      subst his; subst hc
      rw [holds_boolConcept, ← htruth]
      simp only [topRestrictHolds, Bool.false_eq_true, ↓reduceIte, holds]
      exact ⟨fun hall y _ => hall y, fun hall y => hall y (topRole_holds i r hr x y)⟩
    · simp only [holds]
      exact forall_congr' fun y => imp_congr Iff.rfl (ih y)
  | min n r c ih =>
    simpa only [Concept.replaceTop, holds] using
      atLeast_congr (fun y => and_congr Iff.rfl (ih y)) n
  | max n r c ih =>
    simpa only [Concept.replaceTop, holds] using
      not_congr (atLeast_congr (fun y => and_congr Iff.rfl (ih y)) (n + 1))

private theorem topRestrictCount_boolConcept (b : Bool) :
    (boolConcept b).topRestrictCount = 0 := by
  cases b <;> rfl

theorem Concept.topRestrictCount_replaceTop_le (isSome : Bool) (target : Concept)
    (val : Bool) (c : Concept) :
    (c.replaceTop isSome target val).topRestrictCount ≤ c.topRestrictCount := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    exact Nat.le_refl 0
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.replaceTop, Concept.topRestrictCount]
    exact Nat.add_le_add iha ihb
  | some r c ih | all r c ih =>
    unfold Concept.replaceTop
    split
    · rw [topRestrictCount_boolConcept]; exact Nat.zero_le _
    · simp only [Concept.topRestrictCount]
      exact Nat.add_le_add_left ih _
  | min n r c ih | max n r c ih =>
    exact ih

theorem Concept.topRestrictCount_replaceTop_lt_of_find {c : Concept}
    {isSome : Bool} {target : Concept} (val : Bool)
    (h : c.findInnermostTop = Option.some (isSome, target)) :
    (c.replaceTop isSome target val).topRestrictCount < c.topRestrictCount := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop] at h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    simp only [Concept.replaceTop, Concept.topRestrictCount]
    rcases h with ha | ⟨_, hb⟩
    · exact Nat.add_lt_add_of_lt_of_le (iha ha)
        (Concept.topRestrictCount_replaceTop_le isSome target val b)
    · exact Nat.add_lt_add_of_le_of_lt
        (Concept.topRestrictCount_replaceTop_le isSome target val a) (ihb hb)
  | some r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    unfold Concept.replaceTop
    split
    · rw [topRestrictCount_boolConcept]
      rename_i hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      simp only [Concept.topRestrictCount, hm.1.1, beq_self_eq_true, ↓reduceIte]
      omega
    · rename_i hnm
      rcases h with hc | ⟨_, hself⟩
      · simp only [Concept.topRestrictCount]
        exact Nat.add_lt_add_left (ih hc) _
      · by_cases hr : r.1 == topObjectProperty
        · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
          have hcond : (r.1 == topObjectProperty && isSome && c == target) = true := by
            simp [hr, ← hself.1, ← hself.2]
          exact (hnm hcond).elim
        · simp [hr] at hself
  | all r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    unfold Concept.replaceTop
    split
    · rw [topRestrictCount_boolConcept]
      rename_i hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
      simp only [Concept.topRestrictCount, hm.1.1, beq_self_eq_true, ↓reduceIte]
      omega
    · rename_i hnm
      rcases h with hc | ⟨_, hself⟩
      · simp only [Concept.topRestrictCount]
        exact Nat.add_lt_add_left (ih hc) _
      · by_cases hr : r.1 == topObjectProperty
        · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
          have hcond : (r.1 == topObjectProperty && !isSome && c == target) = true := by
            simp [hr, ← hself.1, ← hself.2]
          exact (hnm hcond).elim
        · simp [hr] at hself
  | min n r c ih | max n r c ih =>
    exact ih h

/-! ### 2. Object property inventory, fresh role construction, and model expansion -/

def Concept.objProps : Concept → List IRI
  | .self r _ => [r.1]
  | .conj a b | .disj a b => a.objProps ++ b.objProps
  | .some r c | .all r c | .min _ r c | .max _ r c => r.1 :: c.objProps
  | _ => []

theorem Concept.objProps_dual (c : Concept) : c.dual.objProps = c.objProps := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.objProps]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.objProps]
  | _ => simp_all [Concept.dual, Concept.objProps]

theorem Concept.objProps_replaceTop_subset (isSome : Bool) (target : Concept)
    (val : Bool) (c : Concept) :
    ∀ r ∈ (c.replaceTop isSome target val).objProps, r ∈ c.objProps := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    intro r hr; exact hr
  | conj a b iha ihb | disj a b iha ihb =>
    intro r hr
    simp only [Concept.replaceTop, Concept.objProps, List.mem_append] at hr ⊢
    exact hr.elim (Or.inl ∘ iha r) (Or.inr ∘ ihb r)
  | some r c ih | all r c ih =>
    intro s hs
    unfold Concept.replaceTop at hs
    split at hs
    · cases val <;> simp [boolConcept, Concept.objProps] at hs
    · simp only [Concept.objProps, List.mem_cons] at hs ⊢
      exact hs.elim Or.inl (Or.inr ∘ ih s)
  | min n r c ih | max n r c ih =>
    intro s hs
    simp only [Concept.replaceTop, Concept.objProps, List.mem_cons] at hs ⊢
    exact hs.elim Or.inl (Or.inr ∘ ih s)

theorem Concept.findInnermostTop_objProps_subset {c : Concept}
    {isSome : Bool} {target : Concept}
    (h : c.findInnermostTop = Option.some (isSome, target)) :
    ∀ r ∈ target.objProps, r ∈ c.objProps := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop] at h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    intro r hr
    simp only [Concept.objProps, List.mem_append]
    rcases h with ha | ⟨_, hb⟩
    · exact Or.inl (iha ha r hr)
    · exact Or.inr (ihb hb r hr)
  | some r c ih | all r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at h
    intro s hs
    simp only [Concept.objProps, List.mem_cons]
    rcases h with hc | ⟨_, hself⟩
    · exact Or.inr (ih hc s hs)
    · by_cases hr : r.1 == topObjectProperty
      · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
        exact Or.inr (hself.2 ▸ hs)
      · simp [hr] at hself
  | min n r c ih | max n r c ih =>
    intro s hs
    simp only [Concept.objProps, List.mem_cons]
    exact Or.inr (ih h s hs)

def Problem.objProps (p : Problem) : List IRI :=
  p.root.objProps ++
  p.tbox.flatMap (fun q => q.sub.objProps ++ q.sup.objProps) ++
  p.rules.flatMap (fun rs => [rs.1.1, rs.2.1]) ++
  p.chains.flatMap (fun c => c.head :: c.body.map Prod.fst) ++
  p.chars.reflexive ++
  p.chars.irreflexive ++
  p.chars.asymmetric ++
  p.chars.disjoint.flatMap (fun rs => [rs.1.1, rs.2.1]) ++
  p.keys.flatMap (fun k => k.cls.objProps ++ k.objProps.map Prod.fst) ++
  p.classAssertions.flatMap (fun ac => ac.2.objProps) ++
  p.objAssertions.map (fun rab => rab.1) ++
  p.negObjAssertions.map (fun rab => rab.1)

private def maxStrLen : List String → Nat
  | [] => 0
  | s :: ss => max s.length (maxStrLen ss)

private theorem length_le_maxStrLen {s : String} {ss : List String} (h : s ∈ ss) :
    s.length ≤ maxStrLen ss := by
  induction ss with
  | nil => cases h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

private def padX : Nat → String → String
  | 0, acc => acc
  | n + 1, acc => padX n (acc.push 'x')

private theorem padX_length (n : Nat) (acc : String) :
    (padX n acc).length = acc.length + n := by
  induction n generalizing acc with
  | zero => simp [padX]
  | succ n ih =>
    simp only [padX, ih, String.length_push]
    omega

/-- Construct an ordinary object-property IRI strictly longer than `topObjectProperty`,
`bottomObjectProperty`, and every object property appearing anywhere in `p`. -/
def freshObjProp (p : Problem) : IRI :=
  let forbidden := topObjectProperty :: bottomObjectProperty :: p.objProps
  padX (maxStrLen forbidden + 1) "urn:sabrina:univ:"

private theorem freshObjProp_not_mem_forbidden (p : Problem) :
    freshObjProp p ∉ topObjectProperty :: bottomObjectProperty :: p.objProps := by
  intro hmem
  have hle := length_le_maxStrLen hmem
  have hlen : (freshObjProp p).length =
      "urn:sabrina:univ:".length +
      (maxStrLen (topObjectProperty :: bottomObjectProperty :: p.objProps) + 1) :=
    padX_length _ _
  omega

theorem freshObjProp_ne_top (p : Problem) : freshObjProp p ≠ topObjectProperty := by
  intro h
  exact freshObjProp_not_mem_forbidden p (h ▸ List.mem_cons_self ..)

theorem freshObjProp_ne_bottom (p : Problem) : freshObjProp p ≠ bottomObjectProperty := by
  intro h
  exact freshObjProp_not_mem_forbidden p (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem freshObjProp_core (p : Problem) : isCoreObjPropIRI (freshObjProp p) = true := by
  simp [isCoreObjPropIRI, freshObjProp_ne_top p, freshObjProp_ne_bottom p]

theorem freshObjProp_not_mem (p : Problem) : freshObjProp p ∉ p.objProps := by
  intro h
  exact freshObjProp_not_mem_forbidden p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

/-- Expand an interpretation by making a fresh ordinary object property `w` universal
over `i.Object`. Every other relation, class, datatype, and named individual
(`i.named`, `i.individuals`) is preserved definitionally. -/
def withUniversalRole (i : Interpretation datatypeMap) (w : IRI)
    (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty) :
    Interpretation datatypeMap :=
  { i with
    objectProperties := fun r x y => if r = w then True else i.objectProperties r x y
    topObjectExt := fun x y => by simp [hnt.symm, i.topObjectExt x y]
    bottomObjectExt := fun x y => by simp [hnb.symm, i.bottomObjectExt x y] }

private theorem dataHolds_withUniversalRole_iff (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    (y : i.Data) (d : DataRange) :
    dataHolds (withUniversalRole i w hnt hnb) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ iha ihb => exact and_congr iha ihb
  | union _ _ iha ihb => exact or_congr iha ihb
  | oneOf _ => rfl
  | restriction _ _ => rfl

private theorem holdsOriented_withUniversalRole_ne (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    {r : OrientedRole} (hne : r.1 ≠ w) (x y : i.Object) :
    holdsOriented (withUniversalRole i w hnt hnb) r x y ↔ holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩ <;> simp [holdsOriented, withUniversalRole, hne]

private theorem holdsOriented_withUniversalRole_eq (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    (x y : i.Object) :
    holdsOriented (withUniversalRole i w hnt hnb) (w, false) x y := by
  simp [holdsOriented, withUniversalRole]

private theorem objPath_withUniversalRole_iff (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    {rs : List OrientedRole} (hfresh : ∀ r ∈ rs, r.1 ≠ w) (x y : i.Object) :
    objPath (withUniversalRole i w hnt hnb) rs x y ↔ objPath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    have hr : r.1 ≠ w := hfresh r (List.mem_cons_self ..)
    have hrs : ∀ s ∈ rs, s.1 ≠ w := fun s hs => hfresh s (List.mem_cons_of_mem _ hs)
    change (∃ z : i.Object, holdsOriented (withUniversalRole i w hnt hnb) r x z ∧
        objPath (withUniversalRole i w hnt hnb) rs z y) ↔
      ∃ z : i.Object, holdsOriented i r x z ∧ objPath i rs z y
    exact exists_congr fun z =>
      and_congr (holdsOriented_withUniversalRole_ne i hnt hnb hr x z) (ih hrs z)

theorem holds_withUniversalRole_iff (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    {c : Concept} (hfresh : w ∉ c.objProps) (x : i.Object) :
    holds (withUniversalRole i w hnt hnb) x c ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b => cases b <;> rfl
  | nom _ b => cases b <;> rfl
  | dataValue _ _ b => cases b <;> rfl
  | dataSome r d =>
    change (∃ y : i.Data, i.dataProperties r x y ∧ dataHolds (withUniversalRole i w hnt hnb) y d) ↔
      ∃ y : i.Data, i.dataProperties r x y ∧ dataHolds i y d
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withUniversalRole_iff i hnt hnb y d)
  | dataAll r d =>
    change (∀ y : i.Data, i.dataProperties r x y → dataHolds (withUniversalRole i w hnt hnb) y d) ↔
      ∀ y : i.Data, i.dataProperties r x y → dataHolds i y d
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withUniversalRole_iff i hnt hnb y d)
  | dataMin n r d =>
    change AtLeast n (fun y : i.Data => i.dataProperties r x y ∧ dataHolds (withUniversalRole i w hnt hnb) y d) ↔
      AtLeast n (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact atLeast_congr (fun y => and_congr Iff.rfl (dataHolds_withUniversalRole_iff i hnt hnb y d)) n
  | dataMax n r d =>
    change (¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧ dataHolds (withUniversalRole i w hnt hnb) y d)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact not_congr (atLeast_congr
      (fun y => and_congr Iff.rfl (dataHolds_withUniversalRole_iff i hnt hnb y d)) (n + 1))
  | self r b =>
    have hne : r.1 ≠ w := fun he => hfresh (by simp [Concept.objProps, he])
    cases b <;> simp [holds, holdsOriented_withUniversalRole_ne i hnt hnb hne]
  | conj a b iha ihb =>
    simp only [Concept.objProps, List.mem_append, not_or] at hfresh
    exact and_congr (iha hfresh.1 x) (ihb hfresh.2 x)
  | disj a b iha ihb =>
    simp only [Concept.objProps, List.mem_append, not_or] at hfresh
    exact or_congr (iha hfresh.1 x) (ihb hfresh.2 x)
  | some r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hfresh
    have hne : r.1 ≠ w := Ne.symm hfresh.1
    change (∃ y : i.Object, holdsOriented (withUniversalRole i w hnt hnb) r x y ∧
        holds (withUniversalRole i w hnt hnb) y c) ↔
      ∃ y : i.Object, holdsOriented i r x y ∧ holds i y c
    exact exists_congr fun y =>
      and_congr (holdsOriented_withUniversalRole_ne i hnt hnb hne x y) (ih hfresh.2 y)
  | all r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hfresh
    have hne : r.1 ≠ w := Ne.symm hfresh.1
    change (∀ y : i.Object, holdsOriented (withUniversalRole i w hnt hnb) r x y →
        holds (withUniversalRole i w hnt hnb) y c) ↔
      ∀ y : i.Object, holdsOriented i r x y → holds i y c
    exact forall_congr' fun y =>
      imp_congr (holdsOriented_withUniversalRole_ne i hnt hnb hne x y) (ih hfresh.2 y)
  | min n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hfresh
    have hne : r.1 ≠ w := Ne.symm hfresh.1
    change AtLeast n (fun y : i.Object => holdsOriented (withUniversalRole i w hnt hnb) r x y ∧
        holds (withUniversalRole i w hnt hnb) y c) ↔
      AtLeast n (fun y : i.Object => holdsOriented i r x y ∧ holds i y c)
    exact atLeast_congr
      (fun y => and_congr (holdsOriented_withUniversalRole_ne i hnt hnb hne x y) (ih hfresh.2 y)) n
  | max n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hfresh
    have hne : r.1 ≠ w := Ne.symm hfresh.1
    change (¬ AtLeast (n + 1) (fun y : i.Object => holdsOriented (withUniversalRole i w hnt hnb) r x y ∧
        holds (withUniversalRole i w hnt hnb) y c)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Object => holdsOriented i r x y ∧ holds i y c)
    exact not_congr (atLeast_congr
      (fun y => and_congr (holdsOriented_withUniversalRole_ne i hnt hnb hne x y) (ih hfresh.2 y)) (n + 1))

private theorem problem_objProps_parts {p : Problem} {w : IRI} (h : w ∉ p.objProps) :
    (w ∉ p.root.objProps) ∧
    (∀ q ∈ p.tbox, w ∉ q.sub.objProps ∧ w ∉ q.sup.objProps) ∧
    (∀ rs ∈ p.rules, rs.1.1 ≠ w ∧ rs.2.1 ≠ w) ∧
    (∀ c ∈ p.chains, c.head ≠ w ∧ ∀ r ∈ c.body, r.1 ≠ w) ∧
    (∀ r ∈ p.chars.reflexive, r ≠ w) ∧
    (∀ r ∈ p.chars.irreflexive, r ≠ w) ∧
    (∀ r ∈ p.chars.asymmetric, r ≠ w) ∧
    (∀ rs ∈ p.chars.disjoint, rs.1.1 ≠ w ∧ rs.2.1 ≠ w) ∧
    (∀ k ∈ p.keys, w ∉ k.cls.objProps ∧ ∀ r ∈ k.objProps, r.1 ≠ w) ∧
    (∀ ac ∈ p.classAssertions, w ∉ ac.2.objProps) ∧
    (∀ rab ∈ p.objAssertions, rab.1 ≠ w) ∧
    (∀ rab ∈ p.negObjAssertions, rab.1 ≠ w) := by
  simp only [Problem.objProps, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.1.1.1.1.1.1.1.1.1.1.1
  · intro q hq
    exact h.1.1.1.1.1.1.1.1.1.1.2 q hq
  · intro rs hrs
    have h1 := h.1.1.1.1.1.1.1.1.1.2 rs hrs
    exact ⟨Ne.symm h1.1, Ne.symm h1.2⟩
  · intro c hc
    have h1 := h.1.1.1.1.1.1.1.1.2 c hc
    exact ⟨Ne.symm h1.1, fun r hr => h1.2 r hr⟩
  · intro r hr he; exact h.1.1.1.1.1.1.1.2 (he ▸ hr)
  · intro r hr he; exact h.1.1.1.1.1.1.2 (he ▸ hr)
  · intro r hr he; exact h.1.1.1.1.1.2 (he ▸ hr)
  · intro rs hrs
    have h1 := h.1.1.1.1.2 rs hrs
    exact ⟨Ne.symm h1.1, Ne.symm h1.2⟩
  · intro k hk
    exact h.1.1.1.2 k hk
  · intro ac hac; exact h.1.1.2 ac hac
  · intro rab hrab; exact h.1.2 rab hrab
  · intro rab hrab; exact h.2 rab hrab

theorem models_withUniversalRole_iff (p : Problem) (i : Interpretation datatypeMap)
    {w : IRI} (hnt : w ≠ topObjectProperty) (hnb : w ≠ bottomObjectProperty)
    (hfresh : w ∉ p.objProps) :
    p.Models (withUniversalRole i w hnt hnb) ↔ p.Models i := by
  obtain ⟨_, htbox, hrules, hchains, hrefl, hirrefl, hasym, hdisj, hkeys, hca, hoa, hnoa⟩ :=
    problem_objProps_parts hfresh
  let j := withUniversalRole i w hnt hnb
  have hobj (r : IRI) (hne : r ≠ w) (x y : i.Object) :
      j.objectProperties r x y ↔ i.objectProperties r x y := by
    simp [j, withUniversalRole, hne]
  constructor
  · intro hm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
      ?_, ?_, ?_, ?_, ?_, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩
    · intro q hq x hx
      have ⟨hs1, hs2⟩ := htbox q hq
      exact (holds_withUniversalRole_iff i hnt hnb hs2 x).mp
        (hm.tbox q hq x ((holds_withUniversalRole_iff i hnt hnb hs1 x).mpr hx))
    · intro rs hrs x y hxy
      have ⟨h1, h2⟩ := hrules rs hrs
      exact (holdsOriented_withUniversalRole_ne i hnt hnb h2 x y).mp
        (hm.rules rs hrs x y ((holdsOriented_withUniversalRole_ne i hnt hnb h1 x y).mpr hxy))
    · intro c hc x y hp
      have ⟨hh, hb⟩ := hchains c hc
      exact (hobj c.head hh x y).mp
        (hm.chains c hc x y ((objPath_withUniversalRole_iff i hnt hnb hb x y).mpr hp))
    · intro r hr x; exact (hobj r (hrefl r hr) x x).mp (hm.reflexive r hr x)
    · intro r hr x h; exact hm.irreflexive r hr x ((hobj r (hirrefl r hr) x x).mpr h)
    · intro r hr x y h1 h2
      exact hm.asymmetric r hr x y ((hobj r (hasym r hr) x y).mpr h1)
        ((hobj r (hasym r hr) y x).mpr h2)
    · intro rs hrs x y ⟨h1, h2⟩
      have ⟨hn1, hn2⟩ := hdisj rs hrs
      exact hm.disjoint rs hrs x y
        ⟨(holdsOriented_withUniversalRole_ne i hnt hnb hn1 x y).mpr h1,
         (holdsOriented_withUniversalRole_ne i hnt hnb hn2 x y).mpr h2⟩
    · intro rd hrd x y hxy
      exact (dataHolds_withUniversalRole_iff i hnt hnb y rd.2).mp (hm.dataRanges rd hrd x y hxy)
    · intro k hk x y hx hy hnx hny ho hd
      have ⟨hcls, hkop⟩ := hkeys k hk
      refine hm.keys k hk x y
        ((holds_withUniversalRole_iff i hnt hnb hcls x).mpr hx)
        ((holds_withUniversalRole_iff i hnt hnb hcls y).mpr hy)
        hnx hny ?_ hd
      intro r hr
      obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
      exact ⟨z, hnz,
        (holdsOriented_withUniversalRole_ne i hnt hnb (hkop r hr) x z).mpr hxz,
        (holdsOriented_withUniversalRole_ne i hnt hnb (hkop r hr) y z).mpr hyz⟩
    · intro ac hac
      exact (holds_withUniversalRole_iff i hnt hnb (hca ac hac) _).mp (hm.classAssertions ac hac)
    · intro rab hrab
      exact (hobj rab.1 (hoa rab hrab) _ _).mp (hm.objAssertions rab hrab)
    · intro rab hrab h
      exact hm.negObjAssertions rab hrab ((hobj rab.1 (hnoa rab hrab) _ _).mpr h)
  · intro hm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
      ?_, ?_, ?_, ?_, ?_, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩
    · intro q hq x hx
      have ⟨hs1, hs2⟩ := htbox q hq
      exact (holds_withUniversalRole_iff i hnt hnb hs2 x).mpr
        (hm.tbox q hq x ((holds_withUniversalRole_iff i hnt hnb hs1 x).mp hx))
    · intro rs hrs x y hxy
      have ⟨h1, h2⟩ := hrules rs hrs
      exact (holdsOriented_withUniversalRole_ne i hnt hnb h2 x y).mpr
        (hm.rules rs hrs x y ((holdsOriented_withUniversalRole_ne i hnt hnb h1 x y).mp hxy))
    · intro c hc x y hp
      have ⟨hh, hb⟩ := hchains c hc
      exact (hobj c.head hh x y).mpr
        (hm.chains c hc x y ((objPath_withUniversalRole_iff i hnt hnb hb x y).mp hp))
    · intro r hr x; exact (hobj r (hrefl r hr) x x).mpr (hm.reflexive r hr x)
    · intro r hr x h; exact hm.irreflexive r hr x ((hobj r (hirrefl r hr) x x).mp h)
    · intro r hr x y h1 h2
      exact hm.asymmetric r hr x y ((hobj r (hasym r hr) x y).mp h1)
        ((hobj r (hasym r hr) y x).mp h2)
    · intro rs hrs x y ⟨h1, h2⟩
      have ⟨hn1, hn2⟩ := hdisj rs hrs
      exact hm.disjoint rs hrs x y
        ⟨(holdsOriented_withUniversalRole_ne i hnt hnb hn1 x y).mp h1,
         (holdsOriented_withUniversalRole_ne i hnt hnb hn2 x y).mp h2⟩
    · intro rd hrd x y hxy
      exact (dataHolds_withUniversalRole_iff i hnt hnb y rd.2).mpr (hm.dataRanges rd hrd x y hxy)
    · intro k hk x y hx hy hnx hny ho hd
      have ⟨hcls, hkop⟩ := hkeys k hk
      refine hm.keys k hk x y
        ((holds_withUniversalRole_iff i hnt hnb hcls x).mp hx)
        ((holds_withUniversalRole_iff i hnt hnb hcls y).mp hy)
        hnx hny ?_ hd
      intro r hr
      obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
      exact ⟨z, hnz,
        (holdsOriented_withUniversalRole_ne i hnt hnb (hkop r hr) x z).mp hxz,
        (holdsOriented_withUniversalRole_ne i hnt hnb (hkop r hr) y z).mp hyz⟩
    · intro ac hac
      exact (holds_withUniversalRole_iff i hnt hnb (hca ac hac) _).mpr (hm.classAssertions ac hac)
    · intro rab hrab
      exact (hobj rab.1 (hoa rab hrab) _ _).mpr (hm.objAssertions rab hrab)
    · intro rab hrab h
      exact hm.negObjAssertions rab hrab ((hobj rab.1 (hnoa rab hrab) _ _).mp h)

/-! ### 3. Problem-level innermost universal-role branching and termination -/

def Problem.topRestrictCount (p : Problem) : Nat :=
  p.root.topRestrictCount +
  (p.tbox.map fun q => q.sub.topRestrictCount + q.sup.topRestrictCount).sum +
  (p.keys.map fun k => k.cls.topRestrictCount).sum +
  (p.classAssertions.map fun ac => ac.2.topRestrictCount).sum

private def findFirst {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | a :: rest => orOpt (f a) (findFirst f rest)

private theorem findFirst_none_iff {α β : Type} (f : α → Option β) (xs : List α) :
    findFirst f xs = none ↔ ∀ a ∈ xs, f a = none := by
  induction xs with
  | nil => simp [findFirst]
  | cons a rest ih =>
    simp only [findFirst, orOpt_eq_none, ih, List.forall_mem_cons]

private theorem findFirst_some_mem {α β : Type} {f : α → Option β} {xs : List α} {b : β}
    (h : findFirst f xs = Option.some b) : ∃ a ∈ xs, f a = Option.some b := by
  induction xs with
  | nil => simp [findFirst] at h
  | cons a rest ih =>
    simp only [findFirst, orOpt_eq_some] at h
    rcases h with ha | ⟨_, hr⟩
    · exact ⟨a, List.mem_cons_self .., ha⟩
    · obtain ⟨x, hx, hfx⟩ := ih hr
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

def Problem.findInnermostTop (p : Problem) : Option (Bool × Concept) :=
  orOpt p.root.findInnermostTop
    (orOpt (findFirst (fun q => orOpt q.sub.findInnermostTop q.sup.findInnermostTop) p.tbox)
      (orOpt (findFirst (fun k => k.cls.findInnermostTop) p.keys)
        (findFirst (fun ac => ac.2.findInnermostTop) p.classAssertions)))

private theorem list_sum_map_eq_zero {α : Type} (f : α → Nat) (xs : List α) :
    (xs.map f).sum = 0 ↔ ∀ a ∈ xs, f a = 0 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, ih, List.forall_mem_cons]

private theorem list_sum_map_le {α : Type} (f g : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, f a ≤ g a) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem list_sum_map_lt {α : Type} (f g : α → Nat) (xs : List α)
    (hle : ∀ a ∈ xs, f a ≤ g a) {a₀ : α} (ha : a₀ ∈ xs) (hlt : f a₀ < g a₀) :
    (xs.map f).sum < (xs.map g).sum := by
  induction xs with
  | nil => cases ha
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact Nat.add_lt_add_of_lt_of_le hlt
        (list_sum_map_le f g rest fun x hx => hle x (List.mem_cons_of_mem _ hx))
    · exact Nat.add_lt_add_of_le_of_lt (hle a (List.mem_cons_self ..))
        (ih (fun x hx => hle x (List.mem_cons_of_mem _ hx)) hmem)

theorem Problem.findInnermostTop_none_iff (p : Problem) :
    p.findInnermostTop = none ↔ p.topRestrictCount = 0 := by
  simp only [Problem.findInnermostTop, Problem.topRestrictCount, orOpt_eq_none,
    findFirst_none_iff, Concept.findInnermostTop_none_iff, Nat.add_eq_zero_iff,
    list_sum_map_eq_zero]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩,
         fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem Problem.findInnermostTop_target_zero {p : Problem} {isSome : Bool} {target : Concept}
    (h : p.findInnermostTop = Option.some (isSome, target)) :
    target.topRestrictCount = 0 := by
  simp only [Problem.findInnermostTop, orOpt_eq_some] at h
  rcases h with hr | ⟨_, ht | ⟨_, hk | ⟨_, hca⟩⟩⟩
  · exact Concept.findInnermostTop_target_zero hr
  · obtain ⟨q, _, hq⟩ := findFirst_some_mem ht
    rcases orOpt_eq_some.mp hq with hs | ⟨_, hsp⟩
    · exact Concept.findInnermostTop_target_zero hs
    · exact Concept.findInnermostTop_target_zero hsp
  · obtain ⟨k, _, hk'⟩ := findFirst_some_mem hk
    exact Concept.findInnermostTop_target_zero hk'
  · obtain ⟨ac, _, hac⟩ := findFirst_some_mem hca
    exact Concept.findInnermostTop_target_zero hac

theorem Problem.findInnermostTop_objProps_subset {p : Problem}
    {isSome : Bool} {target : Concept}
    (h : p.findInnermostTop = Option.some (isSome, target)) :
    ∀ r ∈ target.objProps, r ∈ p.objProps := by
  intro r hr
  simp only [Problem.findInnermostTop, orOpt_eq_some] at h
  simp only [Problem.objProps, List.mem_append, List.mem_flatMap]
  rcases h with hroot | ⟨_, ht | ⟨_, hk | ⟨_, hca⟩⟩⟩
  · have hm := Concept.findInnermostTop_objProps_subset hroot r hr
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm))))))))))
  · obtain ⟨q, hq, hqf⟩ := findFirst_some_mem ht
    have hqm : r ∈ q.sub.objProps ∨ r ∈ q.sup.objProps := by
      rcases orOpt_eq_some.mp hqf with hs | ⟨_, hsp⟩
      · exact Or.inl (Concept.findInnermostTop_objProps_subset hs r hr)
      · exact Or.inr (Concept.findInnermostTop_objProps_subset hsp r hr)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, hqm⟩))))))))))
  · obtain ⟨k, hk', hkf⟩ := findFirst_some_mem hk
    have hkm : r ∈ k.cls.objProps ∨ r ∈ k.objProps.map Prod.fst :=
      Or.inl (Concept.findInnermostTop_objProps_subset hkf r hr)
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk', hkm⟩)))
  · obtain ⟨ac, hac, hacf⟩ := findFirst_some_mem hca
    have hm := Concept.findInnermostTop_objProps_subset hacf r hr
    exact Or.inl (Or.inl (Or.inr ⟨ac, hac, hm⟩))

def Problem.replaceTop (p : Problem) (isSome : Bool) (target : Concept) (val : Bool) : Problem :=
  { p with
    tbox := p.tbox.map fun q => ⟨q.sub.replaceTop isSome target val, q.sup.replaceTop isSome target val⟩
    keys := p.keys.map fun k => { k with cls := k.cls.replaceTop isSome target val }
    classAssertions := p.classAssertions.map fun (a, c) => (a, c.replaceTop isSome target val)
    root := p.root.replaceTop isSome target val }

theorem Problem.replaceTop_models_iff (p : Problem) (i : Interpretation datatypeMap)
    {isSome : Bool} {target : Concept} {val : Bool}
    (htruth : topRestrictHolds i isSome target ↔ val = true) :
    (p.replaceTop isSome target val).Models i ↔ p.Models i := by
  have htbox :
      (∀ q ∈ (p.replaceTop isSome target val).tbox, ∀ x, holds i x q.sub → holds i x q.sup) ↔
      (∀ q ∈ p.tbox, ∀ x, holds i x q.sub → holds i x q.sup) := by
    simp only [Problem.replaceTop, List.forall_mem_map, holds_replaceTop_iff i htruth]
  have hkeys :
      (∀ k ∈ (p.replaceTop isSome target val).keys, ∀ x y,
        holds i x k.cls → holds i y k.cls → i.named x → i.named y →
        (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
        (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) ↔
      (∀ k ∈ p.keys, ∀ x y,
        holds i x k.cls → holds i y k.cls → i.named x → i.named y →
        (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
        (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) := by
    simp only [Problem.replaceTop, List.forall_mem_map, holds_replaceTop_iff i htruth]
  have hca :
      (∀ ac ∈ (p.replaceTop isSome target val).classAssertions, holds i (i.individuals ac.1) ac.2) ↔
      (∀ ac ∈ p.classAssertions, holds i (i.individuals ac.1) ac.2) := by
    simp only [Problem.replaceTop, List.forall_mem_map, holds_replaceTop_iff i htruth]
  constructor
  · intro hm
    exact ⟨htbox.mp hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
      hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hkeys.mp hm.keys,
      hca.mp hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
      hm.dataAssertions, hm.negDataAssertions⟩
  · intro hm
    exact ⟨htbox.mpr hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
      hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hkeys.mpr hm.keys,
      hca.mpr hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
      hm.dataAssertions, hm.negDataAssertions⟩

/-- Add one global GCI enforcing the assumed truth value `val` of `(isSome, target)`,
using the fresh ordinary role `w` whenever global existence is required. -/
def topConstraintGCI (w : IRI) (isSome : Bool) (target : Concept) (val : Bool) : Inclusion :=
  match isSome, val with
  | true, true => ⟨.top, .some (w, false) target⟩
  | true, false => ⟨target, .bottom⟩
  | false, true => ⟨.top, target⟩
  | false, false => ⟨.top, .some (w, false) target.dual⟩

def Problem.branchTop (p : Problem) (isSome : Bool) (target : Concept) (val : Bool) : Problem :=
  let q := p.replaceTop isSome target val
  let g := topConstraintGCI (freshObjProp p) isSome target val
  { q with tbox := g :: q.tbox }

theorem Problem.branchTop_count_lt {p : Problem} {isSome : Bool} {target : Concept}
    (val : Bool) (h : p.findInnermostTop = Option.some (isSome, target)) :
    (p.branchTop isSome target val).topRestrictCount < p.topRestrictCount := by
  have ht0 : target.topRestrictCount = 0 := Problem.findInnermostTop_target_zero h
  have hnt : (freshObjProp p == topObjectProperty) = false :=
    beq_false_of_ne (freshObjProp_ne_top p)
  have hg0 : (topConstraintGCI (freshObjProp p) isSome target val).sub.topRestrictCount +
      (topConstraintGCI (freshObjProp p) isSome target val).sup.topRestrictCount = 0 := by
    cases isSome <;> cases val <;>
      simp [topConstraintGCI, Concept.topRestrictCount, Concept.topRestrictCount_dual, ht0, hnt]
  have hbranchEq : (p.branchTop isSome target val).topRestrictCount =
      (p.replaceTop isSome target val).topRestrictCount := by
    simp only [Problem.branchTop, Problem.topRestrictCount, List.map_cons, List.sum_cons, hg0]
    omega
  rw [hbranchEq]
  have hrootLe : (p.root.replaceTop isSome target val).topRestrictCount ≤ p.root.topRestrictCount :=
    Concept.topRestrictCount_replaceTop_le isSome target val p.root
  have htboxLe :
      (((p.replaceTop isSome target val).tbox).map fun q => q.sub.topRestrictCount + q.sup.topRestrictCount).sum ≤
      (p.tbox.map fun q => q.sub.topRestrictCount + q.sup.topRestrictCount).sum := by
    simp only [Problem.replaceTop, List.map_map]
    exact list_sum_map_le _ _ p.tbox fun q _ =>
      Nat.add_le_add (Concept.topRestrictCount_replaceTop_le isSome target val q.sub)
        (Concept.topRestrictCount_replaceTop_le isSome target val q.sup)
  have hkeysLe :
      (((p.replaceTop isSome target val).keys).map fun k => k.cls.topRestrictCount).sum ≤
      (p.keys.map fun k => k.cls.topRestrictCount).sum := by
    simp only [Problem.replaceTop, List.map_map]
    exact list_sum_map_le _ _ p.keys fun k _ =>
      Concept.topRestrictCount_replaceTop_le isSome target val k.cls
  have hcaLe :
      (((p.replaceTop isSome target val).classAssertions).map fun ac => ac.2.topRestrictCount).sum ≤
      (p.classAssertions.map fun ac => ac.2.topRestrictCount).sum := by
    simp only [Problem.replaceTop, List.map_map]
    exact list_sum_map_le _ _ p.classAssertions fun ac _ =>
      Concept.topRestrictCount_replaceTop_le isSome target val ac.2
  simp only [Problem.findInnermostTop, orOpt_eq_some] at h
  unfold Problem.topRestrictCount
  rcases h with hr | ⟨_, ht | ⟨_, hk | ⟨_, hca⟩⟩⟩
  · have hlt := Concept.topRestrictCount_replaceTop_lt_of_find val hr
    simp only [Problem.replaceTop] at htboxLe hkeysLe hcaLe ⊢
    omega
  · obtain ⟨q, hq, hqf⟩ := findFirst_some_mem ht
    have hlt :
        (q.sub.replaceTop isSome target val).topRestrictCount +
        (q.sup.replaceTop isSome target val).topRestrictCount <
        q.sub.topRestrictCount + q.sup.topRestrictCount := by
      rcases orOpt_eq_some.mp hqf with hs | ⟨_, hsp⟩
      · exact Nat.add_lt_add_of_lt_of_le (Concept.topRestrictCount_replaceTop_lt_of_find val hs)
          (Concept.topRestrictCount_replaceTop_le isSome target val q.sup)
      · exact Nat.add_lt_add_of_le_of_lt
          (Concept.topRestrictCount_replaceTop_le isSome target val q.sub)
          (Concept.topRestrictCount_replaceTop_lt_of_find val hsp)
    have hsumLt :
        (((p.replaceTop isSome target val).tbox).map fun q => q.sub.topRestrictCount + q.sup.topRestrictCount).sum <
        (p.tbox.map fun q => q.sub.topRestrictCount + q.sup.topRestrictCount).sum := by
      simp only [Problem.replaceTop, List.map_map]
      exact list_sum_map_lt _ _ p.tbox (fun q _ =>
        Nat.add_le_add (Concept.topRestrictCount_replaceTop_le isSome target val q.sub)
          (Concept.topRestrictCount_replaceTop_le isSome target val q.sup)) hq hlt
    simp only [Problem.replaceTop] at hsumLt hkeysLe hcaLe ⊢
    omega
  · obtain ⟨k, hk', hkf⟩ := findFirst_some_mem hk
    have hsumLt :
        (((p.replaceTop isSome target val).keys).map fun k => k.cls.topRestrictCount).sum <
        (p.keys.map fun k => k.cls.topRestrictCount).sum := by
      simp only [Problem.replaceTop, List.map_map]
      exact list_sum_map_lt _ _ p.keys
        (fun k _ => Concept.topRestrictCount_replaceTop_le isSome target val k.cls)
        hk' (Concept.topRestrictCount_replaceTop_lt_of_find val hkf)
    simp only [Problem.replaceTop] at htboxLe hsumLt hcaLe ⊢
    omega
  · obtain ⟨ac, hac, hacf⟩ := findFirst_some_mem hca
    have hsumLt :
        (((p.replaceTop isSome target val).classAssertions).map fun ac => ac.2.topRestrictCount).sum <
        (p.classAssertions.map fun ac => ac.2.topRestrictCount).sum := by
      simp only [Problem.replaceTop, List.map_map]
      exact list_sum_map_lt _ _ p.classAssertions
        (fun ac _ => Concept.topRestrictCount_replaceTop_le isSome target val ac.2)
        hac (Concept.topRestrictCount_replaceTop_lt_of_find val hacf)
    simp only [Problem.replaceTop] at htboxLe hkeysLe hsumLt ⊢
    omega

private theorem branchTop_models_iff (p : Problem) (isSome : Bool) (target : Concept) (val : Bool)
    (i : Interpretation datatypeMap) :
    (p.branchTop isSome target val).Models i ↔
      (p.replaceTop isSome target val).Models i ∧
      (∀ x, holds i x (topConstraintGCI (freshObjProp p) isSome target val).sub →
            holds i x (topConstraintGCI (freshObjProp p) isSome target val).sup) := by
  constructor
  · intro hm
    have hg := hm.tbox _ (List.mem_cons_self ..)
    have ht : ∀ q ∈ (p.replaceTop isSome target val).tbox, ∀ x, holds i x q.sub → holds i x q.sup :=
      fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq)
    exact ⟨⟨ht, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩, hg⟩
  · rintro ⟨hm, hg⟩
    refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact hg
    · exact hm.tbox q hmem

private theorem branchTop_sat_iff_aux {p : Problem} {isSome : Bool} {target : Concept}
    (w : IRI) (hw_eq : w = freshObjProp p)
    (hw_nt : w ≠ topObjectProperty) (hw_nb : w ≠ bottomObjectProperty)
    (hw_p : w ∉ p.objProps) (hw_t : w ∉ target.objProps) (hw_root : w ∉ p.root.objProps) :
    ((p.branchTop isSome target true).Sat ∨ (p.branchTop isSome target false).Sat) ↔ p.Sat := by
  constructor
  · intro hor
    rcases hor with ⟨i, hm, x₀, hroot⟩ | ⟨i, hm, x₀, hroot⟩
    · obtain ⟨hmr, hg⟩ := (branchTop_models_iff p isSome target true i).mp hm
      have htruth : topRestrictHolds i isSome target ↔ true = true := by
        cases isSome with
        | true =>
          simp only [topConstraintGCI, holds] at hg
          obtain ⟨y, _, hy⟩ := hg x₀ trivial
          exact ⟨fun _ => rfl, fun _ => ⟨y, hy⟩⟩
        | false =>
          simp only [topConstraintGCI, holds] at hg
          exact ⟨fun _ => rfl, fun _ y => hg y trivial⟩
      exact ⟨i, (p.replaceTop_models_iff i htruth).mp hmr, x₀,
        (holds_replaceTop_iff i htruth x₀ p.root).mp hroot⟩
    · obtain ⟨hmr, hg⟩ := (branchTop_models_iff p isSome target false i).mp hm
      have htruth : topRestrictHolds i isSome target ↔ false = true := by
        cases isSome with
        | true =>
          simp only [topConstraintGCI, holds] at hg
          exact ⟨fun ⟨y, hy⟩ => (hg y hy).elim, fun hf => Bool.noConfusion hf⟩
        | false =>
          simp only [topConstraintGCI, holds] at hg
          obtain ⟨y, _, hy⟩ := hg x₀ trivial
          have hny : ¬ holds i y target := (holds_dual i y target).mp hy
          exact ⟨fun hall => (hny (hall y)).elim, fun hf => Bool.noConfusion hf⟩
      exact ⟨i, (p.replaceTop_models_iff i htruth).mp hmr, x₀,
        (holds_replaceTop_iff i htruth x₀ p.root).mp hroot⟩
  · rintro ⟨i, hm, x₀, hroot⟩
    cases isSome with
    | true =>
      by_cases hex : ∃ y, holds i y target
      · left
        obtain ⟨y₀, hy₀⟩ := hex
        let j := withUniversalRole i w hw_nt hw_nb
        have hmj : p.Models j := (models_withUniversalRole_iff p i hw_nt hw_nb hw_p).mpr hm
        have hrootj : holds j x₀ p.root :=
          (holds_withUniversalRole_iff i hw_nt hw_nb hw_root x₀).mpr hroot
        have hy₀j : holds j y₀ target :=
          (holds_withUniversalRole_iff i hw_nt hw_nb hw_t y₀).mpr hy₀
        have htruth : topRestrictHolds j true target ↔ true = true :=
          ⟨fun _ => rfl, fun _ => ⟨y₀, hy₀j⟩⟩
        refine ⟨j, (branchTop_models_iff p true target true j).mpr ⟨?_, ?_⟩, x₀, ?_⟩
        · exact (p.replaceTop_models_iff j htruth).mpr hmj
        · intro x _
          rw [← hw_eq]
          exact ⟨y₀, holdsOriented_withUniversalRole_eq i hw_nt hw_nb x y₀, hy₀j⟩
        · exact (holds_replaceTop_iff j htruth x₀ p.root).mpr hrootj
      · right
        have htruth : topRestrictHolds i true target ↔ false = true :=
          ⟨fun h => (hex h).elim, fun hf => Bool.noConfusion hf⟩
        refine ⟨i, (branchTop_models_iff p true target false i).mpr ⟨?_, ?_⟩, x₀, ?_⟩
        · exact (p.replaceTop_models_iff i htruth).mpr hm
        · intro x hx
          exact hex ⟨x, hx⟩
        · exact (holds_replaceTop_iff i htruth x₀ p.root).mpr hroot
    | false =>
      by_cases hall : ∀ y, holds i y target
      · left
        have htruth : topRestrictHolds i false target ↔ true = true :=
          ⟨fun _ => rfl, fun _ => hall⟩
        refine ⟨i, (branchTop_models_iff p false target true i).mpr ⟨?_, ?_⟩, x₀, ?_⟩
        · exact (p.replaceTop_models_iff i htruth).mpr hm
        · intro x _; exact hall x
        · exact (holds_replaceTop_iff i htruth x₀ p.root).mpr hroot
      · right
        obtain ⟨y₀, hny₀⟩ := Classical.not_forall.mp hall
        let j := withUniversalRole i w hw_nt hw_nb
        have hmj : p.Models j := (models_withUniversalRole_iff p i hw_nt hw_nb hw_p).mpr hm
        have hrootj : holds j x₀ p.root :=
          (holds_withUniversalRole_iff i hw_nt hw_nb hw_root x₀).mpr hroot
        have hny₀j : ¬ holds j y₀ target := fun hy =>
          hny₀ ((holds_withUniversalRole_iff i hw_nt hw_nb hw_t y₀).mp hy)
        have htruth : topRestrictHolds j false target ↔ false = true :=
          ⟨fun hj => (hny₀j (hj y₀)).elim, fun hf => Bool.noConfusion hf⟩
        refine ⟨j, (branchTop_models_iff p false target false j).mpr ⟨?_, ?_⟩, x₀, ?_⟩
        · exact (p.replaceTop_models_iff j htruth).mpr hmj
        · intro x _
          rw [← hw_eq]
          exact ⟨y₀, holdsOriented_withUniversalRole_eq i hw_nt hw_nb x y₀,
            (holds_dual j y₀ target).mpr hny₀j⟩
        · exact (holds_replaceTop_iff j htruth x₀ p.root).mpr hrootj

theorem Problem.branchTop_sat_iff {p : Problem} {isSome : Bool} {target : Concept}
    (h : p.findInnermostTop = Option.some (isSome, target)) :
    ((p.branchTop isSome target true).Sat ∨ (p.branchTop isSome target false).Sat) ↔ p.Sat :=
  branchTop_sat_iff_aux (freshObjProp p) rfl
    (freshObjProp_ne_top p) (freshObjProp_ne_bottom p)
    (freshObjProp_not_mem p)
    (fun hm => freshObjProp_not_mem p (Problem.findInnermostTop_objProps_subset h _ hm))
    (problem_objProps_parts (freshObjProp_not_mem p)).1

/-- Exhaustively expand every universal-role restriction in `p` (innermost first)
into a finite list of universal-role-free problems whose disjunction of
satisfiability is equivalent to `p.Sat`. -/
def expandTopRestrictions (p : Problem) : List Problem :=
  match h : p.findInnermostTop with
  | none => [p]
  | Option.some (isSome, target) =>
    have _ : (p.branchTop isSome target true).topRestrictCount < p.topRestrictCount :=
      Problem.branchTop_count_lt true h
    have _ : (p.branchTop isSome target false).topRestrictCount < p.topRestrictCount :=
      Problem.branchTop_count_lt false h
    expandTopRestrictions (p.branchTop isSome target true) ++
      expandTopRestrictions (p.branchTop isSome target false)
termination_by p.topRestrictCount

theorem expandTopRestrictions_sat_iff (p : Problem) :
    (∃ q ∈ expandTopRestrictions p, q.Sat) ↔ p.Sat := by
  fun_induction expandTopRestrictions p with
  | case1 p hnone =>
    simp
  | case2 p isSome target hsome _ _ ihT ihF =>
    simp only [List.mem_append, or_and_right, exists_or, ihT, ihF]
    exact Problem.branchTop_sat_iff hsome

theorem expandTopRestrictions_noTop (p : Problem) :
    ∀ q ∈ expandTopRestrictions p, q.topRestrictCount = 0 := by
  fun_induction expandTopRestrictions p with
  | case1 p hnone =>
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact (Problem.findInnermostTop_none_iff p).mp hnone
  | case2 p isSome target hsome _ _ ihT ihF =>
    intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact ihT q h1
    · exact ihF q h2

theorem expandTopRestrictions_eq_singleton_of_zero {p : Problem}
    (h : p.topRestrictCount = 0) :
    expandTopRestrictions p = [p] := by
  rw [expandTopRestrictions]
  split
  · rfl
  · rename_i isSome target hsome
    have hn : p.findInnermostTop = none := (Problem.findInnermostTop_none_iff p).mpr h
    rw [hn] at hsome
    cases hsome

/-! ### 4. Static admission (`isSROIQDWithTop`) and preservation into `isSROIQD` -/

def isObjPropOrTop (r : IRI) : Bool :=
  isCoreObjPropIRI r || r == topObjectProperty

/-- Concepts admitted by `SROIQ(D)` extended with `∃ owl:topObjectProperty.C` and
`∀ owl:topObjectProperty.C` (forward or inverse). Non-simple uses of
`owl:topObjectProperty` (`self`, `min`, `max`) remain excluded. -/
def Concept.isSROIQDWithTop : Concept → Bool
  | .top | .bottom => true
  | .lit a _ => isCoreClassIRI a
  | .nom _ _ => true
  | .self r _ => isCoreObjPropIRI r.1
  | .conj a b | .disj a b => a.isSROIQDWithTop && b.isSROIQDWithTop
  | .some r c | .all r c => isObjPropOrTop r.1 && c.isSROIQDWithTop
  | .min _ r c | .max _ r c => isCoreObjPropIRI r.1 && c.isSROIQDWithTop
  | .dataSome dp d | .dataAll dp d | .dataMin _ dp d | .dataMax _ dp d =>
    isCoreDataPropIRI dp && d.isSROIQD
  | .dataValue dp l _ =>
    isCoreDataPropIRI dp && (Sabrina.OWL2.Datatypes.decodeLiteral l).isSome

theorem Concept.isSROIQDWithTop_dual (c : Concept) :
    c.dual.isSROIQDWithTop = c.isSROIQDWithTop := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQDWithTop]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.isSROIQDWithTop]
  | _ => simp_all [Concept.dual, Concept.isSROIQDWithTop]

theorem Concept.isSROIQD_implies_isSROIQDWithTop {c : Concept} (h : c.isSROIQD = true) :
    c.isSROIQDWithTop = true := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => exact h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQD, Concept.isSROIQDWithTop, Bool.and_eq_true] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | some r c ih | all r c ih =>
    simp only [Concept.isSROIQD, Concept.isSROIQDWithTop, isObjPropOrTop,
      Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨Or.inl h.1, ih h.2⟩
  | min n r c ih | max n r c ih =>
    simp only [Concept.isSROIQD, Concept.isSROIQDWithTop, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

theorem Concept.isSROIQD_of_isSROIQDWithTop_zero {c : Concept}
    (h : c.isSROIQDWithTop = true) (hz : c.topRestrictCount = 0) :
    c.isSROIQD = true := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => exact h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    simp only [Concept.topRestrictCount, Nat.add_eq_zero_iff] at hz
    simp only [Concept.isSROIQD, Bool.and_eq_true]
    exact ⟨iha h.1 hz.1, ihb h.2 hz.2⟩
  | some r c ih | all r c ih =>
    simp only [Concept.isSROIQDWithTop, isObjPropOrTop, Bool.and_eq_true, Bool.or_eq_true] at h
    simp only [Concept.topRestrictCount, Nat.add_eq_zero_iff] at hz
    have hnt : (r.1 == topObjectProperty) = false := by
      cases hq : r.1 == topObjectProperty
      · rfl
      · simp [hq] at hz
    have hcore : isCoreObjPropIRI r.1 = true := by
      rcases h.1 with hc | ht
      · exact hc
      · rw [hnt] at ht; cases ht
    simp only [Concept.isSROIQD, Bool.and_eq_true]
    exact ⟨hcore, ih h.2 hz.2⟩
  | min n r c ih | max n r c ih =>
    simp only [Concept.isSROIQDWithTop, Concept.isSROIQD, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2 hz⟩

theorem Concept.isSROIQDWithTop_replaceTop {c : Concept} {isSome : Bool} {target : Concept}
    (val : Bool) (h : c.isSROIQDWithTop = true) :
    (c.replaceTop isSome target val).isSROIQDWithTop = true := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => exact h
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    simp only [Concept.replaceTop, Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | some r c ih | all r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    unfold Concept.replaceTop
    split
    · cases val <;> rfl
    · simp only [Concept.isSROIQDWithTop, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | min n r c ih | max n r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    simp only [Concept.replaceTop, Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨h.1, ih h.2⟩

theorem Concept.findInnermostTop_isSROIQDWithTop {c : Concept} {isSome : Bool} {target : Concept}
    (h : c.isSROIQDWithTop = true) (hf : c.findInnermostTop = Option.some (isSome, target)) :
    target.isSROIQDWithTop = true := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop] at hf
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    simp only [Concept.findInnermostTop, orOpt_eq_some] at hf
    rcases hf with ha | ⟨_, hb⟩
    · exact iha h.1 ha
    · exact ihb h.2 hb
  | some r c ih | all r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    simp only [Concept.findInnermostTop, orOpt_eq_some] at hf
    rcases hf with hc | ⟨_, hself⟩
    · exact ih h.2 hc
    · by_cases hr : r.1 == topObjectProperty
      · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
        exact hself.2 ▸ h.2
      · simp [hr] at hself
  | min n r c ih | max n r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at h
    exact ih h.2 hf

theorem Concept.countedRoles_dual (c : Concept) : c.dual.countedRoles = c.countedRoles := by
  induction c with
  | min n _ _ => cases n <;> simp [Concept.dual, Concept.countedRoles]
  | dataMin n _ _ => cases n <;> simp [Concept.dual, Concept.countedRoles]
  | _ => simp_all [Concept.dual, Concept.countedRoles]

theorem Concept.countedRoles_replaceTop_subset (isSome : Bool) (target : Concept)
    (val : Bool) (c : Concept) :
    ∀ r ∈ (c.replaceTop isSome target val).countedRoles, r ∈ c.countedRoles := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    intro r hr; exact hr
  | conj a b iha ihb | disj a b iha ihb =>
    intro r hr
    simp only [Concept.replaceTop, Concept.countedRoles, List.mem_append] at hr ⊢
    exact hr.elim (Or.inl ∘ iha r) (Or.inr ∘ ihb r)
  | some r c ih | all r c ih =>
    intro s hs
    unfold Concept.replaceTop at hs
    split at hs
    · cases val <;> simp [boolConcept, Concept.countedRoles] at hs
    · exact ih s hs
  | min n r c ih | max n r c ih =>
    intro s hs
    simp only [Concept.replaceTop, Concept.countedRoles, List.mem_cons] at hs ⊢
    exact hs.elim Or.inl (Or.inr ∘ ih s)

theorem Concept.findInnermostTop_countedRoles_subset {c : Concept}
    {isSome : Bool} {target : Concept}
    (hf : c.findInnermostTop = Option.some (isSome, target)) :
    ∀ r ∈ target.countedRoles, r ∈ c.countedRoles := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax =>
    simp [Concept.findInnermostTop] at hf
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at hf
    intro r hr
    simp only [Concept.countedRoles, List.mem_append]
    rcases hf with ha | ⟨_, hb⟩
    · exact Or.inl (iha ha r hr)
    · exact Or.inr (ihb hb r hr)
  | some r c ih | all r c ih =>
    simp only [Concept.findInnermostTop, orOpt_eq_some] at hf
    intro s hs
    rcases hf with hc | ⟨_, hself⟩
    · exact ih hc s hs
    · by_cases hr : r.1 == topObjectProperty
      · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hself
        exact hself.2 ▸ hs
      · simp [hr] at hself
  | min n r c ih | max n r c ih =>
    intro s hs
    simp only [Concept.countedRoles, List.mem_cons]
    exact Or.inr (ih hf s hs)

/-- `Problem` admission extending `Problem.isSROIQD` with `∃ owl:topObjectProperty.C`
and `∀ owl:topObjectProperty.C` in class expressions. -/
def Problem.isSROIQDWithTop (p : Problem) (rank : Rank) : Bool :=
  p.root.isSROIQDWithTop &&
  p.tbox.all (fun q => q.sub.isSROIQDWithTop && q.sup.isSROIQDWithTop) &&
  p.rules.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.chains.all (fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI) &&
  p.chars.reflexive.all isCoreObjPropIRI &&
  p.chars.irreflexive.all isCoreObjPropIRI &&
  p.chars.asymmetric.all isCoreObjPropIRI &&
  p.chars.disjoint.all (fun (r, s) => isCoreObjPropIRI r.1 && isCoreObjPropIRI s.1) &&
  p.classAssertions.all (fun (_, c) => c.isSROIQDWithTop) &&
  p.objAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.negObjAssertions.all (fun (r, _, _) => isCoreObjPropIRI r) &&
  p.keys.all (fun k => k.cls.isSROIQDWithTop && k.objProps.all (fun r => isCoreObjPropIRI r.1) && k.dataProps.all isCoreDataPropIRI) &&
  p.subData.all (fun (r, s) => isCoreDataPropIRI r && isCoreDataPropIRI s) &&
  p.disjointData.all (fun (r, s) => isCoreDataPropIRI r && isCoreDataPropIRI s) &&
  p.funcData.all isCoreDataPropIRI &&
  p.dataRanges.all (fun (r, d) => isCoreDataPropIRI r && d.isSROIQD) &&
  p.dataAssertions.all (fun (r, _, l) => isCoreDataPropIRI r && (Sabrina.OWL2.Datatypes.decodeLiteral l).isSome) &&
  p.negDataAssertions.all (fun (r, _, l) => isCoreDataPropIRI r && (Sabrina.OWL2.Datatypes.decodeLiteral l).isSome) &&
  p.checkSimple && checkRegular rank p.rules p.chains

theorem Problem.isSROIQD_implies_isSROIQDWithTop {p : Problem} {rank : Rank}
    (h : p.isSROIQD rank = true) :
    p.isSROIQDWithTop rank = true := by
  simp only [Problem.isSROIQD, Problem.isSROIQDWithTop, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨Concept.isSROIQD_implies_isSROIQDWithTop h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
    fun q hq => ⟨Concept.isSROIQD_implies_isSROIQDWithTop (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q hq).1,
                 Concept.isSROIQD_implies_isSROIQDWithTop (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q hq).2⟩⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    fun ac hac => Concept.isSROIQD_implies_isSROIQDWithTop (h.1.1.1.1.1.1.1.1.1.1.1.2 ac hac)⟩,
    h.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.2⟩,
    fun k hk => ⟨⟨Concept.isSROIQD_implies_isSROIQDWithTop (h.1.1.1.1.1.1.1.1.2 k hk).1.1,
      (h.1.1.1.1.1.1.1.1.2 k hk).1.2⟩, (h.1.1.1.1.1.1.1.1.2 k hk).2⟩⟩,
    h.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.2⟩,
    h.1.1.1.1.2⟩,
    h.1.1.1.2⟩,
    h.1.1.2⟩,
    h.1.2⟩,
    h.2⟩

theorem Problem.isSROIQD_of_isSROIQDWithTop_zero {p : Problem} {rank : Rank}
    (h : p.isSROIQDWithTop rank = true) (hz : p.topRestrictCount = 0) :
    p.isSROIQD rank = true := by
  simp only [Problem.topRestrictCount, Nat.add_eq_zero_iff, list_sum_map_eq_zero] at hz
  obtain ⟨⟨⟨hzRoot, hzTbox⟩, hzKeys⟩, hzCA⟩ := hz
  simp only [Problem.isSROIQD, Problem.isSROIQDWithTop, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨Concept.isSROIQD_of_isSROIQDWithTop_zero
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 hzRoot,
    fun q hq =>
      ⟨Concept.isSROIQD_of_isSROIQDWithTop_zero (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q hq).1 (hzTbox q hq).1,
       Concept.isSROIQD_of_isSROIQDWithTop_zero (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q hq).2 (hzTbox q hq).2⟩⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    fun ac hac => Concept.isSROIQD_of_isSROIQDWithTop_zero (h.1.1.1.1.1.1.1.1.1.1.1.2 ac hac) (hzCA ac hac)⟩,
    h.1.1.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.1.1.2⟩,
    fun k hk => ⟨⟨Concept.isSROIQD_of_isSROIQDWithTop_zero (h.1.1.1.1.1.1.1.1.2 k hk).1.1 (hzKeys k hk),
      (h.1.1.1.1.1.1.1.1.2 k hk).1.2⟩, (h.1.1.1.1.1.1.1.1.2 k hk).2⟩⟩,
    h.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.2⟩,
    h.1.1.1.1.2⟩,
    h.1.1.1.2⟩,
    h.1.1.2⟩,
    h.1.2⟩,
    h.2⟩

private theorem Problem.findInnermostTop_countedRoles_subset {p : Problem}
    {isSome : Bool} {target : Concept}
    (hf : p.findInnermostTop = Option.some (isSome, target)) :
    ∀ r ∈ target.countedRoles, r ∈ p.simpleRoles := by
  intro r hr
  simp only [Problem.findInnermostTop, orOpt_eq_some] at hf
  simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  rcases hf with hroot | ⟨_, ht | ⟨_, hk | ⟨_, hca⟩⟩⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Concept.findInnermostTop_countedRoles_subset hroot r hr)))))
  · obtain ⟨q, hq, hqf⟩ := findFirst_some_mem ht
    have hqm : r ∈ q.sub.countedRoles ∨ r ∈ q.sup.countedRoles := by
      rcases orOpt_eq_some.mp hqf with hs | ⟨_, hsp⟩
      · exact Or.inl (Concept.findInnermostTop_countedRoles_subset hs r hr)
      · exact Or.inr (Concept.findInnermostTop_countedRoles_subset hsp r hr)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, hqm⟩))))
  · obtain ⟨k, hk', hkf⟩ := findFirst_some_mem hk
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk', Concept.findInnermostTop_countedRoles_subset hkf r hr⟩)))
  · obtain ⟨ac, hac, hacf⟩ := findFirst_some_mem hca
    exact Or.inl (Or.inl (Or.inr ⟨ac, hac, Concept.findInnermostTop_countedRoles_subset hacf r hr⟩))

private theorem Problem.branchTop_simpleRoles_subset {p : Problem}
    {isSome : Bool} {target : Concept} (val : Bool)
    (hf : p.findInnermostTop = Option.some (isSome, target)) :
    ∀ r ∈ (p.branchTop isSome target val).simpleRoles, r ∈ p.simpleRoles := by
  intro r hr
  have hgSub :
      ∀ s ∈ (topConstraintGCI (freshObjProp p) isSome target val).sub.countedRoles ++
            (topConstraintGCI (freshObjProp p) isSome target val).sup.countedRoles,
      s ∈ p.simpleRoles := by
    intro s hs
    have hst : s ∈ target.countedRoles := by
      cases isSome <;> cases val <;>
        simp [topConstraintGCI, Concept.countedRoles, Concept.countedRoles_dual] at hs <;>
        exact hs
    exact Problem.findInnermostTop_countedRoles_subset hf s hst
  simp only [Problem.branchTop, Problem.replaceTop, Problem.simpleRoles,
    List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons] at hr ⊢
  rcases hr with ((((hroot | ht) | hk) | hca) | hnamed) | hdisj
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Concept.countedRoles_replaceTop_subset isSome target val p.root r hroot)))))
  · rcases ht with ⟨q, hq, hqr⟩
    rcases hq with rfl | hqmem
    · have hmem := hgSub r (List.mem_append.mpr hqr)
      simp only [Problem.simpleRoles, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
        List.mem_map, List.mem_cons] at hmem
      exact hmem
    · rcases hqmem with ⟨q₀, hq₀, rfl⟩
      have hsub : r ∈ q₀.sub.countedRoles ∨ r ∈ q₀.sup.countedRoles :=
        hqr.elim
          (Or.inl ∘ Concept.countedRoles_replaceTop_subset isSome target val q₀.sub r)
          (Or.inr ∘ Concept.countedRoles_replaceTop_subset isSome target val q₀.sup r)
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q₀, hq₀, hsub⟩))))
  · rcases hk with ⟨k, ⟨k₀, hk₀, rfl⟩, hkr⟩
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k₀, hk₀,
      Concept.countedRoles_replaceTop_subset isSome target val k₀.cls r hkr⟩)))
  · rcases hca with ⟨ac, ⟨ac₀, hac₀, rfl⟩, hacr⟩
    exact Or.inl (Or.inl (Or.inr ⟨ac₀, hac₀,
      Concept.countedRoles_replaceTop_subset isSome target val ac₀.2 r hacr⟩))
  · exact Or.inl (Or.inr hnamed)
  · exact Or.inr hdisj

theorem Problem.branchTop_isSROIQDWithTop {p : Problem} {rank : Rank}
    {isSome : Bool} {target : Concept} (val : Bool)
    (h : p.isSROIQDWithTop rank = true)
    (hf : p.findInnermostTop = Option.some (isSome, target)) :
    (p.branchTop isSome target val).isSROIQDWithTop rank = true := by
  have hsimple : (p.branchTop isSome target val).checkSimple = true := by
    have hpSimple : p.checkSimple = true := by
      simp only [Problem.isSROIQDWithTop, Bool.and_eq_true] at h
      exact h.1.2
    rw [Problem.checkSimple_iff] at hpSimple ⊢
    intro r hr
    exact hpSimple r (Problem.branchTop_simpleRoles_subset val hf r hr)
  simp only [Problem.isSROIQDWithTop, Bool.and_eq_true, List.all_eq_true] at h
  have htarget : target.isSROIQDWithTop = true := by
    simp only [Problem.findInnermostTop, orOpt_eq_some] at hf
    rcases hf with hr | ⟨_, ht | ⟨_, hk | ⟨_, hca⟩⟩⟩
    · exact Concept.findInnermostTop_isSROIQDWithTop
        h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 hr
    · obtain ⟨q, hq, hqf⟩ := findFirst_some_mem ht
      have hqt := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q hq
      rcases orOpt_eq_some.mp hqf with hs | ⟨_, hsp⟩
      · exact Concept.findInnermostTop_isSROIQDWithTop hqt.1 hs
      · exact Concept.findInnermostTop_isSROIQDWithTop hqt.2 hsp
    · obtain ⟨k, hk', hkf⟩ := findFirst_some_mem hk
      exact Concept.findInnermostTop_isSROIQDWithTop
        (h.1.1.1.1.1.1.1.1.2 k hk').1.1 hkf
    · obtain ⟨ac, hac, hacf⟩ := findFirst_some_mem hca
      exact Concept.findInnermostTop_isSROIQDWithTop
        (h.1.1.1.1.1.1.1.1.1.1.1.2 ac hac) hacf
  have hgOk :
      (topConstraintGCI (freshObjProp p) isSome target val).sub.isSROIQDWithTop = true ∧
      (topConstraintGCI (freshObjProp p) isSome target val).sup.isSROIQDWithTop = true := by
    have hwCore : isObjPropOrTop (freshObjProp p) = true := by
      simp [isObjPropOrTop, freshObjProp_core p]
    cases isSome <;> cases val <;>
      simp [topConstraintGCI, Concept.isSROIQDWithTop, Concept.isSROIQDWithTop_dual,
        hwCore, htarget]
  simp only [Problem.isSROIQDWithTop, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact Concept.isSROIQDWithTop_replaceTop val h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  · intro q hq
    simp only [Problem.branchTop, Problem.replaceTop, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨q₀, hq₀, rfl⟩
    · exact hgOk
    · have hq0 := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 q₀ hq₀
      exact ⟨Concept.isSROIQDWithTop_replaceTop val hq0.1,
             Concept.isSROIQDWithTop_replaceTop val hq0.2⟩
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.1.1.1.2
  · intro ac hac
    simp only [Problem.branchTop, Problem.replaceTop, List.mem_map] at hac
    obtain ⟨ac₀, hac₀, rfl⟩ := hac
    exact Concept.isSROIQDWithTop_replaceTop val (h.1.1.1.1.1.1.1.1.1.1.1.2 ac₀ hac₀)
  · exact h.1.1.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.1.1.2
  · intro k hk
    simp only [Problem.branchTop, Problem.replaceTop, List.mem_map] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    have hk0 := h.1.1.1.1.1.1.1.1.2 k₀ hk₀
    exact ⟨⟨Concept.isSROIQDWithTop_replaceTop val hk0.1.1, hk0.1.2⟩, hk0.2⟩
  · exact h.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.2
  · exact h.1.1.1.1.2
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact hsimple
  · exact h.2

theorem expandTopRestrictions_isSROIQDWithTop {p : Problem} {rank : Rank}
    (h : p.isSROIQDWithTop rank = true) :
    ∀ q ∈ expandTopRestrictions p, q.isSROIQDWithTop rank = true := by
  fun_induction expandTopRestrictions p with
  | case1 p hnone =>
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact h
  | case2 p isSome target hsome _ _ ihT ihF =>
    intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact ihT (Problem.branchTop_isSROIQDWithTop true h hsome) q h1
    · exact ihF (Problem.branchTop_isSROIQDWithTop false h hsome) q h2

theorem expandTopRestrictions_isSROIQD {p : Problem} {rank : Rank}
    (h : p.isSROIQDWithTop rank = true) :
    ∀ q ∈ expandTopRestrictions p, q.isSROIQD rank = true := fun q hq =>
  Problem.isSROIQD_of_isSROIQDWithTop_zero
    (expandTopRestrictions_isSROIQDWithTop h q hq)
    (expandTopRestrictions_noTop p q hq)

/-! ### 5. Fuel-free verified decision procedures and adapter composition -/

namespace Termination.BlockedForest

/-- Fuel-free verified decision procedure for `SROIQ(D)` extended with nested
`∃ owl:topObjectProperty.C` and `∀ owl:topObjectProperty.C` (forward and inverse). -/
def decideSROIQDWithTopBool {rank : Rank} {p : Problem}
    (h : p.isSROIQDWithTop rank = true) : Bool :=
  (expandTopRestrictions p).attach.any fun ⟨q, hq⟩ =>
    decideSROIQDBool (expandTopRestrictions_isSROIQD h q hq)

theorem decideSROIQDWithTopBool_iff {rank : Rank} {p : Problem}
    (h : p.isSROIQDWithTop rank = true) :
    decideSROIQDWithTopBool h = true ↔ p.Sat := by
  unfold decideSROIQDWithTopBool
  rw [List.any_eq_true, ← expandTopRestrictions_sat_iff p]
  constructor
  · rintro ⟨⟨q, hq⟩, _, hdec⟩
    exact ⟨q, hq, (decideSROIQDBool_iff (expandTopRestrictions_isSROIQD h q hq)).mp hdec⟩
  · rintro ⟨q, hq, hsat⟩
    exact ⟨⟨q, hq⟩, List.mem_attach _ _,
      (decideSROIQDBool_iff (expandTopRestrictions_isSROIQD h q hq)).mpr hsat⟩

/-- Opt-in decision adapter extending `decideAfterLoweringChainAliases?` (and
`decideAdmittedOntology?`) with universal-role class restrictions. -/
def decideAfterExpandingUniversalRole? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    let q := p.lowerChainAliases
    (findRank q.rules q.chains).bind fun rank =>
      if p.root = .top ∧ p.checkSimple = true then
        if h : q.lowerBottom.isSROIQDWithTop rank = true then
          Option.some (decideSROIQDWithTopBool h)
        else none
      else none

theorem decideAfterExpandingUniversalRole_iff {o : Ontology} {b : Bool}
    (h : decideAfterExpandingUniversalRole? o = Option.some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideAfterExpandingUniversalRole?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := h
  split at hb
  · rename_i hroot
    split at hb
    · rename_i hadmit
      cases hb
      exact (decideSROIQDWithTopBool_iff hadmit).trans
        (p.lowerChainAliases.lowerBottom_sat_iff.trans
          (p.lowerChainAliases_sat_iff.trans
            ((Normalize.normalizeWithDefs_sat_iff hnorm).trans
              (satisfiable_iff_sat p hroot.1)).symm))
    · contradiction
  · contradiction

theorem decideAfterExpandingUniversalRole_unsat_iff {o : Ontology} {b : Bool}
    (h : decideAfterExpandingUniversalRole? o = Option.some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideAfterExpandingUniversalRole_iff h]
  cases b <;> simp

theorem decideAfterExpandingUniversalRole_extends_aliases {o : Ontology} {b : Bool}
    (h : decideAfterLoweringChainAliases? o = Option.some b) :
    decideAfterExpandingUniversalRole? o = Option.some b := by
  have hiff₁ := decideAfterLoweringChainAliases_iff h
  simp only [decideAfterLoweringChainAliases?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, hfound, hb⟩ := h
  split at hb
  · rename_i hroot
    split at hb
    · rename_i hadmit
      dsimp only at hfound hroot hadmit
      have hadmit' := Problem.isSROIQD_implies_isSROIQDWithTop hadmit
      have hval : decideAfterExpandingUniversalRole? o = Option.some (decideSROIQDWithTopBool hadmit') := by
        simp [decideAfterExpandingUniversalRole?, hnorm, hfound, hroot, hadmit']
      have hiff₂ := decideAfterExpandingUniversalRole_iff hval
      have heq : decideSROIQDWithTopBool hadmit' = b := by
        cases h1 : decideSROIQDWithTopBool hadmit' <;> cases b <;> simp_all
      simpa [heq] using hval
    · contradiction
  · contradiction

theorem decideAfterExpandingUniversalRole_extends_admitted {o : Ontology} {b : Bool}
    (h : decideAdmittedOntology? o = Option.some b) :
    decideAfterExpandingUniversalRole? o = Option.some b :=
  decideAfterExpandingUniversalRole_extends_aliases (decideAfterLoweringChainAliases_extends h)

/-- Combined verified decision adapter: erases tautological top-headed chains,
lowers recursive chain aliases, eliminates bottom properties, and exhaustively
expands universal-role class restrictions before running the fuel-free solver. -/
def decideWithUniversalRole? (o : Ontology) : Option Bool :=
  decideAfterExpandingUniversalRole? (RoleHierarchy.eraseTopHeadedChains o)

theorem decideWithUniversalRole_iff {o : Ontology} {b : Bool}
    (h : decideWithUniversalRole? o = Option.some b) :
    b = true ↔ Satisfiable datatypeMap o :=
  (decideAfterExpandingUniversalRole_iff h).trans
    (RoleHierarchy.eraseTopHeadedChains_sat_iff datatypeMap o)

theorem decideWithUniversalRole_unsat_iff {o : Ontology} {b : Bool}
    (h : decideWithUniversalRole? o = Option.some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideWithUniversalRole_iff h]
  cases b <;> simp

theorem decideWithUniversalRole_extends_topChains {o : Ontology} {b : Bool}
    (h : RoleHierarchy.decideAfterErasingTopChains? o = Option.some b) :
    decideWithUniversalRole? o = Option.some b :=
  decideAfterExpandingUniversalRole_extends_admitted h

#print axioms freshObjProp_core
#print axioms freshObjProp_not_mem
#print axioms models_withUniversalRole_iff
#print axioms expandTopRestrictions_sat_iff
#print axioms expandTopRestrictions_isSROIQD
#print axioms decideSROIQDWithTopBool_iff
#print axioms decideAfterExpandingUniversalRole_iff
#print axioms decideAfterExpandingUniversalRole_unsat_iff
#print axioms decideAfterExpandingUniversalRole_extends_aliases
#print axioms decideAfterExpandingUniversalRole_extends_admitted
#print axioms decideWithUniversalRole_iff
#print axioms decideWithUniversalRole_unsat_iff
#print axioms decideWithUniversalRole_extends_topChains

end Termination.BlockedForest
end Sabrina.OWL2.SROIQD
