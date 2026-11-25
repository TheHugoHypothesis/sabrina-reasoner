import Sabrina.OWL2.SROIQD.Semantics
import Sabrina.RoleChains.Regularity

/-! Eliminate the empty object and data relations from normalized problems.
A chain with an empty step is vacuous. A chain into the empty relation
forbids the corresponding nested existential. These rewrites preserve each
interpretation, including its named individuals and datatype map. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole)
open Sabrina.OWL2.Datatypes (datatypeMap)

private theorem not_bottomRole {dm : DatatypeMap} (i : Interpretation dm)
    (r : OrientedRole) (hr : r.1 = bottomObjectProperty) (x y : i.Object) :
    ¬ holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩
  · change ¬ i.objectProperties name x y
    rw [show name = bottomObjectProperty from hr]
    exact i.bottomObjectExt x y
  · change ¬ i.objectProperties name y x
    rw [show name = bottomObjectProperty from hr]
    exact i.bottomObjectExt y x

private theorem atLeast_empty {α : Type} {p : α → Prop} (hn : ∀ x, ¬ p x) (n : Nat) :
    AtLeast n p ↔ n = 0 := by
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ => ⟨[], rfl, List.nodup_nil, by simp⟩⟩
  | succ n =>
    constructor
    · rintro ⟨xs, hlen, _, hmem⟩
      cases xs with
      | nil => simp at hlen
      | cons x xs => exact (hn x (hmem x (List.mem_cons_self ..))).elim
    · simp

private theorem atLeast_congr {α : Type} {p q : α → Prop} (h : ∀ x, p x ↔ q x) (n : Nat) :
    AtLeast n p ↔ AtLeast n q := by
  simp only [AtLeast, h]

def Concept.lowerBottom : Concept → Concept
  | .self r b => if r.1 = bottomObjectProperty then (if b then .bottom else .top) else .self r b
  | .conj a b => .conj a.lowerBottom b.lowerBottom
  | .disj a b => .disj a.lowerBottom b.lowerBottom
  | .some r c => if r.1 = bottomObjectProperty then .bottom else .some r c.lowerBottom
  | .all r c => if r.1 = bottomObjectProperty then .top else .all r c.lowerBottom
  | .min n r c =>
    if r.1 = bottomObjectProperty then (if n = 0 then .top else .bottom) else .min n r c.lowerBottom
  | .max n r c => if r.1 = bottomObjectProperty then .top else .max n r c.lowerBottom
  | .dataSome r d => if r = bottomDataProperty then .bottom else .dataSome r d
  | .dataAll r d => if r = bottomDataProperty then .top else .dataAll r d
  | .dataValue r l b =>
    if r = bottomDataProperty then (if b then .bottom else .top) else .dataValue r l b
  | .dataMin n r d =>
    if r = bottomDataProperty then (if n = 0 then .top else .bottom) else .dataMin n r d
  | .dataMax n r d => if r = bottomDataProperty then .top else .dataMax n r d
  | c => c

theorem holds_lowerBottom_iff {dm : DatatypeMap} (i : Interpretation dm) (x : i.Object) (c : Concept) :
    holds i x c.lowerBottom ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom | lit | nom => rfl
  | self r b =>
    by_cases hr : r.1 = bottomObjectProperty <;> cases b <;>
      simp [Concept.lowerBottom, hr, holds, not_bottomRole i r]
  | conj a b ha hb => exact and_congr (ha x) (hb x)
  | disj a b ha hb => exact or_congr (ha x) (hb x)
  | some r c ih | all r c ih =>
    by_cases hr : r.1 = bottomObjectProperty <;>
      simp [Concept.lowerBottom, hr, holds, not_bottomRole i r, ih]
  | min n r c ih =>
    by_cases hr : r.1 = bottomObjectProperty
    · have h := atLeast_empty (p := fun y => holdsOriented i r x y ∧ holds i y c)
        (fun y hy => not_bottomRole i r hr x y hy.1) n
      rw [show holds i x (.min n r c) ↔ n = 0 from h]
      by_cases hn : n = 0 <;> simp [Concept.lowerBottom, hr, holds, hn]
    · simpa only [Concept.lowerBottom, hr, ite_false, holds] using
        atLeast_congr (fun y => and_congr Iff.rfl (ih y)) n
  | max n r c ih =>
    by_cases hr : r.1 = bottomObjectProperty
    · have h := atLeast_empty (p := fun y => holdsOriented i r x y ∧ holds i y c)
        (fun y hy => not_bottomRole i r hr x y hy.1) (n + 1)
      simp [Concept.lowerBottom, hr, holds, h]
    · simpa only [Concept.lowerBottom, hr, ite_false, holds] using
        not_congr (atLeast_congr (fun y => and_congr Iff.rfl (ih y)) (n + 1))
  | dataSome r d | dataAll r d =>
    by_cases hr : r = bottomDataProperty <;>
      simp [Concept.lowerBottom, hr, holds, i.bottomDataExt]
  | dataValue r l b =>
    by_cases hr : r = bottomDataProperty <;> cases b <;>
      simp [Concept.lowerBottom, hr, holds, i.bottomDataExt]
  | dataMin n r d =>
    by_cases hr : r = bottomDataProperty
    · have h := atLeast_empty (p := fun y => i.dataProperties r x y ∧ dataHolds i y d)
        (fun y hy => i.bottomDataExt x y (hr ▸ hy.1)) n
      rw [show holds i x (.dataMin n r d) ↔ n = 0 from h]
      by_cases hn : n = 0 <;> simp [Concept.lowerBottom, hr, holds, hn]
    · simp [Concept.lowerBottom, hr]
  | dataMax n r d =>
    by_cases hr : r = bottomDataProperty
    · have h := atLeast_empty (p := fun y => i.dataProperties r x y ∧ dataHolds i y d)
        (fun y hy => i.bottomDataExt x y (hr ▸ hy.1)) (n + 1)
      simp only [Concept.lowerBottom, ite_eq_left hr, holds, h, Nat.succ_ne_zero, not_false_eq_true]
    · simp [Concept.lowerBottom, hr]

/-- A normalized constraint can be retained, discarded, or replaced by
a global prohibition on a concept. -/
inductive Reduction where
  | keep
  | discard
  | forbid (c : Concept)

def retained (f : α → Reduction) (xs : List α) : List α :=
  xs.filter fun a => match f a with | .keep => true | _ => false

def prohibitions (f : α → Reduction) (xs : List α) : List Concept :=
  xs.filterMap fun a => match f a with | .forbid c => some c | _ => none

private theorem reduction_iff {dm : DatatypeMap} (i : Interpretation dm) (f : α → Reduction)
    (xs : List α) (P : α → Prop)
    (h : ∀ a, P a ↔ match f a with
      | .keep => P a
      | .discard => True
      | .forbid c => ∀ x, ¬ holds i x c) :
    (∀ a ∈ xs, P a) ↔
      (∀ a ∈ retained f xs, P a) ∧ ∀ c ∈ prohibitions f xs, ∀ x, ¬ holds i x c := by
  constructor
  · intro hp
    refine ⟨fun a ha => hp a (List.mem_filter.mp ha).1, ?_⟩
    intro c hc
    obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hc
    have hpa := (h a).mp (hp a ha)
    cases hf : f a <;> simp [hf] at he hpa
    exact he ▸ hpa
  · rintro ⟨hk, hf⟩ a ha
    apply (h a).mpr
    cases he : f a with
    | keep => exact hk a (List.mem_filter.mpr ⟨ha, by simp [he]⟩)
    | discard => trivial
    | forbid c => exact hf c (List.mem_filterMap.mpr ⟨a, ha, by simp [he]⟩)

def reduceUnless (bad : α → Bool) (a : α) : Reduction :=
  if bad a then .discard else .keep

def forbidWhen (bad : α → Bool) (a : α) : Reduction :=
  if bad a then .forbid .top else .keep

def isBottomObj (r : IRI) : Bool := r == bottomObjectProperty
def isBottomData (r : IRI) : Bool := r == bottomDataProperty

def bottomRule (rs : OrientedRole × OrientedRole) : Reduction :=
  if isBottomObj rs.1.1 then .discard
  else if isBottomObj rs.2.1 then .forbid (.some rs.1 .top)
  else .keep

def bottomChain (c : RoleChains.Chain) : Reduction :=
  if c.body.any (fun r => isBottomObj r.1) then .discard
  else if isBottomObj c.head then .forbid (c.body.foldr Concept.some .top)
  else .keep

def bottomSubData (rs : IRI × IRI) : Reduction :=
  if isBottomData rs.1 then .discard
  else if isBottomData rs.2 then .forbid (.dataSome rs.1 (.datatype literalDatatype))
  else .keep

def bottomKey (k : KeyAxiom) : Reduction :=
  reduceUnless (fun k => k.objProps.any (fun r => isBottomObj r.1) ||
    k.dataProps.any isBottomData) k

/-- Remove empty relations from a normalized problem. The source hierarchy
remains available to callers for structural validation before this pass. -/
def Problem.lowerBottom (p : Problem) : Problem :=
  let extra := prohibitions bottomRule p.rules ++
    prohibitions bottomChain p.chains ++
    prohibitions (forbidWhen isBottomObj) p.chars.reflexive ++
    prohibitions bottomSubData p.subData ++
    prohibitions (forbidWhen fun (e : IRI × Individual × Individual) => isBottomObj e.1)
      p.objAssertions ++
    prohibitions (forbidWhen fun (e : IRI × Individual × Literal) => isBottomData e.1)
      p.dataAssertions
  { p with
    tbox := p.tbox.map (fun q => ⟨q.sub.lowerBottom, q.sup.lowerBottom⟩) ++
      extra.map (fun c => ⟨c, .bottom⟩)
    rules := retained bottomRule p.rules
    chains := retained bottomChain p.chains
    chars := {
      reflexive := retained (forbidWhen isBottomObj) p.chars.reflexive
      irreflexive := retained (reduceUnless isBottomObj) p.chars.irreflexive
      asymmetric := retained (reduceUnless isBottomObj) p.chars.asymmetric
      disjoint := retained (reduceUnless fun rs => isBottomObj rs.1.1 || isBottomObj rs.2.1)
        p.chars.disjoint }
    subData := retained bottomSubData p.subData
    disjointData := retained (reduceUnless fun rs => isBottomData rs.1 || isBottomData rs.2)
      p.disjointData
    funcData := retained (reduceUnless isBottomData) p.funcData
    dataRanges := retained (reduceUnless fun rd => isBottomData rd.1) p.dataRanges
    keys := (retained bottomKey p.keys).map fun k => {k with cls := k.cls.lowerBottom}
    classAssertions := p.classAssertions.map fun (a, c) => (a, c.lowerBottom)
    objAssertions := retained (forbidWhen fun e => isBottomObj e.1) p.objAssertions
    negObjAssertions := retained (reduceUnless fun e => isBottomObj e.1) p.negObjAssertions
    dataAssertions := retained (forbidWhen fun e => isBottomData e.1) p.dataAssertions
    negDataAssertions := retained (reduceUnless fun e => isBottomData e.1) p.negDataAssertions
    root := p.root.lowerBottom }

theorem Problem.checkRegular_lowerBottom {p : Problem} {rank : RoleChains.Rank}
    (h : RoleChains.checkRegular rank p.rules p.chains = true) :
    RoleChains.checkRegular rank p.lowerBottom.rules p.lowerBottom.chains = true := by
  have hr := RoleChains.checkRegular_iff.mp h
  exact RoleChains.checkRegular_iff.mpr
    ⟨fun r s hm => hr.1 r s (List.mem_filter.mp hm).1,
     fun c hm => hr.2 c (List.mem_filter.mp hm).1⟩

private theorem bottom_obj_eq {r : IRI} (hr : isBottomObj r = true) :
    r = bottomObjectProperty := beq_iff_eq.mp hr

private theorem bottom_data_eq {r : IRI} (hr : isBottomData r = true) :
    r = bottomDataProperty := beq_iff_eq.mp hr

private theorem retained_unless_iff (bad : α → Bool) (xs : List α) (P : α → Prop)
    (h : ∀ a, bad a = true → P a) :
    (∀ a ∈ xs, P a) ↔ ∀ a ∈ retained (reduceUnless bad) xs, P a := by
  constructor
  · intro hp a ha
    exact hp a (List.mem_filter.mp ha).1
  · intro hp a ha
    by_cases hbad : bad a = true
    · exact h a hbad
    · exact hp a (List.mem_filter.mpr ⟨ha, by simp [reduceUnless, hbad]⟩)

private theorem forbidWhen_iff {dm : DatatypeMap} (i : Interpretation dm)
    (bad : α → Bool) (P : α → Prop) (a : α) (h : bad a = true → ¬ P a) :
    P a ↔ match forbidWhen bad a with
      | .keep => P a
      | .discard => True
      | .forbid c => ∀ x, ¬ holds i x c := by
  by_cases hb : bad a = true
  · simp only [forbidWhen, ite_eq_left hb]
    exact ⟨fun hp => (h hb hp).elim, fun hf =>
      i.objectNonempty.elim fun x => (hf x trivial).elim⟩
  · simp [forbidWhen, hb]

private theorem bottomRule_iff {dm : DatatypeMap} (i : Interpretation dm) (rs : OrientedRole × OrientedRole) :
    (∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y) ↔
    match bottomRule rs with
    | .keep => ∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y
    | .discard => True
    | .forbid c => ∀ x, ¬ holds i x c := by
  by_cases hl : isBottomObj rs.1.1 = true
  · simp only [bottomRule, ite_eq_left hl]
    exact ⟨fun _ => trivial, fun _ x y hxy => (not_bottomRole i _ (bottom_obj_eq hl) x y hxy).elim⟩
  · by_cases hr : isBottomObj rs.2.1 = true
    · simp only [bottomRule, ite_eq_right hl, ite_eq_left hr, holds]
      exact ⟨fun h x ⟨y, hy, _⟩ => not_bottomRole i _ (bottom_obj_eq hr) x y (h x y hy),
        fun h x y hy => (h x ⟨y, hy, trivial⟩).elim⟩
    · simp [bottomRule, hl, hr]

private theorem path_without_bottom {dm : DatatypeMap} (i : Interpretation dm) {rs : List OrientedRole}
    (h : rs.any (fun r => isBottomObj r.1) = true) (x y : i.Object) :
    ¬ objPath i rs x y := by
  induction rs generalizing x with
  | nil => simp at h
  | cons r rs ih =>
    intro ⟨z, hr, hz⟩
    rcases Bool.or_eq_true_iff.mp h with he | ht
    · exact not_bottomRole i r (bottom_obj_eq he) x z hr
    · exact ih ht z hz

private theorem holds_path {dm : DatatypeMap} (i : Interpretation dm) (rs : List OrientedRole)
    (x : i.Object) :
    holds i x (rs.foldr Concept.some .top) ↔ ∃ y, objPath i rs x y := by
  induction rs generalizing x with
  | nil => simp [holds, objPath]
  | cons r rs ih =>
    change (∃ z, holdsOriented i r x z ∧ holds i z (rs.foldr Concept.some .top)) ↔
      ∃ y z, holdsOriented i r x z ∧ objPath i rs z y
    constructor
    · rintro ⟨z, hr, hp⟩
      obtain ⟨y, hy⟩ := (ih z).mp hp
      exact ⟨y, z, hr, hy⟩
    · rintro ⟨y, z, hr, hy⟩
      exact ⟨z, hr, (ih z).mpr ⟨y, hy⟩⟩

private theorem bottomChain_iff {dm : DatatypeMap} (i : Interpretation dm) (c : RoleChains.Chain) :
    (∀ x y, objPath i c.body x y → i.objectProperties c.head x y) ↔
    match bottomChain c with
    | .keep => ∀ x y, objPath i c.body x y → i.objectProperties c.head x y
    | .discard => True
    | .forbid d => ∀ x, ¬ holds i x d := by
  by_cases hb : c.body.any (fun r => isBottomObj r.1) = true
  · simp only [bottomChain, ite_eq_left hb]
    exact ⟨fun _ => trivial, fun _ x y h => (path_without_bottom i hb x y h).elim⟩
  · by_cases hh : isBottomObj c.head = true
    · simp only [bottomChain, ite_eq_right hb, ite_eq_left hh, holds_path]
      exact ⟨fun h x ⟨y, hy⟩ => i.bottomObjectExt x y (bottom_obj_eq hh ▸ h x y hy),
        fun h x y hy => (h x ⟨y, hy⟩).elim⟩
    · simp [bottomChain, hb, hh]

private theorem bottomSubData_iff {dm : DatatypeMap} (i : Interpretation dm) (rs : IRI × IRI) :
    (∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y) ↔
    match bottomSubData rs with
    | .keep => ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y
    | .discard => True
    | .forbid c => ∀ x, ¬ holds i x c := by
  by_cases hl : isBottomData rs.1 = true
  · simp only [bottomSubData, ite_eq_left hl]
    exact ⟨fun _ => trivial, fun _ x y hy => (i.bottomDataExt x y (bottom_data_eq hl ▸ hy)).elim⟩
  · by_cases hr : isBottomData rs.2 = true
    · simp only [bottomSubData, ite_eq_right hl, ite_eq_left hr, holds]
      exact ⟨fun h x ⟨y, hy, _⟩ => i.bottomDataExt x y (bottom_data_eq hr ▸ h x y hy),
        fun h x y hy => (h x ⟨y, hy, i.literalDatatypeExt y⟩).elim⟩
    · simp [bottomSubData, hl, hr]

private def keyHolds {dm : DatatypeMap} (i : Interpretation dm) (k : KeyAxiom) : Prop :=
  ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
    (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
    (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y

private theorem lowerKeys_iff {dm : DatatypeMap} (i : Interpretation dm) (keys : List KeyAxiom) :
    (∀ k ∈ keys, keyHolds i k) ↔
      ∀ k ∈ (retained bottomKey keys).map (fun k => {k with cls := k.cls.lowerBottom}), keyHolds i k := by
  have localLower (k : KeyAxiom) :
      keyHolds i k ↔ keyHolds i { k with cls := k.cls.lowerBottom } := by
    simp only [keyHolds, holds_lowerBottom_iff]
  have hdiscard := retained_unless_iff
    (fun k : KeyAxiom => k.objProps.any (fun r => isBottomObj r.1) || k.dataProps.any isBottomData)
    keys (keyHolds i) (by
      intro k hk x y _ _ _ _ ho hd
      rcases Bool.or_eq_true_iff.mp hk with h | h
      · obtain ⟨r, hr, hz⟩ := List.any_eq_true.mp h
        obtain ⟨z, _, hxz, _⟩ := ho r hr
        exact (not_bottomRole i r (bottom_obj_eq hz) x z hxz).elim
      · obtain ⟨r, hr, hz⟩ := List.any_eq_true.mp h
        obtain ⟨z, hxz, _⟩ := hd r hr
        exact (i.bottomDataExt x z (bottom_data_eq hz ▸ hxz)).elim)
  refine hdiscard.trans ?_
  simp only [List.forall_mem_map]
  exact forall_congr' fun k => imp_congr Iff.rfl (localLower k)

theorem Problem.lowerBottom_models_iff {dm : DatatypeMap} (p : Problem) (i : Interpretation dm) :
    p.lowerBottom.Models i ↔ p.Models i := by
  have hr := reduction_iff i bottomRule p.rules _ (bottomRule_iff i)
  have hc := reduction_iff i bottomChain p.chains _ (bottomChain_iff i)
  have hre := reduction_iff i (forbidWhen isBottomObj) p.chars.reflexive
    (fun r => ∀ x, i.objectProperties r x x) (fun r =>
      forbidWhen_iff i isBottomObj (fun r => ∀ x, i.objectProperties r x x) r fun hb h =>
        i.objectNonempty.elim fun x => i.bottomObjectExt x x (bottom_obj_eq hb ▸ h x))
  have hir := retained_unless_iff isBottomObj p.chars.irreflexive
    (fun r => ∀ x, ¬ i.objectProperties r x x) (fun _ hb x h =>
      i.bottomObjectExt x x (bottom_obj_eq hb ▸ h))
  have has := retained_unless_iff isBottomObj p.chars.asymmetric
    (fun r => ∀ x y, i.objectProperties r x y → ¬ i.objectProperties r y x)
    (fun _ hb x y h => (i.bottomObjectExt x y (bottom_obj_eq hb ▸ h)).elim)
  have hdis := retained_unless_iff (fun (rs : OrientedRole × OrientedRole) =>
    isBottomObj rs.1.1 || isBottomObj rs.2.1) p.chars.disjoint
      (fun rs => ∀ x y, ¬ (holdsOriented i rs.1 x y ∧ holdsOriented i rs.2 x y)) (by
        intro rs hb x y h
        rcases Bool.or_eq_true_iff.mp hb with h₁ | h₂
        · exact not_bottomRole i _ (bottom_obj_eq h₁) x y h.1
        · exact not_bottomRole i _ (bottom_obj_eq h₂) x y h.2)
  have hsd := reduction_iff i bottomSubData p.subData _ (bottomSubData_iff i)
  have hdd := retained_unless_iff (fun (rs : IRI × IRI) =>
    isBottomData rs.1 || isBottomData rs.2) p.disjointData
      (fun rs => ∀ x y, ¬ (i.dataProperties rs.1 x y ∧ i.dataProperties rs.2 x y)) (by
        intro rs hb x y h
        rcases Bool.or_eq_true_iff.mp hb with h₁ | h₂
        · exact i.bottomDataExt x y (bottom_data_eq h₁ ▸ h.1)
        · exact i.bottomDataExt x y (bottom_data_eq h₂ ▸ h.2))
  have hfd := retained_unless_iff isBottomData p.funcData
    (fun r => ∀ x y z, i.dataProperties r x y → i.dataProperties r x z → y = z)
      (fun _ hb x y _ h => (i.bottomDataExt x y (bottom_data_eq hb ▸ h)).elim)
  have hdr := retained_unless_iff (fun rd => isBottomData rd.1) p.dataRanges
    (fun rd => ∀ x y, i.dataProperties rd.1 x y → dataHolds i y rd.2)
      (fun _ hb x y h => (i.bottomDataExt x y (bottom_data_eq hb ▸ h)).elim)
  have hk := lowerKeys_iff i p.keys
  have hca :
      (∀ ac ∈ p.classAssertions, holds i (i.individuals ac.1) ac.2) ↔
        ∀ ac ∈ p.lowerBottom.classAssertions, holds i (i.individuals ac.1) ac.2 := by
    simp only [Problem.lowerBottom, List.forall_mem_map, holds_lowerBottom_iff]
  have hoa := reduction_iff i (forbidWhen fun e => isBottomObj e.1) p.objAssertions
    (fun e => i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2))
    (fun e => forbidWhen_iff i (fun e => isBottomObj e.1)
      (fun e => i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2)) e fun hb h =>
      i.bottomObjectExt _ _ (bottom_obj_eq hb ▸ h))
  have hno := retained_unless_iff (fun e => isBottomObj e.1) p.negObjAssertions
    (fun e => ¬ i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2))
    (fun _ hb h => i.bottomObjectExt _ _ (bottom_obj_eq hb ▸ h))
  have hda := reduction_iff i (forbidWhen fun e => isBottomData e.1) p.dataAssertions
    (fun e => i.dataProperties e.1 (i.individuals e.2.1) (i.literalValue e.2.2))
    (fun e => forbidWhen_iff i (fun e => isBottomData e.1)
      (fun e => i.dataProperties e.1 (i.individuals e.2.1) (i.literalValue e.2.2)) e fun hb h =>
      i.bottomDataExt _ _ (bottom_data_eq hb ▸ h))
  have hnd := retained_unless_iff (fun e => isBottomData e.1) p.negDataAssertions
    (fun e => ¬ i.dataProperties e.1 (i.individuals e.2.1) (i.literalValue e.2.2))
    (fun _ hb h => i.bottomDataExt _ _ (bottom_data_eq hb ▸ h))
  constructor
  · intro h
    have ht := h.tbox
    simp only [Problem.lowerBottom, List.forall_mem_append, List.forall_mem_map,
      holds_lowerBottom_iff, holds, and_assoc] at ht
    obtain ⟨htbox, hpr, hpc, hpre, hpsd, hpo, hpd⟩ := ht
    exact ⟨htbox, hr.mpr ⟨h.rules, hpr⟩, hc.mpr ⟨h.chains, hpc⟩,
      hre.mpr ⟨h.reflexive, hpre⟩, hir.mpr h.irreflexive, has.mpr h.asymmetric,
      hdis.mpr h.disjoint, hsd.mpr ⟨h.subData, hpsd⟩, hdd.mpr h.disjointData,
      hfd.mpr h.funcData, hdr.mpr h.dataRanges, hk.mpr h.keys, hca.mpr h.classAssertions,
      hoa.mpr ⟨h.objAssertions, hpo⟩, hno.mpr h.negObjAssertions, h.sameInds, h.diffInds,
      hda.mpr ⟨h.dataAssertions, hpd⟩, hnd.mpr h.negDataAssertions⟩
  · intro h
    obtain ⟨hrule, hpr⟩ := hr.mp h.rules
    obtain ⟨hchain, hpc⟩ := hc.mp h.chains
    obtain ⟨href, hpre⟩ := hre.mp h.reflexive
    obtain ⟨hsub, hpsd⟩ := hsd.mp h.subData
    obtain ⟨hobj, hpo⟩ := hoa.mp h.objAssertions
    obtain ⟨hdata, hpd⟩ := hda.mp h.dataAssertions
    refine ⟨?_, hrule, hchain, href, hir.mp h.irreflexive, has.mp h.asymmetric,
      hdis.mp h.disjoint, hsub, hdd.mp h.disjointData, hfd.mp h.funcData, hdr.mp h.dataRanges,
      hk.mp h.keys, hca.mp h.classAssertions, hobj, hno.mp h.negObjAssertions, h.sameInds,
      h.diffInds, hdata, hnd.mp h.negDataAssertions⟩
    simp only [Problem.lowerBottom, List.forall_mem_append, List.forall_mem_map,
      holds_lowerBottom_iff, holds, and_assoc]
    exact ⟨h.tbox, hpr, hpc, hpre, hpsd, hpo, hpd⟩

theorem Problem.lowerBottom_satWith_iff {dm : DatatypeMap} (p : Problem) :
    p.lowerBottom.SatWith dm ↔ p.SatWith dm := by
  simp only [Problem.SatWith, Problem.lowerBottom_models_iff]
  exact exists_congr fun i => and_congr Iff.rfl
    (exists_congr fun x => holds_lowerBottom_iff i x p.root)

theorem Problem.lowerBottom_sat_iff (p : Problem) : p.lowerBottom.Sat ↔ p.Sat :=
  p.lowerBottom_satWith_iff

#print axioms holds_lowerBottom_iff
#print axioms Problem.lowerBottom_models_iff
#print axioms Problem.lowerBottom_satWith_iff
#print axioms Problem.lowerBottom_sat_iff

end Sabrina.OWL2.SROIQD
