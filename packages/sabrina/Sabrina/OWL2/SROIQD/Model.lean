import Sabrina.OWL2.SROIQD.Semantics
import Sabrina.RoleChains.Model

/-! Finite model checker for unified SROIQ(D) problems, proved sound directly
    against OWL 2 Direct Semantics over the 33-datatype map. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole)
open Sabrina.RoleChains (Graph checkRoleAxioms checkRoleAxioms_iff)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)
open Sabrina.OWL2.DataRanges (compile Compiled)

/-- Positive atomic, nominal, self, and data-value conjunctions (of arbitrary arity)
    can be tested directly against node labels without splitting inactive antecedents. -/
def Concept.absorptionPremises : Concept → Option (List Concept)
  | .lit a true => Option.some [.atom a]
  | .nom ind true => Option.some [.nom ind true]
  | .self r true => Option.some [.self r true]
  | .dataValue dp l true => Option.some [.dataValue dp l true]
  | .conj a b => do
    let pa ← a.absorptionPremises
    let pb ← b.absorptionPremises
    return pa ++ pb
  | _ => none

theorem Concept.absorptionPremises_sound {c : Concept} {ps : List Concept}
    (h : c.absorptionPremises = Option.some ps) (i : Interpretation datatypeMap) (x : i.Object)
    (hp : ∀ d ∈ ps, holds i x d) : holds i x c := by
  induction c generalizing ps with
  | lit a b =>
    cases b <;> simp [Concept.absorptionPremises] at h
    subst ps
    exact hp _ (by simp)
  | nom ind b =>
    cases b <;> simp [Concept.absorptionPremises] at h
    subst ps
    exact hp _ (by simp)
  | self r b =>
    cases b <;> simp [Concept.absorptionPremises] at h
    subst ps
    exact hp _ (by simp)
  | dataValue dp l b =>
    cases b <;> simp [Concept.absorptionPremises] at h
    subst ps
    exact hp _ (by simp)
  | conj a b iha ihb =>
    simp only [Concept.absorptionPremises, bind, Option.bind, pure] at h
    cases ha : a.absorptionPremises with
    | none => rw [ha] at h; cases h
    | some pa =>
      rw [ha] at h; dsimp only at h
      cases hb : b.absorptionPremises with
      | none => rw [hb] at h; cases h
      | some pb =>
        rw [hb] at h; dsimp only at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨iha ha fun d hd => hp d (List.mem_append_left _ hd),
               ihb hb fun d hd => hp d (List.mem_append_right _ hd)⟩
  | _ => simp [Concept.absorptionPremises] at h

/-- Extract a finite disjunction of positive nominals `(a₁ ⊔ … ⊔ aₖ)` (including a singleton `{a}`). -/
def Concept.nominalDisj? : Concept → Option (List Individual)
  | .nom a true => Option.some [a]
  | .disj a b => do
    let ia ← a.nominalDisj?
    let ib ← b.nominalDisj?
    return ia ++ ib
  | _ => none

theorem Concept.nominalDisj?_sound {c : Concept} {inds : List Individual}
    (h : c.nominalDisj? = Option.some inds) (i : Interpretation datatypeMap) (x : i.Object)
    {a : Individual} (ha : a ∈ inds) (hnom : holds i x (.nom a true)) :
    holds i x c := by
  induction c generalizing inds with
  | nom ind b =>
    cases b <;> simp [Concept.nominalDisj?] at h
    subst inds
    rcases List.mem_singleton.mp ha with rfl
    exact hnom
  | disj l r ihl ihr =>
    simp only [Concept.nominalDisj?, bind, Option.bind, pure] at h
    cases hl : l.nominalDisj? with
    | none => rw [hl] at h; cases h
    | some il =>
      rw [hl] at h; dsimp only at h
      cases hr : r.nominalDisj? with
      | none => rw [hr] at h; cases h
      | some ir =>
        rw [hr] at h; dsimp only at h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp ha with hal | har
        · exact Or.inl (ihl hl hal)
        · exact Or.inr (ihr hr har)
  | _ => simp [Concept.nominalDisj?] at h

/-- Extract a nominal guard `(inds, rest)` from a nominal-anchored antecedent such as
    `{a} ⊓ B` or `({a₁} ⊔ … ⊔ {aₖ}) ⊓ B`, where `B` may be an arbitrary complex concept. -/
def Concept.nominalGuard? : Concept → Option (List Individual × Concept)
  | .nom a true => Option.some ([a], .top)
  | .disj a b => (Concept.nominalDisj? (.disj a b)).map (·, .top)
  | .conj a b =>
    match a.nominalDisj? with
    | Option.some inds => Option.some (inds, b)
    | Option.none =>
      match b.nominalDisj? with
      | Option.some inds => Option.some (inds, a)
      | Option.none =>
        match a.nominalGuard? with
        | Option.some (inds, rest) => Option.some (inds, if rest == .top then b else .conj rest b)
        | Option.none =>
          match b.nominalGuard? with
          | Option.some (inds, rest) => Option.some (inds, if rest == .top then a else .conj a rest)
          | Option.none => Option.none
  | _ => Option.none

theorem Concept.nominalGuard?_sound {c : Concept} {inds : List Individual} {rest : Concept}
    (h : c.nominalGuard? = Option.some (inds, rest)) (i : Interpretation datatypeMap) (x : i.Object)
    {a : Individual} (ha : a ∈ inds) (hnom : holds i x (.nom a true)) (hrest : holds i x rest) :
    holds i x c := by
  induction c generalizing inds rest with
  | nom ind b =>
    cases b <;> simp [Concept.nominalGuard?] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases List.mem_singleton.mp ha with rfl
    exact hnom
  | disj l r _ _ =>
    simp only [Concept.nominalGuard?, Option.map_eq_some_iff] at h
    obtain ⟨ds, hds, hpair⟩ := h
    cases hpair
    exact Concept.nominalDisj?_sound hds i x ha hnom
  | conj l r ihl ihr =>
    simp only [Concept.nominalGuard?] at h
    cases hld : l.nominalDisj? with
    | some il =>
      rw [hld] at h; dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Concept.nominalDisj?_sound hld i x ha hnom, hrest⟩
    | none =>
      rw [hld] at h; dsimp only at h
      cases hrd : r.nominalDisj? with
      | some ir =>
        rw [hrd] at h; dsimp only at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hrest, Concept.nominalDisj?_sound hrd i x ha hnom⟩
      | none =>
        rw [hrd] at h; dsimp only at h
        cases hlg : l.nominalGuard? with
        | some pl =>
          rcases pl with ⟨il, rl⟩
          rw [hlg] at h; dsimp only at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          by_cases htop : rl == .top
          · simp only [htop, ↓reduceIte] at hrest
            have hrl : rl = .top := beq_iff_eq.mp htop
            exact ⟨ihl hlg ha (hrl ▸ trivial), hrest⟩
          · simp only [htop, Bool.false_eq_true, ↓reduceIte] at hrest
            exact ⟨ihl hlg ha hrest.1, hrest.2⟩
        | none =>
          rw [hlg] at h; dsimp only at h
          cases hrg : r.nominalGuard? with
          | some pr =>
            rcases pr with ⟨ir, rr⟩
            rw [hrg] at h; dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            by_cases htop : rr == .top
            · simp only [htop, ↓reduceIte] at hrest
              have hrr : rr = .top := beq_iff_eq.mp htop
              exact ⟨hrest, ihr hrg ha (hrr ▸ trivial)⟩
            · simp only [htop, Bool.false_eq_true, ↓reduceIte] at hrest
              exact ⟨hrest.1, ihr hrg ha hrest.2⟩
          | none => rw [hrg] at h; cases h
  | _ => simp [Concept.nominalGuard?] at h

/-- Prefer the whole antecedent if it is already labelled, otherwise try
    unfolding the positive atomic/nominal premises of an absorbable conjunction. -/
def Concept.triggeringPremises (c : Concept) (known : Concept → Bool)
    (absorb : Bool := true) :
    Option { ps : List Concept // (∀ d ∈ ps, known d = true) ∧
      ∀ (i : Interpretation datatypeMap) (x : i.Object), (∀ d ∈ ps, holds i x d) → holds i x c } :=
  if hc : known c then
    Option.some ⟨[c], fun _ hd => (List.mem_singleton.mp hd).symm ▸ hc,
      fun _ _ hp => hp c (List.mem_singleton_self _)⟩
  else if absorb then
    match h : c.absorptionPremises with
    | none => none
    | .some ps =>
      if hp : ps.all known then
        Option.some ⟨ps, List.all_eq_true.mp hp, Concept.absorptionPremises_sound h⟩
      else none
  else none

/-- A local contradiction with explicit label dependencies. Its proof holds at
    any object in any model of the problem, regardless of the branch's node IDs. -/
structure NodeClash (p : Problem) where
  node : Nat
  premises : List Concept
  sound : ∀ (i : Interpretation datatypeMap), p.Models i → ∀ x : i.Object,
    (∀ c ∈ premises, holds i x c) → False

def NodeClash.bottom (p : Problem) (node : Nat) : NodeClash p :=
  ⟨node, [.bottom], fun _ _ _ hs => hs .bottom (by simp)⟩

def NodeClash.dual (p : Problem) (node : Nat) (c : Concept) : NodeClash p :=
  ⟨node, [c, c.dual], fun i _ x hs => (holds_dual i x c).mp (hs _ (by simp)) (hs _ (by simp))⟩

/-- Premises and alternatives of a rule that adds a label to one node. This
    information lets search discharge a choice from a downstream conflict. -/
structure LocalLabelRule (p : Problem) where
  node : Nat
  premises : List Concept
  alternatives : List Concept
  sound : ∀ (i : Interpretation datatypeMap), p.Models i → ∀ x : i.Object,
    (∀ c ∈ premises, holds i x c) → ∃ c ∈ alternatives, holds i x c

def LocalLabelRule.unary {p : Problem} (node : Nat) (ps : List Concept) (c : Concept)
    (deriveLabel : ∀ (i : Interpretation datatypeMap), p.Models i → ∀ x : i.Object,
      (∀ d ∈ ps, holds i x d) → holds i x c) : LocalLabelRule p :=
  ⟨node, ps, [c], fun i hm x hp => ⟨c, by simp, deriveLabel i hm x hp⟩⟩

def LocalLabelRule.binary {p : Problem} (node : Nat) (ps : List Concept) (a b : Concept)
    (deriveChoice : ∀ (i : Interpretation datatypeMap), p.Models i → ∀ x : i.Object,
      (∀ d ∈ ps, holds i x d) → holds i x a ∨ holds i x b) : LocalLabelRule p :=
  ⟨node, ps, [a, b], fun i hm x hp => by
    rcases deriveChoice i hm x hp with ha | hb
    · exact ⟨a, by simp, ha⟩
    · exact ⟨b, by simp, hb⟩⟩

def LocalLabelRule.gci {p : Problem} (node : Nat) (q : Inclusion) (hq : q ∈ p.tbox) :
    LocalLabelRule p :=
  .binary node [] q.sub.dual q.sup fun i hm x _ => by
    classical
    by_cases hs : holds i x q.sub
    · exact .inr (hm.tbox q hq x hs)
    · exact .inl ((holds_dual i x q.sub).mpr hs)

def LocalLabelRule.split (p : Problem) (node : Nat) (c : Concept) : LocalLabelRule p :=
  .binary node [] c c.dual fun i _ x _ => by
    classical
    by_cases h : holds i x c
    · exact .inl h
    · exact .inr ((holds_dual i x c).mpr h)

private def dischargeAlternatives {p : Problem} (node : Nat) :
    (alternatives : List Concept) → List (Option (NodeClash p)) →
    Option { ps : List Concept // ∀ (i : Interpretation datatypeMap), p.Models i → ∀ x : i.Object,
      (∀ c ∈ ps, holds i x c) → ∀ c ∈ alternatives, ¬ holds i x c }
  | [], [] => some ⟨[], fun _ _ _ _ _ hc => nomatch hc⟩
  | a :: as, some clash :: rest => do
    if clash.node != node then none else
      let remaining ← dischargeAlternatives node as rest
      let ps := clash.premises.filter (· != a) ++ remaining.val
      return ⟨ps, fun i hm x hp c hc hholds => by
        rcases List.mem_cons.mp hc with rfl | hc
        · apply clash.sound i hm x
          intro d hd
          if he : d = c then exact he ▸ hholds
          else exact hp d (List.mem_append_left _ (List.mem_filter.mpr ⟨hd, by simp [he]⟩))
        · exact remaining.property i hm x (fun d hd => hp d (List.mem_append_right _ hd)) c hc hholds⟩
  | _, _ => none

/-- Resolve a local conflict in every alternative against the rule that split them. -/
def LocalLabelRule.resolve {p : Problem} (rule : LocalLabelRule p)
    (clashes : List (Option (NodeClash p))) : Option (NodeClash p) := do
  let remaining ← dischargeAlternatives rule.node rule.alternatives clashes
  return ⟨rule.node, (rule.premises ++ remaining.val).eraseDups, fun i hm x hp => by
    have labels (c : Concept) (hc : c ∈ rule.premises ++ remaining.val) : holds i x c :=
      hp c (List.mem_eraseDups.mpr hc)
    obtain ⟨c, hc, holdsC⟩ := rule.sound i hm x (fun c hc => labels c (List.mem_append_left _ hc))
    exact remaining.property i hm x (fun c hc => labels c (List.mem_append_right _ hc)) c hc holdsC⟩

structure SROIQDModel where
  graph : Graph
  nominals : List (IRI × graph.World) := []
  anons : List ((String × String) × graph.World) := []
  dataEdges : List (IRI × graph.World × Value) := []

def SROIQDModel.nomVal (m : SROIQDModel) (a : IRI) : m.graph.World :=
  (m.nominals.lookup a).getD ⟨0, Nat.zero_lt_succ _⟩

def SROIQDModel.anonVal (m : SROIQDModel) (k : String × String) : m.graph.World :=
  (m.anons.lookup k).getD ⟨0, Nat.zero_lt_succ _⟩

def SROIQDModel.indVal (m : SROIQDModel) : Individual → m.graph.World
  | .named a => m.nomVal a
  | .anonymous doc lid => m.anonVal (doc, lid)

def SROIQDModel.isNamedWorld (m : SROIQDModel) (x : m.graph.World) : Bool :=
  (x.val == 0) || m.nominals.any (fun (_, w) => w == x)

private theorem isNamedWorld_nomVal (m : SROIQDModel) (a : IRI) :
    m.isNamedWorld (m.nomVal a) = true := by
  unfold SROIQDModel.isNamedWorld SROIQDModel.nomVal
  cases h : m.nominals.lookup a with
  | none => simp
  | some w =>
    simp only [Option.getD_some, Bool.or_eq_true, List.any_eq_true]
    right
    have hmem : (a, w) ∈ m.nominals := by
      have aux : ∀ xs : List (IRI × m.graph.World), xs.lookup a = some w → (a, w) ∈ xs := fun xs hx => by
        induction xs with
        | nil => simp [List.lookup] at hx
        | cons hd tail ih =>
          rcases hd with ⟨k, v⟩
          simp only [List.lookup] at hx
          cases hb : (a == k) with
          | true =>
            simp only [hb, Option.some.injEq] at hx
            have hk := beq_iff_eq.mp hb; subst hk hx; exact List.mem_cons_self ..
          | false =>
            simp only [hb] at hx; exact List.mem_cons_of_mem _ (ih hx)
      exact aux m.nominals h
    exact ⟨(a, w), hmem, beq_self_eq_true w⟩

def SROIQDModel.hasDataEdge (m : SROIQDModel) (dp : IRI) (x : m.graph.World) (v : Value) : Bool :=
  m.dataEdges.any fun (r, w, val) => r == dp && w == x && val == v

def SROIQDModel.dataValues (m : SROIQDModel) (dp : IRI) (x : m.graph.World) : List Value :=
  (m.dataEdges.filterMap fun (r, w, val) =>
    if r == dp && w == x then some val else none).eraseDups

private theorem mem_dataValues_iff (m : SROIQDModel) (dp : IRI) (x : m.graph.World) (v : Value) :
    v ∈ m.dataValues dp x ↔ m.hasDataEdge dp x v = true := by
  simp only [SROIQDModel.dataValues, SROIQDModel.hasDataEdge, List.mem_eraseDups,
    List.mem_filterMap, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨r, w, val⟩, hmem, hif⟩
    split at hif
    · rename_i hcond
      cases hif
      exact ⟨(r, w, val), hmem, hcond, rfl⟩
    · cases hif
  · rintro ⟨⟨r, w, val⟩, hmem, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨(r, w, val), hmem, by simp⟩

abbrev SROIQDModel.toInterpretation (m : SROIQDModel) : Interpretation datatypeMap where
  Object := m.graph.World
  objectNonempty := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes r x := if r = thing then True else if r = nothing then False else m.graph.atom r x = true
  objectProperties r x y :=
    if r = topObjectProperty then True else if r = bottomObjectProperty then False
    else m.graph.edge r x y = true
  dataProperties r x y :=
    if r = topDataProperty then True else if r = bottomDataProperty then False
    else ∃ v, y = some v ∧ m.hasDataEdge r x v = true
  individuals := m.indVal
  datatypes t y := t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = y
  literalValue l := decodeLiteral l
  lexicalAgreement := fun _ _ h => h
  named x := m.isNamedWorld x = true
  namedIndividual a := isNamedWorld_nomVal m a
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

private def isOrdinaryClass (r : IRI) : Bool := r != thing && r != nothing
private def isOrdinaryObjProp (r : IRI) : Bool := r != topObjectProperty && r != bottomObjectProperty
private def isOrdinaryDataProp (r : IRI) : Bool := r != topDataProperty && r != bottomDataProperty

theorem nodup_eraseDups_list {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  have hrev : ∀ (l : List α), l.Nodup → l.reverse.Nodup := fun l hl => by
    rw [List.Nodup, List.pairwise_reverse]
    exact hl.imp fun h => h.symm
  have hloop : ∀ (l acc : List α), acc.Nodup →
      (List.eraseDupsBy.loop (· == ·) l acc).Nodup := by
    intro l
    induction l with
    | nil => intro acc hacc; exact hrev acc hacc
    | cons a tail ih =>
      intro acc hacc
      simp only [List.eraseDupsBy.loop]
      split
      · exact ih acc hacc
      · rename_i hnot
        refine ih (a :: acc) (List.nodup_cons.mpr ⟨?_, hacc⟩)
        intro hmem
        have ht := List.any_eq_true.mpr ⟨a, hmem, beq_self_eq_true a⟩
        rw [hnot] at ht; cases ht
  exact hloop xs [] List.nodup_nil

theorem nodup_map_inj {α β : Type} {f : α → β} (hinj : ∀ {x y}, f x = f y → x = y)
    {xs : List α} (h : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hm
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
    exact h.1 (hinj heq ▸ hb)

private theorem nodup_of_map {α β : Type} (f : α → β) {xs : List α} (h : (xs.map f).Nodup) :
    xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun hm => h.1 (List.mem_map_of_mem hm), ih h.2⟩

private theorem ordinaryClass_ne {r : IRI} (h : isOrdinaryClass r = true) :
    r ≠ thing ∧ r ≠ nothing := by
  simp only [isOrdinaryClass, Bool.and_eq_true, bne_iff_ne] at h; exact h

private theorem ordinaryObjProp_ne {r : IRI} (h : isOrdinaryObjProp r = true) :
    r ≠ topObjectProperty ∧ r ≠ bottomObjectProperty := by
  simp only [isOrdinaryObjProp, Bool.and_eq_true, bne_iff_ne] at h; exact h

private theorem ordinaryDataProp_ne {r : IRI} (h : isOrdinaryDataProp r = true) :
    r ≠ topDataProperty ∧ r ≠ bottomDataProperty := by
  simp only [isOrdinaryDataProp, Bool.and_eq_true, bne_iff_ne] at h; exact h

private theorem atLeast_filter_iff {α : Type} (xs : List α) (hx : xs.Nodup)
    (hall : ∀ x, x ∈ xs) (test : α → Bool) (n : Nat) :
    n ≤ (xs.filter test).length ↔ AtLeast n (fun x => test x = true) := by
  constructor
  · intro h
    refine ⟨(xs.filter test).take n, List.length_take_of_le h,
      ((List.take_sublist ..).nodup (List.filter_sublist.nodup hx)), ?_⟩
    exact fun _ hm => (List.mem_filter.mp (List.mem_of_mem_take hm)).2
  · rintro ⟨ys, hlen, hy, hp⟩
    rw [← hlen]
    exact hy.length_le_of_subset fun a ha => List.mem_filter.mpr ⟨hall a, hp a ha⟩

private def evalOriented (g : Graph) (r : OrientedRole) (x y : g.World) : Bool :=
  if r.2 then g.edge r.1 y x else g.edge r.1 x y

private theorem evalOriented_iff {m : SROIQDModel} {r : OrientedRole} {x y : m.graph.World}
    (h : isOrdinaryObjProp r.1 = true) :
    evalOriented m.graph r x y = true ↔ holdsOriented m.toInterpretation r x y := by
  have ⟨ho1, ho2⟩ := ordinaryObjProp_ne h
  rcases r with ⟨r, _ | _⟩ <;> simp [evalOriented, holdsOriented, ho1, ho2]

/-- Executable evaluation of an SROIQ(D) concept on a finite model.
    Returns `some b` when all referenced symbols are ordinary and all data
    ranges compile; `none` rejects the model conservatively. -/
def eval? (m : SROIQDModel) (x : m.graph.World) : Concept → Option Bool
  | .top => some true
  | .bottom => some false
  | .lit p sign =>
    if isOrdinaryClass p then some (if sign then m.graph.atom p x else !m.graph.atom p x)
    else none
  | .nom a sign => some (if sign then x == m.indVal a else x != m.indVal a)
  | .self r sign =>
    if isOrdinaryObjProp r.1 then
      some (if sign then evalOriented m.graph r x x else !evalOriented m.graph r x x)
    else none
  | .conj a b => do return (← eval? m x a) && (← eval? m x b)
  | .disj a b => do return (← eval? m x a) || (← eval? m x b)
  | .some r c =>
    if isOrdinaryObjProp r.1 then
      (m.graph.worlds.mapM fun y => (eval? m y c).map fun b => evalOriented m.graph r x y && b).map (·.any id)
    else none
  | .all r c =>
    if isOrdinaryObjProp r.1 then
      (m.graph.worlds.mapM fun y => (eval? m y c).map fun b => !evalOriented m.graph r x y || b).map (·.all id)
    else none
  | .min n r c =>
    if isOrdinaryObjProp r.1 then
      (m.graph.worlds.mapM fun y => (eval? m y c).map fun b => (y, evalOriented m.graph r x y && b)).map
        fun vals => decide (n ≤ (vals.filter Prod.snd).length)
    else none
  | .max n r c =>
    if isOrdinaryObjProp r.1 then
      (m.graph.worlds.mapM fun y => (eval? m y c).map fun b => (y, evalOriented m.graph r x y && b)).map
        fun vals => !decide (n + 1 ≤ (vals.filter Prod.snd).length)
    else none
  | .dataSome dp d =>
    if isOrdinaryDataProp dp then (compile d).map fun c => (m.dataValues dp x).any c.holds
    else none
  | .dataAll dp d =>
    if isOrdinaryDataProp dp then (compile d).map fun c => (m.dataValues dp x).all c.holds
    else none
  | .dataValue dp l sign =>
    if isOrdinaryDataProp dp then
      (decodeLiteral l).map fun v => if sign then m.hasDataEdge dp x v else !m.hasDataEdge dp x v
    else none
  | .dataMin n dp d =>
    if isOrdinaryDataProp dp then
      (compile d).map fun c => decide (n ≤ ((m.dataValues dp x).filter c.holds).length)
    else none
  | .dataMax n dp d =>
    if isOrdinaryDataProp dp then
      (compile d).map fun c => !decide (n + 1 ≤ ((m.dataValues dp x).filter c.holds).length)
    else none

private theorem mapM_option_iff {α β : Type} (xs : List α) (f : α → Option β) (ys : List β)
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (k : Nat) (hk1 : k < xs.length) (hk2 : k < ys.length),
      f xs[k] = some ys[k] := by
  induction xs generalizing ys with
  | nil =>
    simp [List.mapM_nil, pure] at h; subst h; exact ⟨rfl, fun _ hk _ => (Nat.not_lt_zero _ hk).elim⟩
  | cons a tail ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hf : f a with
    | none => simp [hf] at h
    | some b =>
      simp only [hf] at h
      cases hrest : tail.mapM f with
      | none => simp [hrest] at h
      | some bs =>
        simp only [hrest, pure, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hget⟩ := ih bs hrest
        refine ⟨by simp [hlen], fun k hk1 hk2 => ?_⟩
        cases k with
        | zero => exact hf
        | succ k => exact hget k (Nat.lt_of_succ_lt_succ hk1) (Nat.lt_of_succ_lt_succ hk2)

private theorem mapM_worlds_mem {α : Type} (m : SROIQDModel) (f : m.graph.World → Option α)
    (ys : List α) (h : m.graph.worlds.mapM f = some ys) :
    (∀ y, ∃ v ∈ ys, f y = some v) ∧ (∀ v ∈ ys, ∃ y, f y = some v) := by
  obtain ⟨hlen, hget⟩ := mapM_option_iff m.graph.worlds f ys h
  constructor
  · intro y
    have hy : y.val < m.graph.worlds.length := by simp [Graph.worlds]
    have hy2 : y.val < ys.length := hlen ▸ hy
    have hwg : m.graph.worlds[y.val] = y := by simp [Graph.worlds]
    refine ⟨ys[y.val], List.getElem_mem hy2, ?_⟩
    have h1 := hget y.val hy hy2
    rwa [hwg] at h1
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk1 : k < m.graph.worlds.length := hlen ▸ hk
    exact ⟨m.graph.worlds[k], hget k hk1 hk⟩

private theorem mapM_pairs_filter_length (m : SROIQDModel) (test : m.graph.World → Bool)
    (ys : List (m.graph.World × Bool))
    (h : m.graph.worlds.mapM (fun y => some (y, test y)) = some ys) :
    (ys.filter Prod.snd).length = (m.graph.worlds.filter test).length := by
  have heq : ys = m.graph.worlds.map (fun y => (y, test y)) := by
    have hmap : m.graph.worlds.mapM (fun y => some (y, test y)) =
        some (m.graph.worlds.map fun y => (y, test y)) := by
      induction m.graph.worlds with
      | nil => rfl
      | cons w ws ih => simp [List.mapM_cons, ih, pure]
    rw [hmap] at h
    exact (Option.some.inj h).symm
  subst heq
  induction m.graph.worlds with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.filter_cons]
    cases test w <;> simp [ih]

theorem eval?_sound (m : SROIQDModel) (x : m.graph.World) (c : Concept) {b : Bool}
    (h : eval? m x c = some b) :
    b = true ↔ holds m.toInterpretation x c := by
  induction c generalizing x b with
  | top =>
    simp [eval?] at h; subst h; simp [holds]
  | bottom =>
    simp [eval?] at h; subst h; simp [holds]
  | lit p sign =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases h
      have ⟨h1, h2⟩ := ordinaryClass_ne hord
      cases sign <;> simp [holds, h1, h2]
    · cases h
  | nom a sign =>
    simp only [eval?, Option.some.injEq] at h
    subst h
    cases sign <;> simp [holds] <;> exact Iff.rfl
  | self r sign =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases h
      have hev := evalOriented_iff (m := m) (x := x) (y := x) hord
      cases sign
      · simp [holds, ← hev]
      · simp [holds, hev]
    · cases h
  | conj a c ha hc =>
    simp only [eval?, bind, Option.bind, pure] at h
    cases h1 : eval? m x a with
    | none => simp [h1] at h
    | some b1 =>
      simp only [h1] at h
      cases h2 : eval? m x c with
      | none => simp [h2] at h
      | some b2 =>
        simp only [h2, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, holds, ha x h1, hc x h2]
  | disj a c ha hc =>
    simp only [eval?, bind, Option.bind, pure] at h
    cases h1 : eval? m x a with
    | none => simp [h1] at h
    | some b1 =>
      simp only [h1] at h
      cases h2 : eval? m x c with
      | none => simp [h2] at h
      | some b2 =>
        simp only [h2, Option.some.injEq] at h
        subst h
        simp only [Bool.or_eq_true, holds, ha x h1, hc x h2]
  | some r c ih =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hm : m.graph.worlds.mapM (fun y => (eval? m y c).map fun b => evalOriented m.graph r x y && b) with
      | none => simp [hm] at h
      | some vals =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hfor, hback⟩ := mapM_worlds_mem m _ vals hm
        simp only [List.any_eq_true, id_eq, holds]
        constructor
        · rintro ⟨v, hv, rfl⟩
          obtain ⟨y, hy⟩ := hback true hv
          cases he : eval? m y c with
          | none => simp [he] at hy
          | some by' =>
            simp only [he, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hy
            exact ⟨y, (evalOriented_iff hord).mp hy.1, (ih y he).mp hy.2⟩
        · rintro ⟨y, hedge, hcy⟩
          obtain ⟨v, hv, hfy⟩ := hfor y
          cases he : eval? m y c with
          | none => simp [he] at hfy
          | some by' =>
            simp only [he, Option.map_some, Option.some.injEq] at hfy
            have hby : by' = true := (ih y he).mpr hcy
            have hed : evalOriented m.graph r x y = true := (evalOriented_iff hord).mpr hedge
            rw [hed, hby] at hfy
            exact ⟨v, hv, hfy.symm⟩
    · cases h
  | all r c ih =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hm : m.graph.worlds.mapM (fun y => (eval? m y c).map fun b => !evalOriented m.graph r x y || b) with
      | none => simp [hm] at h
      | some vals =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hfor, hback⟩ := mapM_worlds_mem m _ vals hm
        simp only [List.all_eq_true, id_eq, holds]
        constructor
        · intro hall y hedge
          obtain ⟨v, hv, hfy⟩ := hfor y
          have hv1 := hall v hv
          subst hv1
          cases he : eval? m y c with
          | none => simp [he] at hfy
          | some by' =>
            have hed : evalOriented m.graph r x y = true := (evalOriented_iff hord).mpr hedge
            simp only [he, Option.map_some, Option.some.injEq, hed, Bool.not_true,
              Bool.false_or] at hfy
            exact (ih y he).mp hfy
        · intro hall v hv
          obtain ⟨y, hfy⟩ := hback v hv
          cases he : eval? m y c with
          | none => simp [he] at hfy
          | some by' =>
            simp only [he, Option.map_some, Option.some.injEq] at hfy
            rw [← hfy]
            cases hedge : evalOriented m.graph r x y
            · simp
            · simp [(ih y he).mpr (hall y ((evalOriented_iff hord).mp hedge))]
    · cases h
  | min n r c ih =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hm : m.graph.worlds.mapM (fun y => (eval? m y c).map fun b => (y, evalOriented m.graph r x y && b)) with
      | none => simp [hm] at h
      | some vals =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hfor, _⟩ := mapM_worlds_mem m _ vals hm
        let test : m.graph.World → Bool := fun y =>
          evalOriented m.graph r x y && (eval? m y c).getD false
        have htest : ∀ y, eval? m y c = some ((eval? m y c).getD false) := fun y => by
          obtain ⟨_, _, hfy⟩ := hfor y
          cases he : eval? m y c with
          | none => simp [he] at hfy
          | some b' => simp
        have hmeq : m.graph.worlds.mapM (fun y => some (y, test y)) = some vals := by
          rw [← hm]
          congr 1; funext y
          have hy := htest y
          cases he : eval? m y c with
          | none => rw [he] at hy; cases hy
          | some b' => simp [test, he]
        rw [decide_eq_true_eq, mapM_pairs_filter_length m test vals hmeq,
          atLeast_filter_iff m.graph.worlds (List.nodup_finRange _) List.mem_finRange]
        simp only [holds, AtLeast, test, Bool.and_eq_true]
        constructor
        · rintro ⟨xs, hlen, hnd, hp⟩
          exact ⟨xs, hlen, hnd, fun y hy => ⟨(evalOriented_iff hord).mp (hp y hy).1, (ih y (htest y)).mp (hp y hy).2⟩⟩
        · rintro ⟨xs, hlen, hnd, hp⟩
          exact ⟨xs, hlen, hnd, fun y hy => ⟨(evalOriented_iff hord).mpr (hp y hy).1, (ih y (htest y)).mpr (hp y hy).2⟩⟩
    · cases h
  | max n r c ih =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hm : m.graph.worlds.mapM (fun y => (eval? m y c).map fun b => (y, evalOriented m.graph r x y && b)) with
      | none => simp [hm] at h
      | some vals =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hfor, _⟩ := mapM_worlds_mem m _ vals hm
        let test : m.graph.World → Bool := fun y =>
          evalOriented m.graph r x y && (eval? m y c).getD false
        have htest : ∀ y, eval? m y c = some ((eval? m y c).getD false) := fun y => by
          obtain ⟨_, _, hfy⟩ := hfor y
          cases he : eval? m y c with
          | none => simp [he] at hfy
          | some b' => simp
        have hmeq : m.graph.worlds.mapM (fun y => some (y, test y)) = some vals := by
          rw [← hm]
          congr 1; funext y
          have hy := htest y
          cases he : eval? m y c with
          | none => rw [he] at hy; cases hy
          | some b' => simp [test, he]
        rw [Bool.not_eq_true', decide_eq_false_iff_not, mapM_pairs_filter_length m test vals hmeq,
          atLeast_filter_iff m.graph.worlds (List.nodup_finRange _) List.mem_finRange]
        simp only [holds, AtLeast, test, Bool.and_eq_true]
        apply not_congr
        constructor
        · rintro ⟨xs, hlen, hnd, hp⟩
          exact ⟨xs, hlen, hnd, fun y hy => ⟨(evalOriented_iff hord).mp (hp y hy).1, (ih y (htest y)).mp (hp y hy).2⟩⟩
        · rintro ⟨xs, hlen, hnd, hp⟩
          exact ⟨xs, hlen, hnd, fun y hy => ⟨(evalOriented_iff hord).mpr (hp y hy).1, (ih y (htest y)).mpr (hp y hy).2⟩⟩
    · cases h
  | dataSome dp d =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hc : compile d with
      | none => simp [hc] at h
      | some comp =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        have ⟨hd1, hd2⟩ := ordinaryDataProp_ne hord
        simp only [List.any_eq_true, mem_dataValues_iff, holds, hd1, hd2, ↓reduceIte]
        constructor
        · rintro ⟨v, hedge, hcomp⟩
          exact ⟨some v, ⟨v, rfl, hedge⟩, (comp.holds_iff m.toInterpretation v).mp hcomp⟩
        · rintro ⟨y, ⟨v, rfl, hedge⟩, hdata⟩
          exact ⟨v, hedge, (comp.holds_iff m.toInterpretation v).mpr hdata⟩
    · cases h
  | dataAll dp d =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hc : compile d with
      | none => simp [hc] at h
      | some comp =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        have ⟨hd1, hd2⟩ := ordinaryDataProp_ne hord
        simp only [List.all_eq_true, mem_dataValues_iff, holds, hd1, hd2, ↓reduceIte]
        constructor
        · intro hall y ⟨v, hy, hedge⟩
          subst hy
          exact (comp.holds_iff m.toInterpretation v).mp (hall v hedge)
        · intro hall v hedge
          exact (comp.holds_iff m.toInterpretation v).mpr (hall (some v) ⟨v, rfl, hedge⟩)
    · cases h
  | dataValue dp l sign =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hl : decodeLiteral l with
      | none => simp [hl] at h
      | some v =>
        simp only [hl, Option.map_some, Option.some.injEq] at h
        subst h
        have ⟨hd1, hd2⟩ := ordinaryDataProp_ne hord
        cases sign <;> simp [holds, hd1, hd2, hl]
    · cases h
  | dataMin n dp d =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hc : compile d with
      | none => simp [hc] at h
      | some comp =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        rw [decide_eq_true_eq]
        have ⟨hd1, hd2⟩ := ordinaryDataProp_ne hord
        simp only [holds, AtLeast, hd1, hd2, ↓reduceIte]
        constructor
        · intro hlen
          let ys := ((m.dataValues dp x).filter comp.holds).take n
          refine ⟨ys.map some, by simp [ys, Nat.min_eq_left hlen], ?_, ?_⟩
          · exact nodup_map_inj Option.some.inj
              ((List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _)))
          · intro z hz
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
            have hv' := List.mem_filter.mp (List.mem_of_mem_take hv)
            exact ⟨⟨v, rfl, (mem_dataValues_iff m dp x v).mp hv'.1⟩,
              (comp.holds_iff m.toInterpretation v).mp hv'.2⟩
        · rintro ⟨zs, hlen, hnd, hp⟩
          let vs : List Value := zs.filterMap id
          have hmap : vs.map some = zs := by
            have hall : ∀ z ∈ zs, ∃ v, z = some v := fun z hz => by
              obtain ⟨⟨v, rfl, _⟩, _⟩ := hp z hz
              exact ⟨v, rfl⟩
            clear hlen hnd hp
            induction zs with
            | nil => rfl
            | cons z tail ih =>
              obtain ⟨v, rfl⟩ := hall z (List.mem_cons_self ..)
              simp only [vs, List.filterMap_cons, id_eq, List.map_cons]
              exact congrArg (some v :: ·) (ih fun w hw => hall w (List.mem_cons_of_mem _ hw))
          have hvlen : vs.length = n := by
            have := congrArg List.length hmap
            rw [List.length_map, hlen] at this
            exact this
          have hvnd : vs.Nodup := by
            rw [← hmap] at hnd
            exact nodup_of_map some hnd
          rw [← hvlen]
          refine hvnd.length_le_of_subset fun v hv => List.mem_filter.mpr ?_
          have hmem : some v ∈ zs := hmap ▸ List.mem_map_of_mem hv
          obtain ⟨⟨v', heq, hedge⟩, hdata⟩ := hp (some v) hmem
          cases heq
          exact ⟨(mem_dataValues_iff m dp x v).mpr hedge,
            (comp.holds_iff m.toInterpretation v).mpr hdata⟩
    · cases h
  | dataMax n dp d =>
    simp only [eval?] at h
    split at h
    · rename_i hord
      cases hc : compile d with
      | none => simp [hc] at h
      | some comp =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        have ⟨hd1, hd2⟩ := ordinaryDataProp_ne hord
        simp only [holds, AtLeast, hd1, hd2, ↓reduceIte]
        apply not_congr
        constructor
        · intro hlen
          let ys := ((m.dataValues dp x).filter comp.holds).take (n + 1)
          refine ⟨ys.map some, by simp [ys, Nat.min_eq_left hlen], ?_, ?_⟩
          · exact nodup_map_inj Option.some.inj
              ((List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _)))
          · intro z hz
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
            have hv' := List.mem_filter.mp (List.mem_of_mem_take hv)
            exact ⟨⟨v, rfl, (mem_dataValues_iff m dp x v).mp hv'.1⟩,
              (comp.holds_iff m.toInterpretation v).mp hv'.2⟩
        · rintro ⟨zs, hlen, hnd, hp⟩
          let vs : List Value := zs.filterMap id
          have hmap : vs.map some = zs := by
            have hall : ∀ z ∈ zs, ∃ v, z = some v := fun z hz => by
              obtain ⟨⟨v, rfl, _⟩, _⟩ := hp z hz
              exact ⟨v, rfl⟩
            clear hlen hnd hp
            induction zs with
            | nil => rfl
            | cons z tail ih =>
              obtain ⟨v, rfl⟩ := hall z (List.mem_cons_self ..)
              simp only [vs, List.filterMap_cons, id_eq, List.map_cons]
              exact congrArg (some v :: ·) (ih fun w hw => hall w (List.mem_cons_of_mem _ hw))
          have hvlen : vs.length = n + 1 := by
            have := congrArg List.length hmap
            rw [List.length_map, hlen] at this
            exact this
          have hvnd : vs.Nodup := by
            rw [← hmap] at hnd
            exact nodup_of_map some hnd
          rw [← hvlen]
          refine hvnd.length_le_of_subset fun v hv => List.mem_filter.mpr ?_
          have hmem : some v ∈ zs := hmap ▸ List.mem_map_of_mem hv
          obtain ⟨⟨v', heq, hedge⟩, hdata⟩ := hp (some v) hmem
          cases heq
          exact ⟨(mem_dataValues_iff m dp x v).mpr hedge,
            (comp.holds_iff m.toInterpretation v).mpr hdata⟩
    · cases h

private theorem objPath_iff {m : SROIQDModel} {rs : List OrientedRole} {x y : m.graph.World}
    (h : ∀ r ∈ rs, isOrdinaryObjProp r.1 = true) :
    RoleChains.TransitivePaths.WordPath m.graph.interpretation rs x y ↔
      objPath m.toInterpretation rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    change (∃ z, ALC.holdsRole m.graph.interpretation r x z ∧
      RoleChains.TransitivePaths.WordPath m.graph.interpretation tail z y) ↔
      ∃ z, holdsOriented m.toInterpretation r x z ∧ objPath m.toInterpretation tail z y
    refine exists_congr fun z => and_congr ?_ (ih fun s hs => h s (List.mem_cons_of_mem _ hs))
    exact (m.graph.oriented_iff r x z).symm.trans
      (evalOriented_iff (h r (List.mem_cons_self ..)))

def checkModel (p : Problem) (m : SROIQDModel) : Bool :=
  let objOrdinary :=
    p.rules.all (fun (r, s) => isOrdinaryObjProp r.1 && isOrdinaryObjProp s.1) &&
    p.chains.all (fun c => isOrdinaryObjProp c.head && c.bodyNames.all isOrdinaryObjProp) &&
    p.chars.reflexive.all isOrdinaryObjProp &&
    p.chars.irreflexive.all isOrdinaryObjProp &&
    p.chars.asymmetric.all isOrdinaryObjProp &&
    p.chars.disjoint.all (fun (r, s) => isOrdinaryObjProp r.1 && isOrdinaryObjProp s.1) &&
    p.subData.all (fun (r, s) => isOrdinaryDataProp r && isOrdinaryDataProp s) &&
    p.disjointData.all (fun (r, s) => isOrdinaryDataProp r && isOrdinaryDataProp s) &&
    p.keys.all (fun k => k.objProps.all (fun r => isOrdinaryObjProp r.1) && k.dataProps.all isOrdinaryDataProp) &&
    p.objAssertions.all (fun (r, _, _) => isOrdinaryObjProp r) &&
    p.negObjAssertions.all (fun (r, _, _) => isOrdinaryObjProp r) &&
    p.funcData.all isOrdinaryDataProp &&
    p.dataRanges.all (fun (r, _) => isOrdinaryDataProp r) &&
    p.dataAssertions.all (fun (r, _, _) => isOrdinaryDataProp r) &&
    p.negDataAssertions.all (fun (r, _, _) => isOrdinaryDataProp r)
  objOrdinary &&
  checkRoleAxioms p.rules p.chains m.graph &&
  p.chars.reflexive.all (fun r => m.graph.worlds.all fun x => m.graph.edge r x x) &&
  p.chars.irreflexive.all (fun r => m.graph.worlds.all fun x => !m.graph.edge r x x) &&
  p.chars.asymmetric.all (fun r => m.graph.worlds.all fun x => m.graph.worlds.all fun y =>
    !(m.graph.edge r x y && m.graph.edge r y x)) &&
  p.chars.disjoint.all (fun (r, s) => m.graph.worlds.all fun x => m.graph.worlds.all fun y =>
    !(evalOriented m.graph r x y && evalOriented m.graph s x y)) &&
  p.subData.all (fun (r, s) => m.graph.worlds.all fun x =>
    (m.dataValues r x).all fun v => m.hasDataEdge s x v) &&
  p.disjointData.all (fun (r, s) => m.graph.worlds.all fun x =>
    (m.dataValues r x).all fun v => !m.hasDataEdge s x v) &&
  p.funcData.all (fun dp => m.graph.worlds.all fun x => (m.dataValues dp x).length ≤ 1) &&
  p.dataRanges.all (fun (dp, d) =>
    match compile d with
    | some comp => m.graph.worlds.all fun x => (m.dataValues dp x).all comp.holds
    | none => false) &&
  p.tbox.all (fun q => m.graph.worlds.all fun x =>
    match eval? m x q.sub, eval? m x q.sup with
    | some bs, some bt => !bs || bt
    | _, _ => false) &&
  p.keys.all (fun k => m.graph.worlds.all fun x => m.graph.worlds.all fun y =>
    match eval? m x k.cls, eval? m y k.cls with
    | some bx, some by' =>
      !(m.isNamedWorld x && m.isNamedWorld y && bx && by' &&
        k.objProps.all (fun r => m.graph.worlds.any fun z =>
          m.isNamedWorld z && evalOriented m.graph r x z && evalOriented m.graph r y z) &&
        k.dataProps.all (fun dp => (m.dataValues dp x).any fun v => m.hasDataEdge dp y v)) || (x == y)
    | _, _ => false) &&
  p.classAssertions.all (fun (a, c) => eval? m (m.indVal a) c == some true) &&
  p.objAssertions.all (fun (r, a, b) => m.graph.edge r (m.indVal a) (m.indVal b)) &&
  p.negObjAssertions.all (fun (r, a, b) => !m.graph.edge r (m.indVal a) (m.indVal b)) &&
  p.sameInds.all (fun (a, b) => m.indVal a == m.indVal b) &&
  p.diffInds.all (fun (a, b) => m.indVal a != m.indVal b) &&
  p.dataAssertions.all (fun (dp, a, l) =>
    match decodeLiteral l with | some v => m.hasDataEdge dp (m.indVal a) v | none => false) &&
  p.negDataAssertions.all (fun (dp, a, l) =>
    match decodeLiteral l with | some v => !m.hasDataEdge dp (m.indVal a) v | none => false) &&
  m.graph.worlds.any (fun x => eval? m x p.root == some true)

theorem checkModel_sound {p : Problem} {m : SROIQDModel} (h : checkModel p m = true) : p.Sat := by
  unfold checkModel at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hord, hra⟩, href⟩, hirr⟩, hasym⟩, hdisj⟩, hsubD⟩, hdisjD⟩, hfunc⟩, hdr⟩, htbox⟩, hkeys⟩,
    hca⟩, hoa⟩, hnoa⟩, hsame⟩, hdiff⟩, hda⟩, hnda⟩, hroot⟩
  rcases hord with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hordR, hordC⟩, hordRef⟩, hordIrr⟩, hordAsym⟩, hordDisj⟩, hordSubD⟩, hordDisjD⟩, hordKeys⟩,
    hordOA⟩, hordNOA⟩, hordFD⟩, hordDR⟩, hordDA⟩, hordNDA⟩
  obtain ⟨hR, hC⟩ := checkRoleAxioms_iff.mp hra
  obtain ⟨x0, _, hx0⟩ := List.any_eq_true.mp hroot
  have hx0' : holds m.toInterpretation x0 p.root := by
    have heq := beq_iff_eq.mp hx0
    exact (eval?_sound m x0 p.root heq).mp rfl
  refine ⟨m.toInterpretation, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, x0, hx0'⟩
  · -- tbox
    intro q hq x hx
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp htbox q hq) x (List.mem_finRange _)
    cases hs : eval? m x q.sub with
    | none => simp [hs] at h1
    | some bs =>
      cases ht : eval? m x q.sup with
      | none => simp [hs, ht] at h1
      | some bt =>
        simp only [hs, ht, Bool.or_eq_true, Bool.not_eq_true'] at h1
        have hbs : bs = true := (eval?_sound m x q.sub hs).mpr hx
        exact (eval?_sound m x q.sup ht).mp (h1.resolve_left (by simp [hbs]))
  · -- rules
    intro rs hrs x y hxy
    have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordR rs hrs)
    have ⟨ha1, hb1⟩ := ordinaryObjProp_ne ho1
    have ⟨ha2, hb2⟩ := ordinaryObjProp_ne ho2
    have hxy' : ALC.holdsRole m.graph.interpretation rs.1 x y := by
      rcases rs with ⟨⟨r1, b1⟩, ⟨r2, b2⟩⟩
      cases b1 <;> simp [holdsOriented, ALC.holdsRole, Graph.interpretation, ha1, hb1] at hxy ⊢ <;> exact hxy
    have hres := hR rs.1 rs.2 hrs x y hxy'
    rcases rs with ⟨⟨r1, b1⟩, ⟨r2, b2⟩⟩
    cases b2 <;> simp [holdsOriented, ALC.holdsRole, Graph.interpretation, ha2, hb2] at hres ⊢ <;> exact hres
  · -- chains
    intro c hc x y hp
    have ⟨hch, hcb⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordC c hc)
    have ⟨ha, hb⟩ := ordinaryObjProp_ne hch
    simp only [ha, hb, ↓reduceIte]
    exact hC c hc x y ((objPath_iff
      (fun r hr => List.all_eq_true.mp hcb r.1 (List.mem_map_of_mem hr))).mpr hp)
  · -- reflexive
    intro r hr x
    have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordRef r hr)
    simp only [ha, hb, ↓reduceIte]
    exact List.all_eq_true.mp (List.all_eq_true.mp href r hr) x (List.mem_finRange _)
  · -- irreflexive
    intro r hr x
    have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordIrr r hr)
    simp only [ha, hb, ↓reduceIte]
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hirr r hr) x (List.mem_finRange _)
    simpa using h1
  · -- asymmetric
    intro r hr x y hxy hyx
    have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordAsym r hr)
    simp only [ha, hb, ↓reduceIte] at hxy hyx
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hasym r hr) x (List.mem_finRange _)) y (List.mem_finRange _)
    simp [hxy, hyx] at h1
  · -- disjoint
    intro rs hrs x y ⟨h1, h2⟩
    have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordDisj rs hrs)
    have h1' := (evalOriented_iff ho1).mpr h1
    have h2' := (evalOriented_iff ho2).mpr h2
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hdisj rs hrs) x (List.mem_finRange _)) y (List.mem_finRange _)
    simp [h1', h2'] at hchk
  · -- subData
    intro rs hrs x y hy
    have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordSubD rs hrs)
    have ⟨ha1, hb1⟩ := ordinaryDataProp_ne ho1
    have ⟨ha2, hb2⟩ := ordinaryDataProp_ne ho2
    simp only [ha1, hb1, ha2, hb2, ↓reduceIte] at hy ⊢
    obtain ⟨v, rfl, hv⟩ := hy
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hsubD rs hrs) x (List.mem_finRange _)) v ((mem_dataValues_iff m rs.1 x v).mpr hv)
    exact ⟨v, rfl, h1⟩
  · -- disjointData
    intro rs hrs x y ⟨h1, h2⟩
    have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordDisjD rs hrs)
    have ⟨ha1, hb1⟩ := ordinaryDataProp_ne ho1
    have ⟨ha2, hb2⟩ := ordinaryDataProp_ne ho2
    simp only [ha1, hb1, ha2, hb2, ↓reduceIte] at h1 h2
    obtain ⟨v, rfl, hv1⟩ := h1
    obtain ⟨v', heq, hv2⟩ := h2
    cases heq
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hdisjD rs hrs) x (List.mem_finRange _)) v ((mem_dataValues_iff m rs.1 x v).mpr hv1)
    simp [hv2] at hchk
  · -- funcData
    intro dp hdp x y z hy hz
    have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordFD dp hdp)
    simp only [ha, hb, ↓reduceIte] at hy hz
    obtain ⟨v1, rfl, h1⟩ := hy
    obtain ⟨v2, rfl, h2⟩ := hz
    have hlen : (m.dataValues dp x).length ≤ 1 :=
      of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hfunc dp hdp) x (List.mem_finRange _))
    have hm1 := (mem_dataValues_iff m dp x v1).mpr h1
    have hm2 := (mem_dataValues_iff m dp x v2).mpr h2
    cases hvs : m.dataValues dp x with
    | nil => rw [hvs] at hm1; cases hm1
    | cons v rest =>
      cases rest with
      | nil =>
        rw [hvs, List.mem_singleton] at hm1 hm2
        rw [hm1, hm2]
      | cons _ _ =>
        rw [hvs] at hlen; simp at hlen
  · -- dataRanges
    intro rd hrd x y hy
    have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordDR rd hrd)
    simp only [ha, hb, ↓reduceIte] at hy
    obtain ⟨v, rfl, hv⟩ := hy
    have h1 := List.all_eq_true.mp hdr rd hrd
    cases hc : compile rd.2 with
    | none => simp [hc] at h1
    | some comp =>
      simp only [hc] at h1
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1 x (List.mem_finRange _)) v ((mem_dataValues_iff m rd.1 x v).mpr hv)
      exact (comp.holds_iff m.toInterpretation v).mp h2
  · -- keys
    intro k hk x y hx hy hnx hny ho hd
    have ⟨hko, hkd⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordKeys k hk)
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hkeys k hk) x (List.mem_finRange _)) y (List.mem_finRange _)
    cases hex : eval? m x k.cls with
    | none => simp [hex] at h1
    | some bx =>
      cases hey : eval? m y k.cls with
      | none => simp [hex, hey] at h1
      | some by' =>
        simp only [hex, hey, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
        have hbx : bx = true := (eval?_sound m x k.cls hex).mpr hx
        have hby : by' = true := (eval?_sound m y k.cls hey).mpr hy
        have hob : k.objProps.all (fun r => m.graph.worlds.any fun z =>
            m.isNamedWorld z && evalOriented m.graph r x z && evalOriented m.graph r y z) = true := by
          rw [List.all_eq_true]
          intro r hr
          obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
          have hord := List.all_eq_true.mp hko r hr
          exact List.any_eq_true.mpr ⟨z, List.mem_finRange _,
            Bool.and_eq_true_iff.mpr
              ⟨Bool.and_eq_true_iff.mpr ⟨hnz, (evalOriented_iff hord).mpr hxz⟩,
                (evalOriented_iff hord).mpr hyz⟩⟩
        have hdb : k.dataProps.all (fun dp => (m.dataValues dp x).any fun v => m.hasDataEdge dp y v) = true := by
          rw [List.all_eq_true]
          intro dp hdp
          obtain ⟨z, hxz, hyz⟩ := hd dp hdp
          have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hkd dp hdp)
          simp only [ha, hb, ↓reduceIte] at hxz hyz
          obtain ⟨v, rfl, hvx⟩ := hxz
          obtain ⟨v', heq, hvy⟩ := hyz
          cases heq
          exact List.any_eq_true.mpr ⟨v, (mem_dataValues_iff m dp x v).mpr hvx, hvy⟩
        have hnx' : m.isNamedWorld x = true := hnx
        have hny' : m.isNamedWorld y = true := hny
        exact h1.resolve_left (by simp [hnx', hny', hbx, hby, hob, hdb])
  · -- classAssertions
    intro ac hac
    have h1 := beq_iff_eq.mp (List.all_eq_true.mp hca ac hac)
    exact (eval?_sound m (m.indVal ac.1) ac.2 h1).mp rfl
  · -- objAssertions
    intro rab hrab
    have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordOA rab hrab)
    simp only [ha, hb, ↓reduceIte]
    exact List.all_eq_true.mp hoa rab hrab
  · -- negObjAssertions
    intro rab hrab
    have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordNOA rab hrab)
    simp only [ha, hb, ↓reduceIte]
    simpa using List.all_eq_true.mp hnoa rab hrab
  · -- sameInds
    intro ab hab
    exact beq_iff_eq.mp (List.all_eq_true.mp hsame ab hab)
  · -- diffInds
    intro ab hab
    exact bne_iff_ne.mp (List.all_eq_true.mp hdiff ab hab)
  · -- dataAssertions
    intro ral hral
    have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordDA ral hral)
    simp only [ha, hb, ↓reduceIte]
    have h1 := List.all_eq_true.mp hda ral hral
    cases hl : decodeLiteral ral.2.2 with
    | none => simp [hl] at h1
    | some v =>
      simp only [hl] at h1
      exact ⟨v, rfl, h1⟩
  · -- negDataAssertions
    intro ral hral
    have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordNDA ral hral)
    simp only [ha, hb, ↓reduceIte]
    have h1 := List.all_eq_true.mp hnda ral hral
    cases hl : decodeLiteral ral.2.2 with
    | none => simp [hl] at h1
    | some v =>
      simp only [hl, Bool.not_eq_true'] at h1
      rintro ⟨v', hv', hedge⟩
      cases hv'
      rw [h1] at hedge; cases hedge

end Sabrina.OWL2.SROIQD
