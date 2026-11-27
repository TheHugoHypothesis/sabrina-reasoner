import Std.Data.HashSet
import Std.Data.HashMap
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
  | .top => Option.some []
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
  | top => trivial
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

/-- Positive/existential concepts that evaluate to `false` in the minimal canonical model
    unless explicitly witnessed in the tableau branch. Used to defer inactive GCIs in
    `undecidedGCI` until `tryBranchModel` checks the candidate model. -/
def Concept.isDeferrable : Concept → Bool
  | .top | .bottom => true
  | .lit _ true | .nom _ true | .self _ true | .dataValue _ _ true => true
  | .some _ _ | .dataSome _ _ => true
  | .conj a b => a.isDeferrable || b.isDeferrable
  | .disj a b => a.isDeferrable && b.isDeferrable
  | _ => false

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

private def setOfList {α : Type} [BEq α] [Hashable α] (xs : List α) : Std.HashSet α :=
  xs.foldl (fun s a => s.insert a) {}

private theorem setOfList_contains {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (xs : List α) (k : α) : (setOfList xs).contains k = xs.contains k := by
  have h : ∀ (l : List α) (acc : Std.HashSet α),
      (l.foldl (fun s a => s.insert a) acc).contains k = (acc.contains k || l.contains k) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a tl ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [Std.HashSet.contains_insert, List.contains_cons]
      cases h1 : (a == k) <;> cases h2 : (k == a)
      · simp
      · exfalso; have := beq_iff_eq.mp h2; subst this; simp at h1
      · exfalso; have := beq_iff_eq.mp h1; subst this; simp at h2
      · simp
  simpa [setOfList] using h xs {}

private def groupList {α β : Type} [BEq α] [Hashable α] (xs : List (α × β)) :
    Std.HashMap α (List β) :=
  xs.foldl (fun m (k, v) => m.insert k (v :: m.getD k [])) {}

private theorem mem_groupList_iff {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (xs : List (α × β)) (k : α) (v : β) :
    v ∈ (groupList xs).getD k [] ↔ (k, v) ∈ xs := by
  have h : ∀ (l : List (α × β)) (acc : Std.HashMap α (List β)),
      v ∈ (l.foldl (fun m (k0, v0) => m.insert k0 (v0 :: m.getD k0 [])) acc).getD k [] ↔
        v ∈ acc.getD k [] ∨ (k, v) ∈ l := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons hd tl ih =>
      rcases hd with ⟨k0, v0⟩
      intro acc
      rw [List.foldl_cons, ih]
      simp only [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert,
        List.mem_cons, Prod.mk.injEq]
      by_cases hk : k0 = k
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte, Option.getD_some, List.mem_cons, true_and]
        exact ⟨fun h => h.elim (fun h1 => h1.elim (fun e => Or.inr (Or.inl e)) Or.inl) (fun h2 => Or.inr (Or.inr h2)),
               fun h => h.elim (fun h1 => Or.inl (Or.inr h1)) (fun h2 => h2.elim (fun e => Or.inl (Or.inl e)) Or.inr)⟩
      · have hbeq : (k0 == k) = false := beq_false_of_ne hk
        have hne : k ≠ k0 := Ne.symm hk
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hne, false_and, false_or]
  simpa [groupList] using h xs {}

private def lookupMap {α β : Type} [BEq α] [Hashable α] (xs : List (α × β)) : Std.HashMap α β :=
  xs.foldr (fun (k, v) m => m.insert k v) {}

private theorem lookupMap_getElem?_eq {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (xs : List (α × β)) (k : α) : (lookupMap xs)[k]? = xs.lookup k := by
  induction xs with
  | nil => simp [lookupMap, List.lookup]
  | cons hd tl ih =>
    rcases hd with ⟨k0, v0⟩
    simp only [lookupMap, List.foldr_cons, Std.HashMap.getElem?_insert, List.lookup]
    by_cases hk : k0 = k
    · subst hk; simp
    · have h1 : (k0 == k) = false := beq_false_of_ne hk
      have h2 : (k == k0) = false := beq_false_of_ne (Ne.symm hk)
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      exact ih

structure ModelIndex (m : SROIQDModel) where
  atomSet : Std.HashSet (String × m.graph.World)
  edgeSet : Std.HashSet (String × m.graph.World × m.graph.World)
  atomWorlds : Std.HashMap String (List m.graph.World)
  outAdj : Std.HashMap (String × m.graph.World) (List m.graph.World)
  inAdj : Std.HashMap (String × m.graph.World) (List m.graph.World)
  edgesByRole : Std.HashMap String (List (m.graph.World × m.graph.World))
  edgeSources : Std.HashMap OrientedRole (List m.graph.World)
  dataByPropWorld : Std.HashMap (IRI × m.graph.World) (List Value)
  dataSources : Std.HashMap IRI (List m.graph.World)
  nomMap : Std.HashMap IRI m.graph.World
  anonMap : Std.HashMap (String × String) m.graph.World
  namedWorldSet : Std.HashSet m.graph.World

def ModelIndex.build (m : SROIQDModel) : ModelIndex m :=
  { atomSet := setOfList m.graph.atoms
    edgeSet := setOfList m.graph.edges
    atomWorlds := groupList m.graph.atoms
    outAdj := groupList (m.graph.edges.map fun (r, x, y) => ((r, x), y))
    inAdj := groupList (m.graph.edges.map fun (r, x, y) => ((r, y), x))
    edgesByRole := groupList (m.graph.edges.map fun (r, x, y) => (r, (x, y)))
    edgeSources := groupList (m.graph.edges.flatMap fun (r, x, y) => [((r, false), x), ((r, true), y)])
    dataByPropWorld := groupList (m.dataEdges.map fun (dp, w, v) => ((dp, w), v))
    dataSources := groupList (m.dataEdges.map fun (dp, w, _) => (dp, w))
    nomMap := lookupMap m.nominals
    anonMap := lookupMap m.anons
    namedWorldSet := setOfList (m.nominals.map Prod.snd) }

def ModelIndex.indVal {m : SROIQDModel} (idx : ModelIndex m) : Individual → m.graph.World
  | .named a => idx.nomMap.getD a ⟨0, Nat.zero_lt_succ _⟩
  | .anonymous doc lid => idx.anonMap.getD (doc, lid) ⟨0, Nat.zero_lt_succ _⟩

private theorem ModelIndex.indVal_eq (m : SROIQDModel) (ind : Individual) :
    (ModelIndex.build m).indVal ind = m.indVal ind := by
  cases ind with
  | named a =>
    simp only [ModelIndex.indVal, ModelIndex.build, SROIQDModel.indVal, SROIQDModel.nomVal,
      Std.HashMap.getD_eq_getD_getElem?, lookupMap_getElem?_eq]
  | anonymous doc lid =>
    simp only [ModelIndex.indVal, ModelIndex.build, SROIQDModel.indVal, SROIQDModel.anonVal,
      Std.HashMap.getD_eq_getD_getElem?, lookupMap_getElem?_eq]

private theorem ModelIndex.atomSet_eq (m : SROIQDModel) (p : String) (x : m.graph.World) :
    (ModelIndex.build m).atomSet.contains (p, x) = m.graph.atom p x :=
  setOfList_contains m.graph.atoms (p, x)

private theorem ModelIndex.edgeSet_eq (m : SROIQDModel) (r : String) (x y : m.graph.World) :
    (ModelIndex.build m).edgeSet.contains (r, x, y) = m.graph.edge r x y :=
  setOfList_contains m.graph.edges (r, x, y)

private def ModelIndex.hasOriented {m : SROIQDModel} (idx : ModelIndex m)
    (r : OrientedRole) (x y : m.graph.World) : Bool :=
  if r.2 then idx.edgeSet.contains (r.1, y, x) else idx.edgeSet.contains (r.1, x, y)

private theorem ModelIndex.hasOriented_eq (m : SROIQDModel) (r : OrientedRole) (x y : m.graph.World) :
    (ModelIndex.build m).hasOriented r x y = evalOriented m.graph r x y := by
  rcases r with ⟨r, _ | _⟩ <;> simp [ModelIndex.hasOriented, evalOriented, ModelIndex.edgeSet_eq]

private def ModelIndex.neighbors {m : SROIQDModel} (idx : ModelIndex m)
    (r : OrientedRole) (x : m.graph.World) : List m.graph.World :=
  if r.2 then idx.inAdj.getD (r.1, x) [] else idx.outAdj.getD (r.1, x) []

private theorem ModelIndex.mem_neighbors_iff (m : SROIQDModel) (r : OrientedRole) (x y : m.graph.World) :
    y ∈ (ModelIndex.build m).neighbors r x ↔ evalOriented m.graph r x y = true := by
  rcases r with ⟨r, _ | _⟩
  · simp only [ModelIndex.neighbors, ModelIndex.build, Bool.false_eq_true, ↓reduceIte,
      mem_groupList_iff, List.mem_map, Prod.mk.injEq, evalOriented, Graph.edge, List.contains_iff_mem]
    constructor
    · rintro ⟨⟨r', x', y'⟩, hm, ⟨rfl, rfl⟩, rfl⟩; exact hm
    · intro hm; exact ⟨(r, x, y), hm, ⟨rfl, rfl⟩, rfl⟩
  · simp only [ModelIndex.neighbors, ModelIndex.build, ↓reduceIte,
      mem_groupList_iff, List.mem_map, Prod.mk.injEq, evalOriented, Graph.edge, List.contains_iff_mem]
    constructor
    · rintro ⟨⟨r', x', y'⟩, hm, ⟨rfl, rfl⟩, rfl⟩; exact hm
    · intro hm; exact ⟨(r, y, x), hm, ⟨rfl, rfl⟩, rfl⟩

private theorem ModelIndex.mem_edgesByRole_iff (m : SROIQDModel) (r : String) (x y : m.graph.World) :
    (x, y) ∈ (ModelIndex.build m).edgesByRole.getD r [] ↔ m.graph.edge r x y = true := by
  simp only [ModelIndex.build, mem_groupList_iff, List.mem_map, Prod.mk.injEq, Graph.edge, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨r', x', y'⟩, hm, rfl, rfl, rfl⟩; exact hm
  · intro hm; exact ⟨(r, x, y), hm, rfl, rfl, rfl⟩

private theorem ModelIndex.mem_atomWorlds_iff (m : SROIQDModel) (p : String) (x : m.graph.World) :
    x ∈ (ModelIndex.build m).atomWorlds.getD p [] ↔ m.graph.atom p x = true := by
  simp only [ModelIndex.build, mem_groupList_iff, Graph.atom, List.contains_iff_mem]

private theorem ModelIndex.mem_edgeSources_of_edge (m : SROIQDModel) {r : OrientedRole} {x y : m.graph.World}
    (he : evalOriented m.graph r x y = true) :
    x ∈ (ModelIndex.build m).edgeSources.getD r [] := by
  rw [ModelIndex.build, mem_groupList_iff]
  rcases r with ⟨r, _ | _⟩
  · simp only [evalOriented, Bool.false_eq_true, ↓reduceIte, Graph.edge, List.contains_iff_mem] at he
    exact List.mem_flatMap.mpr ⟨(r, x, y), he, by simp⟩
  · simp only [evalOriented, ↓reduceIte, Graph.edge, List.contains_iff_mem] at he
    exact List.mem_flatMap.mpr ⟨(r, y, x), he, by simp⟩

def ModelIndex.dataVals {m : SROIQDModel} (idx : ModelIndex m)
    (dp : IRI) (x : m.graph.World) : List Value :=
  (idx.dataByPropWorld.getD (dp, x) []).eraseDups

private theorem ModelIndex.mem_dataVals_iff (m : SROIQDModel) (dp : IRI) (x : m.graph.World) (v : Value) :
    v ∈ (ModelIndex.build m).dataVals dp x ↔ m.hasDataEdge dp x v = true := by
  simp only [ModelIndex.dataVals, ModelIndex.build, List.mem_eraseDups, mem_groupList_iff,
    List.mem_map, Prod.mk.injEq, SROIQDModel.hasDataEdge, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]

private theorem ModelIndex.mem_dataSources_of_edge (m : SROIQDModel) {dp : IRI} {x : m.graph.World} {v : Value}
    (he : m.hasDataEdge dp x v = true) :
    x ∈ (ModelIndex.build m).dataSources.getD dp [] := by
  simp only [SROIQDModel.hasDataEdge, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨r, w, val⟩, hm, ⟨rfl, rfl⟩, rfl⟩ := he
  rw [ModelIndex.build, mem_groupList_iff]
  exact List.mem_map.mpr ⟨(r, w, val), hm, rfl⟩

private def ModelIndex.isNamedWorld {m : SROIQDModel} (idx : ModelIndex m) (x : m.graph.World) : Bool :=
  (x.val == 0) || idx.namedWorldSet.contains x

private theorem ModelIndex.isNamedWorld_eq (m : SROIQDModel) (x : m.graph.World) :
    (ModelIndex.build m).isNamedWorld x = m.isNamedWorld x := by
  simp only [ModelIndex.isNamedWorld, ModelIndex.build, SROIQDModel.isNamedWorld, setOfList_contains]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map, List.any_eq_true, beq_iff_eq]

private def evalFast? {m : SROIQDModel} (idx : ModelIndex m) (x : m.graph.World) :
    Concept → Option Bool
  | .top => some true
  | .bottom => some false
  | .lit p sign =>
    if isOrdinaryClass p then some (if sign then idx.atomSet.contains (p, x) else !idx.atomSet.contains (p, x))
    else none
  | .nom a sign => some (if sign then x == idx.indVal a else x != idx.indVal a)
  | .self r sign =>
    if isOrdinaryObjProp r.1 then
      some (if sign then idx.hasOriented r x x else !idx.hasOriented r x x)
    else none
  | .conj a b => do
    match ← evalFast? idx x a with
    | false => return false
    | true => evalFast? idx x b
  | .disj a b => do
    match ← evalFast? idx x a with
    | true => return true
    | false => evalFast? idx x b
  | .some r c =>
    if isOrdinaryObjProp r.1 then
      let rec goSome : List m.graph.World → Option Bool
        | [] => some false
        | y :: ys => do
          match ← evalFast? idx y c with
          | true => return true
          | false => goSome ys
      goSome (idx.neighbors r x)
    else none
  | .all r c =>
    if isOrdinaryObjProp r.1 then
      let rec goAll : List m.graph.World → Option Bool
        | [] => some true
        | y :: ys => do
          match ← evalFast? idx y c with
          | false => return false
          | true => goAll ys
      goAll (idx.neighbors r x)
    else none
  | .min n r c =>
    if isOrdinaryObjProp r.1 then
      ((idx.neighbors r x).eraseDups.mapM fun y => evalFast? idx y c).map fun bs =>
        decide (n ≤ (bs.filter id).length)
    else none
  | .max n r c =>
    if isOrdinaryObjProp r.1 then
      ((idx.neighbors r x).eraseDups.mapM fun y => evalFast? idx y c).map fun bs =>
        !decide (n + 1 ≤ (bs.filter id).length)
    else none
  | .dataSome dp d =>
    if isOrdinaryDataProp dp then (compile d).map fun c => (idx.dataVals dp x).any c.holds
    else none
  | .dataAll dp d =>
    if isOrdinaryDataProp dp then (compile d).map fun c => (idx.dataVals dp x).all c.holds
    else none
  | .dataValue dp l sign =>
    if isOrdinaryDataProp dp then
      (decodeLiteral l).map fun v =>
        let has := (idx.dataVals dp x).contains v
        if sign then has else !has
    else none
  | .dataMin n dp d =>
    if isOrdinaryDataProp dp then
      (compile d).map fun c => decide (n ≤ ((idx.dataVals dp x).filter c.holds).length)
    else none
  | .dataMax n dp d =>
    if isOrdinaryDataProp dp then
      (compile d).map fun c => !decide (n + 1 ≤ ((idx.dataVals dp x).filter c.holds).length)
    else none

private theorem evalFast?_some_go {m : SROIQDModel} {c : Concept}
    (ih : ∀ y b, evalFast? (ModelIndex.build m) y c = some b → (b = true ↔ holds m.toInterpretation y c))
    (ys : List m.graph.World) {b : Bool} (h : evalFast?.goSome (ModelIndex.build m) c ys = some b) :
    b = true ↔ ∃ y ∈ ys, holds m.toInterpretation y c := by
  induction ys with
  | nil =>
    simp [evalFast?.goSome] at h; subst h; simp
  | cons y tl ihys =>
    simp only [evalFast?.goSome, bind, Option.bind] at h
    cases hy : evalFast? (ModelIndex.build m) y c with
    | none => simp [hy] at h
    | some by' =>
      simp only [hy] at h
      cases by' with
      | true =>
        simp only [pure, Option.some.injEq] at h; subst h
        simp only [true_iff]
        exact ⟨y, List.mem_cons_self .., (ih y true hy).mp rfl⟩
      | false =>
        rw [ihys h]
        constructor
        · rintro ⟨z, hz, hzc⟩; exact ⟨z, List.mem_cons_of_mem _ hz, hzc⟩
        · rintro ⟨z, hz, hzc⟩
          rcases List.mem_cons.mp hz with rfl | hzt
          · exact Bool.noConfusion ((ih z false hy).mpr hzc)
          · exact ⟨z, hzt, hzc⟩

private theorem evalFast?_all_go {m : SROIQDModel} {c : Concept}
    (ih : ∀ y b, evalFast? (ModelIndex.build m) y c = some b → (b = true ↔ holds m.toInterpretation y c))
    (ys : List m.graph.World) {b : Bool} (h : evalFast?.goAll (ModelIndex.build m) c ys = some b) :
    b = true ↔ ∀ y ∈ ys, holds m.toInterpretation y c := by
  induction ys with
  | nil =>
    simp [evalFast?.goAll] at h; subst h; simp
  | cons y tl ihys =>
    simp only [evalFast?.goAll, bind, Option.bind] at h
    cases hy : evalFast? (ModelIndex.build m) y c with
    | none => simp [hy] at h
    | some by' =>
      simp only [hy] at h
      cases by' with
      | false =>
        simp only [pure, Option.some.injEq] at h; subst h
        simp only [Bool.false_eq_true, false_iff]
        intro hall
        exact Bool.noConfusion ((ih y false hy).mpr (hall y (List.mem_cons_self ..)))
      | true =>
        rw [ihys h]
        constructor
        · intro htl z hz
          rcases List.mem_cons.mp hz with rfl | hzt
          · exact (ih z true hy).mp rfl
          · exact htl z hzt
        · intro hall z hz; exact hall z (List.mem_cons_of_mem _ hz)

private theorem mapM_filter_id_length {α : Type} (xs : List α) (f : α → Option Bool) (bs : List Bool)
    (h : xs.mapM f = some bs) :
    (bs.filter id).length = (xs.filter fun x => f x == some true).length := by
  induction xs generalizing bs with
  | nil => simp [List.mapM_nil, pure] at h; subst h; rfl
  | cons x tl ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      simp only [hx] at h
      cases htl : tl.mapM f with
      | none => simp [htl] at h
      | some bs' =>
        simp only [htl, pure, Option.some.injEq] at h; subst h
        cases b <;> simp [hx, ih bs' htl]

private theorem evalFast?_sound (m : SROIQDModel) (x : m.graph.World) (c : Concept) {b : Bool}
    (h : evalFast? (ModelIndex.build m) x c = some b) :
    b = true ↔ holds m.toInterpretation x c := by
  induction c generalizing x b with
  | top => simp [evalFast?] at h; subst h; simp [holds]
  | bottom => simp [evalFast?] at h; subst h; simp [holds]
  | lit p sign =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      cases h
      have ⟨h1, h2⟩ := ordinaryClass_ne hord
      rw [ModelIndex.atomSet_eq]
      cases sign <;> simp [holds, h1, h2]
    · cases h
  | nom a sign =>
    simp only [evalFast?, ModelIndex.indVal_eq, Option.some.injEq] at h; subst h
    cases sign <;> simp [holds] <;> exact Iff.rfl
  | self r sign =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      cases h
      rw [ModelIndex.hasOriented_eq]
      have hev := evalOriented_iff (m := m) (x := x) (y := x) hord
      cases sign <;> simp [holds, ← hev]
    · cases h
  | conj a d iha ihd =>
    simp only [evalFast?, bind, Option.bind] at h
    cases ha : evalFast? (ModelIndex.build m) x a with
    | none => simp [ha] at h
    | some ba =>
      simp only [ha] at h
      cases ba with
      | false =>
        simp only [pure, Option.some.injEq] at h; subst h
        simp only [Bool.false_eq_true, false_iff, holds]
        intro ⟨hha, _⟩; exact Bool.noConfusion ((iha x ha).mpr hha)
      | true =>
        have hha : holds m.toInterpretation x a := (iha x ha).mp rfl
        rw [ihd x h]; simp [holds, hha]
  | disj a d iha ihd =>
    simp only [evalFast?, bind, Option.bind] at h
    cases ha : evalFast? (ModelIndex.build m) x a with
    | none => simp [ha] at h
    | some ba =>
      simp only [ha] at h
      cases ba with
      | true =>
        simp only [pure, Option.some.injEq] at h; subst h
        simp only [true_iff, holds]
        exact Or.inl ((iha x ha).mp rfl)
      | false =>
        have hnha : ¬ holds m.toInterpretation x a := fun hha => Bool.noConfusion ((iha x ha).mpr hha)
        rw [ihd x h]; simp [holds, hnha]
  | some r body ih =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      rw [evalFast?_some_go (fun y _ hy => ih y hy) _ h]
      simp only [holds]
      constructor
      · rintro ⟨y, hy, hby⟩
        exact ⟨y, (evalOriented_iff hord).mp ((ModelIndex.mem_neighbors_iff m r x y).mp hy), hby⟩
      · rintro ⟨y, hr, hby⟩
        exact ⟨y, (ModelIndex.mem_neighbors_iff m r x y).mpr ((evalOriented_iff hord).mpr hr), hby⟩
    · cases h
  | all r body ih =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      rw [evalFast?_all_go (fun y _ hy => ih y hy) _ h]
      simp only [holds]
      constructor
      · intro hall y hr
        exact hall y ((ModelIndex.mem_neighbors_iff m r x y).mpr ((evalOriented_iff hord).mpr hr))
      · intro hall y hy
        exact hall y ((evalOriented_iff hord).mp ((ModelIndex.mem_neighbors_iff m r x y).mp hy))
    · cases h
  | min n r body ih =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [decide_eq_true_iff, mapM_filter_id_length _ _ _ hbs]
      have hnd : ((ModelIndex.build m).neighbors r x).eraseDups.Nodup := nodup_eraseDups_list _
      obtain ⟨hlen, hget⟩ := mapM_option_iff _ _ _ hbs
      have hfilt_iff : ∀ y ∈ ((ModelIndex.build m).neighbors r x).eraseDups,
          (evalFast? (ModelIndex.build m) y body == some true) = true ↔ holds m.toInterpretation y body := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        have hk2 : k < bs.length := hlen.symm ▸ hk
        have hfk := hget k hk hk2
        rw [hfk, beq_iff_eq, Option.some.injEq]
        exact ih _ hfk
      constructor
      · intro hle
        refine ⟨(((ModelIndex.build m).neighbors r x).eraseDups.filter fun y =>
            evalFast? (ModelIndex.build m) y body == some true).take n,
          List.length_take_of_le hle,
          (List.take_sublist ..).nodup (List.filter_sublist.nodup hnd), ?_⟩
        intro y hy
        have hmf := List.mem_filter.mp (List.mem_of_mem_take hy)
        exact ⟨(evalOriented_iff hord).mp ((ModelIndex.mem_neighbors_iff m r x y).mp (List.mem_eraseDups.mp hmf.1)),
          (hfilt_iff y hmf.1).mp hmf.2⟩
      · rintro ⟨ys, hylen, hynd, hyq⟩
        rw [← hylen]
        refine hynd.length_le_of_subset fun y hy => List.mem_filter.mpr ?_
        have ⟨hr, hby⟩ := hyq y hy
        have hmem : y ∈ ((ModelIndex.build m).neighbors r x).eraseDups :=
          List.mem_eraseDups.mpr ((ModelIndex.mem_neighbors_iff m r x y).mpr ((evalOriented_iff hord).mpr hr))
        exact ⟨hmem, (hfilt_iff y hmem).mpr hby⟩
    · cases h
  | max n r body ih =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Bool.not_eq_true', decide_eq_false_iff_not, mapM_filter_id_length _ _ _ hbs]
      have hnd : ((ModelIndex.build m).neighbors r x).eraseDups.Nodup := nodup_eraseDups_list _
      obtain ⟨hlen, hget⟩ := mapM_option_iff _ _ _ hbs
      have hfilt_iff : ∀ y ∈ ((ModelIndex.build m).neighbors r x).eraseDups,
          (evalFast? (ModelIndex.build m) y body == some true) = true ↔ holds m.toInterpretation y body := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        have hk2 : k < bs.length := hlen.symm ▸ hk
        have hfk := hget k hk hk2
        rw [hfk, beq_iff_eq, Option.some.injEq]
        exact ih _ hfk
      simp only [holds]
      refine not_congr ⟨?_, ?_⟩
      · intro hle
        refine ⟨(((ModelIndex.build m).neighbors r x).eraseDups.filter fun y =>
            evalFast? (ModelIndex.build m) y body == some true).take (n + 1),
          List.length_take_of_le hle,
          (List.take_sublist ..).nodup (List.filter_sublist.nodup hnd), ?_⟩
        intro y hy
        have hmf := List.mem_filter.mp (List.mem_of_mem_take hy)
        exact ⟨(evalOriented_iff hord).mp ((ModelIndex.mem_neighbors_iff m r x y).mp (List.mem_eraseDups.mp hmf.1)),
          (hfilt_iff y hmf.1).mp hmf.2⟩
      · rintro ⟨ys, hylen, hynd, hyq⟩
        rw [← hylen]
        refine hynd.length_le_of_subset fun y hy => List.mem_filter.mpr ?_
        have ⟨hr, hby⟩ := hyq y hy
        have hmem : y ∈ ((ModelIndex.build m).neighbors r x).eraseDups :=
          List.mem_eraseDups.mpr ((ModelIndex.mem_neighbors_iff m r x y).mpr ((evalOriented_iff hord).mpr hr))
        exact ⟨hmem, (hfilt_iff y hmem).mpr hby⟩
    · cases h
  | dataSome dp d =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨comp, hcomp, rfl⟩ := Option.map_eq_some_iff.mp h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      simp only [List.any_eq_true, holds, h1, h2, ↓reduceIte]
      constructor
      · rintro ⟨v, hv, hch⟩
        exact ⟨some v, ⟨v, rfl, (ModelIndex.mem_dataVals_iff m dp x v).mp hv⟩, (comp.holds_iff m.toInterpretation v).mp hch⟩
      · rintro ⟨y, ⟨v, rfl, hedge⟩, hd⟩
        exact ⟨v, (ModelIndex.mem_dataVals_iff m dp x v).mpr hedge, (comp.holds_iff m.toInterpretation v).mpr hd⟩
    · cases h
  | dataAll dp d =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨comp, hcomp, rfl⟩ := Option.map_eq_some_iff.mp h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      simp only [List.all_eq_true, holds, h1, h2, ↓reduceIte]
      constructor
      · rintro hall y ⟨v, rfl, hedge⟩
        exact (comp.holds_iff m.toInterpretation v).mp (hall v ((ModelIndex.mem_dataVals_iff m dp x v).mpr hedge))
      · intro hall v hv
        exact (comp.holds_iff m.toInterpretation v).mpr (hall (some v) ⟨v, rfl, (ModelIndex.mem_dataVals_iff m dp x v).mp hv⟩)
    · cases h
  | dataValue dp l sign =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      have hcon : ((ModelIndex.build m).dataVals dp x).contains v = m.hasDataEdge dp x v := by
        rw [Bool.eq_iff_iff, List.contains_iff_mem, ModelIndex.mem_dataVals_iff]
      rw [hcon]
      cases sign <;> simp [holds, h1, h2, hv]
    · cases h
  | dataMin n dp d =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨comp, hcomp, rfl⟩ := Option.map_eq_some_iff.mp h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      simp only [decide_eq_true_iff, holds, h1, h2, ↓reduceIte]
      constructor
      · intro hle
        let vs := ((ModelIndex.build m).dataVals dp x).filter comp.holds |>.take n
        have hnd : vs.Nodup := (List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _))
        refine ⟨vs.map some, by simp only [vs, List.length_map, List.length_take_of_le hle], nodup_map_inj Option.some.inj hnd, ?_⟩
        intro y hy
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
        have hm := List.mem_filter.mp (List.mem_of_mem_take hv)
        exact ⟨⟨v, rfl, (ModelIndex.mem_dataVals_iff m dp x v).mp hm.1⟩, (comp.holds_iff m.toInterpretation v).mp hm.2⟩
      · rintro ⟨zs, hlen, hnd, hp⟩
        have hvals : ∃ vs : List Value, zs = vs.map some := by
          clear hlen hnd
          induction zs with
          | nil => exact ⟨[], rfl⟩
          | cons z tail ihz =>
            obtain ⟨⟨v, rfl, _⟩, _⟩ := hp z (List.mem_cons_self ..)
            obtain ⟨vs, hvs⟩ := ihz (fun w hw => hp w (List.mem_cons_of_mem _ hw))
            exact ⟨v :: vs, by simp [hvs]⟩
        obtain ⟨vs, hmap⟩ := hvals
        have hvlen : vs.length = n := by rw [hmap, List.length_map] at hlen; exact hlen
        have hvnd : vs.Nodup := nodup_of_map some (hmap ▸ hnd)
        rw [← hvlen]
        refine hvnd.length_le_of_subset fun v hv => List.mem_filter.mpr ?_
        obtain ⟨⟨v', heq, hedge⟩, hdata⟩ := hp (some v) (hmap ▸ List.mem_map_of_mem hv)
        cases heq
        exact ⟨(ModelIndex.mem_dataVals_iff m dp x v).mpr hedge, (comp.holds_iff m.toInterpretation v).mpr hdata⟩
    · cases h
  | dataMax n dp d =>
    simp only [evalFast?] at h
    split at h
    · rename_i hord
      obtain ⟨comp, hcomp, rfl⟩ := Option.map_eq_some_iff.mp h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, holds, h1, h2, ↓reduceIte]
      refine not_congr ⟨?_, ?_⟩
      · intro hle
        let vs := ((ModelIndex.build m).dataVals dp x).filter comp.holds |>.take (n + 1)
        have hnd : vs.Nodup := (List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _))
        refine ⟨vs.map some, by simp only [vs, List.length_map, List.length_take_of_le hle], nodup_map_inj Option.some.inj hnd, ?_⟩
        intro y hy
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
        have hm := List.mem_filter.mp (List.mem_of_mem_take hv)
        exact ⟨⟨v, rfl, (ModelIndex.mem_dataVals_iff m dp x v).mp hm.1⟩, (comp.holds_iff m.toInterpretation v).mp hm.2⟩
      · rintro ⟨zs, hlen, hnd, hp⟩
        have hvals : ∃ vs : List Value, zs = vs.map some := by
          clear hlen hnd
          induction zs with
          | nil => exact ⟨[], rfl⟩
          | cons z tail ihz =>
            obtain ⟨⟨v, rfl, _⟩, _⟩ := hp z (List.mem_cons_self ..)
            obtain ⟨vs, hvs⟩ := ihz (fun w hw => hp w (List.mem_cons_of_mem _ hw))
            exact ⟨v :: vs, by simp [hvs]⟩
        obtain ⟨vs, hmap⟩ := hvals
        have hvlen : vs.length = n + 1 := by rw [hmap, List.length_map] at hlen; exact hlen
        have hvnd : vs.Nodup := nodup_of_map some (hmap ▸ hnd)
        rw [← hvlen]
        refine hvnd.length_le_of_subset fun v hv => List.mem_filter.mpr ?_
        obtain ⟨⟨v', heq, hedge⟩, hdata⟩ := hp (some v) (hmap ▸ List.mem_map_of_mem hv)
        cases heq
        exact ⟨(ModelIndex.mem_dataVals_iff m dp x v).mpr hedge, (comp.holds_iff m.toInterpretation v).mpr hdata⟩
    · cases h

private def gciAnchorWorlds {m : SROIQDModel} (idx : ModelIndex m) :
    Concept → Option (List m.graph.World)
  | .nom a true => some [idx.indVal a]
  | .lit p true => if isOrdinaryClass p then some (idx.atomWorlds.getD p []) else none
  | .some r _ => if isOrdinaryObjProp r.1 then some (idx.edgeSources.getD r []) else none
  | .dataSome dp _ => if isOrdinaryDataProp dp then some (idx.dataSources.getD dp []) else none
  | .conj a b => gciAnchorWorlds idx a <|> gciAnchorWorlds idx b
  | _ => none

private theorem gciAnchorWorlds_complete (m : SROIQDModel) {c : Concept} {ws : List m.graph.World}
    (h : gciAnchorWorlds (ModelIndex.build m) c = some ws) {x : m.graph.World}
    (hx : holds m.toInterpretation x c) : x ∈ ws := by
  induction c generalizing ws with
  | nom a sign =>
    cases sign <;> simp [gciAnchorWorlds] at h
    subst h
    rw [List.mem_singleton, ModelIndex.indVal_eq]
    exact hx
  | lit p sign =>
    cases sign with
    | false => simp [gciAnchorWorlds] at h
    | true =>
      simp only [gciAnchorWorlds] at h
      split at h
      · rename_i hord
        cases h
        have ⟨h1, h2⟩ := ordinaryClass_ne hord
        simp only [holds, h1, h2, ↓reduceIte] at hx
        exact (ModelIndex.mem_atomWorlds_iff m p x).mpr hx
      · cases h
  | some r body _ =>
    simp only [gciAnchorWorlds] at h
    split at h
    · rename_i hord
      cases h
      obtain ⟨y, hr, _⟩ := hx
      exact ModelIndex.mem_edgeSources_of_edge m ((evalOriented_iff hord).mpr hr)
    · cases h
  | dataSome dp d =>
    simp only [gciAnchorWorlds] at h
    split at h
    · rename_i hord
      cases h
      have ⟨h1, h2⟩ := ordinaryDataProp_ne hord
      simp only [holds, h1, h2, ↓reduceIte] at hx
      obtain ⟨y, ⟨v, rfl, hedge⟩, _⟩ := hx
      exact ModelIndex.mem_dataSources_of_edge m hedge
    · cases h
  | conj a b iha ihb =>
    simp only [gciAnchorWorlds, HOrElse.hOrElse, OrElse.orElse] at h
    cases ha : gciAnchorWorlds (ModelIndex.build m) a with
    | some wa =>
      rw [ha] at h; cases h
      exact iha ha hx.1
    | none =>
      rw [ha] at h
      exact ihb h hx.2
  | _ => simp [gciAnchorWorlds] at h

private def walkTargets {m : SROIQDModel} (idx : ModelIndex m) (x : m.graph.World) :
    List OrientedRole → List m.graph.World
  | [] => [x]
  | r :: rs => (idx.neighbors r x).flatMap fun y => walkTargets idx y rs

private theorem mem_walkTargets_of_objPath (m : SROIQDModel) {rs : List OrientedRole}
    (hord : ∀ r ∈ rs, isOrdinaryObjProp r.1 = true) {x y : m.graph.World}
    (hp : objPath m.toInterpretation rs x y) :
    y ∈ walkTargets (ModelIndex.build m) x rs := by
  induction rs generalizing x with
  | nil =>
    cases hp; exact List.mem_singleton_self _
  | cons r tl ih =>
    obtain ⟨z, hrz, hpt⟩ := hp
    refine List.mem_flatMap.mpr ⟨z, ?_, ih (fun s hs => hord s (List.mem_cons_of_mem _ hs)) hpt⟩
    exact (ModelIndex.mem_neighbors_iff m r x z).mpr ((evalOriented_iff (hord r (List.mem_cons_self ..))).mpr hrz)

private def checkChainFast {m : SROIQDModel} (idx : ModelIndex m) (c : RoleChains.Chain) : Bool :=
  match c.body with
  | [] => m.graph.worlds.all fun x => idx.edgeSet.contains (c.head, x, x)
  | r0 :: rs =>
    (idx.edgesByRole.getD r0.1 []).all fun (u, v) =>
      let x := if r0.2 then v else u
      let mid := if r0.2 then u else v
      (walkTargets idx mid rs).all fun y => idx.edgeSet.contains (c.head, x, y)

private def checkGCIFast {m : SROIQDModel} (idx : ModelIndex m) (q : Inclusion) : Bool :=
  let checkAt (x : m.graph.World) : Bool :=
    match evalFast? idx x q.sub with
    | some false => true
    | some true => evalFast? idx x q.sup == some true
    | none => false
  match q.sub, q.sup with
  | .top, .all r _ =>
    if isOrdinaryObjProp r.1 then (idx.edgeSources.getD r []).all checkAt
    else m.graph.worlds.all checkAt
  | .top, .max _ r _ =>
    if isOrdinaryObjProp r.1 then (idx.edgeSources.getD r []).all checkAt
    else m.graph.worlds.all checkAt
  | _, _ =>
    match gciAnchorWorlds idx q.sub with
    | some ws => ws.all checkAt
    | none => m.graph.worlds.all checkAt

private theorem checkGCIFast_sound (m : SROIQDModel) (q : Inclusion)
    (h : checkGCIFast (ModelIndex.build m) q = true) (x : m.graph.World)
    (hx : holds m.toInterpretation x q.sub) : holds m.toInterpretation x q.sup := by
  have hCheckAt : (match evalFast? (ModelIndex.build m) x q.sub with
      | some false => true
      | some true => evalFast? (ModelIndex.build m) x q.sup == some true
      | none => false) = true → holds m.toInterpretation x q.sup := by
    intro hc
    cases hs : evalFast? (ModelIndex.build m) x q.sub with
    | none => simp [hs] at hc
    | some bs =>
      cases bs with
      | false => exact Bool.noConfusion ((evalFast?_sound m x q.sub hs).mpr hx)
      | true =>
        simp only [hs, beq_iff_eq] at hc
        exact (evalFast?_sound m x q.sup hc).mp rfl
  have hFallback : (match gciAnchorWorlds (ModelIndex.build m) q.sub with
      | some ws => ws.all fun y => match evalFast? (ModelIndex.build m) y q.sub with
          | some false => true | some true => evalFast? (ModelIndex.build m) y q.sup == some true | none => false
      | none => m.graph.worlds.all fun y => match evalFast? (ModelIndex.build m) y q.sub with
          | some false => true | some true => evalFast? (ModelIndex.build m) y q.sup == some true | none => false) = true →
      holds m.toInterpretation x q.sup := by
    intro hfb
    cases ha : gciAnchorWorlds (ModelIndex.build m) q.sub with
    | some ws =>
      rw [ha] at hfb
      exact hCheckAt (List.all_eq_true.mp hfb x (gciAnchorWorlds_complete m ha hx))
    | none =>
      rw [ha] at hfb
      exact hCheckAt (List.all_eq_true.mp hfb x (List.mem_finRange _))
  unfold checkGCIFast at h
  rcases q with ⟨qsub, qsup⟩
  dsimp only at h hCheckAt hFallback hx ⊢
  match qsub, qsup with
  | .top, .all r body =>
    dsimp only at h
    split at h
    · rename_i hordR'
      intro y hy
      have hxsrc := ModelIndex.mem_edgeSources_of_edge m ((evalOriented_iff hordR').mpr hy)
      exact (hCheckAt (List.all_eq_true.mp h x hxsrc)) y hy
    · exact hCheckAt (List.all_eq_true.mp h x (List.mem_finRange _))
  | .top, .max n r body =>
    dsimp only at h
    split at h
    · rename_i hordR'
      rintro ⟨ys, hylen, hynd, hyq⟩
      cases ys with
      | nil => simp at hylen
      | cons y0 _ =>
        have hy0 := (hyq y0 (List.mem_cons_self ..)).1
        have hxsrc := ModelIndex.mem_edgeSources_of_edge m ((evalOriented_iff hordR').mpr hy0)
        exact (hCheckAt (List.all_eq_true.mp h x hxsrc)) ⟨y0 :: _, hylen, hynd, hyq⟩
    · exact hCheckAt (List.all_eq_true.mp h x (List.mem_finRange _))
  | .top, .top | .top, .bottom | .top, .lit _ _ | .top, .nom _ _ | .top, .self _ _
  | .top, .conj _ _ | .top, .disj _ _ | .top, .some _ _ | .top, .min _ _ _
  | .top, .dataSome _ _ | .top, .dataAll _ _ | .top, .dataValue _ _ _
  | .top, .dataMin _ _ _ | .top, .dataMax _ _ _
  | .bottom, _ | .lit _ _, _ | .nom _ _, _ | .self _ _, _
  | .conj _ _, _ | .disj _ _, _ | .some _ _, _ | .all _ _, _ | .min _ _ _, _ | .max _ _ _, _
  | .dataSome _ _, _ | .dataAll _ _, _ | .dataValue _ _ _, _ | .dataMin _ _ _, _ | .dataMax _ _ _, _ =>
    exact hFallback h

private def checkModelBody (p : Problem) (m : SROIQDModel) : Bool :=
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
  if !objOrdinary then false
  else
    let idx := ModelIndex.build m
    p.rules.all (fun (r, s) =>
      (idx.edgesByRole.getD r.1 []).all fun (u, v) =>
        let x := if r.2 then v else u
        let y := if r.2 then u else v
        idx.hasOriented s x y) &&
    p.chains.all (checkChainFast idx) &&
    p.chars.reflexive.all (fun r => m.graph.worlds.all fun x => idx.edgeSet.contains (r, x, x)) &&
    p.chars.irreflexive.all (fun r => (idx.edgesByRole.getD r []).all fun (x, y) => x != y) &&
    p.chars.asymmetric.all (fun r => (idx.edgesByRole.getD r []).all fun (x, y) => !idx.edgeSet.contains (r, y, x)) &&
    p.chars.disjoint.all (fun (r, s) =>
      (idx.edgesByRole.getD r.1 []).all fun (u, v) =>
        let x := if r.2 then v else u
        let y := if r.2 then u else v
        !idx.hasOriented s x y) &&
    p.subData.all (fun (r, s) => (idx.dataSources.getD r []).all fun x =>
      (idx.dataVals r x).all fun v => (idx.dataVals s x).contains v) &&
    p.disjointData.all (fun (r, s) => (idx.dataSources.getD r []).all fun x =>
      (idx.dataVals r x).all fun v => !(idx.dataVals s x).contains v) &&
    p.funcData.all (fun dp => (idx.dataSources.getD dp []).all fun x => (idx.dataVals dp x).length ≤ 1) &&
    p.dataRanges.all (fun (dp, d) =>
      match compile d with
      | some comp => (idx.dataSources.getD dp []).all fun x => (idx.dataVals dp x).all comp.holds
      | none => false) &&
    p.tbox.all (checkGCIFast idx) &&
    p.keys.all (fun k => m.graph.worlds.all fun x => m.graph.worlds.all fun y =>
      match evalFast? idx x k.cls, evalFast? idx y k.cls with
      | some bx, some by' =>
        !(idx.isNamedWorld x && idx.isNamedWorld y && bx && by' &&
          k.objProps.all (fun r => (idx.neighbors r x).any fun z =>
            idx.isNamedWorld z && idx.hasOriented r y z) &&
          k.dataProps.all (fun dp => (idx.dataVals dp x).any fun v => (idx.dataVals dp y).contains v)) || (x == y)
      | _, _ => false) &&
    p.classAssertions.all (fun (a, c) => evalFast? idx (idx.indVal a) c == some true) &&
    p.objAssertions.all (fun (r, a, b) => idx.edgeSet.contains (r, idx.indVal a, idx.indVal b)) &&
    p.negObjAssertions.all (fun (r, a, b) => !idx.edgeSet.contains (r, idx.indVal a, idx.indVal b)) &&
    p.sameInds.all (fun (a, b) => idx.indVal a == idx.indVal b) &&
    p.diffInds.all (fun (a, b) => idx.indVal a != idx.indVal b) &&
    p.dataAssertions.all (fun (dp, a, l) =>
      match decodeLiteral l with | some v => (idx.dataVals dp (idx.indVal a)).contains v | none => false) &&
    p.negDataAssertions.all (fun (dp, a, l) =>
      match decodeLiteral l with | some v => !(idx.dataVals dp (idx.indVal a)).contains v | none => false)

def checkModel (p : Problem) (m : SROIQDModel) : Bool :=
  checkModelBody p m &&
  m.graph.worlds.any (fun x => eval? m x p.root == some true)

theorem checkModel_sound {p : Problem} {m : SROIQDModel} (h : checkModel p m = true) : p.Sat := by
  unfold checkModel at h
  obtain ⟨hbody, hroot⟩ := Bool.and_eq_true_iff.mp h
  unfold checkModelBody at hbody
  dsimp only at hbody
  split at hbody
  · cases hbody
  · rename_i hordNot
    have hord : (p.rules.all (fun (r, s) => isOrdinaryObjProp r.1 && isOrdinaryObjProp s.1) &&
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
      p.negDataAssertions.all (fun (r, _, _) => isOrdinaryDataProp r)) = true := by
      cases hc : (p.rules.all (fun (r, s) => isOrdinaryObjProp r.1 && isOrdinaryObjProp s.1) &&
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
        p.negDataAssertions.all (fun (r, _, _) => isOrdinaryDataProp r))
      · simp [hc] at hordNot
      · rfl
    simp only [Bool.and_eq_true] at hbody hord
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hrules, hchains⟩, href⟩, hirr⟩, hasym⟩, hdisj⟩, hsubD⟩, hdisjD⟩, hfunc⟩, hdr⟩, htbox⟩, hkeys⟩,
      hca⟩, hoa⟩, hnoa⟩, hsame⟩, hdiff⟩, hda⟩, hnda⟩
    rcases hord with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hordR, hordC⟩, hordRef⟩, hordIrr⟩, hordAsym⟩, hordDisj⟩, hordSubD⟩, hordDisjD⟩, hordKeys⟩,
      hordOA⟩, hordNOA⟩, hordFD⟩, hordDR⟩, hordDA⟩, hordNDA⟩
    obtain ⟨x0, _, hx0⟩ := List.any_eq_true.mp hroot
    have hx0' : holds m.toInterpretation x0 p.root := (eval?_sound m x0 p.root (beq_iff_eq.mp hx0)).mp rfl
    refine ⟨m.toInterpretation, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, x0, hx0'⟩
    · -- tbox
      intro q hq x hx
      exact checkGCIFast_sound m q (List.all_eq_true.mp htbox q hq) x hx
    · -- rules
      intro rs hrs x y hxy
      have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordR rs hrs)
      have hxyE : evalOriented m.graph rs.1 x y = true := (evalOriented_iff ho1).mpr hxy
      have hrule := List.all_eq_true.mp hrules rs hrs
      rcases rs with ⟨⟨r1, b1⟩, s⟩
      cases b1 with
      | false =>
        simp only [evalOriented, Bool.false_eq_true, ↓reduceIte] at hxyE
        have hmem := (ModelIndex.mem_edgesByRole_iff m r1 x y).mpr hxyE
        have hok := List.all_eq_true.mp hrule (x, y) hmem
        simp only [Bool.false_eq_true, ↓reduceIte, ModelIndex.hasOriented_eq] at hok
        exact (evalOriented_iff ho2).mp hok
      | true =>
        simp only [evalOriented, ↓reduceIte] at hxyE
        have hmem := (ModelIndex.mem_edgesByRole_iff m r1 y x).mpr hxyE
        have hok := List.all_eq_true.mp hrule (y, x) hmem
        simp only [↓reduceIte, ModelIndex.hasOriented_eq] at hok
        exact (evalOriented_iff ho2).mp hok
    · -- chains
      intro c hc x y hp
      have ⟨hch, hcb⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordC c hc)
      have ⟨ha, hb⟩ := ordinaryObjProp_ne hch
      simp only [ha, hb, ↓reduceIte]
      have hck := List.all_eq_true.mp hchains c hc
      unfold checkChainFast at hck
      cases hbodyC : c.body with
      | nil =>
        rw [hbodyC] at hp hck
        cases hp
        have := List.all_eq_true.mp hck x (List.mem_finRange _)
        rwa [ModelIndex.edgeSet_eq] at this
      | cons r0 rs =>
        rw [hbodyC] at hp hck
        obtain ⟨mid, hr0, hprs⟩ := hp
        have hordBody : ∀ r ∈ r0 :: rs, isOrdinaryObjProp r.1 = true := fun r hr =>
          List.all_eq_true.mp hcb r.1 (by rw [RoleChains.Chain.bodyNames, hbodyC]; exact List.mem_map_of_mem hr)
        have hr0E : evalOriented m.graph r0 x mid = true :=
          (evalOriented_iff (hordBody r0 (List.mem_cons_self ..))).mpr hr0
        have hyWalk : y ∈ walkTargets (ModelIndex.build m) mid rs :=
          mem_walkTargets_of_objPath m (fun r hr => hordBody r (List.mem_cons_of_mem _ hr)) hprs
        rcases r0 with ⟨r0n, b0⟩
        cases b0 with
        | false =>
          simp only [evalOriented, Bool.false_eq_true, ↓reduceIte] at hr0E
          have hmem := (ModelIndex.mem_edgesByRole_iff m r0n x mid).mpr hr0E
          have h1 := List.all_eq_true.mp hck (x, mid) hmem
          simp only [Bool.false_eq_true, ↓reduceIte] at h1
          have h2 := List.all_eq_true.mp h1 y hyWalk
          rwa [ModelIndex.edgeSet_eq] at h2
        | true =>
          simp only [evalOriented, ↓reduceIte] at hr0E
          have hmem := (ModelIndex.mem_edgesByRole_iff m r0n mid x).mpr hr0E
          have h1 := List.all_eq_true.mp hck (mid, x) hmem
          simp only [↓reduceIte] at h1
          have h2 := List.all_eq_true.mp h1 y hyWalk
          rwa [ModelIndex.edgeSet_eq] at h2
    · -- reflexive
      intro r hr x
      have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordRef r hr)
      simp only [ha, hb, ↓reduceIte]
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp href r hr) x (List.mem_finRange _)
      rwa [ModelIndex.edgeSet_eq] at h1
    · -- irreflexive
      intro r hr x hxx
      have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordIrr r hr)
      simp only [ha, hb, ↓reduceIte] at hxx
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp hirr r hr) (x, x)
        ((ModelIndex.mem_edgesByRole_iff m r x x).mpr hxx)
      simp at h1
    · -- asymmetric
      intro r hr x y hxy hyx
      have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordAsym r hr)
      simp only [ha, hb, ↓reduceIte] at hxy hyx
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp hasym r hr) (x, y)
        ((ModelIndex.mem_edgesByRole_iff m r x y).mpr hxy)
      rw [ModelIndex.edgeSet_eq] at h1
      simp [hyx] at h1
    · -- disjoint
      intro rs hrs x y ⟨h1, h2⟩
      have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordDisj rs hrs)
      have h1' := (evalOriented_iff ho1).mpr h1
      have h2' := (evalOriented_iff ho2).mpr h2
      have hchk := List.all_eq_true.mp hdisj rs hrs
      rcases rs with ⟨⟨r1, b1⟩, s⟩
      cases b1 with
      | false =>
        simp only [evalOriented, Bool.false_eq_true, ↓reduceIte] at h1'
        have hok := List.all_eq_true.mp hchk (x, y) ((ModelIndex.mem_edgesByRole_iff m r1 x y).mpr h1')
        simp only [Bool.false_eq_true, ↓reduceIte, ModelIndex.hasOriented_eq] at hok
        rw [h2'] at hok; cases hok
      | true =>
        simp only [evalOriented, ↓reduceIte] at h1'
        have hok := List.all_eq_true.mp hchk (y, x) ((ModelIndex.mem_edgesByRole_iff m r1 y x).mpr h1')
        simp only [↓reduceIte, ModelIndex.hasOriented_eq] at hok
        rw [h2'] at hok; cases hok
    · -- subData
      intro rs hrs x y hy
      have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordSubD rs hrs)
      have ⟨ha1, hb1⟩ := ordinaryDataProp_ne ho1
      have ⟨ha2, hb2⟩ := ordinaryDataProp_ne ho2
      simp only [ha1, hb1, ha2, hb2, ↓reduceIte] at hy ⊢
      obtain ⟨v, rfl, hv⟩ := hy
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hsubD rs hrs) x
        (ModelIndex.mem_dataSources_of_edge m hv)) v ((ModelIndex.mem_dataVals_iff m rs.1 x v).mpr hv)
      exact ⟨v, rfl, (ModelIndex.mem_dataVals_iff m rs.2 x v).mp (List.contains_iff_mem.mp h1)⟩
    · -- disjointData
      intro rs hrs x y ⟨h1, h2⟩
      have ⟨ho1, ho2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordDisjD rs hrs)
      have ⟨ha1, hb1⟩ := ordinaryDataProp_ne ho1
      have ⟨ha2, hb2⟩ := ordinaryDataProp_ne ho2
      simp only [ha1, hb1, ha2, hb2, ↓reduceIte] at h1 h2
      obtain ⟨v, rfl, hv1⟩ := h1
      obtain ⟨v', heq, hv2⟩ := h2
      cases heq
      have hchk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hdisjD rs hrs) x
        (ModelIndex.mem_dataSources_of_edge m hv1)) v ((ModelIndex.mem_dataVals_iff m rs.1 x v).mpr hv1)
      have hmem2 : ((ModelIndex.build m).dataVals rs.2 x).contains v = true :=
        List.contains_iff_mem.mpr ((ModelIndex.mem_dataVals_iff m rs.2 x v).mpr hv2)
      rw [hmem2] at hchk; cases hchk
    · -- funcData
      intro dp hdp x y z hy hz
      have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordFD dp hdp)
      simp only [ha, hb, ↓reduceIte] at hy hz
      obtain ⟨v1, rfl, h1⟩ := hy
      obtain ⟨v2, rfl, h2⟩ := hz
      have hlen : ((ModelIndex.build m).dataVals dp x).length ≤ 1 :=
        of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hfunc dp hdp) x
          (ModelIndex.mem_dataSources_of_edge m h1))
      have hm1 := (ModelIndex.mem_dataVals_iff m dp x v1).mpr h1
      have hm2 := (ModelIndex.mem_dataVals_iff m dp x v2).mpr h2
      cases hvs : (ModelIndex.build m).dataVals dp x with
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
        have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1 x (ModelIndex.mem_dataSources_of_edge m hv)) v
          ((ModelIndex.mem_dataVals_iff m rd.1 x v).mpr hv)
        exact (comp.holds_iff m.toInterpretation v).mp h2
    · -- keys
      intro k hk x y hx hy hnx hny ho hd
      have ⟨hko, hkd⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hordKeys k hk)
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hkeys k hk) x (List.mem_finRange _)) y (List.mem_finRange _)
      cases hex : evalFast? (ModelIndex.build m) x k.cls with
      | none => simp [hex] at h1
      | some bx =>
        cases hey : evalFast? (ModelIndex.build m) y k.cls with
        | none => simp [hex, hey] at h1
        | some by' =>
          simp only [hex, hey, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
          have hbx : bx = true := (evalFast?_sound m x k.cls hex).mpr hx
          have hby : by' = true := (evalFast?_sound m y k.cls hey).mpr hy
          have hob : k.objProps.all (fun r => ((ModelIndex.build m).neighbors r x).any fun z =>
              (ModelIndex.build m).isNamedWorld z && (ModelIndex.build m).hasOriented r y z) = true := by
            rw [List.all_eq_true]
            intro r hr
            obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
            have hord' := List.all_eq_true.mp hko r hr
            exact List.any_eq_true.mpr ⟨z,
              (ModelIndex.mem_neighbors_iff m r x z).mpr ((evalOriented_iff hord').mpr hxz),
              Bool.and_eq_true_iff.mpr
                ⟨by rw [ModelIndex.isNamedWorld_eq]; exact hnz,
                 by rw [ModelIndex.hasOriented_eq]; exact (evalOriented_iff hord').mpr hyz⟩⟩
          have hdb : k.dataProps.all (fun dp => ((ModelIndex.build m).dataVals dp x).any fun v =>
              ((ModelIndex.build m).dataVals dp y).contains v) = true := by
            rw [List.all_eq_true]
            intro dp hdp
            obtain ⟨z, hxz, hyz⟩ := hd dp hdp
            have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hkd dp hdp)
            simp only [ha, hb, ↓reduceIte] at hxz hyz
            obtain ⟨v, rfl, hvx⟩ := hxz
            obtain ⟨v', heq, hvy⟩ := hyz
            cases heq
            exact List.any_eq_true.mpr ⟨v, (ModelIndex.mem_dataVals_iff m dp x v).mpr hvx,
              List.contains_iff_mem.mpr ((ModelIndex.mem_dataVals_iff m dp y v).mpr hvy)⟩
          have hnx' : (ModelIndex.build m).isNamedWorld x = true := by rw [ModelIndex.isNamedWorld_eq]; exact hnx
          have hny' : (ModelIndex.build m).isNamedWorld y = true := by rw [ModelIndex.isNamedWorld_eq]; exact hny
          exact h1.resolve_left (by simp only [hnx', hny', hbx, hby, hob, hdb, Bool.and_self]; decide)
    · -- classAssertions
      intro ac hac
      have h1 := beq_iff_eq.mp (List.all_eq_true.mp hca ac hac)
      rw [ModelIndex.indVal_eq] at h1
      exact (evalFast?_sound m (m.indVal ac.1) ac.2 h1).mp rfl
    · -- objAssertions
      intro rab hrab
      have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordOA rab hrab)
      simp only [ha, hb, ↓reduceIte]
      have h1 := List.all_eq_true.mp hoa rab hrab
      rwa [ModelIndex.edgeSet_eq, ModelIndex.indVal_eq, ModelIndex.indVal_eq] at h1
    · -- negObjAssertions
      intro rab hrab
      have ⟨ha, hb⟩ := ordinaryObjProp_ne (List.all_eq_true.mp hordNOA rab hrab)
      simp only [ha, hb, ↓reduceIte]
      have h1 := List.all_eq_true.mp hnoa rab hrab
      rw [ModelIndex.edgeSet_eq, ModelIndex.indVal_eq, ModelIndex.indVal_eq] at h1
      simpa using h1
    · -- sameInds
      intro ab hab
      have h1 := beq_iff_eq.mp (List.all_eq_true.mp hsame ab hab)
      rwa [ModelIndex.indVal_eq, ModelIndex.indVal_eq] at h1
    · -- diffInds
      intro ab hab
      have h1 := bne_iff_ne.mp (List.all_eq_true.mp hdiff ab hab)
      rwa [ModelIndex.indVal_eq, ModelIndex.indVal_eq] at h1
    · -- dataAssertions
      intro ral hral
      have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordDA ral hral)
      simp only [ha, hb, ↓reduceIte]
      have h1 := List.all_eq_true.mp hda ral hral
      cases hl : decodeLiteral ral.2.2 with
      | none => simp [hl] at h1
      | some v =>
        simp only [hl, ModelIndex.indVal_eq] at h1
        exact ⟨v, rfl, (ModelIndex.mem_dataVals_iff m ral.1 (m.indVal ral.2.1) v).mp (List.contains_iff_mem.mp h1)⟩
    · -- negDataAssertions
      intro ral hral
      have ⟨ha, hb⟩ := ordinaryDataProp_ne (List.all_eq_true.mp hordNDA ral hral)
      simp only [ha, hb, ↓reduceIte]
      have h1 := List.all_eq_true.mp hnda ral hral
      cases hl : decodeLiteral ral.2.2 with
      | none => simp [hl] at h1
      | some v =>
        simp only [hl, Bool.not_eq_true', ModelIndex.indVal_eq] at h1
        rintro ⟨v', hv', hedge⟩
        cases hv'
        have hm := List.contains_iff_mem.mpr ((ModelIndex.mem_dataVals_iff m ral.1 (m.indVal ral.2.1) v).mpr hedge)
        rw [h1] at hm; cases hm

/-- Hash-indexed extraction of all `(c, d)` pairs (`c ∈ srcClasses`, `d ∈ dstClasses`,
    non-built-in) separated at some world of `m` (`c` holds and `d` does not). -/
def SROIQDModel.separatedPairsFrom (m : SROIQDModel) (srcClasses dstClasses : List IRI) :
    List (IRI × IRI) :=
  let idx := ModelIndex.build m
  srcClasses.flatMap fun c =>
    if c == thing || c == nothing then []
    else
      let ws := idx.atomWorlds.getD c []
      if ws.isEmpty then []
      else dstClasses.filterMap fun d =>
        if d != thing && d != nothing && d != c && ws.any (fun w => !idx.atomSet.contains (d, w)) then
          some (c, d)
        else none

theorem SROIQDModel.separatedPairsFrom_sound {m : SROIQDModel} {srcClasses dstClasses : List IRI}
    {pair : IRI × IRI} (hmem : pair ∈ m.separatedPairsFrom srcClasses dstClasses) :
    pair.1 ≠ thing ∧ pair.1 ≠ nothing ∧ pair.2 ≠ thing ∧ pair.2 ≠ nothing ∧
    m.graph.worlds.any (fun w => eval? m w (.conj (.atom pair.1) (Concept.atom pair.2).dual) == some true) = true := by
  unfold SROIQDModel.separatedPairsFrom at hmem
  obtain ⟨c, _, hinner⟩ := List.mem_flatMap.mp hmem
  split at hinner
  · cases hinner
  · rename_i hcNot
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcNot
    dsimp only at hinner
    split at hinner
    · cases hinner
    · obtain ⟨d, _, hflt⟩ := List.mem_filterMap.mp hinner
      split at hflt
      · rename_i hcond
        simp only [Option.some.injEq] at hflt
        subst hflt
        simp only [Bool.and_eq_true, bne_iff_ne, List.any_eq_true, Bool.not_eq_true'] at hcond
        obtain ⟨⟨⟨hdT, hdN⟩, _⟩, ⟨w, hwC, hwNotD⟩⟩ := hcond
        have hcAt : m.graph.atom c w = true := (ModelIndex.mem_atomWorlds_iff m c w).mp hwC
        have hdAt : m.graph.atom d w = false := by
          rw [← ModelIndex.atomSet_eq m d w]; exact hwNotD
        have hordC : isOrdinaryClass c = true := by
          simp [isOrdinaryClass]; exact hcNot
        have hordD : isOrdinaryClass d = true := by
          simp [isOrdinaryClass]; exact ⟨hdT, hdN⟩
        refine ⟨hcNot.1, hcNot.2, hdT, hdN, List.any_eq_true.mpr ⟨w, List.mem_finRange w, ?_⟩⟩
        simp [Concept.dual, eval?, hordC, hordD, hcAt, hdAt]
      · cases hflt

/-- Hash-indexed extraction of all classes in `namedClasses` satisfied at some world of `m`. -/
def SROIQDModel.satClasses (m : SROIQDModel) (namedClasses : List IRI) : List IRI :=
  let idx := ModelIndex.build m
  namedClasses.filter fun c =>
    c != thing && c != nothing && !(idx.atomWorlds.getD c []).isEmpty

end Sabrina.OWL2.SROIQD
