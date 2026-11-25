import Sabrina.RoleChains.TransitiveCompletion

namespace Sabrina.RoleChains

open Sabrina.ALC

abbrev Word := List OrientedRole
abbrev Language := Word → Prop

inductive Repeats (L : Language) : Language where
  | nil : Repeats L []
  | cons {u v} : L u → Repeats L v → Repeats L (u ++ v)

theorem Repeats.append {L : Language} {u v : Word} (hu : Repeats L u) (hv : Repeats L v) :
    Repeats L (u ++ v) := by
  induction hu with
  | nil => exact hv
  | cons h _ ih => simpa only [List.append_assoc] using Repeats.cons h ih

inductive PathRegex where
  | zero | epsilon
  | symbol (r : OrientedRole)
  | alt (a b : PathRegex)
  | seq (a b : PathRegex)
  | star (a : PathRegex)
  deriving DecidableEq, Repr

namespace PathRegex

def Matches : PathRegex → Language
  | .zero => fun _ => False
  | .epsilon => (· = [])
  | .symbol r => (· = [r])
  | .alt a b => fun w => Matches a w ∨ Matches b w
  | .seq a b => fun w => ∃ u v, Matches a u ∧ Matches b v ∧ w = u ++ v
  | .star a => Repeats (Matches a)

def choice (es : List PathRegex) : PathRegex := es.foldr .alt .zero

def sequence (es : List PathRegex) : PathRegex := es.foldr .seq .epsilon

theorem matches_choice (es : List PathRegex) (w : Word) :
    (choice es).Matches w ↔ ∃ e ∈ es, e.Matches w := by
  induction es with
  | nil => simp [choice, Matches]
  | cons h t ih =>
    change h.Matches w ∨ (choice t).Matches w ↔ _
    rw [ih]
    constructor
    · rintro (hh | ⟨e, he, hw⟩)
      · exact ⟨h, List.mem_cons_self .., hh⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, hw⟩
    · rintro ⟨e, he, hw⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl hw
      · exact Or.inr ⟨e, he, hw⟩

/-- A word divided into successive segments accepted by a list of languages. -/
inductive Segments : List Language → Language where
  | nil : Segments [] []
  | cons {L ls u v} : L u → Segments ls v → Segments (L :: ls) (u ++ v)

theorem matches_sequence (es : List PathRegex) (w : Word) :
    (sequence es).Matches w ↔ Segments (es.map Matches) w := by
  induction es generalizing w with
  | nil =>
    constructor
    · intro h
      change w = [] at h
      subst w
      exact .nil
    · intro h
      cases h
      rfl
  | cons head tail ih =>
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact .cons hu ((ih v).mp hv)
    · intro h
      cases h with
      | cons hu hv => exact ⟨_, _, hu, (ih _).mpr hv, rfl⟩

def nullable : PathRegex → Bool
  | .zero | .symbol _ => false
  | .epsilon | .star _ => true
  | .alt a b => a.nullable || b.nullable
  | .seq a b => a.nullable && b.nullable

theorem nullable_iff (e : PathRegex) : e.nullable = true ↔ e.Matches [] := by
  induction e with
  | zero | epsilon | symbol => simp [nullable, Matches]
  | alt a b ha hb => simp [nullable, Matches, ha, hb]
  | seq a b ha hb =>
    constructor
    · intro h
      simp only [nullable, Bool.and_eq_true] at h
      exact ⟨[], [], ha.mp h.1, hb.mp h.2, rfl⟩
    · rintro ⟨u,v,hu,hv,hw⟩
      obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp hw.symm
      simp only [nullable, Bool.and_eq_true]
      exact ⟨ha.mpr hu,hb.mpr hv⟩
  | star a _ => exact ⟨fun _ => .nil, fun _ => rfl⟩

/-- Partial derivatives give the transitions of a finite automaton. -/
def derivative (r : OrientedRole) : PathRegex → List PathRegex
  | .zero | .epsilon => []
  | .symbol s => if r == s then [.epsilon] else []
  | .alt a b => a.derivative r ++ b.derivative r
  | .seq a b =>
    (a.derivative r).map (fun p => .seq p b) ++ if a.nullable then b.derivative r else []
  | .star a => (a.derivative r).map (fun p => .seq p (.star a))

private theorem repeats_cons_iff {L : Language} {r : OrientedRole} {w : Word} :
    Repeats L (r :: w) ↔ ∃ u v, L (r :: u) ∧ Repeats L v ∧ w = u ++ v := by
  constructor
  · intro h
    generalize he : r :: w = word at h
    induction h with
    | nil => cases he
    | @cons a b ha hb ih =>
      cases a with
      | nil => exact ih he
      | cons s tail =>
        have ⟨eq, hw⟩ := List.cons.inj he
        subst s
        exact ⟨tail,b,ha,hb,hw⟩
  · rintro ⟨u,v,hu,hv,rfl⟩
    exact .cons hu hv

theorem matches_derivative (e : PathRegex) (r : OrientedRole) (w : Word) :
    e.Matches (r :: w) ↔ ∃ p ∈ e.derivative r, p.Matches w := by
  induction e generalizing w with
  | zero | epsilon => simp [derivative, Matches]
  | symbol s =>
    by_cases h : r = s <;> simp [derivative, Matches, h]
  | alt a b ha hb =>
    simp only [Matches, derivative, ha, hb, List.mem_append]
    constructor
    · rintro (⟨p,hp,hw⟩ | ⟨p,hp,hw⟩)
      · exact ⟨p,Or.inl hp,hw⟩
      · exact ⟨p,Or.inr hp,hw⟩
    · rintro ⟨p,hp,hw⟩
      exact hp.elim (fun h => Or.inl ⟨p,h,hw⟩) (fun h => Or.inr ⟨p,h,hw⟩)
  | seq a b ha hb =>
    constructor
    · rintro ⟨u,v,hu,hv,hw⟩
      cases u with
      | nil =>
        have hn := a.nullable_iff.mpr hu
        change r :: w = v at hw
        subst v
        obtain ⟨p,hp,hm⟩ := (hb _).mp hv
        exact ⟨p,List.mem_append_right _ (by simpa [hn] using hp),hm⟩
      | cons s tail =>
        obtain ⟨hr,hw⟩ := List.cons.inj hw
        subst s
        obtain ⟨p,hp,hm⟩ := (ha _).mp hu
        exact ⟨.seq p b,List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩),tail,v,hm,hv,by simpa using hw⟩
    · rintro ⟨p,hp,hw⟩
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hp
        obtain ⟨u,v,hu,hv,rfl⟩ := hw
        exact ⟨r :: u,v,(ha _).mpr ⟨d,hd,hu⟩,hv,rfl⟩
      · by_cases hn : a.nullable = true
        · exact ⟨[],r :: w,a.nullable_iff.mp hn,
            (hb _).mpr ⟨p,by simpa [hn] using hp,hw⟩,rfl⟩
        · simp [hn] at hp
  | star a ih =>
    constructor
    · intro h
      obtain ⟨u,v,hu,hv,hw⟩ := repeats_cons_iff.mp h
      obtain ⟨p,hp,hm⟩ := (ih _).mp hu
      exact ⟨.seq p (.star a),List.mem_map.mpr ⟨p,hp,rfl⟩,u,v,hm,hv,hw⟩
    · rintro ⟨p,hp,hw⟩
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hp
      obtain ⟨u,v,hu,hv,he⟩ := hw
      exact repeats_cons_iff.mpr ⟨u,v,(ih _).mpr ⟨d,hd,hu⟩,hv,he⟩

def accepts (e : PathRegex) : Word → Bool
  | [] => e.nullable
  | r :: w => (e.derivative r).any fun p => p.accepts w

theorem accepts_iff (e : PathRegex) (w : Word) : e.accepts w = true ↔ e.Matches w := by
  induction w generalizing e with
  | nil => exact e.nullable_iff
  | cons r w ih =>
    rw [accepts, List.any_eq_true, matches_derivative]
    simp only [ih]

/-- All noninitial states that can be reached by taking derivatives. -/
def residuals : PathRegex → List PathRegex
  | .zero | .epsilon => []
  | .symbol _ => [.epsilon]
  | .alt a b => a.residuals ++ b.residuals
  | .seq a b => a.residuals.map (fun p => .seq p b) ++ b.residuals
  | .star a => a.residuals.map (fun p => .seq p (.star a))

theorem derivative_subset (e : PathRegex) (r : OrientedRole) :
    e.derivative r ⊆ e.residuals := by
  induction e with
  | zero | epsilon => simp [derivative, residuals]
  | symbol s =>
    intro p hp
    by_cases h : r = s <;> simp_all [derivative, residuals]
  | alt a b ha hb =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append_left _ (ha hp)
    · exact List.mem_append_right _ (hb hp)
  | seq a b ha hb =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hp
      exact List.mem_append_left _ (List.mem_map.mpr ⟨d,ha hd,rfl⟩)
    · by_cases h : a.nullable = true
      · exact List.mem_append_right _ (hb (by simpa [h] using hp))
      · simp [h] at hp
  | star a ha =>
    intro p hp
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨d,ha hd,rfl⟩

theorem residuals_closed {e p : PathRegex} (h : p ∈ e.residuals) (r : OrientedRole) :
    p.derivative r ⊆ e.residuals := by
  induction e generalizing p with
  | zero | epsilon => simp [residuals] at h
  | symbol s =>
    have hp : p = .epsilon := by simpa [residuals] using h
    subst p
    simp [derivative]
  | alt a b ha hb =>
    intro q hq
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (ha h hq)
    · exact List.mem_append_right _ (hb h hq)
  | seq a b ha hb =>
    intro q hq
    rcases List.mem_append.mp h with h | h
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hq
        exact List.mem_append_left _ (List.mem_map.mpr ⟨f,ha hd hf,rfl⟩)
      · by_cases hn : d.nullable = true
        · exact List.mem_append_right _ (derivative_subset b r (by simpa [hn] using hq))
        · simp [hn] at hq
    · exact List.mem_append_right _ (hb h hq)
  | star a ha =>
    intro q hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hq
      exact List.mem_map.mpr ⟨f,ha hd hf,rfl⟩
    · by_cases hn : d.nullable = true
      · exact derivative_subset (.star a) r (by simpa [hn] using hq)
      · simp [hn] at hq


private def alt' : PathRegex → PathRegex → PathRegex
  | .zero, b => b
  | a, .zero => a
  | a, b => .alt a b

private def seq' : PathRegex → PathRegex → PathRegex
  | .zero, _ | _, .zero => .zero
  | .epsilon, b => b
  | a, .epsilon => a
  | a, b => .seq a b

private def star' : PathRegex → PathRegex
  | .zero | .epsilon => .epsilon
  | a => .star a

def simplify : PathRegex → PathRegex
  | .alt a b => alt' a.simplify b.simplify
  | .seq a b => seq' a.simplify b.simplify
  | .star a => star' a.simplify
  | e => e

private theorem alt'_correct (a b : PathRegex) (w : Word) :
    (alt' a b).Matches w ↔ a.Matches w ∨ b.Matches w := by
  cases a <;> cases b <;> simp [alt', Matches]

private theorem seq'_correct (a b : PathRegex) (w : Word) :
    (seq' a b).Matches w ↔ ∃ u v, a.Matches u ∧ b.Matches v ∧ w = u ++ v := by
  cases a <;> cases b <;> simp [seq', Matches]

private theorem star'_correct (a : PathRegex) (w : Word) :
    (star' a).Matches w ↔ Repeats a.Matches w := by
  cases a with
  | zero =>
    constructor
    · rintro (rfl : w = []); exact .nil
    · intro h
      cases h with
      | nil => rfl
      | cons hh _ => exact hh.elim
  | epsilon =>
    constructor
    · rintro (rfl : w = []); exact .nil
    · intro h
      induction h with
      | nil => rfl
      | cons hu _ ih =>
        change _ = [] at hu
        rw [hu, ih]
        rfl
  | symbol | alt | seq | star => rfl

theorem simplify_correct (e : PathRegex) (w : Word) :
    e.simplify.Matches w ↔ e.Matches w := by
  induction e generalizing w with
  | zero | epsilon | symbol => rfl
  | alt a b ha hb => simp only [simplify, alt'_correct, ha, hb, Matches]
  | seq a b ha hb => simp only [simplify, seq'_correct, ha, hb, Matches]
  | star a ha =>
    rw [simplify, star'_correct]
    change Repeats a.simplify.Matches w ↔ Repeats a.Matches w
    constructor
    · intro h
      induction h with
      | nil => exact .nil
      | cons hu _ ih => exact .cons ((ha _).mp hu) ih
    · intro h
      induction h with
      | nil => exact .nil
      | cons hu _ ih => exact .cons ((ha _).mpr hu) ih

def letters : PathRegex → List OrientedRole
  | .zero | .epsilon => []
  | .symbol r => [r]
  | .alt a b | .seq a b => a.letters ++ b.letters
  | .star a => a.letters

theorem letters_of_matches {e : PathRegex} {w : Word} (h : e.Matches w) :
    w ⊆ e.letters := by
  induction e generalizing w with
  | zero => exact h.elim
  | epsilon =>
    change w = [] at h
    subst w
    simp [letters]
  | symbol s =>
    change w = [s] at h
    subst w
    exact fun _ h => h
  | alt a b ha hb =>
    intro r hr
    rcases h with h | h
    · exact List.mem_append_left _ (ha h hr)
    · exact List.mem_append_right _ (hb h hr)
  | seq a b ha hb =>
    obtain ⟨u,v,hu,hv,rfl⟩ := h
    intro s hs
    exact (List.mem_append.mp hs).elim
      (fun h => List.mem_append_left _ (ha hu h)) (fun h => List.mem_append_right _ (hb hv h))
  | star a ih =>
    change Repeats a.Matches w at h
    induction h with
    | nil => exact fun _ h => (List.not_mem_nil h).elim
    | cons hu _ ih' =>
      intro r hr
      exact (List.mem_append.mp hr).elim (fun h => ih hu h) (fun h => ih' h)

end PathRegex

end Sabrina.RoleChains
