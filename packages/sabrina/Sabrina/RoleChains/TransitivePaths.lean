import Sabrina.ALC.RoleTheory

namespace Sabrina.RoleChains.TransitivePaths

open Sabrina.ALC

/-- Reflexive use of the mirrored role hierarchy. -/
def Below (rules : RoleTheory) (r s : OrientedRole) : Prop :=
  r = s ∨ (r,s) ∈ roleClosure rules

theorem Below.refl (rules : RoleTheory) (r : OrientedRole) : Below rules r r := Or.inl rfl

theorem Below.step {rules : RoleTheory} {r s : OrientedRole}
    (h : (r,s) ∈ mirrored rules) : Below rules r s := Or.inr (ALCH.mem_close h)

theorem Below.trans {rules : RoleTheory} {r s t : OrientedRole}
    (hab : Below rules r s) (hbc : Below rules s t) : Below rules r t := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (ALCH.close_trans hab hbc)

@[simp] theorem converse_converse (r : OrientedRole) : converse (converse r) = r := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

theorem mirrored_flip {rules : RoleTheory} {r s : OrientedRole}
    (h : (r,s) ∈ mirrored rules) : (converse r, converse s) ∈ mirrored rules := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨(r,s), h, rfl⟩)
  · obtain ⟨⟨a,b⟩, hab, eq⟩ := List.mem_map.mp h
    cases eq
    change (converse (converse a), converse (converse b)) ∈ mirrored rules
    rw [converse_converse, converse_converse]
    exact List.mem_append_left _ hab

theorem Below.flip {rules : RoleTheory} {r s : OrientedRole}
    (h : Below rules r s) : Below rules (converse r) (converse s) := by
  rcases h with rfl | h
  · exact Below.refl _ _
  · exact ALCH.close_sound (R := fun a b => Below rules (converse a) (converse b))
      (fun h => Below.step (mirrored_flip h)) Below.trans h

/-- The role-word rules for transitivity, inclusions and inverse declarations.
    The Boolean orientation in the alphabet means that one base edge can be
    read in either direction. Transitivity also applies to a converse. -/
inductive Derives (rules : RoleTheory) (transitive : List String) :
    List OrientedRole → OrientedRole → Prop where
  | letter (r) : Derives rules transitive [r] r
  | promote {w r s} : (r,s) ∈ mirrored rules →
      Derives rules transitive w r → Derives rules transitive w s
  | join {w v r} : r.1 ∈ transitive →
      Derives rules transitive w r → Derives rules transitive v r →
      Derives rules transitive (w ++ v) r

theorem Derives.lift {rules : RoleTheory} {ts : List String} {w r s}
    (h : Below rules r s) (d : Derives rules ts w r) : Derives rules ts w s := by
  rcases h with rfl | h
  · exact d
  · exact ALCH.close_sound (R := fun a b => Derives rules ts w a → Derives rules ts w b)
      (fun h => Derives.promote h) (fun ha hb hd => hb (ha hd)) h d

/-- A compact finite NFA. The initial state accepts no letters. A singleton
    transition takes it to a final state with no outgoing edges. Each repeat
    alphabet gives another final state, entered on one letter of that alphabet
    and looping on the same alphabet. -/
structure Automaton where
  singletons : List OrientedRole
  repeats : List (List OrientedRole)

def Automaton.accepts (a : Automaton) : List OrientedRole → Bool
  | [] => false
  | r :: tail => (tail.isEmpty && a.singletons.contains r) ||
      a.repeats.any (fun letters => (r :: tail).all letters.contains)

def compile (rules : RoleTheory) (ts : List String) (target : OrientedRole) : Automaton :=
  let closed := roleClosure rules
  let letters := ALCH.subroles closed target
  let loops := letters.filter (fun r => ts.contains r.1)
  ⟨letters, loops.map (ALCH.subroles closed)⟩

private def Normal (rules : RoleTheory) (ts : List String)
    (word : List OrientedRole) (target : OrientedRole) : Prop :=
  (∃ r, word = [r] ∧ Below rules r target) ∨
  (∃ r, r.1 ∈ ts ∧ Below rules r target ∧ word ≠ [] ∧
    ∀ s ∈ word, Below rules s r)

private theorem normal_lift {rules ts word r s}
    (h : Below rules r s) : Normal rules ts word r → Normal rules ts word s := by
  rintro (⟨t, ht, htr⟩ | ⟨t, htt, htr, hn, hw⟩)
  · exact Or.inl ⟨t, ht, htr.trans h⟩
  · exact Or.inr ⟨t, htt, htr.trans h, hn, hw⟩

private theorem normal_letters {rules ts word r} (h : Normal rules ts word r) :
    word ≠ [] ∧ ∀ s ∈ word, Below rules s r := by
  rcases h with ⟨t, rfl, ht⟩ | ⟨t, _, ht, hn, ha⟩
  · exact ⟨by simp, fun s hs => (List.mem_singleton.mp hs).symm ▸ ht⟩
  · exact ⟨hn, fun s hs => (ha s hs).trans ht⟩

private theorem normal_of_derives {rules ts word r} (h : Derives rules ts word r) :
    Normal rules ts word r := by
  induction h with
  | letter r => exact Or.inl ⟨r, rfl, Below.refl _ _⟩
  | promote h _ ih => exact normal_lift (Below.step h) ih
  | join hr _ _ ih₁ ih₂ =>
    have ha := normal_letters ih₁
    have hb := normal_letters ih₂
    exact Or.inr ⟨_, hr, Below.refl _ _, by simp [ha.1],
      fun s hs => (List.mem_append.mp hs).elim (ha.2 s) (hb.2 s)⟩

private theorem repeat_derives {rules ts word r} (ht : r.1 ∈ ts)
    (hn : word ≠ []) (hw : ∀ s ∈ word, Below rules s r) : Derives rules ts word r := by
  induction word with
  | nil => exact (hn rfl).elim
  | cons s tail ih =>
    have hs := (Derives.letter (rules := rules) (transitive := ts) s).lift
      (hw s (List.mem_cons_self ..))
    by_cases he : tail = []
    · simpa [he] using hs
    · exact Derives.join ht hs (ih he (fun t ht => hw t (List.mem_cons_of_mem _ ht)))

private theorem derives_of_normal {rules ts word r} (h : Normal rules ts word r) :
    Derives rules ts word r := by
  rcases h with ⟨s, rfl, hs⟩ | ⟨s, ht, hs, hn, hw⟩
  · exact (Derives.letter s).lift hs
  · exact (repeat_derives ht hn hw).lift hs

private theorem accepts_normal (rules : RoleTheory) (ts : List String)
    (word : List OrientedRole) (r : OrientedRole) :
    (compile rules ts r).accepts word = true ↔ Normal rules ts word r := by
  cases word with
  | nil => simp [Automaton.accepts, Normal]
  | cons s tail =>
    simp only [compile, Automaton.accepts, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      List.all_eq_true, List.contains_iff_mem, List.mem_map, List.mem_filter, ALCH.mem_subroles,
      List.isEmpty_iff, Normal, Below]
    constructor
    · rintro (⟨rfl, hs⟩ | ⟨letters, ⟨t, ⟨ht, htt⟩, rfl⟩, hw⟩)
      · exact Or.inl ⟨s, rfl, hs⟩
      · exact Or.inr ⟨t, htt, ht, by simp, fun p hp => ALCH.mem_subroles.mp (hw p hp)⟩
    · rintro (⟨p, hp, hb⟩ | ⟨p, ht, hb, _, hw⟩)
      · simp only [List.cons.injEq] at hp
        exact Or.inl ⟨hp.2, hp.1 ▸ hb⟩
      · exact Or.inr ⟨_, ⟨p, ⟨hb, ht⟩, rfl⟩, fun t ht => ALCH.mem_subroles.mpr (hw t ht)⟩

/-- The finite automaton recognizes exactly the role words derivable under
    hierarchies, named inverses and transitivity. -/
theorem compile_correct (rules : RoleTheory) (ts : List String)
    (word : List OrientedRole) (r : OrientedRole) :
    (compile rules ts r).accepts word = true ↔ Derives rules ts word r :=
  (accepts_normal rules ts word r).trans ⟨derives_of_normal, normal_of_derives⟩

end Sabrina.RoleChains.TransitivePaths
