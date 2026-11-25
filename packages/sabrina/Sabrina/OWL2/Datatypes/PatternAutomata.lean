import Sabrina.OWL2.Datatypes.Extended

/-! Partial derivatives and finite residuals for the existing datatype pattern
syntax. The matcher and the partial derivative machine recognize the same
regular language. -/

namespace Sabrina.OWL2.Datatypes

abbrev Word := List Char

inductive Repeats (L : Word → Prop) : Word → Prop where
  | nil : Repeats L []
  | cons {u v} : L u → Repeats L v → Repeats L (u ++ v)

theorem Repeats.append {L : Word → Prop} {u v : Word} (hu : Repeats L u) (hv : Repeats L v) :
    Repeats L (u ++ v) := by
  induction hu with
  | nil => exact hv
  | cons h _ ih => simpa only [List.append_assoc] using Repeats.cons h ih

namespace Regex

def Matches : Regex → Word → Prop
  | .empty => fun _ => False
  | .eps => (· = [])
  | .any => fun w => ∃ c, w = [c] ∧ (c == '\n' || c == '\r') = false
  | .pred p => fun w => ∃ c, w = [c] ∧ p.accepts c = true
  | .alt a b => fun w => Matches a w ∨ Matches b w
  | .seq a b => fun w => ∃ u v, Matches a u ∧ Matches b v ∧ w = u ++ v
  | .star a => Repeats (Matches a)

theorem nullable_iff (e : Regex) : e.nullable = true ↔ e.Matches [] := by
  induction e with
  | empty | eps | any | pred => simp [nullable, Matches]
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
def derivative (r : Char) : Regex → List Regex
  | .empty | .eps => []
  | .any => if r == '\n' || r == '\r' then [] else [.eps]
  | .pred p => if p.accepts r then [.eps] else []
  | .alt a b => a.derivative r ++ b.derivative r
  | .seq a b =>
    (a.derivative r).map (fun p => .seq p b) ++ if a.nullable then b.derivative r else []
  | .star a => (a.derivative r).map (fun p => .seq p (.star a))

private theorem repeats_cons_iff {L : Word → Prop} {r : Char} {w : Word} :
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

private theorem any_cons (c : Char) (w : Word) :
    Regex.any.Matches (c :: w) ↔ w = [] ∧ (c == '\n' || c == '\r') = false := by
  constructor
  · rintro ⟨d, he, hd⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ⟨rfl, hd⟩
  · rintro ⟨rfl, hc⟩
    exact ⟨c, rfl, hc⟩

private theorem pred_cons (p : PatternClass) (c : Char) (w : Word) :
    (Regex.pred p).Matches (c :: w) ↔ w = [] ∧ p.accepts c = true := by
  constructor
  · rintro ⟨d, he, hd⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ⟨rfl, hd⟩
  · rintro ⟨rfl, hc⟩
    exact ⟨c, rfl, hc⟩

theorem matches_derivative (e : Regex) (r : Char) (w : Word) :
    e.Matches (r :: w) ↔ ∃ p ∈ e.derivative r, p.Matches w := by
  induction e generalizing w with
  | empty | eps => simp [derivative, Matches]
  | any => rw [any_cons]; cases h : (r == '\n' || r == '\r') <;> simp [derivative, Matches, h]
  | pred p => rw [pred_cons]; cases h : p.accepts r <;> simp [derivative, Matches, h]
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

def accepts (e : Regex) : Word → Bool
  | [] => e.nullable
  | r :: w => (e.derivative r).any fun p => p.accepts w

theorem accepts_iff (e : Regex) (w : Word) : e.accepts w = true ↔ e.Matches w := by
  induction w generalizing e with
  | nil => exact e.nullable_iff
  | cons r w ih =>
    rw [accepts, List.any_eq_true, matches_derivative]
    simp only [ih]

/-- All noninitial states that can be reached by taking derivatives. -/
def residuals : Regex → List Regex
  | .empty | .eps => []
  | .any | .pred _ => [.eps]
  | .alt a b => a.residuals ++ b.residuals
  | .seq a b => a.residuals.map (fun p => .seq p b) ++ b.residuals
  | .star a => a.residuals.map (fun p => .seq p (.star a))

theorem derivative_subset (e : Regex) (r : Char) :
    e.derivative r ⊆ e.residuals := by
  induction e with
  | empty | eps => simp [derivative, residuals]
  | any =>
    intro p hp
    cases h : (r == '\n' || r == '\r') <;> simp_all [derivative, residuals]
  | pred s =>
    intro p hp
    cases h : s.accepts r <;> simp_all [derivative, residuals]
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

theorem residuals_closed {e p : Regex} (h : p ∈ e.residuals) (r : Char) :
    p.derivative r ⊆ e.residuals := by
  induction e generalizing p with
  | empty | eps => simp [residuals] at h
  | any | pred _ =>
    have hp : p = .eps := by simpa [residuals] using h
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



private theorem matches_mkAlt (a b : Regex) (w : Word) :
    (mkAlt a b).Matches w ↔ a.Matches w ∨ b.Matches w := by
  cases a <;> cases b <;> simp [mkAlt, Matches]

private theorem matches_mkSeq (a b : Regex) (w : Word) :
    (mkSeq a b).Matches w ↔ (.seq a b : Regex).Matches w := by
  cases a <;> cases b <;> simp [mkSeq, Matches]

theorem matches_deriv_iff (e : Regex) (c : Char) (w : Word) :
    (e.deriv c).Matches w ↔ e.Matches (c :: w) := by
  induction e generalizing w with
  | empty | eps => simp [deriv, Matches]
  | any => rw [any_cons]; cases h : (c == '\n' || c == '\r') <;> simp [deriv, Matches, h]
  | pred p => rw [pred_cons]; cases h : p.accepts c <;> simp [deriv, Matches, h]
  | alt a b ha hb => simp only [deriv, matches_mkAlt, Matches, ha, hb]
  | seq a b ha hb =>
    by_cases hn : a.nullable = true
    · simp only [deriv, hn, ↓reduceIte, matches_mkAlt, matches_mkSeq, Matches, ha, hb]
      constructor
      · intro h
        rcases h with ⟨u, v, hu, hv, rfl⟩ | h
        · exact ⟨c :: u, v, hu, hv, rfl⟩
        · exact ⟨[], c :: w, a.nullable_iff.mp hn, h, rfl⟩
      · rintro ⟨u, v, hu, hv, he⟩
        cases u with
        | nil => exact Or.inr ((List.nil_append _ ▸ he).symm ▸ hv)
        | cons d u =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact Or.inl ⟨u, v, hu, hv, rfl⟩
    · simp only [deriv, hn, Bool.false_eq_true, ↓reduceIte, matches_mkSeq, Matches, ha]
      constructor
      · rintro ⟨u, v, hu, hv, rfl⟩
        exact ⟨c :: u, v, hu, hv, rfl⟩
      · rintro ⟨u, v, hu, hv, he⟩
        cases u with
        | nil => exact (hn (a.nullable_iff.mpr hu)).elim
        | cons d u =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact ⟨u, v, hu, hv, rfl⟩
  | star a ih =>
    rw [deriv, matches_mkSeq, Matches, Matches, repeats_cons_iff]
    simp only [ih]

theorem matches_fold (e : Regex) (w : Word) :
    (w.foldl (fun r c => r.deriv c) e).nullable = true ↔ e.Matches w := by
  induction w generalizing e with
  | nil => exact e.nullable_iff
  | cons c w ih => exact (ih (e.deriv c)).trans (matches_deriv_iff e c w)

end Regex

theorem matchesPattern_iff {pat : String} {r : Regex} (h : parseCompleteRegex pat = some r)
    (s : String) : matchesPattern pat s = true ↔ r.Matches s.toList := by
  rw [matchesPattern, h]
  exact Regex.matches_fold r s.toList

#print axioms matchesPattern_iff

end Sabrina.OWL2.Datatypes
