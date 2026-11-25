import Sabrina.OWL2.SROIQD.Termination.UnicodeStringSampling

/-! A tagged string has two separately testable coordinates. Boolean
combinations of text patterns and language ranges are finite unions of
products of regular languages. -/

namespace Sabrina.OWL2.SROIQD.Termination.TaggedStringSampling

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.StringLanguage

abbrev Rectangle := Constraint × Constraint
abbrev TaggedWord := List Char × List Char

def Rectangle.Holds (r : Rectangle) (w : TaggedWord) : Prop :=
  r.1.Holds w.1 ∧ r.2.Holds w.2

private def universal : Constraint := .not (.atom .empty)

private theorem universal_holds (w : List Char) : universal.Holds w :=
  fun h => h

private def intersect (a b : List Rectangle) : List Rectangle :=
  a.flatMap fun x => b.map fun y => (.and x.1 y.1, .and x.2 y.2)

private theorem intersect_iff (a b : List Rectangle) (w : TaggedWord) :
    (∃ r ∈ intersect a b, r.Holds w) ↔
      (∃ r ∈ a, r.Holds w) ∧ (∃ r ∈ b, r.Holds w) := by
  constructor
  · rintro ⟨r, hr, hh⟩
    obtain ⟨x, hx, hrest⟩ := List.mem_flatMap.mp hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrest
    exact ⟨⟨x, hx, hh.1.1, hh.2.1⟩, ⟨y, hy, hh.1.2, hh.2.2⟩⟩
  · rintro ⟨⟨x, hx, h₁, h₂⟩, ⟨y, hy, h₃, h₄⟩⟩
    exact ⟨_, List.mem_flatMap.mpr ⟨x, hx, List.mem_map_of_mem hy⟩, ⟨h₁, h₃⟩, ⟨h₂, h₄⟩⟩

private def complement : List Rectangle → List Rectangle
  | [] => [(universal, universal)]
  | r :: rest =>
    intersect [(.not r.1, universal), (universal, .not r.2)] (complement rest)

private theorem complement_iff (rs : List Rectangle) (w : TaggedWord) :
    (∃ r ∈ complement rs, r.Holds w) ↔ ¬ ∃ r ∈ rs, r.Holds w := by
  classical
  induction rs with
  | nil =>
    simp [complement, Rectangle.Holds, universal_holds]
  | cons r rs ih =>
    rw [complement, intersect_iff, ih]
    have hl :
        (∃ p ∈ [(.not r.1, universal), (universal, .not r.2)], Rectangle.Holds p w) ↔
          ¬ r.Holds w := by
      simp [Rectangle.Holds, Constraint.Holds, universal_holds]
      constructor
      · exact fun h ha => h.resolve_left (fun hn => hn ha)
      · intro h; by_cases ha : r.1.Holds w.1
        · exact .inr (h ha)
        · exact .inl ha
    rw [hl]
    simp only [List.mem_cons, exists_eq_or_imp, not_or]


inductive Formula where
  | text (f : Constraint)
  | tag (f : Constraint)
  | and (x y : Formula)
  | or (x y : Formula)
  | not (x : Formula)

def Formula.Holds : Formula → TaggedWord → Prop
  | .text f, w => f.Holds w.1
  | .tag f, w => f.Holds w.2
  | .and a b, w => a.Holds w ∧ b.Holds w
  | .or a b, w => a.Holds w ∨ b.Holds w
  | .not a, w => ¬ a.Holds w

def Formula.rectangles : Formula → List Rectangle
  | .text f => [(f, universal)]
  | .tag f => [(universal, f)]
  | .and a b => intersect a.rectangles b.rectangles
  | .or a b => a.rectangles ++ b.rectangles
  | .not a => complement a.rectangles

theorem Formula.rectangles_iff (f : Formula) (w : TaggedWord) :
    (∃ r ∈ f.rectangles, r.Holds w) ↔ f.Holds w := by
  induction f with
  | text f | tag f => simp [Formula.rectangles, Formula.Holds, Rectangle.Holds, universal_holds]
  | and a b ia ib => exact (intersect_iff ..).trans (and_congr ia ib)
  | or a b ia ib =>
    simp only [Formula.rectangles, Formula.Holds, List.mem_append]
    exact ⟨fun ⟨r, h, hr⟩ => h.elim (fun h => .inl (ia.mp ⟨r, h, hr⟩))
      (fun h => .inr (ib.mp ⟨r, h, hr⟩)), fun h => by
      rcases h with h | h
      · obtain ⟨r, hr, hh⟩ := ia.mpr h
        exact ⟨r, .inl hr, hh⟩
      · obtain ⟨r, hr, hh⟩ := ib.mpr h
        exact ⟨r, .inr hr, hh⟩⟩
  | not a ih => exact (complement_iff ..).trans (not_congr ih)

private def Rectangle.samples (r : Rectangle) (K : Nat) : List TaggedWord :=
  let tags := UnicodeStringSampling.sample r.2 K
  (UnicodeStringSampling.sample r.1 K).flatMap fun x =>
    tags.map (x, ·)

def Formula.sample (f : Formula) (K : Nat) : List TaggedWord :=
  ((f.rectangles.flatMap fun r => r.samples K).eraseDups).take K

theorem Formula.sample_exact (f : Formula) (K : Nat) :
    (f.sample K).Nodup ∧ (f.sample K).length ≤ K ∧
      (∀ w ∈ f.sample K, f.Holds w) ∧
      ((f.sample K).length < K → ∀ w, f.Holds w → w ∈ f.sample K) := by
  refine ⟨(List.take_sublist ..).nodup (nodup_eraseDups_list _), List.length_take_le .., ?_, ?_⟩
  · intro w hw
    obtain ⟨r, hr, hw⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp (List.mem_of_mem_take hw))
    obtain ⟨u, hu, rest⟩ := List.mem_flatMap.mp hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp rest
    exact (f.rectangles_iff _).mp ⟨r, hr,
      (UnicodeStringSampling.sample_exact r.1 K).2.2.1 _ hu,
      (UnicodeStringSampling.sample_exact r.2 K).2.2.1 _ hv⟩
  · intro hs w hw
    obtain ⟨r, hr, hh⟩ := (f.rectangles_iff w).mpr hw
    let all := (f.rectangles.flatMap fun r => r.samples K).eraseDups
    have hlo : all.length < K := by
      change (all.take K).length < K at hs
      rw [List.length_take] at hs
      omega
    have htake : f.sample K = all := List.take_of_length_le (Nat.le_of_lt hlo)
    have hpair (u) (hu : u ∈ UnicodeStringSampling.sample r.1 K)
        (v) (hv : v ∈ UnicodeStringSampling.sample r.2 K) : (u, v) ∈ all :=
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr
        ⟨r, hr, List.mem_flatMap.mpr ⟨u, hu, List.mem_map_of_mem hv⟩⟩)
    obtain ⟨nd₁, cap₁, _, complete₁⟩ := UnicodeStringSampling.sample_exact r.1 K
    obtain ⟨nd₂, cap₂, _, complete₂⟩ := UnicodeStringSampling.sample_exact r.2 K
    have ne₁ : UnicodeStringSampling.sample r.1 K ≠ [] := by
      intro he
      have h : (UnicodeStringSampling.sample r.1 K).length < K := by simpa [he] using Nat.zero_lt_of_lt hlo
      have hmem := complete₁ h w.1 hh.1
      rw [he] at hmem; cases hmem
    have ne₂ : UnicodeStringSampling.sample r.2 K ≠ [] := by
      intro he
      have h : (UnicodeStringSampling.sample r.2 K).length < K := by simpa [he] using Nat.zero_lt_of_lt hlo
      have hmem := complete₂ h w.2 hh.2
      rw [he] at hmem; cases hmem
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ ne₁
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ ne₂
    have h₁ : (UnicodeStringSampling.sample r.1 K).length ≤ all.length := by
      let row := (UnicodeStringSampling.sample r.1 K).map (·, v)
      have hn : row.Nodup := nd₁.map (·, v) (fun _ _ hn he => hn (congrArg Prod.fst he))
      have hle := hn.length_le_of_subset (fun z hz => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        exact hpair u hu v hv)
      simpa [row] using hle
    have h₂ : (UnicodeStringSampling.sample r.2 K).length ≤ all.length := by
      let row := (UnicodeStringSampling.sample r.2 K).map (u, ·)
      have hn : row.Nodup := nd₂.map (u, ·) (fun _ _ hn he => hn (congrArg Prod.snd he))
      have hle := hn.length_le_of_subset (fun z hz => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
        exact hpair u hu v hv)
      simpa [row] using hle
    rw [htake]
    exact hpair w.1 (complete₁ (Nat.lt_of_le_of_lt h₁ hlo) w.1 hh.1)
      w.2 (complete₂ (Nat.lt_of_le_of_lt h₂ hlo) w.2 hh.2)

#print axioms Formula.sample_exact

end Sabrina.OWL2.SROIQD.Termination.TaggedStringSampling
