import Sabrina.OWL2.Datatypes.PatternAutomata
import Sabrina.OWL2.SROIQD.Termination.RegularWords

/-! Determinization of the partial-derivative automaton for datatype
patterns. All states fit in the powerset of the finite residual list. -/

namespace Sabrina.OWL2.SROIQD.Termination.StringPatternMachine

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.RegularWords

private def subsets : List α → List (List α)
  | [] => [[]]
  | a :: as => subsets as ++ (subsets as).map (a :: ·)

private theorem mem_subsets_iff {α : Type} {s u : List α} :
    s ∈ subsets u ↔ s.Sublist u := by
  induction u generalizing s with
  | nil => simp [subsets]
  | cons a as ih =>
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact .cons _ (ih.mp h)
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
        exact .cons_cons _ (ih.mp ht)
    · intro h
      cases h with
      | cons _ h => exact List.mem_append_left _ (ih.mpr h)
      | cons_cons _ h => exact List.mem_append_right _ (List.mem_map_of_mem (ih.mpr h))

private def residualPool (r : Regex) : List Regex := r :: r.residuals

private def advance (r : Regex) (s : List Regex) (c : Char) : List Regex :=
  let edges := s.flatMap (Regex.derivative c)
  (residualPool r).filter edges.contains

private theorem advance_mem {r : Regex} {s : List Regex} {c : Char} {q : Regex}
    (hs : s ⊆ residualPool r) :
    q ∈ advance r s c ↔ ∃ e ∈ s, q ∈ e.derivative c := by
  unfold advance
  simp only [List.mem_filter, List.contains_iff_mem, List.mem_flatMap]
  constructor
  · exact And.right
  · rintro ⟨e, he, hq⟩
    have h := hs he
    rw [residualPool, List.mem_cons] at h
    refine ⟨List.mem_cons_of_mem _ ?_, e, he, hq⟩
    rcases h with rfl | hr
    · exact Regex.derivative_subset _ c hq
    · exact Regex.residuals_closed hr c hq

def machine (r : Regex) (alphabet : List Char) : Machine (List Regex) Char where
  statePool := fun _ => subsets (residualPool r)
  alphabet
  transition := advance r
  final := fun s => s.any Regex.nullable
  closed := by
    intro s hs c hc
    exact mem_subsets_iff.mpr List.filter_sublist

theorem start_mem (r : Regex) (alphabet : List Char) : [r] ∈ (machine r alphabet).states :=
  mem_subsets_iff.mpr (List.Sublist.cons_cons _ (List.nil_sublist _))

private theorem accepts_state_iff (r : Regex) (alphabet : List Char) (s : List Regex)
    (hs : s ⊆ residualPool r) (w : List Char) :
    (machine r alphabet).accepts s w = true ↔ ∃ e ∈ s, e.Matches w := by
  induction w generalizing s with
  | nil =>
    simp only [Machine.accepts, machine, List.any_eq_true, Regex.nullable_iff]
  | cons c w ih =>
    have hsub : advance r s c ⊆ residualPool r := fun _ h => (List.mem_filter.mp h).1
    change (machine r alphabet).accepts (advance r s c) w = true ↔ _
    rw [ih _ hsub]
    constructor
    · rintro ⟨q, hq, hm⟩
      obtain ⟨e, he, hq⟩ := (advance_mem hs).mp hq
      exact ⟨e, he, (e.matches_derivative c w).mpr ⟨q, hq, hm⟩⟩
    · rintro ⟨e, he, hm⟩
      obtain ⟨q, hq, hm⟩ := (e.matches_derivative c w).mp hm
      exact ⟨q, (advance_mem hs).mpr ⟨e, he, hq⟩, hm⟩

theorem accepts_iff (r : Regex) (alphabet w : List Char) :
    (machine r alphabet).accepts [r] w = true ↔ r.Matches w := by
  have hs : [r] ⊆ residualPool r := List.Sublist.subset
    (List.Sublist.cons_cons _ (List.nil_sublist _))
  simpa using accepts_state_iff r alphabet [r] hs w

def sample (r : Regex) (alphabet : List Char) (K : Nat) : List (List Char) :=
  (machine r alphabet).sampleReachable K [r] (start_mem r alphabet)

theorem sample_sound (r : Regex) (alphabet : List Char) (K : Nat) :
    (sample r alphabet K).Nodup ∧ (sample r alphabet K).length ≤ K ∧
      ∀ w ∈ sample r alphabet K, r.Matches w ∧ ∀ c ∈ w, c ∈ alphabet := by
  have h := (machine r alphabet).sampleReachable_sound K (start_mem r alphabet)
  exact ⟨h.1, h.2.1, fun w hw =>
    let ⟨hm, ha⟩ := h.2.2 w hw
    ⟨(accepts_iff r alphabet w).mp hm, ha⟩⟩

theorem sample_complete_of_lt (r : Regex) (alphabet : List Char) (K : Nat)
    (hshort : (sample r alphabet K).length < K) {w : List Char} (hm : r.Matches w)
    (ha : ∀ c ∈ w, c ∈ alphabet) : w ∈ sample r alphabet K :=
  (machine r alphabet).sampleReachable_complete K (start_mem r alphabet) hshort
    ((accepts_iff r alphabet w).mpr hm) ha

#print axioms sample_sound
#print axioms sample_complete_of_lt

end Sabrina.OWL2.SROIQD.Termination.StringPatternMachine
