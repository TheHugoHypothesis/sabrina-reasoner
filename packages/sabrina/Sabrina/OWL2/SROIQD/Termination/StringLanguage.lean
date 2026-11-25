import Sabrina.OWL2.SROIQD.Termination.StringPatternMachine
import Sabrina.OWL2.Datatypes.LanguageRangePattern

/-! Regular string constraints compose by product and complement. This
module supplies the exact Boolean-language decision step over a supplied
alphabet of concrete characters. -/

namespace Sabrina.OWL2.SROIQD.Termination.StringLanguage

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.RegularWords
open Sabrina.OWL2.SROIQD.Termination.StringPatternMachine

structure Automaton where
  State : Type
  stateDecidable : DecidableEq State
  graph : Machine State Char
  start : State
  start_mem : start ∈ graph.states

attribute [instance] Automaton.stateDecidable

def Automaton.accepts (a : Automaton) (w : List Char) : Bool :=
  a.graph.accepts a.start w

def Automaton.sample (a : Automaton) (K : Nat) : List (List Char) :=
  a.graph.sampleReachable K a.start a.start_mem

theorem Automaton.sample_sound (a : Automaton) (K : Nat) :
    (a.sample K).Nodup ∧ (a.sample K).length ≤ K ∧
      ∀ w ∈ a.sample K, a.accepts w = true ∧ ∀ c ∈ w, c ∈ a.graph.alphabet :=
  a.graph.sampleReachable_sound K a.start_mem

theorem Automaton.sample_complete_of_lt (a : Automaton) (K : Nat)
    (hshort : (a.sample K).length < K) {w : List Char}
    (hw : a.accepts w = true) (hchar : ∀ c ∈ w, c ∈ a.graph.alphabet) :
    w ∈ a.sample K :=
  a.graph.sampleReachable_complete K a.start_mem hshort hw hchar

def pattern (r : Regex) (alphabet : List Char) : Automaton where
  State := List Regex
  stateDecidable := inferInstance
  graph := StringPatternMachine.machine r alphabet
  start := [r]
  start_mem := StringPatternMachine.start_mem r alphabet

theorem pattern_iff (r : Regex) (alphabet w : List Char) :
    (pattern r alphabet).accepts w = true ↔ r.Matches w :=
  StringPatternMachine.accepts_iff r alphabet w

def negate (a : Automaton) : Automaton where
  State := a.State
  stateDecidable := a.stateDecidable
  graph := { a.graph with final := fun s => !a.graph.final s }
  start := a.start
  start_mem := a.start_mem

private theorem negate_at (a : Automaton) (s : a.State) (w : List Char) :
    (negate a).graph.accepts s w = !a.graph.accepts s w := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih => exact ih (a.graph.transition s c)

theorem negate_accepts (a : Automaton) (w : List Char) :
    (negate a).accepts w = !a.accepts w :=
  negate_at a a.start w

def combine (op : Bool → Bool → Bool) (a b : Automaton)
    (h : a.graph.alphabet = b.graph.alphabet) : Automaton where
  State := a.State × b.State
  stateDecidable := inferInstance
  graph := {
    statePool := fun _ => a.graph.states.flatMap fun x => b.graph.states.map (x, ·)
    alphabet := a.graph.alphabet
    transition := fun (x, y) c => (a.graph.transition x c, b.graph.transition y c)
    final := fun (x, y) => op (a.graph.final x) (b.graph.final y)
    closed := by
      rintro ⟨x, y⟩ hs c hc
      obtain ⟨sx, hx, xy⟩ := List.mem_flatMap.mp hs
      obtain ⟨sy, hy, he⟩ := List.mem_map.mp xy
      cases he
      exact List.mem_flatMap.mpr ⟨_, a.graph.closed _ hx c hc,
        List.mem_map_of_mem (b.graph.closed _ hy c (h ▸ hc))⟩ }
  start := (a.start, b.start)
  start_mem := List.mem_flatMap.mpr ⟨_, a.start_mem, List.mem_map_of_mem b.start_mem⟩

private theorem combine_at (op : Bool → Bool → Bool) (a b : Automaton)
    (h : a.graph.alphabet = b.graph.alphabet) (x : a.State) (y : b.State) (w : List Char) :
    (combine op a b h).graph.accepts (x, y) w = op (a.graph.accepts x w) (b.graph.accepts y w) := by
  induction w generalizing x y with
  | nil => rfl
  | cons c w ih => exact ih (a.graph.transition x c) (b.graph.transition y c)

theorem combine_accepts (op : Bool → Bool → Bool) (a b : Automaton)
    (h : a.graph.alphabet = b.graph.alphabet) (w : List Char) :
    (combine op a b h).accepts w = op (a.accepts w) (b.accepts w) :=
  combine_at op a b h a.start b.start w

inductive Constraint where
  | atom (r : Regex)
  | and (a b : Constraint)
  | or (a b : Constraint)
  | not (a : Constraint)

def Constraint.Holds : Constraint → List Char → Prop
  | .atom r, w => r.Matches w
  | .and a b, w => a.Holds w ∧ b.Holds w
  | .or a b, w => a.Holds w ∨ b.Holds w
  | .not a, w => ¬ a.Holds w

def Constraint.compile (alphabet : List Char) : (f : Constraint) →
    { a : Automaton // a.graph.alphabet = alphabet }
  | .atom r => ⟨pattern r alphabet, rfl⟩
  | .and a b =>
    let x := a.compile alphabet
    let y := b.compile alphabet
    ⟨combine (· && ·) x.val y.val (x.property.trans y.property.symm), x.property⟩
  | .or a b =>
    let x := a.compile alphabet
    let y := b.compile alphabet
    ⟨combine (· || ·) x.val y.val (x.property.trans y.property.symm), x.property⟩
  | .not a =>
    let x := a.compile alphabet
    ⟨negate x.val, x.property⟩

theorem Constraint.compile_iff (f : Constraint) (alphabet w : List Char) :
    (f.compile alphabet).val.accepts w = true ↔ f.Holds w := by
  induction f with
  | atom r => exact pattern_iff r alphabet w
  | and a b ia ib =>
    simp only [Constraint.compile, Constraint.Holds, combine_accepts, Bool.and_eq_true]
    exact and_congr ia ib
  | or a b ia ib =>
    simp only [Constraint.compile, Constraint.Holds, combine_accepts, Bool.or_eq_true]
    exact or_congr ia ib
  | not a ih =>
    simp only [Constraint.compile, Constraint.Holds, negate_accepts, Bool.not_eq_true', Bool.eq_false_iff]
    exact not_congr ih

def Constraint.sample (f : Constraint) (alphabet : List Char) (K : Nat) : List (List Char) :=
  (f.compile alphabet).val.sample K

theorem Constraint.sample_exact (f : Constraint) (alphabet : List Char) (K : Nat) :
    (f.sample alphabet K).Nodup ∧ (f.sample alphabet K).length ≤ K ∧
    (∀ w ∈ f.sample alphabet K, f.Holds w ∧ ∀ c ∈ w, c ∈ alphabet) ∧
    ((f.sample alphabet K).length < K → ∀ w,
      f.Holds w → (∀ c ∈ w, c ∈ alphabet) → w ∈ f.sample alphabet K) := by
  let a := f.compile alphabet
  obtain ⟨hnd, hcap, hsound⟩ := a.val.sample_sound K
  refine ⟨hnd, hcap, fun w hw => ?_, fun hshort w hw ha => ?_⟩
  · obtain ⟨hv, hall⟩ := hsound w hw
    exact ⟨(f.compile_iff alphabet w).mp hv, fun c hc => a.property ▸ hall c hc⟩
  · exact a.val.sample_complete_of_lt K hshort ((f.compile_iff alphabet w).mpr hw)
      fun c hc => a.property.symm ▸ ha c hc

#print axioms Constraint.sample_exact

end Sabrina.OWL2.SROIQD.Termination.StringLanguage
