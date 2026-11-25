import Sabrina.ALC.Query

namespace SabrinaTests.ALC
open Sabrina.ALC

private def a : Concept := .atom "A"
private def b : Concept := .atom "B"
private def cycle : TBox := [⟨a, .some "r" a⟩]
private def clash : TBox := cycle ++ [⟨a, .all "r" (.neg a)⟩]

/-- Cyclic obligations admit a finite witness through a self-loop. -/
example : checkModel cycle a [[a, .some "r" a]] = true := by decide

example : (match search cycle a with
  | .model pool => checkModel cycle a pool
  | .refutation _ => false) = true := by decide

/-- An existential and a universal can prevent a locally coherent root from
surviving. The TBox itself stays consistent with `A` empty. -/
example : checkRefutation clash a 0 = false := by decide

example : (match search clash a with
  | .refutation rounds => checkRefutation clash a rounds
  | .model _ => false) = true := by decide

example : (match search clash .top with
  | .model pool => checkModel clash .top pool
  | .refutation _ => false) = true := by decide

/-- Coherent rows with no successor supporting an existential are rejected. -/
example : checkModel cycle a [[a]] = false := by decide

private def nested : Concept := .some "r" (.conj b (.some "s" (.atom "C")))

example : (match search [⟨a, nested⟩] (.conj a nested) with
  | .model pool => checkModel [⟨a, nested⟩] (.conj a nested) pool
  | .refutation _ => false) = true := by decide

example : (match searchSentenceIndependence cycle a b with
  | some (counter, positive) => checkSentenceIndependence cycle a b counter positive
  | none => false) = true := by decide

example : (searchSentenceIndependence (⟨a, b⟩ :: cycle) a b).isNone = true := by decide

/-- Every model has an `A`, while no `A` may be a `B`. -/
private def forcesCounterexample : TBox := [⟨.top, .some "r" a⟩, ⟨a, .neg b⟩]

example : (searchSentenceIndependence forcesCounterexample a b).isNone = true := by decide

example : (searchInclusion forcesCounterexample ⟨a, b⟩).verdict = .refuted := by decide

example : (searchInclusion [⟨.top, .bottom⟩] ⟨a, b⟩).verdict = .inconsistent := by decide

/-- A certificate for a different query cannot force the refutation verdict. -/
example : checkInclusion forcesCounterexample ⟨a, a⟩
    (searchInclusion forcesCounterexample ⟨a, b⟩) = false := by decide

end SabrinaTests.ALC
