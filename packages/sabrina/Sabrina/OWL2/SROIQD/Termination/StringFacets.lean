import Sabrina.OWL2.SROIQD.Termination.TaggedStringSampling

/-! Exact sampling for Boolean constraints on a text and a language tag.
Pattern syntax is interpreted by the existing datatype parser. -/

namespace Sabrina.OWL2.SROIQD.Termination.StringFacets

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.StringLanguage
open Sabrina.OWL2.SROIQD.Termination.TaggedStringSampling

private def anyChar : Regex := .pred (.neg .empty)

private def lengthPattern : Nat → Regex
  | 0 => .eps
  | n + 1 => .seq anyChar (lengthPattern n)

private theorem lengthPattern_iff (n : Nat) (w : List Char) :
    (lengthPattern n).Matches w ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [lengthPattern, Regex.Matches]
  | succ n ih =>
    constructor
    · rintro ⟨u, v, ⟨c, rfl, _⟩, hv, rfl⟩
      simp [(ih _).mp hv]
    · cases w with
      | nil => simp
      | cons c w =>
        intro h
        refine ⟨[c], w, ⟨c, rfl, rfl⟩, (ih _).mpr ?_, rfl⟩
        simpa using h

private theorem anyStar (w : List Char) : (Regex.star anyChar).Matches w := by
  induction w with
  | nil => exact .nil
  | cons c w ih => exact Repeats.cons (u := [c]) ⟨c, rfl, rfl⟩ ih

private def atLeastPattern (n : Nat) : Regex := .seq (lengthPattern n) (.star anyChar)

private theorem atLeastPattern_iff (n : Nat) (w : List Char) :
    (atLeastPattern n).Matches w ↔ n ≤ w.length := by
  constructor
  · rintro ⟨u, v, hu, _, rfl⟩
    simp [(lengthPattern_iff _ _).mp hu]
  · intro h
    refine ⟨w.take n, w.drop n, (lengthPattern_iff _ _).mpr ?_, anyStar _, (List.take_append_drop ..).symm⟩
    simp [List.length_take, h]

/-- Standalone string facet constraints, with the text and language tag
represented as separate strings of Unicode characters. -/
inductive Query where
  | length (n : Nat)
  | minLength (n : Nat)
  | maxLength (n : Nat)
  | pattern (source : String)
  | langRange (range : String)
  | and (a b : Query)
  | or (a b : Query)
  | not (a : Query)

def Query.Holds : Query → TaggedWord → Prop
  | .length n, w => w.1.length = n
  | .minLength n, w => n ≤ w.1.length
  | .maxLength n, w => w.1.length ≤ n
  | .pattern p, w => matchesPattern p (String.ofList w.1) = true
  | .langRange p, w => matchesLangRange p (String.ofList w.2) = true
  | .and a b, w => a.Holds w ∧ b.Holds w
  | .or a b, w => a.Holds w ∨ b.Holds w
  | .not a, w => ¬ a.Holds w

def Query.compile : (q : Query) →
    Option { f : Formula // ∀ w, f.Holds w ↔ q.Holds w }
  | .length n => some ⟨.text (.atom (lengthPattern n)), fun w => lengthPattern_iff n w.1⟩
  | .minLength n => some ⟨.text (.atom (atLeastPattern n)), fun w => atLeastPattern_iff n w.1⟩
  | .maxLength n =>
    some ⟨.not (.text (.atom (atLeastPattern (n + 1)))), fun w =>
      (not_congr (atLeastPattern_iff (n + 1) w.1)).trans (by simp [Query.Holds, Nat.not_le, Nat.lt_succ_iff])⟩
  | .pattern p =>
    match h : parseCompleteRegex p with
    | none => none
    | some r => some ⟨.text (.atom r), fun w => by
        simpa [Formula.Holds, Constraint.Holds, Query.Holds] using (matchesPattern_iff h (String.ofList w.1)).symm⟩
  | .langRange p => some ⟨.tag (.atom (langRangeRegex p)), fun w => by
      simpa [Formula.Holds, Constraint.Holds, Query.Holds] using langRangeRegex_iff p (String.ofList w.2)⟩
  | .and a b => do
    let x ← a.compile
    let y ← b.compile
    return ⟨.and x.val y.val, fun w => and_congr (x.property w) (y.property w)⟩
  | .or a b => do
    let x ← a.compile
    let y ← b.compile
    return ⟨.or x.val y.val, fun w => or_congr (x.property w) (y.property w)⟩
  | .not a => a.compile.map fun x => ⟨.not x.val, fun w => not_congr (x.property w)⟩

def Query.sample? (q : Query) (K : Nat) : Option (List TaggedWord) :=
  q.compile.map fun f => f.val.sample K

/-- Small results enumerate the whole language. A full result exhibits
the requested number of distinct witnesses. -/
theorem Query.sample_exact {q : Query} {K : Nat} {xs : List TaggedWord}
    (h : q.sample? K = some xs) :
    xs.Nodup ∧ xs.length ≤ K ∧ (∀ w ∈ xs, q.Holds w) ∧
      (xs.length < K → ∀ w, q.Holds w → w ∈ xs) := by
  obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hnd, hcap, hsound, hfull⟩ := f.val.sample_exact K
  exact ⟨hnd, hcap, fun w hw => (f.property w).mp (hsound w hw),
    fun hs w hw => hfull hs w ((f.property w).mpr hw)⟩

#print axioms Query.sample_exact


open Sabrina.OWL2 (Facet IRI)

private def Query.ofLength : LengthFacet → Nat → Query
  | .length => .length
  | .minLength => .minLength
  | .maxLength => .maxLength

private theorem Query.ofLength_holds (lf : LengthFacet) (n : Nat) (text tag : String) :
    (Query.ofLength lf n).Holds (text.toList, tag.toList) ↔ lf.holds n text := by
  cases lf <;> rfl

private def checkLiteralFacet (t : IRI) (f : Facet) (text tag : String) : Bool :=
  (decodeLiteral f.bound).any fun bound => checkFacet t f.name bound (.plainLiteral text tag)

/-- A string facet stripped of its datatype membership test. This compiler
retains the exact test on every value belonging to the base datatype. -/
def compileLiteralFacet (f : Facet) :
    Option { q : Query // ∀ (t : IRI) (text tag : String),
      checkValue t (.plainLiteral text tag) = true →
      (q.Holds (text.toList, tag.toList) ↔ checkLiteralFacet t f text tag = true) } :=
  match hb : decodeLiteral f.bound with
  | some (.number n) =>
    match hlf : lengthFacet f.name with
    | some lf =>
      if hn : n.den = 1 ∧ 0 ≤ n.num then
        some ⟨Query.ofLength lf n.num.toNat, fun t text tag ht => by
          rw [Query.ofLength_holds]
          simp [checkLiteralFacet, hb, checkFacet, hlf, hn.1, Rat.num_nonneg.mp hn.2, ht]⟩
      else none
    | none => none
  | some (.plainLiteral pattern "") =>
    if h : f.name = xsd "pattern" then
      some ⟨.pattern pattern, fun t text tag ht => by
        simp [Query.Holds, checkLiteralFacet, hb, checkFacet, h, ht,
          show xsd "pattern" ≠ rdf "langRange" by decide]⟩
    else if h' : f.name = rdf "langRange" then
      some ⟨.langRange pattern, fun t text tag ht => by
        simp [Query.Holds, checkLiteralFacet, hb, checkFacet, h', ht,
          show rdf "langRange" ≠ xsd "pattern" by decide]⟩
    else none
  | _ => none

theorem compileLiteralFacet_iff {f : Facet} {out}
    (_h : compileLiteralFacet f = some out) (t : IRI) (text tag : String)
    (ht : checkValue t (.plainLiteral text tag) = true) :
    out.val.Holds (text.toList, tag.toList) ↔ checkLiteralFacet t f text tag = true :=
  out.property t text tag ht

#print axioms compileLiteralFacet_iff

end Sabrina.OWL2.SROIQD.Termination.StringFacets
