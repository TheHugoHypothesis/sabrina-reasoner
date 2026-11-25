import Sabrina.OWL2.Datatypes.PatternAutomata

/-! The implemented RFC 4647 basic matcher is a regular language. This
translation lets the string sampler use the same representation for
language-range and text-pattern constraints. -/

namespace Sabrina.OWL2.Datatypes

private def anyCharacter : Regex := .pred (.neg .empty)

private def caseInsensitive (word : List Char) : Regex :=
  word.foldr (fun c r => .seq (.pred (.lowerASCII (.interval c c))) r) .eps

private theorem caseInsensitive_iff (cs w : List Char) :
    (caseInsensitive cs).Matches w ↔ w.map toLowerAscii = cs := by
  induction cs generalizing w with
  | nil => simp [caseInsensitive, Regex.Matches]
  | cons c cs ih =>
    change (Regex.seq (.pred (.lowerASCII (.interval c c))) (caseInsensitive cs)).Matches w ↔ _
    constructor
    · rintro ⟨u, v, ⟨a, rfl, ha⟩, hv, rfl⟩
      have ha : toLowerAscii a = c := by
        have h := Bool.and_eq_true_iff.mp ha
        exact Char.le_antisymm (of_decide_eq_true h.2) (of_decide_eq_true h.1)
      simp [ha, (ih _).mp hv]
    · cases w with
      | nil => simp
      | cons a w =>
        intro h
        obtain ⟨ha, hw⟩ := List.cons.inj h
        have hc : (.lowerASCII (.interval c c) : PatternClass).accepts a = true := by
          simp [PatternClass.accepts, ha]
        exact ⟨[a], w, ⟨a, rfl, hc⟩, (ih _).mpr hw, rfl⟩

private theorem anyStar_holds (w : List Char) : (Regex.star anyCharacter).Matches w := by
  induction w with
  | nil => exact .nil
  | cons c w ih => exact Repeats.cons (u := [c]) ⟨c, rfl, rfl⟩ ih

private theorem listStartsWith_iff {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α) :
    listStartsWith xs ys = true ↔ ∃ zs, ys = xs ++ zs := by
  induction xs generalizing ys with
  | nil => simp [listStartsWith]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listStartsWith]
    | cons y ys =>
      simp only [listStartsWith, Bool.and_eq_true, beq_iff_eq, ih, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, zs, h⟩; exact ⟨zs, rfl, h⟩
      · rintro ⟨zs, rfl, h⟩; exact ⟨rfl, zs, h⟩

private theorem prefixPattern_iff (cs w : List Char) :
    (Regex.seq (caseInsensitive cs) (.star anyCharacter)).Matches w ↔
      listStartsWith cs (w.map toLowerAscii) = true := by
  rw [listStartsWith_iff]
  constructor
  · rintro ⟨u, v, hu, _, rfl⟩
    exact ⟨v.map toLowerAscii, by rw [List.map_append, (caseInsensitive_iff _ _).mp hu]⟩
  · rintro ⟨zs, hz⟩
    have hl : cs.length ≤ w.length := by
      have he := congrArg List.length hz
      simp only [List.length_map, List.length_append] at he
      omega
    refine ⟨w.take cs.length, w.drop cs.length, (caseInsensitive_iff _ _).mpr ?_,
      anyStar_holds _, (List.take_append_drop ..).symm⟩
    rw [List.map_take, hz, List.take_left]

/-- Compile a basic language range using the same case folding and subtag
boundary as the datatype matcher. -/
def langRangeRegex (pat : String) : Regex :=
  let cs := pat.toList.map toLowerAscii
  if cs == ['*'] then .seq anyCharacter (.star anyCharacter)
  else if cs.isEmpty then .empty
  else .alt (caseInsensitive cs) (.seq (caseInsensitive (cs ++ ['-'])) (.star anyCharacter))

theorem langRangeRegex_iff (pat lang : String) :
    (langRangeRegex pat).Matches lang.toList ↔ matchesLangRange pat lang = true := by
  let cs := pat.toList.map toLowerAscii
  let w := lang.toList
  change (if cs == ['*'] then Regex.seq anyCharacter (.star anyCharacter)
    else if cs.isEmpty then .empty
    else .alt (caseInsensitive cs) (.seq (caseInsensitive (cs ++ ['-'])) (.star anyCharacter))).Matches w ↔
    (if cs == ['*'] then !(w.map toLowerAscii).isEmpty
      else if cs.isEmpty then false
      else (w.map toLowerAscii == cs) || listStartsWith (cs ++ ['-']) (w.map toLowerAscii)) = true
  by_cases he : cs == ['*']
  · rw [ite_eq_left he, ite_eq_left he]
    cases w with
    | nil =>
      constructor
      · rintro ⟨u, v, ⟨a, rfl, _⟩, _, he⟩
        cases he
      · intro h
        cases h
    | cons c tail =>
      exact ⟨fun _ => rfl, fun _ =>
        ⟨[c], tail, ⟨c, rfl, rfl⟩, anyStar_holds tail, rfl⟩⟩
  · simp only [ite_eq_right he]
    cases hn : cs.isEmpty with
    | true => simp [Regex.Matches]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      change ((caseInsensitive cs).Matches w ∨
        (Regex.seq (caseInsensitive (cs ++ ['-'])) (.star anyCharacter)).Matches w) ↔ _
      rw [caseInsensitive_iff, prefixPattern_iff, Bool.or_eq_true, beq_iff_eq]

#print axioms langRangeRegex_iff

end Sabrina.OWL2.Datatypes
