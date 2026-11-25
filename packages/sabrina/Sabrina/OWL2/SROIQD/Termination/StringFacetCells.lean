import Sabrina.OWL2.SROIQD.Termination.WiderDataCore
import Sabrina.OWL2.SROIQD.Termination.StringFacets

/-! Exact Venn-cell sampling for string datatypes (`rdf:PlainLiteral`,
`xsd:string`, `xsd:normalizedString`, `xsd:token`, `xsd:language`,
`xsd:NMTOKEN`, `xsd:Name`, `xsd:NCName`) and `xsd:anyURI` with arbitrary
Boolean combinations of length facets, `xsd:pattern`, `rdf:langRange`, and
`DataOneOf` enumerations. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2 Sabrina.OWL2.Datatypes Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination
open Sabrina.OWL2.SROIQD.Termination.StringLanguage
open Sabrina.OWL2.SROIQD.Termination.TaggedStringSampling
open Sabrina.OWL2.SROIQD.Termination.StringFacets

/-! ### 1. Lexical datatype & facet admission predicates -/

def isStringDatatype (t : IRI) : Bool :=
  t == rdf "PlainLiteral" || t == xsd "string" || t == xsd "normalizedString" ||
  t == xsd "token" || t == xsd "language" || t == xsd "NMTOKEN" ||
  t == xsd "Name" || t == xsd "NCName"

def isLexicalDatatype (t : IRI) : Bool :=
  isStringDatatype t || t == xsd "anyURI"

def isStringFacetSupported (t : IRI) (f : Facet) : Bool :=
  match decodeLiteral f.bound with
  | none => false
  | some bound =>
    checkApplicableFacet t f.name bound &&
    if f.name == xsd "pattern" then
      match bound with
      | .plainLiteral pat "" => (parseCompleteRegex pat).isSome
      | _ => false
    else true

def isStringFacetExactAtom : DataRange → Bool
  | .datatype t => isLexicalDatatype t
  | .restriction t fs => isLexicalDatatype t && fs.all (isStringFacetSupported t)
  | _ => false

theorem lexicalDatatype_supported {t : IRI} (h : isLexicalDatatype t = true) :
    supportedDatatype t = true := by
  simp only [isLexicalDatatype, isStringDatatype, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;> decide

theorem stringFacetRestriction_supported {t : IRI} {fs : List Facet}
    (h : isStringFacetExactAtom (.restriction t fs) = true) :
    supportedDatatype t = true ∧ ∀ f ∈ fs, (decodeLiteral f.bound).isSome = true := by
  obtain ⟨ht, hfs⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨lexicalDatatype_supported ht, fun f hf => ?_⟩
  have hsf := List.all_eq_true.mp hfs f hf
  unfold isStringFacetSupported at hsf
  cases hdec : decodeLiteral f.bound <;> simp [hdec] at hsf ⊢

/-! ### 2. Exact regular constraints for all 8 string datatypes & exact words -/

private def anyCharRegex : Regex := .pred (.neg .empty)

private theorem anyCharStar_matches (w : List Char) : (Regex.star anyCharRegex).Matches w := by
  induction w with
  | nil => exact .nil
  | cons c rest ih => exact Repeats.cons (u := [c]) ⟨c, rfl, rfl⟩ ih

private theorem pred_interval_singleton (c d : Char) :
    (PatternClass.interval c c).accepts d = true ↔ d = c := by
  simp only [PatternClass.accepts, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩

private theorem star_pred_iff (p : PatternClass) (w : List Char) :
    (Regex.star (.pred p)).Matches w ↔ ∀ c ∈ w, p.accepts c = true := by
  constructor
  · intro h
    change Repeats (Regex.pred p).Matches w at h
    induction h with
    | nil => simp
    | cons hu _ ih =>
      obtain ⟨c, rfl, hc⟩ := hu
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hc
      · exact ih x hx'
  · intro h
    induction w with
    | nil => exact .nil
    | cons c rest ih =>
      exact Repeats.cons (u := [c]) ⟨c, rfl, h c (List.mem_cons_self ..)⟩
        (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem plus_pred_iff (p : PatternClass) (w : List Char) :
    (Regex.seq (.pred p) (.star (.pred p))).Matches w ↔
      w ≠ [] ∧ ∀ c ∈ w, p.accepts c = true := by
  constructor
  · rintro ⟨u, v, ⟨c, rfl, hc⟩, hv, rfl⟩
    refine ⟨List.cons_ne_nil _ _, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hc
    · exact (star_pred_iff p v).mp hv x hx'
  · rintro ⟨hne, hall⟩
    cases w with
    | nil => exact (hne rfl).elim
    | cons c rest =>
      exact ⟨[c], rest, ⟨c, rfl, hall c (List.mem_cons_self ..)⟩,
        (star_pred_iff p rest).mpr fun x hx => hall x (List.mem_cons_of_mem _ hx), rfl⟩

private def exactWordRegex : List Char → Regex
  | [] => .eps
  | c :: rest => .seq (.pred (.interval c c)) (exactWordRegex rest)

private theorem exactWordRegex_iff (cs w : List Char) :
    (exactWordRegex cs).Matches w ↔ w = cs := by
  induction cs generalizing w with
  | nil => simp [exactWordRegex, Regex.Matches]
  | cons c rest ih =>
    constructor
    · rintro ⟨u, v, ⟨d, rfl, hd⟩, hv, rfl⟩
      have hdc : d = c := (pred_interval_singleton c d).mp hd
      have hvr : v = rest := (ih v).mp hv
      subst hdc; subst hvr; rfl
    · rintro rfl
      exact ⟨[c], rest, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩, (ih rest).mpr rfl, rfl⟩

private def startsWithCharRegex (c : Char) : Regex :=
  .seq (.pred (.interval c c)) (.star anyCharRegex)

private theorem startsWithCharRegex_iff (c : Char) (w : List Char) :
    (startsWithCharRegex c).Matches w ↔ ∃ t, w = c :: t := by
  constructor
  · rintro ⟨u, v, ⟨d, rfl, hd⟩, _, rfl⟩
    exact ⟨v, by rw [(pred_interval_singleton c d).mp hd]; rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨[c], t, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩, anyCharStar_matches t, rfl⟩

private def endsWithCharRegex (c : Char) : Regex :=
  .seq (.star anyCharRegex) (.pred (.interval c c))

private theorem endsWithCharRegex_iff (c : Char) (w : List Char) :
    (endsWithCharRegex c).Matches w ↔ ∃ u, w = u ++ [c] := by
  constructor
  · rintro ⟨u, v, _, ⟨d, rfl, hd⟩, rfl⟩
    exact ⟨u, by rw [(pred_interval_singleton c d).mp hd]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, [c], anyCharStar_matches u, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩, rfl⟩

private def containsCharRegex (c : Char) : Regex :=
  .seq (.star anyCharRegex) (.seq (.pred (.interval c c)) (.star anyCharRegex))

private theorem containsCharRegex_iff (c : Char) (w : List Char) :
    (containsCharRegex c).Matches w ↔ c ∈ w := by
  constructor
  · rintro ⟨u, v, _, ⟨a, b, ⟨d, rfl, hd⟩, _, rfl⟩, rfl⟩
    rw [(pred_interval_singleton c d).mp hd]
    simp
  · intro hc
    obtain ⟨u, v, rfl⟩ := List.append_of_mem hc
    exact ⟨u, c :: v, anyCharStar_matches u,
      ⟨[c], v, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩, anyCharStar_matches v, rfl⟩, rfl⟩

private def containsDoubleCharRegex (c : Char) : Regex :=
  .seq (.star anyCharRegex)
    (.seq (.pred (.interval c c)) (.seq (.pred (.interval c c)) (.star anyCharRegex)))

private theorem containsDoubleCharRegex_iff (c : Char) (w : List Char) :
    (containsDoubleCharRegex c).Matches w ↔ ∃ u v, w = u ++ c :: c :: v := by
  constructor
  · rintro ⟨u, r1, _, ⟨a, r2, ⟨d1, rfl, h1⟩, ⟨b, v, ⟨d2, rfl, h2⟩, _, rfl⟩, rfl⟩, rfl⟩
    rw [(pred_interval_singleton c d1).mp h1, (pred_interval_singleton c d2).mp h2]
    exact ⟨u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨u, c :: c :: v, anyCharStar_matches u,
      ⟨[c], c :: v, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩,
        ⟨[c], v, ⟨c, rfl, (pred_interval_singleton c c).mpr rfl⟩, anyCharStar_matches v, rfl⟩,
        rfl⟩, rfl⟩

private def normClass : PatternClass :=
  .neg (.union (.interval '\r' '\r') (.union (.interval '\n' '\n') (.interval '\t' '\t')))

private theorem normClass_iff (c : Char) :
    normClass.accepts c = true ↔ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\t' := by
  have h1 := pred_interval_singleton '\r' c
  have h2 := pred_interval_singleton '\n' c
  have h3 := pred_interval_singleton '\t' c
  change !((PatternClass.interval '\r' '\r').accepts c ||
    ((PatternClass.interval '\n' '\n').accepts c ||
      (PatternClass.interval '\t' '\t').accepts c)) = true ↔ _
  cases ha : (PatternClass.interval '\r' '\r').accepts c <;>
    cases hb : (PatternClass.interval '\n' '\n').accepts c <;>
    cases hc : (PatternClass.interval '\t' '\t').accepts c <;>
    simp_all

private def normConstraint : Constraint :=
  .atom (.star (.pred normClass))

private theorem normConstraint_iff (s : String) :
    normConstraint.Holds s.toList ↔ isNormalizedString s = true := by
  simp only [normConstraint, Constraint.Holds, star_pred_iff, normClass_iff,
    isNormalizedString, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact forall_congr' fun c => imp_congr_right fun _ =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

private def tokenConstraint : Constraint :=
  .and normConstraint
    (.and (.not (.atom (startsWithCharRegex ' ')))
      (.and (.not (.atom (endsWithCharRegex ' ')))
        (.not (.atom (containsDoubleCharRegex ' ')))))

private theorem tokenConstraint_iff (s : String) :
    tokenConstraint.Holds s.toList ↔ isToken s = true := by
  rw [isToken_iff]
  simp only [tokenConstraint, Constraint.Holds, normConstraint_iff,
    startsWithCharRegex_iff, endsWithCharRegex_iff, containsDoubleCharRegex_iff, not_exists]

private def nmtokenConstraint : Constraint :=
  .atom (.seq (.pred .nameChar) (.star (.pred .nameChar)))

private theorem nmtokenConstraint_iff (s : String) :
    nmtokenConstraint.Holds s.toList ↔ isNMTOKEN s = true := by
  simp only [nmtokenConstraint, Constraint.Holds, plus_pred_iff, PatternClass.accepts,
    isNMTOKEN, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  have hne : s.toList ≠ [] ↔ s.isEmpty = false := by
    cases hs : s.isEmpty
    · simp only [iff_true]
      intro hnil
      have h0 : s = "" := by
        have := congrArg String.ofList hnil
        simpa using this
      subst h0; cases hs
    · simp only [Bool.true_eq_false, iff_false]
      intro hne'
      have h0 := String.isEmpty_iff.mp hs
      subst h0; exact hne' rfl
  rw [hne]

private def nameConstraint : Constraint :=
  .atom (.seq (.pred .nameStart) (.star (.pred .nameChar)))

private theorem nameConstraint_iff (s : String) :
    nameConstraint.Holds s.toList ↔ isName s = true := by
  simp only [nameConstraint, Constraint.Holds, isName]
  cases hs : s.toList with
  | nil =>
    simp only [Regex.Matches, Bool.false_eq_true, iff_false, not_exists, not_and]
    rintro u v ⟨c, rfl, _⟩ _ heq
    cases heq
  | cons c rest =>
    simp only [Bool.and_eq_true, List.all_eq_true]
    constructor
    · rintro ⟨u, v, ⟨d, rfl, hd⟩, hv, heq⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact ⟨hd, (star_pred_iff .nameChar _).mp hv⟩
    · rintro ⟨hc, hrest⟩
      exact ⟨[c], rest, ⟨c, rfl, hc⟩, (star_pred_iff .nameChar rest).mpr hrest, rfl⟩

private def ncNameConstraint : Constraint :=
  .and nameConstraint (.not (.atom (containsCharRegex ':')))

private theorem ncNameConstraint_iff (s : String) :
    ncNameConstraint.Holds s.toList ↔ isNCName s = true := by
  simp only [ncNameConstraint, Constraint.Holds, nameConstraint_iff, containsCharRegex_iff,
    isNCName, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem]

private def alphaClass : PatternClass :=
  .union (.interval 'a' 'z') (.interval 'A' 'Z')

private def alnumClass : PatternClass :=
  .union alphaClass (.interval '0' '9')

private def upToRegex (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => .alt .eps (.seq r (upToRegex r n))

private theorem upToRegex_pred_iff (p : PatternClass) (n : Nat) (w : List Char) :
    (upToRegex (.pred p) n).Matches w ↔ w.length ≤ n ∧ ∀ c ∈ w, p.accepts c = true := by
  induction n generalizing w with
  | zero =>
    simp only [upToRegex, Regex.Matches, Nat.le_zero, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨h, by simp [h]⟩, And.left⟩
  | succ n ih =>
    simp only [upToRegex, Regex.Matches]
    constructor
    · rintro (rfl | ⟨u, v, ⟨c, rfl, hc⟩, hv, rfl⟩)
      · exact ⟨Nat.zero_le _, by simp⟩
      · obtain ⟨hlen, hall⟩ := (ih v).mp hv
        refine ⟨by simp; omega, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hc
        · exact hall x hx'
    · rintro ⟨hlen, hall⟩
      cases w with
      | nil => exact .inl rfl
      | cons c rest =>
        refine .inr ⟨[c], rest, ⟨c, rfl, hall c (List.mem_cons_self ..)⟩,
          (ih rest).mpr ⟨by simp at hlen; omega, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩,
          rfl⟩

private def subtagRegex (p : PatternClass) : Regex :=
  .seq (.pred p) (upToRegex (.pred p) 7)

private theorem subtagRegex_iff (p : PatternClass) (w : List Char) :
    (subtagRegex p).Matches w ↔ 1 ≤ w.length ∧ w.length ≤ 8 ∧ ∀ c ∈ w, p.accepts c = true := by
  constructor
  · rintro ⟨u, v, ⟨c, rfl, hc⟩, hv, rfl⟩
    obtain ⟨hlen, hall⟩ := (upToRegex_pred_iff p 7 v).mp hv
    refine ⟨by simp, by simp; omega, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hc
    · exact hall x hx'
  · rintro ⟨h1, h8, hall⟩
    cases w with
    | nil => simp at h1
    | cons c rest =>
      exact ⟨[c], rest, ⟨c, rfl, hall c (List.mem_cons_self ..)⟩,
        (upToRegex_pred_iff p 7 rest).mpr ⟨by simp at h8; omega, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩,
        rfl⟩

private def languageRegex : Regex :=
  .seq (subtagRegex alphaClass) (.star (.seq (.pred (.interval '-' '-')) (subtagRegex alnumClass)))

private theorem star_dash_subtag_iff (w : List Char) :
    (Regex.star (.seq (.pred (.interval '-' '-')) (subtagRegex alnumClass))).Matches w ↔
      ∃ ps : List (List Char), w = ps.flatMap ('-' :: ·) ∧
        ∀ p ∈ ps, 1 ≤ p.length ∧ p.length ≤ 8 ∧ ∀ c ∈ p, isAsciiAlnumChar c = true := by
  have halnum : ∀ c, alnumClass.accepts c = isAsciiAlnumChar c := fun c => by
    rfl
  constructor
  · intro h
    change Repeats _ w at h
    induction h with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons hu _ ih =>
      obtain ⟨d, p, ⟨c, rfl, hc⟩, hp, rfl⟩ := hu
      have hcd : c = '-' := (pred_interval_singleton '-' c).mp hc
      subst hcd
      obtain ⟨p1, p8, pall⟩ := (subtagRegex_iff alnumClass p).mp hp
      obtain ⟨ps, rfl, hps⟩ := ih
      refine ⟨p :: ps, rfl, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨p1, p8, fun x hx => halnum x ▸ pall x hx⟩
      · exact hps q hq'
  · rintro ⟨ps, rfl, hps⟩
    induction ps with
    | nil => exact .nil
    | cons p rest ih =>
      obtain ⟨p1, p8, pall⟩ := hps p (List.mem_cons_self ..)
      have hhead : (Regex.seq (.pred (.interval '-' '-')) (subtagRegex alnumClass)).Matches ('-' :: p) :=
        ⟨['-'], p, ⟨'-', rfl, (pred_interval_singleton '-' '-').mpr rfl⟩,
          (subtagRegex_iff alnumClass p).mpr ⟨p1, p8, fun x hx => (halnum x).symm ▸ pall x hx⟩, rfl⟩
      exact Repeats.cons hhead (ih fun q hq => hps q (List.mem_cons_of_mem _ hq))

private def languageConstraint : Constraint :=
  .atom languageRegex

private theorem languageConstraint_iff (s : String) :
    languageConstraint.Holds s.toList ↔ isLanguageTag s = true := by
  rw [isLanguageTag_iff]
  have halpha : ∀ c, alphaClass.accepts c = isAsciiAlphaChar c := fun _ => rfl
  change (∃ first tail, (subtagRegex alphaClass).Matches first ∧
      (Regex.star (.seq (.pred (.interval '-' '-')) (subtagRegex alnumClass))).Matches tail ∧
      s.toList = first ++ tail) ↔ _
  simp only [subtagRegex_iff, star_dash_subtag_iff]
  constructor
  · rintro ⟨first, tail, ⟨h1, h8, ha⟩, ⟨rest, rfl, hrest⟩, hs⟩
    exact ⟨first, rest, hs, ⟨h1, h8, fun c hc => halpha c ▸ ha c hc⟩, hrest⟩
  · rintro ⟨first, rest, hs, ⟨h1, h8, ha⟩, hrest⟩
    exact ⟨first, rest.flatMap ('-' :: ·), ⟨h1, h8, fun c hc => (halpha c).symm ▸ ha c hc⟩,
      ⟨rest, rfl, hrest⟩, hs⟩

private def universalFormula : Formula := .text (.not (.atom .empty))
private def emptyFormula : Formula := .text (.atom .empty)

private theorem universalFormula_holds (w : TaggedWord) : universalFormula.Holds w :=
  fun h => h

private theorem emptyFormula_not_holds (w : TaggedWord) : ¬ emptyFormula.Holds w :=
  fun h => h

private def strDatatypeFormula (t : IRI) : Formula :=
  if t == rdf "PlainLiteral" then universalFormula
  else if t == xsd "string" then .tag (.atom .eps)
  else if t == xsd "normalizedString" then .and (.tag (.atom .eps)) (.text normConstraint)
  else if t == xsd "token" then .and (.tag (.atom .eps)) (.text tokenConstraint)
  else if t == xsd "language" then .and (.tag (.atom .eps)) (.text languageConstraint)
  else if t == xsd "NMTOKEN" then .and (.tag (.atom .eps)) (.text nmtokenConstraint)
  else if t == xsd "Name" then .and (.tag (.atom .eps)) (.text nameConstraint)
  else if t == xsd "NCName" then .and (.tag (.atom .eps)) (.text ncNameConstraint)
  else emptyFormula

private theorem eps_matches_isEmpty (lang : String) :
    Regex.eps.Matches lang.toList ↔ lang.isEmpty = true := by
  simp only [Regex.Matches]
  constructor
  · intro h
    have h0 : lang = "" := by
      have := congrArg String.ofList h
      simpa using this
    subst h0; rfl
  · intro h
    rw [String.isEmpty_iff.mp h]; rfl

theorem checkValue_plainLiteral_false_of_not_str {t : IRI} (h : isStringDatatype t = false)
    (s lang : String) : checkValue t (.plainLiteral s lang) = false := by
  cases hc : checkValue t (.plainLiteral s lang)
  · rfl
  · exfalso
    have hvs := valueSpace_plainLiteral_iri ((checkValue_iff t (.plainLiteral s lang)).mp hc)
    have hstr : isStringDatatype t = true := by
      rcases hvs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h] at hstr; cases hstr

private theorem strDatatypeFormula_iff (t : IRI) (s lang : String) :
    (strDatatypeFormula t).Holds (s.toList, lang.toList) ↔
      checkValue t (.plainLiteral s lang) = true := by
  unfold strDatatypeFormula
  by_cases h1 : t = rdf "PlainLiteral"
  · subst h1; simp [universalFormula_holds]; rfl
  simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : t = xsd "string"
  · subst h2
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds, eps_matches_isEmpty]
    change lang.isEmpty = true ↔ decide (lang.isEmpty = true) = true
    simp
  simp only [beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : t = xsd "normalizedString"
  · subst h3
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, normConstraint_iff]
    change (lang.isEmpty = true ∧ isNormalizedString s = true) ↔
      decide ((lang.isEmpty && isNormalizedString s) = true) = true
    simp
  simp only [beq_false_of_ne h3, Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : t = xsd "token"
  · subst h4
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, tokenConstraint_iff]
    change (lang.isEmpty = true ∧ isToken s = true) ↔
      decide ((lang.isEmpty && isToken s) = true) = true
    simp
  simp only [beq_false_of_ne h4, Bool.false_eq_true, ↓reduceIte]
  by_cases h5 : t = xsd "language"
  · subst h5
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, languageConstraint_iff]
    change (lang.isEmpty = true ∧ isLanguageTag s = true) ↔
      decide ((lang.isEmpty && isLanguageTag s) = true) = true
    simp
  simp only [beq_false_of_ne h5, Bool.false_eq_true, ↓reduceIte]
  by_cases h6 : t = xsd "NMTOKEN"
  · subst h6
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, nmtokenConstraint_iff]
    change (lang.isEmpty = true ∧ isNMTOKEN s = true) ↔
      decide ((lang.isEmpty && isNMTOKEN s) = true) = true
    simp
  simp only [beq_false_of_ne h6, Bool.false_eq_true, ↓reduceIte]
  by_cases h7 : t = xsd "Name"
  · subst h7
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, nameConstraint_iff]
    change (lang.isEmpty = true ∧ isName s = true) ↔
      decide ((lang.isEmpty && isName s) = true) = true
    simp
  simp only [beq_false_of_ne h7, Bool.false_eq_true, ↓reduceIte]
  by_cases h8 : t = xsd "NCName"
  · subst h8
    simp only [beq_self_eq_true, ↓reduceIte, Formula.Holds, Constraint.Holds,
      eps_matches_isEmpty, ncNameConstraint_iff]
    change (lang.isEmpty = true ∧ isNCName s = true) ↔
      decide ((lang.isEmpty && isNCName s) = true) = true
    simp
  simp only [beq_false_of_ne h8, Bool.false_eq_true, ↓reduceIte]
  have hnotStr : isStringDatatype t = false := by
    simp [isStringDatatype, beq_false_of_ne, h1, h2, h3, h4, h5, h6, h7, h8]
  rw [checkValue_plainLiteral_false_of_not_str hnotStr]
  exact ⟨fun h => (emptyFormula_not_holds _ h).elim, fun h => by cases h⟩

/-! ### 3. Compiling atoms and Venn partitions to `Formula` (for `.plainLiteral`) -/

private def lengthConstraint (lf : LengthFacet) (n : Nat) : Constraint :=
  match lf with
  | .length => .atom (lengthPatternAux n)
  | .minLength => .atom (.seq (lengthPatternAux n) (.star anyCharRegex))
  | .maxLength => .not (.atom (.seq (lengthPatternAux (n + 1)) (.star anyCharRegex)))
where
  lengthPatternAux : Nat → Regex
    | 0 => .eps
    | k + 1 => .seq anyCharRegex (lengthPatternAux k)

private theorem lengthPatternAux_iff (n : Nat) (w : List Char) :
    (lengthConstraint.lengthPatternAux n).Matches w ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [lengthConstraint.lengthPatternAux, Regex.Matches]
  | succ n ih =>
    constructor
    · rintro ⟨u, v, ⟨c, rfl, _⟩, hv, rfl⟩
      simp [(ih v).mp hv]
    · cases w with
      | nil => simp
      | cons c rest =>
        intro h
        exact ⟨[c], rest, ⟨c, rfl, rfl⟩, (ih rest).mpr (by simpa using h), rfl⟩

private theorem minLengthRegex_iff (n : Nat) (w : List Char) :
    (Regex.seq (lengthConstraint.lengthPatternAux n) (.star anyCharRegex)).Matches w ↔ n ≤ w.length := by
  constructor
  · rintro ⟨u, v, hu, _, rfl⟩
    simp [(lengthPatternAux_iff n u).mp hu]
  · intro h
    exact ⟨w.take n, w.drop n, (lengthPatternAux_iff n _).mpr (by simp [List.length_take, h]),
      anyCharStar_matches _, (List.take_append_drop ..).symm⟩

private theorem lengthConstraint_iff (lf : LengthFacet) (n : Nat) (s : String) :
    (lengthConstraint lf n).Holds s.toList ↔ lf.holds n s := by
  cases lf with
  | length =>
    simpa [lengthConstraint, Constraint.Holds, LengthFacet.holds, String.length] using
      lengthPatternAux_iff n s.toList
  | minLength =>
    simpa [lengthConstraint, Constraint.Holds, LengthFacet.holds, String.length] using
      minLengthRegex_iff n s.toList
  | maxLength =>
    simp only [lengthConstraint, Constraint.Holds, LengthFacet.holds, String.length,
      minLengthRegex_iff]
    omega

private def plainFacetFormula? (f : Facet) : Option Formula :=
  match decodeLiteral f.bound with
  | some (.number n) =>
    match lengthFacet f.name with
    | some lf => if n.den = 1 ∧ 0 ≤ n.num then some (.text (lengthConstraint lf n.num.toNat)) else none
    | none => none
  | some (.plainLiteral pat "") =>
    if f.name == xsd "pattern" then (parseCompleteRegex pat).map fun r => .text (.atom r)
    else if f.name == rdf "langRange" then some (.tag (.atom (langRangeRegex pat)))
    else none
  | _ => none

private theorem plainFacetFormula_iff {t : IRI} {f : Facet}
    (hs : isStringFacetSupported t f = true) (hstr : isStringDatatype t = true) :
    ∃ phi, plainFacetFormula? f = some phi ∧
      ∀ s lang, checkValue t (.plainLiteral s lang) = true →
        (phi.Holds (s.toList, lang.toList) ↔
          (match decodeLiteral f.bound with
           | some b => checkFacet t f.name b (.plainLiteral s lang)
           | none => false) = true) := by
  unfold isStringFacetSupported at hs
  cases hdec : decodeLiteral f.bound with
  | none => simp [hdec] at hs
  | some bound =>
    simp only [hdec, Bool.and_eq_true] at hs
    obtain ⟨happ, hpat⟩ := hs
    have happ' := (checkApplicableFacet_iff t f.name bound).mp happ
    have htCases : t = rdf "PlainLiteral" ∨ t = xsd "string" ∨ t = xsd "normalizedString" ∨
        t = xsd "token" ∨ t = xsd "language" ∨ t = xsd "NMTOKEN" ∨
        t = xsd "Name" ∨ t = xsd "NCName" := by
      simp only [isStringDatatype, Bool.or_eq_true, beq_iff_eq] at hstr
      rcases hstr with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr (.inl rfl)))
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
    rcases applicableFacet_str_cases htCases happ' with
      ⟨n, rfl, hden, hnn, hlf⟩ | ⟨pat, rfl, hfn | ⟨_, hfn⟩⟩
    · obtain ⟨lf, hlfEq⟩ := Option.isSome_iff_exists.mp hlf
      refine ⟨.text (lengthConstraint lf n.num.toNat), ?_, fun s lang ht => ?_⟩
      · simp [plainFacetFormula?, hdec, hlfEq, hden, hnn]
      · simp [Formula.Holds, lengthConstraint_iff, checkFacet, hlfEq, hden, hnn, ht]
    · simp only [hfn, beq_self_eq_true, ↓reduceIte] at hpat
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hpat
      have hne : xsd "pattern" ≠ rdf "langRange" := by decide
      refine ⟨.text (.atom r), ?_, fun s lang ht => ?_⟩
      · simp [plainFacetFormula?, hdec, hfn, hr]
      · simp only [Formula.Holds, Constraint.Holds, checkFacet, hfn, beq_self_eq_true,
          beq_false_of_ne hne, ht, Bool.true_and, Bool.false_and, Bool.or_false]
        exact (matchesPattern_iff hr s).symm
    · have hne : rdf "langRange" ≠ xsd "pattern" := by decide
      refine ⟨.tag (.atom (langRangeRegex pat)), ?_, fun s lang ht => ?_⟩
      · simp [plainFacetFormula?, hdec, hfn, beq_false_of_ne hne]
      · simp only [Formula.Holds, Constraint.Holds, checkFacet, hfn, beq_false_of_ne hne,
          beq_self_eq_true, ht, Bool.true_and, Bool.false_and, Bool.false_or]
        exact langRangeRegex_iff pat lang

private def foldPlainFacets? (acc : Formula) : List Facet → Option Formula
  | [] => some acc
  | f :: fs => (plainFacetFormula? f).bind fun phi => foldPlainFacets? (.and acc phi) fs

private def oneOfPlainFormula : List Value → Formula
  | [] => emptyFormula
  | .plainLiteral s l :: rest =>
    .or (.and (.text (.atom (exactWordRegex s.toList))) (.tag (.atom (exactWordRegex l.toList))))
      (oneOfPlainFormula rest)
  | _ :: rest => oneOfPlainFormula rest

private theorem oneOfPlainFormula_iff (vs : List Value) (s lang : String) :
    (oneOfPlainFormula vs).Holds (s.toList, lang.toList) ↔ Value.plainLiteral s lang ∈ vs := by
  induction vs with
  | nil => simp [oneOfPlainFormula, emptyFormula_not_holds]
  | cons v rest ih =>
    cases v
    case plainLiteral s' l' =>
      simp only [oneOfPlainFormula, Formula.Holds, Constraint.Holds,
        exactWordRegex_iff, ih, List.mem_cons, Value.plainLiteral.injEq]
      refine or_congr ?_ Iff.rfl
      exact ⟨fun ⟨h1, h2⟩ => ⟨by simpa using congrArg String.ofList h1, by simpa using congrArg String.ofList h2⟩,
             fun ⟨h1, h2⟩ => ⟨congrArg String.toList h1, congrArg String.toList h2⟩⟩
    all_goals
      simp [oneOfPlainFormula, ih]

private def plainAtomFormula? : DataRange → Option Formula
  | .datatype t =>
    if t == literalDatatype then some universalFormula else some (strDatatypeFormula t)
  | .restriction t fs =>
    if isStringDatatype t then foldPlainFacets? (strDatatypeFormula t) fs
    else some emptyFormula
  | .oneOf ls =>
    match decodeLiteralsList ls with
    | some vs => some (oneOfPlainFormula vs)
    | none => some emptyFormula
  | _ => some emptyFormula

private theorem foldPlainFacets_iff {t : IRI} {fs : List Facet}
    (hstr : isStringDatatype t = true) (hfs : ∀ f ∈ fs, isStringFacetSupported t f = true)
    (acc : Formula) :
    ∃ phi, foldPlainFacets? acc fs = some phi ∧
      ∀ s lang, checkValue t (.plainLiteral s lang) = true →
        (phi.Holds (s.toList, lang.toList) ↔
          acc.Holds (s.toList, lang.toList) ∧
          ∀ f ∈ fs, (match decodeLiteral f.bound with
            | some b => checkFacet t f.name b (.plainLiteral s lang)
            | none => false) = true) := by
  induction fs generalizing acc with
  | nil => exact ⟨acc, rfl, fun _ _ _ => by simp⟩
  | cons f rest ih =>
    obtain ⟨pf, hpf, hpfIff⟩ := plainFacetFormula_iff (hfs f (List.mem_cons_self ..)) hstr
    obtain ⟨res, hres, hresIff⟩ := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) (.and acc pf)
    refine ⟨res, by simp [foldPlainFacets?, hpf, hres], fun s lang ht => ?_⟩
    rw [hresIff s lang ht]
    simp only [Formula.Holds, hpfIff s lang ht, List.forall_mem_cons]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

private theorem plainAtomFormula_spec {a : DataRange}
    (ha : match a with
      | .restriction t fs => isStringDatatype t = true → ∀ f ∈ fs, isStringFacetSupported t f = true
      | _ => True) :
    ∃ phi, plainAtomFormula? a = some phi ∧
      ∀ s lang, phi.Holds (s.toList, lang.toList) ↔ evalWiderAtom a (.plainLiteral s lang) = true := by
  cases a with
  | datatype t =>
    by_cases hlit : t = literalDatatype
    · subst hlit
      exact ⟨universalFormula, by simp [plainAtomFormula?], fun _ _ => by simp [universalFormula_holds, evalWiderAtom]⟩
    · exact ⟨strDatatypeFormula t, by simp [plainAtomFormula?, beq_false_of_ne hlit],
        fun s lang => by simp [evalWiderAtom, beq_false_of_ne hlit, strDatatypeFormula_iff]⟩
  | restriction t fs =>
    cases hstr : isStringDatatype t
    · refine ⟨emptyFormula, by simp [plainAtomFormula?, hstr], fun s lang => ?_⟩
      simp [evalWiderAtom, checkValue_plainLiteral_false_of_not_str hstr, emptyFormula_not_holds]
    · obtain ⟨phi, hphi, hphiIff⟩ := foldPlainFacets_iff hstr (ha hstr) (strDatatypeFormula t)
      refine ⟨phi, by simp [plainAtomFormula?, hstr, hphi], fun s lang => ?_⟩
      simp only [evalWiderAtom, Bool.and_eq_true, List.all_eq_true]
      by_cases ht : checkValue t (.plainLiteral s lang) = true
      · rw [hphiIff s lang ht, strDatatypeFormula_iff, ht]; simp only [true_and]; exact Iff.rfl
      · have htF : checkValue t (.plainLiteral s lang) = false := Bool.eq_false_iff.mpr ht
        have hnotAcc : ¬ (strDatatypeFormula t).Holds (s.toList, lang.toList) := by
          rw [strDatatypeFormula_iff]; exact ht
        have hsub : ∀ (l : List Facet) (init res : Formula),
            foldPlainFacets? init l = some res →
            ∀ w, res.Holds w → init.Holds w := by
          intro l
          induction l with
          | nil => intro init res h; cases h; intro _ hw; exact hw
          | cons f tail iht =>
            intro init res h w hw
            simp only [foldPlainFacets?, Option.bind_eq_some_iff] at h
            obtain ⟨pf, _, htail⟩ := h
            exact (iht (.and init pf) res htail w hw).1
        exact ⟨fun hp => (hnotAcc (hsub fs (strDatatypeFormula t) phi hphi _ hp)).elim,
               fun ⟨hc, _⟩ => (ht hc).elim⟩
  | oneOf ls =>
    cases hdec : decodeLiteralsList ls with
    | none =>
      exact ⟨emptyFormula, by simp [plainAtomFormula?, hdec],
        fun _ _ => by simp [evalWiderAtom, hdec, emptyFormula_not_holds]⟩
    | some vs =>
      exact ⟨oneOfPlainFormula vs, by simp [plainAtomFormula?, hdec],
        fun s lang => by simp [evalWiderAtom, hdec, oneOfPlainFormula_iff]⟩
  | complement _ | intersection _ _ | union _ _ =>
    exact ⟨emptyFormula, rfl, fun _ _ => by simp [evalWiderAtom, emptyFormula_not_holds]⟩

private def plainPartitionFormula? (pos neg : List DataRange) : Option Formula := do
  let p ← pos.foldrM (fun a acc => (plainAtomFormula? a).map (.and · acc)) universalFormula
  neg.foldrM (fun a acc => (plainAtomFormula? a).map fun phi => .and (.not phi) acc) p

private theorem foldrM_and_spec {α : Type} (f : α → Option Formula) (xs : List α)
    (init : Formula)
    (hf : ∀ a ∈ xs, ∃ phi, f a = some phi) :
    ∃ res, xs.foldrM (fun a acc => (f a).map (.and · acc)) init = some res ∧
      ∀ w, res.Holds w ↔ init.Holds w ∧ ∀ a ∈ xs, ∀ phi, f a = some phi → phi.Holds w := by
  induction xs with
  | nil => exact ⟨init, rfl, fun _ => by simp⟩
  | cons a rest ih =>
    obtain ⟨pa, hpa⟩ := hf a (List.mem_cons_self ..)
    obtain ⟨res, hres, hresIff⟩ := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    refine ⟨.and pa res, ?_, fun w => ?_⟩
    · simp only [List.foldrM_cons, hres, Option.bind_eq_bind, Option.bind_some, hpa, Option.map_some]
    · simp only [Formula.Holds, hresIff w, List.forall_mem_cons]
      constructor
      · rintro ⟨hp, hi, hrest⟩
        refine ⟨hi, fun phi hfa => ?_, hrest⟩
        rw [hpa] at hfa; cases hfa; exact hp
      · rintro ⟨hi, ha, hrest⟩
        exact ⟨ha pa hpa, hi, hrest⟩

private theorem foldrM_not_spec {α : Type} (f : α → Option Formula) (xs : List α)
    (init : Formula)
    (hf : ∀ a ∈ xs, ∃ phi, f a = some phi) :
    ∃ res, xs.foldrM (fun a acc => (f a).map fun phi => .and (.not phi) acc) init = some res ∧
      ∀ w, res.Holds w ↔ init.Holds w ∧ ∀ a ∈ xs, ∀ phi, f a = some phi → ¬ phi.Holds w := by
  induction xs with
  | nil => exact ⟨init, rfl, fun _ => by simp⟩
  | cons a rest ih =>
    obtain ⟨pa, hpa⟩ := hf a (List.mem_cons_self ..)
    obtain ⟨res, hres, hresIff⟩ := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    refine ⟨.and (.not pa) res, ?_, fun w => ?_⟩
    · simp only [List.foldrM_cons, hres, Option.bind_eq_bind, Option.bind_some, hpa, Option.map_some]
    · simp only [Formula.Holds, hresIff w, List.forall_mem_cons]
      constructor
      · rintro ⟨hp, hi, hrest⟩
        refine ⟨hi, fun phi hfa => ?_, hrest⟩
        rw [hpa] at hfa; cases hfa; exact hp
      · rintro ⟨hi, ha, hrest⟩
        exact ⟨ha pa hpa, hi, hrest⟩

def stringFacetPlainCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  match plainPartitionFormula? pos neg with
  | some F => (F.sample K).map fun w => Value.plainLiteral (String.ofList w.1) (String.ofList w.2)
  | none => []

theorem stringFacetPlainCandidates_cover {K : Nat} {pos neg : List DataRange}
    (hadm : ∀ a ∈ pos ++ neg, match a with
      | .restriction t fs => isStringDatatype t = true → ∀ f ∈ fs, isStringFacetSupported t f = true
      | _ => True)
    {s lang : String} (hev : evalWiderPartition pos neg (.plainLiteral s lang) = true)
    (hshort : ((stringFacetPlainCandidates K pos neg).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    Value.plainLiteral s lang ∈ stringFacetPlainCandidates K pos neg := by
  have hpSpec : ∀ a ∈ pos, ∃ phi, plainAtomFormula? a = some phi ∧
      ∀ s' l', phi.Holds (s'.toList, l'.toList) ↔ evalWiderAtom a (.plainLiteral s' l') = true :=
    fun a ha => plainAtomFormula_spec (hadm a (List.mem_append_left _ ha))
  have hnSpec : ∀ a ∈ neg, ∃ phi, plainAtomFormula? a = some phi ∧
      ∀ s' l', phi.Holds (s'.toList, l'.toList) ↔ evalWiderAtom a (.plainLiteral s' l') = true :=
    fun a ha => plainAtomFormula_spec (hadm a (List.mem_append_right _ ha))
  obtain ⟨pF, hpF, hpFIff⟩ := foldrM_and_spec plainAtomFormula? pos universalFormula
    (fun a ha => let ⟨phi, h, _⟩ := hpSpec a ha; ⟨phi, h⟩)
  obtain ⟨F, hF, hFIff⟩ := foldrM_not_spec plainAtomFormula? neg pF
    (fun a ha => let ⟨phi, h, _⟩ := hnSpec a ha; ⟨phi, h⟩)
  have hpartEq : plainPartitionFormula? pos neg = some F := by
    simp [plainPartitionFormula?, hpF, hF]
  have hEvalIff (s' l' : String) :
      F.Holds (s'.toList, l'.toList) ↔ evalWiderPartition pos neg (.plainLiteral s' l') = true := by
    rw [hFIff, hpFIff]
    simp only [universalFormula_holds, true_and, evalWiderPartition, Bool.and_eq_true,
      List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    refine and_congr ?_ ?_
    · constructor
      · intro h a ha
        obtain ⟨phi, hphi, hiff⟩ := hpSpec a ha
        exact (hiff s' l').mp (h a ha phi hphi)
      · intro h a ha phi hphi
        obtain ⟨phi', hphi', hiff⟩ := hpSpec a ha
        rw [hphi] at hphi'; cases hphi'
        exact (hiff s' l').mpr (h a ha)
    · constructor
      · intro h a ha
        obtain ⟨phi, hphi, hiff⟩ := hnSpec a ha
        exact fun he => h a ha phi hphi ((hiff s' l').mpr he)
      · intro h a ha phi hphi
        obtain ⟨phi', hphi', hiff⟩ := hnSpec a ha
        rw [hphi] at hphi'; cases hphi'
        exact fun hp => h a ha ((hiff s' l').mp hp)
  have hcandEq : stringFacetPlainCandidates K pos neg =
      (F.sample K).map fun w => Value.plainLiteral (String.ofList w.1) (String.ofList w.2) := by
    simp [stringFacetPlainCandidates, hpartEq]
  obtain ⟨hnd, _, hsound, hfull⟩ := F.sample_exact K
  have hinj : ∀ w₁ w₂ : TaggedWord,
      Value.plainLiteral (String.ofList w₁.1) (String.ofList w₁.2) =
      Value.plainLiteral (String.ofList w₂.1) (String.ofList w₂.2) → w₁ = w₂ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    obtain ⟨ha, hb⟩ := Value.plainLiteral.inj h
    have h1 : a₁ = a₂ := by simpa using congrArg String.toList ha
    have h2 : b₁ = b₂ := by simpa using congrArg String.toList hb
    subst h1; subst h2; rfl
  have hndMap : (stringFacetPlainCandidates K pos neg).Nodup := by
    rw [hcandEq]
    exact hnd.map _ (fun _ _ hne heq => hne (hinj _ _ heq))
  have hallTrue : ∀ v ∈ stringFacetPlainCandidates K pos neg, evalWiderPartition pos neg v = true := by
    intro v hv
    rw [hcandEq] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hhold := hsound w hw
    exact (hEvalIff (String.ofList w.1) (String.ofList w.2)).mp
      (by simpa only [String.toList_ofList] using hhold)
  have hlenLe : (F.sample K).length ≤
      ((stringFacetPlainCandidates K pos neg).eraseDups.filter
        (evalWiderPartition pos neg)).length := by
    have h1 : (stringFacetPlainCandidates K pos neg).length ≤
        ((stringFacetPlainCandidates K pos neg).eraseDups.filter
          (evalWiderPartition pos neg)).length :=
      hndMap.length_le_of_subset fun v hv =>
        List.mem_filter.mpr ⟨List.mem_eraseDups.mpr hv, hallTrue v hv⟩
    have hlen : (stringFacetPlainCandidates K pos neg).length = (F.sample K).length := by
      rw [hcandEq, List.length_map]
    exact hlen ▸ h1
  have hlt : (F.sample K).length < K := Nat.lt_of_le_of_lt hlenLe hshort
  have hmem : (s.toList, lang.toList) ∈ F.sample K :=
    hfull hlt (s.toList, lang.toList) ((hEvalIff s lang).mpr hev)
  rw [hcandEq]
  refine List.mem_map.mpr ⟨(s.toList, lang.toList), hmem, ?_⟩
  simp

/-! ### 4. Compiling atoms and Venn partitions to `Constraint` (for `.anyURI`) -/

private def universalConstraint : Constraint := .not (.atom .empty)
private def emptyConstraint : Constraint := .atom .empty

private def uriFacetConstraint? (f : Facet) : Option Constraint :=
  match decodeLiteral f.bound with
  | some (.number n) =>
    match lengthFacet f.name with
    | some lf => if n.den = 1 ∧ 0 ≤ n.num then some (lengthConstraint lf n.num.toNat) else none
    | none => none
  | some (.plainLiteral pat "") =>
    if f.name == xsd "pattern" then (parseCompleteRegex pat).map Constraint.atom
    else none
  | _ => none

private theorem uriFacetConstraint_iff {f : Facet}
    (hs : isStringFacetSupported (xsd "anyURI") f = true) :
    ∃ c, uriFacetConstraint? f = some c ∧
      ∀ s, c.Holds s.toList ↔
        (match decodeLiteral f.bound with
         | some b => checkFacet (xsd "anyURI") f.name b (.anyURI s)
         | none => false) = true := by
  unfold isStringFacetSupported at hs
  cases hdec : decodeLiteral f.bound with
  | none => simp [hdec] at hs
  | some bound =>
    simp only [hdec, Bool.and_eq_true] at hs
    obtain ⟨happ, hpat⟩ := hs
    have happ' := (checkApplicableFacet_iff (xsd "anyURI") f.name bound).mp happ
    rcases applicableFacet_anyURI_cases happ' with
      ⟨n, rfl, hden, hnn, hlf⟩ | ⟨pat, rfl, hfn⟩
    · obtain ⟨lf, hlfEq⟩ := Option.isSome_iff_exists.mp hlf
      refine ⟨lengthConstraint lf n.num.toNat, ?_, fun s => ?_⟩
      · simp [uriFacetConstraint?, hdec, hlfEq, hden, hnn]
      · rw [lengthConstraint_iff]
        have hcvs : checkValue (xsd "anyURI") (.anyURI s) = true := rfl
        simp [checkFacet, hlfEq, hden, Rat.num_nonneg.mp hnn, hcvs]
    · simp only [hfn, beq_self_eq_true, ↓reduceIte] at hpat
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hpat
      refine ⟨.atom r, ?_, fun s => ?_⟩
      · simp [uriFacetConstraint?, hdec, hfn, hr]
      · have hcvs : checkValue (xsd "anyURI") (.anyURI s) = true := rfl
        simp only [Constraint.Holds, checkFacet, hfn, beq_self_eq_true, hcvs, Bool.true_and]
        exact (matchesPattern_iff hr s).symm

private def foldURIFacets? (acc : Constraint) : List Facet → Option Constraint
  | [] => some acc
  | f :: fs => (uriFacetConstraint? f).bind fun c => foldURIFacets? (.and acc c) fs

private def oneOfURIConstraint : List Value → Constraint
  | [] => emptyConstraint
  | .anyURI s :: rest => .or (.atom (exactWordRegex s.toList)) (oneOfURIConstraint rest)
  | _ :: rest => oneOfURIConstraint rest

private theorem oneOfURIConstraint_iff (vs : List Value) (s : String) :
    (oneOfURIConstraint vs).Holds s.toList ↔ Value.anyURI s ∈ vs := by
  induction vs with
  | nil => simp [oneOfURIConstraint, emptyConstraint, Constraint.Holds, Regex.Matches]
  | cons v rest ih =>
    cases v
    case anyURI s' =>
      simp only [oneOfURIConstraint, Constraint.Holds,
        exactWordRegex_iff, ih, List.mem_cons, Value.anyURI.injEq]
      refine or_congr ?_ Iff.rfl
      exact ⟨fun h => by simpa using congrArg String.ofList h, congrArg String.toList⟩
    all_goals
      simp [oneOfURIConstraint, ih]

theorem checkValue_anyURI_false_of_ne {t : IRI} (hne : t ≠ xsd "anyURI") (s : String) :
    checkValue t (.anyURI s) = false := by
  cases hc : checkValue t (.anyURI s)
  · rfl
  · exact (hne ((valueSpace_anyURI_iff t s).mp ((checkValue_iff t (.anyURI s)).mp hc))).elim

private def uriAtomConstraint? : DataRange → Option Constraint
  | .datatype t =>
    if t == literalDatatype || t == xsd "anyURI" then some universalConstraint
    else some emptyConstraint
  | .restriction t fs =>
    if t == xsd "anyURI" then foldURIFacets? universalConstraint fs
    else some emptyConstraint
  | .oneOf ls =>
    match decodeLiteralsList ls with
    | some vs => some (oneOfURIConstraint vs)
    | none => some emptyConstraint
  | _ => some emptyConstraint

private theorem foldURIFacets_iff {fs : List Facet}
    (hfs : ∀ f ∈ fs, isStringFacetSupported (xsd "anyURI") f = true)
    (acc : Constraint) :
    ∃ c, foldURIFacets? acc fs = some c ∧
      ∀ s, c.Holds s.toList ↔
        acc.Holds s.toList ∧
        ∀ f ∈ fs, (match decodeLiteral f.bound with
          | some b => checkFacet (xsd "anyURI") f.name b (.anyURI s)
          | none => false) = true := by
  induction fs generalizing acc with
  | nil => exact ⟨acc, rfl, fun _ => by simp⟩
  | cons f rest ih =>
    obtain ⟨cf, hcf, hcfIff⟩ := uriFacetConstraint_iff (hfs f (List.mem_cons_self ..))
    obtain ⟨res, hres, hresIff⟩ := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) (.and acc cf)
    refine ⟨res, by simp [foldURIFacets?, hcf, hres], fun s => ?_⟩
    rw [hresIff s]
    simp only [Constraint.Holds, hcfIff s, List.forall_mem_cons]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

private theorem uriAtomConstraint_spec {a : DataRange}
    (ha : match a with
      | .restriction t fs => t = xsd "anyURI" → ∀ f ∈ fs, isStringFacetSupported t f = true
      | _ => True) :
    ∃ c, uriAtomConstraint? a = some c ∧
      ∀ s, c.Holds s.toList ↔ evalWiderAtom a (.anyURI s) = true := by
  cases a with
  | datatype t =>
    by_cases hlit : t = literalDatatype
    · subst hlit
      exact ⟨universalConstraint, by simp [uriAtomConstraint?],
        fun _ => by simp [universalConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom]⟩
    · by_cases hu : t = xsd "anyURI"
      · subst hu
        exact ⟨universalConstraint, by simp [uriAtomConstraint?], fun s => by
          have hcvs : checkValue (xsd "anyURI") (.anyURI s) = true := rfl
          simp [universalConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom,
            beq_false_of_ne hlit, hcvs]⟩
      · exact ⟨emptyConstraint, by simp [uriAtomConstraint?, beq_false_of_ne hlit, beq_false_of_ne hu],
          fun s => by simp [emptyConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom,
            beq_false_of_ne hlit, checkValue_anyURI_false_of_ne hu]⟩
  | restriction t fs =>
    by_cases hu : t = xsd "anyURI"
    · subst hu
      obtain ⟨c, hc, hcIff⟩ := foldURIFacets_iff (ha rfl) universalConstraint
      refine ⟨c, by simp [uriAtomConstraint?, hc], fun s => ?_⟩
      have hcvs : checkValue (xsd "anyURI") (.anyURI s) = true := rfl
      simp only [hcIff s, universalConstraint, Constraint.Holds, Regex.Matches, not_false_eq_true,
        true_and, evalWiderAtom, hcvs, Bool.true_and, List.all_eq_true]
      exact Iff.rfl
    · exact ⟨emptyConstraint, by simp [uriAtomConstraint?, beq_false_of_ne hu],
        fun s => by simp [emptyConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom,
          checkValue_anyURI_false_of_ne hu]⟩
  | oneOf ls =>
    cases hdec : decodeLiteralsList ls with
    | none =>
      exact ⟨emptyConstraint, by simp [uriAtomConstraint?, hdec],
        fun _ => by simp [emptyConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom, hdec]⟩
    | some vs =>
      exact ⟨oneOfURIConstraint vs, by simp [uriAtomConstraint?, hdec],
        fun s => by simp [evalWiderAtom, hdec, oneOfURIConstraint_iff]⟩
  | complement _ | intersection _ _ | union _ _ =>
    exact ⟨emptyConstraint, rfl, fun _ => by simp [emptyConstraint, Constraint.Holds, Regex.Matches, evalWiderAtom]⟩

private def uriPartitionConstraint? (pos neg : List DataRange) : Option Constraint := do
  let p ← pos.foldrM (fun a acc => (uriAtomConstraint? a).map (.and · acc)) universalConstraint
  neg.foldrM (fun a acc => (uriAtomConstraint? a).map fun c => .and (.not c) acc) p

private theorem foldrM_and_constraint_spec {α : Type} (f : α → Option Constraint) (xs : List α)
    (init : Constraint)
    (hf : ∀ a ∈ xs, ∃ c, f a = some c) :
    ∃ res, xs.foldrM (fun a acc => (f a).map (.and · acc)) init = some res ∧
      ∀ w, res.Holds w ↔ init.Holds w ∧ ∀ a ∈ xs, ∀ c, f a = some c → c.Holds w := by
  induction xs with
  | nil => exact ⟨init, rfl, fun _ => by simp⟩
  | cons a rest ih =>
    obtain ⟨ca, hca⟩ := hf a (List.mem_cons_self ..)
    obtain ⟨res, hres, hresIff⟩ := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    refine ⟨.and ca res, ?_, fun w => ?_⟩
    · simp only [List.foldrM_cons, hres, Option.bind_eq_bind, Option.bind_some, hca, Option.map_some]
    · simp only [Constraint.Holds, hresIff w, List.forall_mem_cons]
      constructor
      · rintro ⟨hc, hi, hrest⟩
        refine ⟨hi, fun c hfa => ?_, hrest⟩
        rw [hca] at hfa; cases hfa; exact hc
      · rintro ⟨hi, ha, hrest⟩
        exact ⟨ha ca hca, hi, hrest⟩

private theorem foldrM_not_constraint_spec {α : Type} (f : α → Option Constraint) (xs : List α)
    (init : Constraint)
    (hf : ∀ a ∈ xs, ∃ c, f a = some c) :
    ∃ res, xs.foldrM (fun a acc => (f a).map fun c => .and (.not c) acc) init = some res ∧
      ∀ w, res.Holds w ↔ init.Holds w ∧ ∀ a ∈ xs, ∀ c, f a = some c → ¬ c.Holds w := by
  induction xs with
  | nil => exact ⟨init, rfl, fun _ => by simp⟩
  | cons a rest ih =>
    obtain ⟨ca, hca⟩ := hf a (List.mem_cons_self ..)
    obtain ⟨res, hres, hresIff⟩ := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    refine ⟨.and (.not ca) res, ?_, fun w => ?_⟩
    · simp only [List.foldrM_cons, hres, Option.bind_eq_bind, Option.bind_some, hca, Option.map_some]
    · simp only [Constraint.Holds, hresIff w, List.forall_mem_cons]
      constructor
      · rintro ⟨hc, hi, hrest⟩
        refine ⟨hi, fun c hfa => ?_, hrest⟩
        rw [hca] at hfa; cases hfa; exact hc
      · rintro ⟨hi, ha, hrest⟩
        exact ⟨ha ca hca, hi, hrest⟩

def stringFacetURICandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  match uriPartitionConstraint? pos neg with
  | some C => (UnicodeStringSampling.sample C K).map fun w => Value.anyURI (String.ofList w)
  | none => []

theorem stringFacetURICandidates_cover {K : Nat} {pos neg : List DataRange}
    (hadm : ∀ a ∈ pos ++ neg, match a with
      | .restriction t fs => t = xsd "anyURI" → ∀ f ∈ fs, isStringFacetSupported t f = true
      | _ => True)
    {s : String} (hev : evalWiderPartition pos neg (.anyURI s) = true)
    (hshort : ((stringFacetURICandidates K pos neg).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    Value.anyURI s ∈ stringFacetURICandidates K pos neg := by
  have hpSpec : ∀ a ∈ pos, ∃ c, uriAtomConstraint? a = some c ∧
      ∀ s', c.Holds s'.toList ↔ evalWiderAtom a (.anyURI s') = true :=
    fun a ha => uriAtomConstraint_spec (hadm a (List.mem_append_left _ ha))
  have hnSpec : ∀ a ∈ neg, ∃ c, uriAtomConstraint? a = some c ∧
      ∀ s', c.Holds s'.toList ↔ evalWiderAtom a (.anyURI s') = true :=
    fun a ha => uriAtomConstraint_spec (hadm a (List.mem_append_right _ ha))
  obtain ⟨pC, hpC, hpCIff⟩ := foldrM_and_constraint_spec uriAtomConstraint? pos universalConstraint
    (fun a ha => let ⟨c, h, _⟩ := hpSpec a ha; ⟨c, h⟩)
  obtain ⟨C, hC, hCIff⟩ := foldrM_not_constraint_spec uriAtomConstraint? neg pC
    (fun a ha => let ⟨c, h, _⟩ := hnSpec a ha; ⟨c, h⟩)
  have hpartEq : uriPartitionConstraint? pos neg = some C := by
    simp [uriPartitionConstraint?, hpC, hC]
  have hEvalIff (s' : String) :
      C.Holds s'.toList ↔ evalWiderPartition pos neg (.anyURI s') = true := by
    rw [hCIff, hpCIff]
    simp only [universalConstraint, Constraint.Holds, Regex.Matches, not_false_eq_true, true_and,
      evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq]
    refine and_congr ?_ ?_
    · constructor
      · intro h a ha
        obtain ⟨c, hc, hiff⟩ := hpSpec a ha
        exact (hiff s').mp (h a ha c hc)
      · intro h a ha c hc
        obtain ⟨c', hc', hiff⟩ := hpSpec a ha
        rw [hc] at hc'; cases hc'
        exact (hiff s').mpr (h a ha)
    · constructor
      · intro h a ha
        obtain ⟨c, hc, hiff⟩ := hnSpec a ha
        exact fun he => h a ha c hc ((hiff s').mpr he)
      · intro h a ha c hc
        obtain ⟨c', hc', hiff⟩ := hnSpec a ha
        rw [hc] at hc'; cases hc'
        exact fun hp => h a ha ((hiff s').mp hp)
  have hcandEq : stringFacetURICandidates K pos neg =
      (UnicodeStringSampling.sample C K).map fun w => Value.anyURI (String.ofList w) := by
    simp [stringFacetURICandidates, hpartEq]
  obtain ⟨hnd, _, hsound, hfull⟩ := UnicodeStringSampling.sample_exact C K
  have hinj : ∀ w₁ w₂ : List Char,
      Value.anyURI (String.ofList w₁) = Value.anyURI (String.ofList w₂) → w₁ = w₂ := by
    intro w₁ w₂ h
    have h1 := Value.anyURI.inj h
    simpa using congrArg String.toList h1
  have hndMap : (stringFacetURICandidates K pos neg).Nodup := by
    rw [hcandEq]
    exact hnd.map _ (fun _ _ hne heq => hne (hinj _ _ heq))
  have hallTrue : ∀ v ∈ stringFacetURICandidates K pos neg, evalWiderPartition pos neg v = true := by
    intro v hv
    rw [hcandEq] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hhold := hsound w hw
    exact (hEvalIff (String.ofList w)).mp (by simpa only [String.toList_ofList] using hhold)
  have hlenLe : (UnicodeStringSampling.sample C K).length ≤
      ((stringFacetURICandidates K pos neg).eraseDups.filter
        (evalWiderPartition pos neg)).length := by
    have h1 : (stringFacetURICandidates K pos neg).length ≤
        ((stringFacetURICandidates K pos neg).eraseDups.filter
          (evalWiderPartition pos neg)).length :=
      hndMap.length_le_of_subset fun v hv =>
        List.mem_filter.mpr ⟨List.mem_eraseDups.mpr hv, hallTrue v hv⟩
    have hlen : (stringFacetURICandidates K pos neg).length = (UnicodeStringSampling.sample C K).length := by
      rw [hcandEq, List.length_map]
    exact hlen ▸ h1
  have hlt : (UnicodeStringSampling.sample C K).length < K := Nat.lt_of_le_of_lt hlenLe hshort
  have hmem : s.toList ∈ UnicodeStringSampling.sample C K :=
    hfull hlt s.toList ((hEvalIff s).mpr hev)
  rw [hcandEq]
  refine List.mem_map.mpr ⟨s.toList, hmem, ?_⟩
  simp

#print axioms stringFacetPlainCandidates_cover
#print axioms stringFacetURICandidates_cover

end Sabrina.OWL2.SROIQD.Termination.WiderData
