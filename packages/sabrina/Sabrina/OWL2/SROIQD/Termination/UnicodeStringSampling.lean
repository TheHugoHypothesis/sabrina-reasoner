import Sabrina.OWL2.SROIQD.Termination.StringLanguage
import Sabrina.OWL2.SROIQD.Termination.BoundedWords

/-! A finite quotient of Unicode characters by the tests used in a
constraint. Each equivalence class retains up to the word witness cap.
Below that cap, the sampled language is exact over all Unicode scalars.

The quotient is constructed directly from the finite code-point boundaries of
the `PatternClass` predicates rather than scanning all 1,112,064 Unicode
scalars, yielding an exact alphabet in microseconds. -/

namespace Sabrina.OWL2.SROIQD.Termination.UnicodeStringSampling

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.SROIQD.Termination.StringLanguage

private def dotClass : PatternClass :=
  .neg (.union (.interval '\n' '\n') (.interval '\r' '\r'))

private theorem dotClass_iff (c : Char) :
    dotClass.accepts c = true ↔ (c == '\n' || c == '\r') = false := by
  have singleton (d : Char) :
      (PatternClass.interval d d).accepts c = (c == d) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
      exact beq_iff_eq.mpr (Char.le_antisymm (of_decide_eq_true hb) (of_decide_eq_true ha))
    · intro h
      obtain rfl := beq_iff_eq.mp h
      simp [PatternClass.accepts]
  change !((PatternClass.interval '\n' '\n').accepts c ||
    (PatternClass.interval '\r' '\r').accepts c) = true ↔ _
  rw [singleton, singleton]
  cases h : (c == '\n' || c == '\r') <;> simp

def regexTests : Regex → List PatternClass
  | .empty | .eps => []
  | .any => [dotClass]
  | .pred p => [p]
  | .seq a b | .alt a b => regexTests a ++ regexTests b
  | .star a => regexTests a

def constraintTests : Constraint → List PatternClass
  | .atom r => regexTests r
  | .and a b | .or a b => constraintTests a ++ constraintTests b
  | .not a => constraintTests a

def signature (ps : List PatternClass) (c : Char) : List Bool :=
  ps.map (·.accepts c)

private theorem test_eq_of_signature {ps : List PatternClass} {a b : Char}
    (h : signature ps a = signature ps b) {p : PatternClass} (hp : p ∈ ps) :
    p.accepts a = p.accepts b := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    obtain ⟨hhead, htail⟩ := List.cons.inj h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hhead
    · exact ih htail hp

private theorem split_word {α β : Type} (f : α → β) {u v w : List α}
    (h : w.map f = (u ++ v).map f) :
    (w.take u.length).map f = u.map f ∧ (w.drop u.length).map f = v.map f := by
  simp only [List.map_append] at h
  rw [List.map_take, List.map_drop, h]
  exact ⟨List.take_left' (List.length_map ..), List.drop_left' (List.length_map ..)⟩

private theorem regex_matches_of_signature (r : Regex) {ps : List PatternClass}
    (hp : regexTests r ⊆ ps) {u v : List Char}
    (he : u.map (signature ps) = v.map (signature ps)) (hu : r.Matches u) : r.Matches v := by
  induction r generalizing u v with
  | empty => contradiction
  | eps =>
    cases hu
    exact List.map_eq_nil_iff.mp he.symm
  | any =>
    obtain ⟨c, rfl, hc⟩ := hu
    cases v with
    | nil => cases he
    | cons d tail =>
      obtain ⟨h, hnil⟩ := List.cons.inj he
      have hnil := List.map_eq_nil_iff.mp hnil.symm
      subst tail
      have hd := test_eq_of_signature h (hp (List.mem_singleton_self dotClass))
      exact ⟨d, rfl, (dotClass_iff d).mp (hd ▸ (dotClass_iff c).mpr hc)⟩
  | pred p =>
    obtain ⟨c, rfl, hc⟩ := hu
    cases v with
    | nil => cases he
    | cons d tail =>
      obtain ⟨h, hnil⟩ := List.cons.inj he
      have hnil := List.map_eq_nil_iff.mp hnil.symm
      subst tail
      exact ⟨d, rfl, test_eq_of_signature h (hp (List.mem_singleton_self p)) ▸ hc⟩
  | alt a b ia ib =>
    rcases hu with ha | hb
    · exact .inl (ia (fun _ h => hp (List.mem_append_left _ h)) he ha)
    · exact .inr (ib (fun _ h => hp (List.mem_append_right _ h)) he hb)
  | seq a b ia ib =>
    obtain ⟨u, w, ha, hb, rfl⟩ := hu
    obtain ⟨hx, hy⟩ := split_word _ he.symm
    refine ⟨v.take u.length, v.drop u.length,
      ia (fun _ h => hp (List.mem_append_left _ h)) hx.symm ha,
      ib (fun _ h => hp (List.mem_append_right _ h)) hy.symm hb,
      (List.take_append_drop ..).symm⟩
  | star a ia =>
    change Repeats a.Matches u at hu
    induction hu generalizing v with
    | nil =>
      have hnil := List.map_eq_nil_iff.mp he.symm
      subst v
      exact .nil
    | @cons head tail hh _ ih =>
      obtain ⟨hx, hy⟩ := split_word _ he.symm
      have hx' := ia hp hx.symm hh
      have hy' := ih hy.symm
      change Repeats a.Matches v
      exact (List.take_append_drop head.length v) ▸ Repeats.cons hx' hy'

private theorem constraint_holds_iff (f : Constraint) {ps : List PatternClass}
    (hp : constraintTests f ⊆ ps) {u v : List Char}
    (he : u.map (signature ps) = v.map (signature ps)) : f.Holds u ↔ f.Holds v := by
  induction f with
  | atom r => exact ⟨regex_matches_of_signature r hp he, regex_matches_of_signature r hp he.symm⟩
  | and a b ia ib =>
    exact and_congr (ia fun _ h => hp (List.mem_append_left _ h))
      (ib fun _ h => hp (List.mem_append_right _ h))
  | or a b ia ib =>
    exact or_congr (ia fun _ h => hp (List.mem_append_left _ h))
      (ib fun _ h => hp (List.mem_append_right _ h))
  | not a ih => exact not_congr (ih hp)

/-! ### Exact code-point boundary partition for `PatternClass` -/

private def rangeCuts (rs : List (Nat × Nat)) : List Nat :=
  rs.flatMap fun (lo, hi) => [lo, hi]

private theorem inRanges_const_of_no_cut (rs : List (Nat × Nat)) {a b : Nat} (hle : a ≤ b)
    (hno : ∀ x ∈ rangeCuts rs, ¬ (a < x ∧ x ≤ b)) :
    XMLNames.inRanges rs a = XMLNames.inRanges rs b := by
  apply Bool.eq_iff_iff.mpr
  simp only [XMLNames.inRanges_iff]
  refine exists_congr fun r => and_congr_right fun hr => ?_
  have h1 : ¬ (a < r.1 ∧ r.1 ≤ b) := hno r.1 (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  have h2 : ¬ (a < r.2 ∧ r.2 ≤ b) := hno r.2 (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
  omega

private def classCuts : PatternClass → List Nat
  | .empty => []
  | .interval lo hi => [lo.toNat, hi.toNat + 1]
  | .ranges rs => rangeCuts rs
  | .space => [9, 11, 13, 14, 32, 33]
  | .word => [48, 58, 65, 91, 95, 96, 97, 123]
  | .nameStart => [58, 59, 65, 91, 95, 96, 97, 123] ++ rangeCuts XMLNames.highStarts
  | .nameChar => [45, 47, 48, 59, 65, 91, 95, 96, 97, 123] ++
      rangeCuts XMLNames.highStarts ++ rangeCuts XMLNames.highExtras
  | .union a b => classCuts a ++ classCuts b
  | .diff a b => classCuts a ++ classCuts b
  | .neg a => classCuts a
  | .lowerASCII a =>
    [65, 91] ++ classCuts a ++
      (classCuts a).filterMap fun x => if 97 ≤ x && x ≤ 123 then some (x - 32) else none

private theorem char_toNat_ofNat_valid {n : Nat}
    (hv : n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hvalid : Nat.isValidChar n := by
    change n < 0xD800 ∨ 0xDFFF < n ∧ n < 0x110000
    omega
  simp only [Char.ofNat, hvalid, ↓reduceDIte, Char.toNat, Char.ofNatAux]
  exact UInt32.toNat_ofNatLT

private theorem char_le_iff_toNat (a b : Char) : (a ≤ b) ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

private theorem char_beq_iff_toNat (a b : Char) : (a == b) = true ↔ a.toNat = b.toNat := by
  simp [beq_iff_eq, ← Char.toNat_inj]

private theorem isNameStartChar_split (c : Char) :
    isNameStartChar c = true ↔
      (c.toNat = 58 ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ c.toNat = 95 ∨
        (97 ≤ c.toNat ∧ c.toNat ≤ 122)) ∨
      XMLNames.inRanges XMLNames.highStarts c.toNat = true := by
  rw [isNameStartChar_iff]
  simp only [XMLNames.NameStartChar, XMLNames.inRanges_iff, XMLNames.highStarts,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  omega

private theorem isNameChar_split (c : Char) :
    isNameChar c = true ↔
      (c.toNat = 45 ∨ c.toNat = 46 ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨
        c.toNat = 58 ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ c.toNat = 95 ∨
        (97 ≤ c.toNat ∧ c.toNat ≤ 122)) ∨
      XMLNames.inRanges XMLNames.highStarts c.toNat = true ∨
      XMLNames.inRanges XMLNames.highExtras c.toNat = true := by
  rw [isNameChar_iff, XMLNames.NameChar, ← isNameStartChar_iff, isNameStartChar_split]
  by_cases hhs : XMLNames.inRanges XMLNames.highStarts c.toNat = true
  · simp [hhs]
  · simp [hhs, XMLNames.inRanges_iff, XMLNames.highExtras]
    omega

private theorem patternClass_const_of_no_cut (p : PatternClass) {a b : Char}
    (hle : a.toNat ≤ b.toNat) (hno : ∀ x ∈ classCuts p, ¬ (a.toNat < x ∧ x ≤ b.toNat)) :
    p.accepts a = p.accepts b := by
  induction p generalizing a b with
  | empty => rfl
  | interval lo hi =>
    have h1 := hno lo.toNat (by simp [classCuts])
    have h2 := hno (hi.toNat + 1) (by simp [classCuts])
    apply Bool.eq_iff_iff.mpr
    simp only [PatternClass.accepts, Bool.and_eq_true, decide_eq_true_eq, char_le_iff_toNat]
    omega
  | ranges rs =>
    exact inRanges_const_of_no_cut rs hle hno
  | space =>
    have h9 := hno 9 (by simp [classCuts])
    have h11 := hno 11 (by simp [classCuts])
    have h13 := hno 13 (by simp [classCuts])
    have h14 := hno 14 (by simp [classCuts])
    have h32 := hno 32 (by simp [classCuts])
    have h33 := hno 33 (by simp [classCuts])
    apply Bool.eq_iff_iff.mpr
    simp only [PatternClass.accepts, Bool.or_eq_true, char_beq_iff_toNat]
    have hs1 : ' '.toNat = 32 := rfl
    have hs2 : '\t'.toNat = 9 := rfl
    have hs3 : '\n'.toNat = 10 := rfl
    have hs4 : '\r'.toNat = 13 := rfl
    rw [hs1, hs2, hs3, hs4]
    omega
  | word =>
    have h48 := hno 48 (by simp [classCuts])
    have h58 := hno 58 (by simp [classCuts])
    have h65 := hno 65 (by simp [classCuts])
    have h91 := hno 91 (by simp [classCuts])
    have h95 := hno 95 (by simp [classCuts])
    have h96 := hno 96 (by simp [classCuts])
    have h97 := hno 97 (by simp [classCuts])
    have h123 := hno 123 (by simp [classCuts])
    apply Bool.eq_iff_iff.mpr
    simp only [PatternClass.accepts, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower,
      Char.isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      ge_iff_le, UInt32.le_iff_toNat_le, char_beq_iff_toNat]
    change (((65 ≤ a.toNat ∧ a.toNat ≤ 90) ∨ (97 ≤ a.toNat ∧ a.toNat ≤ 122)) ∨
        (48 ≤ a.toNat ∧ a.toNat ≤ 57)) ∨ a.toNat = 95 ↔
      (((65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122)) ∨
        (48 ≤ b.toNat ∧ b.toNat ≤ 57)) ∨ b.toNat = 95
    omega
  | nameStart =>
    have h58 := hno 58 (by simp [classCuts])
    have h59 := hno 59 (by simp [classCuts])
    have h65 := hno 65 (by simp [classCuts])
    have h91 := hno 91 (by simp [classCuts])
    have h95 := hno 95 (by simp [classCuts])
    have h96 := hno 96 (by simp [classCuts])
    have h97 := hno 97 (by simp [classCuts])
    have h123 := hno 123 (by simp [classCuts])
    have hhi := inRanges_const_of_no_cut XMLNames.highStarts hle fun x hx =>
      hno x (List.mem_append_right _ hx)
    apply Bool.eq_iff_iff.mpr
    simp only [PatternClass.accepts, isNameStartChar_split, hhi]
    have hlow : (a.toNat = 58 ∨ (65 ≤ a.toNat ∧ a.toNat ≤ 90) ∨ a.toNat = 95 ∨
        (97 ≤ a.toNat ∧ a.toNat ≤ 122)) ↔
      (b.toNat = 58 ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ b.toNat = 95 ∨
        (97 ≤ b.toNat ∧ b.toNat ≤ 122)) := by omega
    rw [hlow]
  | nameChar =>
    have h45 := hno 45 (by simp [classCuts])
    have h47 := hno 47 (by simp [classCuts])
    have h48 := hno 48 (by simp [classCuts])
    have h59 := hno 59 (by simp [classCuts])
    have h65 := hno 65 (by simp [classCuts])
    have h91 := hno 91 (by simp [classCuts])
    have h95 := hno 95 (by simp [classCuts])
    have h96 := hno 96 (by simp [classCuts])
    have h97 := hno 97 (by simp [classCuts])
    have h123 := hno 123 (by simp [classCuts])
    have hhs := inRanges_const_of_no_cut XMLNames.highStarts hle fun x hx =>
      hno x (List.mem_append_left _ (List.mem_append_right _ hx))
    have hhe := inRanges_const_of_no_cut XMLNames.highExtras hle fun x hx =>
      hno x (List.mem_append_right _ hx)
    apply Bool.eq_iff_iff.mpr
    simp only [PatternClass.accepts, isNameChar_split, hhs, hhe]
    have hlow : (a.toNat = 45 ∨ a.toNat = 46 ∨ (48 ≤ a.toNat ∧ a.toNat ≤ 57) ∨
        a.toNat = 58 ∨ (65 ≤ a.toNat ∧ a.toNat ≤ 90) ∨ a.toNat = 95 ∨
        (97 ≤ a.toNat ∧ a.toNat ≤ 122)) ↔
      (b.toNat = 45 ∨ b.toNat = 46 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
        b.toNat = 58 ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ b.toNat = 95 ∨
        (97 ≤ b.toNat ∧ b.toNat ≤ 122)) := by omega
    rw [hlow]
  | union p q ihp ihq =>
    simp only [PatternClass.accepts]
    rw [ihp hle fun x hx => hno x (List.mem_append_left _ hx),
        ihq hle fun x hx => hno x (List.mem_append_right _ hx)]
  | diff p q ihp ihq =>
    simp only [PatternClass.accepts]
    rw [ihp hle fun x hx => hno x (List.mem_append_left _ hx),
        ihq hle fun x hx => hno x (List.mem_append_right _ hx)]
  | neg p ih =>
    simp only [PatternClass.accepts, ih hle hno]
  | lowerASCII p ih =>
    simp only [PatternClass.accepts]
    have h65 := hno 65 (by simp [classCuts])
    have h91 := hno 91 (by simp [classCuts])
    have hnoP : ∀ x ∈ classCuts p, ¬ (a.toNat < x ∧ x ≤ b.toNat) := fun x hx =>
      hno x (List.mem_append_left _ (List.mem_append_right _ hx))
    have hnoShift : ∀ x ∈ classCuts p, 97 ≤ x → x ≤ 123 → ¬ (a.toNat < x - 32 ∧ x - 32 ≤ b.toNat) :=
      fun x hx h97 h123 =>
        hno (x - 32) (List.mem_append_right _ (List.mem_filterMap.mpr ⟨x, hx, by simp [h97, h123]⟩))
    by_cases hup : 65 ≤ a.toNat ∧ a.toNat ≤ 90
    · have hupB : 65 ≤ b.toNat ∧ b.toNat ≤ 90 := by omega
      have hta : (toLowerAscii a).toNat = a.toNat + 32 := by
        have hc : ('A' ≤ a && a ≤ 'Z') = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_iff_toNat]
          exact hup
        simp only [toLowerAscii, hc, ↓reduceIte]
        exact char_toNat_ofNat_valid (Or.inl (by omega))
      have htb : (toLowerAscii b).toNat = b.toNat + 32 := by
        have hc : ('A' ≤ b && b ≤ 'Z') = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_iff_toNat]
          exact hupB
        simp only [toLowerAscii, hc, ↓reduceIte]
        exact char_toNat_ofNat_valid (Or.inl (by omega))
      apply ih (by omega)
      intro x hx hbad
      rw [hta, htb] at hbad
      exact hnoShift x hx (by omega) (by omega) (by omega)
    · have hnotB : ¬ (65 ≤ b.toNat ∧ b.toNat ≤ 90) := by omega
      have hta : toLowerAscii a = a := by
        have hc : ('A' ≤ a && a ≤ 'Z') = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_iff_toNat] at h
          exact hup h
        simp [toLowerAscii, hc]
      have htb : toLowerAscii b = b := by
        have hc : ('A' ≤ b && b ≤ 'Z') = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_iff_toNat] at h
          exact hnotB h
        simp [toLowerAscii, hc]
      rw [hta, htb]
      exact ih hle hnoP

private theorem signature_const_of_no_cut (ps : List PatternClass) {a b : Char}
    (hle : a.toNat ≤ b.toNat)
    (hno : ∀ x ∈ ps.flatMap classCuts, ¬ (a.toNat < x ∧ x ≤ b.toNat)) :
    signature ps a = signature ps b := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [signature, List.map_cons, List.cons.injEq]
    refine ⟨patternClass_const_of_no_cut p hle fun x hx =>
      hno x (List.mem_flatMap.mpr ⟨p, List.mem_cons_self .., hx⟩), ?_⟩
    exact ih fun x hx => by
      obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hx
      exact hno x (List.mem_flatMap.mpr ⟨q, List.mem_cons_of_mem _ hq, hxq⟩)

private def insertNatSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x == y then y :: ys
    else y :: insertNatSorted x ys

private def sortNatDedup : List Nat → List Nat
  | [] => []
  | x :: xs => insertNatSorted x (sortNatDedup xs)

private def isStrictSorted : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ isStrictSorted (b :: rest)

private theorem mem_insertNatSorted (x y : Nat) (xs : List Nat) :
    y ∈ insertNatSorted x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertNatSorted]
  | cons z zs ih =>
    unfold insertNatSorted
    split
    · simp
    · split
      · rename_i hlt heq
        have hx := beq_iff_eq.mp heq
        subst hx
        simp
      · simp [ih, or_left_comm]

private theorem isStrictSorted_insertNatSorted (x : Nat) {xs : List Nat}
    (hs : isStrictSorted xs) : isStrictSorted (insertNatSorted x xs) := by
  induction xs with
  | nil => trivial
  | cons z zs ih =>
    unfold insertNatSorted
    split
    · rename_i hlt
      exact ⟨hlt, hs⟩
    · split
      · exact hs
      · rename_i hge hne
        have hltz : z < x := by
          have : x ≠ z := fun h => hne (beq_iff_eq.mpr h)
          omega
        cases zs with
        | nil => exact ⟨hltz, trivial⟩
        | cons w ws =>
          obtain ⟨hzw, hws⟩ := hs
          have ih' := ih hws
          unfold insertNatSorted at ih' ⊢
          by_cases hxw : x < w
          · simp only [hxw, ↓reduceIte] at ih' ⊢
            exact ⟨hltz, ih'⟩
          · simp only [hxw, ↓reduceIte] at ih' ⊢
            by_cases hxe : (x == w) = true
            · simp only [hxe, ↓reduceIte] at ih' ⊢
              exact ⟨hzw, hws⟩
            · simp only [hxe] at ih' ⊢
              exact ⟨hzw, ih'⟩

private theorem mem_sortNatDedup (xs : List Nat) (y : Nat) :
    y ∈ sortNatDedup xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp [sortNatDedup]
  | cons z zs ih =>
    simp [sortNatDedup, mem_insertNatSorted, ih]

private theorem isStrictSorted_sortNatDedup (xs : List Nat) :
    isStrictSorted (sortNatDedup xs) := by
  induction xs with
  | nil => trivial
  | cons z zs ih => exact isStrictSorted_insertNatSorted z ih

private def adjacentPairs : List Nat → List (Nat × Nat)
  | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)
  | _ => []

private theorem isStrictSorted_head_le {u : Nat} {us : List Nat}
    (hs : isStrictSorted (u :: us)) : ∀ z ∈ u :: us, u ≤ z := by
  induction us generalizing u with
  | nil => intro z hz; rw [List.mem_singleton] at hz; omega
  | cons v vs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hzv
    · exact Nat.le_refl _
    · have := ih hs.2 z hzv
      have := hs.1
      omega

private theorem isStrictSorted_adj_le {u : Nat} {us : List Nat}
    (hs : isStrictSorted (u :: us)) : ∀ p ∈ adjacentPairs (u :: us), u ≤ p.1 := by
  induction us generalizing u with
  | nil => intro _ hp; cases hp
  | cons v vs ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hpt
    · exact Nat.le_refl _
    · have := ih hs.2 p hpt
      have := hs.1
      omega

private theorem adjacentPairs_lt {xs : List Nat} (hs : isStrictSorted xs)
    {lo hi : Nat} (h : (lo, hi) ∈ adjacentPairs xs) :
    lo < hi ∧ ∀ x ∈ xs, ¬ (lo < x ∧ x < hi) := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    cases rest with
    | nil => cases h
    | cons b tail =>
      obtain ⟨hab, htail⟩ := hs
      rcases List.mem_cons.mp h with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        refine ⟨hab, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · have := isStrictSorted_head_le htail x hx'
          omega
      · obtain ⟨hlt, hno⟩ := ih htail hmem
        have hle_b : b ≤ lo := isStrictSorted_adj_le htail (lo, hi) hmem
        refine ⟨hlt, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hno x hx'

private theorem exists_adjacentPair {xs : List Nat} (hs : isStrictSorted xs)
    {n : Nat} {a b : Nat} (ha : a ∈ xs) (hb : b ∈ xs) (hlo : a ≤ n) (hhi : n < b) :
    ∃ p ∈ adjacentPairs xs, p.1 ≤ n ∧ n < p.2 := by
  induction xs generalizing a with
  | nil => cases ha
  | cons u rest ih =>
    cases rest with
    | nil =>
      rw [List.mem_singleton] at ha hb
      subst ha; subst hb; omega
    | cons v tail =>
      obtain ⟨huv, htail⟩ := hs
      by_cases hltv : n < v
      · have hle : u ≤ n := by
          rcases List.mem_cons.mp ha with rfl | hav
          · exact hlo
          · have := isStrictSorted_head_le htail a hav
            omega
        exact ⟨(u, v), List.mem_cons_self .., hle, hltv⟩
      · have hbv : b ∈ v :: tail := by
          rcases List.mem_cons.mp hb with rfl | hbt
          · omega
          · exact hbt
        obtain ⟨p, hp, hp1, hp2⟩ := ih htail (List.mem_cons_self ..) hbv (by omega)
        exact ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩

private def sortedCuts (ps : List PatternClass) : List Nat :=
  sortNatDedup (([0, 0xD800, 0xE000, 0x110000] ++ ps.flatMap classCuts).filter (· ≤ 0x110000))

private def validIntervals (ps : List PatternClass) : List (Nat × Nat) :=
  (adjacentPairs (sortedCuts ps)).filter fun (lo, _) => lo < 0xD800 || 0xE000 ≤ lo

private theorem validInterval_spec (ps : List PatternClass) {lo hi : Nat}
    (h : (lo, hi) ∈ validIntervals ps) :
    lo < hi ∧
    (∀ n, lo ≤ n → n < hi → (n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x110000))) ∧
    (∀ n, lo ≤ n → n < hi → signature ps (Char.ofNat n) = signature ps (Char.ofNat lo)) := by
  obtain ⟨hpair, hok⟩ := List.mem_filter.mp h
  have hss : isStrictSorted (sortedCuts ps) := isStrictSorted_sortNatDedup _
  obtain ⟨hlt, hno⟩ := adjacentPairs_lt hss hpair
  have hd8 : 0xD800 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have he0 : 0xE000 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have hmax : 0x110000 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have hhiLe : hi ≤ 0x110000 := by
    have hmemHi : hi ∈ sortedCuts ps := by
      have aux : ∀ (l : List Nat) (p : Nat × Nat), p ∈ adjacentPairs l → p.2 ∈ l := by
        intro l
        induction l with
        | nil => intro _ hp; cases hp
        | cons u us ih =>
          cases us with
          | nil => intro _ hp; cases hp
          | cons v vs =>
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hpt
            · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
            · exact List.mem_cons_of_mem _ (ih p hpt)
      exact aux _ (lo, hi) hpair
    exact of_decide_eq_true (List.mem_filter.mp ((mem_sortNatDedup _ _).mp hmemHi)).2
  have hnoD8 := hno 0xD800 hd8
  have hnoE0 := hno 0xE000 he0
  have hvalid : ∀ n, lo ≤ n → n < hi → n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x110000) := by
    intro n h1 h2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    omega
  refine ⟨hlt, hvalid, fun n h1 h2 => ?_⟩
  have hloV := char_toNat_ofNat_valid (hvalid lo (Nat.le_refl _) hlt)
  have hnV := char_toNat_ofNat_valid (hvalid n h1 h2)
  refine (signature_const_of_no_cut ps (by omega) fun x hx hbad => ?_).symm
  rw [hloV, hnV] at hbad
  have hxLe : x ≤ 0x110000 := by omega
  have hxMem : x ∈ sortedCuts ps :=
    (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨List.mem_append_right _ hx, decide_eq_true hxLe⟩)
  exact hno x hxMem (by omega)

private theorem exists_validInterval (ps : List PatternClass) (c : Char) :
    ∃ p ∈ validIntervals ps, p.1 ≤ c.toNat ∧ c.toNat < p.2 := by
  have hss : isStrictSorted (sortedCuts ps) := isStrictSorted_sortNatDedup _
  have h0 : 0 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have hmax : 0x110000 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have hcV : c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat < 0x110000) := by
    have hv := c.valid
    unfold UInt32.isValidChar at hv
    change c.toNat < 0xD800 ∨ 0xDFFF < c.toNat ∧ c.toNat < 0x110000 at hv
    omega
  have hltMax : c.toNat < 0x110000 := by omega
  obtain ⟨⟨lo, hi⟩, hpair, hlo, hhi⟩ := exists_adjacentPair hss h0 hmax (Nat.zero_le _) hltMax
  obtain ⟨hlt, hno⟩ := adjacentPairs_lt hss hpair
  have hd8 : 0xD800 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have he0 : 0xE000 ∈ sortedCuts ps := (mem_sortNatDedup _ _).mpr (List.mem_filter.mpr ⟨by simp, by decide⟩)
  have hnoD8 := hno 0xD800 hd8
  have hnoE0 := hno 0xE000 he0
  refine ⟨(lo, hi), List.mem_filter.mpr ⟨hpair, ?_⟩, hlo, hhi⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

private def intervalChars (K : Nat) (lo hi : Nat) : List Char :=
  (List.range (min K (hi - lo))).map fun j => Char.ofNat (lo + j)

private def rawCandidates (K : Nat) (ps : List PatternClass) : List Char :=
  ((validIntervals ps).flatMap fun (lo, hi) => intervalChars K lo hi).eraseDups

private abbrev Buckets := List (List Bool × List Char)

private def prependBucket (K : Nat) (key : List Bool) (c : Char) : Buckets → Buckets
  | [] => [(key, [c].take K)]
  | (k, xs) :: rest =>
    if k == key then (k, (c :: xs).take K) :: rest
    else (k, xs) :: prependBucket K key c rest

private theorem lookup_prependBucket (K : Nat) (key other : List Bool) (c : Char)
    (bs : Buckets) :
    ((prependBucket K key c bs).lookup other).getD [] =
    if other = key then (c :: (bs.lookup other).getD []).take K
    else (bs.lookup other).getD [] := by
  induction bs with
  | nil => by_cases he : other = key <;> simp [prependBucket, List.lookup_cons, beq_false_of_ne, he]
  | cons entry bs ih =>
    rcases entry with ⟨k, xs⟩
    by_cases hk : k = key
    · subst k
      by_cases ho : other = key <;>
        simp [prependBucket, List.lookup_cons, beq_false_of_ne, ho]
    · by_cases ho : other = k
      · subst other
        simp [prependBucket, beq_false_of_ne, hk]
      · simp [prependBucket, List.lookup_cons, beq_false_of_ne, ho, hk, ih]

private theorem take_cons_take {α : Type} (K : Nat) (x : α) (xs : List α) :
    (x :: xs.take K).take K = (x :: xs).take K := by
  cases K with
  | zero => rfl
  | succ K => simp [List.take_take, Nat.min_eq_left (Nat.le_succ _)]

private def table (K : Nat) (ps : List PatternClass) (xs : List Char) : Buckets :=
  xs.foldr (fun c => prependBucket K (signature ps c) c) []

private theorem lookup_table (K : Nat) (ps : List PatternClass) (key : List Bool) (cs : List Char) :
    (((table K ps cs).lookup key).getD []) = (cs.filter fun c => signature ps c == key).take K := by
  induction cs with
  | nil => simp [table]
  | cons c cs ih =>
    rw [table, List.foldr_cons, lookup_prependBucket]
    change (if key = signature ps c then (c :: ((table K ps cs).lookup key).getD []).take K
      else ((table K ps cs).lookup key).getD []) = _
    rw [ih]
    by_cases he : key = signature ps c
    · simp [he, take_cons_take]
    · simp [he, beq_false_of_ne (Ne.symm he)]

private theorem mem_lookup_buckets {table : Buckets} {key : List Bool} {x : Char}
    (hx : x ∈ (table.lookup key).getD []) : x ∈ table.flatMap Prod.snd := by
  induction table with
  | nil => cases hx
  | cons a as ih =>
    rcases a with ⟨k, xs⟩
    by_cases h : key = k
    · subst k
      exact List.mem_append_left _ (by simpa using hx)
    · apply List.mem_append_right
      exact ih (by simpa [List.lookup_cons, beq_false_of_ne h] using hx)

private def bucket (K : Nat) (ps : List PatternClass) (key : List Bool) : List Char :=
  ((rawCandidates K ps).filter fun c => signature ps c == key).take K

def alphabet (K : Nat) (ps : List PatternClass) : List Char :=
  (table K ps (rawCandidates K ps)).flatMap Prod.snd

private theorem bucket_mem_alphabet (K : Nat) (ps : List PatternClass) (c : Char) :
    ∀ x ∈ bucket K ps (signature ps c), x ∈ alphabet K ps := by
  intro x hx
  apply mem_lookup_buckets (key := signature ps c)
  rwa [lookup_table]

private theorem bucket_key {K : Nat} {ps : List PatternClass} {key : List Bool}
    {c : Char} (hc : c ∈ bucket K ps key) : signature ps c = key :=
  beq_iff_eq.mp (List.mem_filter.mp (List.mem_of_mem_take hc)).2

private theorem bucket_nodup (K : Nat) (ps : List PatternClass) (key : List Bool) :
    (bucket K ps key).Nodup :=
  (List.take_sublist ..).nodup (List.filter_sublist.nodup (nodup_eraseDups_list _))

private theorem bucket_full_of_missing {K : Nat} {ps : List PatternClass} {c : Char}
    (hc : c ∉ alphabet K ps) : (bucket K ps (signature ps c)).length = K := by
  obtain ⟨⟨lo, hi⟩, hiv, hlo, hhi⟩ := exists_validInterval ps c
  obtain ⟨hlt, hval, hsig⟩ := validInterval_spec ps hiv
  have hsigC : signature ps c = signature ps (Char.ofNat lo) := by
    have := hsig c.toNat hlo hhi
    simpa [Char.ofNat_toNat] using this
  have hsub : ∀ x ∈ intervalChars K lo hi,
      x ∈ (rawCandidates K ps).filter (fun y => signature ps y == signature ps c) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjlt := List.mem_range.mp hj
    have hmemRaw : Char.ofNat (lo + j) ∈ rawCandidates K ps :=
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(lo, hi), hiv, List.mem_map.mpr ⟨j, hj, rfl⟩⟩)
    refine List.mem_filter.mpr ⟨hmemRaw, beq_iff_eq.mpr ?_⟩
    rw [hsig (lo + j) (by omega) (by omega), hsigC]
  have hndIv : (intervalChars K lo hi).Nodup := by
    unfold intervalChars
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply List.nodup_range.imp_of_mem
    intro j₁ j₂ h1 h2 hne heq
    have h1' := List.mem_range.mp h1
    have h2' := List.mem_range.mp h2
    have ht := congrArg Char.toNat heq
    rw [char_toNat_ofNat_valid (hval (lo + j₁) (by omega) (by omega)),
        char_toNat_ofNat_valid (hval (lo + j₂) (by omega) (by omega))] at ht
    omega
  have hlenGe : min K (hi - lo) ≤
      ((rawCandidates K ps).filter (fun y => signature ps y == signature ps c)).length := by
    have := hndIv.length_le_of_subset hsub
    simpa [intervalChars] using this
  have hlenK : K ≤ ((rawCandidates K ps).filter (fun y => signature ps y == signature ps c)).length := by
    apply Classical.byContradiction
    intro hltK
    have hdiff : hi - lo < K := by omega
    have hjlt : c.toNat - lo < min K (hi - lo) := by omega
    have hcIv : c ∈ intervalChars K lo hi := by
      refine List.mem_map.mpr ⟨c.toNat - lo, List.mem_range.mpr hjlt, ?_⟩
      have : lo + (c.toNat - lo) = c.toNat := by omega
      rw [this, Char.ofNat_toNat]
    have hcFilt := hsub c hcIv
    apply hc
    apply bucket_mem_alphabet K ps c c
    unfold bucket
    rw [List.take_of_length_le (by omega)]
    exact hcFilt
  simp [bucket, List.length_take, hlenK]

private def representative (K : Nat) (ps : List PatternClass) (c : Char) : Char :=
  (bucket K ps (signature ps c)).headD c

private theorem representative_mem {K : Nat} (hK : 0 < K) (ps : List PatternClass)
    (c : Char) : representative K ps c ∈ bucket K ps (signature ps c) := by
  obtain ⟨⟨lo, hi⟩, hiv, hlo, hhi⟩ := exists_validInterval ps c
  obtain ⟨hlt, _, hsig⟩ := validInterval_spec ps hiv
  have hsigC : signature ps c = signature ps (Char.ofNat lo) := by
    have := hsig c.toNat hlo hhi
    simpa [Char.ofNat_toNat] using this
  have hloMem : Char.ofNat lo ∈ (rawCandidates K ps).filter (fun y => signature ps y == signature ps c) := by
    have h0 : 0 < min K (hi - lo) := by omega
    have hmemRaw : Char.ofNat lo ∈ rawCandidates K ps :=
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(lo, hi), hiv,
        List.mem_map.mpr ⟨0, List.mem_range.mpr h0, by simp⟩⟩)
    exact List.mem_filter.mpr ⟨hmemRaw, beq_iff_eq.mpr hsigC.symm⟩
  have hn : bucket K ps (signature ps c) ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    have hl : 0 < ((rawCandidates K ps).filter (fun x => signature ps x == signature ps c)).length :=
      List.length_pos_iff.mpr (fun h => by rw [h] at hloMem; cases hloMem)
    change (bucket K ps (signature ps c)).length = 0 at hlen
    simp only [bucket, List.length_take] at hlen
    omega
  unfold representative
  generalize bucket K ps (signature ps c) = xs at *
  cases xs <;> simp_all

private theorem mapped_signature (K : Nat) (hK : 0 < K) (ps : List PatternClass)
    (w : List Char) :
    (w.map (representative K ps)).map (signature ps) = w.map (signature ps) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, ih, bucket_key (representative_mem hK ps c)]

def sample (f : Constraint) (K : Nat) : List (List Char) :=
  f.sample (alphabet K (constraintTests f)) K

theorem sample_exact (f : Constraint) (K : Nat) :
    (sample f K).Nodup ∧ (sample f K).length ≤ K ∧
      (∀ w ∈ sample f K, f.Holds w) ∧
      ((sample f K).length < K → ∀ w, f.Holds w → w ∈ sample f K) := by
  let ps := constraintTests f
  obtain ⟨hnd, hcap, hsound, hcomplete⟩ := f.sample_exact (alphabet K ps) K
  refine ⟨hnd, hcap, fun w hw => (hsound w hw).1, ?_⟩
  intro hshort w hw
  have hK : 0 < K := Nat.zero_lt_of_lt hshort
  apply hcomplete hshort w hw
  intro c hc
  apply Classical.byContradiction
  intro hbad
  obtain ⟨u, v, rfl, _⟩ := List.eq_append_cons_of_mem hc
  let form (x : Char) := u.map (representative K ps) ++ x :: v.map (representative K ps)
  let ws := (bucket K ps (signature ps c)).map form
  have hndw : ws.Nodup :=
    (bucket_nodup K ps (signature ps c)).map form
      (fun _ _ hn he => hn (List.cons.inj (List.append_cancel_left he)).1)
  have hsub (v') (hv' : v' ∈ ws) : v' ∈ sample f K := by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv'
    have he : (form x).map (signature ps) = (u ++ c :: v).map (signature ps) := by
      simp only [form, List.map_append, List.map_cons, mapped_signature K hK ps, bucket_key hx]
    refine hcomplete hshort _ ((constraint_holds_iff f (fun _ h => h) he).mpr hw) ?_
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
      exact bucket_mem_alphabet K ps a _ (representative_mem hK ps a)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact bucket_mem_alphabet K ps c _ hx
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
        exact bucket_mem_alphabet K ps a _ (representative_mem hK ps a)
  have hlen := hndw.length_le_of_subset hsub
  simp only [ws, List.length_map, bucket_full_of_missing hbad] at hlen
  omega

#print axioms sample_exact

end Sabrina.OWL2.SROIQD.Termination.UnicodeStringSampling
