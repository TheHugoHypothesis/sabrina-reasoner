import Sabrina.OWL2.Datatypes.PatternAutomata

/-! Independent W3C XSD 1.1 Part 2 Appendix G Regular Expression BNF Grammar,
    Denotational Semantics, and Correspondence Proofs (Milestone C.2.3).

Defines an independent inductive AST mirroring W3C XSD 1.1 Appendix G:
- `GrammarRegExp` (`branch` alternation)
- `GrammarBranch` (`piece` concatenation)
- `GrammarPiece` (`atom` with `GrammarQuantifier`: `?`, `*`, `+`, `{n}`, `{n,}`, `{n,m}`)
- `GrammarAtom` (normal char, `.`, escapes `\d`/`\D`/`\w`/`\W`/`\s`/`\S`/`\i`/`\I`/`\c`/`\C`,
  `\p{...}`/`\P{...}`, character-class expressions `[...]` / `[^...]` / `[base-[sub]]`,
  parenthesized sub-expressions)

Proves `compile_matches_iff`: the language recognized by SABRINA's compiled
`Regex` / Brzozowski matcher / partial-derivative automaton is **identical** over
all Unicode scalar words (`List Char`) to the independent W3C BNF denotational
semantics `GrammarRegExp.Denotes`. -/

namespace Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence

open Sabrina.OWL2.Datatypes

/-! ### 1. Independent W3C XSD 1.1 Appendix G BNF Grammar AST -/

inductive GrammarEscape where
  | single (c : Char)
  | nameStart | notNameStart
  | nameChar | notNameChar
  | digit | notDigit
  | word | notWord
  | space | notSpace
  | category (name : String) (ranges : List (Nat × Nat))
  | complCategory (name : String) (ranges : List (Nat × Nat))
  deriving DecidableEq

inductive GrammarCharClassItem where
  | char (c : Char)
  | range (lo hi : Char) (hle : lo ≤ hi)
  | esc (e : GrammarEscape)

inductive GrammarCharClass where
  | group (neg : Bool) (items : List GrammarCharClassItem)
  | subtract (base sub : GrammarCharClass)

inductive GrammarQuantifier where
  | one
  | opt
  | star
  | plus
  | exact (n : Nat)
  | atLeast (n : Nat)
  | bounded (n m : Nat) (hle : n ≤ m)
  deriving DecidableEq

mutual
  inductive GrammarAtom where
    | normal (c : Char)
    | dot
    | esc (e : GrammarEscape)
    | charClass (cc : GrammarCharClass)
    | group (re : GrammarRegExp)

  inductive GrammarPiece where
    | mk (atom : GrammarAtom) (q : GrammarQuantifier)

  inductive GrammarBranch where
    | nil
    | cons (hd : GrammarPiece) (tl : GrammarBranch)

  inductive GrammarRegExp where
    | single (b : GrammarBranch)
    | alt (b : GrammarBranch) (rest : GrammarRegExp)
end

/-! ### 2. Independent Denotational Semantics Over All Unicode Scalar Words -/

def GrammarEscape.Accepts : GrammarEscape → Char → Prop
  | .single ch, c => c = ch
  | .nameStart, c => XMLNames.NameStartChar c
  | .notNameStart, c => ¬ XMLNames.NameStartChar c
  | .nameChar, c => XMLNames.NameChar c
  | .notNameChar, c => ¬ XMLNames.NameChar c
  | .digit, c => XMLNames.inRanges UnicodeCategories.catNd c.toNat = true
  | .notDigit, c => XMLNames.inRanges UnicodeCategories.catNd c.toNat = false
  | .word, c => XMLNames.inRanges UnicodeCategories.xsdWordRanges c.toNat = true
  | .notWord, c => XMLNames.inRanges UnicodeCategories.xsdWordRanges c.toNat = false
  | .space, c => c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'
  | .notSpace, c => ¬ (c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r')
  | .category _ rs, c => XMLNames.inRanges rs c.toNat = true
  | .complCategory _ rs, c => XMLNames.inRanges rs c.toNat = false

def GrammarCharClassItem.Accepts : GrammarCharClassItem → Char → Prop
  | .char ch, c => c = ch
  | .range lo hi _, c => lo ≤ c ∧ c ≤ hi
  | .esc e, c => e.Accepts c

def GrammarCharClass.Accepts : GrammarCharClass → Char → Prop
  | .group false items, c => ∃ it ∈ items, it.Accepts c
  | .group true items, c => ¬ ∃ it ∈ items, it.Accepts c
  | .subtract base sub, c => base.Accepts c ∧ ¬ sub.Accepts c

/-- Exact `n`-fold language concatenation `L^n`. -/
inductive RepeatExact (L : Word → Prop) : Nat → Word → Prop where
  | zero : RepeatExact L 0 []
  | succ {n u v} : L u → RepeatExact L n v → RepeatExact L (n + 1) (u ++ v)

/-- Bounded `0..k`-fold language concatenation `L^{≤k}`. -/
def RepeatUpTo (L : Word → Prop) (k : Nat) (w : Word) : Prop :=
  ∃ j ≤ k, RepeatExact L j w

def GrammarQuantifier.Apply (q : GrammarQuantifier) (L : Word → Prop) (w : Word) : Prop :=
  match q with
  | .one => L w
  | .opt => w = [] ∨ L w
  | .star => Repeats L w
  | .plus => ∃ u v, L u ∧ Repeats L v ∧ w = u ++ v
  | .exact n => RepeatExact L n w
  | .atLeast n => ∃ u v, RepeatExact L n u ∧ Repeats L v ∧ w = u ++ v
  | .bounded n m _ => ∃ u v, RepeatExact L n u ∧ RepeatUpTo L (m - n) v ∧ w = u ++ v

mutual
  def GrammarAtom.Denotes : GrammarAtom → Word → Prop
    | .normal ch, w => w = [ch]
    | .dot, w => ∃ c, w = [c] ∧ c ≠ '\n' ∧ c ≠ '\r'
    | .esc e, w => ∃ c, w = [c] ∧ e.Accepts c
    | .charClass cc, w => ∃ c, w = [c] ∧ cc.Accepts c
    | .group re, w => re.Denotes w

  def GrammarPiece.Denotes : GrammarPiece → Word → Prop
    | .mk a q, w => q.Apply a.Denotes w

  def GrammarBranch.Denotes : GrammarBranch → Word → Prop
    | .nil, w => w = []
    | .cons hd tl, w => ∃ u v, hd.Denotes u ∧ tl.Denotes v ∧ w = u ++ v

  def GrammarRegExp.Denotes : GrammarRegExp → Word → Prop
    | .single b, w => b.Denotes w
    | .alt b rest, w => b.Denotes w ∨ rest.Denotes w
end

/-! ### 3. Compilation to SABRINA's `PatternClass` / `Regex` & Exact Equivalence Proof -/

def GrammarEscape.compile : GrammarEscape → PatternClass
  | .single c => .interval c c
  | .nameStart => .nameStart
  | .notNameStart => .neg .nameStart
  | .nameChar => .nameChar
  | .notNameChar => .neg .nameChar
  | .digit => .ranges UnicodeCategories.catNd
  | .notDigit => .neg (.ranges UnicodeCategories.catNd)
  | .word => .ranges UnicodeCategories.xsdWordRanges
  | .notWord => .neg (.ranges UnicodeCategories.xsdWordRanges)
  | .space => .space
  | .notSpace => .neg .space
  | .category _ rs => .ranges rs
  | .complCategory _ rs => .neg (.ranges rs)

def GrammarCharClassItem.compile : GrammarCharClassItem → PatternClass
  | .char c => .interval c c
  | .range lo hi _ => .interval lo hi
  | .esc e => e.compile

def compileItems : List GrammarCharClassItem → PatternClass
  | [] => .empty
  | it :: rest => .union (compileItems rest) it.compile

def GrammarCharClass.compile : GrammarCharClass → PatternClass
  | .group false items => compileItems items
  | .group true items => .neg (compileItems items)
  | .subtract base sub => .diff base.compile sub.compile

private def compileRepeat (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => .seq r (compileRepeat r n)

private def compileUpTo (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => .alt .eps (.seq r (compileUpTo r n))

def GrammarQuantifier.compile (q : GrammarQuantifier) (r : Regex) : Regex :=
  match q with
  | .one => r
  | .opt => .alt .eps r
  | .star => .star r
  | .plus => .seq r (.star r)
  | .exact n => compileRepeat r n
  | .atLeast n => .seq (compileRepeat r n) (.star r)
  | .bounded n m _ => .seq (compileRepeat r n) (compileUpTo r (m - n))

mutual
  def GrammarAtom.compile : GrammarAtom → Regex
    | .normal c => .pred (.interval c c)
    | .dot => .any
    | .esc e => .pred e.compile
    | .charClass cc => .pred cc.compile
    | .group re => re.compile

  def GrammarPiece.compile : GrammarPiece → Regex
    | .mk a q => q.compile a.compile

  def GrammarBranch.compile : GrammarBranch → Regex
    | .nil => .eps
    | .cons hd tl => .seq hd.compile tl.compile

  def GrammarRegExp.compile : GrammarRegExp → Regex
    | .single b => b.compile
    | .alt b rest => .alt b.compile rest.compile
end

theorem GrammarEscape.compile_iff (e : GrammarEscape) (c : Char) :
    e.compile.accepts c = true ↔ e.Accepts c := by
  cases e with
  | single ch =>
    simp only [compile, Accepts, PatternClass.accepts, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩
  | nameStart => simpa [compile, Accepts, PatternClass.accepts] using isNameStartChar_iff c
  | notNameStart =>
    simp [compile, Accepts, PatternClass.accepts, ← isNameStartChar_iff]
  | nameChar => simpa [compile, Accepts, PatternClass.accepts] using isNameChar_iff c
  | notNameChar =>
    simp [compile, Accepts, PatternClass.accepts, ← isNameChar_iff]
  | digit | notDigit | word | notWord | category _ _ | complCategory _ _ =>
    simp [compile, Accepts, PatternClass.accepts]
  | space =>
    simp [compile, Accepts, PatternClass.accepts, or_assoc]
  | notSpace =>
    simp [compile, Accepts, PatternClass.accepts, and_assoc]

theorem GrammarCharClassItem.compile_iff (it : GrammarCharClassItem) (c : Char) :
    it.compile.accepts c = true ↔ it.Accepts c := by
  cases it with
  | char ch =>
    simp only [compile, Accepts, PatternClass.accepts, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩
  | range lo hi _ =>
    simp [compile, Accepts, PatternClass.accepts]
  | esc e => exact e.compile_iff c

private theorem compileItems_iff (items : List GrammarCharClassItem) (c : Char) :
    (compileItems items).accepts c = true ↔ ∃ it ∈ items, it.Accepts c := by
  induction items with
  | nil => simp [compileItems, PatternClass.accepts]
  | cons it rest ih =>
    simp only [compileItems, PatternClass.accepts, Bool.or_eq_true, ih,
      GrammarCharClassItem.compile_iff, List.mem_cons, exists_eq_or_imp, or_comm]

theorem GrammarCharClass.compile_iff (cc : GrammarCharClass) (c : Char) :
    cc.compile.accepts c = true ↔ cc.Accepts c := by
  induction cc with
  | group neg items =>
    cases neg with
    | false => exact compileItems_iff items c
    | true =>
      simp only [compile, Accepts, PatternClass.accepts, Bool.not_eq_true',
        Bool.eq_false_iff, ← compileItems_iff]
  | subtract base sub ihb ihs =>
    simp only [compile, Accepts, PatternClass.accepts, Bool.and_eq_true,
      Bool.not_eq_true', Bool.eq_false_iff]
    exact and_congr ihb (not_congr ihs)

private theorem compileRepeat_iff (r : Regex) (n : Nat) (w : Word) :
    (compileRepeat r n).Matches w ↔ RepeatExact r.Matches n w := by
  induction n generalizing w with
  | zero =>
    simp only [compileRepeat, Regex.Matches]
    constructor
    · rintro rfl; exact .zero
    · intro h; cases h; rfl
  | succ n ih =>
    simp only [compileRepeat, Regex.Matches]
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact .succ hu ((ih v).mp hv)
    · intro h
      cases h with
      | succ hu hv => exact ⟨_, _, hu, (ih _).mpr hv, rfl⟩

private theorem compileUpTo_iff (r : Regex) (k : Nat) (w : Word) :
    (compileUpTo r k).Matches w ↔ RepeatUpTo r.Matches k w := by
  induction k generalizing w with
  | zero =>
    simp only [compileUpTo, Regex.Matches, RepeatUpTo]
    constructor
    · rintro rfl; exact ⟨0, Nat.le_refl 0, .zero⟩
    · rintro ⟨j, hj, hrep⟩
      have hj0 : j = 0 := by omega
      subst hj0; cases hrep; rfl
  | succ k ih =>
    simp only [compileUpTo, Regex.Matches, RepeatUpTo]
    constructor
    · rintro (rfl | ⟨u, v, hu, hv, rfl⟩)
      · exact ⟨0, Nat.zero_le _, .zero⟩
      · obtain ⟨j, hj, hrep⟩ := (ih v).mp hv
        exact ⟨j + 1, by omega, .succ hu hrep⟩
    · rintro ⟨j, hj, hrep⟩
      cases hrep with
      | zero => exact .inl rfl
      | @succ j' u v hu hv =>
        exact .inr ⟨u, v, hu, (ih v).mpr ⟨j', by omega, hv⟩, rfl⟩

private theorem repeatExact_congr {L1 L2 : Word → Prop} (h : ∀ w, L1 w ↔ L2 w) (n : Nat) (w : Word) :
    RepeatExact L1 n w ↔ RepeatExact L2 n w := by
  constructor <;> intro hr
  · induction hr with
    | zero => exact .zero
    | succ hu _ ih => exact .succ ((h _).mp hu) ih
  · induction hr with
    | zero => exact .zero
    | succ hu _ ih => exact .succ ((h _).mpr hu) ih

private theorem repeats_congr {L1 L2 : Word → Prop} (h : ∀ w, L1 w ↔ L2 w) (w : Word) :
    Repeats L1 w ↔ Repeats L2 w := by
  constructor <;> intro hr
  · induction hr with
    | nil => exact .nil
    | cons hu _ ih => exact .cons ((h _).mp hu) ih
  · induction hr with
    | nil => exact .nil
    | cons hu _ ih => exact .cons ((h _).mpr hu) ih

theorem GrammarQuantifier.compile_iff (q : GrammarQuantifier) {r : Regex} {L : Word → Prop}
    (h : ∀ w, r.Matches w ↔ L w) (w : Word) :
    (q.compile r).Matches w ↔ q.Apply L w := by
  cases q with
  | one => exact h w
  | opt => simp [compile, Apply, Regex.Matches, h]
  | star => exact repeats_congr h w
  | plus =>
    simp only [compile, Apply, Regex.Matches]
    exact exists_congr fun u => exists_congr fun v =>
      and_congr (h u) (and_congr (repeats_congr h v) Iff.rfl)
  | exact n =>
    exact (compileRepeat_iff r n w).trans (repeatExact_congr h n w)
  | atLeast n =>
    simp only [compile, Apply, Regex.Matches]
    exact exists_congr fun u => exists_congr fun v =>
      and_congr ((compileRepeat_iff r n u).trans (repeatExact_congr h n u))
        (and_congr (repeats_congr h v) Iff.rfl)
  | bounded n m hle =>
    simp only [compile, Apply, Regex.Matches]
    exact exists_congr fun u => exists_congr fun v =>
      and_congr ((compileRepeat_iff r n u).trans (repeatExact_congr h n u))
        (and_congr ((compileUpTo_iff r (m - n) v).trans
          (exists_congr fun j => and_congr Iff.rfl (repeatExact_congr h j v))) Iff.rfl)

mutual
  theorem GrammarAtom.compile_matches_iff (a : GrammarAtom) (w : Word) :
      a.compile.Matches w ↔ a.Denotes w := by
    cases a with
    | normal ch =>
      simp only [GrammarAtom.compile, GrammarAtom.Denotes, Regex.Matches, PatternClass.accepts,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨c, rfl, h1, h2⟩
        rw [Char.le_antisymm h2 h1]
      · rintro rfl
        exact ⟨ch, rfl, Char.le_refl _, Char.le_refl _⟩
    | dot =>
      simp only [GrammarAtom.compile, GrammarAtom.Denotes, Regex.Matches, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]
    | esc e =>
      simp only [GrammarAtom.compile, GrammarAtom.Denotes, Regex.Matches, GrammarEscape.compile_iff]
    | charClass cc =>
      simp only [GrammarAtom.compile, GrammarAtom.Denotes, Regex.Matches, GrammarCharClass.compile_iff]
    | group re =>
      exact re.compile_matches_iff w

  theorem GrammarPiece.compile_matches_iff (p : GrammarPiece) (w : Word) :
      p.compile.Matches w ↔ p.Denotes w := by
    cases p with
    | mk a q =>
      exact q.compile_iff (fun u => a.compile_matches_iff u) w

  theorem GrammarBranch.compile_matches_iff (b : GrammarBranch) (w : Word) :
      b.compile.Matches w ↔ b.Denotes w := by
    cases b with
    | nil => rfl
    | cons hd tl =>
      simp only [GrammarBranch.compile, GrammarBranch.Denotes, Regex.Matches]
      exact exists_congr fun u => exists_congr fun v =>
        and_congr (hd.compile_matches_iff u) (and_congr (tl.compile_matches_iff v) Iff.rfl)

  theorem GrammarRegExp.compile_matches_iff (re : GrammarRegExp) (w : Word) :
      re.compile.Matches w ↔ re.Denotes w := by
    cases re with
    | single b => exact b.compile_matches_iff w
    | alt b rest =>
      simp only [GrammarRegExp.compile, GrammarRegExp.Denotes, Regex.Matches]
      exact or_congr (b.compile_matches_iff w) (rest.compile_matches_iff w)
end

/-- End-to-end theorem linking SABRINA's `matchesPattern` directly to any
W3C XSD 1.1 BNF `GrammarRegExp` whose compiled form equals `parseCompleteRegex pat`. -/
theorem matchesPattern_denotes_iff {pat : String} {g : GrammarRegExp}
    (hp : parseCompleteRegex pat = some g.compile) (s : String) :
    matchesPattern pat s = true ↔ g.Denotes s.toList :=
  (matchesPattern_iff hp s).trans (g.compile_matches_iff s.toList)

#print axioms GrammarEscape.compile_iff
#print axioms GrammarCharClass.compile_iff
#print axioms GrammarRegExp.compile_matches_iff
#print axioms matchesPattern_denotes_iff

end Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence
