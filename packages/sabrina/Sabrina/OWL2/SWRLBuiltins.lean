import Sabrina.OWL2.SWRL

/-!
W3C SWRL built-ins (`swrlb:*`):
1. Exact value-level relational evaluator (`evalBuiltinRel`) and deterministic functional
   evaluator (`evalBuiltinOutput?`) over `Datatypes.Value`.
2. Direct-semantics built-in interpretations for both `datatypeMap` (`stdBuiltinSem`)
   and Dedekind-cut `realDatatypeMap` (`realBuiltinSem`), agreeing with OWL 2 order
   and regex facets across all values (including irrational cuts).
3. Kernel-verified open-world facet lowering (`builtinToDataRange?`) for comparison,
   equality, `swrlb:matches`, and `swrlb:stringLength` atoms against constant literals.
-/

namespace Sabrina.OWL2.SWRL

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes

/-! ### 1. Exact Value-Level Comparisons and Arithmetic -/

def valueLt : Value → Value → Bool
  | .number a, .number b => decide (a < b)
  | .float a, .float b => FloatVal.lt a b
  | .double a, .double b => FloatVal.lt a b
  | .dateTime a, .dateTime b => DateTimeVal.lt a b
  | .plainLiteral a la, .plainLiteral b lb => la == lb && decide (a < b)
  | .anyURI a, .anyURI b => decide (a < b)
  | _, _ => false

def valueLe : Value → Value → Bool
  | .number a, .number b => decide (a ≤ b)
  | .float a, .float b => FloatVal.le a b
  | .double a, .double b => FloatVal.le a b
  | .dateTime a, .dateTime b => DateTimeVal.le a b
  | .plainLiteral a la, .plainLiteral b lb => la == lb && decide (a ≤ b)
  | .anyURI a, .anyURI b => decide (a ≤ b)
  | _, _ => false

private def extractRats : List Value → Option (List Rat)
  | [] => some []
  | .number q :: rest => (extractRats rest).map (q :: ·)
  | _ => none

private def extractInt? : Value → Option Int
  | .number q => if q.den == 1 then some q.num else none
  | _ => none

private def extractString? : Value → Option String
  | .plainLiteral s "" => some s
  | _ => none

private def extractStrings : List Value → Option (List String)
  | [] => some []
  | .plainLiteral s "" :: rest => (extractStrings rest).map (s :: ·)
  | _ => none

private def substringOneBased (s : String) (startPos : Int) (len? : Option Int) : String :=
  let cs := s.toList
  let startIdx : Nat := if startPos ≤ 1 then 0 else (startPos - 1).toNat
  let dropped := cs.drop startIdx
  match len? with
  | none => String.ofList dropped
  | some l =>
    if l ≤ 0 then ""
    else String.ofList (dropped.take l.toNat)

private def containsSubstring (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let hs := haystack.toList
    let ns := needle.toList
    let nLen := ns.length
    let rec go : List Char → Bool
      | [] => false
      | c :: rest =>
        if (c :: rest).take nLen == ns then true
        else go rest
    go hs

private def roundHalfUp (q : Rat) : Int :=
  (q + mkRat 1 2).floor

private def nearestEven (q : Rat) : Int :=
  let lo := q.floor
  if q - Rat.ofInt lo == mkRat 1 2 && lo % 2 == 0 then lo else roundHalfUp q

private def signedPower (base : Rat) (exponent : Int) : Rat :=
  let power := base ^ exponent.natAbs
  if exponent < 0 then 1 / power else power

private def exactNthRoot (n k : Nat) : Option Nat := Id.run do
  if n ≤ 1 || k == 1 then return some n
  if k == 0 || k > n.log2 then return none
  let mut lo := 1
  let mut hi := n
  for _ in [:n.log2 + 2] do
    if lo > hi then return none
    let mid := (lo + hi) / 2
    let p := mid ^ k
    if p == n then return some mid
    if p < n then lo := mid + 1 else hi := mid - 1
  return none

private def exactPower (base exponent : Rat) : Option Rat := do
  if base == 0 && exponent.num < 0 then none
  else if exponent.den == 1 then some (signedPower base exponent.num)
  else if base.num < 0 && exponent.den % 2 == 0 then none
  else
    let n ← exactNthRoot base.num.natAbs exponent.den
    let d ← exactNthRoot base.den exponent.den
    let signed : Int := if base.num < 0 then -(Int.ofNat n) else Int.ofNat n
    return signedPower (mkRat signed d) exponent.num

private def roundHalfToEven (q : Rat) (precision : Int) : Rat :=
  let scale := signedPower 10 precision
  Rat.ofInt (nearestEven (q * scale)) / scale

private def normalizeSpace (s : String) : String :=
  let spaced := String.ofList (s.toList.map fun c =>
    if c == '\t' || c == '\n' || c == '\r' then ' ' else c)
  String.intercalate " " ((spaced.splitOn " ").filter fun w => !w.isEmpty)

private def translateChars (s sourceChars targetChars : String) : String :=
  let source := sourceChars.toList
  let replacement := targetChars.toList
  String.ofList (s.toList.filterMap fun c =>
    let idx := source.idxOf c
    if idx == source.length then some c else replacement[idx]?)

private def splitAtSubstring (needle : List Char) : List Char → List Char →
    Option (List Char × List Char)
  | [], acc => if needle.isEmpty then some (acc.reverse, []) else none
  | c :: rest, acc =>
    if (c :: rest).take needle.length == needle then
      some (acc.reverse, (c :: rest).drop needle.length)
    else splitAtSubstring needle rest (c :: acc)

/-- Ordered regex structure for replacement. The datatype matcher erases
    capture boundaries and is independent of alternation priority. -/
private inductive ReplacementPattern where
  | character (r : Regex)
  | sequence (parts : List ReplacementPattern)
  | choice (branches : List ReplacementPattern)
  | capture (index : Nat) (term : ReplacementPattern)
  | repeat (term : ReplacementPattern) (min : Nat) (max : Option Nat) (greedy : Bool)
  | start
  | finish
  | reference (index : Nat)

private structure ReplacementFrame where
  parts : List ReplacementPattern := []
  branches : List ReplacementPattern := []

private def ReplacementFrame.close (f : ReplacementFrame) : ReplacementPattern :=
  .choice ((.sequence f.parts.reverse :: f.branches).reverse)

private def regexDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def bracketToken : List Char → Nat → List Char → Option (List Char × List Char)
  | [], _, _ => none
  | '\\' :: c :: cs, depth, acc => bracketToken cs depth (c :: '\\' :: acc)
  | '[' :: cs, depth, acc => bracketToken cs (depth + 1) ('[' :: acc)
  | ']' :: cs, depth, acc =>
    if depth == 1 then some ((']' :: acc).reverse, cs) else bracketToken cs (depth - 1) (']' :: acc)
  | c :: cs, depth, acc => bracketToken cs depth (c :: acc)

private def replacementAtom : List Char → Option (ReplacementPattern × List Char)
  | '^' :: rest => some (.start, rest)
  | '$' :: rest => some (.finish, rest)
  | '[' :: rest => do
    let (tok, tail) ← bracketToken rest 1 ['[']
    return (.character (← parseCompleteRegex (String.ofList tok)), tail)
  | '\\' :: c :: rest =>
    if regexDigit c && c != '0' then
      let (digits, tail) := rest.span regexDigit
      (parseNatDigits (c :: digits)).map fun n => (.reference n, tail)
    else if (c == 'p' || c == 'P') && rest.head? == some '{' then do
      let (prop, tail) := (rest.drop 1).span (· != '}')
      let '}' :: tail := tail | none
      let tok := ['\\', c, '{'] ++ prop ++ ['}']
      return (.character (← parseCompleteRegex (String.ofList tok)), tail)
    else if c == '$' then some (.character (.pred (.interval '$' '$')), rest)
    else (parseCompleteRegex (String.ofList ['\\', c])).map fun r => (.character r, rest)
  | c :: rest => (parseCompleteRegex (String.singleton c)).map fun r => (.character r, rest)
  | [] => none

private def quantifyReplacement (p : ReplacementPattern) (rest : List Char) :
    Option (ReplacementPattern × List Char) := do
  let greedy (n : Nat) (m : Option Nat) : List Char → ReplacementPattern × List Char
    | '?' :: cs => (.repeat p n m false, cs)
    | cs => (.repeat p n m true, cs)
  match rest with
  | '*' :: cs => return greedy 0 none cs
  | '+' :: cs => return greedy 1 none cs
  | '?' :: cs => return greedy 0 (some 1) cs
  | '{' :: cs =>
    let (digits, delim) := cs.span regexDigit
    let lo ← parseNatDigits digits
    match delim with
    | '}' :: tail => return greedy lo (some lo) tail
    | ',' :: '}' :: tail => return greedy lo none tail
    | ',' :: bound =>
      let (digits, endToken) := bound.span regexDigit
      let hi ← parseNatDigits digits
      let '}' :: tail := endToken | none
      if lo ≤ hi then some (greedy lo (some hi) tail) else none
    | _ => none
  | _ => return (p, rest)

private def parseReplacementPattern : Nat → List Char → ReplacementFrame →
    List (Option Nat × ReplacementFrame) → Nat → Option (ReplacementPattern × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, chars, frame, parents, groups => do
    match chars with
    | [] => if parents.isEmpty then some (frame.close, groups) else none
    | '|' :: tail =>
      parseReplacementPattern fuel tail ⟨[], .sequence frame.parts.reverse :: frame.branches⟩ parents groups
    | '(' :: '?' :: ':' :: tail =>
      parseReplacementPattern fuel tail {} ((none, frame) :: parents) groups
    | '(' :: tail =>
      parseReplacementPattern fuel tail {} ((some (groups + 1), frame) :: parents) (groups + 1)
    | ')' :: tail =>
      let (group, outer) :: outers := parents | none
      let term := group.elim frame.close (fun i => .capture i frame.close)
      let (term, rest) ← quantifyReplacement term tail
      parseReplacementPattern fuel rest { outer with parts := term :: outer.parts } outers groups
    | _ =>
      let (term, tail) ← replacementAtom chars
      let (term, rest) ← quantifyReplacement term tail
      parseReplacementPattern fuel rest { frame with parts := term :: frame.parts } parents groups

private structure MatchPosition where
  rest : List Char
  offset : Nat
  captures : List (Nat × List Char) := []

private inductive ReplacementTask where
  | test (p : ReplacementPattern)
  | record (index : Nat) (start : MatchPosition)
  | continueRepeat (p : ReplacementPattern) (min : Nat) (max : Option Nat)
      (greedy : Bool) (offset : Nat)

private def matchReplacement : Nat → List ReplacementTask → MatchPosition →
    Except Unit (Option MatchPosition)
  | _, [], pos => .ok (some pos)
  | 0, _ :: _, _ => .error ()
  | fuel + 1, task :: todo, pos => do
    let run := matchReplacement fuel
    match task with
    | .record i start =>
      let matched := start.rest.take (pos.offset - start.offset)
      run todo { pos with captures := (i, matched) :: pos.captures }
    | .continueRepeat p lo hi greedy atOffset =>
      if atOffset == pos.offset && lo == 0 then run todo pos
      else run (.test (.repeat p lo hi greedy) :: todo) pos
    | .test (.character r) =>
      match pos.rest with
      | c :: rest =>
        if (r.deriv c).nullable then run todo { pos with rest, offset := pos.offset + 1 }
        else return none
      | [] => return none
    | .test (.start) => if pos.offset == 0 then run todo pos else return none
    | .test (.finish) => if pos.rest.isEmpty then run todo pos else return none
    | .test (.reference n) =>
      let some chars := pos.captures.lookup n | return none
      if pos.rest.take chars.length == chars then
        run todo { pos with rest := pos.rest.drop chars.length, offset := pos.offset + chars.length }
      else return none
    | .test (.sequence parts) => run (parts.map .test ++ todo) pos
    | .test (.choice branches) =>
      for part in branches do
        if let some matched ← run (.test part :: todo) pos then return some matched
      return none
    | .test (.capture n p) => run (.test p :: .record n pos :: todo) pos
    | .test (.repeat p lo hi greedy) =>
      if hi == some 0 then
        if lo == 0 then run todo pos else return none
      else
        let again := .test p :: .continueRepeat p (lo - 1) (hi.map (· - 1)) greedy pos.offset :: todo
        if lo > 0 then run again pos
        else if greedy then
          if let some found ← run again pos then return some found
          run todo pos
        else
          if let some found ← run todo pos then return some found
          run again pos

private def replacementText (captures : List (Nat × List Char)) :
    List Char → Option (List Char)
  | [] => some []
  | '\\' :: c :: cs =>
    if c == '\\' || c == '$' then (replacementText captures cs).map (c :: ·) else none
  | '$' :: digit :: cs =>
    if regexDigit digit then
      let n := digit.toNat - '0'.toNat
      (replacementText captures cs).map ((captures.lookup n).getD [] ++ ·)
    else none
  | ['$'] | ['\\'] => none
  | c :: cs => (replacementText captures cs).map (c :: ·)

private def replaceRegex (s pattern replacement : String) : Option String := do
  let (compiled, _) ← parseReplacementPattern (pattern.length + 1) pattern.toList {} [] 0
  let steps := 32 * (pattern.length + 1) * (s.length + 1) + 1024
  let isEmptyMatch ← (matchReplacement steps [.test compiled] ⟨[], 0, []⟩).toOption
  if isEmptyMatch.isSome || (replacementText [] replacement.toList).isNone then none
  else
    let rec go : Nat → MatchPosition → List Char → Option String
      | 0, pos, acc => some (String.ofList (acc.reverse ++ pos.rest))
      | fuel + 1, pos, acc => do
        let outcome ← (matchReplacement steps [.test compiled] pos).toOption
        match outcome with
        | some next =>
          if next.offset == pos.offset then none
          else
            let matched := pos.rest.take (next.offset - pos.offset)
            let text ← replacementText ((0, matched) :: next.captures) replacement.toList
            go fuel { next with captures := [] } (text.reverse ++ acc)
        | none =>
          match pos.rest with
          | [] => some (String.ofList acc.reverse)
          | c :: rest => go fuel { pos with rest, offset := pos.offset + 1 } (c :: acc)
    go (s.length + 1) ⟨s.toList, 0, []⟩ []

/-! ### 2. Deterministic Functional Built-in Evaluation (`arg0 = f(arg1, ...)`) -/

/-- Compute the deterministic output `arg0` of a functional `swrlb:*` built-in
    given its input arguments `inputs = args.tail`. -/
def evalBuiltinOutput? (b : IRI) (inputs : List Value) : Option Value :=
  if b == swrlb "add" then
    match extractRats inputs with
    | some (q :: qs) => some (.number (qs.foldl (· + ·) q))
    | _ => none
  else if b == swrlb "subtract" then
    match inputs with
    | [.number x, .number y] => some (.number (x - y))
    | _ => none
  else if b == swrlb "multiply" then
    match extractRats inputs with
    | some (q :: qs) => some (.number (qs.foldl (· * ·) q))
    | _ => none
  else if b == swrlb "divide" then
    match inputs with
    | [.number x, .number y] => if y == 0 then none else some (.number (x / y))
    | _ => none
  else if b == swrlb "integerDivide" then
    match inputs with
    | [vx, vy] =>
      match extractInt? vx, extractInt? vy with
      | some x, some y => if y == 0 then none else some (.integer (Int.tdiv x y))
      | _, _ => none
    | _ => none
  else if b == swrlb "mod" then
    match inputs with
    | [vx, vy] =>
      match extractInt? vx, extractInt? vy with
      | some x, some y => if y == 0 then none else some (.integer (Int.tmod x y))
      | _, _ => none
    | _ => none
  else if b == swrlb "unaryPlus" then
    match inputs with
    | [.number x] => some (.number x)
    | _ => none
  else if b == swrlb "unaryMinus" then
    match inputs with
    | [.number x] => some (.number (-x))
    | _ => none
  else if b == swrlb "abs" then
    match inputs with
    | [.number x] => some (.number (if x < 0 then -x else x))
    | _ => none
  else if b == swrlb "ceiling" then
    match inputs with
    | [.number x] => some (.integer x.ceil)
    | _ => none
  else if b == swrlb "floor" then
    match inputs with
    | [.number x] => some (.integer x.floor)
    | _ => none
  else if b == swrlb "round" then
    match inputs with
    | [.number x] => some (.integer (roundHalfUp x))
    | _ => none
  else if b == swrlb "pow" then
    match inputs with
    | [.number base, .number exponent] => (exactPower base exponent).map Value.number
    | _ => none
  else if b == swrlb "roundHalfToEven" then
    match inputs with
    | [.number q] => some (.number (roundHalfToEven q 0))
    | [.number q, precision] => (extractInt? precision).map fun n => .number (roundHalfToEven q n)
    | _ => none
  else if b == swrlb "booleanNot" then
    match inputs with
    | [.boolean x] => some (.boolean (!x))
    | _ => none
  else if b == swrlb "stringConcat" then
    match extractStrings inputs with
    | some ss => some (Value.string (String.join ss))
    | none => none
  else if b == swrlb "substring" then
    match inputs with
    | [vs, vStart] =>
      match extractString? vs, extractInt? vStart with
      | some s, some st => some (Value.string (substringOneBased s st none))
      | _, _ => none
    | [vs, vStart, vLen] =>
      match extractString? vs, extractInt? vStart, extractInt? vLen with
      | some s, some st, some ln => some (Value.string (substringOneBased s st (some ln)))
      | _, _, _ => none
    | _ => none
  else if b == swrlb "stringLength" then
    match inputs with
    | [vs] => (extractString? vs).map fun s => .integer (Int.ofNat s.length)
    | _ => none
  else if b == swrlb "normalizeSpace" then
    match inputs with
    | [v] => (extractString? v).map fun s => Value.string (normalizeSpace s)
    | _ => none
  else if b == swrlb "translate" then
    match extractStrings inputs with
    | some [s, sourceChars, targetChars] => some (Value.string (translateChars s sourceChars targetChars))
    | _ => none
  else if b == swrlb "substringBefore" || b == swrlb "substringAfter" then
    match extractStrings inputs with
    | some [s, needle] =>
      let result := splitAtSubstring needle.toList s.toList []
      let chars := result.map (if b == swrlb "substringBefore" then Prod.fst else Prod.snd)
      some (Value.string (String.ofList (chars.getD [])))
    | _ => none
  else if b == swrlb "replace" then
    match extractStrings inputs with
    | some [s, pat, replacement] => (replaceRegex s pat replacement).map Value.string
    | _ => none
  else if b == swrlb "upperCase" then
    match inputs with
    | [vs] => (extractString? vs).map fun s => Value.string s.toUpper
    | _ => none
  else if b == swrlb "lowerCase" then
    match inputs with
    | [vs] => (extractString? vs).map fun s => Value.string s.toLower
    | _ => none
  else none

def isFunctionalBuiltin (b : IRI) : Bool :=
  b == swrlb "add" || b == swrlb "subtract" || b == swrlb "multiply" ||
  b == swrlb "divide" || b == swrlb "integerDivide" || b == swrlb "mod" ||
  b == swrlb "unaryPlus" || b == swrlb "unaryMinus" || b == swrlb "abs" ||
  b == swrlb "ceiling" || b == swrlb "floor" || b == swrlb "round" ||
  b == swrlb "pow" || b == swrlb "roundHalfToEven" ||
  b == swrlb "booleanNot" || b == swrlb "stringConcat" || b == swrlb "substring" ||
  b == swrlb "stringLength" || b == swrlb "upperCase" || b == swrlb "lowerCase" ||
  b == swrlb "normalizeSpace" || b == swrlb "translate" || b == swrlb "substringBefore" ||
  b == swrlb "substringAfter" || b == swrlb "replace"

def isPredicateBuiltin (b : IRI) : Bool :=
  b == swrlb "equal" || b == swrlb "notEqual" ||
  b == swrlb "lessThan" || b == swrlb "lessThanOrEqual" ||
  b == swrlb "greaterThan" || b == swrlb "greaterThanOrEqual" ||
  b == swrlb "stringEqualIgnoreCase" ||
  b == swrlb "contains" || b == swrlb "containsIgnoreCase" ||
  b == swrlb "startsWith" || b == swrlb "endsWith" ||
  b == swrlb "matches"

def isSupportedBuiltin (b : IRI) : Bool :=
  isPredicateBuiltin b || isFunctionalBuiltin b

/-- Exact relational built-in evaluation on concrete `Datatypes.Value` arguments. -/
def evalBuiltinRel (b : IRI) (args : List Value) : Bool :=
  if b == swrlb "equal" then
    match args with | [x, y] => x == y | _ => false
  else if b == swrlb "notEqual" then
    match args with | [x, y] => x != y | _ => false
  else if b == swrlb "lessThan" then
    match args with | [x, y] => valueLt x y | _ => false
  else if b == swrlb "lessThanOrEqual" then
    match args with | [x, y] => valueLe x y | _ => false
  else if b == swrlb "greaterThan" then
    match args with | [x, y] => valueLt y x | _ => false
  else if b == swrlb "greaterThanOrEqual" then
    match args with | [x, y] => valueLe y x | _ => false
  else if b == swrlb "stringEqualIgnoreCase" then
    match args with
    | [vx, vy] =>
      match extractString? vx, extractString? vy with
      | some sx, some sy => sx.toLower == sy.toLower
      | _, _ => false
    | _ => false
  else if b == swrlb "contains" then
    match args with
    | [vx, vy] =>
      match extractString? vx, extractString? vy with
      | some sx, some sy => containsSubstring sx sy
      | _, _ => false
    | _ => false
  else if b == swrlb "containsIgnoreCase" then
    match args with
    | [vx, vy] =>
      match extractString? vx, extractString? vy with
      | some sx, some sy => containsSubstring sx.toLower sy.toLower
      | _, _ => false
    | _ => false
  else if b == swrlb "startsWith" then
    match args with
    | [vx, vy] =>
      match extractString? vx, extractString? vy with
      | some sx, some sy => sx.startsWith sy
      | _, _ => false
    | _ => false
  else if b == swrlb "endsWith" then
    match args with
    | [vx, vy] =>
      match extractString? vx, extractString? vy with
      | some sx, some sy => sx.endsWith sy
      | _, _ => false
    | _ => false
  else if b == swrlb "matches" then
    match args with
    | [vx, vpat] =>
      match extractString? vx, extractString? vpat with
      | some sx, some pat => matchesPattern pat sx
      | _, _ => false
    | _ => false
  else
    match args with
    | out :: inputs => evalBuiltinOutput? b inputs == some out
    | [] => false

theorem evalBuiltinRel_of_output {b : IRI} {inputs : List Value} {out : Value}
    (hfunc : isPredicateBuiltin b = false)
    (hout : evalBuiltinOutput? b inputs = some out) :
    evalBuiltinRel b (out :: inputs) = true := by
  simp only [isPredicateBuiltin, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hfunc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hfunc
  unfold evalBuiltinRel
  simp [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4,
    beq_false_of_ne h5, beq_false_of_ne h6, beq_false_of_ne h7, beq_false_of_ne h8,
    beq_false_of_ne h9, beq_false_of_ne h10, beq_false_of_ne h11, beq_false_of_ne h12, hout]

/-- Render a concrete `Datatypes.Value` back to a canonical OWL 2 `Literal`
    (verified by `decodeLiteral l == some v` at call sites). -/
def valueToLiteral? : Value → Option Literal
  | .boolean true => some ⟨"true", xsd "boolean"⟩
  | .boolean false => some ⟨"false", xsd "boolean"⟩
  | .number q =>
    if q.den == 1 then some ⟨toString q.num, xsd "integer"⟩
    else some ⟨s!"{q.num}/{q.den}", owlRational⟩
  | .plainLiteral s "" => some ⟨s, xsd "string"⟩
  | .anyURI s => some ⟨s, xsd "anyURI"⟩
  | _ => none

/-! ### Concrete temporal values for SWRL built-in chains -/

inductive BuiltinValue where
  | owl (v : Value)
  | date (v : DateTimeVal)
  | time (v : DateTimeVal)
  | months (v : Int)
  | seconds (v : Rat)
  deriving DecidableEq, Repr

def isBuiltinTemporalDatatype (t : IRI) : Bool :=
  [xsd "date", xsd "time", xsd "duration", xsd "yearMonthDuration", xsd "dayTimeDuration"].contains t

private def decimalDigits (den : Nat) : Nat → Nat → Option (List Char)
  | 0, r => if r == 0 then some [] else none
  | fuel + 1, r =>
    if r == 0 then some []
    else
      let next := r * 10
      (decimalDigits den fuel (next % den)).map (Char.ofNat ('0'.toNat + next / den) :: ·)

private def decimalText (q : Rat) : Option String := do
  let whole := q.num.natAbs / q.den
  let digits ← decimalDigits q.den (q.den.log2 + 1) (q.num.natAbs % q.den)
  let sign := if q.num < 0 then "-" else ""
  return sign ++ toString whole ++ (if digits.isEmpty then "" else "." ++ String.ofList digits)

private def padNumber (width n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

private def yearText (year : Int) : String :=
  (if year < 0 then "-" else "") ++ padNumber 4 year.natAbs

private def secondsText (seconds : Rat) : Option String :=
  (decimalText seconds).map fun s => if seconds < 10 then "0" ++ s else s

private def timezoneText : Option Int → String
  | none => ""
  | some 0 => "Z"
  | some offset =>
    let minutes := offset.natAbs / 60
    (if offset < 0 then "-" else "+") ++ padNumber 2 (minutes / 60) ++ ":" ++ padNumber 2 (minutes % 60)

private def civilFromDays (days : Int) : Int × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let year := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let month := if mp < 10 then mp + 3 else mp - 9
  (if month ≤ 2 then year + 1 else year, month.toNat, (doy - (153 * mp + 2) / 5 + 1).toNat)

private def localDay (v : DateTimeVal) : Int :=
  (v.epochSeconds + Rat.ofInt (v.timezoneOffset.getD 0)).floor / 86400

private def localClock (v : DateTimeVal) : Rat :=
  v.epochSeconds + Rat.ofInt (v.timezoneOffset.getD 0 - localDay v * 86400)

private def civilText (year : Int) (month day : Nat) : String :=
  yearText year ++ "-" ++ padNumber 2 month ++ "-" ++ padNumber 2 day

private def clockText (clock : Rat) : Option String := do
  let whole := clock.floor.toNat
  let seconds ← secondsText (clock - Rat.ofInt (Int.ofNat (whole / 60 * 60)))
  return padNumber 2 (whole / 3600) ++ ":" ++ padNumber 2 (whole / 60 % 60) ++ ":" ++ seconds

private def dateTimeLiteral (v : DateTimeVal) : Option Literal := do
  let (y, m, d) := civilFromDays (localDay v)
  let clock ← clockText (localClock v)
  return ⟨civilText y m d ++ "T" ++ clock ++ timezoneText v.timezoneOffset, xsd "dateTime"⟩

private def parseDate (s : String) : Option DateTimeVal := do
  let chars := s.toList
  let suffix := if chars.head? == some '-' then chars.drop 1 else chars
  let yearWidth := (suffix.takeWhile (· != '-')).length + if chars.head? == some '-' then 1 else 0
  let split := yearWidth + 6
  parseDateTime false (String.ofList (chars.take split) ++ "T00:00:00" ++ String.ofList (chars.drop split))

private def parseTime (s : String) : Option DateTimeVal := do
  let v ← parseDateTime false ("1970-01-01T" ++ s)
  return { v with epochSeconds := localClock v - Rat.ofInt (v.timezoneOffset.getD 0) }

private def durationComponent (tag : Char) (fractional : Bool) (chars : List Char) :
    Option (Rat × Bool × List Char) := do
  let (digits, rest) := chars.span (fun c => ('0' ≤ c && c ≤ '9') || (fractional && c == '.'))
  match rest with
  | t :: tail =>
    if t == tag then
      let n ← parseDecimal (String.ofList digits)
      return (n, true, tail)
    else return (0, false, chars)
  | [] => return (0, false, chars)

private def parseDuration (s : String) : Option BuiltinValue := do
  let (negative, chars) := match s.toList with
    | '-' :: cs => (true, cs)
    | cs => (false, cs)
  let 'P' :: body := chars | none
  let sign := fun (q : Rat) => if negative then -q else q
  let (years, hasY, afterY) ← durationComponent 'Y' false body
  let (months, hasM, afterM) ← durationComponent 'M' false afterY
  if hasY || hasM then
    if afterM.isEmpty then return .months (sign (years * 12 + months)).floor
    else none
  else
    let (days, hasD, afterD) ← durationComponent 'D' false body
    match afterD with
    | [] => if hasD then some (.seconds (sign (days * 86400))) else none
    | 'T' :: clock =>
      let (hours, hasH, afterH) ← durationComponent 'H' false clock
      let (minutes, hasMin, afterMin) ← durationComponent 'M' false afterH
      let (seconds, hasS, afterS) ← durationComponent 'S' true afterMin
      if afterS.isEmpty && (hasH || hasMin || hasS) then
        some (.seconds (sign (days * 86400 + hours * 3600 + minutes * 60 + seconds)))
      else none
    | _ => none

def decodeBuiltinLiteral? (l : Literal) : Option BuiltinValue :=
  if l.datatype == xsd "date" then (parseDate l.lexical).map .date
  else if l.datatype == xsd "time" then (parseTime l.lexical).map .time
  else if l.datatype == xsd "yearMonthDuration" then
    match parseDuration l.lexical with | some (.months m) => some (.months m) | _ => none
  else if l.datatype == xsd "dayTimeDuration" then
    match parseDuration l.lexical with | some (.seconds s) => some (.seconds s) | _ => none
  else if l.datatype == xsd "duration" then parseDuration l.lexical
  else (decodeLiteral l).map .owl

def builtinValueToLiteral? : BuiltinValue → Option Literal
  | .owl (.dateTime v) => dateTimeLiteral v
  | .owl v => valueToLiteral? v
  | .date v =>
    let (y, m, d) := civilFromDays (localDay v)
    some ⟨civilText y m d ++ timezoneText v.timezoneOffset, xsd "date"⟩
  | .time v =>
    (clockText (localClock v)).map fun s => ⟨s ++ timezoneText v.timezoneOffset, xsd "time"⟩
  | .months m =>
    some ⟨(if m < 0 then "-" else "") ++ "P" ++ toString m.natAbs ++ "M", xsd "yearMonthDuration"⟩
  | .seconds s =>
    (decimalText (if s < 0 then -s else s)).map fun text =>
      ⟨(if s < 0 then "-" else "") ++ "PT" ++ text ++ "S", xsd "dayTimeDuration"⟩

private def numericArg : BuiltinValue → Option Rat
  | .owl (.number q) => some q
  | _ => none

private def integerArg (v : BuiltinValue) : Option Int :=
  (numericArg v).bind fun q => if q.den == 1 then some q.num else none

private def secondsArg : BuiltinValue → Option Rat
  | .seconds q => some q
  | _ => none

private def monthsArg : BuiltinValue → Option Int
  | .months m => some m
  | _ => none

private def stringArg : BuiltinValue → Option String
  | .owl (.plainLiteral s "") => some s
  | _ => none

private def tzArg (v : BuiltinValue) : Option (Option Int) := do
  let s ← stringArg v
  parseTzSuffix s.toList

private def constructorDate (y m d tz : BuiltinValue) : Option String := do
  let year ← integerArg y
  let month ← integerArg m
  let day ← integerArg d
  let offset ← tzArg tz
  if month < 1 || month > 12 || day < 1 || day > 31 then none
  else return civilText year month.toNat day.toNat ++ timezoneText offset

private def constructorClock (h m s : BuiltinValue) : Option String := do
  let hour ← integerArg h
  let minute ← integerArg m
  let seconds ← numericArg s
  if hour < 0 || hour > 24 || minute < 0 || minute ≥ 60 || seconds < 0 || seconds ≥ 60 then none
  else
    let secondText ← secondsText seconds
    return padNumber 2 hour.toNat ++ ":" ++ padNumber 2 minute.toNat ++ ":" ++ secondText

private def isTemporalBuiltin (b : IRI) : Bool :=
  (["dateTime", "date", "time", "yearMonthDuration", "dayTimeDuration",
    "addYearMonthDurations", "subtractYearMonthDurations", "multiplyYearMonthDurations",
    "divideYearMonthDurations", "addDayTimeDurations", "subtractDayTimeDurations",
    "multiplyDayTimeDurations", "divideDayTimeDuration", "subtractDates", "subtractTimes",
    "addYearMonthDurationToDateTime", "addDayTimeDurationToDateTime",
    "subtractYearMonthDurationFromDateTime", "subtractDayTimeDurationFromDateTime",
    "addYearMonthDurationToDate", "addDayTimeDurationToDate", "subtractYearMonthDurationFromDate",
    "subtractDayTimeDurationFromDate", "addDayTimeDurationToTime", "subtractDayTimeDurationFromTime",
    "subtractDateTimesYieldingYearMonthDuration", "subtractDateTimesYieldingDayTimeDuration"].map swrlb).contains b

private def daysInCivilMonth (year : Int) (month : Nat) : Nat :=
  match month with
  | 2 => if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

private def shiftMonths (v : DateTimeVal) (n : Int) : Option DateTimeVal := do
  let (y, m, d) := civilFromDays (localDay v)
  let total := 12 * y + Int.ofNat m - 1 + n
  let year := total / 12
  let month := (total % 12).toNat + 1
  let start ← parseDateTime false (civilText year month (min d (daysInCivilMonth year month)) ++
    "T00:00:00" ++ timezoneText v.timezoneOffset)
  return { start with epochSeconds := start.epochSeconds + localClock v }

private def shiftSeconds (v : DateTimeVal) (n : Rat) : DateTimeVal :=
  { v with epochSeconds := v.epochSeconds + n }

private def midnight (v : DateTimeVal) : DateTimeVal :=
  { v with epochSeconds := Rat.ofInt (localDay v * 86400 - v.timezoneOffset.getD 0) }

private def clockOnly (v : DateTimeVal) : DateTimeVal :=
  { v with epochSeconds := localClock v - Rat.ofInt (v.timezoneOffset.getD 0) }

private def subtractInstants (x y : DateTimeVal) : Option Rat :=
  if x.hasTimezone == y.hasTimezone then some (x.epochSeconds - y.epochSeconds) else none

private def subtractMonths (x y : DateTimeVal) : Option Int := do
  let seconds ← subtractInstants x y
  let x := { x with timezoneOffset := y.timezoneOffset }
  let (xYear, xMonth, _) := civilFromDays (localDay x)
  let (yYear, yMonth, _) := civilFromDays (localDay y)
  let months := (xYear - yYear) * 12 + Int.ofNat xMonth - Int.ofNat yMonth
  let shifted ← shiftMonths y months
  if seconds ≥ 0 && shifted.epochSeconds > x.epochSeconds then return months - 1
  else if seconds < 0 && shifted.epochSeconds < x.epochSeconds then return months + 1
  else return months

private def evalTemporalOutput? (b : IRI) (inputs : List BuiltinValue) : Option BuiltinValue := do
  match (b.splitOn "#").getLast?, inputs with
  | some "dateTime", [y, m, d, h, min, s, tz] =>
    let date ← constructorDate y m d (.owl (.string ""))
    let clock ← constructorClock h min s
    return .owl (.dateTime (← parseDateTime false (date ++ "T" ++ clock ++ timezoneText (← tzArg tz))))
  | some "date", [y, m, d, tz] => return .date (← parseDate (← constructorDate y m d tz))
  | some "time", [h, m, s, tz] =>
    return .time (← parseTime ((← constructorClock h m s) ++ timezoneText (← tzArg tz)))
  | some "yearMonthDuration", [y, m] => return .months ((← integerArg y) * 12 + (← integerArg m))
  | some "dayTimeDuration", [d, h, m, s] =>
    return .seconds ((← numericArg d) * 86400 + (← numericArg h) * 3600 + (← numericArg m) * 60 + (← numericArg s))
  | some "addYearMonthDurations", .months m :: rest =>
    return .months ((← rest.mapM monthsArg).foldl (· + ·) m)
  | some "addDayTimeDurations", .seconds s :: rest =>
    return .seconds ((← rest.mapM secondsArg).foldl (· + ·) s)
  | some "subtractYearMonthDurations", [.months x, .months y] => return .months (x - y)
  | some "subtractDayTimeDurations", [.seconds x, .seconds y] => return .seconds (x - y)
  | some "multiplyYearMonthDurations", [.months x, .owl (.number y)] =>
    return .months (roundHalfUp (Rat.ofInt x * y))
  | some "multiplyDayTimeDurations", [.seconds x, .owl (.number y)] => return .seconds (x * y)
  | some "divideYearMonthDurations", [.months x, .owl (.number y)] =>
    if y == 0 then none else some (.months (roundHalfUp (Rat.ofInt x / y)))
  | some "divideDayTimeDuration", [.seconds x, .owl (.number y)] =>
    if y == 0 then none else some (.seconds (x / y))
  | some "divideYearMonthDurations", [.months x, .months y] =>
    if y == 0 then none else some (.owl (.number (Rat.ofInt x / Rat.ofInt y)))
  | some "divideDayTimeDuration", [.seconds x, .seconds y] =>
    if y == 0 then none else some (.owl (.number (x / y)))
  | some "subtractDates", [.date x, .date y]
  | some "subtractTimes", [.time x, .time y]
  | some "subtractDateTimesYieldingDayTimeDuration", [.owl (.dateTime x), .owl (.dateTime y)] =>
    (subtractInstants x y).map .seconds
  | some "subtractDateTimesYieldingYearMonthDuration", [.owl (.dateTime x), .owl (.dateTime y)] =>
    (subtractMonths x y).map .months
  | some "addYearMonthDurationToDateTime", [.owl (.dateTime v), .months m] =>
    (shiftMonths v m).map fun w => .owl (.dateTime w)
  | some "subtractYearMonthDurationFromDateTime", [.owl (.dateTime v), .months m] =>
    (shiftMonths v (-m)).map fun w => .owl (.dateTime w)
  | some "addDayTimeDurationToDateTime", [.owl (.dateTime v), .seconds s] =>
    return .owl (.dateTime (shiftSeconds v s))
  | some "subtractDayTimeDurationFromDateTime", [.owl (.dateTime v), .seconds s] =>
    return .owl (.dateTime (shiftSeconds v (-s)))
  | some "addYearMonthDurationToDate", [.date v, .months m] => (shiftMonths v m).map .date
  | some "subtractYearMonthDurationFromDate", [.date v, .months m] => (shiftMonths v (-m)).map .date
  | some "addDayTimeDurationToDate", [.date v, .seconds s] => return .date (midnight (shiftSeconds v s))
  | some "subtractDayTimeDurationFromDate", [.date v, .seconds s] => return .date (midnight (shiftSeconds v (-s)))
  | some "addDayTimeDurationToTime", [.time v, .seconds s] => return .time (clockOnly (shiftSeconds v s))
  | some "subtractDayTimeDurationFromTime", [.time v, .seconds s] => return .time (clockOnly (shiftSeconds v (-s)))
  | _, _ => none

def isConcreteFunctionalBuiltin (b : IRI) : Bool := isFunctionalBuiltin b || isTemporalBuiltin b

def isSupportedConcreteBuiltin (b : IRI) : Bool := isSupportedBuiltin b || isTemporalBuiltin b

def evalConcreteBuiltinOutput? (b : IRI) (inputs : List BuiltinValue) : Option BuiltinValue :=
  if isTemporalBuiltin b then evalTemporalOutput? b inputs
  else (inputs.mapM fun | BuiltinValue.owl v => some v | _ => none).bind fun values =>
    (evalBuiltinOutput? b values).map BuiltinValue.owl

def evalConcreteBuiltinRel (b : IRI) (args : List BuiltinValue) : Bool :=
  if b == swrlb "equal" then
    match args with | [x, y] => x == y | _ => false
  else if b == swrlb "notEqual" then
    match args with | [x, y] => x != y | _ => false
  else if isTemporalBuiltin b then
    match args with
    | out :: inputs => evalTemporalOutput? b inputs == some out
    | _ => false
  else
    match args.mapM (fun | .owl v => some v | _ => none) with
    | some values => evalBuiltinRel b values
    | none => false

/-- Distinguish undefined operations from inputs outside the implemented exact
    numeric or regex fragment, which must be reported to the grounding caller. -/
def requireConcreteBuiltinOutput (b : IRI) : Bool :=
  isTemporalBuiltin b || b == swrlb "pow" || b == swrlb "replace"

/-! ### 3. Direct Semantics for Built-ins over `datatypeMap` and `realDatatypeMap` -/

private def orderName : OrderFacet → IRI
  | .minInclusive => xsd "minInclusive"
  | .maxInclusive => xsd "maxInclusive"
  | .minExclusive => xsd "minExclusive"
  | .maxExclusive => xsd "maxExclusive"

private def flipOrder : OrderFacet → OrderFacet
  | .minInclusive => .maxInclusive
  | .maxInclusive => .minInclusive
  | .minExclusive => .maxExclusive
  | .maxExclusive => .minExclusive

@[simp] private theorem orderFacet_orderName (f : OrderFacet) :
    orderFacet (orderName f) = some f := by cases f <;> rfl

@[simp] private theorem lengthFacet_orderName (f : OrderFacet) :
    lengthFacet (orderName f) = none := by cases f <;> rfl

private def builtinOrder? (b : IRI) : Option OrderFacet :=
  if b == swrlb "greaterThan" then some .minExclusive
  else if b == swrlb "greaterThanOrEqual" then some .minInclusive
  else if b == swrlb "lessThan" then some .maxExclusive
  else if b == swrlb "lessThanOrEqual" then some .maxInclusive
  else none

private def orderBase? : Value → Option IRI
  | .number _ => some owlReal
  | .float _ => some (xsd "float")
  | .double _ => some (xsd "double")
  | .dateTime _ => some (xsd "dateTime")
  | _ => none

private def orderedText : OrderFacet → String → String → Prop
  | .minInclusive, b, v => b ≤ v
  | .maxInclusive, b, v => v ≤ b
  | .minExclusive, b, v => b < v
  | .maxExclusive, b, v => v < b

private def realOrdered (ord : OrderFacet) : RealValue → RealValue → Prop
  | .inl (.number b), .inl (.number v) => ord.holds b v
  | .inl (.float b), .inl (.float v) =>
    FloatFormat.binary32.contains b ∧ FloatFormat.binary32.contains v ∧ ord.holdsFloat b v = true
  | .inl (.double b), .inl (.double v) =>
    FloatFormat.binary64.contains b ∧ FloatFormat.binary64.contains v ∧ ord.holdsFloat b v = true
  | .inl (.dateTime b), .inl (.dateTime v) => b.valid ∧ v.valid ∧ ord.holdsDateTime b v = true
  | .inl (.plainLiteral b lb), .inl (.plainLiteral v lv) => lb = lv ∧ orderedText ord b v
  | .inl (.anyURI b), .inl (.anyURI v) => orderedText ord b v
  | .inl (.number b), .inr v => v.atFacet b ord
  | .inr b, .inl (.number v) => b.atRational v ord
  | .inr b, .inr v => v.atCut b ord
  | _, _ => False

private theorem realOrdered_flip (ord : OrderFacet) (b v : RealValue) :
    realOrdered ord b v ↔ realOrdered (flipOrder ord) v b := by
  cases b <;> cases v
  case inl.inl b v =>
    cases b <;> cases v <;> try rfl
    all_goals cases ord <;>
      simp only [realOrdered, flipOrder, OrderFacet.holds, OrderFacet.holdsFloat,
        OrderFacet.holdsDateTime, orderedText, and_left_comm, eq_comm (a := (_ : String))]
  case inl.inr b v => cases b <;> cases ord <;> rfl
  case inr.inl b v => cases v <;> cases ord <;> rfl
  case inr.inr b v => cases ord <;> rfl

private theorem decodedOrderBase_typed {l : Literal} {b : Value} {dt : IRI}
    (hl : decodeLiteral l = some b) (h : orderBase? b = some dt) : valueSpace dt b := by
  have hb := (datatypeMap.lexical_typed l b hl).2
  change valueSpace l.datatype b at hb
  cases b <;> simp [orderBase?] at h
  all_goals subst dt
  · simp [valueSpace_real_iff]
  · exact (valueSpace_float_iff _ _).mpr ⟨rfl, ((valueSpace_float_iff _ _).mp hb).2⟩
  · exact (valueSpace_double_iff _ _).mpr ⟨rfl, ((valueSpace_double_iff _ _).mp hb).2⟩
  · exact (valueSpace_dateTime_iff _ _).mpr ⟨((valueSpace_dateTime_iff _ _).mp hb).1, .inl rfl⟩

private theorem realOrdered_facet {dt : IRI} {bound : Value}
    (h : orderBase? bound = some dt) (typed : valueSpace dt bound)
    (ord : OrderFacet) (v : RealValue) :
    realOrdered ord (.inl bound) v ↔ realFacetSpace dt (orderName ord) (.inl bound) v := by
  cases bound <;> simp [orderBase?] at h
  all_goals subst dt
  all_goals cases v with
    | inl v =>
      cases v <;>
        simp_all [realOrdered, realFacetSpace, facetSpace, Value.isIrrationalWitness,
          valueSpace_real_iff, valueSpace_float_iff, valueSpace_double_iff, valueSpace_dateTime_iff]
    | inr v => simp [realOrdered, realFacetSpace]

/-- Exact built-in comparison on the real datatype map, including cut values. -/
def realValueLt (a b : RealValue) : Prop := realOrdered .maxExclusive b a

def realValueLe (a b : RealValue) : Prop := realOrdered .maxInclusive b a

/-- Standard built-in semantics for `datatypeMap`. -/
def stdBuiltinSem : BuiltinSemantics datatypeMap :=
  fun i b xs =>
    if b == swrlb "equal" then
      match xs with | [x, y] => x = y | _ => False
    else if b == swrlb "notEqual" then
      match xs with | [x, y] => x ≠ y | _ => False
    else
      ∃ vs : List Value, xs = vs.map i.embedValue ∧ evalBuiltinRel b vs = true

private def stringFacetRelation (i : Interpretation realDatatypeMap) (facet : IRI)
    (x b : i.Data) : Prop :=
  ∃ bound v, i.embedValue bound = b ∧ i.embedValue v = x ∧
    realFacetSpace (xsd "string") facet bound v

/-- Built-ins over exact real values. Ordering and string tests share the OWL
    facet semantics used by local data-variable roll-up. -/
def realBuiltinSem : BuiltinSemantics realDatatypeMap :=
  fun i b xs =>
    if b == swrlb "equal" then
      match xs with | [x, y] => x = y | _ => False
    else if b == swrlb "notEqual" then
      match xs with | [x, y] => x ≠ y | _ => False
    else if let some ord := builtinOrder? b then
      match xs with
      | [x, y] => ∃ v bound, i.embedValue v = x ∧ i.embedValue bound = y ∧ realOrdered ord bound v
      | _ => False
    else if b == swrlb "matches" then
      match xs with | [x, pat] => stringFacetRelation i (xsd "pattern") x pat | _ => False
    else if b == swrlb "stringLength" then
      match xs with | [n, x] => stringFacetRelation i (xsd "length") x n | _ => False
    else
      ∃ vs : List Value, xs = vs.map (fun v => i.embedValue (.inl v)) ∧ evalBuiltinRel b vs = true

theorem realBuiltinSem_classes_irrel (i : Interpretation realDatatypeMap)
    (cls : IRI → i.Object → Prop) (hT : ∀ x, cls thing x) (hN : ∀ x, ¬ cls nothing x)
    (b : IRI) (vs : List i.Data) :
    realBuiltinSem { i with classes := cls, thingExt := hT, nothingExt := hN } b vs ↔
      realBuiltinSem i b vs := by
  unfold realBuiltinSem stringFacetRelation
  rcases vs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp

private def comparisonArgs : List DArg → Option (IRI × Literal × Bool)
  | [.var v, .lit l] => some (v, l, false)
  | [.lit l, .var v] => some (v, l, true)
  | _ => none

private theorem comparisonArgs_cases {args : List DArg} {v : IRI} {l : Literal} {swap : Bool}
    (h : comparisonArgs args = some (v, l, swap)) :
    (args = [.var v, .lit l] ∧ swap = false) ∨ (args = [.lit l, .var v] ∧ swap = true) := by
  cases args with
  | nil => cases h
  | cons a tail =>
    cases tail with
    | nil => cases a <;> cases h
    | cons b tail =>
      cases tail with
      | nil => cases a <;> cases b <;> simp_all [comparisonArgs]
      | cons c rest => cases a <;> cases b <;> cases h

private def orderLowering (ord : OrderFacet) (args : List DArg) : Option (IRI × DataRange) :=
  (comparisonArgs args).bind fun (v, l, swap) =>
    (decodeLiteral l).bind fun value =>
      (orderBase? value).map fun dt =>
        (v, .restriction dt [⟨orderName (if swap then flipOrder ord else ord), l⟩])

/-- Lower a single-variable comparison, equality, regex or string-length
    built-in against a constant literal into an OWL 2 data range. -/
def builtinToDataRange? (b : IRI) (args : List DArg) : Option (IRI × DataRange) :=
  if b == swrlb "equal" then
    (comparisonArgs args).bind fun (v, l, _) =>
      if (decodeLiteral l).isSome then some (v, .oneOf [l]) else none
  else if b == swrlb "notEqual" then
    (comparisonArgs args).bind fun (v, l, _) =>
      if (decodeLiteral l).isSome then some (v, .complement (.oneOf [l])) else none
  else if let some ord := builtinOrder? b then orderLowering ord args
  else if b == swrlb "matches" then
    match args with
    | [.var v, .lit patLit] =>
      match decodeLiteral patLit with
      | some (.plainLiteral _ "") => some (v, .restriction (xsd "string") [⟨xsd "pattern", patLit⟩])
      | _ => none
    | _ => none
  else if b == swrlb "stringLength" then
    match args with
    | [.lit lenLit, .var v] =>
      match decodeLiteral lenLit with
      | some (.number q) =>
        if q.den == 1 && q.num ≥ 0 then
          some (v, .restriction (xsd "string") [⟨xsd "length", lenLit⟩])
        else none
      | _ => none
    | _ => none
  else none

/-- Soundness of `builtinToDataRange?` for `swrlb:equal` and `swrlb:notEqual`
    over any `DatatypeMap` whose built-in semantics matches equality. -/
theorem builtinToDataRange_equal_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (hEq : ∀ (i : Interpretation dm) x y, bSem i (swrlb "equal") [x, y] ↔ x = y)
    (i : Interpretation dm) (σD : IRI → i.Data) (v : IRI) (l : Literal) :
    atomHolds bSem i (fun _ => i.individuals (.named "")) σD (.builtinAtom (swrlb "equal") [.var v, .lit l]) ↔
      dataHolds i (σD v) (.oneOf [l]) := by
  simp [atomHolds, evalDArg, dataHolds, hEq, eq_comm]

theorem builtinToDataRange_notEqual_iff {dm : DatatypeMap} (bSem : BuiltinSemantics dm)
    (hNeq : ∀ (i : Interpretation dm) x y, bSem i (swrlb "notEqual") [x, y] ↔ x ≠ y)
    (i : Interpretation dm) (σD : IRI → i.Data) (v : IRI) (l : Literal) :
    atomHolds bSem i (fun _ => i.individuals (.named "")) σD (.builtinAtom (swrlb "notEqual") [.var v, .lit l]) ↔
      dataHolds i (σD v) (.complement (.oneOf [l])) := by
  simp [atomHolds, evalDArg, dataHolds, hNeq, eq_comm]

private theorem realLexical_of_decode {l : Literal} {b : Value}
    (h : decodeLiteral l = some b) :
    realDatatypeMap.lexicalValue l = some (.inl b) := by
  simp [realDatatypeMap, h]

private theorem realSingleFacet_iff (i : Interpretation realDatatypeMap) (x : i.Data)
    {l : Literal} {t f : IRI} {b : Value} (hd : decodeLiteral l = some b)
    (ht : realDatatypeMap.builtin t) (ha : applicableFacet t f b) :
    dataHolds i x (.restriction t [⟨f, l⟩]) ↔
      ∃ v, i.embedValue v = x ∧ realFacetSpace t f (.inl b) v := by
  let facet : Facet := ⟨f, l⟩
  have hl := realLexical_of_decode hd
  have valid : realDatatypeMap.validFacet t facet := ⟨ht, .inl b, hl, ha⟩
  constructor
  · intro h
    obtain ⟨bound, v, hl', hf, he⟩ := h.2 facet (List.mem_singleton_self _)
    have eq : bound = .inl b := Option.some.inj (hl'.symm.trans hl)
    subst bound
    exact ⟨v, he, hf⟩
  · rintro ⟨v, he, hv⟩
    have hf : facetHolds i t facet x := ⟨.inl b, v, hl, hv, he⟩
    exact ⟨facet_value_typed i valid hf, fun g hg => (List.mem_singleton.mp hg).symm ▸ hf⟩

private theorem stringFacetRelation_iff (i : Interpretation realDatatypeMap) (x : i.Data)
    {l : Literal} {f : IRI} {b : Value} (hd : decodeLiteral l = some b)
    (ha : applicableFacet (xsd "string") f b) :
    stringFacetRelation i f x (i.literalValue l) ↔
      dataHolds i x (.restriction (xsd "string") [⟨f, l⟩]) := by
  have hl := i.lexicalAgreement l (.inl b) (realLexical_of_decode hd)
  rw [realSingleFacet_iff i x hd (by rfl) ha]
  constructor
  · rintro ⟨bound, v, h, hv, hf⟩
    have eq := i.embedValue_injective (h.trans hl)
    subst bound
    exact ⟨v, hv, hf⟩
  · rintro ⟨v, hv, hf⟩
    exact ⟨.inl b, v, hl.symm, hv, hf⟩

private theorem orderFacet_applicable {b : Value} {dt : IRI} (ord : OrderFacet)
    (h : orderBase? b = some dt) : applicableFacet dt (orderName ord) b := by
  apply (checkApplicableFacet_iff _ _ _).mp
  cases b <;> simp [orderBase?] at h
  all_goals subst dt
  all_goals cases ord <;> rfl

private theorem orderedRange_iff (i : Interpretation realDatatypeMap) (x : i.Data)
    {l : Literal} {b : Value} {dt : IRI} (ord : OrderFacet)
    (hd : decodeLiteral l = some b) (hb : orderBase? b = some dt) :
    (∃ v bound, i.embedValue v = x ∧ i.embedValue bound = i.literalValue l ∧ realOrdered ord bound v) ↔
      dataHolds i x (.restriction dt [⟨orderName ord, l⟩]) := by
  have hl := i.lexicalAgreement l (.inl b) (realLexical_of_decode hd)
  have typed := decodedOrderBase_typed hd hb
  have ht : realDatatypeMap.builtin dt := by
    cases b <;> simp [orderBase?] at hb
    all_goals subst dt; rfl
  rw [realSingleFacet_iff i x hd ht (orderFacet_applicable ord hb)]
  constructor
  · rintro ⟨v, bound, hv, hbound, hr⟩
    have eq := i.embedValue_injective (hbound.trans hl)
    subst bound
    exact ⟨v, hv, (realOrdered_facet hb typed ord v).mp hr⟩
  · rintro ⟨v, hv, hr⟩
    exact ⟨v, .inl b, hv, hl.symm, (realOrdered_facet hb typed ord v).mpr hr⟩

/-- Every successful facet lowering is an equivalence in every interpretation
    of the exact real datatype map. No caller-supplied built-in assumption is needed. -/
theorem builtinToDataRange_real_iff (i : Interpretation realDatatypeMap)
    (σI : IRI → i.Object) (σD : IRI → i.Data) {b : IRI} {args : List DArg}
    {v : IRI} {d : DataRange} (h : builtinToDataRange? b args = some (v, d)) :
    atomHolds realBuiltinSem i σI σD (.builtinAtom b args) ↔ dataHolds i (σD v) d := by
  unfold builtinToDataRange? at h
  split at h
  · rename_i he
    obtain ⟨⟨x, l, swap⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h <;> try contradiction
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rcases comparisonArgs_cases ha with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      simp [atomHolds, evalDArg, realBuiltinSem, dataHolds, he, eq_comm]
  · rename_i he
    split at h
    · rename_i hn
      obtain ⟨⟨x, l, swap⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h <;> try contradiction
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rcases comparisonArgs_cases ha with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
        simp [atomHolds, evalDArg, realBuiltinSem, dataHolds, he, hn, eq_comm]
    · rename_i hn
      split at h
      · rename_i ord hord
        obtain ⟨⟨x, l, swap⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨bound, hd, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨dt, ht, h⟩ := Option.map_eq_some_iff.mp h
        change (x, .restriction dt [⟨orderName (if swap then flipOrder ord else ord), l⟩]) =
          (v, d) at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rcases comparisonArgs_cases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [atomHolds, evalDArg, realBuiltinSem, he, hn, hord] using
            orderedRange_iff i (σD x) ord hd ht
        · simp only [atomHolds, realBuiltinSem, he, hn, hord, ↓reduceIte]
          rw [← orderedRange_iff i (σD x) (flipOrder ord) hd ht]
          constructor
          · rintro ⟨b, a, hb, ha, h⟩
            exact ⟨a, b, ha, hb, (realOrdered_flip ord a b).mp h⟩
          · rintro ⟨a, b, ha, hb, h⟩
            exact ⟨b, a, hb, ha, (realOrdered_flip ord a b).mpr h⟩
      · rename_i hord
        split at h
        · rename_i hm
          split at h <;> try contradiction
          split at h <;> try contradiction
          rename_i pat hp
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have ha : applicableFacet (xsd "string") (xsd "pattern") (.plainLiteral pat "") :=
            (checkApplicableFacet_iff _ _ _).mp rfl
          simpa [atomHolds, evalDArg, realBuiltinSem, he, hn, hord, hm] using
            stringFacetRelation_iff i (σD _) hp ha
        · rename_i hm
          split at h <;> try contradiction
          rename_i hs
          split at h <;> try contradiction
          split at h <;> try contradiction
          rename_i q hq
          split at h <;> try contradiction
          rename_i hLength
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have ha : applicableFacet (xsd "string") (xsd "length") (.number q) := by
            apply (checkApplicableFacet_iff _ _ _).mp
            change (decide (q.den = 1 ∧ 0 ≤ q.num) && true) = true
            simpa using hLength
          simpa [atomHolds, evalDArg, realBuiltinSem, he, hn, hord, hm, hs] using
            stringFacetRelation_iff i (σD _) hq ha

#print axioms builtinToDataRange_real_iff
#print axioms evalBuiltinRel_of_output
#print axioms builtinToDataRange_equal_iff
#print axioms builtinToDataRange_notEqual_iff

end Sabrina.OWL2.SWRL
