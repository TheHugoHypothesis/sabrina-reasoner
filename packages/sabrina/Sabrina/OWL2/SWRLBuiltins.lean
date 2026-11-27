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
  b == swrlb "booleanNot" || b == swrlb "stringConcat" || b == swrlb "substring" ||
  b == swrlb "stringLength" || b == swrlb "upperCase" || b == swrlb "lowerCase"

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

/-! ### 3. Direct Semantics for Built-ins over `datatypeMap` and `realDatatypeMap` -/

/-- Relational comparison on `realDatatypeMap.Value` (`Value ⊕ IrrationalCut`),
    extending `valueLt` to Dedekind cuts so `swrlb:lessThan`/`greaterThan` agree
    exactly with OWL 2 `xsd:minExclusive`/`maxExclusive` facets on `owl:real`. -/
def realValueLt : (Value ⊕ IrrationalCut) → (Value ⊕ IrrationalCut) → Prop
  | .inl v1, .inl v2 => valueLt v1 v2 = true
  | .inl (.number q), .inr c => c.lower q
  | .inr c, .inl (.number q) => ¬ c.lower q
  | .inr c1, .inr c2 => ∃ q : Rat, ¬ c1.lower q ∧ c2.lower q
  | _, _ => False

def realValueLe (a b : Value ⊕ IrrationalCut) : Prop :=
  a = b ∨ realValueLt a b

/-- Standard built-in semantics for `datatypeMap`. -/
def stdBuiltinSem : BuiltinSemantics datatypeMap :=
  fun i b xs =>
    if b == swrlb "equal" then
      match xs with | [x, y] => x = y | _ => False
    else if b == swrlb "notEqual" then
      match xs with | [x, y] => x ≠ y | _ => False
    else
      ∃ vs : List Value, xs = vs.map i.embedValue ∧ evalBuiltinRel b vs = true

/-- Built-in semantics for Dedekind-cut `realDatatypeMap`, extending order
    comparisons to irrational cuts. -/
def realBuiltinSem : BuiltinSemantics realDatatypeMap :=
  fun i b xs =>
    if b == swrlb "equal" then
      match xs with | [x, y] => x = y | _ => False
    else if b == swrlb "notEqual" then
      match xs with | [x, y] => x ≠ y | _ => False
    else if b == swrlb "lessThan" then
      match xs with
      | [x, y] => ∃ vx vy, i.embedValue vx = x ∧ i.embedValue vy = y ∧ realValueLt vx vy
      | _ => False
    else if b == swrlb "lessThanOrEqual" then
      match xs with
      | [x, y] => ∃ vx vy, i.embedValue vx = x ∧ i.embedValue vy = y ∧ realValueLe vx vy
      | _ => False
    else if b == swrlb "greaterThan" then
      match xs with
      | [x, y] => ∃ vx vy, i.embedValue vx = x ∧ i.embedValue vy = y ∧ realValueLt vy vx
      | _ => False
    else if b == swrlb "greaterThanOrEqual" then
      match xs with
      | [x, y] => ∃ vx vy, i.embedValue vx = x ∧ i.embedValue vy = y ∧ realValueLe vy vx
      | _ => False
    else
      ∃ vs : List Value, xs = vs.map (fun v => i.embedValue (.inl v)) ∧ evalBuiltinRel b vs = true

/-! ### 4. Open-World Facet Lowering for Single-Variable Built-in Atoms -/

/-- Infer the maximal OWL 2 datatype family for a decoded literal in order comparisons. -/
private def orderBaseDatatype? (l : Literal) : Option IRI :=
  match decodeLiteral l with
  | some (.number _) => some owlReal
  | some (.float _) => some (xsd "float")
  | some (.double _) => some (xsd "double")
  | some (.dateTime dt) => some (if dt.hasTimezone then xsd "dateTimeStamp" else xsd "dateTime")
  | _ => none

/-- Lower a single-variable comparison, equality, `swrlb:matches`, or `swrlb:stringLength`
    built-in atom against a constant literal into an equivalent `(varName, DataRange)`
    constraint. -/
def builtinToDataRange? (b : IRI) (args : List DArg) : Option (IRI × DataRange) :=
  if b == swrlb "equal" then
    match args with
    | [.var v, .lit l] | [.lit l, .var v] =>
      if (decodeLiteral l).isSome then some (v, .oneOf [l]) else none
    | _ => none
  else if b == swrlb "notEqual" then
    match args with
    | [.var v, .lit l] | [.lit l, .var v] =>
      if (decodeLiteral l).isSome then some (v, .complement (.oneOf [l])) else none
    | _ => none
  else if b == swrlb "greaterThan" then
    match args with
    | [.var v, .lit l] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "minExclusive", l⟩])
    | [.lit l, .var v] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "maxExclusive", l⟩])
    | _ => none
  else if b == swrlb "greaterThanOrEqual" then
    match args with
    | [.var v, .lit l] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "minInclusive", l⟩])
    | [.lit l, .var v] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "maxInclusive", l⟩])
    | _ => none
  else if b == swrlb "lessThan" then
    match args with
    | [.var v, .lit l] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "maxExclusive", l⟩])
    | [.lit l, .var v] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "minExclusive", l⟩])
    | _ => none
  else if b == swrlb "lessThanOrEqual" then
    match args with
    | [.var v, .lit l] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "maxInclusive", l⟩])
    | [.lit l, .var v] => (orderBaseDatatype? l).map fun dt => (v, .restriction dt [⟨xsd "minInclusive", l⟩])
    | _ => none
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

#print axioms evalBuiltinRel_of_output
#print axioms builtinToDataRange_equal_iff
#print axioms builtinToDataRange_notEqual_iff

end Sabrina.OWL2.SWRL
