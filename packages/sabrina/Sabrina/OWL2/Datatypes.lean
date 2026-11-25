import Sabrina.OWL2.DirectSemantics
import Sabrina.OWL2.Datatypes.Lexical
import Sabrina.OWL2.Datatypes.DecimalSpace
import Sabrina.OWL2.Datatypes.Extended

/-! The OWL 2 DL datatype map: Boolean, exact numeric (`owl:real`,
`owl:rational`, `xsd:decimal`, `xsd:integer` and its 12 named subtypes),
floating-point (`xsd:float`, `xsd:double`), string family (`rdf:PlainLiteral`,
`xsd:string` and its 6 named subtypes), `xsd:anyURI`, binary (`xsd:hexBinary`,
`xsd:base64Binary`), date/time (`xsd:dateTime`, `xsd:dateTimeStamp`), and
`rdf:XMLLiteral`. -/

namespace Sabrina.OWL2.Datatypes

def xsd (name : String) : IRI := "http://www.w3.org/2001/XMLSchema#" ++ name
def rdf (name : String) : IRI := "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ++ name

inductive Value where
  | boolean (v : Bool)
  | number (v : Rat)
  | float (v : FloatVal)
  | double (v : FloatVal)
  | plainLiteral (text : String) (lang : String)
  | anyURI (v : String)
  | hexBinary (bytes : List UInt8)
  | base64Binary (bytes : List UInt8)
  | dateTime (v : DateTimeVal)
  | xmlLiteral (raw : String)
  /-- An irrational witness immediately above the anchor in comparisons with
  rational facet bounds. Realization into an ordered real domain uses the
  finitely many facet bounds of the ontology. -/
  | irrational (anchor : Rat)
  deriving DecidableEq, Repr

/-- Integer values are the denominator-one rationals in the same carrier. -/
abbrev Value.integer (v : Int) : Value := .number (Rat.ofInt v)

/-- `xsd:string` values are `rdf:PlainLiteral` values with an empty language tag. -/
abbrev Value.string (s : String) : Value := .plainLiteral s ""

def owlReal : IRI := "http://www.w3.org/2002/07/owl#real"
def owlRational : IRI := "http://www.w3.org/2002/07/owl#rational"

structure IntegerBounds where
  lower : Option Int := none
  upper : Option Int := none
  deriving DecidableEq, Repr

def IntegerBounds.contains (bounds : IntegerBounds) (n : Int) : Prop :=
  (bounds.lower.elim True (· ≤ n)) ∧ (bounds.upper.elim True (n ≤ ·))

def IntegerBounds.intersect (a b : IntegerBounds) : IntegerBounds :=
  { lower := match a.lower, b.lower with
      | none, y => y
      | x, none => x
      | some x, some y => some (max x y),
    upper := match a.upper, b.upper with
      | none, y => y
      | x, none => x
      | some x, some y => some (min x y) }

theorem IntegerBounds.contains_intersect (a b : IntegerBounds) (z : Int) :
    (a.intersect b).contains z ↔ a.contains z ∧ b.contains z := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases al <;> cases bl <;> cases au <;> cases bu <;>
    simp [IntegerBounds.intersect, IntegerBounds.contains] <;> omega

instance (bounds : IntegerBounds) (n : Int) : Decidable (bounds.contains n) := by
  rcases bounds with ⟨lower,upper⟩
  cases lower <;> cases upper <;> unfold IntegerBounds.contains <;> dsimp <;> infer_instance

private def signedBounds (bits : Nat) : IntegerBounds :=
  let magnitude : Int := 2 ^ (bits - 1)
  ⟨some (-magnitude),some (magnitude - 1)⟩

private def unsignedBounds (bits : Nat) : IntegerBounds :=
  ⟨some 0,some (2 ^ bits - 1)⟩

private def integerDatatypes : List (IRI × IntegerBounds) :=
  [(xsd "integer", {}),
   (xsd "nonNegativeInteger", { lower := some 0 }),
   (xsd "nonPositiveInteger", { upper := some 0 }),
   (xsd "positiveInteger", { lower := some 1 }),
   (xsd "negativeInteger", { upper := some (-1) }),
   (xsd "long", signedBounds 64),
   (xsd "int", signedBounds 32),
   (xsd "short", signedBounds 16),
   (xsd "byte", signedBounds 8),
   (xsd "unsignedLong", unsignedBounds 64),
   (xsd "unsignedInt", unsignedBounds 32),
   (xsd "unsignedShort", unsignedBounds 16),
   (xsd "unsignedByte", unsignedBounds 8)]

def integerBounds (t : IRI) : Option IntegerBounds := integerDatatypes.lookup t

private inductive StringKind where
  | plainLiteral
  | string
  | normalizedString
  | token
  | language
  | nmtoken
  | name
  | ncname

private def StringKind.accepts : StringKind → String → String → Bool
  | .plainLiteral, _, _ => true
  | .string, _, lang => lang.isEmpty
  | .normalizedString, s, lang => lang.isEmpty && isNormalizedString s
  | .token, s, lang => lang.isEmpty && isToken s
  | .language, s, lang => lang.isEmpty && isLanguageTag s
  | .nmtoken, s, lang => lang.isEmpty && isNMTOKEN s
  | .name, s, lang => lang.isEmpty && isName s
  | .ncname, s, lang => lang.isEmpty && isNCName s

private inductive Datatype where
  | boolean
  | integer (bounds : IntegerBounds)
  | decimal
  | rational
  | real
  | float
  | double
  | str (kind : StringKind)
  | anyURI
  | hexBinary
  | base64Binary
  | dateTime (requireTz : Bool)
  | xmlLiteral

private def findDatatype (t : IRI) : Option Datatype :=
  if t = xsd "boolean" then some .boolean
  else if t = xsd "decimal" then some .decimal
  else if t = owlRational then some .rational
  else if t = owlReal then some .real
  else if t = xsd "float" then some .float
  else if t = xsd "double" then some .double
  else if t = rdf "PlainLiteral" then some (.str .plainLiteral)
  else if t = xsd "string" then some (.str .string)
  else if t = xsd "normalizedString" then some (.str .normalizedString)
  else if t = xsd "token" then some (.str .token)
  else if t = xsd "language" then some (.str .language)
  else if t = xsd "NMTOKEN" then some (.str .nmtoken)
  else if t = xsd "Name" then some (.str .name)
  else if t = xsd "NCName" then some (.str .ncname)
  else if t = xsd "anyURI" then some .anyURI
  else if t = xsd "hexBinary" then some .hexBinary
  else if t = xsd "base64Binary" then some .base64Binary
  else if t = xsd "dateTime" then some (.dateTime false)
  else if t = xsd "dateTimeStamp" then some (.dateTime true)
  else if t = rdf "XMLLiteral" then some .xmlLiteral
  else (integerBounds t).map .integer

def supportedDatatype (t : IRI) : Bool := (findDatatype t).isSome

private def Datatype.contains : Datatype → Value → Prop
  | .boolean, .boolean _ => True
  | .integer bounds, .number q => q.den = 1 ∧ bounds.contains q.num
  | .decimal, .number q => DecimalValue q
  | .rational, .number _ => True
  | .real, .number _ => True
  | .real, .irrational q => DecimalValue q ∧ q.den ≠ 1
  | .float, .float v => FloatFormat.binary32.contains v
  | .double, .double v => FloatFormat.binary64.contains v
  | .str kind, .plainLiteral s lang => kind.accepts s lang = true
  | .anyURI, .anyURI _ => True
  | .hexBinary, .hexBinary _ => True
  | .base64Binary, .base64Binary _ => True
  | .dateTime reqTz, .dateTime dt => dt.valid ∧ (reqTz = false ∨ dt.hasTimezone = true)
  | .xmlLiteral, .xmlLiteral s => checkCanonicalXMLLiteral s = true
  | _, _ => False

private instance (t : Datatype) (v : Value) : Decidable (t.contains v) := by
  cases t <;> cases v <;> unfold Datatype.contains <;> infer_instance

def valueSpace (t : IRI) (v : Value) : Prop :=
  ∃ datatype, findDatatype t = some datatype ∧ datatype.contains v

def checkValue (t : IRI) (v : Value) : Bool :=
  match findDatatype t with
  | some datatype => decide (datatype.contains v)
  | none => false

theorem checkValue_iff (t : IRI) (v : Value) :
    checkValue t v = true ↔ valueSpace t v := by
  cases ht : findDatatype t <;> simp [checkValue, valueSpace, ht]

private theorem findIte_some_of_ne {p : Prop} [Decidable p] {tail : Option Datatype}
    {d target : Datatype} (hd : d ≠ target) :
    (if p then some d else tail) = some target ↔ ¬ p ∧ tail = some target := by
  by_cases hp : p <;> simp [hp, hd]

theorem valueSpace_float_iff (t : IRI) (f : FloatVal) :
    valueSpace t (.float f) ↔ t = xsd "float" ∧ FloatFormat.binary32.contains f := by
  constructor
  · rintro ⟨d, hd, hf⟩
    cases d <;> try contradiction
    by_cases ht : t = xsd "float"
    · exact ⟨ht, hf⟩
    · unfold findDatatype at hd
      simp only [ht, ↓reduceIte] at hd
      repeat'
        rw [findIte_some_of_ne (by intro h; cases h)] at hd
        obtain ⟨_, hd⟩ := hd
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hd
      cases he
  · rintro ⟨rfl, hf⟩
    exact ⟨.float, rfl, hf⟩

theorem valueSpace_double_iff (t : IRI) (f : FloatVal) :
    valueSpace t (.double f) ↔ t = xsd "double" ∧ FloatFormat.binary64.contains f := by
  constructor
  · rintro ⟨d, hd, hf⟩
    cases d <;> try contradiction
    by_cases ht : t = xsd "double"
    · exact ⟨ht, hf⟩
    · unfold findDatatype at hd
      simp only [ht, ↓reduceIte] at hd
      repeat'
        rw [findIte_some_of_ne (by intro h; cases h)] at hd
        obtain ⟨_, hd⟩ := hd
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hd
      cases he
  · rintro ⟨rfl, hf⟩
    exact ⟨.double, rfl, hf⟩

theorem valueSpace_dateTime_iff (t : IRI) (dt : DateTimeVal) :
    valueSpace t (.dateTime dt) ↔ dt.valid ∧
      (t = xsd "dateTime" ∨ (t = xsd "dateTimeStamp" ∧ dt.hasTimezone = true)) := by
  constructor
  · rintro ⟨d, hd, hf⟩
    cases d <;> try contradiction
    case dateTime req =>
      refine ⟨hf.1, ?_⟩
      by_cases ht : t = xsd "dateTime"
      · exact .inl ht
      · by_cases hs : t = xsd "dateTimeStamp"
        · subst t
          have he : req = true := by cases hd; rfl
          subst req
          exact .inr ⟨rfl, hf.2.resolve_left (by decide)⟩
        · unfold findDatatype at hd
          simp only [ht, hs, ↓reduceIte] at hd
          repeat'
            rw [findIte_some_of_ne (by intro h; cases h)] at hd
            obtain ⟨_, hd⟩ := hd
          obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hd
          cases he
  · rintro ⟨hv, rfl | ⟨rfl, hz⟩⟩
    · exact ⟨.dateTime false, rfl, hv, .inl rfl⟩
    · exact ⟨.dateTime true, rfl, hv, .inr hz⟩

theorem valueSpace_plainLiteral_iri {t : IRI} {s lang : String}
    (h : valueSpace t (.plainLiteral s lang)) :
    t = rdf "PlainLiteral" ∨ t = xsd "string" ∨ t = xsd "normalizedString" ∨
      t = xsd "token" ∨ t = xsd "language" ∨ t = xsd "NMTOKEN" ∨
      t = xsd "Name" ∨ t = xsd "NCName" := by
  obtain ⟨d, hd, hcon⟩ := h
  cases d <;> try contradiction
  case str kind =>
    by_cases h1 : t = rdf "PlainLiteral"; · exact .inl h1
    by_cases h2 : t = xsd "string"; · exact .inr (.inl h2)
    by_cases h3 : t = xsd "normalizedString"; · exact .inr (.inr (.inl h3))
    by_cases h4 : t = xsd "token"; · exact .inr (.inr (.inr (.inl h4)))
    by_cases h5 : t = xsd "language"; · exact .inr (.inr (.inr (.inr (.inl h5))))
    by_cases h6 : t = xsd "NMTOKEN"; · exact .inr (.inr (.inr (.inr (.inr (.inl h6)))))
    by_cases h7 : t = xsd "Name"; · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h7))))))
    by_cases h8 : t = xsd "NCName"; · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h8))))))
    exfalso
    unfold findDatatype at hd
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte] at hd
    repeat'
      rw [findIte_some_of_ne (by intro h; cases h)] at hd
      obtain ⟨_, hd⟩ := hd
    obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hd
    cases he

theorem valueSpace_anyURI_iff (t : IRI) (s : String) :
    valueSpace t (.anyURI s) ↔ t = xsd "anyURI" := by
  constructor
  · rintro ⟨d, hd, hcon⟩
    cases d <;> try contradiction
    by_cases ht : t = xsd "anyURI"
    · exact ht
    · exfalso
      unfold findDatatype at hd
      simp only [ht, ↓reduceIte] at hd
      repeat'
        rw [findIte_some_of_ne (by intro h; cases h)] at hd
        obtain ⟨_, hd⟩ := hd
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hd
      cases he
  · rintro rfl
    exact ⟨.anyURI, rfl, trivial⟩

theorem valueSpace_integer_iff (v : Value) :
    valueSpace (xsd "integer") v ↔ ∃ z : Int, v = .integer z := by
  have hfind : findDatatype (xsd "integer") = some (.integer {}) := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | number q =>
      refine ⟨q.num, ?_⟩
      simp only [Value.integer]
      congr 1
      apply Rat.ext <;> simp [hcon.1]
    | _ => exact False.elim hcon
  · rintro ⟨z, rfl⟩
    exact ⟨.integer {}, hfind, by simp [Datatype.contains, IntegerBounds.contains]⟩

private def Datatype.parse : Datatype → String → Option Value
  | .boolean, raw => (parseBoolean raw).map .boolean
  | .integer _, raw => (parseInteger raw).map Value.integer
  | .decimal, raw => (parseDecimal raw).map .number
  | .rational, raw => (parseRational raw).map .number
  | .real, _ => none
  | .float, raw => (parseFloatVal raw).map .float
  | .double, raw => (parseFloatVal raw .binary64).map .double
  | .str .plainLiteral, raw => (parsePlainLiteral raw).map fun (s, l) => .plainLiteral s l
  | .str _, raw => some (.plainLiteral raw "")
  | .anyURI, raw => some (.anyURI raw)
  | .hexBinary, raw => (parseHexBinary raw).map .hexBinary
  | .base64Binary, raw => (parseBase64Binary raw).map .base64Binary
  | .dateTime reqTz, raw => (parseDateTime reqTz raw).map .dateTime
  | .xmlLiteral, raw => if checkCanonicalXMLLiteral raw then some (.xmlLiteral raw) else none

private def Datatype.lexical : Datatype → String → Value → Prop
  | .boolean, raw, .boolean b => BooleanLexical raw b
  | .integer _, raw, .number q => ∃ z, IntegerLexical raw z ∧ Rat.ofInt z = q
  | .decimal, raw, .number q => DecimalLexical raw q
  | .rational, raw, .number q => RationalLexical raw q
  | .float, raw, .float fv => parseFloatVal raw = some fv
  | .double, raw, .double fv => parseFloatVal raw .binary64 = some fv
  | .str .plainLiteral, raw, .plainLiteral s lang => parsePlainLiteral raw = some (s, lang)
  | .str _, raw, .plainLiteral s lang => raw = s ∧ lang = ""
  | .anyURI, raw, .anyURI s => raw = s
  | .hexBinary, raw, .hexBinary bs => parseHexBinary raw = some bs
  | .base64Binary, raw, .base64Binary bs => parseBase64Binary raw = some bs
  | .dateTime reqTz, raw, .dateTime dt => parseDateTime reqTz raw = some dt
  | .xmlLiteral, raw, .xmlLiteral s => raw = s ∧ checkCanonicalXMLLiteral raw = true
  | _, _, _ => False

private theorem parse_iff (t : Datatype) (raw : String) (v : Value) :
    t.parse raw = some v ↔ t.lexical raw v := by
  cases t with
  | str kind =>
    cases kind <;> cases v <;>
      simp [Datatype.parse, Datatype.lexical, Option.map_eq_some_iff]
  | _ =>
    cases v <;>
      simp [Datatype.parse, Datatype.lexical, Option.map_eq_some_iff, parseBoolean_iff,
        parseInteger_iff, parseDecimal_iff, parseRational_iff, Value.integer, and_comm]

def decodeLiteral (l : Literal) : Option Value := do
  let datatype ← findDatatype l.datatype
  let v ← datatype.parse l.lexical
  if datatype.contains v then some v else none

def LiteralDenotes (l : Literal) (v : Value) : Prop :=
  ∃ datatype, findDatatype l.datatype = some datatype ∧
    datatype.lexical l.lexical v ∧ datatype.contains v

theorem decodeLiteral_iff (l : Literal) (v : Value) :
    decodeLiteral l = some v ↔ LiteralDenotes l v := by
  constructor
  · intro h
    obtain ⟨datatype,ht,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨parsed,hp,h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hv
      cases h
      exact ⟨datatype,ht,(parse_iff _ _ _).mp hp,hv⟩
    · cases h
  · rintro ⟨datatype,ht,hp,hv⟩
    simp [decodeLiteral, ht, (parse_iff _ _ _).mpr hp, hv]

private theorem findDatatype_integer {t : IRI} {bounds : IntegerBounds}
    (h : integerBounds t = some bounds) : findDatatype t = some (.integer bounds) := by
  have ne {r : IRI} (hr : integerBounds r = none) : t ≠ r := by
    intro he
    rw [he, hr] at h
    cases h
  rw [findDatatype,
    ite_eq_right (ne (by decide : integerBounds (xsd "boolean") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "decimal") = none)),
    ite_eq_right (ne (by decide : integerBounds owlRational = none)),
    ite_eq_right (ne (by decide : integerBounds owlReal = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "float") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "double") = none)),
    ite_eq_right (ne (by decide : integerBounds (rdf "PlainLiteral") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "string") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "normalizedString") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "token") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "language") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "NMTOKEN") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "Name") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "NCName") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "anyURI") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "hexBinary") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "base64Binary") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "dateTime") = none)),
    ite_eq_right (ne (by decide : integerBounds (xsd "dateTimeStamp") = none)),
    ite_eq_right (ne (by decide : integerBounds (rdf "XMLLiteral") = none)), h]
  rfl

theorem integerBounds_supported {t : IRI} {bounds : IntegerBounds}
    (h : integerBounds t = some bounds) : supportedDatatype t = true := by
  simp [supportedDatatype, findDatatype_integer h]

theorem valueSpace_integerSubtype_iff {t : IRI} {bounds : IntegerBounds}
    (h : integerBounds t = some bounds) (v : Value) :
    valueSpace t v ↔ ∃ z : Int, bounds.contains z ∧ v = .integer z := by
  have hfind := findDatatype_integer h
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | number q =>
      refine ⟨q.num, hcon.2, ?_⟩
      simp only [Value.integer]
      congr 1
      apply Rat.ext <;> simp [hcon.1]
    | _ => exact False.elim hcon
  · rintro ⟨z, hz, rfl⟩
    exact ⟨.integer bounds, hfind, by simp [Datatype.contains, hz]⟩

theorem valueSpace_boolean_iff (v : Value) :
    valueSpace (xsd "boolean") v ↔ ∃ b : Bool, v = .boolean b := by
  have hfind : findDatatype (xsd "boolean") = some .boolean := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | boolean b => exact ⟨b, rfl⟩
    | _ => exact False.elim hcon
  · rintro ⟨b, rfl⟩
    exact ⟨.boolean, hfind, trivial⟩

theorem valueSpace_decimal_iff (v : Value) :
    valueSpace (xsd "decimal") v ↔ ∃ q : Rat, DecimalValue q ∧ v = .number q := by
  have hfind : findDatatype (xsd "decimal") = some .decimal := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | number q => exact ⟨q, hcon, rfl⟩
    | _ => exact False.elim hcon
  · rintro ⟨q, hq, rfl⟩
    exact ⟨.decimal, hfind, hq⟩

theorem valueSpace_rational_iff (v : Value) :
    valueSpace owlRational v ↔ ∃ q : Rat, v = .number q := by
  have hfind : findDatatype owlRational = some .rational := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | number q => exact ⟨q, rfl⟩
    | _ => exact False.elim hcon
  · rintro ⟨q, rfl⟩
    exact ⟨.rational, hfind, trivial⟩

theorem valueSpace_real_iff (v : Value) :
    valueSpace owlReal v ↔ (∃ q, v = .number q) ∨
      (∃ q, DecimalValue q ∧ q.den ≠ 1 ∧ v = .irrational q) := by
  have hfind : findDatatype owlReal = some .real := rfl
  cases v <;> simp [valueSpace, hfind, Datatype.contains]

private theorem ite_eq_some_real {p : Prop} [Decidable p] {t : Option Datatype}
    {d : Datatype} (hd : d ≠ .real) :
    (if p then some d else t) = some .real ↔ ¬ p ∧ t = some .real := by
  by_cases hp : p <;> simp [hp, hd]

theorem valueSpace_irrational_iff (t : IRI) (q : Rat) :
    valueSpace t (.irrational q) ↔ t = owlReal ∧ DecimalValue q ∧ q.den ≠ 1 := by
  have hfind : ∀ dt : Datatype, dt.contains (.irrational q) → dt = .real := by
    intro dt h
    cases dt <;> first | rfl | contradiction
  constructor
  · rintro ⟨dt, he, hv⟩
    have eq := hfind dt hv
    subst dt
    by_cases ht : t = owlReal
    · exact ⟨ht, hv⟩
    · simp only [findDatatype, ht, ↓reduceIte] at he
      repeat'
        rw [ite_eq_some_real (by intro h; cases h)] at he
        obtain ⟨_, he⟩ := he
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp he
      contradiction
  · rintro ⟨rfl, h⟩
    exact ⟨.real, rfl, h⟩

theorem decodeLiteral_ne_irrational (l : Literal) (q : Rat) :
    decodeLiteral l ≠ some (.irrational q) := by
  intro h
  obtain ⟨dt, _, hl, _⟩ := (decodeLiteral_iff _ _).mp h
  cases dt <;> try exact hl
  case str k => cases k <;> exact hl

theorem valueSpace_string_iff (v : Value) :
    valueSpace (xsd "string") v ↔ ∃ s : String, v = .string s := by
  have hfind : findDatatype (xsd "string") = some (.str .string) := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | plainLiteral s lang =>
      have hl : lang = "" := by
        simp [Datatype.contains, StringKind.accepts] at hcon
        exact hcon
      subst hl
      exact ⟨s, rfl⟩
    | _ => exact False.elim hcon
  · rintro ⟨s, rfl⟩
    exact ⟨.str .string, hfind, by simp [Datatype.contains, StringKind.accepts]⟩

/-- The built-in proper subtypes of `xsd:string`. -/
def isStringSubtype (t : IRI) : Bool :=
  match findDatatype t with
  | some (.str .plainLiteral) | some (.str .string) => false
  | some (.str _) => true
  | _ => false

theorem isStringSubtype_builtin {t : IRI} (ht : isStringSubtype t = true) :
    supportedDatatype t = true := by
  unfold isStringSubtype at ht
  split at ht
  all_goals first | contradiction | rename_i h; simp [supportedDatatype, h]

theorem valueSpace_string_of_subtype {t : IRI} {v : Value}
    (ht : isStringSubtype t = true) (hv : valueSpace t v) : valueSpace (xsd "string") v := by
  obtain ⟨dt, hdt, hvalue⟩ := hv
  rw [isStringSubtype, hdt] at ht
  cases dt with
  | str k =>
    cases k <;> try contradiction
    all_goals
      cases v <;> try contradiction
      simp only [Datatype.contains, StringKind.accepts, Bool.and_eq_true] at hvalue
      exact (valueSpace_string_iff _).mpr ⟨_, by rw [String.isEmpty_iff.mp hvalue.1]⟩
  | _ => contradiction

theorem valueSpace_xmlLiteral_iff (v : Value) :
    valueSpace (rdf "XMLLiteral") v ↔ ∃ s : String, checkCanonicalXMLLiteral s = true ∧ v = .xmlLiteral s := by
  have hfind : findDatatype (rdf "XMLLiteral") = some .xmlLiteral := rfl
  constructor
  · rintro ⟨dt, hdt, hcon⟩
    rw [hfind] at hdt
    cases hdt
    cases v with
    | xmlLiteral s => exact ⟨s, hcon, rfl⟩
    | _ => exact False.elim hcon
  · rintro ⟨s, hs, rfl⟩
    exact ⟨.xmlLiteral, hfind, hs⟩

theorem decodeXMLLiteral_iff (raw s : String) :
    decodeLiteral ⟨raw, rdf "XMLLiteral"⟩ = some (.xmlLiteral s) ↔
      raw = s ∧ checkCanonicalXMLLiteral raw = true := by
  rw [decodeLiteral_iff]
  have hfind : findDatatype (rdf "XMLLiteral") = some .xmlLiteral := rfl
  simp only [LiteralDenotes, hfind, Option.some.injEq, exists_eq_left', Datatype.lexical,
    Datatype.contains]
  exact ⟨And.left, fun ⟨rfl, h⟩ => ⟨⟨rfl, h⟩, h⟩⟩

theorem decodeXMLLiteral_eq (raw : String) :
    decodeLiteral ⟨raw, rdf "XMLLiteral"⟩ =
      if checkCanonicalXMLLiteral raw then some (.xmlLiteral raw) else none := by
  have hfind : findDatatype (rdf "XMLLiteral") = some .xmlLiteral := rfl
  simp only [decodeLiteral, hfind, Option.bind_eq_bind, Option.bind_some, Datatype.parse]
  cases h : checkCanonicalXMLLiteral raw <;> simp [h, Datatype.contains]

/-- The shared rational representation preserves integer decoding and subtype bounds. -/
theorem decodeInteger_iff {t : IRI} {bounds : IntegerBounds}
    (h : integerBounds t = some bounds) (raw : String) (n : Int) :
    decodeLiteral ⟨raw,t⟩ = some (.integer n) ↔ IntegerLexical raw n ∧ bounds.contains n := by
  have same (z : Int) : Rat.ofInt z = Rat.ofInt n ↔ z = n :=
    ⟨fun eq => congrArg Rat.num eq,congrArg Rat.ofInt⟩
  simp [decodeLiteral_iff, LiteralDenotes, findDatatype_integer h, Datatype.lexical,
    Datatype.contains, Value.integer, same]

theorem decimalLexical_value {raw : String} {q : Rat} (h : DecimalLexical raw q) :
    DecimalValue q := by
  rcases h with ⟨z,_,rfl⟩ | ⟨_,fraction,z,_,_,_,rfl⟩
  · refine ⟨z,0,?_⟩
    apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat]
  · exact ⟨z,fraction.length,rfl⟩

/-- For decimals the value-space check adds no extra lexical restriction. -/
theorem decodeDecimal_iff (raw : String) (q : Rat) :
    decodeLiteral ⟨raw,xsd "decimal"⟩ = some (.number q) ↔ DecimalLexical raw q := by
  rw [decodeLiteral_iff]
  have hfind : findDatatype (xsd "decimal") = some .decimal := rfl
  simp only [LiteralDenotes, hfind, Option.some.injEq, exists_eq_left', Datatype.lexical,
    Datatype.contains]
  exact ⟨And.left, fun h => ⟨h,decimalLexical_value h⟩⟩

theorem decodeRational_iff (raw : String) (q : Rat) :
    decodeLiteral ⟨raw,owlRational⟩ = some (.number q) ↔ RationalLexical raw q := by
  rw [decodeLiteral_iff]
  have hfind : findDatatype owlRational = some .rational := rfl
  simp only [LiteralDenotes, hfind, Option.some.injEq, exists_eq_left', Datatype.lexical,
    Datatype.contains, and_true]

inductive OrderFacet where
  | minInclusive | maxInclusive | minExclusive | maxExclusive
  deriving DecidableEq, Repr

def orderFacet (f : IRI) : Option OrderFacet :=
  ([(xsd "minInclusive",.minInclusive), (xsd "maxInclusive",.maxInclusive),
    (xsd "minExclusive",.minExclusive), (xsd "maxExclusive",.maxExclusive)]
    : List (IRI × OrderFacet)).lookup f

def OrderFacet.holds : OrderFacet → Rat → Rat → Prop
  | .minInclusive, bound, value => bound ≤ value
  | .maxInclusive, bound, value => value ≤ bound
  | .minExclusive, bound, value => bound < value
  | .maxExclusive, bound, value => value < bound

instance (facet : OrderFacet) (bound value : Rat) : Decidable (facet.holds bound value) := by
  cases facet <;> unfold OrderFacet.holds <;> infer_instance

/-- Order tests at an irrational witness with rational anchor `q`. The
  witness has the same side as `q` at unequal bounds and is above `q`. -/
def OrderFacet.holdsAbove : OrderFacet → Rat → Rat → Prop
  | .minInclusive, bound, q | .minExclusive, bound, q => bound ≤ q
  | .maxInclusive, bound, q | .maxExclusive, bound, q => q < bound

instance (facet : OrderFacet) (bound q : Rat) : Decidable (facet.holdsAbove bound q) := by
  cases facet <;> unfold OrderFacet.holdsAbove <;> infer_instance

inductive LengthFacet where
  | length | minLength | maxLength
  deriving DecidableEq, Repr

def lengthFacet (f : IRI) : Option LengthFacet :=
  ([(xsd "length", .length), (xsd "minLength", .minLength), (xsd "maxLength", .maxLength)]
    : List (IRI × LengthFacet)).lookup f

def LengthFacet.holds : LengthFacet → Nat → String → Prop
  | .length, n, s => s.length = n
  | .minLength, n, s => n ≤ s.length
  | .maxLength, n, s => s.length ≤ n

instance (facet : LengthFacet) (n : Nat) (s : String) : Decidable (facet.holds n s) := by
  cases facet <;> unfold LengthFacet.holds <;> infer_instance

def OrderFacet.holdsFloat : OrderFacet → FloatVal → FloatVal → Bool
  | .minInclusive, bound, value => bound.le value
  | .maxInclusive, bound, value => value.le bound
  | .minExclusive, bound, value => bound.lt value
  | .maxExclusive, bound, value => value.lt bound

def OrderFacet.holdsDateTime : OrderFacet → DateTimeVal → DateTimeVal → Bool
  | .minInclusive, bound, value => bound.le value
  | .maxInclusive, bound, value => value.le bound
  | .minExclusive, bound, value => bound.lt value
  | .maxExclusive, bound, value => value.lt bound

def LengthFacet.holdsNat : LengthFacet → Nat → Nat → Prop
  | .length, n, len => len = n
  | .minLength, n, len => n ≤ len
  | .maxLength, n, len => len ≤ n

instance (facet : LengthFacet) (n len : Nat) : Decidable (facet.holdsNat n len) := by
  cases facet <;> unfold LengthFacet.holdsNat <;> infer_instance

def applicableFacet (t f : IRI) (bound : Value) : Prop :=
  match findDatatype t, bound with
  | some (.integer _), .number _ | some .decimal, .number _ | some .rational, .number _ | some .real, .number _ =>
    (orderFacet f).isSome
  | some .float, .float _ | some .double, .double _ =>
    (orderFacet f).isSome
  | some (.dateTime _), .dateTime _ =>
    (orderFacet f).isSome
  | some (.str _), .number q | some .anyURI, .number q | some .hexBinary, .number q | some .base64Binary, .number q =>
    q.den = 1 ∧ 0 ≤ q.num ∧ (lengthFacet f).isSome
  | some (.str .plainLiteral), .plainLiteral _ lang =>
    lang = "" ∧ (f = xsd "pattern" ∨ f = rdf "langRange")
  | some (.str _), .plainLiteral _ lang | some .anyURI, .plainLiteral _ lang =>
    lang = "" ∧ f = xsd "pattern"
  | _, _ => False

theorem applicableFacet_str_cases {t f : IRI} {bound : Value}
    (ht : t = rdf "PlainLiteral" ∨ t = xsd "string" ∨ t = xsd "normalizedString" ∨
      t = xsd "token" ∨ t = xsd "language" ∨ t = xsd "NMTOKEN" ∨
      t = xsd "Name" ∨ t = xsd "NCName")
    (happ : applicableFacet t f bound) :
    (∃ q, bound = .number q ∧ q.den = 1 ∧ 0 ≤ q.num ∧ (lengthFacet f).isSome) ∨
    (∃ pat, bound = .plainLiteral pat "" ∧ (f = xsd "pattern" ∨ (t = rdf "PlainLiteral" ∧ f = rdf "langRange"))) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases bound with
    | number q => exact .inl ⟨q, rfl, happ⟩
    | plainLiteral pat lang =>
      obtain ⟨rfl, h | h⟩ := happ
      · exact .inr ⟨pat, rfl, .inl h⟩
      · exact .inr ⟨pat, rfl, .inr ⟨rfl, h⟩⟩
    | _ => exact False.elim happ
  all_goals
    cases bound with
    | number q => exact .inl ⟨q, rfl, happ⟩
    | plainLiteral pat lang =>
      obtain ⟨rfl, h⟩ := happ
      exact .inr ⟨pat, rfl, .inl h⟩
    | _ => exact False.elim happ

theorem applicableFacet_anyURI_cases {f : IRI} {bound : Value}
    (happ : applicableFacet (xsd "anyURI") f bound) :
    (∃ q, bound = .number q ∧ q.den = 1 ∧ 0 ≤ q.num ∧ (lengthFacet f).isSome) ∨
    (∃ pat, bound = .plainLiteral pat "" ∧ f = xsd "pattern") := by
  cases bound with
  | number q => exact .inl ⟨q, rfl, happ⟩
  | plainLiteral pat lang =>
    obtain ⟨rfl, h⟩ := happ
    exact .inr ⟨pat, rfl, h⟩
  | _ => exact False.elim happ

def checkApplicableFacet (t f : IRI) (bound : Value) : Bool :=
  match findDatatype t, bound with
  | some (.integer _), .number _ | some .decimal, .number _ | some .rational, .number _ | some .real, .number _ =>
    (orderFacet f).isSome
  | some .float, .float _ | some .double, .double _ =>
    (orderFacet f).isSome
  | some (.dateTime _), .dateTime _ =>
    (orderFacet f).isSome
  | some (.str _), .number q | some .anyURI, .number q | some .hexBinary, .number q | some .base64Binary, .number q =>
    decide (q.den = 1 ∧ 0 ≤ q.num) && (lengthFacet f).isSome
  | some (.str .plainLiteral), .plainLiteral _ lang =>
    lang == "" && (f == xsd "pattern" || f == rdf "langRange")
  | some (.str _), .plainLiteral _ lang | some .anyURI, .plainLiteral _ lang =>
    lang == "" && f == xsd "pattern"
  | _, _ => false

theorem checkApplicableFacet_iff (t f : IRI) (bound : Value) :
    checkApplicableFacet t f bound = true ↔ applicableFacet t f bound := by
  cases h : findDatatype t with
  | none => simp [checkApplicableFacet, applicableFacet, h]
  | some dt =>
    cases dt with
    | str kind =>
      cases kind <;> cases bound <;> simp [checkApplicableFacet, applicableFacet, h, and_assoc]
    | _ =>
      cases bound <;> simp [checkApplicableFacet, applicableFacet, h, and_assoc]

def facetSpace (t f : IRI) : Value → Value → Prop
  | .number b, .number v =>
    valueSpace t (.number v) ∧ ∃ order, orderFacet f = some order ∧ order.holds b v
  | .number b, .irrational q =>
    valueSpace t (.irrational q) ∧ ∃ order, orderFacet f = some order ∧ order.holdsAbove b q
  | .float b, .float v =>
    valueSpace t (.float v) ∧ ∃ order, orderFacet f = some order ∧ order.holdsFloat b v = true
  | .double b, .double v =>
    valueSpace t (.double v) ∧ ∃ order, orderFacet f = some order ∧ order.holdsFloat b v = true
  | .dateTime b, .dateTime v =>
    valueSpace t (.dateTime v) ∧ ∃ order, orderFacet f = some order ∧ order.holdsDateTime b v = true
  | .number b, .plainLiteral s lang =>
    b.den = 1 ∧ 0 ≤ b.num ∧ valueSpace t (.plainLiteral s lang) ∧
      ∃ lf, lengthFacet f = some lf ∧ lf.holds b.num.toNat s
  | .number b, .anyURI s =>
    b.den = 1 ∧ 0 ≤ b.num ∧ valueSpace t (.anyURI s) ∧
      ∃ lf, lengthFacet f = some lf ∧ lf.holds b.num.toNat s
  | .number b, .hexBinary bs =>
    b.den = 1 ∧ 0 ≤ b.num ∧ valueSpace t (.hexBinary bs) ∧
      ∃ lf, lengthFacet f = some lf ∧ lf.holdsNat b.num.toNat bs.length
  | .number b, .base64Binary bs =>
    b.den = 1 ∧ 0 ≤ b.num ∧ valueSpace t (.base64Binary bs) ∧
      ∃ lf, lengthFacet f = some lf ∧ lf.holdsNat b.num.toNat bs.length
  | .plainLiteral pat langB, .plainLiteral s lang =>
    langB = "" ∧ valueSpace t (.plainLiteral s lang) ∧
      ((f = xsd "pattern" ∧ matchesPattern pat s = true) ∨
       (f = rdf "langRange" ∧ matchesLangRange pat lang = true))
  | .plainLiteral pat langB, .anyURI s =>
    langB = "" ∧ valueSpace t (.anyURI s) ∧ f = xsd "pattern" ∧ matchesPattern pat s = true
  | _, _ => False

def checkFacet (t f : IRI) : Value → Value → Bool
  | .number b, .number v =>
    match orderFacet f with
    | some order => checkValue t (.number v) && decide (order.holds b v)
    | none => false
  | .number b, .irrational q =>
    match orderFacet f with
    | some order => checkValue t (.irrational q) && decide (order.holdsAbove b q)
    | none => false
  | .float b, .float v =>
    match orderFacet f with
    | some order => checkValue t (.float v) && order.holdsFloat b v
    | none => false
  | .double b, .double v =>
    match orderFacet f with
    | some order => checkValue t (.double v) && order.holdsFloat b v
    | none => false
  | .dateTime b, .dateTime v =>
    match orderFacet f with
    | some order => checkValue t (.dateTime v) && order.holdsDateTime b v
    | none => false
  | .number b, .plainLiteral s lang =>
    match lengthFacet f with
    | some lf => decide (b.den = 1 ∧ 0 ≤ b.num) && checkValue t (.plainLiteral s lang) &&
        decide (lf.holds b.num.toNat s)
    | none => false
  | .number b, .anyURI s =>
    match lengthFacet f with
    | some lf => decide (b.den = 1 ∧ 0 ≤ b.num) && checkValue t (.anyURI s) &&
        decide (lf.holds b.num.toNat s)
    | none => false
  | .number b, .hexBinary bs =>
    match lengthFacet f with
    | some lf => decide (b.den = 1 ∧ 0 ≤ b.num) && checkValue t (.hexBinary bs) &&
        decide (lf.holdsNat b.num.toNat bs.length)
    | none => false
  | .number b, .base64Binary bs =>
    match lengthFacet f with
    | some lf => decide (b.den = 1 ∧ 0 ≤ b.num) && checkValue t (.base64Binary bs) &&
        decide (lf.holdsNat b.num.toNat bs.length)
    | none => false
  | .plainLiteral pat langB, .plainLiteral s lang =>
    langB == "" && checkValue t (.plainLiteral s lang) &&
      ((f == xsd "pattern" && matchesPattern pat s) ||
       (f == rdf "langRange" && matchesLangRange pat lang))
  | .plainLiteral pat langB, .anyURI s =>
    langB == "" && checkValue t (.anyURI s) && f == xsd "pattern" && matchesPattern pat s
  | _, _ => false

theorem checkFacet_iff (t f : IRI) (b v : Value) :
    checkFacet t f b v = true ↔ facetSpace t f b v := by
  cases b <;> cases v <;> try rfl
  case number.number =>
    cases hf : orderFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff]
  case number.irrational =>
    cases hf : orderFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff]
  case float.float =>
    cases hf : orderFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff]
  case double.double =>
    cases hf : orderFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff]
  case dateTime.dateTime =>
    cases hf : orderFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff]
  case number.plainLiteral =>
    cases hf : lengthFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff, and_assoc]
  case number.anyURI =>
    cases hf : lengthFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff, and_assoc]
  case number.hexBinary =>
    cases hf : lengthFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff, and_assoc]
  case number.base64Binary =>
    cases hf : lengthFacet f <;> simp [checkFacet, facetSpace, hf, checkValue_iff, and_assoc]
  case plainLiteral.plainLiteral =>
    simp [checkFacet, facetSpace, checkValue_iff, and_assoc]
  case plainLiteral.anyURI =>
    simp [checkFacet, facetSpace, checkValue_iff, and_assoc]
  all_goals simp [checkFacet, facetSpace]

def datatypeMap : DatatypeMap where
  Value := Value
  builtin t := supportedDatatype t = true
  valueSpace := valueSpace
  lexicalValue := decodeLiteral
  applicableFacet := applicableFacet
  facetSpace := facetSpace
  literal_not_builtin := by decide
  lexical_typed := by
    intro l v hv
    obtain ⟨datatype,ht,_,hc⟩ := (decodeLiteral_iff l v).mp hv
    exact ⟨by simp [supportedDatatype, ht],⟨datatype,ht,hc⟩⟩
  facet_typed := by
    intro _ _ b v _ hv
    cases b <;> cases v
    case number.number => exact hv.1
    case number.irrational => exact hv.1
    case float.float => exact hv.1
    case double.double => exact hv.1
    case dateTime.dateTime => exact hv.1
    case number.plainLiteral => exact hv.2.2.1
    case number.anyURI => exact hv.2.2.1
    case number.hexBinary => exact hv.2.2.1
    case number.base64Binary => exact hv.2.2.1
    case plainLiteral.plainLiteral => exact hv.2.1
    case plainLiteral.anyURI => exact hv.2.1
    all_goals exact False.elim hv

/-- The executable order check describes facet membership in any interpretation
    extending this datatype map. -/
theorem facetHolds_iff_check (i : Interpretation datatypeMap) (t : IRI) (f : Facet)
    (bound value : Value) (h : decodeLiteral f.bound = some bound) :
    facetHolds i t f (i.embedValue value) ↔ checkFacet t f.name bound value = true := by
  rw [checkFacet_iff]
  constructor
  · rintro ⟨b,v,hb,hf,hv⟩
    have he : b = bound := Option.some.inj (hb.symm.trans h)
    have hv' : v = value := i.embedValue_injective hv
    cases he
    cases hv'
    exact hf
  · intro hspace
    exact ⟨bound,value,h,hspace,rfl⟩

end Sabrina.OWL2.Datatypes
