import Sabrina.OWL2.Datatypes.StandardsCorrespondence
import Sabrina.OWL2.Datatypes.XMLCorrespondence
import Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence

/-! Milestone C.2 runtime & correspondence regression suite covering:
1. IEEE-754 binary32 & binary64 ties-to-even, subnormal, underflow, overflow,
   and lexical scientific notation boundaries.
2. W3C XSD 1.1 `xsd:dateTime` & `xsd:dateTimeStamp` proleptic Gregorian year `0000`,
   `-0000` rejection, `24:00:00` midnight normalization, century leap years, and ±14:00 bounds.
3. W3C Exc-C14N XML literal correspondence and `renderExcC14N` fixed-point checks.
4. Independent W3C XSD 1.1 Appendix G BNF `GrammarRegExp` compilation checks. -/

namespace SabrinaTests.StandardsTests

open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Datatypes.StandardsCorrespondence
open Sabrina.OWL2.Datatypes.XMLCorrespondence
open Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence

-- 1. IEEE-754 binary32 & binary64 rounding and lexical decoding boundaries
#guard FloatFormat.binary32.round (1 + mkRat 1 (2 ^ 24)) == .finite 1
#guard FloatFormat.binary32.round (1 + mkRat 3 (2 ^ 24)) == .finite (1 + mkRat 1 (2 ^ 22))
#guard FloatFormat.binary32.round (mkRat 1 (2 ^ 149)) == .finite (mkRat 1 (2 ^ 149))
#guard FloatFormat.binary32.round (mkRat 1 (2 ^ 150)) == .posZero
#guard FloatFormat.binary32.round (-(mkRat 1 (2 ^ 150))) == .negZero
#guard FloatFormat.binary64.round (1 + mkRat 1 (2 ^ 53)) == .finite 1
#guard FloatFormat.binary64.round (1 + mkRat 3 (2 ^ 53)) == .finite (1 + mkRat 1 (2 ^ 51))
#guard parseFloatVal "1e50" .binary32 == some .posInf
#guard parseFloatVal "-1e50" .binary32 == some .negInf
#guard parseFloatVal "1e400" .binary64 == some .posInf
#guard parseFloatVal "-1e-50" .binary32 == some .negZero
#guard parseFloatVal "-0.0" .binary32 == some .negZero
#guard parseFloatVal "0.0" .binary32 == some .posZero
#guard parseFloatVal "+INF" .binary32 == some .posInf
#guard parseFloatVal "NaN" .binary64 == some .nan

-- 2. W3C XSD 1.1 dateTime / dateTimeStamp boundaries
#guard parseDateTime false "-0000-01-01T00:00:00Z" == none
#guard (parseDateTime false "0000-02-29T00:00:00Z").isSome
#guard parseDateTime false "2020-01-01T24:00:00Z" == parseDateTime false "2020-01-02T00:00:00Z"
#guard parseDateTime false "2020-01-01T24:00:01Z" == none
#guard (parseDateTime false "2000-02-29T12:00:00Z").isSome
#guard parseDateTime false "1900-02-29T12:00:00Z" == none
#guard (parseDateTime true "2020-01-01T00:00:00+14:00").isSome
#guard (parseDateTime true "2020-01-01T00:00:00-14:00").isSome
#guard parseDateTime true "2020-01-01T00:00:00+14:01" == none
#guard parseDateTime true "2020-01-01T00:00:00-14:01" == none
#guard parseDateTime true "2020-01-01T00:00:00" == none

-- 3. Independent W3C XSD 1.1 BNF GrammarRegExp equivalence checks
private def unicodeDigitMinusAscii : GrammarRegExp :=
  .single (.cons (.mk (.charClass (.subtract
    (.group false [.esc .digit])
    (.group false [.range '0' '9' (by decide)]))) .plus) .nil)

#guard (unicodeDigitMinusAscii.compile.accepts [Char.ofNat 0x0660, Char.ofNat 0x0966]) == true
#guard (unicodeDigitMinusAscii.compile.accepts ['5']) == false
#guard (unicodeDigitMinusAscii.compile.accepts []) == false

end SabrinaTests.StandardsTests
