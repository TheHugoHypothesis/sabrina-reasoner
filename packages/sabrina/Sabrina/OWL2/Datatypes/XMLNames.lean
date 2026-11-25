import Init

/-! XML 1.0 Fifth Edition productions [4] and [4a] and Namespaces in
XML 1.0 Third Edition production [4]. The reference predicates use Unicode
code points. Executable tables use half-open intervals.
https://www.w3.org/TR/xml/#NT-NameStartChar
https://www.w3.org/TR/xml-names/#NT-NCName -/

namespace Sabrina.OWL2.Datatypes.XMLNames

def NameStartChar (c : Char) : Prop :=
  let n := c.toNat
  n = 0x3A ∨ 0x41 ≤ n ∧ n ≤ 0x5A ∨ n = 0x5F ∨ 0x61 ≤ n ∧ n ≤ 0x7A ∨
  0xC0 ≤ n ∧ n ≤ 0xD6 ∨ 0xD8 ≤ n ∧ n ≤ 0xF6 ∨ 0xF8 ≤ n ∧ n ≤ 0x2FF ∨
  0x370 ≤ n ∧ n ≤ 0x37D ∨ 0x37F ≤ n ∧ n ≤ 0x1FFF ∨
  0x200C ≤ n ∧ n ≤ 0x200D ∨ 0x2070 ≤ n ∧ n ≤ 0x218F ∨
  0x2C00 ≤ n ∧ n ≤ 0x2FEF ∨ 0x3001 ≤ n ∧ n ≤ 0xD7FF ∨
  0xF900 ≤ n ∧ n ≤ 0xFDCF ∨ 0xFDF0 ≤ n ∧ n ≤ 0xFFFD ∨
  0x10000 ≤ n ∧ n ≤ 0xEFFFF

def NameChar (c : Char) : Prop :=
  let n := c.toNat
  NameStartChar c ∨ n = 0x2D ∨ n = 0x2E ∨ 0x30 ≤ n ∧ n ≤ 0x39 ∨
    n = 0xB7 ∨ 0x300 ≤ n ∧ n ≤ 0x36F ∨ 0x203F ≤ n ∧ n ≤ 0x2040

def Name (cs : List Char) : Prop :=
  ∃ head tail, cs = head :: tail ∧ NameStartChar head ∧ ∀ c ∈ tail, NameChar c

def NCName (cs : List Char) : Prop := Name cs ∧ ':' ∉ cs

def Nmtoken (cs : List Char) : Prop := cs ≠ [] ∧ ∀ c ∈ cs, NameChar c

def highStarts : List (Nat × Nat) :=
  [(0xC0, 0xD7), (0xD8, 0xF7), (0xF8, 0x300), (0x370, 0x37E), (0x37F, 0x2000),
   (0x200C, 0x200E), (0x2070, 0x2190), (0x2C00, 0x2FF0), (0x3001, 0xD800),
   (0xF900, 0xFDD0), (0xFDF0, 0xFFFE), (0x10000, 0xF0000)]

def highExtras : List (Nat × Nat) := [(0xB7, 0xB8), (0x300, 0x370), (0x203F, 0x2041)]

def inRanges (ranges : List (Nat × Nat)) (n : Nat) : Bool :=
  ranges.any fun (lo, hi) => lo ≤ n && n < hi

theorem inRanges_iff {ranges : List (Nat × Nat)} {n : Nat} :
    inRanges ranges n = true ↔ ∃ r ∈ ranges, r.1 ≤ n ∧ n < r.2 := by
  simp [inRanges, List.any_eq_true]

theorem inRanges_eq_false_of_low {ranges : List (Nat × Nat)} {n : Nat}
    (h : n < 128) (hr : ∀ r ∈ ranges, 128 ≤ r.1) :
    inRanges ranges n = false := by
  apply Bool.eq_false_iff.mpr
  intro hn
  obtain ⟨r, hm, hlo, _⟩ := inRanges_iff.mp hn
  exact Nat.not_le_of_lt h (Nat.le_trans (hr r hm) hlo)

theorem highStarts_low {n : Nat} (h : n < 128) : inRanges highStarts n = false :=
  inRanges_eq_false_of_low h (by simp [highStarts])

theorem highExtras_low {n : Nat} (h : n < 128) : inRanges highExtras n = false :=
  inRanges_eq_false_of_low h (by simp [highExtras])

end Sabrina.OWL2.Datatypes.XMLNames
