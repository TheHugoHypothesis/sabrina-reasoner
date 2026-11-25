import Sabrina.OWL2.Datatypes.Extended

/-! Prefixes of a finite alphabet's word enumeration, used to count bounded
data values without exhausting the alphabet or enumerating all words. -/
namespace Sabrina.OWL2.SROIQD.Termination.BoundedWords

structure Alphabet (α : Type) where
  size : Nat
  positive : 0 < size
  decode : Nat → α
  encode : α → Nat
  encode_lt : ∀ a, encode a < size
  decode_encode : ∀ a, decode (encode a) = a
  encode_decode : ∀ i, i < size → encode (decode i) = i

def Alphabet.word {α} (a : Alphabet α) : Nat → Nat → List α
  | 0, _ => []
  | n + 1, i => a.decode (i % a.size) :: a.word n (i / a.size)

private def Alphabet.wordCode {α} (a : Alphabet α) : List α → Nat
  | [] => 0
  | x :: xs => a.encode x + a.size * a.wordCode xs

theorem Alphabet.word_length {α} (a : Alphabet α) (n i : Nat) : (a.word n i).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [Alphabet.word, ih]

private theorem Alphabet.wordCode_lt {α} (a : Alphabet α) (xs : List α) :
    a.wordCode xs < a.size ^ xs.length := by
  induction xs with
  | nil => simp [Alphabet.wordCode]
  | cons x xs ih =>
    simp only [Alphabet.wordCode, List.length_cons, Nat.pow_succ]
    have hmul := Nat.mul_le_mul_left a.size (show a.wordCode xs + 1 ≤ a.size ^ xs.length by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm a.size (a.size ^ xs.length)] at hmul
    have hd := a.encode_lt x
    omega

private theorem Alphabet.word_wordCode {α} (a : Alphabet α) (xs : List α) :
    a.word xs.length (a.wordCode xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [Alphabet.word, Alphabet.wordCode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (a.encode_lt x),
      Nat.add_mul_div_left _ _ a.positive, Nat.div_eq_of_lt (a.encode_lt x), a.decode_encode, ih]

private theorem Alphabet.wordCode_word {α} (a : Alphabet α) {n i : Nat} (hi : i < a.size ^ n) :
    a.wordCode (a.word n i) = i := by
  induction n generalizing i with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have : i = 0 := by omega
    simp [Alphabet.word, Alphabet.wordCode, this]
  | succ n ih =>
    have hquot : i / a.size < a.size ^ n := (Nat.div_lt_iff_lt_mul a.positive).mpr (by simpa [Nat.pow_succ] using hi)
    simp only [Alphabet.word, Alphabet.wordCode, a.encode_decode _ (Nat.mod_lt _ a.positive), ih hquot]
    exact Nat.mod_add_div ..

theorem Alphabet.word_injective {α} (a : Alphabet α) {n i j : Nat}
    (hi : i < a.size ^ n) (hj : j < a.size ^ n) (eq : a.word n i = a.word n j) : i = j :=
  (a.wordCode_word hi).symm.trans ((congrArg a.wordCode eq).trans (a.wordCode_word hj))

def sampleLength (k lo hi : Nat) : Nat :=
  min hi (max lo (k.log2 + 1))

theorem sampleLength_bounds {k lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ sampleLength k lo hi ∧ sampleLength k lo hi ≤ hi := by
  unfold sampleLength
  omega

private theorem sampleLength_eq_hi_of_small {α} (a : Alphabet α) (halpha : 2 ≤ a.size)
    {k lo hi : Nat} (h : ¬ k ≤ a.size ^ sampleLength k lo hi) :
    sampleLength k lo hi = hi := by
  by_cases hhi : hi ≤ max lo (k.log2 + 1)
  · exact Nat.min_eq_left hhi
  · rw [sampleLength, Nat.min_eq_right (by omega)] at h
    have h₁ := Nat.lt_log2_self (n := k)
    have h₂ := Nat.pow_le_pow_left halpha (k.log2 + 1)
    have h₃ := Nat.pow_le_pow_right a.positive (Nat.le_max_right lo (k.log2 + 1))
    omega

def Alphabet.sample {α} (a : Alphabet α) (k lo hi : Nat) : List (List α) :=
  let n := sampleLength k lo hi
  if k ≤ a.size ^ n then (List.range k).map (a.word n)
  else (List.range' lo (hi + 1 - lo)).flatMap fun n =>
    (List.range (a.size ^ n)).map (a.word n)

theorem Alphabet.large_mem {α} (a : Alphabet α) {k lo hi i : Nat}
    (h : k ≤ a.size ^ sampleLength k lo hi) (hi' : i < k) :
    a.word (sampleLength k lo hi) i ∈ a.sample k lo hi := by
  simp only [Alphabet.sample, h, ite_true]
  exact List.mem_map_of_mem (List.mem_range.mpr hi')

theorem Alphabet.small_mem {α} (a : Alphabet α) {k lo hi : Nat} {xs : List α}
    (h : ¬ k ≤ a.size ^ sampleLength k lo hi) (hlo : lo ≤ xs.length) (hhi : xs.length ≤ hi) :
    xs ∈ a.sample k lo hi := by
  simp only [Alphabet.sample, h, ite_false, List.mem_flatMap]
  exact ⟨xs.length, List.mem_range'.mpr ⟨xs.length - lo, by omega, by omega⟩,
    List.mem_map.mpr ⟨a.wordCode xs, List.mem_range.mpr (a.wordCode_lt xs), a.word_wordCode xs⟩⟩

def bytes : Alphabet UInt8 where
  size := 256
  positive := by decide
  decode := UInt8.ofNat
  encode := UInt8.toNat
  encode_lt := UInt8.toNat_lt
  decode_encode _ := UInt8.ofNat_toNat
  encode_decode i h := by rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

private def scalarIndex (c : Char) : Nat :=
  if c.toNat < 0xD800 then c.toNat else c.toNat - 0x800

private def scalarCodepoint (i : Nat) : Nat :=
  if i < 0xD800 then i else i + 0x800

private theorem scalarValid (c : Char) :
    c.toNat < 0xD800 ∨ 0xE000 ≤ c.toNat ∧ c.toNat < 0x110000 := by
  have h : UInt32.isValidChar c.val := c.valid
  unfold UInt32.isValidChar at h
  change (c.toNat < 0xD800 ∨ 0xDFFF < c.toNat ∧ c.toNat < 0x110000) at h
  omega

def scalars : Alphabet Char where
  size := 0x10F800
  positive := by decide
  decode i := Char.ofNat (scalarCodepoint i)
  encode := scalarIndex
  encode_lt c := by
    have hc := scalarValid c
    unfold scalarIndex
    split <;> omega
  decode_encode c := by
    have hc := scalarValid c
    have h : scalarCodepoint (scalarIndex c) = c.toNat := by
      unfold scalarCodepoint scalarIndex
      split <;> (try split) <;> omega
    rw [h, Char.ofNat_toNat]
  encode_decode i hi := by
    have hv : Nat.isValidChar (scalarCodepoint i) := by
      change scalarCodepoint i < 0xD800 ∨
        0xDFFF < scalarCodepoint i ∧ scalarCodepoint i < 0x110000
      unfold scalarCodepoint
      split <;> omega
    have hnat : (Char.ofNat (scalarCodepoint i)).toNat = scalarCodepoint i := by
      simp only [Char.ofNat, hv, ↓reduceDIte, Char.toNat, Char.ofNatAux]
      exact UInt32.toNat_ofNatLT
    rw [scalarIndex, hnat]
    unfold scalarCodepoint
    split <;> (try split) <;> omega

/-- If the chosen length has too few words, the search uses the entire finite
interval and that interval has a small upper endpoint. -/
theorem Alphabet.small_length_bound {α} (a : Alphabet α) (halpha : 2 ≤ a.size)
    {k lo hi : Nat} (h : ¬ k ≤ a.size ^ sampleLength k lo hi) :
    a.size ^ hi < k := by
  rw [sampleLength_eq_hi_of_small a halpha h] at h
  omega

end Sabrina.OWL2.SROIQD.Termination.BoundedWords
