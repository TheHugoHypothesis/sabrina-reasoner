import Sabrina.OWL2.SROIQD.Termination.BoundedWords
import Sabrina.OWL2.SROIQD.Model

/-! Exact finite enumeration of a string cell at a fixed length. Character
profiles preserve every supported string subtype predicate. Enumeration
caps each profile's concrete substitutions while retaining exact counts
below the requested cap. -/
namespace Sabrina.OWL2.SROIQD.Termination.StringLengthCells

open Datatypes
open Datatypes.XMLNames (highStarts highExtras inRanges inRanges_iff)
open SROIQD (nodup_eraseDups_list)

theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, ys, hnd, hsub => by
    obtain ⟨hna, hnda⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ ys := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ as, x ∈ ys.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun he => hna (by rw [← he]; exact hx))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have hle := length_le_of_nodup_subset hnda hsub'
    have her : (ys.erase a).length + 1 = ys.length := by
      have := List.length_erase_of_mem ha
      have hpos : 0 < ys.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

-- The parts of Unicode above ASCII that are outside both XML name tables.
private def highOthers : List (Nat × Nat) :=
  [(0x80, 0xB7), (0xB8, 0xC0), (0xD7, 0xD8), (0xF7, 0xF8), (0x37E, 0x37F),
   (0x2000, 0x200C), (0x200E, 0x203F), (0x2041, 0x2070), (0x2190, 0x2C00),
   (0x2FF0, 0x3001), (0xE000, 0xF900), (0xFDD0, 0xFDF0), (0xFFFE, 0x10000),
   (0xF0000, 0x110000)]

private theorem highOthers_iff (n : Nat) (hlow : 128 ≤ n) (hv : Nat.isValidChar n) :
    inRanges highOthers n = true ↔
      inRanges highStarts n = false ∧ inRanges highExtras n = false := by
  change n < 0xD800 ∨ 0xDFFF < n ∧ n < 0x110000 at hv
  simp [inRanges, highOthers, highStarts, highExtras, Bool.or_eq_true,
    Bool.and_eq_true, Bool.eq_false_iff] <;> omega

private theorem highExtras_disjoint {n : Nat} (h : inRanges highExtras n = true) :
    inRanges highStarts n = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  simp [inRanges, highStarts, highExtras, Bool.or_eq_true, Bool.and_eq_true] at hs h
  omega

private def profileRanges (p : Char) : List (Nat × Nat) :=
  if p = 'À' then highStarts else if p = '·' then highExtras else if p = '!' then highOthers else []

private theorem profileRanges_iff (p c : Char) (hlow : 128 ≤ c.toNat) :
    inRanges (profileRanges p) c.toNat = true ↔ stringCharacterProfile c = p := by
  have hv : Nat.isValidChar c.toNat := c.valid
  rw [stringCharacterProfile_high c hlow]
  by_cases hp : p = 'À'
  · subst p
    cases hs : inRanges highStarts c.toNat <;> cases he : inRanges highExtras c.toNat <;>
      simp_all [profileRanges]
  by_cases heq : p = '·'
  · subst p
    cases hs : inRanges highStarts c.toNat <;> cases he : inRanges highExtras c.toNat <;>
      simp_all [profileRanges]
    exact Bool.noConfusion (hs.symm.trans (highExtras_disjoint he))
  by_cases ho : p = '!'
  · subst p
    rw [profileRanges, ite_eq_right (by decide : '!' ≠ 'À'), ite_eq_right (by decide : '!' ≠ '·'),
      ite_eq_left rfl, highOthers_iff c.toNat hlow hv]
    cases hs : inRanges highStarts c.toNat <;> cases he : inRanges highExtras c.toNat <;>
      simp
  · cases hs : inRanges highStarts c.toNat <;> cases he : inRanges highExtras c.toNat <;>
      simp [profileRanges, inRanges, hp, heq, ho, Ne.symm hp, Ne.symm heq, Ne.symm ho]

private theorem profileRange_valid {p : Char} {r : Nat × Nat} {i : Nat}
    (hr : r ∈ profileRanges p) (hl : r.1 ≤ i) (hh : i < r.2) :
    128 ≤ i ∧ Nat.isValidChar i := by
  change 128 ≤ i ∧ (i < 0xD800 ∨ 0xDFFF < i ∧ i < 0x110000)
  unfold profileRanges at hr
  split at hr
  · simp [highStarts] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp at hl hh <;> omega
  split at hr
  · simp [highExtras] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp at hl hh <;> omega
  split at hr
  · simp [highOthers] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp at hl hh <;> omega
  · simp at hr

private theorem ofNat_code {i : Nat} (h : Nat.isValidChar i) : (Char.ofNat i).toNat = i := by
  simp only [Char.ofNat, h, ↓reduceDIte, Char.toNat, Char.ofNatAux]
  exact UInt32.toNat_ofNatLT

private def rangeChars (count : Nat) (r : Nat × Nat) : List Char :=
  (List.range' r.1 (min count (r.2 - r.1))).map Char.ofNat

private def options (count : Nat) (p : Char) : List Char :=
  ((List.range 128).map Char.ofNat).filter (fun c => stringCharacterProfile c == p) ++
    (profileRanges p).flatMap (rangeChars count)

private theorem options_profile {count : Nat} {p c : Char} (hc : c ∈ options count p) :
    stringCharacterProfile c = p := by
  rcases List.mem_append.mp hc with hm | hm
  · exact beq_iff_eq.mp (List.mem_filter.mp hm).2
  · obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    have hbound := Nat.lt_of_lt_of_le hj (Nat.min_le_right ..)
    have ⟨hlow, hv⟩ := profileRange_valid (i := r.1 + 1 * j) hr (by omega) (by omega)
    apply (profileRanges_iff p _ (by rw [ofNat_code hv]; exact hlow)).mp
    rw [ofNat_code hv, inRanges_iff]
    exact ⟨r, hr, by omega, by omega⟩

private theorem options_cover (count : Nat) (c : Char) :
    c ∈ options count (stringCharacterProfile c) ∨
    count ≤ (options count (stringCharacterProfile c)).eraseDups.length := by
  by_cases h : c.toNat < 128
  · exact .inl (List.mem_append_left _ (List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨c.toNat, List.mem_range.mpr h, Char.ofNat_toNat c⟩, by simp⟩))
  let p := stringCharacterProfile c
  obtain ⟨r, hr, hlo, hhi⟩ := inRanges_iff.mp
    ((profileRanges_iff p c (by omega)).mpr rfl)
  have sub : ∀ x ∈ rangeChars count r, x ∈ options count p := fun x hx =>
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, hx⟩)
  by_cases hcount : c.toNat - r.1 < count
  · apply Or.inl
    apply sub
    exact List.mem_map.mpr ⟨c.toNat, List.mem_range'.mpr
      ⟨c.toNat - r.1, Nat.lt_min.mpr ⟨hcount, by omega⟩, by omega⟩, Char.ofNat_toNat c⟩
  · apply Or.inr
    have hnd : (rangeChars count r).Nodup := by
      have valid (i : Nat) (hi : i ∈ List.range' r.1 (min count (r.2 - r.1))) :
          Nat.isValidChar i := by
        obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
        have hbound := Nat.lt_of_lt_of_le hj (Nat.min_le_right ..)
        exact (profileRange_valid hr (by omega) (by omega)).2
      unfold rangeChars List.Nodup
      rw [List.pairwise_map]
      apply (List.nodup_range' 1).imp_of_mem
      intro a b ha hb hab he
      exact hab (by simpa [ofNat_code (valid a ha), ofNat_code (valid b hb)] using
        (congrArg Char.toNat he))
    have hle := length_le_of_nodup_subset hnd
      (ys := (options count p).eraseDups) fun x hx => List.mem_eraseDups.mpr (sub x hx)
    simpa [rangeChars, Nat.min_eq_left (by omega : count ≤ r.2 - r.1)] using hle

private def skeletons : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 =>
    let tails := skeletons n
    stringCharacterProfiles.flatMap fun c => tails.map (c :: ·)

private theorem skeleton_mem (xs : List Char) :
    xs.map stringCharacterProfile ∈ skeletons xs.length := by
  induction xs with
  | nil => simp [skeletons]
  | cons c xs ih =>
    exact List.mem_flatMap.mpr ⟨_, stringCharacterProfile_mem c, List.mem_map_of_mem ih⟩

private def substitutions (count : Nat) : List Char → List (List Char)
  | [] => [[]].take count
  | c :: cs =>
    let tails := substitutions count cs
    (((options count c).flatMap fun d => tails.map (d :: ·)).eraseDups).take count

private theorem substitutions_profile {count : Nat} {ps ws : List Char}
    (h : ws ∈ substitutions count ps) : ws.map stringCharacterProfile = ps := by
  induction ps generalizing ws with
  | nil =>
    have hh := (List.take_sublist ..).subset h
    obtain rfl := List.mem_singleton.mp hh
    rfl
  | cons p ps ih =>
    obtain ⟨c, hc, hs⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ((List.take_sublist ..).subset h))
    obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hs
    have e := options_profile hc
    simp only [List.map_cons, e, ih hx]

private theorem nodup_substitutions (count : Nat) (ps : List Char) :
    (substitutions count ps).Nodup := by
  cases ps with
  | nil => exact (List.take_sublist ..).nodup (by simp)
  | cons p ps => exact (List.take_sublist ..).nodup (nodup_eraseDups_list _)

private theorem substitutions_cover (count : Nat) (xs : List Char) :
    xs ∈ substitutions count (xs.map stringCharacterProfile) ∨
      count ≤ (substitutions count (xs.map stringCharacterProfile)).length := by
  induction xs with
  | nil =>
    cases count <;> simp [substitutions]
  | cons c xs ih =>
    let cs := options count (stringCharacterProfile c)
    let tails := substitutions count (xs.map stringCharacterProfile)
    let big := (cs.flatMap fun d => tails.map (d :: ·)).eraseDups
    change c :: xs ∈ big.take count ∨ count ≤ (big.take count).length
    by_cases hbig : count ≤ big.length
    · exact .inr (by simp [List.length_take, hbig])
    · have hc := options_cover count c
      have hcount : 0 < count := by omega
      have hcs : cs ≠ [] := by
        rcases hc with hc | hc
        · exact List.ne_nil_of_mem hc
        · intro e
          change count ≤ cs.eraseDups.length at hc
          simp [e] at hc
          omega
      have ht : tails ≠ [] := by
        rcases ih with hm | hn
        · exact List.ne_nil_of_mem hm
        · intro e
          change count ≤ tails.length at hn
          simp [e] at hn
          omega
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hcs
      obtain ⟨ys, hys⟩ := List.exists_mem_of_ne_nil _ ht
      rcases hc with hc | hc
      · rcases ih with hx | hx
        · left
          rw [List.take_of_length_le (by omega : big.length ≤ count)]
          exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨_, hc, List.mem_map_of_mem hx⟩)
        · have hle : tails.length ≤ big.length := by
            simpa using length_le_of_nodup_subset
              ((nodup_substitutions count (xs.map stringCharacterProfile)).map (c :: ·)
                (fun _ _ hn eq => hn (List.cons.inj eq).2))
              (ys := big) (fun w hw => List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨_, hc, hw⟩))
          exact (hbig (Nat.le_trans hx hle)).elim
      · have hle : cs.eraseDups.length ≤ big.length := by
          simpa using length_le_of_nodup_subset
            ((nodup_eraseDups_list cs).map (· :: ys) (fun _ _ hn eq => hn (List.cons.inj eq).1))
            (ys := big) (fun w hw => by
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
              exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr
                ⟨d, List.mem_eraseDups.mp hd, List.mem_map_of_mem hys⟩))
        exact (hbig (Nat.le_trans hc hle)).elim

private def expandProfiles (count : Nat) (profiles : List (List Char))
    (accept : String → Bool) : List String :=
  profiles.flatMap fun p =>
    if accept (String.ofList p) then (substitutions count p).map String.ofList else []

def sample (count length : Nat) (accept : String → Bool) : List String :=
  expandProfiles count (skeletons length) accept

/-- Try a few character profile sequences before enumerating all of them.
The caller checks the resulting strings before using their count. -/
def sampleShortlist (count length : Nat) (accept : String → Bool) : List String :=
  match length with
  | 0 => expandProfiles count [[]] accept
  | n + 1 =>
    let letters := stringCharacterProfiles.map (fun c => c :: List.replicate n 'a')
    let subtagFirst := if n % 2 = 0 then ['a'] else ['a', 'a']
    let subtags := subtagFirst ++ (List.replicate (n / 2) ['-', 'a']).flatten
    expandProfiles count (subtags :: letters) accept

/-- Either an input is represented directly or the sampler contains at
least `count` distinct strings of the same length and character profile. -/
theorem sample_cover (count : Nat) (xs : List Char) {accept : String → Bool}
    (haccept : accept (String.ofList (xs.map stringCharacterProfile)) = true) :
    String.ofList xs ∈ sample count xs.length accept ∨
    ∃ ws : List String, ws.Nodup ∧ count ≤ ws.length ∧
      ∀ s ∈ ws, s ∈ sample count xs.length accept ∧
        s.length = xs.length ∧ stringSubtypeFlags s = stringSubtypeFlags (String.ofList xs) := by
  let p := xs.map stringCharacterProfile
  have hmem (ws : List Char) (h : ws ∈ substitutions count p) :
      String.ofList ws ∈ sample count xs.length accept := by
    refine List.mem_flatMap.mpr ⟨_, skeleton_mem xs, ?_⟩
    simp only [haccept, ite_true]
    exact List.mem_map_of_mem h
  rcases substitutions_cover count xs with h | h
  · exact .inl (hmem _ h)
  · right
    refine ⟨(substitutions count p).map String.ofList,
      (nodup_substitutions count p).map _ (fun _ _ hn eq => hn (String.ofList_inj.mp eq)),
      by simpa using h, ?_⟩
    intro s hs
    obtain ⟨ws, hw, rfl⟩ := List.mem_map.mp hs
    have he := substitutions_profile hw
    refine ⟨hmem _ hw, ?_, stringSubtypeFlags_eq_of_profile he⟩
    simpa [p] using congrArg List.length he

#print axioms sample_cover

end Sabrina.OWL2.SROIQD.Termination.StringLengthCells
