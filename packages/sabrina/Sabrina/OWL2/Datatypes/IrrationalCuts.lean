import Init.Data.Rat.Lemmas
import Init.Data.List.Lemmas
import Init.Omega

/-! Irrational Dedekind cuts of the rationals. The last condition excludes
rational cuts by requiring the upper part to have no least element. -/

namespace Sabrina.OWL2.Datatypes

structure IrrationalCut where
  lower : Rat → Prop
  inhabited : ∃ q, lower q
  proper : ∃ q, ¬ lower q
  downward : ∀ {p q}, p < q → lower q → lower p
  noGreatest : ∀ {q}, lower q → ∃ r, q < r ∧ lower r
  noLeastUpper : ∀ {q}, ¬ lower q → ∃ r, r < q ∧ ¬ lower r

namespace IrrationalCut

private theorem lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) : a < c :=
  Rat.not_le.mp (fun h => Rat.not_le.mpr hab (Rat.le_trans (Rat.le_of_lt hbc) h))

private theorem lt_le_trans {a b c : Rat} (hab : a < b) (hbc : b ≤ c) : a < c :=
  Rat.not_le.mp (fun h => Rat.not_le.mpr hab (Rat.le_trans hbc h))

private theorem le_lt_trans {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Rat.not_le.mp (fun h => Rat.not_le.mpr hbc (Rat.le_trans h hab))

theorem separated (c : IrrationalCut) {a b : Rat} (ha : c.lower a) (hb : ¬ c.lower b) : a < b := by
  apply Rat.not_le.mp
  intro h
  by_cases he : a = b
  · exact hb (he ▸ ha)
  · have ht : b < a := Rat.not_le.mp fun h' => he (Rat.le_antisymm h' h)
    exact hb (c.downward ht ha)

private def mid (a b : Rat) : Rat := (a + b) / 2

private theorem mid_between {a b : Rat} (h : a < b) : a < mid a b ∧ mid a b < b := by
  have two : (2 : Rat) = 1 + 1 := by
    apply Rat.ext <;> simp [Rat.add_def]
  constructor
  · rw [mid, Rat.lt_div_iff (by decide : (0 : Rat) < 2),
      two, Rat.mul_add, Rat.mul_one]
    exact Rat.add_lt_add_left.mpr h
  · rw [mid, Rat.div_lt_iff (by decide : (0 : Rat) < 2),
      two, Rat.mul_add, Rat.mul_one]
    exact Rat.add_lt_add_right.mpr h

private structure Interval where
  lo : Rat
  hi : Rat
  nonempty : lo < hi

private def exclude (i : Interval) (q : Rat) : Interval :=
  let m := mid i.lo i.hi
  let h := mid_between i.nonempty
  if q < m then ⟨m, mid m i.hi, (mid_between h.2).1⟩
  else
    let n := mid i.lo m
    ⟨n, mid n m, (mid_between (mid_between h.1).2).1⟩

private theorem exclude_spec (i : Interval) (q : Rat) :
    i.lo < (exclude i q).lo ∧ (exclude i q).hi < i.hi ∧
      (q < (exclude i q).lo ∨ (exclude i q).hi < q) := by
  unfold exclude
  dsimp only
  split
  · rename_i h
    exact ⟨(mid_between i.nonempty).1, (mid_between (mid_between i.nonempty).2).2, .inl h⟩
  · rename_i h
    have hm := mid_between i.nonempty
    have hn := mid_between hm.1
    have ht := (mid_between hn.2).2
    exact ⟨hn.1, lt_trans ht hm.2, .inr (lt_le_trans ht (Rat.not_lt.mp h))⟩

private theorem foldExclude_spec (qs : List Rat) (i : Interval) :
    i.lo ≤ (qs.foldl exclude i).lo ∧ (qs.foldl exclude i).hi ≤ i.hi ∧
      ∀ q ∈ qs, q < (qs.foldl exclude i).lo ∨ (qs.foldl exclude i).hi < q := by
  induction qs generalizing i with
  | nil => simp
  | cons q rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨hlo, hhi, hex⟩ := exclude_spec i q
    obtain ⟨hlo', hhi', hr⟩ := ih (exclude i q)
    refine ⟨Rat.le_trans (Rat.le_of_lt hlo) hlo', Rat.le_trans hhi' (Rat.le_of_lt hhi), ?_⟩
    intro r hm
    rcases List.mem_cons.mp hm with rfl | ht
    · exact hex.imp (fun h => lt_le_trans h hlo') (fun h => le_lt_trans hhi' h)
    · exact hr r ht

private def rationals (n : Nat) : List Rat :=
  (List.range (n + 1)).flatMap fun a =>
    (List.range (n + 1)).flatMap fun b => [mkRat (Int.ofNat a) b, mkRat (-Int.ofNat a) b]

private theorem mem_rationals (q : Rat) : q ∈ rationals (max q.num.natAbs q.den) := by
  refine List.mem_flatMap.mpr ⟨q.num.natAbs, List.mem_range.mpr (by omega), ?_⟩
  refine List.mem_flatMap.mpr ⟨q.den, List.mem_range.mpr (by omega), ?_⟩
  rcases Int.natAbs_eq q.num with h | h
  · exact List.mem_cons.mpr (.inl (q.mkRat_self.symm.trans (congrArg (mkRat · q.den) h)))
  · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr
      (q.mkRat_self.symm.trans (congrArg (mkRat · q.den) h))))

private def nested (i : Interval) : Nat → Interval
  | 0 => i
  | n + 1 => (rationals n).foldl exclude (nested i n)

private theorem nested_monotone (i : Interval) {m n : Nat} (h : m ≤ n) :
    (nested i m).lo ≤ (nested i n).lo ∧ (nested i n).hi ≤ (nested i m).hi := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst m
      exact ⟨Rat.le_refl, Rat.le_refl⟩
    · obtain ⟨hl, hu⟩ := ih (by omega)
      obtain ⟨hl', hu', _⟩ := foldExclude_spec (rationals n) (nested i n)
      exact ⟨Rat.le_trans hl hl', Rat.le_trans hu' hu⟩

private theorem nested_separated (i : Interval) (m n : Nat) :
    (nested i m).lo < (nested i n).hi := by
  rcases Nat.le_total m n with h | h
  · exact le_lt_trans (nested_monotone i h).1 (nested i n).nonempty
  · exact lt_le_trans (nested i m).nonempty (nested_monotone i h).2

private def make (i : Interval) : IrrationalCut where
  lower q := ∃ n, q < (nested i n).lo
  inhabited := ⟨i.lo - 1, 0, by
    change i.lo - 1 < i.lo
    have h : (-1 : Rat) + i.lo < 0 + i.lo :=
      Rat.add_lt_add_right.mpr (by decide : (-1 : Rat) < 0)
    simpa only [Rat.zero_add, Rat.sub_eq_add_neg, Rat.add_comm i.lo (-1)] using h⟩
  proper := ⟨i.hi, fun ⟨n, h⟩ => Rat.not_le.mpr h (Rat.le_of_lt (nested_separated i n 0))⟩
  downward := fun hp ⟨n, hq⟩ => ⟨n, lt_trans hp hq⟩
  noGreatest := fun ⟨n, hq⟩ => ⟨mid _ _, (mid_between hq).1, n, (mid_between hq).2⟩
  noLeastUpper := by
    intro q hq
    let n := max q.num.natAbs q.den
    rcases (foldExclude_spec (rationals n) (nested i n)).2.2 q (mem_rationals q) with h | h
    · exact (hq ⟨n + 1, h⟩).elim
    · refine ⟨(nested i (n + 1)).hi, h, ?_⟩
      rintro ⟨m, hm⟩
      exact Rat.not_le.mpr hm (Rat.le_of_lt (nested_separated i m (n + 1)))

/-- Every nonempty rational interval contains an irrational real cut. -/
theorem exists_between {a b : Rat} (h : a < b) :
    ∃ c : IrrationalCut, c.lower a ∧ ¬ c.lower b := by
  let i : Interval := ⟨mid a b, b, (mid_between h).2⟩
  exact ⟨make i, ⟨0, (mid_between h).1⟩, fun ⟨n, hn⟩ =>
    Rat.not_le.mpr hn (Rat.le_of_lt (nested_separated i n 0))⟩

#print axioms exists_between

end IrrationalCut
end Sabrina.OWL2.Datatypes
