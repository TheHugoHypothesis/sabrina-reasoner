import Init.Data.List.Erase
import Std.Data.HashSet.Lemmas

namespace Sabrina.ALCH

/-- Each pair `(r, s)` asserts that every `r` edge is an `s` edge. -/
abbrev HierarchyOf (α : Type) := List (α × α)
abbrev Hierarchy := HierarchyOf String

variable {α : Type} [BEq α] [LawfulBEq α]

private def extend (edges : HierarchyOf α) (pivot : α) : HierarchyOf α :=
  let outgoing := edges.filter fun e => e.1 == pivot
  (edges ++ (edges.filter fun e => e.2 == pivot).flatMap fun e =>
    outgoing.map fun f => (e.1, f.2)).eraseDups

private theorem mem_extend {edges : HierarchyOf α} {p a b : α} :
    (a, b) ∈ extend edges p ↔ (a, b) ∈ edges ∨ ((a, p) ∈ edges ∧ (p, b) ∈ edges) := by
  simp only [extend, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_filter,
    List.mem_map, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨⟨x, y⟩, ⟨he, hy⟩, ⟨⟨z, w⟩, ⟨hf, hz⟩, hx, hw⟩⟩)
    · exact Or.inl h
    · change x = a at hx
      change y = p at hy
      change z = p at hz
      change w = b at hw
      subst x; subst y; subst z; subst w
      exact Or.inr ⟨he, hf⟩
  · rintro (h | ⟨he, hf⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(a, p), ⟨he, rfl⟩, (p, b), ⟨hf, rfl⟩, rfl, rfl⟩

private def closeThrough (edges : HierarchyOf α) : List α → HierarchyOf α
  | [] => edges
  | p :: rest => extend (closeThrough edges rest) p

private theorem mem_closeThrough {edges : HierarchyOf α} {a b : α} (pivots : List α)
    (h : (a, b) ∈ edges) : (a, b) ∈ closeThrough edges pivots := by
  induction pivots with
  | nil => exact h
  | cons _ _ ih => exact mem_extend.mpr (Or.inl ih)

private theorem closeThrough_trans {edges : HierarchyOf α} {p : α} {pivots : List α}
    (hp : p ∈ pivots) {a b : α} (ha : (a, p) ∈ closeThrough edges pivots)
    (hb : (p, b) ∈ closeThrough edges pivots) : (a, b) ∈ closeThrough edges pivots := by
  induction pivots generalizing a b with
  | nil => simp at hp
  | cons t rest ih =>
    rcases List.mem_cons.mp hp with rfl | hrest
    · exact mem_extend.mpr (Or.inr ⟨(mem_extend.mp ha).elim id And.left,
        (mem_extend.mp hb).elim id And.right⟩)
    · rcases mem_extend.mp ha with h₁ | ⟨hat, htp⟩
      · rcases mem_extend.mp hb with h₂ | ⟨hpt, htb⟩
        · exact mem_extend.mpr (Or.inl (ih hrest h₁ h₂))
        · exact mem_extend.mpr (Or.inr ⟨ih hrest h₁ hpt, htb⟩)
      · rcases mem_extend.mp hb with h₂ | ⟨_, htb⟩
        · exact mem_extend.mpr (Or.inr ⟨hat, ih hrest htp h₂⟩)
        · exact mem_extend.mpr (Or.inr ⟨hat, htb⟩)

private theorem closeThrough_sound {edges : HierarchyOf α} {R : α → α → Prop}
    (h : ∀ {a b}, (a, b) ∈ edges → R a b)
    (trans : ∀ {a p b}, R a p → R p b → R a b) (pivots : List α) {a b : α}
    (hab : (a, b) ∈ closeThrough edges pivots) : R a b := by
  induction pivots generalizing a b with
  | nil => exact h hab
  | cons p rest ih =>
    rcases mem_extend.mp hab with hab | ⟨hap, hpb⟩
    · exact ih hab
    · exact trans (ih hap) (ih hpb)

/-- Floyd–Warshall's pivot recurrence over the explicit role pairs.
    The endpoints of asserted inclusions are the pivots. -/
def close (edges : HierarchyOf α) : HierarchyOf α :=
  closeThrough edges (edges.flatMap fun (a, b) => [a, b]).eraseDups

section Indexed

variable [Hashable α] [LawfulHashable α]

private def dedupLoop : List α → Std.HashSet α → List α → List α
  | [], _, kept => kept.reverse
  | x :: xs, seen, kept =>
    if seen.contains x then dedupLoop xs seen kept
    else dedupLoop xs (seen.insert x) (x :: kept)

private theorem dedupLoop_eq (xs kept : List α) (seen : Std.HashSet α)
    (hseen : ∀ x, seen.contains x = kept.contains x) :
    dedupLoop xs seen kept = List.eraseDupsBy.loop (· == ·) xs kept := by
  induction xs generalizing seen kept with
  | nil => rfl
  | cons x xs ih =>
    simp only [dedupLoop, List.eraseDupsBy.loop, ← List.contains_eq_any_beq, ← hseen x]
    cases hx : seen.contains x with
    | true => exact ih _ _ hseen
    | false =>
      apply ih
      intro y
      simp only [Std.HashSet.contains_insert, List.contains_cons, hseen y]
      rw [Bool.beq_comm (a := x) (b := y)]

private def dedupIndexed (xs : List α) : List α :=
  dedupLoop xs (∅ : Std.HashSet α) []

private theorem dedupIndexed_eq (xs : List α) :
    dedupIndexed xs = xs.eraseDups :=
  dedupLoop_eq xs [] _ (by simp)

private def closeThroughIndexed (edges : HierarchyOf α) : List α → HierarchyOf α
  | [] => edges
  | p :: rest =>
    let cur := closeThroughIndexed edges rest
    let outgoing := cur.filter (fun e => e.1 == p)
    dedupIndexed (cur ++ (cur.filter (fun e => e.2 == p)).flatMap fun e =>
      outgoing.map fun f => (e.1, f.2))

/-- Compute the same ordered closure using indexed duplicate checks at each pivot. -/
def closeIndexed (edges : HierarchyOf α) : HierarchyOf α :=
  closeThroughIndexed edges (dedupIndexed (edges.flatMap fun (a, b) => [a, b]))

theorem closeIndexed_eq (edges : HierarchyOf α) : closeIndexed edges = close edges := by
  have stepEq (pivots : List α) : closeThroughIndexed edges pivots = closeThrough edges pivots := by
    induction pivots with
    | nil => rfl
    | cons p rest ih => simp only [closeThroughIndexed, closeThrough, dedupIndexed_eq, ih, extend]
  simp only [closeIndexed, close, dedupIndexed_eq, stepEq]

end Indexed

theorem mem_close {edges : HierarchyOf α} {a b : α} (h : (a, b) ∈ edges) :
    (a, b) ∈ close edges := mem_closeThrough _ h

theorem close_step {edges : HierarchyOf α} {a p b : α}
    (ha : (a, p) ∈ close edges) (hb : (p, b) ∈ edges) : (a, b) ∈ close edges :=
  closeThrough_trans (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(p, b), hb, by simp⟩))
    ha (mem_close hb)

theorem close_prepend {edges : HierarchyOf α} {a p b : α}
    (ha : (a, p) ∈ edges) (hb : (p, b) ∈ close edges) : (a, b) ∈ close edges :=
  closeThrough_trans (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(a, p), ha, by simp⟩))
    (mem_close ha) hb

theorem close_sound {edges : HierarchyOf α} {R : α → α → Prop}
    (h : ∀ {a b}, (a, b) ∈ edges → R a b)
    (trans : ∀ {a p b}, R a p → R p b → R a b) {a b : α}
    (hab : (a, b) ∈ close edges) : R a b := closeThrough_sound h trans _ hab

theorem close_trans {edges : HierarchyOf α} {a p b : α}
    (ha : (a,p) ∈ close edges) (hb : (p,b) ∈ close edges) : (a,b) ∈ close edges := by
  let endpoints := edges.flatMap fun (r,s) => [r,s]
  have hp : p ∈ endpoints := (close_sound
    (R := fun r s => r ∈ endpoints ∧ s ∈ endpoints)
    (fun {r s} h => ⟨List.mem_flatMap.mpr ⟨(r,s), h, by simp⟩,
      List.mem_flatMap.mpr ⟨(r,s), h, by simp⟩⟩)
    (fun h₁ h₂ => ⟨h₁.1,h₂.2⟩) ha).2
  exact closeThrough_trans (List.mem_eraseDups.mpr hp) ha hb

def properSubroles (closed : HierarchyOf α) (r : α) : List α :=
  (((closed.filter fun e => e.2 == r).map Prod.fst).eraseDups).filter (· != r)

theorem mem_properSubroles {closed : HierarchyOf α} {s r : α} :
    s ∈ properSubroles closed r ↔ (s, r) ∈ closed ∧ s ≠ r := by
  simp only [properSubroles, List.mem_filter, List.mem_eraseDups, List.mem_map, beq_iff_eq,
    bne_iff_ne]
  constructor
  · rintro ⟨⟨⟨a, b⟩, ⟨he, hb⟩, ha⟩, hn⟩
    change a = s at ha
    change b = r at hb
    subst a; subst b
    exact ⟨he, hn⟩
  · rintro ⟨he, hn⟩
    exact ⟨⟨(s, r), ⟨he, rfl⟩, rfl⟩, hn⟩

def subroles (closed : HierarchyOf α) (r : α) : List α :=
  r :: properSubroles closed r

theorem mem_subroles {closed : HierarchyOf α} {s r : α} :
    s ∈ subroles closed r ↔ s = r ∨ (s, r) ∈ closed := by
  rw [subroles, List.mem_cons, mem_properSubroles]
  by_cases h : s = r <;> simp [h]

end Sabrina.ALCH
