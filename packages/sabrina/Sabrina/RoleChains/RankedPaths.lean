import Sabrina.RoleChains.Regularity
import Sabrina.RoleChains.RegularBlock

namespace Sabrina.RoleChains.RankedPaths

open Sabrina.ALC
open TransitivePaths (Below flipWord)

inductive Pattern where
  | base (word : Word)
  | pre (word : Word)
  | post (word : Word)
  | transitive
  deriving DecidableEq, Repr

def Pattern.body (r : OrientedRole) : Pattern → Word
  | .base w => w
  | .pre w => w ++ [r]
  | .post w => r :: w
  | .transitive => [r,r]

def Pattern.lower : Pattern → Word
  | .base w | .pre w | .post w => w
  | .transitive => []

def Pattern.flip : Pattern → Pattern
  | .base w => .base (flipWord w)
  | .pre w => .post (flipWord w)
  | .post w => .pre (flipWord w)
  | .transitive => .transitive

theorem flipWord_append (u v : Word) : flipWord (u ++ v) = flipWord v ++ flipWord u := by
  simp [flipWord]

@[simp] theorem flipWord_involution (w : Word) : flipWord (flipWord w) = w := by
  simp [flipWord, List.map_reverse, List.map_map, Function.comp_def]

theorem Pattern.flip_body (p : Pattern) (r : OrientedRole) :
    p.flip.body (converse r) = flipWord (p.body r) := by
  cases p <;> simp [Pattern.flip, Pattern.body, flipWord]

@[simp] theorem Pattern.flip_flip (p : Pattern) : p.flip.flip = p := by
  cases p <;> simp [Pattern.flip]

structure Rule where
  head : OrientedRole
  pattern : Pattern
  deriving DecidableEq, Repr

def Rule.flip (r : Rule) : Rule := ⟨converse r.head, r.pattern.flip⟩

@[simp] theorem Rule.flip_flip (r : Rule) : r.flip.flip = r := by
  cases r
  simp [Rule.flip]

def shape (c : Chain) : Pattern :=
  if c.body = [(c.head,false),(c.head,false)] then .transitive
  else if c.body.head? = some (c.head,false) then .post ((c.body.drop 1))
  else if c.body.getLast? = some (c.head,false) then .pre (c.body.dropLast)
  else .base (c.body)

theorem shape_body (c : Chain) :
    (shape c).body (c.head,false) = c.body := by
  unfold shape
  split
  · rename_i h
    rw [h]
    rfl
  · split
    · rename_i h
      cases hb : c.body with
      | nil => simp [hb] at h
      | cons r rest =>
        simp only [hb, List.head?_cons, Option.some.injEq] at h
        subst r
        simp [Pattern.body]
    · split
      · rename_i h
        have hn : c.body ≠ [] := by
          intro he
          simp [he] at h
        have he := List.dropLast_concat_getLast hn
        have hl : c.body.getLast hn = (c.head,false) := by
          simpa [List.getLast?_eq_some_getLast hn] using h
        rw [hl] at he
        simpa [Pattern.body] using he
      · rfl

def normalize (chains : List Chain) : List Rule :=
  let rs := chains.map fun c => (⟨(c.head,false), shape c⟩ : Rule)
  rs ++ rs.map Rule.flip

theorem normalize_flip {chains r} (h : r ∈ normalize chains) : r.flip ∈ normalize chains := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨r, h, rfl⟩)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    simpa only [normalize, Rule.flip_flip] using List.mem_append_left ((chains.map fun c =>
      (⟨(c.head,false), shape c⟩ : Rule)).map Rule.flip) hr

theorem normalize_original {chains c} (h : c ∈ chains) :
    (⟨(c.head,false), shape c⟩ : Rule) ∈ normalize chains :=
  List.mem_append_left _ (List.mem_map.mpr ⟨c,h,rfl⟩)

private theorem lower_shape {rank : Rank} {c : Chain}
    (h : c.body = [(c.head,false),(c.head,false)] ∨
      (∀ r ∈ c.body, rank r.1 < rank c.head) ∨
      (∃ rest, c.body = (c.head,false) :: rest ∧ ∀ r ∈ rest, rank r.1 < rank c.head) ∨
      (∃ rest, c.body = rest ++ [(c.head,false)] ∧ ∀ r ∈ rest, rank r.1 < rank c.head))
    {r : OrientedRole} (hr : r ∈ (shape c).lower) : rank r.1 < rank c.head := by
  unfold shape at hr
  split at hr
  · simp [Pattern.lower] at hr
  · rename_i notTrans
    rcases h with hc | hc | ⟨rest, he, hl⟩ | ⟨rest, he, hl⟩
    · exact (notTrans hc).elim
    · have hm : r ∈ c.body := by
        split at hr
        · exact List.mem_of_mem_drop hr
        · split at hr
          · exact List.dropLast_subset _ hr
          · exact hr
      exact hc r hm
    · simp only [he, List.head?_cons, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
        Pattern.lower] at hr
      exact hl r hr
    · cases rest with
      | nil => simp [he, Pattern.lower] at hr
      | cons a tail =>
        have ha := hl a (List.mem_cons_self ..)
        have hne : a ≠ (c.head,false) := fun hp => (Nat.lt_irrefl _ (hp ▸ ha))
        have hn : c.body.head? ≠ some (c.head,false) := by simpa [he] using hne
        have hlst : c.body.getLast? = some (c.head,false) := by
          rw [he]
          change ((a :: tail) ++ [(c.head,false)]).getLast? = _
          rw [List.getLast?_append]; rfl
        rw [ite_eq_right hn, ite_eq_left hlst] at hr
        have hd : c.body.dropLast = a :: tail := by
          rw [he]
          change ((a :: tail) ++ [(c.head,false)]).dropLast = _
          rw [List.dropLast_append_cons]; simp only [List.dropLast_singleton, List.append_nil]
        rw [Pattern.lower, hd] at hr
        exact hl r hr

theorem normalize_lower {rank rules chains} (h : Ranked rank rules chains)
    {c : Rule} (hc : c ∈ normalize chains) {r : OrientedRole} (hr : r ∈ c.pattern.lower) :
    rank r.1 < rank c.head.1 := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    exact lower_shape (h.2 k hk).2 hr
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    cases hp : shape k with
    | transitive => simp [Rule.flip, hp, Pattern.flip, Pattern.lower] at hr
    | base w | pre w | post w =>
      simp only [Rule.flip, hp, Pattern.flip, Pattern.lower, flipWord, List.mem_reverse] at hr
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      exact lower_shape (h.2 k hk).2 (r := s) (by simpa [hp, Pattern.lower] using hs)

end Sabrina.RoleChains.RankedPaths
