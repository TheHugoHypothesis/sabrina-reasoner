import Sabrina.RoleChains.SimpleRoles

namespace Sabrina.RoleChains

open Sabrina.ALC (OrientedRole RoleTheory)

/-- The four recursive-chain forms used by the compiler. The final index
lists exactly the roles required to be strictly below the head in that form. -/
inductive ChainShape (head : OrientedRole) : List OrientedRole → List OrientedRole → Prop where
  | transitive : ChainShape head [head, head] []
  | plain (body) : ChainShape head body body
  | left (tail) : ChainShape head (head :: tail) tail
  | right (init) : ChainShape head (init ++ [head]) init

theorem chainShape_iff {head : OrientedRole} {word : List OrientedRole}
    {lower : OrientedRole → Prop} :
    (∃ rest, ChainShape head word rest ∧ ∀ r ∈ rest, lower r) ↔
      word = [head, head] ∨ (∀ r ∈ word, lower r) ∨
      (∃ rest, word = head :: rest ∧ ∀ r ∈ rest, lower r) ∨
      (∃ rest, word = rest ++ [head] ∧ ∀ r ∈ rest, lower r) := by
  constructor
  · rintro ⟨rest, hshape, hlower⟩
    cases hshape with
    | transitive => exact .inl rfl
    | plain _ => exact .inr (.inl hlower)
    | left rest => exact .inr (.inr (.inl ⟨rest, rfl, hlower⟩))
    | right rest => exact .inr (.inr (.inr ⟨rest, rfl, hlower⟩))
  · rintro (rfl | hall | ⟨rest, rfl, hlower⟩ | ⟨rest, rfl, hlower⟩)
    · exact ⟨[], .transitive, by simp⟩
    · exact ⟨word, .plain word, hall⟩
    · exact ⟨rest, .left rest, hlower⟩
    · exact ⟨rest, .right rest, hlower⟩

theorem ChainShape.lower_eq_body_of_head_absent {head : OrientedRole} {word rest}
    (h : ChainShape head word rest) (hhead : head ∉ word) : rest = word := by
  cases h <;> simp_all

theorem Ranked.lt_of_head_absent {rank rules chains} (h : Ranked rank rules chains)
    {c : Chain} (hc : c ∈ chains) (hhead : (c.head, false) ∉ c.body)
    {r : OrientedRole} (hr : r ∈ c.body) : rank r.1 < rank c.head := by
  obtain ⟨rest, hshape, hlower⟩ := chainShape_iff.mpr (h.2 c hc).2
  exact hlower r ((hshape.lower_eq_body_of_head_absent hhead).symm ▸ hr)

/-- Paths through unary (weak) and chain (strict) dependencies. The index
records whether the path uses at least one strict edge. -/
inductive DependencyPath (weak strict : List (String × String)) :
    Bool → String → String → Prop where
  | refl (v) : DependencyPath weak strict false v v
  | weak {a b} : (a, b) ∈ weak → DependencyPath weak strict false a b
  | strict {a b} : (a, b) ∈ strict → DependencyPath weak strict true a b
  | trans {i j a b c} : DependencyPath weak strict i a b →
      DependencyPath weak strict j b c → DependencyPath weak strict (i || j) a c

theorem DependencyPath.rank_le {weak strict : List (String × String)} {rank : Rank}
    (hw : ∀ a b, (a, b) ∈ weak → rank a ≤ rank b)
    (hs : ∀ a b, (a, b) ∈ strict → rank a < rank b)
    {i a b} (path : DependencyPath weak strict i a b) :
    if i then rank a < rank b else rank a ≤ rank b := by
  induction path with
  | refl => exact Nat.le_refl _
  | weak h => exact hw _ _ h
  | strict h => exact hs _ _ h
  | @trans i j _ _ _ _ _ hi hj =>
    cases i <;> cases j <;> simp at hi hj ⊢ <;> omega

private theorem countP_lt_of_witness {α : Type} {xs : List α} {p q : α → Bool}
    (hsub : ∀ x ∈ xs, p x → q x) (hex : ∃ x ∈ xs, q x ∧ ¬ p x) :
    xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at hex
  | cons a as ih =>
    have htail : ∀ x ∈ as, p x → q x := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
    obtain ⟨x, hx, hq, hn⟩ := hex
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hxs
    · have hp : p x = false := Bool.eq_false_iff.mpr hn
      have hle := List.countP_mono_left htail
      rw [hp, hq]
      simp
      omega
    · have hlt := ih htail ⟨x, hxs, hq, hn⟩
      have ha := hsub a (List.mem_cons_self ..)
      cases hp : p a <;> cases hqa : q a <;> simp_all <;> omega

/-- A mixed cycle exists exactly when no simultaneous weak and strict rank
assignment exists. In the reverse direction, count strict predecessors
among the finitely many sources of strict edges. -/
theorem dependencyRanks_iff {weak strict : List (String × String)} :
    (∃ rank : Rank, (∀ a b, (a, b) ∈ weak → rank a ≤ rank b) ∧
      (∀ a b, (a, b) ∈ strict → rank a < rank b)) ↔
    (∀ x, ¬ DependencyPath weak strict true x x) := by
  constructor
  · rintro ⟨rank, hw, hs⟩ x cycle
    exact Nat.lt_irrefl _ (cycle.rank_le hw hs)
  · intro hacyclic
    classical
    let sources := strict.map Prod.fst
    let pred (x u : String) : Bool := decide (DependencyPath weak strict true u x)
    let rank : Rank := fun x => sources.countP (pred x)
    have mono {a b : String} {i : Bool} (h : DependencyPath weak strict i a b) :
        ∀ u ∈ sources, pred a u → pred b u := by
      intro u _ hu
      exact decide_eq_true (DependencyPath.trans (of_decide_eq_true hu) h)
    refine ⟨rank, fun a b h => List.countP_mono_left (mono (.weak h)), ?_⟩
    intro a b h
    exact countP_lt_of_witness (mono (.strict h))
      ⟨a, List.mem_map_of_mem h, decide_eq_true (DependencyPath.strict h),
        fun ha => hacyclic a (of_decide_eq_true ha)⟩

def weakDependencies (rules : RoleTheory) : List (String × String) :=
  rules.map fun (r, s) => (r.1, s.1)

def strictDependencies (chains : List Chain) (lower : Chain → List OrientedRole) :
    List (String × String) :=
  chains.flatMap fun c => (lower c).map fun r => (r.1, c.head)

/-- The compiler's graph criterion on base names. Unary cycles are allowed.
Cycles containing a strict chain dependency are forbidden. -/
def HasAcyclicDependencies (rules : RoleTheory) (chains : List Chain) : Prop :=
  ∃ lower : Chain → List OrientedRole,
    (∀ c ∈ chains, 2 ≤ c.body.length ∧ ChainShape (c.head, false) c.body (lower c)) ∧
    ∀ x, ¬ DependencyPath (weakDependencies rules) (strictDependencies chains lower) true x x

theorem exists_ranked_iff_acyclicDependencies {rules : RoleTheory} {chains : List Chain} :
    (∃ rank, Ranked rank rules chains) ↔ HasAcyclicDependencies rules chains := by
  classical
  constructor
  · rintro ⟨rank, hunary, hchains⟩
    have hex (c : Chain) : ∃ rest, c ∈ chains →
        ChainShape (c.head, false) c.body rest ∧ ∀ r ∈ rest, rank r.1 < rank c.head := by
      by_cases hc : c ∈ chains
      · obtain ⟨rest, hrest⟩ := chainShape_iff.mpr (hchains c hc).2
        exact ⟨rest, fun _ => hrest⟩
      · exact ⟨[], fun h => (hc h).elim⟩
    let lower c := Classical.choose (hex c)
    have hrest (c : Chain) (hc : c ∈ chains) :=
      Classical.choose_spec (hex c) hc
    refine ⟨lower, fun c hc => ⟨(hchains c hc).1, (hrest c hc).1⟩, ?_⟩
    apply dependencyRanks_iff.mp
    refine ⟨rank, ?_, ?_⟩
    · intro a b ha
      obtain ⟨⟨r, s⟩, hrs, he⟩ := List.mem_map.mp ha
      cases he
      exact hunary r s hrs
    · intro a b ha
      obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp ha
      obtain ⟨r, hr, he⟩ := List.mem_map.mp h
      cases he
      exact (hrest c hc).2 r hr
  · rintro ⟨lower, hshape, hacyclic⟩
    obtain ⟨rank, hweak, hstrict⟩ := dependencyRanks_iff.mpr hacyclic
    refine ⟨rank, fun r s h => hweak _ _ (List.mem_map_of_mem h), ?_⟩
    intro c hc
    refine ⟨(hshape c hc).1, chainShape_iff.mp ⟨lower c, (hshape c hc).2, ?_⟩⟩
    intro r hr
    exact hstrict _ _ (List.mem_flatMap.mpr ⟨c, hc, List.mem_map_of_mem hr⟩)

theorem findRank_iff_acyclicDependencies {rules : RoleTheory} {chains : List Chain} :
    (findRank rules chains).isSome = true ↔ HasAcyclicDependencies rules chains :=
  findRank_iff.trans exists_ranked_iff_acyclicDependencies

#print axioms dependencyRanks_iff
#print axioms findRank_iff_acyclicDependencies

end Sabrina.RoleChains
