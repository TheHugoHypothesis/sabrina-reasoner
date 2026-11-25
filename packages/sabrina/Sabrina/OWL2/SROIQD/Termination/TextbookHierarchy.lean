import Sabrina.OWL2.SROIQD.Termination.HierarchyRank
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQ

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

open Sabrina.ALC (OrientedRole RoleTheory)
open Sabrina.RoleChains (Chain ChainShape DependencyPath Ranked)

def Role.orient : Role → OrientedRole
  | .named name => (name, false)
  | .inverse name => (name, true)

@[simp] theorem Role.orient_name (r : Role) : r.orient.1 = r.name := by
  cases r <;> rfl

def hierarchyRules (hierarchy : List Inclusion) : RoleTheory :=
  hierarchy.filterMap fun a =>
    if a.rest.isEmpty then some (a.first.orient, (a.head, false)) else none

def hierarchyChains (hierarchy : List Inclusion) : List Chain :=
  hierarchy.filterMap fun a =>
    if a.rest.isEmpty then none else some ⟨a.body.map Role.orient, a.head⟩

/-- Definition 2 with an order that ignores orientation. This is a separate
condition from `Regular`, whose order ranges over oriented roles. -/
def ConverseRegular (hierarchy : List Inclusion) : Prop :=
  ∃ lt : String → String → Prop,
    (∀ r, ¬ lt r r) ∧
    (∀ r s t, lt r s → lt s t → lt r t) ∧
    ∀ a ∈ hierarchy, a.regularFor (fun r s => lt r.name s.name)

theorem ConverseRegular.regular {hierarchy : List Inclusion} (h : ConverseRegular hierarchy) :
    Regular hierarchy := by
  obtain ⟨lt, hirr, htrans, hshape⟩ := h
  exact ⟨fun a b => lt a.name b.name, fun a => hirr a.name,
    fun a b c => htrans a.name b.name c.name, hshape⟩

/-- For named chain letters, restricting a textbook order to named roles
has no effect on any of the required comparisons. -/
theorem Regular.converseRegular_of_named {hierarchy : List Inclusion} (h : Regular hierarchy)
    (hnamed : ∀ a ∈ hierarchy, ∀ r ∈ a.body, r = .named r.name) :
    ConverseRegular hierarchy := by
  obtain ⟨lt, hirr, htrans, hregular⟩ := h
  refine ⟨fun a b => lt (.named a) (.named b), fun a => hirr _,
    fun a b c => htrans (.named a) (.named b) (.named c), ?_⟩
  intro a ha
  have lift {r} (hr : r ∈ a.body) (hlt : lt r (.named a.head)) :
      lt (.named r.name) (.named a.head) :=
    (hnamed a ha r hr) ▸ hlt
  rcases hregular a ha with he | he | hlt | ⟨tail, hne, he, hlt⟩ | ⟨init, hne, he, hlt⟩
  · exact .inl he
  · exact .inr (.inl he)
  · exact .inr (.inr (.inl fun r hr => lift hr (hlt r hr)))
  · refine .inr (.inr (.inr (.inl ⟨tail, hne, he, fun r hr => ?_⟩)))
    exact lift (he.symm ▸ List.mem_cons_of_mem _ hr) (hlt r hr)
  · refine .inr (.inr (.inr (.inr ⟨init, hne, he, fun r hr => ?_⟩)))
    exact lift (he.symm ▸ List.mem_append_left _ hr) (hlt r hr)

theorem unary_regularFor {lt : Role → Role → Prop} {r : Role} {head : String}
    (h : (Inclusion.mk r [] head).regularFor lt) :
    r = .inverse head ∨ lt r (.named head) := by
  rcases h with h | h | h | ⟨rest, hne, he, _⟩ | ⟨rest, hne, he, _⟩
  · simp [Inclusion.body] at h
  · exact .inl (List.cons.inj h).1
  · exact .inr (h r (List.mem_cons_self ..))
  · exact (hne (List.cons.inj he).2.symm).elim
  · cases rest with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp [Inclusion.body] at he

private theorem chainDemand {lt : String → String → Prop} {a : Inclusion}
    (hlength : a.rest ≠ []) (h : a.regularFor fun r s => lt r.name s.name) :
    2 ≤ a.body.length ∧ ∃ lower,
      ChainShape (a.head, false) (a.body.map Role.orient) lower ∧
        ∀ r ∈ lower, lt r.1 a.head := by
  have hlen : 2 ≤ a.body.length := by
    cases he : a.rest <;> simp_all [Inclusion.body]
  have lift {rs : List Role} (hrs : ∀ r ∈ rs, lt r.name a.head) :
      ∀ r ∈ rs.map Role.orient, lt r.1 a.head := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    simpa using hrs s hs
  refine ⟨hlen, ?_⟩
  rcases h with he | he | hp | ⟨tail, _, he, hp⟩ | ⟨init, _, he, hp⟩
  · refine ⟨[], ?_, by simp⟩
    rw [he]
    exact .transitive
  · rw [he] at hlen
    simp at hlen
  · exact ⟨_, .plain _, lift hp⟩
  · refine ⟨tail.map Role.orient, ?_, lift hp⟩
    rw [he]
    exact .left _
  · refine ⟨init.map Role.orient, ?_, lift hp⟩
    rw [he, List.map_append]
    exact .right _

private theorem dependencyPath_order {lt : String → String → Prop}
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    {weak strict : List (String × String)}
    (hw : ∀ a b, (a, b) ∈ weak → a = b ∨ lt a b)
    (hs : ∀ a b, (a, b) ∈ strict → lt a b)
    {i a b} (h : DependencyPath weak strict i a b) :
    if i then lt a b else a = b ∨ lt a b := by
  induction h with
  | refl => exact .inl rfl
  | weak h => exact hw _ _ h
  | strict h => exact hs _ _ h
  | @trans i j _ _ _ _ _ hi hj =>
    cases i <;> cases j <;> simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true,
      ite_false, ite_true] at hi hj ⊢
    · rcases hi with rfl | hi
      · exact hj
      · rcases hj with rfl | hj
        · exact .inr hi
        · exact .inr (htrans _ _ _ hi hj)
    · rcases hi with rfl | hi
      · exact hj
      · exact htrans _ _ _ hi hj
    · rcases hj with rfl | hj
      · exact hi
      · exact htrans _ _ _ hi hj
    · exact htrans _ _ _ hi hj

/-- A converse-invariant textbook order supplies an admitted numeric rank
for the compiled inclusions. Symmetry gives an equal-rank unary edge. -/
theorem ConverseRegular.exists_ranked {hierarchy : List Inclusion}
    (h : ConverseRegular hierarchy) :
    ∃ rank, Ranked rank (hierarchyRules hierarchy) (hierarchyChains hierarchy) := by
  classical
  obtain ⟨lt, hirr, htrans, htext⟩ := h
  have hchain (c : Chain) (hc : c ∈ hierarchyChains hierarchy) :
      2 ≤ c.body.length ∧ ∃ rest, ChainShape (c.head, false) c.body rest ∧
        ∀ r ∈ rest, lt r.1 c.head := by
    obtain ⟨a, ha, hc⟩ := List.mem_filterMap.mp hc
    cases hrest : a.rest with
    | nil => simp [hrest] at hc
    | cons r rs =>
      have hn : a.rest ≠ [] := by simp [hrest]
      simp only [hrest, List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.some.injEq] at hc
      subst c
      obtain ⟨hlen, hshape⟩ := chainDemand hn (htext a ha)
      exact ⟨by simpa using hlen, hshape⟩
  have hchoice (c : Chain) : ∃ rest, c ∈ hierarchyChains hierarchy →
      ChainShape (c.head, false) c.body rest ∧ ∀ r ∈ rest, lt r.1 c.head := by
    by_cases hc : c ∈ hierarchyChains hierarchy
    · obtain ⟨rest, hshape⟩ := (hchain c hc).2
      exact ⟨rest, fun _ => hshape⟩
    · exact ⟨[], fun he => (hc he).elim⟩
  let lower c := Classical.choose (hchoice c)
  have hlower c hc := Classical.choose_spec (hchoice c) hc
  apply Sabrina.RoleChains.exists_ranked_iff_acyclicDependencies.mpr
  refine ⟨lower, fun c hc => ⟨(hchain c hc).1, (hlower c hc).1⟩, ?_⟩
  have hw (u v : String) (h : (u, v) ∈
      Sabrina.RoleChains.weakDependencies (hierarchyRules hierarchy)) : u = v ∨ lt u v := by
    obtain ⟨⟨r, s⟩, hrs, he⟩ := List.mem_map.mp h
    cases he
    obtain ⟨⟨first, rest, name⟩, ha, hrs⟩ := List.mem_filterMap.mp hrs
    cases rest with
    | nil =>
      change some (first.orient, (name, false)) = some (r, s) at hrs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrs)
      rcases unary_regularFor (htext ⟨first, [], name⟩ ha) with rfl | hlt
      · exact .inl rfl
      · exact .inr (by simpa [Role.name] using hlt)
    | cons _ _ => contradiction
  have hs (u v : String) (h : (u, v) ∈
      Sabrina.RoleChains.strictDependencies (hierarchyChains hierarchy) lower) : lt u v := by
    obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
    obtain ⟨r, hr, he⟩ := List.mem_map.mp h
    cases he
    exact (hlower c hc).2 r hr
  exact fun x cycle => hirr x (dependencyPath_order htrans hw hs cycle)

theorem Regular.exists_ranked_of_named {hierarchy : List Inclusion} (h : Regular hierarchy)
    (hnamed : ∀ a ∈ hierarchy, ∀ r ∈ a.body, r = .named r.name) :
    ∃ rank, Ranked rank (hierarchyRules hierarchy) (hierarchyChains hierarchy) :=
  (h.converseRegular_of_named hnamed).exists_ranked

#print axioms ConverseRegular.exists_ranked
#print axioms Regular.exists_ranked_of_named

end Sabrina.OWL2.SROIQD.TextbookSRIQ
