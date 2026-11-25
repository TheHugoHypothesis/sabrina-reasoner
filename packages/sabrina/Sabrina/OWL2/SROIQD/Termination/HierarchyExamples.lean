import Sabrina.OWL2.SROIQD.Termination.OWLHierarchy
import Sabrina.OWL2.SROIQD.Termination.TextbookHierarchy

namespace Sabrina.OWL2.RoleHierarchy

open Sabrina.ALC (OrientedRole RoleTheory roleClosure)
open Sabrina.RoleChains (Rank Ranked)
open Sabrina.RoleChains.SimpleRoles (below_iff_reachable)

private theorem written_of_disjoint_comparisons (rules : RoleTheory) (chains : List PropertyChain)
    (comparisons : List (String × OrientedRole))
    (hdisjoint : ∀ a ∈ comparisons, ∀ b ∈ comparisons, a.2.1 ≠ b.1)
    (hback : ∀ e ∈ comparisons, (e.2, (e.1, false)) ∉ roleClosure rules ∧
      (e.2, (e.1, true)) ∉ roleClosure rules)
    (hshape : ∀ c ∈ chains, 2 ≤ c.body.length ∧
      ∀ r ∈ c.body, (r.1, c.head) ∈ comparisons) :
    WrittenRegular rules chains := by
  let lt := fun (r s : OrientedRole) => (r.1, s) ∈ comparisons
  refine ⟨lt, ?_, ?_, fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro r hr
    exact hdisjoint _ hr _ hr rfl
  · intro r s t hrs hst
    exact (hdisjoint _ hrs _ hst rfl).elim
  · intro r s hlt hrev
    rcases below_iff_reachable.mpr hrev with rfl | hrev
    · exact hdisjoint _ hlt _ hlt rfl
    · obtain ⟨r, _ | _⟩ := r
      · exact (hback _ hlt).1 hrev
      · exact (hback _ hlt).2 hrev
  · intro c hc
    exact ⟨(hshape c hc).1, .inr ⟨c.body, .plain _, (hshape c hc).2⟩⟩

private def subRole (r s : String) : Axiom := .subObjectProperty (.named r) (.named s)
private def subChain (word : List String) (r : String) : Axiom :=
  .subObjectPropertyChain (word.map ObjectProperty.named) (.named r)

/-- Both strict comparisons pass the printed OWL test individually. Together
with both unary edges, they form a cycle with a strict dependency. -/
def alternatingHierarchy : Ontology :=
  [subChain ["r", "r"] "s", subChain ["t", "t"] "u", subRole "s" "t", subRole "u" "r"]

theorem alternatingHierarchy_writtenRegular : WrittenOntologyRegular alternatingHierarchy := by
  apply written_of_disjoint_comparisons _ _ [("r", ("s", false)), ("t", ("u", false))]
  · decide
  · decide
  · decide

private theorem alternatingHierarchy_rank_impossible (rules : RoleTheory) (chains : List RoleChains.Chain)
    (hst : (("s", false), ("t", false)) ∈ rules)
    (hur : (("u", false), ("r", false)) ∈ rules)
    (hrs : RoleChains.Chain.named ["r", "r"] "s" ∈ chains)
    (htu : RoleChains.Chain.named ["t", "t"] "u" ∈ chains) :
    ∀ rank, ¬ Ranked rank rules chains := by
  intro rank h
  have hrlt : rank "r" < rank "s" := h.lt_of_head_absent hrs (by decide)
    (show ("r", false) ∈ (RoleChains.Chain.named ["r", "r"] "s").body by decide)
  have htlt : rank "t" < rank "u" := h.lt_of_head_absent htu (by decide)
    (show ("t", false) ∈ (RoleChains.Chain.named ["t", "t"] "u").body by decide)
  have hst := h.1 _ _ hst
  have hur := h.1 _ _ hur
  change rank "s" ≤ rank "t" at hst
  change rank "u" ≤ rank "r" at hur
  omega

theorem alternatingHierarchy_no_rank :
    ¬ ∃ rank, Ranked rank (unaryEdges alternatingHierarchy)
      ((propertyChains alternatingHierarchy).map PropertyChain.orient) := by
  exact fun ⟨rank, h⟩ =>
    alternatingHierarchy_rank_impossible _ _ (by decide) (by decide) (by decide) (by decide) rank h

theorem alternatingHierarchy_normalized_no_rank {defs p}
    (hnorm : Normalize.normalizeWithDefs alternatingHierarchy = some (defs, p)) :
    ∀ rank, RoleChains.checkRegular rank p.rules p.chains = false := by
  let q : SROIQD.Problem := {
    rules := [(("u", false), ("r", false)), (("s", false), ("t", false))]
    chains := [RoleChains.Chain.named ["t", "t"] "u", RoleChains.Chain.named ["r", "r"] "s"] }
  have hq : Normalize.normalizeWithDefs alternatingHierarchy = some ([], q) := rfl
  rw [hq] at hnorm
  have hp : p = q := (Prod.mk.inj (Option.some.inj hnorm)).2.symm
  rw [hp]
  intro rank
  exact Bool.eq_false_iff.mpr fun h =>
    alternatingHierarchy_rank_impossible _ _ (by decide) (by decide) (by decide) (by decide)
      rank (RoleChains.checkRegular_sound h)

/-- Stefanoni (2015), Chapter 12, Example 12.2. The literature establishes
nonregularity of the generated language. Here we check written admission
and failure of a numeric rank. -/
def stefanoniHierarchy : Ontology :=
  [subChain ["a", "s", "b"] "r", subRole "r'" "s",
   subChain ["a'", "s'", "b'"] "r'", subRole "r" "s'"]

theorem stefanoniHierarchy_writtenRegular : WrittenOntologyRegular stefanoniHierarchy := by
  apply written_of_disjoint_comparisons _ _
    [("a", ("r", false)), ("s", ("r", false)), ("b", ("r", false)),
     ("a'", ("r'", false)), ("s'", ("r'", false)), ("b'", ("r'", false))]
  · decide
  · decide
  · decide

theorem stefanoniHierarchy_no_rank :
    ¬ ∃ rank, Ranked rank (unaryEdges stefanoniHierarchy)
      ((propertyChains stefanoniHierarchy).map PropertyChain.orient) := by
  rintro ⟨rank, h⟩
  have hrs : rank "r" ≤ rank "s'" :=
    h.1 ("r", false) ("s'", false) (by decide)
  have hrs' : rank "r'" ≤ rank "s" :=
    h.1 ("r'", false) ("s", false) (by decide)
  have hs : rank "s" < rank "r" := h.lt_of_head_absent
    (c := RoleChains.Chain.named ["a", "s", "b"] "r") (by decide) (by decide)
    (r := ("s", false)) (by decide)
  have hs' : rank "s'" < rank "r'" := h.lt_of_head_absent
    (c := RoleChains.Chain.named ["a'", "s'", "b'"] "r'") (by decide) (by decide)
    (r := ("s'", false)) (by decide)
  omega

#print axioms alternatingHierarchy_writtenRegular
#print axioms alternatingHierarchy_normalized_no_rank
#print axioms stefanoniHierarchy_writtenRegular
#print axioms stefanoniHierarchy_no_rank

end Sabrina.OWL2.RoleHierarchy

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

open Sabrina.RoleChains (Ranked)

def unaryCycle : List Inclusion := [⟨.named "r", [], "s"⟩, ⟨.named "s", [], "r"⟩]

theorem unaryCycle_ranked : Ranked (fun _ => 0) (hierarchyRules unaryCycle) (hierarchyChains unaryCycle) :=
  Sabrina.RoleChains.checkRegular_sound (by decide)

theorem unaryCycle_not_regular : ¬ Regular unaryCycle := by
  rintro ⟨lt, hirr, htrans, h⟩
  have hrs := unary_regularFor (h ⟨.named "r", [], "s"⟩ (by decide))
  have hsr := unary_regularFor (h ⟨.named "s", [], "r"⟩ (by decide))
  simp only [reduceCtorEq, false_or] at hrs hsr
  exact hirr _ (htrans _ _ _ hrs hsr)

def converseRecursion : List Inclusion := [⟨.inverse "r", [.inverse "r"], "r"⟩]

theorem converseRecursion_regular : Regular converseRecursion := by
  let lt := fun a b => a = Role.inverse "r" ∧ b = Role.named "r"
  refine ⟨lt, ?_, ?_, ?_⟩
  · rintro x ⟨rfl, h⟩
    cases h
  · rintro _ _ _ ⟨_, rfl⟩ ⟨h, _⟩
    cases h
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact .inr (.inr (.inl (by decide)))

theorem converseRecursion_no_rank :
    ¬ ∃ rank, Ranked rank (hierarchyRules converseRecursion) (hierarchyChains converseRecursion) := by
  rintro ⟨rank, h⟩
  have hn : rank "r" < rank "r" := h.lt_of_head_absent
    (c := ⟨[("r", true), ("r", true)], "r"⟩) (by decide) (by decide)
    (r := ("r", true)) (by decide)
  exact Nat.lt_irrefl _ hn

#print axioms unaryCycle_ranked
#print axioms unaryCycle_not_regular
#print axioms converseRecursion_regular
#print axioms converseRecursion_no_rank

end Sabrina.OWL2.SROIQD.TextbookSRIQ
