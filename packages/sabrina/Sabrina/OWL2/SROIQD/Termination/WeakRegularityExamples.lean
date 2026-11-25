import Sabrina.OWL2.SROIQD.Termination.WeakRegularity
import Sabrina.OWL2.SROIQD.Termination.HierarchyExamples
import Sabrina.OWL2.SROIQD.Termination.ChainAliases

namespace Sabrina.OWL2.RoleHierarchy.Stefanoni

open Sabrina.ALC (RoleTheory)
open Sabrina.RoleChains (Chain Ranked)

private theorem no_empty_path {r s} (h : NonemptyPath [] r s) : False := by
  induction h with
  | edge h => simp at h
  | trans _ _ ih _ => exact ih

/-- The literal printed side condition admits this chain. The graph has no
edges because it drops both orientations of the head as sources. -/
def converseChain : Chain := ⟨[("r", true), ("r", true)], "r"⟩

theorem converseChain_printed : WeaklyRegular .printed (compiledBox [] [converseChain]) := by
  refine ⟨?_, ?_⟩
  · intro r _ hp
    have he : graphEdges (compiledBox [] [converseChain]) = [] := by decide
    rw [he] at hp
    exact no_empty_path hp
  · intro a ha
    change a ∈ [_] at ha
    obtain rfl := List.mem_singleton.mp ha
    refine .inr (.inr ⟨_, .plain _, ?_⟩)
    change ∀ r ∈ converseChain.body, allowedLower .printed ("r", false) r
    intro r hr
    have he : r = ("r", true) := by simpa [converseChain] using hr
    subst r
    unfold allowedLower
    decide

theorem converseChain_no_rank : ¬ ∃ rank, Ranked rank [] [converseChain] := by
  rintro ⟨rank, h⟩
  have hn : rank "r" < rank "r" :=
    h.lt_of_head_absent (c := converseChain) (by decide) (by decide)
      (r := ("r", true)) (by decide)
  exact Nat.lt_irrefl _ hn

theorem converseChain_head_exclusion : ¬ WeaklyRegular .head (compiledBox [] [converseChain]) :=
  fun h => converseChain_no_rank
    (weaklyRegular_exists_ranked (by unfold Ordinary; decide) (by decide) h)

def compositeAliasRules : RoleTheory := [(("r", false), ("s", false)), (("s", false), ("r", false))]
def compositeAliasChain : Chain := Chain.named ["a", "b"] "r"

theorem compositeAlias_ranked : ∃ rank, Ranked rank compositeAliasRules [compositeAliasChain] := by
  refine ⟨fun r => if r = "r" ∨ r = "s" then 1 else 0, ?_⟩
  exact Sabrina.RoleChains.checkRegular_sound (by decide)

/-- Stefanoni forbids unary cycles through a composite head. A SABRINA
rank can leave both ends of such a cycle at the same level. -/
theorem compositeAlias_not_weaklyRegular :
    ¬ WeaklyRegular .head (compiledBox compositeAliasRules [compositeAliasChain]) := by
  intro h
  have hc : Composite (compiledBox compositeAliasRules [compositeAliasChain]) ("r", false) :=
    ⟨⟨compositeAliasChain.body, ("r", false)⟩, by decide, by decide, by decide, .inl rfl⟩
  have hrs : NonemptyPath (graphEdges (compiledBox compositeAliasRules [compositeAliasChain]))
      ("r", false) ("s", false) := .edge (by decide)
  have hsr : NonemptyPath (graphEdges (compiledBox compositeAliasRules [compositeAliasChain]))
      ("s", false) ("r", false) := .edge (by decide)
  exact h.1 _ hc (hrs.trans hsr)

theorem stefanoniHierarchy_not_weaklyRegular :
    ¬ WeaklyRegular .head
      (compiledBox (unaryEdges stefanoniHierarchy)
        ((propertyChains stefanoniHierarchy).map PropertyChain.orient)) :=
  fun h => stefanoniHierarchy_no_rank
    (weaklyRegular_exists_ranked (by unfold Ordinary; decide) (by decide) h)

#print axioms converseChain_printed
#print axioms converseChain_no_rank
#print axioms converseChain_head_exclusion
#print axioms compositeAlias_not_weaklyRegular
#print axioms stefanoniHierarchy_not_weaklyRegular

end Sabrina.OWL2.RoleHierarchy.Stefanoni

namespace Sabrina.OWL2.SROIQD.Termination.BlockedForest

private def r : ObjectProperty := .named "urn:example:r"
private def s : ObjectProperty := .named "urn:example:s"

private def converseAlias : Ontology :=
  [.symmetricObjectProperty r, .subObjectPropertyChain [r.converse, r.converse] r]

private def namedAlias : Ontology :=
  [.equivalentObjectProperties [r, s], .subObjectPropertyChain [s, s] r]

private def breaksTransitivity : Ontology :=
  let a := Individual.named "urn:example:a"
  let b := Individual.named "urn:example:b"
  let c := Individual.named "urn:example:c"
  [.objectAssertion r a b, .objectAssertion r b c, .negativeObjectAssertion r a c]

#guard decideAdmittedOntology? converseAlias == none
#guard decideAfterLoweringChainAliases? converseAlias == some true
#guard decideAfterLoweringChainAliases? (converseAlias ++ breaksTransitivity) == some false
#guard decideAdmittedOntology? namedAlias == none
#guard decideAfterLoweringChainAliases? namedAlias == some true
#guard decideAfterLoweringChainAliases? (namedAlias ++ breaksTransitivity) == some false
#guard decideAfterLoweringChainAliases? [.subObjectPropertyChain [r.converse, r.converse] r] ==
  none

end Sabrina.OWL2.SROIQD.Termination.BlockedForest
