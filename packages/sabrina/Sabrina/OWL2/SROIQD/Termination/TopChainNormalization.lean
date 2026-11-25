import Sabrina.OWL2.SROIQD.Termination.SROIQDecidable

namespace Sabrina.OWL2.RoleHierarchy

open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.OWL2.SROIQD.Termination.BlockedForest
  (decideAdmittedOntology? decideAdmittedOntology_iff)

private def isTopHeadedChain : Axiom → Bool
  | .subObjectPropertyChain body (.named head) =>
    decide (2 ≤ body.length) && head == topObjectProperty
  | _ => false

/-- The top relation already contains every composition. Preserve malformed
chain lengths so that lowering cannot bypass the source arity check. -/
def eraseTopHeadedChains (o : Ontology) : Ontology :=
  o.filter fun a => !isTopHeadedChain a

private theorem topHeadedChain_holds {d : DatatypeMap} (i : Interpretation d) {a : Axiom}
    (h : isTopHeadedChain a = true) : axiomHolds i a := by
  cases a <;> try contradiction
  case subObjectPropertyChain body head =>
    cases head with
    | named r =>
      simp only [isTopHeadedChain, Bool.and_eq_true, beq_iff_eq] at h
      have he : r = topObjectProperty := h.2
      subst r
      exact fun x y _ => i.topObjectExt x y
    | inverse _ => contradiction

theorem eraseTopHeadedChains_satisfies_iff {d : DatatypeMap} (i : Interpretation d) (o : Ontology) :
    satisfies i (eraseTopHeadedChains o) ↔ satisfies i o := by
  constructor
  · intro hm a ha
    by_cases htop : isTopHeadedChain a = true
    · exact topHeadedChain_holds i htop
    · exact hm a (List.mem_filter.mpr ⟨ha, by simp [htop]⟩)
  · intro hm a ha
    exact hm a (List.mem_filter.mp ha).1

theorem eraseTopHeadedChains_sat_iff (d : DatatypeMap) (o : Ontology) :
    Satisfiable d (eraseTopHeadedChains o) ↔ Satisfiable d o :=
  exists_congr fun i => exists_congr fun assign =>
    eraseTopHeadedChains_satisfies_iff (i.withAnonymous assign) o

/-- Use the existing solver after removing only the tautological chains.
All its usual admission checks apply to the remaining ontology. -/
def decideAfterErasingTopChains? (o : Ontology) : Option Bool :=
  decideAdmittedOntology? (eraseTopHeadedChains o)

theorem decideAfterErasingTopChains_iff {o : Ontology} {b : Bool}
    (h : decideAfterErasingTopChains? o = some b) : b = true ↔ Satisfiable datatypeMap o :=
  (decideAdmittedOntology_iff h).trans (eraseTopHeadedChains_sat_iff datatypeMap o)

private def topChain : Axiom :=
  .subObjectPropertyChain [.named "r", .named topObjectProperty, .named "r"]
    (.named topObjectProperty)

private def malformedTopChain : Axiom :=
  .subObjectPropertyChain [.named "r"] (.named topObjectProperty)

#guard decideAdmittedOntology? [topChain] == none
#guard decideAfterErasingTopChains? [topChain] == some true
#guard decideAfterErasingTopChains? [topChain, .subClassOf (.named thing) (.named nothing)] ==
  some false
#guard decideAfterErasingTopChains? [malformedTopChain] == none

#print axioms eraseTopHeadedChains_sat_iff
#print axioms decideAfterErasingTopChains_iff

end Sabrina.OWL2.RoleHierarchy
