import Sabrina.OWL2.SROIQD.Search
import Sabrina.OWL2.SROIQD.CoreCompleteness
import Sabrina.OWL2.DecisionProcedure

/-! Regression tests for the unified SROIQ(D) engine: mixed object + data HasKey
    with SameIndividual merge propagation, ABox + TBox + 33-datatype reasoning,
    ObjectInverseOf in class expressions, data property hierarchy, anonymous
    individuals, and OWL 2 Direct Semantics soundness. -/

namespace SabrinaTests.SROIQD

open Sabrina.OWL2 Sabrina.OWL2.SROIQD Sabrina.OWL2.Datatypes

private def xsdInt : IRI := "http://www.w3.org/2001/XMLSchema#integer"
private def xsdDec : IRI := "http://www.w3.org/2001/XMLSchema#decimal"
private def xsdStr : IRI := "http://www.w3.org/2001/XMLSchema#string"
private def minInc : IRI := "http://www.w3.org/2001/XMLSchema#minInclusive"
private def maxInc : IRI := "http://www.w3.org/2001/XMLSchema#maxInclusive"
private def minLen : IRI := "http://www.w3.org/2001/XMLSchema#minLength"
private def maxLen : IRI := "http://www.w3.org/2001/XMLSchema#maxLength"
private def nonNeg : IRI := "http://www.w3.org/2001/XMLSchema#nonNegativeInteger"

-- 1. Mixed object + data HasKey merges two individuals and propagates class membership:
private def mixedKeyProblem : Problem := {
  keys := [⟨.atom "urn:ex:Employee", [("urn:ex:inDept", false)], ["urn:ex:badgeId"]⟩]
  classAssertions := [
    (.named "urn:ex:alice", .atom "urn:ex:Employee"),
    (.named "urn:ex:bob", .atom "urn:ex:Employee"),
    (.named "urn:ex:alice", .atom "urn:ex:Manager")
  ]
  objAssertions := [
    ("urn:ex:inDept", .named "urn:ex:alice", .named "urn:ex:dept1"),
    ("urn:ex:inDept", .named "urn:ex:bob", .named "urn:ex:dept1")
  ]
  dataAssertions := [
    ("urn:ex:badgeId", .named "urn:ex:alice", ⟨"01", xsdInt⟩),
    ("urn:ex:badgeId", .named "urn:ex:bob", ⟨"1.0", xsdDec⟩)
  ]
}

private def bobIsManager : Inclusion := ⟨.nom (.named "urn:ex:bob") true, .atom "urn:ex:Manager"⟩

#guard match propose (counterProblem mixedKeyProblem bobIsManager) {},
             propose (inclusionProblem mixedKeyProblem bobIsManager) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion mixedKeyProblem bobIsManager 16 ev && ev.verdict == .entailed
  | _, _ => false

-- 2. Mixed object + data HasKey + DifferentIndividuals -> INCONSISTENT_ONTOLOGY.
private def mixedKeyClash : Problem :=
  { mixedKeyProblem with diffInds := [(.named "urn:ex:alice", .named "urn:ex:bob")] }

#guard match propose mixedKeyClash {} with
  | some (.refutation d) => checkConsistency mixedKeyClash 16 (.refutation d)
  | _ => false

-- 3. Unified TBox + RBox + ABox + string length facet clash:
private def stringClashProblem : Problem := {
  tbox := [⟨.atom "urn:ex:Verified", .dataSome "urn:ex:hasCode"
    (.restriction xsdStr [⟨minLen, ⟨"5", nonNeg⟩⟩, ⟨maxLen, ⟨"3", nonNeg⟩⟩])⟩]
  classAssertions := [(.named "urn:ex:doc", .some ("urn:ex:reviewedBy", false) (.atom "urn:ex:Verified"))]
}

#guard match propose stringClashProblem {} with
  | some (.refutation d) => checkConsistency stringClashProblem 16 (.refutation d)
  | _ => false

-- 4. Unified satisfiable ontology with object edges, nominals, and data existential witness:
private def unifiedSatProblem : Problem := {
  tbox := [⟨.atom "urn:ex:Submission", .dataSome "urn:ex:hasScore"
    (.restriction xsdInt [⟨minInc, ⟨"0", xsdInt⟩⟩, ⟨maxInc, ⟨"100", xsdInt⟩⟩])⟩]
  classAssertions := [(.named "urn:ex:sub1", .atom "urn:ex:Submission")]
  funcData := ["urn:ex:hasScore"]
}

#guard match propose unifiedSatProblem {} with
  | some (.model m) => checkConsistency unifiedSatProblem 16 (.model m)
  | _ => false

-- 5. Pairwise blocking closes a cyclic ontology with nominals + data existentials:
private def cyclicNominalDataProblem : Problem := {
  tbox := [
    ⟨.atom "urn:ex:Employee", .some ("urn:ex:reportsTo", false) (.atom "urn:ex:Employee")⟩,
    ⟨.atom "urn:ex:Employee", .dataSome "urn:ex:hasAge"
      (.restriction xsdInt [⟨minInc, ⟨"18", xsdInt⟩⟩, ⟨maxInc, ⟨"65", xsdInt⟩⟩])⟩
  ]
  classAssertions := [(.named "urn:ex:alice", .atom "urn:ex:Employee")]
}

#guard match propose cyclicNominalDataProblem {} with
  | some (.model m) => checkConsistency cyclicNominalDataProblem 16 (.model m)
  | _ => false

-- 6. Cyclic ontology with direct inverse-functional role (≤ 1 r⁻.⊤):
private def cyclicInvFuncProblem : Problem := {
  tbox := [
    ⟨.atom "urn:ex:A", .some ("urn:ex:r", false) (.atom "urn:ex:A")⟩,
    ⟨.top, .max 1 ("urn:ex:r", true) .top⟩
  ]
}

private def aSubB : Inclusion := ⟨.atom "urn:ex:A", .atom "urn:ex:B"⟩

#guard match propose (counterProblem cyclicInvFuncProblem aSubB) {},
             propose (inclusionProblem cyclicInvFuncProblem aSubB) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion cyclicInvFuncProblem aSubB 16 ev && ev.verdict == .independent
  | _, _ => false

-- 7. M4 Core ALCHI fragment boundary (`Problem.isCore`) & nested core refutation
private def nestedCoreUnsatProblem : Problem := {
  tbox := [
    ⟨.atom "urn:ex:A", .some ("urn:ex:r", false) (.conj (.atom "urn:ex:B") (.some ("urn:ex:s", true) (.atom "urn:ex:C")))⟩,
    ⟨.atom "urn:ex:A", .all ("urn:ex:t", false) (.disj (.lit "urn:ex:B" false) (.all ("urn:ex:s", true) (.lit "urn:ex:C" false)))⟩
  ]
  rules := [(("urn:ex:r", false), ("urn:ex:t", false))]
  root := .atom "urn:ex:A"
}

#guard nestedCoreUnsatProblem.isCore
#guard match propose nestedCoreUnsatProblem {} with
  | some (.refutation d) => checkEvidence nestedCoreUnsatProblem 16 (.refutation d)
  | _ => false

-- 8. M9 Total, budget-free decision procedure over Ranked ALCHI + Regular Role Chains
private def m9RankedInput : Sabrina.OWL2.DecisionProcedure.RankedInput where
  rules := [(("r", false), ("s", false))]
  chains := [Sabrina.RoleChains.Chain.named ["s", "s"] "s"]
  tbox := [
    ⟨.atom "A", .some "r" (.atom "B")⟩,
    ⟨.atom "B", .some "s" (.atom "C")⟩
  ]
  rank := Sabrina.RoleChains.inferRank [(("r", false), ("s", false))] [Sabrina.RoleChains.Chain.named ["s", "s"] "s"]
  regular := by decide

#guard Sabrina.OWL2.DecisionProcedure.decideRankedInclusion m9RankedInput
  ⟨.atom "A", .some "s" (.atom "C")⟩ == .entailed
#guard Sabrina.OWL2.DecisionProcedure.decideRankedInclusion m9RankedInput
  ⟨.atom "A", .atom "D"⟩ == .independent

-- Input roots leave room for generated witnesses under the default runtime budget.
private def manyInputWorlds : Problem := {
  classAssertions := (List.range 32).map (fun n =>
    (.named s!"urn:ex:individual{n}", .lit "urn:ex:C" false)) ++
    [(.anonymous "urn:ex:doc" "a", .some ("urn:ex:r", false) .top)]
}

#guard (Limits.forProblem manyInputWorlds).worlds == 50
#guard (propose manyInputWorlds { worlds := 16 }).isNone
#guard
  let limits := Limits.forProblem manyInputWorlds
  match propose manyInputWorlds limits with
  | some (.model m) => m.graph.additionalWorlds + 1 == 35 &&
      checkConsistency manyInputWorlds limits.worlds (.model m)
  | _ => false

-- 9. Generalized GCI absorption: n-ary atomic conjunctions and nominal-anchored axioms
private def quadConj : Concept :=
  .conj (.conj (.atom "urn:ex:A1") (.atom "urn:ex:A2"))
        (.conj (.atom "urn:ex:A3") (.atom "urn:ex:A4"))

#guard quadConj.absorptionPremises ==
  some [.atom "urn:ex:A1", .atom "urn:ex:A2", .atom "urn:ex:A3", .atom "urn:ex:A4"]

private def naryConjClash : Problem := {
  tbox :=
    [⟨quadConj, .atom "urn:ex:Target"⟩,
     ⟨.conj (.atom "urn:ex:Target") (.atom "urn:ex:Disj"), .bottom⟩] ++
    (List.range 12).map fun k =>
      ⟨.conj (.conj (.atom s!"urn:ex:P{k}") (.atom s!"urn:ex:Q{k}")) (.atom s!"urn:ex:R{k}"),
       .atom s!"urn:ex:Out{k}"⟩
  root := .conj quadConj (.atom "urn:ex:Disj")
}

#guard
  let limits := Limits.forProblem naryConjClash
  match propose naryConjClash limits with
  | some (.refutation d) => checkEvidence naryConjClash limits.worlds (.refutation d)
  | _ => false

private def nominalAnchoredProblem (withClash : Bool) : Problem := {
  tbox := (List.range 16).map fun k =>
    ⟨.conj (.nom (.named s!"urn:ex:n{k}") true) (.some ("urn:ex:r", false) (.atom "urn:ex:D")),
     .atom s!"urn:ex:E{k}"⟩
  classAssertions :=
    [(.named "urn:ex:n0", .some ("urn:ex:r", false) (.atom "urn:ex:D"))] ++
    (if withClash then [(.named "urn:ex:n0", .lit "urn:ex:E0" false)] else []) ++
    (List.range 15).map fun k => (.named s!"urn:ex:n{k + 1}", .atom "urn:ex:Other")
}

#guard
  let p := nominalAnchoredProblem false
  let limits := Limits.forProblem p
  match propose p limits with
  | some (.model m) => checkConsistency p limits.worlds (.model m)
  | _ => false

#guard
  let p := nominalAnchoredProblem true
  let limits := Limits.forProblem p
  match propose p limits with
  | some (.refutation d) => checkConsistency p limits.worlds (.refutation d)
  | _ => false

#guard
  let disjGuard := Concept.conj
    (.disj (.nom (.named "urn:ex:a") true) (.nom (.named "urn:ex:b") true))
    (.some ("urn:ex:r", false) (.atom "urn:ex:D"))
  disjGuard.nominalGuard? == some ([.named "urn:ex:a", .named "urn:ex:b"], .some ("urn:ex:r", false) (.atom "urn:ex:D"))

private def nominalEdgeAnchoredProblem (withClash : Bool) : Problem := {
  tbox := (List.range 16).map fun k =>
    ⟨.conj (.nom (.named s!"urn:ex:n{k}") true) (.some ("urn:ex:r", false) (.atom "urn:ex:D")),
     .atom s!"urn:ex:E{k}"⟩
  classAssertions :=
    [(.named "urn:ex:n1", .atom "urn:ex:D")] ++
    (if withClash then [(.named "urn:ex:n0", .lit "urn:ex:E0" false)] else []) ++
    (List.range 14).map fun k => (.named s!"urn:ex:n{k + 2}", .atom "urn:ex:Other")
  objAssertions := [("urn:ex:r", .named "urn:ex:n0", .named "urn:ex:n1")]
}

#guard
  let p := nominalEdgeAnchoredProblem false
  let limits := Limits.forProblem p
  match propose p limits with
  | some (.model m) => checkConsistency p limits.worlds (.model m)
  | _ => false

#guard
  let p := nominalEdgeAnchoredProblem true
  let limits := Limits.forProblem p
  match propose p limits with
  | some (.refutation d) => checkConsistency p limits.worlds (.refutation d)
  | _ => false

end SabrinaTests.SROIQD
