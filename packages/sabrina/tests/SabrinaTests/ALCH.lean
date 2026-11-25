import Sabrina.ALCH.Query

namespace SabrinaTests.ALCH

open Sabrina.ALC

private def a : Concept := .atom "A"
private def rToS : Inclusion := ⟨.some "r" a, .some "s" a⟩

private def chain : Sabrina.ALCH.Ontology :=
  ⟨[], [("r", "t"), ("t", "s")]⟩

-- The inferred pair must exist in the declared direction.
example : ("r", "s") ∈ Sabrina.ALCH.close chain.hierarchy := by decide
example : ("s", "r") ∉ Sabrina.ALCH.close chain.hierarchy := by decide

private def brokenChain : Sabrina.ALCH.Ontology := ⟨[], [("r", "t")]⟩

-- Removing the second inclusion keeps the original existential unchanged.
example : (Sabrina.ALCH.compile brokenChain rToS).2.sup = .some "s" a := by decide

-- Every branch of a diamond and every member of a cycle occurs once.
example : (Sabrina.ALCH.subroles
    (Sabrina.ALCH.close [("r", "s"), ("r", "t"), ("s", "u"), ("t", "u"), ("u", "s")]) "u").length = 4 :=
  by decide

end SabrinaTests.ALCH
