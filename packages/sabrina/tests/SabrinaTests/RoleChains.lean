import Sabrina.RoleChains.Search
import Sabrina.RoleChains.Regularity

namespace SabrinaTests.RoleChains

open Sabrina.ALC Sabrina.RoleChains

private def chain : Chain := Chain.named ["r","s"] "t"

private def graph : Graph := ⟨2, [], [("r",0,1), ("s",1,2)]⟩

-- The checker replays the path and demands the implied edge.
example : checkGraph [] [chain] [] .top graph = false := by decide
example : checkGraph [] [chain] [] .top {graph with edges := graph.edges ++ [("t",0,2)]} = true := by decide

private def regular : List Chain :=
  [Sabrina.RoleChains.Chain.named ["r","s"] "r", Sabrina.RoleChains.Chain.named ["s","r"] "r", Sabrina.RoleChains.Chain.named ["r","r"] "r"]

example : checkRegular (inferRank [] regular) [] regular = true := by decide

private def cyclic : List Chain := [Sabrina.RoleChains.Chain.named ["r","s"] "t", Sabrina.RoleChains.Chain.named ["t","s"] "r"]

example : checkRegular (inferRank [] cyclic) [] cyclic = false := by decide
example : (findRank [] regular).isSome = true := by decide
example : (findRank [] cyclic).isSome = false := by decide

private def inverseBody : List Chain := [⟨[("r", true), ("s", false)], "t"⟩]

#guard (RankedPaths.compile (inferRank [] inverseBody) []
  (RankedPaths.normalize inverseBody) ("t", false)).accepts [("r", true), ("s", false)]
#guard (RankedPaths.compile (inferRank [] inverseBody) []
  (RankedPaths.normalize inverseBody) ("t", true)).accepts [("s", true), ("r", false)]
#guard !(RankedPaths.compile (inferRank [] inverseBody) []
  (RankedPaths.normalize inverseBody) ("t", false)).accepts [("r", false), ("s", false)]

-- An inverse occurrence of the head does not qualify as the recursive head.
example : (findRank [] [⟨[("r", true), ("s", false)], "r"⟩]).isSome = false := by decide
example : (findRank [] [⟨[("r", false), ("s", true)], "r"⟩]).isSome = true := by decide

open Sabrina.RoleChains.TransitivePaths

private def hierarchy : RoleTheory :=
  [ (("r",false),("t",false)), (("s",false),("t",false)), (("t",false),("u",false)) ] ++
  Sabrina.ALCHI.inverseRules "u" "back"

example : (compile hierarchy ["t"] ("u",false)).accepts
    [("r",false),("s",false),("r",false),("s",false)] = true := by decide
example : (compile hierarchy ["t"] ("back",false)).accepts
    [("s",true),("r",true)] = true := by decide
example : (compile hierarchy ["t"] ("back",false)).accepts
    [("s",false),("r",false)] = false := by decide
example : (compile hierarchy ["t"] ("u",false)).accepts [] = false := by decide

-- Two different transitive subroles of a nontransitive superrole cannot be mixed.
example : (compile
    [(("r",false),("u",false)), (("s",false),("u",false))]
    ["r","s"] ("u",false)).accepts [("r",false),("s",false)] = false := by decide

private def completed := completeGraph graph hierarchy ["t"] ["r","s","t","u","back"]
example : completed.edge "u" 0 2 = true := by decide
example : completed.edge "back" 2 0 = true := by decide
example : completed.edge "back" 0 2 = false := by decide
example : completed.edge "r" 0 1 = true := by decide
example : completed.edge "t" 0 0 = false := by decide

/-- A user class can use the same spelling as an internal flag. Its truth
    remains independent of that flag. -/
example :
    (let root := Concept.conj (.neg (.atom "g")) (.some "r" (.atom "g"))
     match proposeWithin [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] root 0 18 with
     | some (.guarded (.model _)) => true
     | _ => false) = true := by decide


private def delegation : List Chain := [Sabrina.RoleChains.Chain.named ["oversees","delegatesTo"] "oversees"]
private def delegationRules : RoleTheory :=
  Sabrina.ALCHI.inverseRules "oversees" "overseenBy" ++
    Sabrina.ALCHI.inverseRules "delegatesTo" "delegatedBy"

private def delegationRegex (r : String) : PathRegex :=
  (RankedPaths.compile (inferRank delegationRules delegation) delegationRules
    (RankedPaths.normalize delegation) (r,false)).simplify

#guard (delegationRegex "oversees").accepts
    [("oversees",false),("delegatesTo",false),("delegatesTo",false)] == true
#guard (delegationRegex "overseenBy").accepts
    [("delegatedBy",false),("delegatedBy",false),("overseenBy",false)] == true
#guard (delegationRegex "overseenBy").accepts
    [("overseenBy",false),("delegatedBy",false)] == false
#guard (delegationRegex "oversees").accepts [] == false

/-- The hierarchy cycle is handled as a single component; it shares prefix,
    suffix, transitivity and lower-chain seeds. -/
private def mixedRules : RoleTheory :=
  [(("r",false),("t",false)),(("t",false),("r",false))]
private def mixedChains : List Chain :=
  [Sabrina.RoleChains.Chain.named ["l","t"] "t", Sabrina.RoleChains.Chain.named ["r","s"] "r", Sabrina.RoleChains.Chain.named ["r","r"] "r", Sabrina.RoleChains.Chain.named ["a","b","c"] "t"]

example : checkRegular (inferRank mixedRules mixedChains) mixedRules mixedChains = true := by decide
#guard ((RankedPaths.compile (inferRank mixedRules mixedChains) mixedRules
    (RankedPaths.normalize mixedChains) ("t",false)).simplify).accepts
      [("l",false),("a",false),("b",false),("c",false),("s",false),
        ("l",false),("r",false),("s",false)] == true

end SabrinaTests.RoleChains
