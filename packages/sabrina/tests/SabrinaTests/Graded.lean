import Sabrina.Graded.Search

namespace SabrinaTests.Graded

open Sabrina.Graded Sabrina.RoleChains
open Sabrina.ALC (RoleTheory)

private def roles : RoleTheory :=
  [(("chainHead",false),("superrole",false))] ++
    Sabrina.ALCHI.inverseRules "superrole" "inverse"

private def chains : List Chain := [Sabrina.RoleChains.Chain.named ["step","member"] "chainHead"]

example : SimpleRoles.check roles chains ("member",false) = true := by decide
example : SimpleRoles.check roles chains ("inverse",false) = false := by decide
example : SimpleRoles.check [] [] ("http://www.w3.org/2002/07/owl#bottomObjectProperty",true)
    = false := by decide

private def graph : NominalGraph :=
  ⟨⟨2,[("B",1),("B",2)],[("r",0,1),("r",0,1),("r",0,2)]⟩, [("a",1), ("b",2)]⟩

-- Duplicate edge facts count only once and zero is a valid bound.
example : eval graph 0 (.exact 2 "r" (.atom "B")) = true := by decide
example : eval graph 0 (.min 3 "r" (.atom "B")) = false := by decide
example : eval graph 1 (.exact 0 "r" (.atom "B")) = true := by decide
example : eval graph 0 (.hasValue "r" "a") = true := by decide
example : eval graph 0 (.exact 2 "r" (.oneOf ["a", "b"])) = true := by decide

private def impossible : Problem :=
  ⟨[],[],[],.conj (.min 3 "r" (.atom "B")) (.max 2 "r" (.atom "B")),{}⟩

#guard match propose impossible {} with
  | some (.refutation depth) =>
    checkEvidence impossible 16 (.refutation depth) &&
      !checkEvidence {impossible with root := .min 3 "r" (.atom "B")} 16 (.refutation depth)
  | _ => false

-- M6 nominal reasoning tests:
-- 1. Nominal pigeonhole: ≥ 3 r.{a, b} is unsatisfiable.
private def nomPigeonhole : Problem :=
  ⟨[],[],[],.min 3 "r" (.oneOf ["a", "b"]),{}⟩

#guard match propose nomPigeonhole {} with
  | some (.refutation depth) => checkEvidence nomPigeonhole 16 (.refutation depth)
  | _ => false

-- 2. Nominal singleton closure: ∃r.{a} entails ≤ 1 r.{a}.
private def nomSingletonQuery : Inclusion :=
  ⟨.hasValue "r" "a", .max 1 "r" (.oneOf ["a"])⟩

#guard match propose (counterProblem [] [] [] nomSingletonQuery) {},
             propose (inclusionProblem [] [] [] nomSingletonQuery) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] [] nomSingletonQuery 16 ev && ev.verdict == .entailed
  | _, _ => false

-- 3. Merge propagation with hasValue + max 1:
--    TBox: A ⊑ ∃r.{a}, A ⊑ ≤ 1 r.⊤, A ⊑ ∃r.B  ⊨  A ⊑ ∃r.({a} ⊓ B)
private def nomMergeTBox : TBox :=
  [⟨.atom "A", .hasValue "r" "a"⟩,
   ⟨.atom "A", .max 1 "r" .top⟩,
   ⟨.atom "A", .some "r" (.atom "B")⟩]

private def nomMergeQuery : Inclusion :=
  ⟨.atom "A", .some "r" (.conj (.oneOf ["a"]) (.atom "B"))⟩

#guard match propose (counterProblem [] [] nomMergeTBox nomMergeQuery) {},
             propose (inclusionProblem [] [] nomMergeTBox nomMergeQuery) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] nomMergeTBox nomMergeQuery 16 ev && ev.verdict == .entailed
  | _, _ => false

-- 4. Independent nominal model: ∃r.{a, b} does not entail ∃r.{a}.
private def nomIndepQuery : Inclusion :=
  ⟨.some "r" (.oneOf ["a", "b"]), .hasValue "r" "a"⟩

#guard match propose (counterProblem [] [] [] nomIndepQuery) {},
             propose (inclusionProblem [] [] [] nomIndepQuery) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] [] nomIndepQuery 16 ev && ev.verdict == .independent
  | _, _ => false

-- M5 object property characteristics & ObjectHasSelf tests:
-- 1. Reflexive role entails ObjectHasSelf and ∃r.⊤.
private def reflQuery : Inclusion := ⟨.top, .self "r" true⟩
private def reflChars : RoleChars := { reflexive := ["r"] }

#guard match propose (counterProblem [] [] [] reflQuery reflChars) {},
             propose (inclusionProblem [] [] [] reflQuery reflChars) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] [] reflQuery 16 ev reflChars && ev.verdict == .entailed
  | _, _ => false

-- 2. Irreflexive role + ObjectHasSelf is unsatisfiable (Self(r) ⊑ ⊥).
private def irreflQuery : Inclusion := ⟨.self "r" true, .bottom⟩
private def irreflChars : RoleChars := { irreflexive := ["r"] }

#guard match propose (counterProblem [] [] [] irreflQuery irreflChars) {},
             propose (inclusionProblem [] [] [] irreflQuery irreflChars) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] [] irreflQuery 16 ev irreflChars && ev.verdict == .entailed
  | _, _ => false

-- 3. Symmetric + Asymmetric role forces ∃r.⊤ ⊑ ⊥.
private def symAsymRules : RoleTheory := [(("r", true), ("r", false))]
private def symAsymChars : RoleChars := { asymmetric := ["r"] }
private def symAsymQuery : Inclusion := ⟨.some "r" .top, .bottom⟩

#guard match propose (counterProblem symAsymRules [] [] symAsymQuery symAsymChars) {},
             propose (inclusionProblem symAsymRules [] [] symAsymQuery symAsymChars) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion symAsymRules [] [] symAsymQuery 16 ev symAsymChars && ev.verdict == .entailed
  | _, _ => false

-- 4. Disjoint roles + subrole forces ∃r.⊤ ⊑ ⊥.
private def disjRules : RoleTheory := [(("r", false), ("s", false))]
private def disjChars : RoleChars := { disjoint := [(("r", false), ("s", false))] }
private def disjQuery : Inclusion := ⟨.some "r" .top, .bottom⟩

#guard match propose (counterProblem disjRules [] [] disjQuery disjChars) {},
             propose (inclusionProblem disjRules [] [] disjQuery disjChars) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion disjRules [] [] disjQuery 16 ev disjChars && ev.verdict == .entailed
  | _, _ => false

-- 5. Simple-role validation rejects irreflexive/asymmetric/disjoint/self on composite roles,
--    while allowing reflexive on transitive roles.
example : checkSimple [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] reflQuery reflChars = false := by decide
example : checkSimple [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] ⟨.top, .some "r" .top⟩ reflChars = true := by decide
example : checkSimple [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] ⟨.top, .top⟩ irreflChars = false := by decide
example : checkSimple [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] ⟨.top, .top⟩ symAsymChars = false := by decide
example : checkSimple [] [Sabrina.RoleChains.Chain.named ["r","r"] "r"] [] ⟨.top, .top⟩ disjChars = false := by decide

-- 6. Pairwise blocking finds a compact finite countermodel for cyclic graded TBox:
--    A ⊑ ∃r.A ∧ ≤ 1 r.⊤ does not entail A ⊑ B.
private def cyclicGradedTBox : TBox :=
  [⟨.atom "A", .some "r" (.atom "A")⟩, ⟨.atom "A", .max 1 "r" .top⟩]
private def cyclicGradedQuery : Inclusion := ⟨.atom "A", .atom "B"⟩

#guard match propose (counterProblem [] [] cyclicGradedTBox cyclicGradedQuery) {},
             propose (inclusionProblem [] [] cyclicGradedTBox cyclicGradedQuery) {} with
  | some c, some inc =>
    let ev : InclusionEvidence := ⟨c, inc⟩
    checkInclusion [] [] cyclicGradedTBox cyclicGradedQuery 16 ev && ev.verdict == .independent
  | _, _ => false

end SabrinaTests.Graded
