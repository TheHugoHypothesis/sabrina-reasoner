import Sabrina.OWL2.Normalize
import Sabrina.OWL2.SROIQD.Termination.HierarchyRank

namespace Sabrina.OWL2.RoleHierarchy

open Sabrina.ALC (OrientedRole RoleTheory converse)
open Sabrina.RoleChains (ChainShape Ranked)
open Sabrina.RoleChains.SimpleRoles (Reachable)
open Sabrina.RoleChains.TransitivePaths (flipWord)

/-- A chain as written in the OWL syntax. Its head can be an inverse expression. -/
structure PropertyChain where
  body : List OrientedRole
  head : OrientedRole
  deriving DecidableEq, Repr

def PropertyChain.orient (c : PropertyChain) : RoleChains.Chain :=
  ⟨if c.head.2 then flipWord c.body else c.body, c.head.1⟩

/-- Unary hierarchy edges of §11.1. `Reachable` also inserts the mirrors and
takes reflexive transitive closure. The self-pairs from equivalence are harmless. -/
def unaryEdges (o : Ontology) : RoleTheory :=
  o.flatMap fun
    | .subObjectProperty r s => [(Normalize.toOriented r, Normalize.toOriented s)]
    | .equivalentObjectProperties rs =>
      rs.flatMap fun r => rs.map fun s => (Normalize.toOriented r, Normalize.toOriented s)
    | .inverseObjectProperties r s =>
      [(Normalize.toOriented r, Normalize.toOriented s.converse),
       (Normalize.toOriented s.converse, Normalize.toOriented r)]
    | .symmetricObjectProperty r => [(Normalize.toOriented r, Normalize.toOriented r.converse)]
    | _ => []

def propertyChains (o : Ontology) : List PropertyChain :=
  o.filterMap fun
    | .subObjectPropertyChain rs s => some ⟨rs.map Normalize.toOriented, Normalize.toOriented s⟩
    | _ => none

/-- The property-hierarchy condition written in W3C OWL 2 Syntax §11.2.
The domain of the order includes unused property expressions, which can be
left isolated. Converse invariance is imposed on the first argument, as
specified. The condition concerns the hierarchy alone. -/
def WrittenRegular (rules : RoleTheory) (chains : List PropertyChain) : Prop :=
  ∃ lt : OrientedRole → OrientedRole → Prop,
    (∀ r, ¬ lt r r) ∧
    (∀ r s t, lt r s → lt s t → lt r t) ∧
    (∀ r s, lt r s ↔ lt (converse r) s) ∧
    (∀ r s, lt r s → ¬ Reachable rules s r) ∧
    ∀ c ∈ chains, 2 ≤ c.body.length ∧
      (c.head = (topObjectProperty, false) ∨
        ∃ lower, ChainShape c.head c.body lower ∧ ∀ r ∈ lower, lt r c.head)

def WrittenOntologyRegular (o : Ontology) : Prop :=
  WrittenRegular (unaryEdges o) (propertyChains o)

private theorem shape_flip {head : OrientedRole} {body lower : List OrientedRole}
    (h : ChainShape head body lower) :
    ChainShape (converse head) (flipWord body) (flipWord lower) := by
  cases h with
  | transitive => exact .transitive
  | plain body => exact .plain (flipWord body)
  | left =>
    rw [show head :: lower = [head] ++ lower by rfl, RoleChains.RankedPaths.flipWord_append]
    exact .right (flipWord lower)
  | right =>
    rw [RoleChains.RankedPaths.flipWord_append]
    exact .left (flipWord lower)

private theorem rank_le_of_reachable {rules chains rank} (h : Ranked rank rules chains)
    {a b} (hr : Reachable rules a b) : rank a.1 ≤ rank b.1 := by
  rcases RoleChains.SimpleRoles.below_iff_reachable.mpr hr with rfl | hmem
  · exact Nat.le_refl _
  · exact h.respectsClosure hmem

private theorem oriented_shape {rank : RoleChains.Rank} {c : PropertyChain}
    (hlen : 2 ≤ c.orient.body.length)
    (h : ∃ lower, ChainShape (c.orient.head, false) c.orient.body lower ∧
      ∀ r ∈ lower, rank r.1 < rank c.orient.head) :
    2 ≤ c.body.length ∧
      ∃ lower, ChainShape c.head c.body lower ∧ ∀ r ∈ lower, rank r.1 < rank c.head.1 := by
  obtain ⟨body, name, _ | _⟩ := c
  · exact ⟨hlen, h⟩
  · change 2 ≤ (flipWord body).length at hlen
    have hlen' : 2 ≤ body.length := by simpa [flipWord] using hlen
    obtain ⟨lower, hshape, hlt⟩ := h
    change ChainShape (name, false) (flipWord body) lower at hshape
    have hm := shape_flip hshape
    rw [RoleChains.RankedPaths.flipWord_involution] at hm
    refine ⟨hlen', flipWord lower, hm, ?_⟩
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hr)
    exact hlt s hs

/-- The compiler's rank witnesses imply the written W3C hierarchy condition
for the same unary edges and chains, including before orienting inverse heads. -/
theorem ranked_implies_writtenRegular {rules : RoleTheory} {chains : List PropertyChain}
    {rank : RoleChains.Rank} (h : Ranked rank rules (chains.map PropertyChain.orient)) :
    WrittenRegular rules chains := by
  let lt := fun (r s : OrientedRole) => rank r.1 < rank s.1
  refine ⟨lt, fun r => Nat.lt_irrefl (rank r.1), fun _ _ _ => Nat.lt_trans,
    fun _ _ => Iff.rfl, fun r s hlt hr => Nat.not_le_of_lt hlt (rank_le_of_reachable h hr), ?_⟩
  intro c hc
  obtain ⟨hlen, hshape⟩ := h.2 c.orient (List.mem_map_of_mem hc)
  obtain ⟨hlen', hshape'⟩ := oriented_shape hlen (RoleChains.chainShape_iff.mpr hshape)
  exact ⟨hlen', .inr hshape'⟩

#print axioms ranked_implies_writtenRegular

end Sabrina.OWL2.RoleHierarchy
