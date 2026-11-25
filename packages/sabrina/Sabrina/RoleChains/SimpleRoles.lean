import Sabrina.RoleChains.RankedCompletion

namespace Sabrina.RoleChains.SimpleRoles

open Sabrina.ALC
open TransitivePaths (Below WordPath)

def builtinRoles : List String :=
  ["http://www.w3.org/2002/07/owl#topObjectProperty",
   "http://www.w3.org/2002/07/owl#bottomObjectProperty"]

private def compositeNames (chains : List Chain) : List String :=
  builtinRoles ++ (chains.filter fun c => decide (2 ≤ c.body.length)).map Chain.head

/-- Composite roles in the typed closure, including both orientations.
    A transitivity declaration is represented by a chain with the head twice. -/
def Composite (chains : List Chain) (r : OrientedRole) : Prop :=
  r.1 ∈ builtinRoles ∨ ∃ c ∈ chains, 2 ≤ c.body.length ∧ c.head = r.1

/-- Reflexive transitive closure of the submitted unary inclusions and their converses.
    Equivalence and named inverses enter the typed input as signed inclusions. -/
inductive Reachable (rules : RoleTheory) : OrientedRole → OrientedRole → Prop where
  | refl (r) : Reachable rules r r
  | step {r s} : (r,s) ∈ mirrored rules → Reachable rules r s
  | trans {r s t} : Reachable rules r s → Reachable rules s t → Reachable rules r t

theorem below_iff_reachable {rules : RoleTheory} {r s : OrientedRole} :
    Below rules r s ↔ Reachable rules r s := by
  constructor
  · rintro (rfl | h)
    · exact .refl _
    · exact ALCH.close_sound (fun h => Reachable.step h) Reachable.trans h
  · intro h
    induction h with
    | refl => exact Below.refl _ _
    | step h => exact Below.step h
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def Simple (rules : RoleTheory) (chains : List Chain) (r : OrientedRole) : Prop :=
  ∀ s, Reachable rules s r → ¬ Composite chains s

def firstComposite (closed : RoleTheory) (chains : List Chain) (r : OrientedRole) :
    Option OrientedRole :=
  (ALCH.subroles closed r).find? (fun s => (compositeNames chains).contains s.1)

def check (rules : RoleTheory) (chains : List Chain) (r : OrientedRole) : Bool :=
  (firstComposite (roleClosure rules) chains r).isNone

private theorem mem_compositeNames {chains : List Chain} {r : OrientedRole} :
    r.1 ∈ compositeNames chains ↔ Composite chains r := by
  simp [compositeNames, Composite, and_assoc]

theorem check_iff {rules : RoleTheory} {chains : List Chain} {r : OrientedRole} :
    check rules chains r = true ↔ Simple rules chains r := by
  simp only [check, firstComposite, Option.isNone_iff_eq_none, List.find?_eq_none,
    ALCH.mem_subroles, List.contains_iff_mem]
  constructor
  · intro h s hs hc
    exact h s (below_iff_reachable.mpr hs) (mem_compositeNames.mpr hc)
  · intro h s hs hc
    exact h s (below_iff_reachable.mp hs) (mem_compositeNames.mp hc)

theorem simple_converse {rules : RoleTheory} {chains : List Chain} {r : OrientedRole} :
    Simple rules chains (converse r) ↔ Simple rules chains r := by
  have flip {s t : OrientedRole} (h : Reachable rules s t) :
      Reachable rules (converse s) (converse t) :=
    below_iff_reachable.mp (below_iff_reachable.mpr h).flip
  constructor
  · intro h s hs hc
    exact h _ (flip hs) hc
  · intro h s hs hc
    have hb := flip hs
    rw [TransitivePaths.converse_converse] at hb
    exact h _ hb hc

private theorem normalized_composite {rank rules chains} (h : Ranked rank rules chains)
    {c : RankedPaths.Rule} (hc : c ∈ RankedPaths.normalize chains) :
    Composite chains c.head := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    exact Or.inr ⟨k,hk,(h.2 k hk).1,rfl⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact Or.inr ⟨k,hk,(h.2 k hk).1,rfl⟩

/-- Every derivation into a simple role is a single edge plus unary promotions. -/
theorem generated_simple {rank rules chains} (h : Ranked rank rules chains)
    {r w} (hw : RankedPaths.Generated rules (RankedPaths.normalize chains) r w)
    (hs : Simple rules chains r) : ∃ s, w = [s] ∧ Below rules s r := by
  let L : OrientedRole → Language := fun t word =>
    Simple rules chains t → ∃ s, word = [s] ∧ Below rules s t
  apply hw L _ hs
  refine ⟨fun r _ => ⟨r,rfl,Below.refl _ _⟩, ?_, ?_⟩
  · intro s t word he hl ht
    have hs : Simple rules chains s := fun a ha => ht a (ha.trans (below_iff_reachable.mp he))
    obtain ⟨a,ha,hb⟩ := hl hs
    exact ⟨a,ha,hb.trans he⟩
  · intro c word hc _ hs
    exact (hs c.head (.refl _) (normalized_composite h hc)).elim

/-- Saturating chain edges preserves the exact successor set of any simple role
    in a graph already satisfying the unary hierarchy. -/
theorem completed_simple_iff {i : Interpretation} {rank rules chains}
    (h : Ranked rank rules chains) (hr : modelsRoles i rules)
    {r : String} (hs : Simple rules chains (r,false)) (x y : i.Domain) :
    (RankedPaths.complete i rules chains).role r x y ↔ i.role r x y := by
  constructor
  · rintro ⟨word,hw,hp⟩
    obtain ⟨s,rfl,hb⟩ := generated_simple h hw hs
    obtain ⟨z,hz,hzy⟩ := hp
    change z = y at hzy
    subst z
    rcases hb with he | he
    · rw [he] at hz
      exact hz
    · exact modelsClosure hr s (r,false) he x y hz
  · exact RankedPaths.complete_extension

end Sabrina.RoleChains.SimpleRoles
