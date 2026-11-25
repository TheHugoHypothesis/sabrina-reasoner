import Sabrina.OWL2.SROIQD.Termination.SROIQDecidable
import Sabrina.OWL2.SROIQD.Termination.HierarchyRank

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole RoleTheory roleClosure)
open Sabrina.OWL2.Datatypes (datatypeMap)

def replaceAlias (closed : RoleTheory) (head r : OrientedRole) : OrientedRole :=
  if closed.contains (r, head) && closed.contains (head, r) then head else r

def replaceChainAliases (closed : RoleTheory) (c : RoleChains.Chain) : RoleChains.Chain :=
  {c with body := c.body.map (replaceAlias closed (c.head, false))}

/-- Replace a chain letter with the head if the unary hierarchy entails
inclusions in both directions. Chain heads and lengths are preserved. -/
def Problem.lowerChainAliases (p : Problem) : Problem :=
  {p with chains := p.chains.map (replaceChainAliases (roleClosure p.rules))}

private def objectView (i : Interpretation datatypeMap) : ALC.Interpretation :=
  ⟨i.Object, i.objectNonempty, i.classes, i.objectProperties⟩

private theorem replaceAlias_holds_iff (i : Interpretation datatypeMap) {p : Problem}
    (rules : ∀ rs ∈ p.rules, ∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y)
    (head r : OrientedRole) (x y : i.Object) :
    holdsOriented i (replaceAlias (roleClosure p.rules) head r) x y ↔ holdsOriented i r x y := by
  have hrules : ALC.modelsRoles (objectView i) p.rules :=
    fun a b h x y he => rules (a, b) h x y he
  unfold replaceAlias
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨ALC.modelsClosure hrules head r h.2 x y, ALC.modelsClosure hrules r head h.1 x y⟩
  · exact Iff.rfl

private theorem replaceAliases_path_iff (i : Interpretation datatypeMap) {p : Problem}
    (rules : ∀ rs ∈ p.rules, ∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y)
    (head : OrientedRole) (word : List OrientedRole) (x y : i.Object) :
    objPath i (word.map (replaceAlias (roleClosure p.rules) head)) x y ↔ objPath i word x y := by
  induction word generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, objPath, replaceAlias_holds_iff i rules, ih]

theorem Problem.lowerChainAliases_models_iff (p : Problem) (i : Interpretation datatypeMap) :
    p.lowerChainAliases.Models i ↔ p.Models i := by
  constructor
  · intro h
    refine {h with chains := ?_}
    intro c hc x y hp
    exact h.chains _ (List.mem_map_of_mem hc) x y
      ((replaceAliases_path_iff i h.rules (c.head, false) c.body x y).mpr hp)
  · intro h
    refine {h with chains := ?_}
    intro c hc x y hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact h.chains a ha x y
      ((replaceAliases_path_iff i h.rules (a.head, false) a.body x y).mp hp)

theorem Problem.lowerChainAliases_sat_iff (p : Problem) :
    p.lowerChainAliases.Sat ↔ p.Sat :=
  exists_congr fun i => and_congr (p.lowerChainAliases_models_iff i) Iff.rfl

private theorem mem_lower_of_ne_head {head : OrientedRole} {body rest}
    (hs : RoleChains.ChainShape head body rest) {r} (hr : r ∈ body) (hne : r ≠ head) :
    r ∈ rest := by
  cases hs <;> simp_all

/-- A ranked input already has the head in every eligible recursive position.
Replacing aliases therefore leaves every previously ranked input intact. -/
theorem Problem.lowerChainAliases_eq_of_ranked {p : Problem} {rank : RoleChains.Rank}
    (h : RoleChains.Ranked rank p.rules p.chains) : p.lowerChainAliases = p := by
  have hchain (c : RoleChains.Chain) (hc : c ∈ p.chains) :
      replaceChainAliases (roleClosure p.rules) c = c := by
    obtain ⟨rest, hshape, hlt⟩ := RoleChains.chainShape_iff.mpr (h.2 c hc).2
    have hletter (r : OrientedRole) (hr : r ∈ c.body) :
        replaceAlias (roleClosure p.rules) (c.head, false) r = r := by
      unfold replaceAlias
      split
      · rename_i hclosed
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hclosed
        apply Classical.byContradiction
        intro hne
        have hstrict := hlt r (mem_lower_of_ne_head hshape hr (Ne.symm hne))
        exact (Nat.not_le_of_lt hstrict) (h.respectsClosure hclosed.2)
      · rfl
    have hbody : c.body.map (replaceAlias (roleClosure p.rules) (c.head, false)) = c.body := by
      simpa only [List.map_id] using (List.map_congr_left (g := id) hletter)
    unfold replaceChainAliases
    rw [hbody]
  have hchains : p.chains.map (replaceChainAliases (roleClosure p.rules)) = p.chains := by
    simpa only [List.map_id] using (List.map_congr_left (g := id) hchain)
  unfold Problem.lowerChainAliases
  rw [hchains]

namespace Termination.BlockedForest

open Sabrina.RoleChains (findRank)

/-- Opt-in decision adapter. Simplicity is checked on the original problem,
and the rank is checked on the equivalent problem with chain aliases lowered. -/
def decideAfterLoweringChainAliases? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    let q := p.lowerChainAliases
    (findRank q.rules q.chains).bind fun rank =>
      if p.root = .top ∧ p.checkSimple = true then
        if h : q.lowerBottom.isSROIQD rank = true then some (decideSROIQDBool h)
        else none
      else none

theorem decideAfterLoweringChainAliases_iff {o : Ontology} {b : Bool}
    (h : decideAfterLoweringChainAliases? o = some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideAfterLoweringChainAliases?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := h
  split at hb
  · rename_i hroot
    split at hb
    · rename_i hadmit
      cases hb
      exact (decideSROIQDBool_iff hadmit).trans
        (p.lowerChainAliases.lowerBottom_sat_iff.trans
          (p.lowerChainAliases_sat_iff.trans
            ((Normalize.normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot.1)).symm))
    · contradiction
  · contradiction

theorem decideAfterLoweringChainAliases_unsat_iff {o : Ontology} {b : Bool}
    (h : decideAfterLoweringChainAliases? o = some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideAfterLoweringChainAliases_iff h]
  cases b <;> simp

theorem decideAfterLoweringChainAliases_extends {o : Ontology} {b : Bool}
    (h : decideAdmittedOntology? o = some b) :
    decideAfterLoweringChainAliases? o = some b := by
  simp only [decideAdmittedOntology?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, hfound, hb⟩ := h
  have he := Problem.lowerChainAliases_eq_of_ranked (RoleChains.findRank_sound hfound)
  unfold decideAfterLoweringChainAliases?
  exact Option.bind_eq_some_iff.mpr ⟨(defs, p), hnorm, by simpa [he, hfound] using hb⟩

#print axioms Problem.lowerChainAliases_models_iff
#print axioms decideAfterLoweringChainAliases_iff
#print axioms decideAfterLoweringChainAliases_unsat_iff
#print axioms decideAfterLoweringChainAliases_extends

end Termination.BlockedForest
end Sabrina.OWL2.SROIQD
