import Sabrina.OWL2.SROIQD.Termination.WeakRegularity
import Sabrina.OWL2.SROIQD.Termination.SROIQDecidable

namespace Sabrina.OWL2.RoleHierarchy.Stefanoni

open Sabrina.RoleChains (findRank Rank checkRegular)
open SROIQD SROIQD.Termination.BlockedForest

/-- Rank-independent input conditions on a normalized object problem. With no
chains, the zero rank accepts every unary hierarchy. This first test reuses
the forest solver's object syntax checks, including object keys and ABoxes.
Simplicity and weak regularity below are checked on the original hierarchy. -/
structure RegularObjectInput (p : Problem) : Prop where
  objects : ({p with chains := []} : Problem).isSROIQ (fun _ => 0) = true
  simple : p.checkSimple = true
  ordinary : Ordinary (compiledBox p.rules p.chains)
  lengths : ∀ c ∈ p.chains, 2 ≤ c.body.length
  regular : WeaklyRegular .head (compiledBox p.rules p.chains)

private theorem rankExists {p} (h : RegularObjectInput p) :
    (findRank p.rules p.chains).isSome = true :=
  weaklyRegular_findRank_isSome h.ordinary h.lengths h.regular

private def computedRank {p} (h : RegularObjectInput p) : Rank :=
  (findRank p.rules p.chains).get (rankExists h)

private theorem checked {p} (h : RegularObjectInput p) : p.isSROIQ (computedRank h) = true := by
  have hr := Sabrina.RoleChains.checkRegular_iff.mpr
    (Sabrina.RoleChains.findRank_sound (Option.some_get (rankExists h)).symm)
  have hc : p.chains.all (fun c => isCoreObjPropIRI c.head && c.bodyNames.all isCoreObjPropIRI) = true := by
    apply List.all_eq_true.mpr
    intro c hm
    have hmem : (⟨c.body, (c.head, false)⟩ : PropertyChain) ∈ compiledBox p.rules p.chains :=
      List.mem_append_right _ (List.mem_map_of_mem hm)
    obtain ⟨hh, hb⟩ := h.ordinary _ hmem
    simp only [Bool.and_eq_true, List.all_eq_true, isCoreObjPropIRI, bne_iff_ne]
    refine ⟨hh, ?_⟩
    intro n hn
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hn
    exact hb r hm
  have ho := h.objects
  unfold Problem.isSROIQ at ho ⊢
  simp only [hc, h.simple, show checkRegular (computedRank h) p.rules p.chains = true from hr,
    Bool.and_true]
  simp only [Bool.and_eq_true] at ho ⊢
  grind only

/-- All ranked search parameters are computed. Cyclic GCIs, existential and
qualified counting restrictions, nominals and object keys use the same total
forest procedure. -/
def decideRegularObject (p : Problem) (h : RegularObjectInput p) : Bool :=
  decideSROIQBool (checked h)

theorem decideRegularObject_iff {p : Problem} (h : RegularObjectInput p) :
    decideRegularObject p h = true ↔ p.Sat :=
  decideSROIQBool_iff (checked h)

theorem decideRegularObject_ontology_iff {p : Problem} {o : Ontology} {defs}
    (hnorm : Normalize.normalizeWithDefs o = some (defs,p)) (hroot : p.root = .top)
    (h : RegularObjectInput p) :
    decideRegularObject p h = true ↔ Satisfiable Datatypes.datatypeMap o :=
  decideSROIQBool_ontology_iff (checked h) hnorm hroot

#print axioms decideRegularObject_iff
#print axioms decideRegularObject_ontology_iff

end Sabrina.OWL2.RoleHierarchy.Stefanoni
