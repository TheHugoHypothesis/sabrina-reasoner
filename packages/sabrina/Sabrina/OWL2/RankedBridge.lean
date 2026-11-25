import Sabrina.OWL2.GradedBridge
import Sabrina.RoleChains.RankedSearch

/-! Relate the complete noncounting search to the shared model theory via
the graded embedding. -/

namespace Sabrina.OWL2.RankedBridge

open Sabrina.RoleChains (Chain Ranked Rank)
open Sabrina.ALC (RoleTheory)

def gradedConcept : Sabrina.ALC.Concept → Sabrina.Graded.Concept
  | .top => .top
  | .atom name => .atom name
  | .neg c => (gradedConcept c).dual
  | .conj a b => .conj (gradedConcept a) (gradedConcept b)
  | .some r c => .some r (gradedConcept c)

def gradedInclusion (q : Sabrina.ALC.Inclusion) : Sabrina.Graded.Inclusion :=
  ⟨gradedConcept q.sub,gradedConcept q.sup⟩

private theorem holds_iff (i : Sabrina.ALC.Interpretation) (nom : String → i.Domain)
    (x : i.Domain) (c : Sabrina.ALC.Concept) :
    Sabrina.Graded.holds i nom x (gradedConcept c) ↔ Sabrina.ALC.holds i x c := by
  induction c generalizing x with
  | top | atom => rfl
  | neg c ih =>
    simp only [gradedConcept,Sabrina.Graded.holds_dual,Sabrina.ALC.holds,ih]
  | conj a b ha hb => simp only [gradedConcept,Sabrina.Graded.holds,Sabrina.ALC.holds,ha,hb]
  | some r c ih => simp only [gradedConcept,Sabrina.Graded.holds,Sabrina.ALC.holds,ih]

private theorem tbox_iff (i : Sabrina.ALC.Interpretation) (nom : String → i.Domain)
    (tbox : Sabrina.ALC.TBox) :
    Sabrina.Graded.models i nom (tbox.map gradedInclusion) ↔ Sabrina.ALC.models i tbox := by
  constructor
  · intro h q hq x hx
    exact (holds_iff i nom x q.sup).mp
      (h (gradedInclusion q) (List.mem_map_of_mem hq) x ((holds_iff i nom x q.sub).mpr hx))
  · intro h q hq x hx
    obtain ⟨ax,hax,rfl⟩ := List.mem_map.mp hq
    exact (holds_iff i nom x ax.sup).mpr (h ax hax x ((holds_iff i nom x ax.sub).mp hx))

def ontology (rules : RoleTheory) (chains : List Chain) (tbox : Sabrina.ALC.TBox) : Ontology :=
  GradedBridge.ontology rules chains (tbox.map gradedInclusion)

def conceptSat (d : DatatypeMap) (rules : RoleTheory) (chains : List Chain)
    (tbox : Sabrina.ALC.TBox) (root : Sabrina.ALC.Concept) : Prop :=
  ∃ i : Interpretation d, models i (ontology rules chains tbox) ∧
    ∃ x, classHolds i x (GradedBridge.concept (gradedConcept root))

theorem conceptSat_iff (d : DatatypeMap) (rules : RoleTheory) (chains : List Chain)
    (tbox : Sabrina.ALC.TBox) (root : Sabrina.ALC.Concept) :
    conceptSat d rules chains tbox root ↔ Sabrina.RoleChains.ConceptSat rules chains tbox root := by
  refine (GradedBridge.conceptSat_iff d rules chains (tbox.map gradedInclusion)
    (gradedConcept root)).symm.trans ?_
  constructor
  · rintro ⟨i,nom,hr,hc,_,ht,x,hx⟩
    exact ⟨i,hr,hc,(tbox_iff i nom tbox).mp ht,x,(holds_iff i nom x root).mp hx⟩
  · rintro ⟨i,hr,hc,ht,x,hx⟩
    exact ⟨i,fun _ => x,hr,hc,⟨by simp,by simp,by simp,by simp⟩,
      (tbox_iff i (fun _ => x) tbox).mpr ht,x,(holds_iff i (fun _ => x) x root).mpr hx⟩

theorem search_model_iff (d : DatatypeMap) {rank : Rank} {rules : RoleTheory} {chains : List Chain}
    (h : Ranked rank rules chains) (tbox : Sabrina.ALC.TBox) (root : Sabrina.ALC.Concept) :
    (∃ pool, Sabrina.RoleChains.RankedPaths.search rank rules chains tbox root = .model pool) ↔
      conceptSat d rules chains tbox root :=
  (Sabrina.RoleChains.RankedPaths.search_model_iff h tbox root).trans
    (conceptSat_iff d rules chains tbox root).symm

theorem search_refutation_iff (d : DatatypeMap) {rank : Rank} {rules : RoleTheory}
    {chains : List Chain} (h : Ranked rank rules chains) (tbox : Sabrina.ALC.TBox)
    (root : Sabrina.ALC.Concept) :
    (∃ depth, Sabrina.RoleChains.RankedPaths.search rank rules chains tbox root = .refutation depth) ↔
      ¬ conceptSat d rules chains tbox root :=
  (Sabrina.RoleChains.RankedPaths.search_refutation_iff h tbox root).trans
    (not_congr (conceptSat_iff d rules chains tbox root).symm)

end Sabrina.OWL2.RankedBridge
