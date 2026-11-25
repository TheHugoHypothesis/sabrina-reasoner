import Sabrina.ALC.Semantics
import Sabrina.ALCH.Hierarchy

namespace Sabrina.ALCH

open Sabrina.ALC

def ModelsRoles (edges : Hierarchy) (i : Interpretation) : Prop :=
  ∀ r s, (r, s) ∈ edges → ∀ {x y}, i.role r x y → i.role s x y

structure Ontology where
  tbox : TBox
  hierarchy : Hierarchy

def Models (o : Ontology) (i : Interpretation) : Prop :=
  models i o.tbox ∧ ModelsRoles o.hierarchy i

def ConceptSat (o : Ontology) (c : Concept) : Prop :=
  ∃ i : Interpretation, Models o i ∧ ∃ x, holds i x c

def liftRoles (closed : Hierarchy) (i : Interpretation) : Interpretation :=
  { i with role := fun r x y => ∃ s ∈ subroles closed r, i.role s x y }

theorem liftRoles_models (edges : Hierarchy) (i : Interpretation) :
    ModelsRoles edges (liftRoles (close edges) i) := by
  intro r s h x y
  rintro ⟨u, hu, hxy⟩
  refine ⟨u, mem_subroles.mpr (Or.inr ?_), hxy⟩
  rcases mem_subroles.mp hu with rfl | hu
  · exact mem_close h
  · exact close_step hu h

private theorem liftRoles_role_eq {edges : Hierarchy} {i : Interpretation}
    (h : ModelsRoles edges i) : (liftRoles (close edges) i).role = i.role := by
  funext r x y
  apply propext
  constructor
  · rintro ⟨s, hs, hxy⟩
    rcases mem_subroles.mp hs with rfl | hs
    · exact hxy
    · let Included := fun a b => ∀ u v, i.role a u v → i.role b u v
      have hsub : Included s r := close_sound (R := Included)
        (fun {a b} hab _ _ huv => h a b hab huv)
        (fun hab hbc u v huv => hbc u v (hab u v huv)) hs
      exact hsub x y hxy
  · intro hxy
    exact ⟨r, mem_subroles.mpr (Or.inl rfl), hxy⟩

/-- Taking the union of subrole relations preserves a model of the hierarchy. -/
theorem liftRoles_eq {edges : Hierarchy} {i : Interpretation} (h : ModelsRoles edges i) :
    liftRoles (close edges) i = i := by
  have hr := liftRoles_role_eq h
  cases i
  simp only [liftRoles] at hr ⊢
  rw [hr]

theorem holds_liftRoles {edges : Hierarchy} {i : Interpretation} (h : ModelsRoles edges i)
    {x : i.Domain} {c : Concept} : holds (liftRoles (close edges) i) x c ↔ holds i x c := by
  have hr := liftRoles_role_eq h
  cases i
  simp only [liftRoles] at hr ⊢
  rw [hr]

private def someChoice (c : Concept) : List String → Concept
  | [] => .bottom
  | [r] => .some r c
  | r :: s :: rest => .disj (.some r c) (someChoice c (s :: rest))

private theorem holds_someChoice (i : Interpretation) (x : i.Domain) (c : Concept)
    (rs : List String) :
    holds i x (someChoice c rs) ↔ ∃ r ∈ rs, ∃ y, i.role r x y ∧ holds i y c := by
  induction rs with
  | nil => simp [someChoice, holds_bottom]
  | cons r rs ih =>
    cases rs with
    | nil => simp [someChoice, holds]
    | cons s rest =>
      rw [someChoice, holds_disj, ih]
      constructor
      · rintro (⟨y, hr, hc⟩ | ⟨t, ht, y, hr, hc⟩)
        · exact ⟨r, List.mem_cons_self .., y, hr, hc⟩
        · exact ⟨t, List.mem_cons_of_mem _ ht, y, hr, hc⟩
      · rintro ⟨t, ht, y, hr, hc⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inl ⟨y, hr, hc⟩
        · exact Or.inr ⟨t, ht, y, hr, hc⟩

def translate (closed : Hierarchy) : Concept → Concept
  | .top => .top
  | .atom a => .atom a
  | .neg c => .neg (translate closed c)
  | .conj a b => .conj (translate closed a) (translate closed b)
  | .some r c => someChoice (translate closed c) (subroles closed r)

theorem holds_translate (closed : Hierarchy) (i : Interpretation) (x : i.Domain)
    (c : Concept) : holds i x (translate closed c) ↔ holds (liftRoles closed i) x c := by
  induction c generalizing x with
  | top | atom => rfl
  | neg c ih => simp only [translate, holds, ih]
  | conj a b iha ihb => simp only [translate, holds, iha, ihb]
  | some r c ih =>
    rw [translate, holds_someChoice]
    constructor
    · rintro ⟨s, hs, y, hxy, hc⟩
      exact ⟨y, ⟨s, hs, hxy⟩, (ih y).mp hc⟩
    · rintro ⟨y, ⟨s, hs, hxy⟩, hc⟩
      exact ⟨s, hs, y, hxy, (ih y).mpr hc⟩

def translateInclusion (closed : Hierarchy) (q : Inclusion) : Inclusion :=
  ⟨translate closed q.sub, translate closed q.sup⟩

def compile (o : Ontology) (q : Inclusion) : TBox × Inclusion :=
  let closed := close o.hierarchy
  (o.tbox.map (translateInclusion closed), translateInclusion closed q)

theorem holds_inclusion_translate (closed : Hierarchy) (i : Interpretation) (q : Inclusion) :
    (∀ x, holds i x (translate closed q.sub) → holds i x (translate closed q.sup)) ↔
      (∀ x, holds (liftRoles closed i) x q.sub → holds (liftRoles closed i) x q.sup) := by
  simp only [holds_translate]
  rfl

theorem models_translate (closed : Hierarchy) (i : Interpretation) (tbox : TBox) :
    models i (tbox.map (translateInclusion closed)) ↔ models (liftRoles closed i) tbox := by
  constructor
  · intro h q hq
    exact (holds_inclusion_translate closed i q).mp
      (h _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro h _ hq
    obtain ⟨q, hmem, rfl⟩ := List.mem_map.mp hq
    exact (holds_inclusion_translate closed i q).mpr (h q hmem)

theorem models_lift_iff (o : Ontology) (i : Interpretation) :
    models i (o.tbox.map (translateInclusion (close o.hierarchy))) ↔
      Models o (liftRoles (close o.hierarchy) i) := by
  rw [models_translate]
  exact ⟨fun h => ⟨h, liftRoles_models o.hierarchy i⟩, And.left⟩

theorem conceptSat_iff (o : Ontology) (c : Concept) :
    ALC.ConceptSat (o.tbox.map (translateInclusion (close o.hierarchy)))
      (translate (close o.hierarchy) c) ↔ ConceptSat o c := by
  constructor
  · rintro ⟨i, hm, x, hx⟩
    exact ⟨liftRoles (close o.hierarchy) i, (models_lift_iff o i).mp hm, x,
      (holds_translate _ i x c).mp hx⟩
  · rintro ⟨i, hm, x, hx⟩
    have he := liftRoles_eq hm.2
    refine ⟨i, (models_lift_iff o i).mpr ?_, x, (holds_translate _ i x c).mpr ?_⟩
    · rwa [he]
    · exact (holds_liftRoles hm.2).mpr hx

end Sabrina.ALCH
