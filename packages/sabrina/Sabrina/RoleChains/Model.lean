import Sabrina.RoleChains.Semantics

namespace Sabrina.RoleChains

open Sabrina.ALC

/-- Explicit model evidence. World zero exists even when all facts are empty. -/
structure Graph where
  additionalWorlds : Nat
  atoms : List (String × Fin (additionalWorlds + 1))
  edges : List (String × Fin (additionalWorlds + 1) × Fin (additionalWorlds + 1))

abbrev Graph.World (g : Graph) := Fin (g.additionalWorlds + 1)

def Graph.worlds (g : Graph) : List g.World := List.finRange (g.additionalWorlds + 1)

def Graph.atom (g : Graph) (p : String) (x : g.World) : Bool := g.atoms.contains (p,x)
def Graph.edge (g : Graph) (r : String) (x y : g.World) : Bool := g.edges.contains (r,x,y)

def Graph.interpretation (g : Graph) : Interpretation where
  Domain := g.World
  nonempty := ⟨0⟩
  atom p x := g.atom p x = true
  role r x y := g.edge r x y = true

def Graph.oriented (g : Graph) (r : OrientedRole) (x y : g.World) : Bool :=
  if r.2 then g.edge r.1 y x else g.edge r.1 x y

theorem Graph.oriented_iff (g : Graph) (r : OrientedRole) (x y : g.World) :
    g.oriented r x y = true ↔ holdsRole g.interpretation r x y := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

def Graph.holds (g : Graph) (x : g.World) : Concept → Bool
  | .top => true
  | .atom p => g.atom p x
  | .neg c => !(g.holds x c)
  | .conj c d => g.holds x c && g.holds x d
  | .some r c => g.worlds.any fun y => g.edge r x y && g.holds y c

theorem Graph.holds_iff (g : Graph) (x : g.World) (c : Concept) :
    g.holds x c = true ↔ ALC.holds g.interpretation x c := by
  induction c generalizing x with
  | top | atom => simp [Graph.holds, ALC.holds, Graph.interpretation]
  | neg c ih => simp [Graph.holds, ALC.holds, ← ih]
  | conj a b iha ihb => simp [Graph.holds, ALC.holds, iha, ihb]
  | some r c ih =>
    simp [Graph.holds, ALC.holds, Graph.interpretation, List.any_eq_true, Graph.worlds, ih]

private def Graph.starts (g : Graph) (target : g.World) : List OrientedRole → List g.World
  | [] => [target]
  | r :: tail =>
    let next := g.starts target tail
    g.worlds.filter fun x => next.any (g.oriented r x)

private theorem Graph.mem_starts (g : Graph) (word : List OrientedRole) (x y : g.World) :
    x ∈ g.starts y word ↔ TransitivePaths.WordPath g.interpretation word x y := by
  induction word generalizing x with
  | nil => simp [Graph.starts, TransitivePaths.WordPath] <;> rfl
  | cons r tail ih =>
    simp [Graph.starts, TransitivePaths.WordPath, Graph.oriented_iff, List.any_eq_true, Graph.worlds, ih, and_comm] <;> rfl

/-- Dynamic programming over the suffixes of the word. -/
def Graph.path (g : Graph) (word : List OrientedRole) (x y : g.World) : Bool :=
  (g.starts y word).contains x

theorem Graph.path_iff (g : Graph) (word : List OrientedRole) (x y : g.World) :
    g.path word x y = true ↔ TransitivePaths.WordPath g.interpretation word x y := by
  simpa only [Graph.path, List.contains_iff_mem] using g.mem_starts word x y

def checkRoleAxioms (rules : RoleTheory) (chains : List Chain) (g : Graph) : Bool :=
  rules.all (fun (r,s) => g.worlds.all fun x => g.worlds.all fun y =>
    !g.oriented r x y || g.oriented s x y) &&
  chains.all (fun c => g.worlds.all fun x => g.worlds.all fun y =>
    !g.path c.body x y || g.edge c.head x y)

private theorem implies_of_check {p q : Bool} (h : (!p || q) = true) (hp : p = true) : q = true := by
  simpa [hp] using h

private theorem check_implication {p q : Bool} (h : p = true → q = true) : (!p || q) = true := by
  cases p with
  | false => rfl
  | true => simpa using h rfl

theorem checkRoleAxioms_iff {rules chains g} :
    checkRoleAxioms rules chains g = true ↔
      modelsRoles g.interpretation rules ∧ modelsChains g.interpretation chains := by
  simp only [checkRoleAxioms, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hr,hc⟩
    refine ⟨?_,?_⟩
    · intro r s hrs x y he
      exact (g.oriented_iff s x y).mp (implies_of_check
        (hr (r,s) hrs x (List.mem_finRange _) y (List.mem_finRange _))
        ((g.oriented_iff r x y).mpr he))
    · intro c hc' x y hp
      exact implies_of_check
        (hc c hc' x (List.mem_finRange _) y (List.mem_finRange _))
        ((g.path_iff c.body x y).mpr hp)
  · rintro ⟨hr,hc⟩
    refine ⟨?_,?_⟩
    · rintro ⟨r,s⟩ hrs x _ y _
      exact check_implication fun h => (g.oriented_iff s x y).mpr
        (hr r s hrs x y ((g.oriented_iff r x y).mp h))
    · intro c hchain x _ y _
      exact check_implication fun h => hc c hchain x y ((g.path_iff c.body x y).mp h)

def checkGraph (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) (g : Graph) : Bool :=
  checkRoleAxioms rules chains g &&
  tbox.all (fun q => g.worlds.all fun x => !g.holds x q.sub || g.holds x q.sup) &&
  g.worlds.any (fun x => g.holds x root)

theorem checkGraph_sound {rules chains tbox root g}
    (h : checkGraph rules chains tbox root g = true) : ConceptSat rules chains tbox root := by
  simp only [checkGraph, Bool.and_eq_true, List.all_eq_true] at h
  have ⟨hr,hc⟩ := checkRoleAxioms_iff.mp h.1.1
  refine ⟨g.interpretation,hr,hc,?_,?_⟩
  · intro q hq x hx
    exact (g.holds_iff x q.sup).mp (implies_of_check
      (h.1.2 q hq x (List.mem_finRange _)) ((g.holds_iff x q.sub).mpr hx))
  · obtain ⟨x, _, hx⟩ := List.any_eq_true.mp h.2
    exact ⟨x, (g.holds_iff x root).mp hx⟩

/-- Every explicitly supplied graph satisfying the problem passes the same
    check used for generated graph evidence. -/
theorem checkGraph_complete {rules chains tbox root g}
    (hr : modelsRoles g.interpretation rules) (hc : modelsChains g.interpretation chains)
    (ht : models g.interpretation tbox) (hw : ∃ x, ALC.holds g.interpretation x root) :
    checkGraph rules chains tbox root g = true := by
  simp only [checkGraph, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  obtain ⟨w,hw⟩ := hw
  refine ⟨⟨checkRoleAxioms_iff.mpr ⟨hr,hc⟩,?_⟩,w,List.mem_finRange _,(g.holds_iff w root).mpr hw⟩
  intro q hq x _
  exact check_implication fun h => (g.holds_iff x q.sup).mpr (ht q hq x ((g.holds_iff x q.sub).mp h))

end Sabrina.RoleChains
