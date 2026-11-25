import Sabrina.OWL2.SROIQD.Termination.Closure
import Sabrina.RoleChains.RankedCompletion

/-! Finite automaton guards for universal restrictions. The existing ranked
compiler establishes the role language, and its derivative automaton supplies
the states that can be carried on a blocked tableau node. -/
namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole)
open Sabrina.RoleChains (PathRegex Word Rank checkRegular)
open Sabrina.RoleChains.RankedPaths (compile normalize Generated)
open Sabrina.RoleChains.TransitivePaths (WordPath)
open Sabrina.OWL2.Datatypes (datatypeMap)

structure Guard where
  state : PathRegex
  filler : Concept
  deriving DecidableEq, Repr

def roleLanguage (rank : Rank) (p : Problem) (r : OrientedRole) : PathRegex :=
  compile rank p.rules (normalize p.chains) r

theorem roleLanguage_accepts {rank : Rank} {p : Problem}
    (hr : checkRegular rank p.rules p.chains = true) (r : OrientedRole) (w : Word) :
    (roleLanguage rank p r).accepts w = true ↔ Generated p.rules (normalize p.chains) r w :=
  ((roleLanguage rank p r).accepts_iff w).trans
    (Sabrina.RoleChains.RankedPaths.compile_correct (Sabrina.RoleChains.checkRegular_sound hr) r w)

def guardStates (rank : Rank) (p : Problem) (r : OrientedRole) (c : Concept) : List Guard :=
  let e := roleLanguage rank p r
  (e :: e.residuals).map (fun state => ⟨state,c⟩)

def guards (rank : Rank) (p : Problem) : List Guard :=
  ((clos p).flatMap fun
    | .all r c => guardStates rank p r c
    | _ => []).eraseDups

theorem initial_guard_mem {rank : Rank} {p : Problem} {r : OrientedRole} {c : Concept}
    (h : .all r c ∈ clos p) : (⟨roleLanguage rank p r,c⟩ : Guard) ∈ guards rank p := by
  simp only [guards, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.all r c,h,List.mem_map.mpr ⟨_,List.mem_cons_self ..,rfl⟩⟩

def Guard.advance (g : Guard) (r : OrientedRole) : List Guard :=
  (g.state.derivative r).map (fun state => ⟨state,g.filler⟩)

private theorem guardStates_closed {rank : Rank} {p : Problem} {r : OrientedRole}
    {c : Concept} {g : Guard} (hg : g ∈ guardStates rank p r c) (s : OrientedRole) :
    g.advance s ⊆ guardStates rank p r c := by
  obtain ⟨state,hs,rfl⟩ := List.mem_map.mp hg
  intro q hq
  obtain ⟨qState,hnext,rfl⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  refine ⟨qState,List.mem_cons_of_mem _ ?_,rfl⟩
  rcases List.mem_cons.mp hs with rfl | h
  · exact (roleLanguage rank p r).derivative_subset s hnext
  · exact PathRegex.residuals_closed h s hnext

theorem guards_closed {rank : Rank} {p : Problem} {g : Guard} (hg : g ∈ guards rank p)
    (r : OrientedRole) : g.advance r ⊆ guards rank p := by
  simp only [guards, List.mem_eraseDups, List.mem_flatMap] at hg
  obtain ⟨c,hc,hg⟩ := hg
  cases c <;> try (simp at hg; done)
  rename_i role filler
  intro q hq
  simp only [guards, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.all role filler,hc,guardStates_closed hg r hq⟩

theorem guard_filler_mem {rank : Rank} {p : Problem} {g : Guard} (hg : g ∈ guards rank p) :
    g.filler ∈ clos p := by
  simp only [guards, List.mem_eraseDups, List.mem_flatMap] at hg
  obtain ⟨c,hc,hg⟩ := hg
  cases c <;> try (simp at hg; done)
  rename_i role filler
  obtain ⟨state,_,rfl⟩ := List.mem_map.mp hg
  exact clos_operands hc (by simp [operands])

private def objectReduct (i : Interpretation datatypeMap) : Sabrina.ALC.Interpretation where
  Domain := i.Object
  nonempty := i.objectNonempty
  atom := i.classes
  role := i.objectProperties

private theorem oriented_iff (i : Interpretation datatypeMap) (r : OrientedRole) (x y : i.Object) :
    Sabrina.ALC.holdsRole (objectReduct i) r x y ↔ holdsOriented i r x y := by
  rcases r with ⟨_, _ | _⟩ <;> rfl

private theorem word_path_iff (i : Interpretation datatypeMap) (body : List OrientedRole)
    (x y : i.Object) :
    Sabrina.RoleChains.TransitivePaths.WordPath (objectReduct i) body x y ↔ objPath i body x y := by
  induction body generalizing x with
  | nil => rfl
  | cons r rest ih =>
    constructor
    · rintro ⟨z,hr,hp⟩
      exact ⟨z,(oriented_iff i r _ _).mp hr,(ih z).mp hp⟩
    · rintro ⟨z,hr,hp⟩
      exact ⟨z,(oriented_iff i r _ _).mpr hr,(ih z).mpr hp⟩

/-- A guard asserts the filler at the end of every path accepted by its state. -/
def Guard.Holds (i : Interpretation datatypeMap) (x : i.Object) (g : Guard) : Prop :=
  ∀ w y, g.state.Matches w → WordPath (objectReduct i) w x y → holds i y g.filler

theorem initial_guard_sound {rank : Rank} {p : Problem} {i : Interpretation datatypeMap}
    (hr : checkRegular rank p.rules p.chains = true) (hm : p.Models i)
    {r : OrientedRole} {x : i.Object} {c : Concept} (h : holds i x (.all r c)) :
    Guard.Holds i x ⟨roleLanguage rank p r,c⟩ := by
  have hroles : Sabrina.ALC.modelsRoles (objectReduct i) p.rules := by
    intro a b hab u v huv
    exact (oriented_iff i b u v).mpr (hm.rules (a,b) hab u v ((oriented_iff i a u v).mp huv))
  have hchains : Sabrina.RoleChains.modelsChains (objectReduct i) p.chains := by
    intro ch hch u v hp
    exact hm.chains ch hch u v ((word_path_iff i ch.body u v).mp hp)
  intro w y hw hp
  have hgenerated :=
    (Sabrina.RoleChains.RankedPaths.compile_correct (Sabrina.RoleChains.checkRegular_sound hr) r w).mp hw
  exact h y ((oriented_iff i r x y).mp
    (Sabrina.RoleChains.RankedPaths.Generated.sound hgenerated hroles hchains hp))

theorem guard_step_sound {i : Interpretation datatypeMap} {x y : i.Object}
    {g nextGuard : Guard} {r : OrientedRole} (hg : g.Holds i x) (hr : holdsOriented i r x y)
    (hs : nextGuard ∈ g.advance r) : nextGuard.Holds i y := by
  change nextGuard ∈ (g.state.derivative r).map (fun state => ⟨state, g.filler⟩) at hs
  obtain ⟨state,hstate,rfl⟩ :=
    (List.mem_map (f := fun state => (⟨state, g.filler⟩ : Guard))).mp hs
  intro w z hw hp
  exact hg (r :: w) z ((PathRegex.matches_derivative _ _ _).mpr ⟨state,hstate,hw⟩)
    ⟨y,(oriented_iff i r x y).mpr hr,hp⟩

theorem guard_accept_sound {i : Interpretation datatypeMap} {x : i.Object}
    {g : Guard} (hg : g.Holds i x) (h : g.state.nullable = true) : holds i x g.filler :=
  hg [] x (g.state.nullable_iff.mp h) rfl

/-- Ordinary concepts and automaton-state labels use a common finite alphabet. -/
def alphabet (rank : Rank) (p : Problem) : List (Concept ⊕ Guard) :=
  (clos p).map Sum.inl ++ (guards rank p).map Sum.inr

theorem mixed_label_set_bound (rank : Rank) (p : Problem) :
    ∃ rows : List (List (Concept ⊕ Guard)), rows.length = 2 ^ (alphabet rank p).length ∧
      ∀ keep : Concept ⊕ Guard → Bool, (alphabet rank p).filter keep ∈ rows :=
  ⟨subsets _,subsets_length _,fun keep => filter_mem_subsets keep _⟩

#print axioms roleLanguage_accepts
#print axioms guards_closed
#print axioms guard_filler_mem
#print axioms initial_guard_sound
#print axioms guard_step_sound
#print axioms guard_accept_sound
#print axioms mixed_label_set_bound

end Sabrina.OWL2.SROIQD.Termination
