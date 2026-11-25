import Sabrina.OWL2.SROIQD.Termination.ForestUnraveling

/-!
Core forest operations and invariant/realization/witness-preservation theorems
for full cyclic `SROIQ`:
- Initial forest construction from a `Problem` (`BlockedForest.initial`),
- Local enrichments (`addLabel`, `addGuard`, `addEdge`),
- Blockable witness allocation (`appendChildren`) and NN-rule root allocation
  (`appendNNRoots`),
- Unified forest merge (`mergeForest`) covering root-to-root merges,
  blockable-to-root merges, sibling merges, and parent/grandparent ancestor
  merges, together with realization, alphabet-within, binding, geometric depth/
  level bounds, and protected-witness preservation.
-/

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank)
open Sabrina.RoleChains.TransitivePaths (converse_converse)

namespace BlockedForest

private theorem orientation_flip (i : Interpretation datatypeMap) (r : OrientedRole)
    (x y : i.Object) : holdsOriented i (converse r) y x ↔ holdsOriented i r x y := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

private theorem ite_some_eq_some {α : Type} {P : Prop} [Decidable P] {a b : α}
    (h : (if P then some a else none) = some b) : P ∧ a = b := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte, Option.some.injEq] at h; exact ⟨hp, h⟩
  · simp only [hp, ↓reduceIte] at h; cases h

private theorem ite_none_some_eq_some {α : Type} {P : Prop} {inst : Decidable P} {a b : α}
    (h : (@ite _ P inst none (some a)) = some b) : ¬ P ∧ a = b := by
  cases inst with
  | isTrue hp => cases h
  | isFalse hnp => cases h; exact ⟨hnp, rfl⟩

/-! ### Shared search invariants and witness predicates -/

/-- Geometric invariants maintained across all reachable `SROIQ` search states:
1. root `0` always has nominal level `0`,
2. all roots bound to input individuals have nominal level `0`,
3. every node has depth `≤ sroiqMaxDepth rank p + 1`,
4. every root has `nomLevel ≤ sroiqMaxDepth rank p`,
5. every non-child `toRoot` edge from blockable `x` to root `r` satisfies
   `depth x + nomLevel r ≤ sroiqMaxDepth rank p`. -/
structure ForestGeom (rank : Rank) (p : Problem) (b : BlockedForest) : Prop where
  nomLevel0 : b.nomLevel 0 = 0
  boundNomZero : ∀ a r, (a, r) ∈ b.noms → b.nomLevel r = 0
  boundAnonZero : ∀ k r, (k, r) ∈ b.anons → b.nomLevel r = 0
  depthBound : ∀ x : b.Node, b.depth x ≤ sroiqMaxDepth rank p + 1
  nomLevelBound : ∀ r : b.Node, b.isRoot r = true → b.nomLevel r ≤ sroiqMaxDepth rank p
  toRootBound : ∀ x : b.Node, ∀ e ∈ b.toRoot x, b.depth x + b.nomLevel e.2 ≤ sroiqMaxDepth rank p

/-- ABox constraints carried across all reachable search states. -/
structure ABoxSeeded (p : Problem) (b : BlockedForest) : Prop where
  root : p.root ∈ b.labels 0
  classAssertions : ∀ ac ∈ p.classAssertions, ∀ r, b.BoundTo ac.1 r → ac.2 ∈ b.labels r
  objAssertions : ∀ rab ∈ p.objAssertions, ∀ r₁ r₂,
    b.BoundTo rab.2.1 r₁ → b.BoundTo rab.2.2 r₂ → b.Edge (rab.1, false) r₁ r₂
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, ∀ r₁,
    b.BoundTo rab.2.1 r₁ → .all (rab.1, false) (.nom rab.2.2 false) ∈ b.labels r₁
  sameInds : ∀ ab ∈ p.sameInds, ∀ r₁,
    b.BoundTo ab.1 r₁ → .nom ab.2 true ∈ b.labels r₁
  diffInds : ∀ ab ∈ p.diffInds, ∀ r₁,
    b.BoundTo ab.1 r₁ → .nom ab.2 false ∈ b.labels r₁
  dataAssertions : ∀ dal ∈ p.dataAssertions, ∀ r,
    b.BoundTo dal.2.1 r → .dataValue dal.1 dal.2.2 true ∈ b.labels r
  negDataAssertions : ∀ dal ∈ p.negDataAssertions, ∀ r,
    b.BoundTo dal.2.1 r → .dataValue dal.1 dal.2.2 false ∈ b.labels r

/-- Explicit inequality between two template nodes (symmetric). -/
def RecordedDistinct (b : BlockedForest) (x y : b.Node) : Prop :=
  (x, y) ∈ b.unequal ∨ (y, x) ∈ b.unequal

theorem RecordedDistinct.symm {b : BlockedForest} {x y : b.Node}
    (h : b.RecordedDistinct x y) : b.RecordedDistinct y x :=
  h.elim Or.inr Or.inl

instance (b : BlockedForest) (x y : b.Node) : Decidable (b.RecordedDistinct x y) := by
  unfold RecordedDistinct; infer_instance

/-- Witness list for `(x, r, c, n)` where witnesses are pairwise recorded
distinct and, when `x` is a root, every witness is either a root or a direct
child of `x` (guaranteeing unblockedness and survival across subtree prunes). -/
def ProtectedWitnesses (b : BlockedForest) (x : b.Node) (r : OrientedRole)
    (c : Concept) (n : Nat) : Prop :=
  ∃ ys : List b.Node, ys.length = n ∧ ys.Nodup ∧
    ys.Pairwise b.RecordedDistinct ∧
    ∀ y ∈ ys, (b.isRoot x = true → b.isRoot y = true ∨ b.Child x y) ∧
      b.Edge r x y ∧ c ∈ b.labels y

/-- Whether a generating concept `some`/`min` already has protected witnesses. -/
def GenProtected (b : BlockedForest) (x : b.Node) : Concept → Prop
  | .some r c => b.ProtectedWitnesses x r c 1
  | .min n r c => b.ProtectedWitnesses x r c n
  | _ => True

/-- Whether an upper-bound concept `.max _ r c` already has an NN-rule entry at `x`. -/
def HasNNBound (b : BlockedForest) (x : b.Node) : Concept → Prop
  | .max _ r c => ∃ ts, (x, r, c, ts) ∈ b.nnBounds
  | _ => True

/-! ### Helper lemmas for alphabets and membership -/

theorem sroiqRoleNames_of_concept {p : Problem} {c : Concept} (hc : c ∈ sroiqClos p) :
    (∀ r d, c = .some r d → r.1 ∈ sroiqRoleNames p) ∧
    (∀ r d, c = .all r d → r.1 ∈ sroiqRoleNames p) ∧
    (∀ n r d, c = .min n r d → r.1 ∈ sroiqRoleNames p) ∧
    (∀ n r d, c = .max n r d → r.1 ∈ sroiqRoleNames p) ∧
    (∀ r s, c = .self r s → r.1 ∈ sroiqRoleNames p) := by
  have mem_rn (r : IRI) (h : r ∈ (sroiqClos p).flatMap sroiqConceptRoles) : r ∈ sroiqRoleNames p := by
    simp only [sroiqRoleNames, List.mem_eraseDups, List.mem_append]
    grind
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro r d rfl; exact mem_rn r.1 (List.mem_flatMap.mpr ⟨.some r d, hc, by simp [sroiqConceptRoles]⟩)
  · rintro r d rfl; exact mem_rn r.1 (List.mem_flatMap.mpr ⟨.all r d, hc, by simp [sroiqConceptRoles]⟩)
  · rintro n r d rfl; exact mem_rn r.1 (List.mem_flatMap.mpr ⟨.min n r d, hc, by simp [sroiqConceptRoles]⟩)
  · rintro n r d rfl; exact mem_rn r.1 (List.mem_flatMap.mpr ⟨.max n r d, hc, by simp [sroiqConceptRoles]⟩)
  · rintro r s rfl; exact mem_rn r.1 (List.mem_flatMap.mpr ⟨.self r s, hc, by simp [sroiqConceptRoles]⟩)

theorem sroiqRoleNames_of_rule {p : Problem} {q : OrientedRole × OrientedRole}
    (hq : q ∈ p.rules) : q.1.1 ∈ sroiqRoleNames p ∧ q.2.1 ∈ sroiqRoleNames p := by
  have h1 : q.1.1 ∈ p.rules.flatMap (fun (r, s) => [r.1, s.1]) :=
    List.mem_flatMap.mpr ⟨q, hq, by simp⟩
  have h2 : q.2.1 ∈ p.rules.flatMap (fun (r, s) => [r.1, s.1]) :=
    List.mem_flatMap.mpr ⟨q, hq, by simp⟩
  simp only [sroiqRoleNames, List.mem_eraseDups, List.mem_append]
  grind

theorem sroiqRoleNames_of_refl {p : Problem} {r : IRI} (hr : r ∈ p.chars.reflexive) :
    r ∈ sroiqRoleNames p := by
  simp only [sroiqRoleNames, List.mem_eraseDups, List.mem_append]
  grind

theorem sroiqRoleNames_of_objAssertion {p : Problem} {rab : IRI × Individual × Individual}
    (h : rab ∈ p.objAssertions) : rab.1 ∈ sroiqRoleNames p := by
  have hm : rab.1 ∈ p.objAssertions.map Prod.fst := List.mem_map.mpr ⟨rab, h, rfl⟩
  simp only [sroiqRoleNames, List.mem_eraseDups, List.mem_append]
  grind

theorem sroiqRoleNames_of_key {p : Problem} {k : KeyAxiom} (hk : k ∈ p.keys)
    {r : OrientedRole} (hr : r ∈ k.objProps) : r.1 ∈ sroiqRoleNames p := by
  have hm : r.1 ∈ p.keys.flatMap (fun k => k.objProps.map Prod.fst) :=
    List.mem_flatMap.mpr ⟨k, hk, List.mem_map_of_mem hr⟩
  simp only [sroiqRoleNames, List.mem_eraseDups, List.mem_append]
  grind

theorem root_mem_sroiqClos (p : Problem) : p.root ∈ sroiqClos p :=
  sroiqSeed_mem_clos (base_seed_mem_sroiqSeeds (by simp [seeds]))

theorem tbox_mem_sroiqClos {p : Problem} {q : Inclusion} (hq : q ∈ p.tbox) :
    q.sub.dual ∈ sroiqClos p ∧ q.sup ∈ sroiqClos p := by
  have hsub : q.sub ∈ seeds p := by
    have hm : q.sub ∈ p.tbox.flatMap (fun a => [a.sub, a.sup]) :=
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩
    simp [seeds, hm]
  have hsup : q.sup ∈ seeds p := by
    have hm : q.sup ∈ p.tbox.flatMap (fun a => [a.sub, a.sup]) :=
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩
    simp [seeds, hm]
  exact ⟨sroiqSeed_dual_mem_clos (base_seed_mem_sroiqSeeds hsub),
    sroiqSeed_mem_clos (base_seed_mem_sroiqSeeds hsup)⟩

theorem classAssertion_mem_sroiqClos {p : Problem} {ac : Individual × Concept}
    (h : ac ∈ p.classAssertions) : ac.2 ∈ sroiqClos p := by
  have hm : ac.2 ∈ seeds p := by
    have m : ac.2 ∈ p.classAssertions.map Prod.snd := List.mem_map.mpr ⟨ac, h, rfl⟩
    simp [seeds, m]
  exact sroiqSeed_mem_clos (base_seed_mem_sroiqSeeds hm)

theorem negObjAssertion_mem_sroiqClos {p : Problem} {rab : IRI × Individual × Individual}
    (h : rab ∈ p.negObjAssertions) :
    .all (rab.1, false) (.nom rab.2.2 false) ∈ sroiqClos p := by
  apply sroiqSeed_mem_clos
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨rab, h, rfl⟩

theorem allInd_nom_mem_sroiqClos {p : Problem} {ind : Individual} (h : ind ∈ p.allIndividuals) :
    Concept.nom ind true ∈ sroiqClos p ∧ Concept.nom ind false ∈ sroiqClos p := by
  have hm : Concept.nom ind true ∈ seeds p := by
    have m : Concept.nom ind true ∈ p.allIndividuals.map (fun a => Concept.nom a true) :=
      List.mem_map.mpr ⟨ind, h, rfl⟩
    simp [seeds, m]
  exact ⟨sroiqSeed_mem_clos (base_seed_mem_sroiqSeeds hm),
    sroiqSeed_dual_mem_clos (base_seed_mem_sroiqSeeds hm)⟩

theorem key_cls_mem_sroiqClos {p : Problem} {k : KeyAxiom} (hk : k ∈ p.keys) :
    k.cls ∈ sroiqClos p ∧ k.cls.dual ∈ sroiqClos p := by
  have hm : k.cls ∈ seeds p := by
    have m : k.cls ∈ p.keys.map KeyAxiom.cls := List.mem_map.mpr ⟨k, hk, rfl⟩
    simp [seeds, m]
  exact ⟨sroiqSeed_mem_clos (base_seed_mem_sroiqSeeds hm),
    sroiqSeed_dual_mem_clos (base_seed_mem_sroiqSeeds hm)⟩

theorem key_objSplit_mem_sroiqClos {p : Problem} {k : KeyAxiom} (hk : k ∈ p.keys)
    {r : OrientedRole} (hr : r ∈ k.objProps) {a : IRI} (ha : a ∈ p.nominals) :
    .all r (.nom (.named a) false) ∈ sroiqClos p := by
  apply sroiqSeed_mem_clos
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨k, hk, List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨a, ha, rfl⟩⟩⟩

theorem dataAssertion_mem_sroiqClos {p : Problem} {dal : IRI × Individual × Literal}
    (h : dal ∈ p.dataAssertions) : .dataValue dal.1 dal.2.2 true ∈ sroiqClos p := by
  apply sroiqSeed_mem_clos
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨dal, h, rfl⟩

theorem negDataAssertion_mem_sroiqClos {p : Problem} {dal : IRI × Individual × Literal}
    (h : dal ∈ p.negDataAssertions) : .dataValue dal.1 dal.2.2 false ∈ sroiqClos p := by
  apply sroiqSeed_mem_clos
  apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨dal, h, rfl⟩

theorem edge_role_within {b : BlockedForest} {p : Problem} (hw : b.RolesWithin p)
    {r : OrientedRole} {x y : b.Node} (he : b.Edge r x y) :
    r.1 ∈ sroiqRoleNames p := by
  rcases he with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h
  · exact (hw.1 x).2.2 h
  · rcases r with ⟨r, _ | _⟩
    · exact hw.2.1 _ h
    · exact hw.2.1 _ h
  · rcases r with ⟨r, _ | _⟩
    · exact (hw.1 y).1 h
    · exact (hw.1 y).2.1 h
  · rcases r with ⟨r, _ | _⟩
    · exact (hw.1 x).2.1 h
    · exact (hw.1 x).1 h
  · exact hw.2.2 x _ h
  · exact hw.2.2 y _ h

def sroiqOrientedRoles (p : Problem) : List OrientedRole :=
  (sroiqRoleNames p).flatMap (fun r => [(r, false), (r, true)])

theorem mem_sroiqOrientedRoles {p : Problem} {r : OrientedRole}
    (h : r.1 ∈ sroiqRoleNames p) : r ∈ sroiqOrientedRoles p := by
  rcases r with ⟨r, _ | _⟩ <;> exact List.mem_flatMap.mpr ⟨r, h, by simp⟩

/-! ### Initial forest construction -/

private def initNoms (p : Problem) : List IRI := p.nominals.eraseDups
private def initAnons (p : Problem) : List (String × String) := p.anons.eraseDups

private theorem initNoms_nodup (p : Problem) : (initNoms p).Nodup := nodup_eraseDups_list _
private theorem initAnons_nodup (p : Problem) : (initAnons p).Nodup := nodup_eraseDups_list _

private def initNomPairs (p : Problem) :
    List (IRI × Fin ((initNoms p).length + (initAnons p).length + 1)) :=
  (List.finRange (initNoms p).length).map fun i =>
    ((initNoms p).get i, ⟨i.val + 1, by omega⟩)

private def initAnonPairs (p : Problem) :
    List ((String × String) × Fin ((initNoms p).length + (initAnons p).length + 1)) :=
  (List.finRange (initAnons p).length).map fun i =>
    ((initAnons p).get i, ⟨(initNoms p).length + i.val + 1, by omega⟩)

private def initNodeInd (p : Problem)
    (x : Fin ((initNoms p).length + (initAnons p).length + 1)) : Option Individual :=
  if _h0 : x.val = 0 then none
  else if h1 : x.val - 1 < (initNoms p).length then
    some (.named ((initNoms p).get ⟨x.val - 1, h1⟩))
  else
    have hlt : x.val - 1 - (initNoms p).length < (initAnons p).length := by
      have hx := x.isLt; omega
    let k := (initAnons p).get ⟨x.val - 1 - (initNoms p).length, hlt⟩
    some (.anonymous k.1 k.2)

private theorem mem_initNomPairs_iff {p : Problem} {a : IRI}
    {x : Fin ((initNoms p).length + (initAnons p).length + 1)} :
    (a, x) ∈ initNomPairs p ↔ initNodeInd p x = some (.named a) := by
  constructor
  · intro h
    obtain ⟨i, _, heq⟩ := List.mem_map.mp h
    have ha : (initNoms p).get i = a := congrArg Prod.fst heq
    have hx : (⟨i.val + 1, by omega⟩ : Fin _) = x := congrArg Prod.snd heq
    subst hx; subst ha
    have h0 : ¬ (i.val + 1 = 0) := by omega
    have h1 : i.val + 1 - 1 < (initNoms p).length := by omega
    simp only [initNodeInd, h0, ↓reduceDIte, h1]
    have hi : (⟨i.val + 1 - 1, h1⟩ : Fin (initNoms p).length) = i := Fin.ext (by simp)
    rw [hi]
  · intro h
    unfold initNodeInd at h
    split at h
    · cases h
    · split at h
      · rename_i h0 h1
        have ha : (initNoms p).get ⟨x.val - 1, h1⟩ = a := by
          have := Option.some.inj h; cases this; rfl
        refine List.mem_map.mpr ⟨⟨x.val - 1, h1⟩, List.mem_finRange _, ?_⟩
        apply Prod.ext
        · exact ha
        · apply Fin.ext; dsimp; omega
      · cases h

private theorem mem_initAnonPairs_iff {p : Problem} {k : String × String}
    {x : Fin ((initNoms p).length + (initAnons p).length + 1)} :
    (k, x) ∈ initAnonPairs p ↔ initNodeInd p x = some (.anonymous k.1 k.2) := by
  constructor
  · intro h
    obtain ⟨i, _, heq⟩ := List.mem_map.mp h
    have hk : (initAnons p).get i = k := congrArg Prod.fst heq
    have hx : (⟨(initNoms p).length + i.val + 1, by omega⟩ : Fin _) = x := congrArg Prod.snd heq
    subst hx; subst hk
    have h0 : ¬ ((initNoms p).length + i.val + 1 = 0) := by omega
    have h1 : ¬ ((initNoms p).length + i.val + 1 - 1 < (initNoms p).length) := by omega
    simp only [initNodeInd, h0, ↓reduceDIte, h1]
    have hi : (⟨(initNoms p).length + i.val + 1 - 1 - (initNoms p).length, by omega⟩ :
        Fin (initAnons p).length) = i := Fin.ext (by dsimp; omega)
    rw [hi]
  · intro h
    unfold initNodeInd at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h0 h1
        have hlt : x.val - 1 - (initNoms p).length < (initAnons p).length := by
          have hx := x.isLt; omega
        have hk : (initAnons p).get ⟨x.val - 1 - (initNoms p).length, hlt⟩ = k := by
          have := Option.some.inj h
          rcases k with ⟨d, l⟩
          cases this; rfl
        refine List.mem_map.mpr ⟨⟨x.val - 1 - (initNoms p).length, hlt⟩, List.mem_finRange _, ?_⟩
        apply Prod.ext
        · exact hk
        · apply Fin.ext; dsimp; omega

private def initLookupInd (p : Problem) :
    Individual → Option (Fin ((initNoms p).length + (initAnons p).length + 1))
  | .named a => (initNomPairs p).lookup a
  | .anonymous d l => (initAnonPairs p).lookup (d, l)

private def initLabels (p : Problem)
    (x : Fin ((initNoms p).length + (initAnons p).length + 1)) : List Concept :=
  match initNodeInd p x with
  | none => [p.root]
  | some ind =>
    (p.classAssertions.filterMap fun (a, c) => if a == ind then some c else none) ++
    (p.negObjAssertions.filterMap fun (r, a, b) =>
      if a == ind then some (.all (r, false) (.nom b false)) else none) ++
    (p.sameInds.filterMap fun (a, b) => if a == ind then some (.nom b true) else none) ++
    (p.diffInds.filterMap fun (a, b) => if a == ind then some (.nom b false) else none) ++
    (p.dataAssertions.filterMap fun (dp, a, l) =>
      if a == ind then some (.dataValue dp l true) else none) ++
    (p.negDataAssertions.filterMap fun (dp, a, l) =>
      if a == ind then some (.dataValue dp l false) else none)

private def initLoops (p : Problem)
    (x : Fin ((initNoms p).length + (initAnons p).length + 1)) : List IRI :=
  match initNodeInd p x with
  | none => []
  | some ind =>
    p.objAssertions.filterMap fun (r, a, b) => if a == ind && b == ind then some r else none

private def initRootEdges (p : Problem) :
    List (IRI × Fin ((initNoms p).length + (initAnons p).length + 1) ×
      Fin ((initNoms p).length + (initAnons p).length + 1)) :=
  p.objAssertions.filterMap fun (r, a, b) =>
    match initLookupInd p a, initLookupInd p b with
    | some x, some y => if x ≠ y then some (r, x, y) else none
    | _, _ => none

/-- Initial nominal-rooted blocked forest for a `SROIQ` problem.
Node `0` carries `p.root`; each distinct named or anonymous individual in `p`
gets a dedicated level-0 root node seeded with its ABox assertions. -/
def initial (p : Problem) : BlockedForest where
  size := (initNoms p).length + (initAnons p).length
  isRoot _ := true
  root0 := rfl
  nomLevel _ := 0
  parent _ := 0
  parent_lt _ h := by cases h
  labels := initLabels p
  guardLabels _ := []
  down _ := []
  up _ := []
  loops := initLoops p
  rootEdges := initRootEdges p
  rootEdges_valid := by
    intro e he
    obtain ⟨⟨r, a, b⟩, _, hm⟩ := List.mem_filterMap.mp he
    cases ha : initLookupInd p a <;> cases hb : initLookupInd p b <;> simp [ha, hb] at hm
    rcases hm with ⟨hne, rfl⟩
    exact ⟨rfl, rfl, hne⟩
  toRoot _ := []
  toRoot_valid _ _ h := (List.not_mem_nil h).elim
  noms := initNomPairs p
  noms_valid _ _ := rfl
  anons := initAnonPairs p
  anons_valid _ _ := rfl
  unequal := []
  nnBounds := []
  nnBounds_valid _ h := (List.not_mem_nil h).elim
  blockedBy _ := none

theorem initial_boundTo_iff {p : Problem} {ind : Individual} {x : (initial p).Node} :
    (initial p).BoundTo ind x ↔ initNodeInd p x = some ind := by
  cases ind with
  | named a =>
    dsimp only [BoundTo, initial]
    exact mem_initNomPairs_iff
  | anonymous d l =>
    dsimp only [BoundTo, initial]
    exact mem_initAnonPairs_iff

private theorem nodup_keys_initNomPairs (p : Problem) :
    ((initNomPairs p).map Prod.fst).Nodup := by
  have heq : (initNomPairs p).map Prod.fst = initNoms p := by
    apply List.ext_getElem
    · simp [initNomPairs]
    · intro i h1 h2
      simp [initNomPairs]
  rw [heq]
  exact initNoms_nodup p

private theorem nodup_keys_initAnonPairs (p : Problem) :
    ((initAnonPairs p).map Prod.fst).Nodup := by
  have heq : (initAnonPairs p).map Prod.fst = initAnons p := by
    apply List.ext_getElem
    · simp [initAnonPairs]
    · intro i h1 h2
      simp [initAnonPairs]
  rw [heq]
  exact initAnons_nodup p

private theorem list_lookup_eq_some_of_nodup {α β : Type} [DecidableEq α]
    {xs : List (α × β)} (hnd : (xs.map Prod.fst).Nodup) {a : α} {b : β}
    (hm : (a, b) ∈ xs) : xs.lookup a = some b := by
  induction xs with
  | nil => cases hm
  | cons hd tl ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hm with rfl | htl
    · simp [List.lookup]
    · have hne : (a == hd.1) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact hna (heq ▸ List.mem_map.mpr ⟨(a, b), htl, rfl⟩)
      simp only [List.lookup, hne]
      exact ih hnd' htl

private theorem list_mem_of_lookup_eq_some {α β : Type} [DecidableEq α]
    {xs : List (α × β)} {a : α} {b : β} (h : xs.lookup a = some b) : (a, b) ∈ xs := by
  induction xs with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    cases heq : (a == hd.1) with
    | true =>
      simp only [heq] at h
      have h1 : a = hd.1 := beq_iff_eq.mp heq
      have h2 : hd.2 = b := Option.some.inj h
      have hpair : (a, b) = hd := Prod.ext h1 h2.symm
      rw [hpair]
      exact List.mem_cons_self ..
    | false =>
      simp only [heq] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem initLookupInd_eq_some_iff {p : Problem} {ind : Individual}
    {x : Fin ((initNoms p).length + (initAnons p).length + 1)} :
    initLookupInd p ind = some x ↔ (initial p).BoundTo ind x := by
  cases ind with
  | named a =>
    change (initNomPairs p).lookup a = some x ↔ (a, x) ∈ initNomPairs p
    exact ⟨list_mem_of_lookup_eq_some, list_lookup_eq_some_of_nodup (nodup_keys_initNomPairs p)⟩
  | anonymous d l =>
    change (initAnonPairs p).lookup (d, l) = some x ↔ ((d, l), x) ∈ initAnonPairs p
    exact ⟨list_mem_of_lookup_eq_some, list_lookup_eq_some_of_nodup (nodup_keys_initAnonPairs p)⟩

theorem initial_bindings (p : Problem) : (initial p).BindingsValid p := by
  constructor
  · intro a ha
    have hm : a ∈ initNoms p := List.mem_eraseDups.mpr ha
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hm
    have hlt : i + 1 < (initNoms p).length + (initAnons p).length + 1 := by omega
    refine ⟨⟨i + 1, hlt⟩, ?_⟩
    change (a, ⟨i + 1, hlt⟩) ∈ initNomPairs p
    exact List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_finRange _, Prod.ext (by simp [List.get_eq_getElem, heq]) rfl⟩
  · intro k hk
    have hm : k ∈ initAnons p := List.mem_eraseDups.mpr hk
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hm
    have hlt : (initNoms p).length + i + 1 < (initNoms p).length + (initAnons p).length + 1 := by omega
    refine ⟨⟨(initNoms p).length + i + 1, hlt⟩, ?_⟩
    change (k, ⟨(initNoms p).length + i + 1, hlt⟩) ∈ initAnonPairs p
    exact List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_finRange _, Prod.ext (by simp [List.get_eq_getElem, heq]) rfl⟩
  · intro a r₁ r₂ h1 h2
    dsimp only [initial] at h1 h2
    have l1 := list_lookup_eq_some_of_nodup (nodup_keys_initNomPairs p) h1
    have l2 := list_lookup_eq_some_of_nodup (nodup_keys_initNomPairs p) h2
    exact Option.some.inj (l1.symm.trans l2)
  · intro k r₁ r₂ h1 h2
    dsimp only [initial] at h1 h2
    have l1 := list_lookup_eq_some_of_nodup (nodup_keys_initAnonPairs p) h1
    have l2 := list_lookup_eq_some_of_nodup (nodup_keys_initAnonPairs p) h2
    exact Option.some.inj (l1.symm.trans l2)

theorem initial_within (rank : Rank) (p : Problem) : (initial p).Within rank p := by
  refine ⟨?_, fun _ _ h => (List.not_mem_nil h).elim, ?_⟩
  · intro x c hc
    change c ∈ initLabels p x at hc
    unfold initLabels at hc
    cases h : initNodeInd p x with
    | none =>
      simp only [h, List.mem_singleton] at hc
      subst hc; exact root_mem_sroiqClos p
    | some ind =>
      simp only [h, List.mem_append, List.mem_filterMap] at hc
      rcases hc with ((((⟨⟨a, d⟩, hm, hd⟩ | ⟨⟨r, a, b⟩, hm, hd⟩) | ⟨⟨a, b⟩, hm, hd⟩) |
          ⟨⟨a, b⟩, hm, hd⟩) | ⟨⟨dp, a, l⟩, hm, hd⟩) | ⟨⟨dp, a, l⟩, hm, hd⟩
      · split at hd
        · cases hd; exact classAssertion_mem_sroiqClos hm
        · cases hd
      · split at hd
        · cases hd; exact negObjAssertion_mem_sroiqClos hm
        · cases hd
      · split at hd
        · cases hd
          have hb : b ∈ p.allIndividuals := by
            have m : b ∈ p.sameInds.flatMap (fun (x, y) => [x, y]) :=
              List.mem_flatMap.mpr ⟨(a, b), hm, by simp⟩
            simp [Problem.allIndividuals, m]
          exact (allInd_nom_mem_sroiqClos hb).1
        · cases hd
      · split at hd
        · cases hd
          have hb : b ∈ p.allIndividuals := by
            have m : b ∈ p.diffInds.flatMap (fun (x, y) => [x, y]) :=
              List.mem_flatMap.mpr ⟨(a, b), hm, by simp⟩
            simp [Problem.allIndividuals, m]
          exact (allInd_nom_mem_sroiqClos hb).2
        · cases hd
      · split at hd
        · cases hd; exact dataAssertion_mem_sroiqClos hm
        · cases hd
      · split at hd
        · cases hd; exact negDataAssertion_mem_sroiqClos hm
        · cases hd
  · refine ⟨fun x => ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, ?_⟩, ?_, fun _ _ h => (List.not_mem_nil h).elim⟩
    · intro r hr
      change r ∈ initLoops p x at hr
      unfold initLoops at hr
      cases h : initNodeInd p x with
      | none => simp [h] at hr
      | some ind =>
        simp only [h, List.mem_filterMap] at hr
        obtain ⟨⟨r', a, b⟩, hm, hres⟩ := hr
        split at hres
        · cases hres; exact sroiqRoleNames_of_objAssertion hm
        · cases hres
    · intro e he
      dsimp only [initial] at he
      obtain ⟨⟨r, a, b⟩, hm, hres⟩ := List.mem_filterMap.mp he
      cases ha : initLookupInd p a <;> cases hb : initLookupInd p b <;> simp [ha, hb] at hres
      · rename_i u v
        by_cases hne : u = v
        · simp [hne] at hres
        · simp [hne] at hres; cases hres; exact sroiqRoleNames_of_objAssertion hm

theorem initial_geom (rank : Rank) (p : Problem) : (initial p).ForestGeom rank p :=
  ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun x => by rw [depth_root rfl]; exact Nat.zero_le _,
    fun _ _ => Nat.zero_le _,
    fun _ _ h => (List.not_mem_nil h).elim⟩

theorem initial_aboxSeeded (p : Problem) : (initial p).ABoxSeeded p := by
  constructor
  · change p.root ∈ initLabels p 0
    simp [initLabels, initNodeInd]
  · intro ⟨a, c⟩ hm r hr
    have hi := initial_boundTo_iff.mp hr
    change c ∈ initLabels p r
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inl (.inl (.inl (.inl (.inl ⟨(a, c), hm, by simp⟩))))
  · intro ⟨r, a, b⟩ hm r₁ r₂ h1 h2
    by_cases heq : r₁ = r₂
    · subst heq
      apply (edge_loop_iff (initial p) (r, false) r₁).mpr
      have hi1 := initial_boundTo_iff.mp h1
      have hi2 := initial_boundTo_iff.mp h2
      have hab : a = b := Option.some.inj (hi1.symm.trans hi2)
      change r ∈ initLoops p r₁
      simp only [initLoops, hi1, List.mem_filterMap]
      exact ⟨(r, a, b), hm, by simp [hab]⟩
    · apply (edge_root_iff (b := initial p) rfl rfl heq).mpr
      dsimp only [RootEdge, initial, initRootEdges]
      refine List.mem_filterMap.mpr ⟨(r, a, b), hm, ?_⟩
      dsimp only
      have hl1 : initLookupInd p a = some r₁ := initLookupInd_eq_some_iff.mpr h1
      have hl2 : initLookupInd p b = some r₂ := initLookupInd_eq_some_iff.mpr h2
      rw [hl1, hl2]; dsimp only; exact ite_eq_left heq
  · intro ⟨r, a, b⟩ hm r₁ h1
    have hi := initial_boundTo_iff.mp h1
    change .all (r, false) (.nom b false) ∈ initLabels p r₁
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inl (.inl (.inl (.inl (.inr ⟨(r, a, b), hm, by simp⟩))))
  · intro ⟨a, b⟩ hm r₁ h1
    have hi := initial_boundTo_iff.mp h1
    change .nom b true ∈ initLabels p r₁
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inl (.inl (.inl (.inr ⟨(a, b), hm, by simp⟩)))
  · intro ⟨a, b⟩ hm r₁ h1
    have hi := initial_boundTo_iff.mp h1
    change .nom b false ∈ initLabels p r₁
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inl (.inl (.inr ⟨(a, b), hm, by simp⟩))
  · intro ⟨dp, a, l⟩ hm r₁ h1
    have hi := initial_boundTo_iff.mp h1
    change .dataValue dp l true ∈ initLabels p r₁
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inl (.inr ⟨(dp, a, l), hm, by simp⟩)
  · intro ⟨dp, a, l⟩ hm r₁ h1
    have hi := initial_boundTo_iff.mp h1
    change .dataValue dp l false ∈ initLabels p r₁
    simp only [initLabels, hi, List.mem_append, List.mem_filterMap]
    exact .inr ⟨(dp, a, l), hm, by simp⟩

theorem initial_sat_iff (p : Problem) : (initial p).Sat p ↔ p.Sat := by
  constructor
  · rintro ⟨i, hm, env, hr⟩
    exact ⟨i, hm, env 0, hr.labels 0 p.root (initial_aboxSeeded p).root⟩
  · rintro ⟨i, hm, w, hw⟩
    let env : (initial p).Node → i.Object := fun x =>
      match initNodeInd p x with
      | none => w
      | some ind => i.individuals ind
    refine ⟨i, hm, env, ?_⟩
    constructor
    case labels =>
      intro x c hc
      change c ∈ initLabels p x at hc
      unfold initLabels at hc
      cases h : initNodeInd p x with
      | none =>
        simp only [h, List.mem_singleton] at hc
        subst hc; simpa [env, h] using hw
      | some ind =>
        simp only [h, List.mem_append, List.mem_filterMap] at hc
        rcases hc with ((((⟨⟨a, d⟩, hmem, hd⟩ | ⟨⟨r, a, b⟩, hmem, hd⟩) | ⟨⟨a, b⟩, hmem, hd⟩) |
            ⟨⟨a, b⟩, hmem, hd⟩) | ⟨⟨dp, a, l⟩, hmem, hd⟩) | ⟨⟨dp, a, l⟩, hmem, hd⟩
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            simpa [env, h, ha] using hm.classAssertions (a, d) hmem
          · cases hd
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            intro z hz hzb
            have hneg := hm.negObjAssertions (r, a, b) hmem
            simp only [env, h] at hz
            rw [← ha] at hz
            exact hneg (hzb ▸ hz)
          · cases hd
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            have hs := hm.sameInds (a, b) hmem
            simp only [holds, env, h, ← ha]; exact hs
          · cases hd
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            have hd' := hm.diffInds (a, b) hmem
            simp only [holds, env, h, ← ha]; exact hd'
          · cases hd
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            have hda := hm.dataAssertions (dp, a, l) hmem
            simp only [holds, env, h, ← ha]; exact hda
          · cases hd
        · split at hd
          · cases hd; rename_i heq
            have ha : a = ind := beq_iff_eq.mp heq
            have hnda := hm.negDataAssertions (dp, a, l) hmem
            simp only [holds, env, h, ← ha]; exact hnda
          · cases hd
    case edges =>
      intro r x y he
      rcases he with ⟨rfl, hl⟩ | ⟨_, _, hre⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
      · dsimp only [initial] at hl
        unfold initLoops at hl
        cases h : initNodeInd p x with
        | none => simp [h] at hl
        | some ind =>
          simp only [h, List.mem_filterMap] at hl
          obtain ⟨⟨rn, a, b⟩, hmem, hres⟩ := hl
          split at hres
          · rename_i heq
            have hrn : rn = r.1 := Option.some.inj hres
            simp only [Bool.and_eq_true, beq_iff_eq] at heq
            have ho := hm.objAssertions (rn, a, b) hmem
            have hab : a = b := heq.1.trans heq.2.symm
            subst hab
            rcases r with ⟨r0, _ | _⟩
            · dsimp at hrn; subst hrn; simpa [holdsOriented, env, h, ← heq.1] using ho
            · dsimp at hrn; subst hrn; simpa [holdsOriented, env, h, ← heq.1] using ho
          · cases hres
      · have getRoot (s : IRI) (u v : (initial p).Node) (h : (s, u, v) ∈ initRootEdges p) :
            holdsOriented i (s, false) (env u) (env v) := by
          obtain ⟨⟨rn, a, b⟩, hmem, hres⟩ := List.mem_filterMap.mp h
          cases ha : initLookupInd p a <;> cases hb : initLookupInd p b <;> simp [ha, hb] at hres
          rename_i u' v'
          by_cases hne : u' = v'
          · simp [hne] at hres
          · simp [hne] at hres
            obtain ⟨rfl, rfl, rfl⟩ := hres
            have hu := initial_boundTo_iff.mp (initLookupInd_eq_some_iff.mp ha)
            have hv := initial_boundTo_iff.mp (initLookupInd_eq_some_iff.mp hb)
            simpa [env, hu, hv, holdsOriented] using hm.objAssertions (s, a, b) hmem
        rcases r with ⟨s, _ | _⟩
        · exact getRoot s x y hre
        · exact (orientation_flip i (s, false) (env y) (env x)).mp (getRoot s y x hre)
      · cases hc.1
      · cases hc.1
      · cases htr
      · cases htr
    case guards => intro _ _ h; cases h
    case unequal => intro _ _ h; cases h
    case noms =>
      intro a x h
      dsimp only [initial] at h
      have hi := mem_initNomPairs_iff.mp h
      simp [env, hi]
    case anons =>
      intro k x h
      dsimp only [initial] at h
      have hi := mem_initAnonPairs_iff.mp h
      simp [env, hi]
    case nnBounds => intro _ h; cases h
    case keyDisjoint => intro _ h; cases h

/-! ### Depth invariance across same-tree updates -/

theorem depth_eq_of_same_shape {b₁ b₂ : BlockedForest}
    (hs : b₁.size = b₂.size)
    (hr : ∀ x : b₁.Node, b₁.isRoot x = b₂.isRoot ⟨x.val, hs ▸ x.isLt⟩)
    (hp : ∀ x : b₁.Node, b₁.isRoot x = false →
      (b₁.parent x).val = (b₂.parent ⟨x.val, hs ▸ x.isLt⟩).val)
    (x : b₁.Node) : b₁.depth x = b₂.depth ⟨x.val, hs ▸ x.isLt⟩ := by
  by_cases hrx : b₁.isRoot x = true
  · have hrx2 : b₂.isRoot ⟨x.val, hs ▸ x.isLt⟩ = true := (hr x).symm.trans hrx
    rw [depth_root hrx, depth_root hrx2]
  · have hfx : b₁.isRoot x = false := Bool.eq_false_iff.mpr hrx
    have hfx2 : b₂.isRoot ⟨x.val, hs ▸ x.isLt⟩ = false := (hr x).symm.trans hfx
    have hc1 : b₁.Child (b₁.parent x) x := ⟨hfx, rfl⟩
    have hc2 : b₂.Child ⟨(b₁.parent x).val, hs ▸ (b₁.parent x).isLt⟩ ⟨x.val, hs ▸ x.isLt⟩ :=
      ⟨hfx2, Fin.ext (hp x hfx).symm⟩
    rw [depth_child hc1, depth_child hc2]
    exact congrArg Nat.succ (depth_eq_of_same_shape hs hr hp (b₁.parent x))
termination_by x.val
decreasing_by exact b₁.parent_lt x (Bool.eq_false_iff.mpr hrx)

theorem reblock_depth (b : BlockedForest) (x : b.Node) : b.reblock.depth x = b.depth x :=
  depth_eq_of_same_shape (b₁ := b.reblock) (b₂ := b) rfl (fun _ => rfl) (fun _ _ => rfl) x

theorem reblock_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (h : b.Within rank p) : b.reblock.Within rank p :=
  ⟨h.labels, h.guards, h.roles⟩

theorem reblock_bindings {b : BlockedForest} {p : Problem}
    (h : b.BindingsValid p) : b.reblock.BindingsValid p :=
  ⟨h.nomComplete, h.anonComplete, h.nomFunctional, h.anonFunctional⟩

theorem reblock_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (h : b.ForestGeom rank p) : b.reblock.ForestGeom rank p :=
  ⟨h.nomLevel0, h.boundNomZero, h.boundAnonZero,
    fun x => (reblock_depth b x).symm ▸ h.depthBound x,
    h.nomLevelBound,
    fun x e he => (reblock_depth b x).symm ▸ h.toRootBound x e he⟩

theorem reblock_aboxSeeded {b : BlockedForest} {p : Problem}
    (h : b.ABoxSeeded p) : b.reblock.ABoxSeeded p :=
  ⟨h.root, h.classAssertions, h.objAssertions, h.negObjAssertions, h.sameInds, h.diffInds,
    h.dataAssertions, h.negDataAssertions⟩

theorem reblock_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} : b.reblock.Realizes i env ↔ b.Realizes i env :=
  ⟨fun h => ⟨h.labels, h.edges, h.guards, h.unequal, h.noms, h.anons, h.nnBounds, h.keyDisjoint⟩,
   fun h => ⟨h.labels, h.edges, h.guards, h.unequal, h.noms, h.anons, h.nnBounds, h.keyDisjoint⟩⟩

/-! ### Local enrichments: `addLabel`, `addGuard`, `addEdge` -/

def addLabel (b : BlockedForest) (x : b.Node) (c : Concept) : BlockedForest :=
  { b with labels := fun y => if y = x then c :: b.labels y else b.labels y }

theorem addLabel_mem {b : BlockedForest} {x y : b.Node} {c d : Concept} :
    d ∈ (b.addLabel x c).labels y ↔ (y = x ∧ d = c) ∨ d ∈ b.labels y := by
  by_cases hy : y = x
  · subst hy; simp [addLabel]
  · simp [addLabel, hy]

theorem addLabel_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {x : b.Node} {c : Concept}
    (hc : holds i (env x) c) : (b.addLabel x c).Realizes i env :=
  { hr with labels := fun y d hd =>
      (addLabel_mem.mp hd).elim (fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ hc) (hr.labels y d) }

theorem addLabel_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x : b.Node} {c : Concept} (hc : c ∈ sroiqClos p) :
    (b.addLabel x c).Within rank p :=
  { hw with labels := fun y _ hd =>
      (addLabel_mem.mp hd).elim (fun ⟨_, h2⟩ => h2 ▸ hc) (fun hm => hw.labels y hm) }

theorem addLabel_depth (b : BlockedForest) (x : b.Node) (c : Concept) (z : b.Node) :
    (b.addLabel x c).depth z = b.depth z :=
  depth_eq_of_same_shape (b₁ := b.addLabel x c) (b₂ := b) rfl (fun _ => rfl) (fun _ _ => rfl) z

theorem addLabel_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) (x : b.Node) (c : Concept) :
    (b.addLabel x c).ForestGeom rank p :=
  ⟨hg.nomLevel0, hg.boundNomZero, hg.boundAnonZero,
    fun z => (addLabel_depth b x c z).symm ▸ hg.depthBound z,
    hg.nomLevelBound,
    fun z e he => (addLabel_depth b x c z).symm ▸ hg.toRootBound z e he⟩

theorem addLabel_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) (x : b.Node) (c : Concept) :
    (b.addLabel x c).ABoxSeeded p :=
  ⟨addLabel_mem.mpr (.inr ha.root),
    fun ac h r hr => addLabel_mem.mpr (.inr (ha.classAssertions ac h r hr)),
    ha.objAssertions,
    fun rab h r hr => addLabel_mem.mpr (.inr (ha.negObjAssertions rab h r hr)),
    fun ab h r hr => addLabel_mem.mpr (.inr (ha.sameInds ab h r hr)),
    fun ab h r hr => addLabel_mem.mpr (.inr (ha.diffInds ab h r hr)),
    fun dal h r hr => addLabel_mem.mpr (.inr (ha.dataAssertions dal h r hr)),
    fun dal h r hr => addLabel_mem.mpr (.inr (ha.negDataAssertions dal h r hr))⟩

theorem addLabel_protected {b : BlockedForest} {x : b.Node} {c : Concept}
    {z : b.Node} {r : OrientedRole} {d : Concept} {n : Nat}
    (hp : b.ProtectedWitnesses z r d n) : (b.addLabel x c).ProtectedWitnesses z r d n := by
  obtain ⟨ys, hlen, hnd, hdist, hspec⟩ := hp
  exact ⟨ys, hlen, hnd, hdist, fun y hy =>
    ⟨(hspec y hy).1, (hspec y hy).2.1, addLabel_mem.mpr (.inr (hspec y hy).2.2)⟩⟩

def addGuard (b : BlockedForest) (x : b.Node) (g : Guard) : BlockedForest :=
  { b with guardLabels := fun y => if y = x then g :: b.guardLabels y else b.guardLabels y }

theorem addGuard_mem {b : BlockedForest} {x y : b.Node} {g k : Guard} :
    k ∈ (b.addGuard x g).guardLabels y ↔ (y = x ∧ k = g) ∨ k ∈ b.guardLabels y := by
  by_cases hy : y = x
  · subst hy; simp [addGuard]
  · simp [addGuard, hy]

theorem addGuard_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {x : b.Node} {g : Guard}
    (hg : g.Holds i (env x)) : (b.addGuard x g).Realizes i env :=
  { hr with guards := fun y k hk =>
      (addGuard_mem.mp hk).elim (fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ hg) (hr.guards y k) }

theorem addGuard_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {x : b.Node} {g : Guard} (hg : g ∈ sroiqGuards rank p) :
    (b.addGuard x g).Within rank p :=
  { hw with guards := fun y _ hk =>
      (addGuard_mem.mp hk).elim (fun ⟨_, h2⟩ => h2 ▸ hg) (fun hm => hw.guards y hm) }

theorem addGuard_depth (b : BlockedForest) (x : b.Node) (g : Guard) (z : b.Node) :
    (b.addGuard x g).depth z = b.depth z :=
  depth_eq_of_same_shape (b₁ := b.addGuard x g) (b₂ := b) rfl (fun _ => rfl) (fun _ _ => rfl) z

theorem addGuard_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) (x : b.Node) (g : Guard) :
    (b.addGuard x g).ForestGeom rank p :=
  ⟨hg.nomLevel0, hg.boundNomZero, hg.boundAnonZero,
    fun z => (addGuard_depth b x g z).symm ▸ hg.depthBound z,
    hg.nomLevelBound,
    fun z e he => (addGuard_depth b x g z).symm ▸ hg.toRootBound z e he⟩

def addKeyDisjoint (b : BlockedForest) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true) : BlockedForest :=
  { b with
    keyDisjoint := (r₁, r₂, dp) :: b.keyDisjoint
    keyDisjoint_valid := by
      intro e he
      rcases List.mem_cons.mp he with rfl | hm
      · exact ⟨hr₁, hr₂⟩
      · exact b.keyDisjoint_valid e hm }

theorem addKeyDisjoint_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {r₁ r₂ : b.Node} {dp : IRI}
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true)
    (hkd : ∀ y : i.Data, ¬ (i.dataProperties dp (env r₁) y ∧ i.dataProperties dp (env r₂) y)) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).Realizes i env := by
  refine { hr with keyDisjoint := fun e he y => ?_ }
  rcases List.mem_cons.mp he with rfl | hm
  · exact hkd y
  · exact hr.keyDisjoint e hm y

theorem addKeyDisjoint_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).Within rank p :=
  ⟨hw.labels, hw.guards, hw.roles⟩

theorem addKeyDisjoint_depth (b : BlockedForest) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true) (z : b.Node) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).depth z = b.depth z :=
  depth_eq_of_same_shape (b₁ := b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂) (b₂ := b)
    rfl (fun _ => rfl) (fun _ _ => rfl) z

theorem addKeyDisjoint_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).ForestGeom rank p :=
  ⟨hg.nomLevel0, hg.boundNomZero, hg.boundAnonZero,
    fun z => (addKeyDisjoint_depth b r₁ r₂ dp hr₁ hr₂ z).symm ▸ hg.depthBound z,
    hg.nomLevelBound,
    fun z e he => (addKeyDisjoint_depth b r₁ r₂ dp hr₁ hr₂ z).symm ▸ hg.toRootBound z e he⟩

theorem addKeyDisjoint_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) (r₁ r₂ : b.Node) (dp : IRI)
    (hr₁ : b.isRoot r₁ = true) (hr₂ : b.isRoot r₂ = true) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).ABoxSeeded p :=
  ⟨ha.root, ha.classAssertions, ha.objAssertions, ha.negObjAssertions,
    ha.sameInds, ha.diffInds, ha.dataAssertions, ha.negDataAssertions⟩

theorem addKeyDisjoint_protected {b : BlockedForest} {r₁ r₂ : b.Node} {dp : IRI}
    {hr₁ : b.isRoot r₁ = true} {hr₂ : b.isRoot r₂ = true}
    {z : b.Node} {r : OrientedRole} {d : Concept} {n : Nat}
    (hp : b.ProtectedWitnesses z r d n) :
    (b.addKeyDisjoint r₁ r₂ dp hr₁ hr₂).ProtectedWitnesses z r d n := by
  obtain ⟨ys, hlen, hnd, hdist, hspec⟩ := hp
  exact ⟨ys, hlen, hnd, hdist, hspec⟩

/-- Geometric admissibility for adding an edge `(r, x, y)` in a forest:
loop, root-to-root, parent-child, or blockable-to-root (non-parent). -/
def EdgeAdmissible (b : BlockedForest) (x y : b.Node) : Prop :=
  x = y ∨ (b.isRoot x = true ∧ b.isRoot y = true) ∨ b.Child x y ∨ b.Child y x ∨
  (b.isRoot x = false ∧ b.isRoot y = true) ∨ (b.isRoot x = true ∧ b.isRoot y = false)

theorem Edge.admissible {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (h : b.Edge r x y) : b.EdgeAdmissible x y := by
  rcases h with ⟨h, _⟩ | ⟨hx, hy, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
  · exact .inl h
  · exact .inr (.inl ⟨hx, hy⟩)
  · exact .inr (.inr (.inl hc))
  · exact .inr (.inr (.inr (.inl hc)))
  · have ⟨hx, hy, _⟩ := b.toRoot_valid x _ htr
    exact .inr (.inr (.inr (.inr (.inl ⟨hx, hy⟩))))
  · have ⟨hy, hx, _⟩ := b.toRoot_valid y _ htr
    exact .inr (.inr (.inr (.inr (.inr ⟨hx, hy⟩))))

/-- Add an oriented edge `r` from `x` to `y` into the unique disjoint edge
bucket matching their geometric relationship. Preserves `size`, `isRoot`,
`parent`, `nomLevel`, `labels`, `guardLabels`, `noms`, `anons`, `unequal`,
and `nnBounds` definitionally. -/
def addEdge (b : BlockedForest) (r : OrientedRole) (x y : b.Node) : BlockedForest :=
  { b with
    loops := fun z =>
      if x = y ∧ z = x then r.1 :: b.loops z else b.loops z
    rootEdges :=
      if x ≠ y ∧ b.isRoot x = true ∧ b.isRoot y = true then
        (if r.2 then (r.1, y, x) else (r.1, x, y)) :: b.rootEdges
      else b.rootEdges
    rootEdges_valid := by
      intro e he
      split at he
      · rename_i h
        rcases List.mem_cons.mp he with rfl | hm
        · cases r.2 <;> simp [h.1, h.1.symm, h.2.1, h.2.2]
        · exact b.rootEdges_valid e hm
      · exact b.rootEdges_valid e he
    down := fun z =>
      if (b.isRoot y = false ∧ b.parent y = x ∧ z = y ∧ r.2 = false) ∨
         (b.isRoot x = false ∧ b.parent x = y ∧ z = x ∧ r.2 = true) then
        r.1 :: b.down z
      else b.down z
    up := fun z =>
      if (b.isRoot y = false ∧ b.parent y = x ∧ z = y ∧ r.2 = true) ∨
         (b.isRoot x = false ∧ b.parent x = y ∧ z = x ∧ r.2 = false) then
        r.1 :: b.up z
      else b.up z
    toRoot := fun z =>
      if b.isRoot x = false ∧ b.isRoot y = true ∧ b.parent x ≠ y ∧ z = x then
        (r, y) :: b.toRoot z
      else if b.isRoot x = true ∧ b.isRoot y = false ∧ b.parent y ≠ x ∧ z = y then
        (converse r, x) :: b.toRoot z
      else b.toRoot z
    toRoot_valid := by
      intro z e he
      split at he
      · rename_i h
        rcases List.mem_cons.mp he with rfl | hm
        · exact ⟨h.2.2.2 ▸ h.1, h.2.1, h.2.2.2 ▸ h.2.2.1⟩
        · exact b.toRoot_valid z e hm
      · split at he
        · rename_i h
          rcases List.mem_cons.mp he with rfl | hm
          · exact ⟨h.2.2.2 ▸ h.2.1, h.1, h.2.2.2 ▸ h.2.2.1⟩
          · exact b.toRoot_valid z e hm
        · exact b.toRoot_valid z e he }

theorem addEdge_depth (b : BlockedForest) (r : OrientedRole) (x y z : b.Node) :
    (b.addEdge r x y).depth z = b.depth z :=
  depth_eq_of_same_shape (b₁ := b.addEdge r x y) (b₂ := b) rfl (fun _ => rfl) (fun _ _ => rfl) z

theorem addEdge_monotone {b : BlockedForest} {r : OrientedRole} {x y : b.Node} :
    (∀ z, b.down z ⊆ (b.addEdge r x y).down z) ∧
    (∀ z, b.up z ⊆ (b.addEdge r x y).up z) ∧
    (∀ z, b.loops z ⊆ (b.addEdge r x y).loops z) ∧
    (b.rootEdges ⊆ (b.addEdge r x y).rootEdges) ∧
    (∀ z, b.toRoot z ⊆ (b.addEdge r x y).toRoot z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z s hs; dsimp [addEdge]; split; exact List.mem_cons_of_mem _ hs; exact hs
  · intro z s hs; dsimp [addEdge]; split; exact List.mem_cons_of_mem _ hs; exact hs
  · intro z s hs; dsimp [addEdge]; split; exact List.mem_cons_of_mem _ hs; exact hs
  · intro e he; dsimp [addEdge]; split; exact List.mem_cons_of_mem _ he; exact he
  · intro z e he; dsimp [addEdge]
    split
    · exact List.mem_cons_of_mem _ he
    · split; exact List.mem_cons_of_mem _ he; exact he

theorem addEdge_retains {b : BlockedForest} {r s : OrientedRole} {x y u v : b.Node}
    (he : b.Edge s u v) : (b.addEdge r x y).Edge s u v := by
  have ⟨hd, hu, hl, hr, ht⟩ := addEdge_monotone (b := b) (r := r) (x := x) (y := y)
  rcases he with ⟨rfl, h⟩ | ⟨hu', hv', h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | h | h
  · exact .inl ⟨rfl, hl _ h⟩
  · refine .inr (.inl ⟨hu', hv', ?_⟩); rcases s with ⟨_, _ | _⟩ <;> exact hr h
  · refine .inr (.inr (.inl ⟨hc, ?_⟩))
    rcases s with ⟨_, _ | _⟩
    · exact hd _ h
    · exact hu _ h
  · refine .inr (.inr (.inr (.inl ⟨hc, ?_⟩)))
    rcases s with ⟨_, _ | _⟩
    · exact hu _ h
    · exact hd _ h
  · exact .inr (.inr (.inr (.inr (.inl (ht _ h)))))
  · exact .inr (.inr (.inr (.inr (.inr (ht _ h)))))

theorem addEdge_has_edge {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    (hadm : b.EdgeAdmissible x y) : (b.addEdge r x y).Edge r x y := by
  rcases hadm with rfl | ⟨hx, hy⟩ | hcy | hcx | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact .inl ⟨rfl, by simp [addEdge]⟩
  · by_cases hxy : x = y
    · subst hxy; exact .inl ⟨rfl, by simp [addEdge]⟩
    · refine .inr (.inl ⟨hx, hy, ?_⟩)
      rcases r with ⟨rn, _ | _⟩
      · change (rn, x, y) ∈ if x ≠ y ∧ b.isRoot x = true ∧ b.isRoot y = true then (rn, x, y) :: b.rootEdges else b.rootEdges
        rw [ite_eq_left ⟨hxy, hx, hy⟩]; exact List.mem_cons_self ..
      · change (rn, y, x) ∈ if x ≠ y ∧ b.isRoot x = true ∧ b.isRoot y = true then (rn, y, x) :: b.rootEdges else b.rootEdges
        rw [ite_eq_left ⟨hxy, hx, hy⟩]; exact List.mem_cons_self ..
  · refine .inr (.inr (.inl ⟨hcy, ?_⟩))
    rcases r with ⟨rn, _ | _⟩ <;> simp [Down, addEdge, hcy.1, hcy.2]
  · refine .inr (.inr (.inr (.inl ⟨hcx, ?_⟩)))
    rcases r with ⟨rn, _ | _⟩ <;> simp [Down, converse, addEdge, hcx.1, hcx.2]
  · by_cases hp : b.parent x = y
    · refine .inr (.inr (.inr (.inl ⟨⟨hx, hp⟩, ?_⟩)))
      rcases r with ⟨rn, _ | _⟩ <;> simp [Down, converse, addEdge, hx, hp]
    · refine .inr (.inr (.inr (.inr (.inl ?_))))
      change (r, y) ∈ if b.isRoot x = false ∧ b.isRoot y = true ∧ b.parent x ≠ y ∧ x = x then
        (r, y) :: b.toRoot x else _
      rw [ite_eq_left ⟨hx, hy, hp, rfl⟩]; exact List.mem_cons_self ..
  · by_cases hp : b.parent y = x
    · refine .inr (.inr (.inl ⟨⟨hy, hp⟩, ?_⟩))
      rcases r with ⟨rn, _ | _⟩ <;> simp [Down, addEdge, hy, hp]
    · refine .inr (.inr (.inr (.inr (.inr ?_))))
      have hnot : ¬ (b.isRoot x = false ∧ b.isRoot y = true ∧ b.parent x ≠ y ∧ y = x) := by
        intro h; rw [hx] at h; cases h.1
      change (converse r, x) ∈ if b.isRoot x = false ∧ b.isRoot y = true ∧ b.parent x ≠ y ∧ y = x then
        (r, y) :: b.toRoot y
        else if b.isRoot x = true ∧ b.isRoot y = false ∧ b.parent y ≠ x ∧ y = y then
        (converse r, x) :: b.toRoot y else b.toRoot y
      rw [ite_eq_right hnot, ite_eq_left ⟨hx, hy, hp, rfl⟩]; exact List.mem_cons_self ..

theorem addEdge_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {r : OrientedRole} {x y : b.Node}
    (he : holdsOriented i r (env x) (env y)) : (b.addEdge r x y).Realizes i env := by
  refine { hr with edges := fun s u v huv => ?_ }
  rcases huv with ⟨rfl, hl⟩ | ⟨hu, hv, hre⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩ | htr | htr
  · dsimp [addEdge] at hl
    split at hl
    · rename_i h
      rcases List.mem_cons.mp hl with hsr | hm
      · obtain ⟨hxy, hux⟩ := h
        rw [hux]
        have he' : holdsOriented i r (env x) (env x) := hxy ▸ he
        rcases r with ⟨rn, _ | _⟩ <;> rcases s with ⟨sn, _ | _⟩ <;>
          (dsimp at hsr; subst hsr; exact he')
      · exact hr.edges s u u (.inl ⟨rfl, hm⟩)
    · exact hr.edges s u u (.inl ⟨rfl, hl⟩)
  · have rootCase (sn : IRI) (a c : b.Node) (h : (sn, a, c) ∈ (b.addEdge r x y).rootEdges) :
        holdsOriented i (sn, false) (env a) (env c) := by
      dsimp [addEdge] at h
      split at h
      · rename_i hcond
        rcases List.mem_cons.mp h with hnew | hold
        · rcases r with ⟨rn, _ | _⟩ <;> simp at hnew
          · obtain ⟨rfl, rfl, rfl⟩ := hnew; exact he
          · obtain ⟨rfl, rfl, rfl⟩ := hnew; exact (orientation_flip i (sn, false) _ _).mp he
        · exact hr.edges (sn, false) a c (.inr (.inl ⟨(b.rootEdges_valid _ hold).1, (b.rootEdges_valid _ hold).2.1, hold⟩))
      · exact hr.edges (sn, false) a c (.inr (.inl ⟨(b.rootEdges_valid _ h).1, (b.rootEdges_valid _ h).2.1, h⟩))
    rcases s with ⟨sn, _ | _⟩
    · exact rootCase sn u v hre
    · exact (orientation_flip i (sn, false) _ _).mpr (rootCase sn v u hre)
  · have downCase (s' : OrientedRole) (a c : b.Node) (hc' : b.Child a c)
        (hd' : (b.addEdge r x y).Down s' c) : holdsOriented i s' (env a) (env c) := by
      rcases s' with ⟨sn, _ | _⟩
      · dsimp [Down, addEdge] at hd'
        split at hd'
        · rename_i hcond
          rcases List.mem_cons.mp hd' with hsr | hm
          · subst hsr
            rcases hcond with ⟨_, hpy, rfl, hr2⟩ | ⟨_, hpx, rfl, hr2⟩
            · have ha : a = x := hc'.2.symm.trans hpy
              subst ha; rcases r with ⟨rn, _ | _⟩; exact he; cases hr2
            · have ha : a = y := hc'.2.symm.trans hpx
              subst ha; rcases r with ⟨rn, _ | _⟩; cases hr2; exact (orientation_flip i (rn, false) _ _).mp he
          · exact hr.edges (sn, false) a c (.inr (.inr (.inl ⟨hc', hm⟩)))
        · exact hr.edges (sn, false) a c (.inr (.inr (.inl ⟨hc', hd'⟩)))
      · dsimp [Down, addEdge] at hd'
        split at hd'
        · rename_i hcond
          rcases List.mem_cons.mp hd' with hsr | hm
          · subst hsr
            rcases hcond with ⟨_, hpy, rfl, hr2⟩ | ⟨_, hpx, rfl, hr2⟩
            · have ha : a = x := hc'.2.symm.trans hpy
              subst ha; rcases r with ⟨rn, _ | _⟩; cases hr2; exact he
            · have ha : a = y := hc'.2.symm.trans hpx
              subst ha; rcases r with ⟨rn, _ | _⟩; exact (orientation_flip i (rn, false) _ _).mpr he; cases hr2
          · exact hr.edges (sn, true) a c (.inr (.inr (.inl ⟨hc', hm⟩)))
        · exact hr.edges (sn, true) a c (.inr (.inr (.inl ⟨hc', hd'⟩)))
    exact downCase s u v hc hd
  · have downCase (s' : OrientedRole) (a c : b.Node) (hc' : b.Child a c)
        (hd' : (b.addEdge r x y).Down s' c) : holdsOriented i s' (env a) (env c) := by
      rcases s' with ⟨sn, _ | _⟩
      · dsimp [Down, addEdge] at hd'
        split at hd'
        · rename_i hcond
          rcases List.mem_cons.mp hd' with hsr | hm
          · subst hsr
            rcases hcond with ⟨_, hpy, rfl, hr2⟩ | ⟨_, hpx, rfl, hr2⟩
            · have ha : a = x := hc'.2.symm.trans hpy
              subst ha; rcases r with ⟨rn, _ | _⟩; exact he; cases hr2
            · have ha : a = y := hc'.2.symm.trans hpx
              subst ha; rcases r with ⟨rn, _ | _⟩; cases hr2; exact (orientation_flip i (rn, false) _ _).mp he
          · exact hr.edges (sn, false) a c (.inr (.inr (.inl ⟨hc', hm⟩)))
        · exact hr.edges (sn, false) a c (.inr (.inr (.inl ⟨hc', hd'⟩)))
      · dsimp [Down, addEdge] at hd'
        split at hd'
        · rename_i hcond
          rcases List.mem_cons.mp hd' with hsr | hm
          · subst hsr
            rcases hcond with ⟨_, hpy, rfl, hr2⟩ | ⟨_, hpx, rfl, hr2⟩
            · have ha : a = x := hc'.2.symm.trans hpy
              subst ha; rcases r with ⟨rn, _ | _⟩; cases hr2; exact he
            · have ha : a = y := hc'.2.symm.trans hpx
              subst ha; rcases r with ⟨rn, _ | _⟩; exact (orientation_flip i (rn, false) _ _).mpr he; cases hr2
          · exact hr.edges (sn, true) a c (.inr (.inr (.inl ⟨hc', hm⟩)))
        · exact hr.edges (sn, true) a c (.inr (.inr (.inl ⟨hc', hd'⟩)))
    exact (orientation_flip i s _ _).mp (downCase (converse s) v u hc hd)
  · dsimp [addEdge] at htr
    split at htr
    · rename_i h; rcases List.mem_cons.mp htr with hnew | hm
      · cases hnew; rw [h.2.2.2]; exact he
      · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inl hm)))))
    · split at htr
      · rename_i h; rcases List.mem_cons.mp htr with hnew | hm
        · cases hnew; rw [h.2.2.2]; exact (orientation_flip i r _ _).mpr he
        · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inl hm)))))
      · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inl htr)))))
  · dsimp [addEdge] at htr
    split at htr
    · rename_i h; rcases List.mem_cons.mp htr with hnew | hm
      · have hsr : s = converse r := by
          have := congrArg converse (congrArg Prod.fst hnew); simpa [converse_converse] using this
        have huv : u = y := congrArg Prod.snd hnew
        rw [hsr, huv, h.2.2.2]; exact (orientation_flip i r _ _).mpr he
      · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inr hm)))))
    · split at htr
      · rename_i h; rcases List.mem_cons.mp htr with hnew | hm
        · have hsr : s = r := by
            have := congrArg converse (congrArg Prod.fst hnew); simpa [converse_converse] using this
          have huv : u = x := congrArg Prod.snd hnew
          rw [hsr, huv, h.2.2.2]; exact he
        · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inr hm)))))
      · exact hr.edges s u v (.inr (.inr (.inr (.inr (.inr htr)))))

theorem addEdge_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {r : OrientedRole} (hr : r.1 ∈ sroiqRoleNames p) (x y : b.Node) :
    (b.addEdge r x y).Within rank p := by
  refine ⟨hw.labels, hw.guards, ⟨?_, ?_, ?_⟩⟩
  · intro z
    refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · dsimp [addEdge] at hs; split at hs
      · exact (List.mem_cons.mp hs).elim (fun h => h ▸ hr) (fun h => (hw.roles.1 z).1 h)
      · exact (hw.roles.1 z).1 hs
    · dsimp [addEdge] at hs; split at hs
      · exact (List.mem_cons.mp hs).elim (fun h => h ▸ hr) (fun h => (hw.roles.1 z).2.1 h)
      · exact (hw.roles.1 z).2.1 hs
    · dsimp [addEdge] at hs; split at hs
      · exact (List.mem_cons.mp hs).elim (fun h => h ▸ hr) (fun h => (hw.roles.1 z).2.2 h)
      · exact (hw.roles.1 z).2.2 hs
  · intro e he; dsimp [addEdge] at he; split at he
    · rcases List.mem_cons.mp he with rfl | hm
      · cases r.2 <;> exact hr
      · exact hw.roles.2.1 e hm
    · exact hw.roles.2.1 e he
  · intro z e he; dsimp [addEdge] at he; split at he
    · rcases List.mem_cons.mp he with rfl | hm
      · exact hr
      · exact hw.roles.2.2 z e hm
    · split at he
      · rcases List.mem_cons.mp he with rfl | hm
        · rcases r with ⟨rn, _ | _⟩ <;> exact hr
        · exact hw.roles.2.2 z e hm
      · exact hw.roles.2.2 z e he

theorem addEdge_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) {r : OrientedRole} {x y : b.Node}
    (hxy : b.isRoot x = false → b.isRoot y = true → b.parent x ≠ y →
      b.depth x + b.nomLevel y ≤ sroiqMaxDepth rank p)
    (hyx : b.isRoot x = true → b.isRoot y = false → b.parent y ≠ x →
      b.depth y + b.nomLevel x ≤ sroiqMaxDepth rank p) :
    (b.addEdge r x y).ForestGeom rank p := by
  refine ⟨hg.nomLevel0, hg.boundNomZero, hg.boundAnonZero,
    fun z => (addEdge_depth b r x y z).symm ▸ hg.depthBound z,
    hg.nomLevelBound, fun z e he => ?_⟩
  rw [addEdge_depth b r x y z]
  dsimp [addEdge] at he
  split at he
  · rename_i h
    rcases List.mem_cons.mp he with rfl | hm
    · rw [h.2.2.2]; exact hxy h.1 h.2.1 h.2.2.1
    · exact hg.toRootBound z e hm
  · split at he
    · rename_i h
      rcases List.mem_cons.mp he with rfl | hm
      · rw [h.2.2.2]; exact hyx h.1 h.2.1 h.2.2.1
      · exact hg.toRootBound z e hm
    · exact hg.toRootBound z e he

theorem addEdge_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) (r : OrientedRole) (x y : b.Node) :
    (b.addEdge r x y).ABoxSeeded p :=
  ⟨ha.root, ha.classAssertions,
    fun rab hm r₁ r₂ h1 h2 => addEdge_retains (ha.objAssertions rab hm r₁ r₂ h1 h2),
    ha.negObjAssertions, ha.sameInds, ha.diffInds, ha.dataAssertions, ha.negDataAssertions⟩

theorem addEdge_protected {b : BlockedForest} {r : OrientedRole} {x y : b.Node}
    {z : b.Node} {s : OrientedRole} {c : Concept} {n : Nat}
    (hp : b.ProtectedWitnesses z s c n) : (b.addEdge r x y).ProtectedWitnesses z s c n := by
  obtain ⟨ys, hlen, hnd, hdist, hspec⟩ := hp
  exact ⟨ys, hlen, hnd, hdist, fun w hw =>
    ⟨(hspec w hw).1, addEdge_retains (hspec w hw).2.1, (hspec w hw).2.2⟩⟩

/-! ### Blockable witness generation (`appendChildren`) -/

def oldNode {b : BlockedForest} (n : Nat) (x : b.Node) : Fin (b.size + n + 1) :=
  ⟨x.val, by omega⟩

def newNode (b : BlockedForest) {n : Nat} (k : Fin n) : Fin (b.size + n + 1) :=
  ⟨b.size + 1 + k.val, by omega⟩

private def onExtended {b : BlockedForest} {n : Nat} {α : Type}
    (old : b.Node → α) (fresh : Fin n → α) (x : Fin (b.size + n + 1)) : α :=
  if h : x.val < b.size + 1 then old ⟨x.val, h⟩
  else fresh ⟨x.val - (b.size + 1), by have hx := x.isLt; omega⟩

theorem onExtended_old {b : BlockedForest} {n : Nat} {α : Type}
    {old : b.Node → α} {fresh : Fin n → α} (x : b.Node) :
    onExtended old fresh (oldNode n x) = old x := by
  simp [onExtended, oldNode, x.isLt]

theorem onExtended_new {b : BlockedForest} {n : Nat} {α : Type}
    {old : b.Node → α} {fresh : Fin n → α} (k : Fin n) :
    onExtended old fresh (b.newNode k) = fresh k := by
  have h : ¬ (b.size + 1 + k.val < b.size + 1) := by omega
  simp [onExtended, newNode, h]

theorem oldNode_inj {b : BlockedForest} {n : Nat} {x y : b.Node}
    (h : oldNode n x = oldNode n y) : x = y :=
  Fin.ext (by simpa [oldNode] using congrArg Fin.val h)

theorem newNode_inj {b : BlockedForest} {n : Nat} {j k : Fin n}
    (h : b.newNode j = b.newNode k) : j = k :=
  Fin.ext (by have := congrArg Fin.val h; dsimp [newNode] at this; omega)

theorem old_ne_new {b : BlockedForest} {n : Nat} (x : b.Node) (k : Fin n) :
    oldNode n x ≠ b.newNode k := by
  intro h; have := congrArg Fin.val h; dsimp [oldNode, newNode] at this; omega

theorem extended_cases {b : BlockedForest} {n : Nat} (x : Fin (b.size + n + 1)) :
    (∃ z : b.Node, x = oldNode n z) ∨ (∃ k : Fin n, x = b.newNode k) := by
  by_cases h : x.val < b.size + 1
  · exact .inl ⟨⟨x.val, h⟩, Fin.ext rfl⟩
  · exact .inr ⟨⟨x.val - (b.size + 1), by omega⟩, Fin.ext (by dsimp [newNode]; omega)⟩

private def freshPairs (b : BlockedForest) (n : Nat) :
    List (Fin (b.size + n + 1) × Fin (b.size + n + 1)) :=
  (List.finRange n).flatMap fun j =>
    (List.finRange n).filterMap fun k =>
      if j.val < k.val then some (b.newNode j, b.newNode k) else none

/-- Append `n` fresh blockable children of `x`, linked by `r` with label `c`
and pairwise recorded unequal. -/
def appendChildren (b : BlockedForest) (n : Nat) (x : b.Node) (r : OrientedRole)
    (c : Concept) : BlockedForest where
  size := b.size + n
  isRoot := onExtended b.isRoot (fun _ => false)
  root0 := by simpa [oldNode, onExtended] using b.root0
  nomLevel := onExtended b.nomLevel (fun _ => 0)
  parent := onExtended (fun u => oldNode n (b.parent u)) (fun _ => oldNode n x)
  parent_lt := by
    intro y hy
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [onExtended_old] at hy ⊢
      exact b.parent_lt z hy
    · rw [onExtended_new]
      dsimp [oldNode, newNode]; omega
  labels := onExtended b.labels (fun _ => [c])
  guardLabels := onExtended b.guardLabels (fun _ => [])
  down := onExtended b.down (fun _ => if r.2 then [] else [r.1])
  up := onExtended b.up (fun _ => if r.2 then [r.1] else [])
  loops := onExtended b.loops (fun _ => [])
  rootEdges := b.rootEdges.map fun (s, u, v) => (s, oldNode n u, oldNode n v)
  rootEdges_valid := by
    intro e he
    obtain ⟨⟨s, u, v⟩, hm, rfl⟩ := List.mem_map.mp he
    have ⟨hu, hv, hne⟩ := b.rootEdges_valid _ hm
    exact ⟨by rw [onExtended_old]; exact hu, by rw [onExtended_old]; exact hv,
      fun h => hne (oldNode_inj h)⟩
  toRoot := onExtended (fun u => (b.toRoot u).map fun (s, t) => (s, oldNode n t)) (fun _ => [])
  toRoot_valid := by
    intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he
      have ⟨hz, ht, hnp⟩ := b.toRoot_valid z _ hm
      exact ⟨by rw [onExtended_old]; exact hz, by rw [onExtended_old]; exact ht,
        by rw [onExtended_old]; exact fun h => hnp (oldNode_inj h)⟩
    · rw [onExtended_new] at he; cases he
  noms := b.noms.map fun (a, u) => (a, oldNode n u)
  noms_valid := by
    intro q hq
    obtain ⟨⟨a, u⟩, hm, rfl⟩ := List.mem_map.mp hq
    rw [onExtended_old]; exact b.noms_valid _ hm
  anons := b.anons.map fun (k, u) => (k, oldNode n u)
  anons_valid := by
    intro q hq
    obtain ⟨⟨k, u⟩, hm, rfl⟩ := List.mem_map.mp hq
    rw [onExtended_old]; exact b.anons_valid _ hm
  unequal := b.unequal.map (fun (u, v) => (oldNode n u, oldNode n v)) ++ freshPairs b n
  nnBounds := b.nnBounds.map fun (u, s, d, ts) => (oldNode n u, s, d, ts.map (oldNode n))
  nnBounds_valid := by
    intro e he
    obtain ⟨⟨u, s, d, ts⟩, hm, rfl⟩ := List.mem_map.mp he
    have ⟨hu, hts⟩ := b.nnBounds_valid _ hm
    refine ⟨by rw [onExtended_old]; exact hu, fun o ho => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
    simpa only [onExtended_old] using hts t ht
  blockedBy _ := none
  keyDisjoint := b.keyDisjoint.map fun (r₁, r₂, dp) => (oldNode n r₁, oldNode n r₂, dp)
  keyDisjoint_valid := by
    intro e he
    obtain ⟨⟨r₁, r₂, dp⟩, hm, rfl⟩ := List.mem_map.mp he
    have ⟨hr₁, hr₂⟩ := b.keyDisjoint_valid _ hm
    exact ⟨by rw [onExtended_old]; exact hr₁, by rw [onExtended_old]; exact hr₂⟩

theorem appendChildren_child_old {b : BlockedForest} {n : Nat} {x u v : b.Node}
    {r : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Child (oldNode n u) (oldNode n v) ↔ b.Child u v := by
  simp only [Child, appendChildren, onExtended_old]
  exact and_congr Iff.rfl ⟨oldNode_inj, congrArg (oldNode n)⟩

theorem appendChildren_child_new {b : BlockedForest} {n : Nat} {x u : b.Node} {k : Fin n}
    {r : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Child (oldNode n u) (b.newNode k) ↔ u = x := by
  simp only [Child, appendChildren, onExtended_new, true_and]
  exact ⟨fun h => (oldNode_inj h).symm, fun h => h ▸ rfl⟩

private theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (heq : l[i]'hi = l[j]'hj) : i = j := by
  have hp := List.pairwise_iff_getElem.mp h
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · exact (hp i j hi hj hlt heq).elim
  · rfl
  · exact (hp j i hj hi hgt heq.symm).elim

private theorem pairwise_lt_finRange (n : Nat) :
    (List.finRange n).Pairwise (fun j k : Fin n => j.val < k.val) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hlt
  simp [hlt]

theorem appendChildren_depth_old {b : BlockedForest} {n : Nat} {x : b.Node}
    {r : OrientedRole} {c : Concept} (z : b.Node) :
    (b.appendChildren n x r c).depth (oldNode n z) = b.depth z := by
  by_cases hr : b.isRoot z = true
  · have hr' : (b.appendChildren n x r c).isRoot (oldNode n z) = true := by
      simpa [appendChildren, onExtended_old] using hr
    rw [depth_root hr', depth_root hr]
  · have hnr : b.isRoot z = false := Bool.eq_false_iff.mpr hr
    have hc : b.Child (b.parent z) z := ⟨hnr, rfl⟩
    have hc' : (b.appendChildren n x r c).Child (oldNode n (b.parent z)) (oldNode n z) :=
      appendChildren_child_old.mpr hc
    rw [depth_child hc, depth_child hc', appendChildren_depth_old (b.parent z)]
termination_by z.val
decreasing_by exact b.parent_lt z (Bool.eq_false_iff.mpr hr)

theorem appendChildren_depth_new {b : BlockedForest} {n : Nat} {x : b.Node}
    {r : OrientedRole} {c : Concept} (k : Fin n) :
    (b.appendChildren n x r c).depth (b.newNode k) = b.depth x + 1 := by
  have hc : (b.appendChildren n x r c).Child (oldNode n x) (b.newNode k) :=
    appendChildren_child_new.mpr rfl
  rw [depth_child hc, appendChildren_depth_old x]

theorem appendChildren_edge_old {b : BlockedForest} {n : Nat} {x u v : b.Node}
    {r s : OrientedRole} {c : Concept} (he : b.Edge s u v) :
    (b.appendChildren n x r c).Edge s (oldNode n u) (oldNode n v) := by
  rcases he with ⟨rfl, h⟩ | ⟨hu, hv, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | h | h
  · exact .inl ⟨rfl, by simpa [appendChildren, onExtended_old] using h⟩
  · refine .inr (.inl ⟨by simpa [appendChildren, onExtended_old] using hu,
      by simpa [appendChildren, onExtended_old] using hv, ?_⟩)
    rcases s with ⟨s, _ | _⟩ <;> exact List.mem_map.mpr ⟨_, h, rfl⟩
  · refine .inr (.inr (.inl ⟨appendChildren_child_old.mpr hc, ?_⟩))
    rcases s with ⟨s, _ | _⟩ <;> simpa [Down, appendChildren, onExtended_old] using h
  · refine .inr (.inr (.inr (.inl ⟨appendChildren_child_old.mpr hc, ?_⟩)))
    rcases s with ⟨s, _ | _⟩ <;> simpa [Down, converse, appendChildren, onExtended_old] using h
  · refine .inr (.inr (.inr (.inr (.inl ?_))))
    simp only [appendChildren, onExtended_old]
    exact List.mem_map.mpr ⟨(s, v), h, rfl⟩
  · refine .inr (.inr (.inr (.inr (.inr ?_))))
    simp only [appendChildren, onExtended_old]
    exact List.mem_map.mpr ⟨(converse s, u), h, rfl⟩

theorem appendChildren_edge_new {b : BlockedForest} {n : Nat} {x : b.Node} {k : Fin n}
    {r : OrientedRole} {c : Concept} :
    (b.appendChildren n x r c).Edge r (oldNode n x) (b.newNode k) := by
  apply (edge_child_iff (appendChildren_child_new.mpr rfl)).mpr
  rcases r with ⟨r, _ | _⟩ <;> simp [Down, appendChildren, onExtended_new]

theorem appendChildren_protected_new (b : BlockedForest) (n : Nat) (x : b.Node)
    (r : OrientedRole) (c : Concept) :
    (b.appendChildren n x r c).ProtectedWitnesses (oldNode n x) r c n := by
  refine ⟨(List.finRange n).map b.newNode, ?_, ?_, ?_, ?_⟩
  · exact (List.length_map _).trans (List.length_finRange)
  · exact List.pairwise_map.mpr
      ((List.nodup_finRange n).imp fun hne heq => hne (newNode_inj heq))
  · refine List.pairwise_map.mpr ((pairwise_lt_finRange n).imp fun {j k} hlt => ?_)
    refine .inl (List.mem_append_right _ ?_)
    unfold freshPairs
    exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      List.mem_filterMap.mpr ⟨k, List.mem_finRange k, by simp [hlt]; rfl⟩⟩
  · intro y hy
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
    refine ⟨fun _ => .inr (appendChildren_child_new.mpr rfl), appendChildren_edge_new, ?_⟩
    simp [appendChildren, onExtended_new]

theorem appendChildren_protected_old {b : BlockedForest} {n : Nat} {x z : b.Node}
    {r s : OrientedRole} {c d : Concept} {m : Nat}
    (hp : b.ProtectedWitnesses z s d m) :
    (b.appendChildren n x r c).ProtectedWitnesses (oldNode n z) s d m := by
  obtain ⟨ys, hlen, hnd, hdist, hspec⟩ := hp
  refine ⟨ys.map (oldNode n), ?_, ?_, ?_, ?_⟩
  · exact (List.length_map _).trans hlen
  · exact List.pairwise_map.mpr (hnd.imp fun hne heq => hne (oldNode_inj heq))
  · refine List.pairwise_map.mpr (hdist.imp fun hd => ?_)
    rcases hd with h | h
    · exact .inl (List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩))
    · exact .inr (List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩))
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    have ⟨hroot, hedge, hlab⟩ := hspec w hw
    refine ⟨fun hr => ?_, appendChildren_edge_old hedge, by simpa [appendChildren, onExtended_old] using hlab⟩
    simp only [appendChildren, onExtended_old] at hr
    rcases hroot hr with hrw | hcw
    · exact .inl (by simpa [appendChildren, onExtended_old] using hrw)
    · exact .inr (appendChildren_child_old.mpr hcw)

theorem appendChildren_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {n : Nat} {x : b.Node}
    {r : OrientedRole} {c : Concept}
    (hw : AtLeast n (fun w => holdsOriented i r (env x) w ∧ holds i w c)) :
    ∃ env', (b.appendChildren n x r c).Realizes i env' := by
  obtain ⟨ws, hlen, hnd, hspec⟩ := hw
  let fresh (k : Fin n) : i.Object := ws[k.val]'(hlen ▸ k.isLt)
  let env' := onExtended env fresh
  refine ⟨env', ?_⟩
  constructor
  case labels =>
    intro y d hd
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, env', onExtended_old] at hd ⊢; exact hr.labels z d hd
    · simp only [appendChildren, env', onExtended_new] at hd ⊢
      obtain rfl := List.mem_singleton.mp hd
      exact (hspec _ (List.getElem_mem _)).2
  case edges =>
    intro s u v huv
    rcases huv with ⟨rfl, hl⟩ | ⟨hu, hv, hre⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩ | htr | htr
    · rcases extended_cases (b := b) u with ⟨z, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendChildren, env', onExtended_old] at hl ⊢; exact hr.edges s z z (.inl ⟨rfl, hl⟩)
      · simp only [appendChildren, onExtended_new] at hl; cases hl
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · simp only [env', onExtended_old]
          rcases s with ⟨sn, _ | _⟩
          · obtain ⟨⟨s', a, d⟩, hm, heq⟩ := List.mem_map.mp hre
            obtain ⟨h1, ha, hd⟩ : s' = sn ∧ oldNode n a = oldNode n zu ∧ oldNode n d = oldNode n zv :=
              ⟨congrArg Prod.fst heq, congrArg (fun q => q.2.1) heq, congrArg (fun q => q.2.2) heq⟩
            rw [← h1, ← oldNode_inj ha, ← oldNode_inj hd]
            exact hr.edges (s', false) a d (.inr (.inl ⟨(b.rootEdges_valid _ hm).1, (b.rootEdges_valid _ hm).2.1, hm⟩))
          · obtain ⟨⟨s', a, d⟩, hm, heq⟩ := List.mem_map.mp hre
            obtain ⟨h1, ha, hd⟩ : s' = sn ∧ oldNode n a = oldNode n zv ∧ oldNode n d = oldNode n zu :=
              ⟨congrArg Prod.fst heq, congrArg (fun q => q.2.1) heq, congrArg (fun q => q.2.2) heq⟩
            rw [← h1, ← oldNode_inj ha, ← oldNode_inj hd]
            exact hr.edges (s', true) d a (.inr (.inl ⟨(b.rootEdges_valid _ hm).2.1, (b.rootEdges_valid _ hm).1, hm⟩))
        · simp only [appendChildren, onExtended_new] at hv; cases hv
      · simp only [appendChildren, onExtended_new] at hu; cases hu
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · simp only [env', onExtended_old]
          have hco := appendChildren_child_old.mp hc
          have hdo : b.Down s zv := by rcases s with ⟨s, _ | _⟩ <;> simpa [Down, appendChildren, onExtended_old] using hd
          exact hr.edges s zu zv (.inr (.inr (.inl ⟨hco, hdo⟩)))
        · obtain rfl := appendChildren_child_new.mp hc
          simp only [env', onExtended_old, onExtended_new]
          have hsr : s = r := by
            rcases s with ⟨sn, _ | _⟩ <;> rcases r with ⟨rn, _ | _⟩ <;>
              simp [Down, appendChildren, onExtended_new] at hd <;> subst hd <;> rfl
          subst hsr
          exact (hspec _ (List.getElem_mem _)).1
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · have := hc.2; simp only [appendChildren, onExtended_old] at this
          exact (old_ne_new _ _ this).elim
        · have := hc.2; simp only [appendChildren, onExtended_new] at this
          exact (old_ne_new _ _ this).elim
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · simp only [env', onExtended_old]
          have hco := appendChildren_child_old.mp hc
          have hdo : b.Down (converse s) zu := by
            rcases s with ⟨s, _ | _⟩ <;> simpa [Down, converse, appendChildren, onExtended_old] using hd
          exact hr.edges s zu zv (.inr (.inr (.inr (.inl ⟨hco, hdo⟩))))
        · have := hc.2; simp only [appendChildren, onExtended_old] at this
          exact (old_ne_new _ _ this).elim
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · obtain rfl := appendChildren_child_new.mp hc
          simp only [env', onExtended_old, onExtended_new]
          have hsr : converse s = r := by
            rcases s with ⟨sn, _ | _⟩ <;> rcases r with ⟨rn, _ | _⟩ <;>
              simp [Down, converse, appendChildren, onExtended_new] at hd <;> subst hd <;> rfl
          rw [← converse_converse s, hsr]
          exact (orientation_flip i r _ _).mpr (hspec _ (List.getElem_mem _)).1
        · have := hc.2; simp only [appendChildren, onExtended_new] at this
          exact (old_ne_new _ _ this).elim
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendChildren, onExtended_old] at htr
        obtain ⟨⟨s', t⟩, hm, heq⟩ := List.mem_map.mp htr
        cases heq
        simp only [env', onExtended_old]
        exact hr.edges s' zu t (.inr (.inr (.inr (.inr (.inl hm)))))
      · simp only [appendChildren, onExtended_new] at htr; cases htr
    · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendChildren, onExtended_old] at htr
        obtain ⟨⟨s', t⟩, hm, heq⟩ := List.mem_map.mp htr
        have h1 : s' = converse s := congrArg Prod.fst heq
        have h2 : oldNode n t = u := congrArg Prod.snd heq
        subst h2
        simp only [env', onExtended_old]
        exact hr.edges s t zv (.inr (.inr (.inr (.inr (.inr (h1 ▸ hm))))))
      · simp only [appendChildren, onExtended_new] at htr; cases htr
  case guards =>
    intro y g hg
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, env', onExtended_old] at hg ⊢; exact hr.guards z g hg
    · simp only [appendChildren, onExtended_new] at hg; cases hg
  case unequal =>
    intro u v huv
    rcases List.mem_append.mp huv with hold | hnew
    · obtain ⟨⟨a, d⟩, hm, heq⟩ := List.mem_map.mp hold
      cases heq
      simp only [env', onExtended_old]; exact hr.unequal a d hm
    · obtain ⟨j, _, hk⟩ := List.mem_flatMap.mp hnew
      obtain ⟨k, _, hres⟩ := List.mem_filterMap.mp hk
      split at hres
      · rename_i hlt; cases hres
        simp only [env', onExtended_new, fresh]
        intro heq
        exact (Nat.ne_of_lt hlt) (nodup_getElem_inj hnd (hlen ▸ j.isLt) (hlen ▸ k.isLt) heq)
      · cases hres
  case noms =>
    intro a y hy
    obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simp only [env', onExtended_old]; exact hr.noms a u hm
  case anons =>
    intro k y hy
    obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simp only [env', onExtended_old]; exact hr.anons k u hm
  case nnBounds =>
    intro e he z hz hzc
    obtain ⟨⟨u, s, d, ts⟩, hm, rfl⟩ := List.mem_map.mp he
    simp only [env', onExtended_old] at hz
    obtain ⟨o, ho, rfl⟩ := hr.nnBounds (u, s, d, ts) hm z hz hzc
    exact ⟨oldNode n o, List.mem_map.mpr ⟨o, ho, rfl⟩, by simp [env', onExtended_old]⟩
  case keyDisjoint =>
    intro e he y
    obtain ⟨⟨r₁, r₂, dp⟩, hm, rfl⟩ := List.mem_map.mp he
    simp only [env', onExtended_old]
    exact hr.keyDisjoint (r₁, r₂, dp) hm y

theorem appendChildren_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {n : Nat} {x : b.Node} {r : OrientedRole} {c : Concept}
    (hr : r.1 ∈ sroiqRoleNames p) (hc : c ∈ sroiqClos p) :
    (b.appendChildren n x r c).Within rank p := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · intro y d hd
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, onExtended_old] at hd; exact hw.labels z hd
    · simp only [appendChildren, onExtended_new] at hd
      obtain rfl := List.mem_singleton.mp hd; exact hc
  · intro y g hg
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, onExtended_old] at hg; exact hw.guards z hg
    · simp only [appendChildren, onExtended_new] at hg; cases hg
  · intro y
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simpa [appendChildren, onExtended_old] using hw.roles.1 z
    · refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
      · simp only [appendChildren, onExtended_new] at hs
        rcases r with ⟨rn, _ | _⟩ <;> simp at hs; exact hs ▸ hr
      · simp only [appendChildren, onExtended_new] at hs
        rcases r with ⟨rn, _ | _⟩ <;> simp at hs; exact hs ▸ hr
      · simp only [appendChildren, onExtended_new] at hs; cases hs
  · intro e he
    obtain ⟨⟨s, u, v⟩, hm, rfl⟩ := List.mem_map.mp he
    exact hw.roles.2.1 _ hm
  · intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he
      exact hw.roles.2.2 z _ hm
    · simp only [appendChildren, onExtended_new] at he; cases he

theorem appendChildren_bindings {b : BlockedForest} {p : Problem}
    (hb : b.BindingsValid p) (n : Nat) (x : b.Node) (r : OrientedRole) (c : Concept) :
    (b.appendChildren n x r c).BindingsValid p := by
  constructor
  · intro a ha; obtain ⟨u, hu⟩ := hb.nomComplete a ha
    exact ⟨oldNode n u, List.mem_map.mpr ⟨(a, u), hu, rfl⟩⟩
  · intro k hk; obtain ⟨u, hu⟩ := hb.anonComplete k hk
    exact ⟨oldNode n u, List.mem_map.mpr ⟨(k, u), hu, rfl⟩⟩
  · intro a r₁ r₂ h1 h2
    obtain ⟨⟨a1, u1⟩, hu1, heq1⟩ := List.mem_map.mp h1
    obtain ⟨⟨a2, u2⟩, hu2, heq2⟩ := List.mem_map.mp h2
    cases heq1; cases heq2
    exact congrArg (oldNode n) (hb.nomFunctional _ u1 u2 hu1 hu2)
  · intro k r₁ r₂ h1 h2
    obtain ⟨⟨k1, u1⟩, hu1, heq1⟩ := List.mem_map.mp h1
    obtain ⟨⟨k2, u2⟩, hu2, heq2⟩ := List.mem_map.mp h2
    cases heq1; cases heq2
    exact congrArg (oldNode n) (hb.anonFunctional _ u1 u2 hu1 hu2)

theorem appendChildren_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) {n : Nat} {x : b.Node}
    (hx : b.depth x ≤ sroiqMaxDepth rank p) (r : OrientedRole) (c : Concept) :
    (b.appendChildren n x r c).ForestGeom rank p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [appendChildren, oldNode, onExtended] using hg.nomLevel0
  · intro a y hy
    obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simpa [appendChildren, onExtended_old] using hg.boundNomZero a u hm
  · intro k y hy
    obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simpa [appendChildren, onExtended_old] using hg.boundAnonZero k u hm
  · intro y
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [appendChildren_depth_old]; exact hg.depthBound z
    · rw [appendChildren_depth_new]; omega
  · intro y hy
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, onExtended_old] at hy ⊢; exact hg.nomLevelBound z hy
    · simp only [appendChildren, onExtended_new] at hy; cases hy
  · intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendChildren, onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he
      rw [appendChildren_depth_old]; simpa [appendChildren, onExtended_old] using hg.toRootBound z _ hm
    · simp only [appendChildren, onExtended_new] at he; cases he

theorem appendChildren_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) (n : Nat) (x : b.Node) (r : OrientedRole) (c : Concept) :
    (b.appendChildren n x r c).ABoxSeeded p := by
  have boundOld (ind : Individual) (y : (b.appendChildren n x r c).Node)
      (h : (b.appendChildren n x r c).BoundTo ind y) :
      ∃ u, y = oldNode n u ∧ b.BoundTo ind u := by
    cases ind with
    | named a =>
      obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp h
      cases heq; exact ⟨u, rfl, hm⟩
    | anonymous d l =>
      obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp h
      cases heq; exact ⟨u, rfl, hm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [appendChildren, oldNode, onExtended] using ha.root
  · intro ac hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ac.1 y hy
    simpa [appendChildren, onExtended_old] using ha.classAssertions ac hm u hu
  · intro rab hm y₁ y₂ h1 h2
    obtain ⟨u₁, rfl, hu1⟩ := boundOld rab.2.1 y₁ h1
    obtain ⟨u₂, rfl, hu2⟩ := boundOld rab.2.2 y₂ h2
    exact appendChildren_edge_old (ha.objAssertions rab hm u₁ u₂ hu1 hu2)
  · intro rab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld rab.2.1 y hy
    simpa [appendChildren, onExtended_old] using ha.negObjAssertions rab hm u hu
  · intro ab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ab.1 y hy
    simpa [appendChildren, onExtended_old] using ha.sameInds ab hm u hu
  · intro ab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ab.1 y hy
    simpa [appendChildren, onExtended_old] using ha.diffInds ab hm u hu
  · intro dal hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld dal.2.1 y hy
    simpa [appendChildren, onExtended_old] using ha.dataAssertions dal hm u hu
  · intro dal hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld dal.2.1 y hy
    simpa [appendChildren, onExtended_old] using ha.negDataAssertions dal hm u hu

/-! ### NN-rule root generation (`appendNNRoots`) -/

/-- Append `m` fresh root nodes at nominal level `b.nomLevel r + 1` as
exact NN-rule witnesses for `.max n rel c` at root `r`, linked by `rootEdges`
from `r`, labeled `c`, pairwise unequal, and recorded in `nnBounds`. -/
def appendNNRoots (b : BlockedForest) (m : Nat) (r : b.Node) (hr : b.isRoot r = true)
    (rel : OrientedRole) (c : Concept) : BlockedForest where
  size := b.size + m
  isRoot := onExtended b.isRoot (fun _ => true)
  root0 := by simpa [oldNode, onExtended] using b.root0
  nomLevel := onExtended b.nomLevel (fun _ => b.nomLevel r + 1)
  parent := onExtended (fun u => oldNode m (b.parent u)) (fun _ => 0)
  parent_lt := by
    intro y hy
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [onExtended_old] at hy ⊢; exact b.parent_lt z hy
    · rw [onExtended_new] at hy; cases hy
  labels := onExtended b.labels (fun _ => [c])
  guardLabels := onExtended b.guardLabels (fun _ => [])
  down := onExtended b.down (fun _ => [])
  up := onExtended b.up (fun _ => [])
  loops := onExtended b.loops (fun _ => [])
  rootEdges :=
    (b.rootEdges.map fun (s, u, v) => (s, oldNode m u, oldNode m v)) ++
    (List.finRange m).map fun k =>
      if rel.2 then (rel.1, b.newNode k, oldNode m r) else (rel.1, oldNode m r, b.newNode k)
  rootEdges_valid := by
    intro e he
    rcases List.mem_append.mp he with hold | hnew
    · obtain ⟨⟨s, u, v⟩, hm, rfl⟩ := List.mem_map.mp hold
      have ⟨hu, hv, hne⟩ := b.rootEdges_valid _ hm
      exact ⟨by rw [onExtended_old]; exact hu, by rw [onExtended_old]; exact hv,
        fun h => hne (oldNode_inj h)⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hnew
      cases rel.2 <;> simp [onExtended_old, onExtended_new, hr, old_ne_new, Ne.symm (old_ne_new r k)]
  toRoot := onExtended (fun u => (b.toRoot u).map fun (s, t) => (s, oldNode m t)) (fun _ => [])
  toRoot_valid := by
    intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he
      have ⟨hz, ht, hnp⟩ := b.toRoot_valid z _ hm
      exact ⟨by rw [onExtended_old]; exact hz, by rw [onExtended_old]; exact ht,
        by rw [onExtended_old]; exact fun h => hnp (oldNode_inj h)⟩
    · rw [onExtended_new] at he; cases he
  noms := b.noms.map fun (a, u) => (a, oldNode m u)
  noms_valid := by
    intro q hq
    obtain ⟨⟨a, u⟩, hm, rfl⟩ := List.mem_map.mp hq
    rw [onExtended_old]; exact b.noms_valid _ hm
  anons := b.anons.map fun (k, u) => (k, oldNode m u)
  anons_valid := by
    intro q hq
    obtain ⟨⟨k, u⟩, hm, rfl⟩ := List.mem_map.mp hq
    rw [onExtended_old]; exact b.anons_valid _ hm
  unequal := b.unequal.map (fun (u, v) => (oldNode m u, oldNode m v)) ++ freshPairs b m
  nnBounds :=
    (oldNode m r, rel, c, (List.finRange m).map b.newNode) ::
    b.nnBounds.map fun (u, s, d, ts) => (oldNode m u, s, d, ts.map (oldNode m))
  nnBounds_valid := by
    intro e he
    rcases List.mem_cons.mp he with rfl | hold
    · refine ⟨by rw [onExtended_old]; exact hr, fun o ho => ?_⟩
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ho
      simp [onExtended_old, onExtended_new]
    · obtain ⟨⟨u, s, d, ts⟩, hm, rfl⟩ := List.mem_map.mp hold
      have ⟨hu, hts⟩ := b.nnBounds_valid _ hm
      refine ⟨by rw [onExtended_old]; exact hu, fun o ho => ?_⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
      simpa only [onExtended_old] using hts t ht
  blockedBy _ := none
  keyDisjoint := b.keyDisjoint.map fun (r₁, r₂, dp) => (oldNode m r₁, oldNode m r₂, dp)
  keyDisjoint_valid := by
    intro e he
    obtain ⟨⟨r₁, r₂, dp⟩, hm, rfl⟩ := List.mem_map.mp he
    have ⟨hr₁, hr₂⟩ := b.keyDisjoint_valid _ hm
    exact ⟨by rw [onExtended_old]; exact hr₁, by rw [onExtended_old]; exact hr₂⟩

theorem appendNNRoots_depth_old {b : BlockedForest} {m : Nat} {r : b.Node}
    {hr : b.isRoot r = true} {rel : OrientedRole} {c : Concept} (z : b.Node) :
    (b.appendNNRoots m r hr rel c).depth (oldNode m z) = b.depth z := by
  by_cases hrz : b.isRoot z = true
  · have hr' : (b.appendNNRoots m r hr rel c).isRoot (oldNode m z) = true := by
      simpa [appendNNRoots, onExtended_old] using hrz
    rw [depth_root hr', depth_root hrz]
  · have hnr : b.isRoot z = false := Bool.eq_false_iff.mpr hrz
    have hc : b.Child (b.parent z) z := ⟨hnr, rfl⟩
    have hc' : (b.appendNNRoots m r hr rel c).Child (oldNode m (b.parent z)) (oldNode m z) :=
      ⟨by simpa [appendNNRoots, onExtended_old] using hnr,
       by simp [appendNNRoots, onExtended_old]⟩
    rw [depth_child hc, depth_child hc', appendNNRoots_depth_old (b.parent z)]
termination_by z.val
decreasing_by exact b.parent_lt z (Bool.eq_false_iff.mpr hrz)

theorem appendNNRoots_depth_new {b : BlockedForest} {m : Nat} {r : b.Node}
    {hr : b.isRoot r = true} {rel : OrientedRole} {c : Concept} (k : Fin m) :
    (b.appendNNRoots m r hr rel c).depth (b.newNode k) = 0 :=
  depth_root (by simp [appendNNRoots, onExtended_new])

theorem appendNNRoots_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hreal : b.Realizes i env) {m : Nat} {r : b.Node}
    (hr : b.isRoot r = true) {rel : OrientedRole} {c : Concept}
    {ws : List i.Object} (hlen : ws.length = m) (hnd : ws.Nodup)
    (hspec : ∀ w ∈ ws, holdsOriented i rel (env r) w ∧ holds i w c)
    (hmax : ∀ z : i.Object, holdsOriented i rel (env r) z → holds i z c → z ∈ ws) :
    ∃ env', (b.appendNNRoots m r hr rel c).Realizes i env' := by
  let fresh (k : Fin m) : i.Object := ws[k.val]'(hlen ▸ k.isLt)
  let env' := onExtended env fresh
  refine ⟨env', ?_⟩
  constructor
  case labels =>
    intro y d hd
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, env', onExtended_old] at hd ⊢; exact hreal.labels z d hd
    · simp only [appendNNRoots, env', onExtended_new] at hd ⊢
      obtain rfl := List.mem_singleton.mp hd
      exact (hspec _ (List.getElem_mem _)).2
  case edges =>
    intro s u v huv
    rcases huv with ⟨rfl, hl⟩ | ⟨hu, hv, hre⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩ | htr | htr
    · rcases extended_cases (b := b) u with ⟨z, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendNNRoots, env', onExtended_old] at hl ⊢; exact hreal.edges s z z (.inl ⟨rfl, hl⟩)
      · simp only [appendNNRoots, onExtended_new] at hl; cases hl
    · rcases s with ⟨sn, _ | _⟩
      · rcases List.mem_append.mp hre with hold | hnew
        · obtain ⟨⟨s', a, d⟩, hm, heq⟩ := List.mem_map.mp hold
          cases heq
          simp only [env', onExtended_old]
          exact hreal.edges (sn, false) a d (.inr (.inl ⟨(b.rootEdges_valid _ hm).1, (b.rootEdges_valid _ hm).2.1, hm⟩))
        · obtain ⟨k, _, heq⟩ := List.mem_map.mp hnew
          rcases rel with ⟨rn, _ | _⟩ <;> simp at heq
          · obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [env', onExtended_old, onExtended_new]
            exact (hspec _ (List.getElem_mem _)).1
          · obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [env', onExtended_old, onExtended_new]
            exact (orientation_flip i (sn, false) _ _).mp (hspec _ (List.getElem_mem _)).1
      · rcases List.mem_append.mp hre with hold | hnew
        · obtain ⟨⟨s', a, d⟩, hm, heq⟩ := List.mem_map.mp hold
          cases heq
          simp only [env', onExtended_old]
          exact hreal.edges (sn, true) d a (.inr (.inl ⟨(b.rootEdges_valid _ hm).2.1, (b.rootEdges_valid _ hm).1, hm⟩))
        · obtain ⟨k, _, heq⟩ := List.mem_map.mp hnew
          rcases rel with ⟨rn, _ | _⟩ <;> simp at heq
          · obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [env', onExtended_old, onExtended_new]
            exact (orientation_flip i (sn, false) _ _).mpr (hspec _ (List.getElem_mem _)).1
          · obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [env', onExtended_old, onExtended_new]
            exact (hspec _ (List.getElem_mem _)).1
    · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k, rfl⟩
      · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k', rfl⟩
        · simp only [env', onExtended_old]
          have hco : b.Child zu zv := ⟨by simpa [appendNNRoots, onExtended_old] using hc.1,
            oldNode_inj (by simpa [appendNNRoots, onExtended_old] using hc.2)⟩
          have hdo : b.Down s zv := by rcases s with ⟨s, _ | _⟩ <;> simpa [Down, appendNNRoots, onExtended_old] using hd
          exact hreal.edges s zu zv (.inr (.inr (.inl ⟨hco, hdo⟩)))
        · have := hc.2; simp only [appendNNRoots, onExtended_old] at this
          exact (old_ne_new _ _ this).elim
      · have := hc.1; simp [appendNNRoots, onExtended_new] at this
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k', rfl⟩
        · simp only [env', onExtended_old]
          have hco : b.Child zv zu := ⟨by simpa [appendNNRoots, onExtended_old] using hc.1,
            oldNode_inj (by simpa [appendNNRoots, onExtended_old] using hc.2)⟩
          have hdo : b.Down (converse s) zu := by
            rcases s with ⟨s, _ | _⟩ <;> simpa [Down, converse, appendNNRoots, onExtended_old] using hd
          exact hreal.edges s zu zv (.inr (.inr (.inr (.inl ⟨hco, hdo⟩))))
        · have := hc.2; simp only [appendNNRoots, onExtended_old] at this
          exact (old_ne_new _ _ this).elim
      · have := hc.1; simp [appendNNRoots, onExtended_new] at this
    · rcases extended_cases (b := b) u with ⟨zu, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendNNRoots, onExtended_old] at htr
        obtain ⟨⟨s', t⟩, hm, heq⟩ := List.mem_map.mp htr
        cases heq
        simp only [env', onExtended_old]
        exact hreal.edges s' zu t (.inr (.inr (.inr (.inr (.inl hm)))))
      · simp only [appendNNRoots, onExtended_new] at htr; cases htr
    · rcases extended_cases (b := b) v with ⟨zv, rfl⟩ | ⟨k, rfl⟩
      · simp only [appendNNRoots, onExtended_old] at htr
        obtain ⟨⟨s', t⟩, hm, heq⟩ := List.mem_map.mp htr
        have h1 : s' = converse s := congrArg Prod.fst heq
        have h2 : oldNode m t = u := congrArg Prod.snd heq
        subst h2
        simp only [env', onExtended_old]
        exact hreal.edges s t zv (.inr (.inr (.inr (.inr (.inr (h1 ▸ hm))))))
      · simp only [appendNNRoots, onExtended_new] at htr; cases htr
  case guards =>
    intro y g hg
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, env', onExtended_old] at hg ⊢; exact hreal.guards z g hg
    · simp only [appendNNRoots, onExtended_new] at hg; cases hg
  case unequal =>
    intro u v huv
    rcases List.mem_append.mp huv with hold | hnew
    · obtain ⟨⟨a, d⟩, hm, heq⟩ := List.mem_map.mp hold
      cases heq
      simp only [env', onExtended_old]; exact hreal.unequal a d hm
    · obtain ⟨j, _, hk⟩ := List.mem_flatMap.mp hnew
      obtain ⟨k, _, hres⟩ := List.mem_filterMap.mp hk
      split at hres
      · rename_i hlt; cases hres
        simp only [env', onExtended_new, fresh]
        intro heq
        exact (Nat.ne_of_lt hlt) (nodup_getElem_inj hnd (hlen ▸ j.isLt) (hlen ▸ k.isLt) heq)
      · cases hres
  case noms =>
    intro a y hy
    obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simp only [env', onExtended_old]; exact hreal.noms a u hm
  case anons =>
    intro k y hy
    obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simp only [env', onExtended_old]; exact hreal.anons k u hm
  case nnBounds =>
    intro e he z hz hzc
    rcases List.mem_cons.mp he with rfl | hold
    · simp only [env', onExtended_old] at hz
      have hzm : z ∈ ws := hmax z hz hzc
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hzm
      exact ⟨b.newNode ⟨idx, hlen ▸ hidx⟩, List.mem_map.mpr ⟨⟨idx, hlen ▸ hidx⟩, List.mem_finRange _, rfl⟩,
        by simp [env', onExtended_new, fresh]⟩
    · obtain ⟨⟨u, s, d, ts⟩, hm, rfl⟩ := List.mem_map.mp hold
      simp only [env', onExtended_old] at hz
      obtain ⟨o, ho, rfl⟩ := hreal.nnBounds (u, s, d, ts) hm z hz hzc
      exact ⟨oldNode m o, List.mem_map.mpr ⟨o, ho, rfl⟩, by simp [env', onExtended_old]⟩
  case keyDisjoint =>
    intro e he y
    obtain ⟨⟨r₁, r₂, dp⟩, hm, rfl⟩ := List.mem_map.mp he
    simp only [env', onExtended_old]
    exact hreal.keyDisjoint (r₁, r₂, dp) hm y

theorem appendNNRoots_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {m : Nat} {r : b.Node} (hr : b.isRoot r = true)
    {rel : OrientedRole} {c : Concept}
    (hrel : rel.1 ∈ sroiqRoleNames p) (hc : c ∈ sroiqClos p) :
    (b.appendNNRoots m r hr rel c).Within rank p := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · intro y d hd
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, onExtended_old] at hd; exact hw.labels z hd
    · simp only [appendNNRoots, onExtended_new] at hd
      obtain rfl := List.mem_singleton.mp hd; exact hc
  · intro y g hg
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, onExtended_old] at hg; exact hw.guards z hg
    · simp only [appendNNRoots, onExtended_new] at hg; cases hg
  · intro y
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simpa [appendNNRoots, onExtended_old] using hw.roles.1 z
    · exact ⟨fun _ h => by simp [appendNNRoots, onExtended_new] at h,
        fun _ h => by simp [appendNNRoots, onExtended_new] at h,
        fun _ h => by simp [appendNNRoots, onExtended_new] at h⟩
  · intro e he
    rcases List.mem_append.mp he with hold | hnew
    · obtain ⟨⟨s, u, v⟩, hm, rfl⟩ := List.mem_map.mp hold; exact hw.roles.2.1 _ hm
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hnew; cases rel.2 <;> exact hrel
  · intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he; exact hw.roles.2.2 z _ hm
    · simp only [appendNNRoots, onExtended_new] at he; cases he

theorem appendNNRoots_bindings {b : BlockedForest} {p : Problem}
    (hb : b.BindingsValid p) (m : Nat) (r : b.Node) (hr : b.isRoot r = true)
    (rel : OrientedRole) (c : Concept) :
    (b.appendNNRoots m r hr rel c).BindingsValid p := by
  constructor
  · intro a ha; obtain ⟨u, hu⟩ := hb.nomComplete a ha
    exact ⟨oldNode m u, List.mem_map.mpr ⟨(a, u), hu, rfl⟩⟩
  · intro k hk; obtain ⟨u, hu⟩ := hb.anonComplete k hk
    exact ⟨oldNode m u, List.mem_map.mpr ⟨(k, u), hu, rfl⟩⟩
  · intro a r₁ r₂ h1 h2
    obtain ⟨⟨a1, u1⟩, hu1, heq1⟩ := List.mem_map.mp h1
    obtain ⟨⟨a2, u2⟩, hu2, heq2⟩ := List.mem_map.mp h2
    cases heq1; cases heq2
    exact congrArg (oldNode m) (hb.nomFunctional _ u1 u2 hu1 hu2)
  · intro k r₁ r₂ h1 h2
    obtain ⟨⟨k1, u1⟩, hu1, heq1⟩ := List.mem_map.mp h1
    obtain ⟨⟨k2, u2⟩, hu2, heq2⟩ := List.mem_map.mp h2
    cases heq1; cases heq2
    exact congrArg (oldNode m) (hb.anonFunctional _ u1 u2 hu1 hu2)

theorem appendNNRoots_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) {m : Nat} {r : b.Node} (hr : b.isRoot r = true)
    (hlvl : b.nomLevel r + 1 ≤ sroiqMaxDepth rank p) (rel : OrientedRole) (c : Concept) :
    (b.appendNNRoots m r hr rel c).ForestGeom rank p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [appendNNRoots, oldNode, onExtended] using hg.nomLevel0
  · intro a y hy
    obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simpa [appendNNRoots, onExtended_old] using hg.boundNomZero a u hm
  · intro k y hy
    obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp hy
    cases heq
    simpa [appendNNRoots, onExtended_old] using hg.boundAnonZero k u hm
  · intro y
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · rw [appendNNRoots_depth_old]; exact hg.depthBound z
    · rw [appendNNRoots_depth_new]; exact Nat.zero_le _
  · intro y hy
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, onExtended_old] at hy ⊢; exact hg.nomLevelBound z hy
    · simp only [appendNNRoots, onExtended_new]; exact hlvl
  · intro y e he
    rcases extended_cases (b := b) y with ⟨z, rfl⟩ | ⟨k, rfl⟩
    · simp only [appendNNRoots, onExtended_old] at he
      obtain ⟨⟨s, t⟩, hm, rfl⟩ := List.mem_map.mp he
      rw [appendNNRoots_depth_old]; simpa [appendNNRoots, onExtended_old] using hg.toRootBound z _ hm
    · simp only [appendNNRoots, onExtended_new] at he; cases he

theorem appendNNRoots_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) (m : Nat) (r : b.Node) (hr : b.isRoot r = true)
    (rel : OrientedRole) (c : Concept) :
    (b.appendNNRoots m r hr rel c).ABoxSeeded p := by
  have boundOld (ind : Individual) (y : (b.appendNNRoots m r hr rel c).Node)
      (h : (b.appendNNRoots m r hr rel c).BoundTo ind y) :
      ∃ u, y = oldNode m u ∧ b.BoundTo ind u := by
    cases ind with
    | named a =>
      obtain ⟨⟨a', u⟩, hm, heq⟩ := List.mem_map.mp h
      cases heq; exact ⟨u, rfl, hm⟩
    | anonymous d l =>
      obtain ⟨⟨k', u⟩, hm, heq⟩ := List.mem_map.mp h
      cases heq; exact ⟨u, rfl, hm⟩
  have edgeOld (s : OrientedRole) (u v : b.Node) (he : b.Edge s u v) :
      (b.appendNNRoots m r hr rel c).Edge s (oldNode m u) (oldNode m v) := by
    rcases he with ⟨rfl, h⟩ | ⟨hu, hv, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | h | h
    · exact .inl ⟨rfl, by simpa [appendNNRoots, onExtended_old] using h⟩
    · refine .inr (.inl ⟨by simpa [appendNNRoots, onExtended_old] using hu,
        by simpa [appendNNRoots, onExtended_old] using hv, ?_⟩)
      rcases s with ⟨s, _ | _⟩ <;> exact List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩)
    · refine .inr (.inr (.inl ⟨⟨by simpa [appendNNRoots, onExtended_old] using hc.1,
        by simp [appendNNRoots, onExtended_old, hc.2]⟩, ?_⟩))
      rcases s with ⟨s, _ | _⟩ <;> simpa [Down, appendNNRoots, onExtended_old] using h
    · refine .inr (.inr (.inr (.inl ⟨⟨by simpa [appendNNRoots, onExtended_old] using hc.1,
        by simp [appendNNRoots, onExtended_old, hc.2]⟩, ?_⟩)))
      rcases s with ⟨s, _ | _⟩ <;> simpa [Down, converse, appendNNRoots, onExtended_old] using h
    · refine .inr (.inr (.inr (.inr (.inl ?_))))
      simp only [appendNNRoots, onExtended_old]
      exact List.mem_map.mpr ⟨(s, v), h, rfl⟩
    · refine .inr (.inr (.inr (.inr (.inr ?_))))
      simp only [appendNNRoots, onExtended_old]
      exact List.mem_map.mpr ⟨(converse s, u), h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [appendNNRoots, oldNode, onExtended] using ha.root
  · intro ac hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ac.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.classAssertions ac hm u hu
  · intro rab hm y₁ y₂ h1 h2
    obtain ⟨u₁, rfl, hu1⟩ := boundOld rab.2.1 y₁ h1
    obtain ⟨u₂, rfl, hu2⟩ := boundOld rab.2.2 y₂ h2
    exact edgeOld (rab.1, false) u₁ u₂ (ha.objAssertions rab hm u₁ u₂ hu1 hu2)
  · intro rab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld rab.2.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.negObjAssertions rab hm u hu
  · intro ab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ab.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.sameInds ab hm u hu
  · intro ab hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld ab.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.diffInds ab hm u hu
  · intro dal hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld dal.2.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.dataAssertions dal hm u hu
  · intro dal hm y hy
    obtain ⟨u, rfl, hu⟩ := boundOld dal.2.1 y hy
    simpa [appendNNRoots, onExtended_old] using ha.negDataAssertions dal hm u hu

/-! ### Subtree pruning and unified forest merge (`mergeForest`) -/

def retained (b : BlockedForest) (drop : b.Node) : List b.Node :=
  (List.finRange (b.size + 1)).filter fun x => decide (x ≠ drop ∧ !(b.ancestors x).contains drop)

theorem mem_retained {b : BlockedForest} {drop x : b.Node} :
    x ∈ b.retained drop ↔ x ≠ drop ∧ ¬ b.Anc drop x := by
  simp [retained, mem_ancestors]

theorem retained_nodup (b : BlockedForest) (drop : b.Node) : (b.retained drop).Nodup :=
  (List.nodup_finRange _).filter _

theorem retained_pairwise_lt (b : BlockedForest) (drop : b.Node) :
    (b.retained drop).Pairwise (fun x y => x.val < y.val) :=
  (pairwise_lt_finRange _).filter _

theorem retained_root {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) :
    0 ∈ b.retained drop := by
  refine mem_retained.mpr ⟨hd.symm, fun h => ?_⟩
  have hf := h.not_root_right; rw [b.root0] at hf; cases hf

theorem retained_of_isRoot {b : BlockedForest} {drop x : b.Node}
    (hx : b.isRoot x = true) (hne : x ≠ drop) : x ∈ b.retained drop := by
  refine mem_retained.mpr ⟨hne, fun h => ?_⟩
  have hf := h.not_root_right; rw [hx] at hf; cases hf

theorem retained_parent {b : BlockedForest} {drop x : b.Node}
    (hx : x ∈ b.retained drop) (hnr : b.isRoot x = false) :
    b.parent x ∈ b.retained drop := by
  have ⟨hxd, hna⟩ := mem_retained.mp hx
  have hc : b.Child (b.parent x) x := ⟨hnr, rfl⟩
  refine mem_retained.mpr ⟨fun h => hna (h ▸ .parent hc), fun h => hna (.step h hc)⟩

theorem retained_pos {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) :
    0 < (b.retained drop).length :=
  List.length_pos_of_mem (retained_root hd)

abbrev Pruned (b : BlockedForest) (drop : b.Node) := Fin (b.retained drop).length

def source {b : BlockedForest} {drop : b.Node} (_hd : drop ≠ 0) (y : b.Pruned drop) : b.Node :=
  (b.retained drop)[y.val]'y.isLt

theorem source_mem {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) (y : b.Pruned drop) :
    source hd y ∈ b.retained drop :=
  List.getElem_mem y.isLt

theorem source_inj {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) {x y : b.Pruned drop}
    (h : source hd x = source hd y) : x = y :=
  Fin.ext (nodup_getElem_inj (retained_nodup b drop) x.isLt y.isLt h)

theorem source_strictMono {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    {x y : b.Pruned drop} (h : x.val < y.val) : (source hd x).val < (source hd y).val :=
  (List.pairwise_iff_getElem.mp (retained_pairwise_lt b drop)) x.val y.val x.isLt y.isLt h

theorem source_lt_iff {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    {x y : b.Pruned drop} : (source hd x).val < (source hd y).val ↔ x.val < y.val := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy x.val y.val with hlt | heq | hgt
    · exact hlt
    · exact (Nat.lt_irrefl _ (Fin.ext heq ▸ h)).elim
    · exact (Nat.lt_asymm h (source_strictMono hd hgt)).elim
  · exact source_strictMono hd

theorem source_zero {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) :
    source hd ⟨0, retained_pos hd⟩ = 0 := by
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < (source hd ⟨0, retained_pos hd⟩).val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem (retained_root hd)
  cases j with
  | zero => exact hne heq
  | succ k =>
    have hlt := source_strictMono hd (x := ⟨0, retained_pos hd⟩) (y := ⟨k + 1, hj⟩) (Nat.zero_lt_succ k)
    change (source hd ⟨0, retained_pos hd⟩).val < ((b.retained drop)[k + 1]'hj).val at hlt
    rw [heq] at hlt
    have h0v : (0 : b.Node).val = 0 := rfl
    omega

def compact {b : BlockedForest} {drop x : b.Node} (_hd : drop ≠ 0) (hx : x ∈ b.retained drop) :
    b.Pruned drop :=
  ⟨(b.retained drop).idxOf x, List.idxOf_lt_length_of_mem hx⟩

theorem source_compact {b : BlockedForest} {drop x : b.Node} (hd : drop ≠ 0)
    (hx : x ∈ b.retained drop) : source hd (compact hd hx) = x :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)

theorem compact_source {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0) (y : b.Pruned drop) :
    compact hd (source_mem hd y) = y :=
  source_inj hd (source_compact hd (source_mem hd y))

def compactParent {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : b.Pruned drop) : b.Pruned drop :=
  if h : b.isRoot (source hd y) = true then ⟨0, retained_pos hd⟩
  else compact hd (retained_parent (source_mem hd y) (Bool.eq_false_iff.mpr h))

theorem compactParent_source {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    {y : b.Pruned drop} (hnr : b.isRoot (source hd y) = false) :
    source hd (compactParent hd y) = b.parent (source hd y) := by
  have h : ¬ (b.isRoot (source hd y) = true) := by simp [hnr]
  unfold compactParent
  rw [dite_eq_right h, source_compact]

theorem compactParent_lt {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    {y : b.Pruned drop} (hnr : b.isRoot (source hd y) = false) :
    (compactParent hd y).val < y.val :=
  (source_lt_iff hd).mp (by rw [compactParent_source hd hnr]; exact b.parent_lt _ hnr)

def mergeIndex {b : BlockedForest} {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (z : b.Node) : Option (b.Pruned drop) :=
  if z = drop then some (compact hd hk)
  else if h : z ∈ b.retained drop then some (compact hd h)
  else none

theorem mergeIndex_kept {b : BlockedForest} {keep drop z : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hz : z ∈ b.retained drop) :
    mergeIndex hd hk z = some (compact hd hz) := by
  simp [mergeIndex, (mem_retained.mp hz).1, hz]

theorem mergeIndex_drop {b : BlockedForest} {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) :
    mergeIndex hd hk drop = some (compact hd hk) := by
  simp [mergeIndex]

theorem mergeIndex_source {b : BlockedForest} {keep drop z : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) {y : b.Pruned drop} (h : mergeIndex hd hk z = some y) :
    source hd y = if z = drop then keep else z := by
  unfold mergeIndex at h
  split at h
  · rename_i hz; cases h; simp [hz, source_compact]
  · split at h
    · rename_i hne hr; cases h; simp [hne, source_compact]
    · cases h

/-- Geometric admissibility of merging `drop` into `keep`:
- root-into-root (`nomLevel keep ≤ nomLevel drop`),
- blockable-into-root,
- blockable sibling-into-sibling (`parent keep = parent drop`), or
- blockable child/grandchild-into-ancestor (`Child keep drop ∨ Child keep (parent drop)`). -/
def MergeValid (b : BlockedForest) (keep drop : b.Node) : Prop :=
  (b.isRoot keep = true ∧ (b.isRoot drop = true → b.nomLevel keep ≤ b.nomLevel drop)) ∨
  (b.isRoot keep = false ∧ b.isRoot drop = false ∧
    (b.parent keep = b.parent drop ∨ b.Child keep drop ∨ b.Child keep (b.parent drop)))

/-- Orient two distinct roots so `keep` has smaller `nomLevel` (tie-breaking on
smaller index, guaranteeing `drop ≠ 0` whenever `nomLevel 0 = 0`). -/
def orientRootMerge (b : BlockedForest) (r₁ r₂ : b.Node) : b.Node × b.Node :=
  if b.nomLevel r₁ < b.nomLevel r₂ then (r₁, r₂)
  else if b.nomLevel r₂ < b.nomLevel r₁ then (r₂, r₁)
  else if r₁.val < r₂.val then (r₁, r₂)
  else (r₂, r₁)

theorem orientRootMerge_spec {b : BlockedForest} {r₁ r₂ : b.Node}
    (hne : r₁ ≠ r₂) (h0 : b.nomLevel 0 = 0) :
    let (keep, drop) := b.orientRootMerge r₁ r₂
    ((keep = r₁ ∧ drop = r₂) ∨ (keep = r₂ ∧ drop = r₁)) ∧
    keep ≠ drop ∧ drop ≠ 0 ∧ b.nomLevel keep ≤ b.nomLevel drop := by
  dsimp only [orientRootMerge]
  by_cases h1 : b.nomLevel r₁ < b.nomLevel r₂
  · rw [ite_eq_left h1]
    refine ⟨.inl ⟨rfl, rfl⟩, hne, ?_, Nat.le_of_lt h1⟩
    rintro rfl; rw [h0] at h1; omega
  · rw [ite_eq_right h1]
    by_cases h2 : b.nomLevel r₂ < b.nomLevel r₁
    · rw [ite_eq_left h2]
      refine ⟨.inr ⟨rfl, rfl⟩, hne.symm, ?_, Nat.le_of_lt h2⟩
      rintro rfl; rw [h0] at h2; omega
    · rw [ite_eq_right h2]
      by_cases h3 : r₁.val < r₂.val
      · rw [ite_eq_left h3]; dsimp only
        refine ⟨.inl ⟨rfl, rfl⟩, hne, ?_, by omega⟩
        rintro rfl; have h0v : (0 : b.Node).val = 0 := rfl; omega
      · rw [ite_eq_right h3]; dsimp only
        refine ⟨.inr ⟨rfl, rfl⟩, hne.symm, ?_, by omega⟩
        rintro rfl; have h0v : (0 : b.Node).val = 0 := rfl
        exact hne (Fin.ext (by omega))

private def mergeExtraLoops (b : BlockedForest) (keep drop : b.Node) : List IRI :=
  (if b.isRoot drop = true then
    b.rootEdges.filterMap fun (r, u, v) =>
      if (u == keep && v == drop) || (u == drop && v == keep) then some r else none
   else []) ++
  (if b.isRoot drop = false ∧ b.parent drop = keep then b.down drop ++ b.up drop else []) ++
  (if b.isRoot drop = false then
    (b.toRoot drop).filterMap fun (r, t) => if t == keep then some r.1 else none
   else [])

private def mergeExtraDown (b : BlockedForest) (keep drop sy : b.Node) : List IRI :=
  (if sy = keep ∧ b.isRoot keep = false ∧ b.isRoot drop = false ∧ b.parent keep = b.parent drop then
    b.down drop else []) ++
  (if b.isRoot drop = false ∧ sy = b.parent drop ∧ sy ≠ keep ∧
      b.isRoot sy = false ∧ b.parent sy = keep then
    b.up drop else []) ++
  (if b.isRoot drop = true ∧ b.isRoot sy = false ∧ b.parent sy = keep then
    (b.toRoot sy).filterMap fun (r, t) => if t == drop && r.2 then some r.1 else none
   else []) ++
  (if b.isRoot drop = false ∧ sy = keep ∧ b.isRoot keep = false then
    (b.toRoot drop).filterMap fun (r, t) => if t == b.parent keep && r.2 then some r.1 else none
   else [])

private def mergeExtraUp (b : BlockedForest) (keep drop sy : b.Node) : List IRI :=
  (if sy = keep ∧ b.isRoot keep = false ∧ b.isRoot drop = false ∧ b.parent keep = b.parent drop then
    b.up drop else []) ++
  (if b.isRoot drop = false ∧ sy = b.parent drop ∧ sy ≠ keep ∧
      b.isRoot sy = false ∧ b.parent sy = keep then
    b.down drop else []) ++
  (if b.isRoot drop = true ∧ b.isRoot sy = false ∧ b.parent sy = keep then
    (b.toRoot sy).filterMap fun (r, t) => if t == drop && !r.2 then some r.1 else none
   else []) ++
  (if b.isRoot drop = false ∧ sy = keep ∧ b.isRoot keep = false then
    (b.toRoot drop).filterMap fun (r, t) => if t == b.parent keep && !r.2 then some r.1 else none
   else [])

/-- Index conversion between `Fin ((b.retained drop).length - 1 + 1)` and `b.Pruned drop`. -/
def prunedTo {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : Fin ((b.retained drop).length - 1 + 1)) : b.Pruned drop :=
  ⟨y.val, by have hy := y.isLt; have hp := retained_pos hd; omega⟩

def prunedFrom {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : b.Pruned drop) : Fin ((b.retained drop).length - 1 + 1) :=
  ⟨y.val, by have hy := y.isLt; have hp := retained_pos hd; omega⟩

def prunedSrc {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : Fin ((b.retained drop).length - 1 + 1)) : b.Node :=
  source hd (prunedTo hd y)

def prunedIdx {b : BlockedForest} {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (z : b.Node) : Option (Fin ((b.retained drop).length - 1 + 1)) :=
  (mergeIndex hd hk z).map (prunedFrom hd)

def prunedPar {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : Fin ((b.retained drop).length - 1 + 1)) : Fin ((b.retained drop).length - 1 + 1) :=
  prunedFrom hd (compactParent hd (prunedTo hd y))

theorem prunedSrc_from {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    (y : b.Pruned drop) : prunedSrc hd (prunedFrom hd y) = source hd y := rfl

theorem prunedSrc_compact {b : BlockedForest} {drop x : b.Node} (hd : drop ≠ 0)
    (hx : x ∈ b.retained drop) : prunedSrc hd (prunedFrom hd (compact hd hx)) = x :=
  source_compact hd hx

theorem prunedSrc_inj {b : BlockedForest} {drop : b.Node} (hd : drop ≠ 0)
    {x y : Fin ((b.retained drop).length - 1 + 1)} (h : prunedSrc hd x = prunedSrc hd y) :
    x = y := by
  have hv : (prunedTo hd x).val = (prunedTo hd y).val := congrArg Fin.val (source_inj hd h)
  exact Fin.ext hv

/-- Unified forest merge: prunes `drop`'s blockable subtree and redirects all
labels, guards, edges, bindings, inequalities, and NN-bounds from `drop` to `keep`. -/
def mergeForest (b : BlockedForest) (keep drop : b.Node)
    (hd : drop ≠ 0) (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) :
    BlockedForest :=
  have hkeepRootOfDropRoot : b.isRoot drop = true → b.isRoot keep = true := by
    intro hdr
    rcases hvalid with ⟨hkr, _⟩ | ⟨_, hdnf, _⟩
    · exact hkr
    · rw [hdr] at hdnf; cases hdnf
  have mIdx_isRoot : ∀ z y', b.isRoot z = true → prunedIdx hd hk z = some y' →
      b.isRoot (prunedSrc hd y') = true := by
    intro z y' hzr hm
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hm
    have hs := mergeIndex_source hd hk hp'
    rw [prunedSrc_from, hs]
    split
    · subst z; exact hkeepRootOfDropRoot hzr
    · exact hzr
  { size := (b.retained drop).length - 1
    isRoot := fun y => b.isRoot (prunedSrc hd y)
    root0 := by
      have h0 : prunedTo hd 0 = ⟨0, retained_pos hd⟩ := Fin.ext rfl
      change b.isRoot (source hd (prunedTo hd 0)) = true
      rw [h0, source_zero hd]; exact b.root0
    nomLevel := fun y => b.nomLevel (prunedSrc hd y)
    parent := prunedPar hd
    parent_lt := fun y hy => compactParent_lt hd hy
    labels := fun y => b.labels (prunedSrc hd y) ++ if prunedSrc hd y = keep then b.labels drop else []
    guardLabels := fun y => b.guardLabels (prunedSrc hd y) ++ if prunedSrc hd y = keep then b.guardLabels drop else []
    down := fun y => b.down (prunedSrc hd y) ++ mergeExtraDown b keep drop (prunedSrc hd y)
    up := fun y => b.up (prunedSrc hd y) ++ mergeExtraUp b keep drop (prunedSrc hd y)
    loops := fun y => b.loops (prunedSrc hd y) ++
      if prunedSrc hd y = keep then b.loops drop ++ mergeExtraLoops b keep drop else []
    rootEdges :=
      (b.rootEdges.filterMap fun (r, u, v) =>
        match prunedIdx hd hk u, prunedIdx hd hk v with
        | some u', some v' => if u' ≠ v' then some (r, u', v') else none
        | _, _ => none) ++
      (if h : b.isRoot keep = true ∧ b.isRoot drop = false ∧
            b.isRoot (b.parent drop) = true ∧ b.parent drop ≠ keep then
        let p' := prunedFrom hd (compact hd (retained_of_isRoot h.2.2.1
          (fun heq => by rw [heq, h.2.1] at h; exact Bool.noConfusion h.2.2.1)))
        let k' := prunedFrom hd (compact hd hk)
        (b.down drop).map (fun r => (r, p', k')) ++ (b.up drop).map (fun r => (r, k', p'))
      else []) ++
      (if _h : b.isRoot keep = true ∧ b.isRoot drop = false then
        let k' := prunedFrom hd (compact hd hk)
        (b.toRoot drop).filterMap fun (r, t) =>
          match prunedIdx hd hk t with
          | some t' =>
            if t' ≠ k' then some (if r.2 then (r.1, t', k') else (r.1, k', t')) else none
          | none => none
      else [])
    rootEdges_valid := by
      intro e he
      rcases List.mem_append.mp he with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · obtain ⟨⟨r, u, v⟩, hm, hres⟩ := List.mem_filterMap.mp h1
          have ⟨hu, hv, _⟩ := b.rootEdges_valid _ hm
          cases hu' : prunedIdx hd hk u <;> cases hv' : prunedIdx hd hk v <;> simp [hu', hv'] at hres
          rename_i u' v'
          by_cases hne : u' = v'
          · simp [hne] at hres
          · simp [hne] at hres
            cases hres
            exact ⟨mIdx_isRoot u u' hu hu', mIdx_isRoot v v' hv hv', hne⟩
        · split at h2
          · rename_i h
            have hne : prunedFrom hd (compact hd (retained_of_isRoot h.2.2.1
                (fun heq => by rw [heq, h.2.1] at h; exact Bool.noConfusion h.2.2.1))) ≠
                prunedFrom hd (compact hd hk) := by
              intro heq
              have hsrc := congrArg (prunedSrc hd) heq
              rw [prunedSrc_compact, prunedSrc_compact] at hsrc
              exact h.2.2.2 hsrc
            rcases List.mem_append.mp h2 with hd' | hu'
            · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hd'
              exact ⟨by rw [prunedSrc_compact]; exact h.2.2.1,
                by rw [prunedSrc_compact]; exact h.1, hne⟩
            · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hu'
              exact ⟨by rw [prunedSrc_compact]; exact h.1,
                by rw [prunedSrc_compact]; exact h.2.2.1, Ne.symm hne⟩
          · cases h2
      · split at h3
        · rename_i h
          obtain ⟨⟨r, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
          have ht := (b.toRoot_valid drop _ hm).2.1
          cases ht' : prunedIdx hd hk t <;> simp [ht'] at hres
          rename_i t'
          by_cases hne : t' = prunedFrom hd (compact hd hk)
          · simp [hne] at hres
          · simp [hne] at hres
            cases hres
            have hk' : b.isRoot (prunedSrc hd (prunedFrom hd (compact hd hk))) = true := by
              rw [prunedSrc_compact]; exact h.1
            cases r.2 <;> simp [hk', mIdx_isRoot t t' ht ht', hne, Ne.symm hne]
        · cases h3
    toRoot := fun y =>
      ((b.toRoot (prunedSrc hd y)).filterMap fun (r, t) =>
        match prunedIdx hd hk t with
        | some t' => if prunedPar hd y ≠ t' then some (r, t') else none
        | none => none) ++
      (if _h : b.isRoot keep = true ∧ b.isRoot drop = false ∧ prunedSrc hd y = b.parent drop ∧
            b.isRoot (prunedSrc hd y) = false ∧ b.parent (prunedSrc hd y) ≠ keep then
        let k' := prunedFrom hd (compact hd hk)
        (b.down drop).map (fun r => ((r, false), k')) ++ (b.up drop).map (fun r => ((r, true), k'))
      else []) ++
      (if _h : b.isRoot keep = false ∧ b.isRoot drop = false ∧ prunedSrc hd y = keep then
        (b.toRoot drop).filterMap fun (r, t) =>
          match prunedIdx hd hk t with
          | some t' => if prunedPar hd y ≠ t' then some (r, t') else none
          | none => none
      else [])
    toRoot_valid := by
      intro y e he
      rcases List.mem_append.mp he with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · obtain ⟨⟨r, t⟩, hm, hres⟩ := List.mem_filterMap.mp h1
          have ⟨hsy, ht, _⟩ := b.toRoot_valid (prunedSrc hd y) _ hm
          cases ht' : prunedIdx hd hk t <;> simp [ht'] at hres
          rename_i t'
          by_cases hne : prunedPar hd y = t'
          · simp [hne] at hres
          · simp [hne] at hres
            cases hres
            exact ⟨hsy, mIdx_isRoot t t' ht ht', hne⟩
        · split at h2
          · rename_i h
            have hne : prunedPar hd y ≠ prunedFrom hd (compact hd hk) := by
              intro heq
              have hs := congrArg (prunedSrc hd) heq
              rw [prunedSrc_compact] at hs
              have hp : prunedSrc hd (prunedPar hd y) = b.parent (prunedSrc hd y) :=
                compactParent_source hd h.2.2.2.1
              exact h.2.2.2.2 (hp.symm.trans hs)
            rcases List.mem_append.mp h2 with hd' | hu'
            · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hd'
              exact ⟨h.2.2.2.1, by rw [prunedSrc_compact]; exact h.1, hne⟩
            · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hu'
              exact ⟨h.2.2.2.1, by rw [prunedSrc_compact]; exact h.1, hne⟩
          · cases h2
      · split at h3
        · rename_i h
          obtain ⟨⟨r, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
          have ht := (b.toRoot_valid drop _ hm).2.1
          cases ht' : prunedIdx hd hk t <;> simp [ht'] at hres
          rename_i t'
          by_cases hne : prunedPar hd y = t'
          · simp [hne] at hres
          · simp [hne] at hres
            cases hres
            exact ⟨h.2.2 ▸ h.1, mIdx_isRoot t t' ht ht', hne⟩
        · cases h3
    noms := b.noms.filterMap fun (a, u) => (prunedIdx hd hk u).map (a, ·)
    noms_valid := by
      intro q hq
      obtain ⟨⟨a, u⟩, hm, hres⟩ := List.mem_filterMap.mp hq
      obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hres
      exact mIdx_isRoot u u' (b.noms_valid _ hm) hu'
    anons := b.anons.filterMap fun (k, u) => (prunedIdx hd hk u).map (k, ·)
    anons_valid := by
      intro q hq
      obtain ⟨⟨k, u⟩, hm, hres⟩ := List.mem_filterMap.mp hq
      obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hres
      exact mIdx_isRoot u u' (b.anons_valid _ hm) hu'
    unequal := b.unequal.filterMap fun (u, v) =>
      match prunedIdx hd hk u, prunedIdx hd hk v with
      | some u', some v' => some (u', v')
      | _, _ => none
    nnBounds := b.nnBounds.filterMap fun (u, r, c, ts) =>
      if u = drop then none
      else (prunedIdx hd hk u).map fun u' => (u', r, c, ts.filterMap (prunedIdx hd hk))
    nnBounds_valid := by
      intro e he
      obtain ⟨⟨u, r, c, ts⟩, hm, hres⟩ := List.mem_filterMap.mp he
      by_cases hud : u = drop
      · simp [hud] at hres
      · simp only [hud, ↓reduceIte] at hres
        obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hres
        have ⟨hur, hts⟩ := b.nnBounds_valid _ hm
        have hsu : prunedSrc hd u' = u := by
          obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hu'
          rw [prunedSrc_from, mergeIndex_source hd hk hp']; simp [hud]
        refine ⟨hsu.symm ▸ hur, fun o' ho' => ?_⟩
        obtain ⟨o, ho, ho'm⟩ := List.mem_filterMap.mp ho'
        have ⟨hor, holvl⟩ := hts o ho
        refine ⟨mIdx_isRoot o o' hor ho'm, ?_⟩
        obtain ⟨po, hpo, rfl⟩ := Option.map_eq_some_iff.mp ho'm
        rw [prunedSrc_from, mergeIndex_source hd hk hpo, hsu]
        split
        · subst o
          rcases hvalid with ⟨_, hkl⟩ | ⟨_, hdnf, _⟩
          · exact Nat.le_trans (hkl hor) holvl
          · rw [hor] at hdnf; cases hdnf
        · exact holvl
    blockedBy _ := none
    keyDisjoint := b.keyDisjoint.filterMap fun (r₁, r₂, dp) =>
      match prunedIdx hd hk r₁, prunedIdx hd hk r₂ with
      | some r₁', some r₂' => some (r₁', r₂', dp)
      | _, _ => none
    keyDisjoint_valid := by
      intro e he
      obtain ⟨⟨r₁, r₂, dp⟩, hm, hres⟩ := List.mem_filterMap.mp he
      have ⟨hr₁, hr₂⟩ := b.keyDisjoint_valid _ hm
      cases h1 : prunedIdx hd hk r₁ <;> cases h2 : prunedIdx hd hk r₂ <;> simp [h1, h2] at hres
      cases hres
      exact ⟨mIdx_isRoot r₁ _ hr₁ h1, mIdx_isRoot r₂ _ hr₂ h2⟩ }

private abbrev mergeSrc {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (y : (b.mergeForest keep drop hd hk hvalid).Node) : b.Node :=
  prunedSrc hd y

private abbrev mergeIdx {b : BlockedForest} {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) (z : b.Node) :
    Option (b.mergeForest keep drop hd hk hvalid).Node :=
  prunedIdx hd hk z

private theorem mergeSrc_mem {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (y : (b.mergeForest keep drop hd hk hvalid).Node) :
    mergeSrc y ∈ b.retained drop :=
  source_mem hd _

private theorem mergeSrc_inj {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {x y : (b.mergeForest keep drop hd hk hvalid).Node}
    (h : mergeSrc x = mergeSrc y) : x = y :=
  prunedSrc_inj hd h

private theorem mergeIdx_kept {b : BlockedForest} {keep drop z : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (hz : z ∈ b.retained drop) :
    ∃ y, mergeIdx hd hk hvalid z = some y ∧ mergeSrc y = z := by
  refine ⟨prunedFrom hd (compact hd hz), ?_, prunedSrc_compact hd hz⟩
  unfold mergeIdx prunedIdx
  rw [mergeIndex_kept hd hk hz]; rfl

private theorem mergeIdx_drop {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop} :
    ∃ y, mergeIdx hd hk hvalid drop = some y ∧ mergeSrc y = keep := by
  refine ⟨prunedFrom hd (compact hd hk), ?_, prunedSrc_compact hd hk⟩
  unfold mergeIdx prunedIdx
  rw [mergeIndex_drop hd hk]; rfl

private theorem mergeIdx_src {b : BlockedForest} {keep drop z : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {y : (b.mergeForest keep drop hd hk hvalid).Node}
    (h : mergeIdx hd hk hvalid z = some y) :
    mergeSrc y = if z = drop then keep else z := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact mergeIndex_source hd hk hp

private theorem mergeIdx_of_isRoot {b : BlockedForest} {keep drop z : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (hz : b.isRoot z = true) :
    ∃ y, mergeIdx hd hk hvalid z = some y := by
  by_cases hzd : z = drop
  · subst hzd; obtain ⟨y, hy, _⟩ := mergeIdx_drop (hd := hd) (hk := hk) (hvalid := hvalid)
    exact ⟨y, hy⟩
  · obtain ⟨y, hy, _⟩ := mergeIdx_kept (hd := hd) (hk := hk) (hvalid := hvalid) (retained_of_isRoot hz hzd)
    exact ⟨y, hy⟩

private theorem mergeForest_child_iff {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {u v : (b.mergeForest keep drop hd hk hvalid).Node} :
    (b.mergeForest keep drop hd hk hvalid).Child u v ↔ b.Child (mergeSrc u) (mergeSrc v) := by
  constructor
  · rintro ⟨hv, hp⟩
    refine ⟨hv, ?_⟩
    have := congrArg mergeSrc hp
    change mergeSrc ⟨(compactParent hd _).val, _⟩ = mergeSrc u at this
    have hc := compactParent_source hd hv
    exact hc.symm.trans this
  · rintro ⟨hv, hp⟩
    refine ⟨hv, mergeSrc_inj ?_⟩
    change source hd (compactParent hd ⟨v.val, _⟩) = mergeSrc u
    have hc := compactParent_source hd (y := ⟨v.val, by have := v.isLt; have := retained_pos hd; dsimp [mergeForest] at *; omega⟩) hv
    exact hc.trans hp

theorem mergeForest_depth {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (y : (b.mergeForest keep drop hd hk hvalid).Node) :
    (b.mergeForest keep drop hd hk hvalid).depth y = b.depth (mergeSrc y) := by
  by_cases hr : b.isRoot (mergeSrc y) = true
  · have hr' : (b.mergeForest keep drop hd hk hvalid).isRoot y = true := hr
    rw [depth_root hr', depth_root hr]
  · have hnr : b.isRoot (mergeSrc y) = false := Bool.eq_false_iff.mpr hr
    have hc : (b.mergeForest keep drop hd hk hvalid).Child
        ((b.mergeForest keep drop hd hk hvalid).parent y) y := ⟨hnr, rfl⟩
    have hc' := mergeForest_child_iff.mp hc
    rw [depth_child hc, depth_child hc', mergeForest_depth]
termination_by y.val
decreasing_by exact (b.mergeForest keep drop hd hk hvalid).parent_lt y (Bool.eq_false_iff.mpr hr)

theorem mergeForest_realizes {b : BlockedForest} {i : Interpretation datatypeMap}
    {env : b.Node → i.Object} (hr : b.Realizes i env) {keep drop : b.Node}
    (hd : drop ≠ 0) (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop)
    (heq : env keep = env drop) :
    (b.mergeForest keep drop hd hk hvalid).Realizes i (fun y => env (mergeSrc y)) := by
  have envIdx (z : b.Node) (y : (b.mergeForest keep drop hd hk hvalid).Node)
      (hm : mergeIdx hd hk hvalid z = some y) : env (mergeSrc y) = env z := by
    rw [mergeIdx_src hm]
    split
    · subst z; exact heq
    · rfl
  constructor
  case labels =>
    intro y c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hr.labels _ c h1
    · split at h2
      · rename_i hsy; change holds i (env (prunedSrc hd y)) c; rw [hsy, heq]; exact hr.labels drop c h2
      · cases h2
  case guards =>
    intro y g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hr.guards _ g h1
    · split at h2
      · rename_i hsy; change g.Holds i (env (prunedSrc hd y)); rw [hsy, heq]; exact hr.guards drop g h2
      · cases h2
  case unequal =>
    intro u v huv
    obtain ⟨⟨a, d⟩, hm, hres⟩ := List.mem_filterMap.mp huv
    cases ha : mergeIdx hd hk hvalid a <;> cases hd' : mergeIdx hd hk hvalid d <;>
      simp [ha, hd'] at hres
    cases hres
    rw [envIdx a _ ha, envIdx d _ hd']
    exact hr.unequal a d hm
  case noms =>
    intro a y hy
    obtain ⟨⟨a', u⟩, hm, hres⟩ := List.mem_filterMap.mp hy
    obtain ⟨u', hu', heq'⟩ := Option.map_eq_some_iff.mp hres
    cases heq'
    rw [envIdx u y hu']
    exact hr.noms a u hm
  case anons =>
    intro k y hy
    obtain ⟨⟨k', u⟩, hm, hres⟩ := List.mem_filterMap.mp hy
    obtain ⟨u', hu', heq'⟩ := Option.map_eq_some_iff.mp hres
    cases heq'
    rw [envIdx u y hu']
    exact hr.anons k u hm
  case nnBounds =>
    intro e he z hz hzc
    obtain ⟨⟨u, s, d, ts⟩, hm, hres⟩ := List.mem_filterMap.mp he
    by_cases hud : u = drop
    · simp [hud] at hres
    · simp only [hud, ↓reduceIte] at hres
      obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hres
      rw [envIdx u u' hu'] at hz
      obtain ⟨o, ho, rfl⟩ := hr.nnBounds (u, s, d, ts) hm z hz hzc
      obtain ⟨o', ho'⟩ := mergeIdx_of_isRoot (hd := hd) (hk := hk) (hvalid := hvalid)
        ((b.nnBounds_valid _ hm).2 o ho).1
      exact ⟨o', List.mem_filterMap.mpr ⟨o, ho, ho'⟩, (envIdx o o' ho').symm⟩
  case keyDisjoint =>
    intro e he y
    obtain ⟨⟨r₁, r₂, dp⟩, hm, hres⟩ := List.mem_filterMap.mp he
    cases h1 : mergeIdx hd hk hvalid r₁ <;> cases h2 : mergeIdx hd hk hvalid r₂ <;>
      simp [h1, h2] at hres
    cases hres
    rw [envIdx r₁ _ h1, envIdx r₂ _ h2]
    exact hr.keyDisjoint (r₁, r₂, dp) hm y
  case edges =>
    have childHelper (s : OrientedRole) (u v : (b.mergeForest keep drop hd hk hvalid).Node)
        (hc : (b.mergeForest keep drop hd hk hvalid).Child u v)
        (hdwn : (b.mergeForest keep drop hd hk hvalid).Down s v) :
        holdsOriented i s (env (mergeSrc u)) (env (mergeSrc v)) := by
      have hcb := mergeForest_child_iff.mp hc
      have hor : b.Down s (mergeSrc v) ∨
          (if s.2 then s.1 ∈ mergeExtraUp b keep drop (mergeSrc v)
           else s.1 ∈ mergeExtraDown b keep drop (mergeSrc v)) := by
        rcases s with ⟨sn, _ | _⟩ <;> exact List.mem_append.mp hdwn
      rcases hor with hold | hextra
      · exact hr.edges s _ _ (.inr (.inr (.inl ⟨hcb, hold⟩)))
      · rcases s with ⟨sn, _ | _⟩
        · dsimp [mergeExtraDown] at hextra
          rcases List.mem_append.mp hextra with h123 | h4
          · rcases List.mem_append.mp h123 with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · split at h1
                · rename_i h
                  have hpu : b.parent keep = mergeSrc u := (congrArg b.parent h.1).symm.trans hcb.2
                  have hcd : b.Child (mergeSrc u) drop := ⟨h.2.2.1, h.2.2.2.symm.trans hpu⟩
                  rw [h.1, heq]; exact hr.edges (sn, false) _ _ (.inr (.inr (.inl ⟨hcd, h1⟩)))
                · cases h1
              · split at h2
                · rename_i h
                  have hcd : b.Child (mergeSrc v) drop := ⟨h.1, h.2.1.symm⟩
                  have huk : mergeSrc u = keep := hcb.2.symm.trans h.2.2.2.2
                  rw [huk, heq]
                  exact (orientation_flip i (sn, false) _ _).mp
                    (hr.edges (sn, true) _ _ (.inr (.inr (.inl ⟨hcd, h2⟩))))
                · cases h2
            · split at h3
              · rename_i h
                obtain ⟨⟨trel, tt⟩, htm, htres⟩ := List.mem_filterMap.mp h3
                by_cases hcond : (tt == drop && trel.2) = true
                · simp only [hcond, ↓reduceIte, Option.some.injEq] at htres
                  subst htres
                  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                  have huk : mergeSrc u = keep := hcb.2.symm.trans h.2.2
                  have he1 := hr.edges trel (mergeSrc v) tt (.inr (.inr (.inr (.inr (.inl htm)))))
                  have hte : env (mergeSrc u) = env tt := by rw [huk, heq, hcond.1]
                  rw [hte]
                  rcases trel with ⟨tn, _ | _⟩
                  · cases hcond.2
                  · exact (orientation_flip i (tn, false) _ _).mp he1
                · simp [hcond] at htres
              · cases h3
          · split at h4
            · rename_i h
              obtain ⟨⟨trel, tt⟩, htm, htres⟩ := List.mem_filterMap.mp h4
              by_cases hcond : (tt == b.parent keep && trel.2) = true
              · simp only [hcond, ↓reduceIte, Option.some.injEq] at htres
                subst htres
                simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                have hu : mergeSrc u = b.parent keep := hcb.2.symm.trans (congrArg b.parent h.2.1)
                have he1 := hr.edges trel drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
                have hue : env (mergeSrc u) = env tt := by rw [hu, hcond.1]
                have hve : env (mergeSrc v) = env drop := by rw [h.2.1, heq]
                rw [hue, hve]
                rcases trel with ⟨tn, _ | _⟩
                · cases hcond.2
                · exact (orientation_flip i (tn, false) _ _).mp he1
              · simp [hcond] at htres
            · cases h4
        · dsimp [mergeExtraUp] at hextra
          rcases List.mem_append.mp hextra with h123 | h4
          · rcases List.mem_append.mp h123 with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · split at h1
                · rename_i h
                  have hpu : b.parent keep = mergeSrc u := (congrArg b.parent h.1).symm.trans hcb.2
                  have hcd : b.Child (mergeSrc u) drop := ⟨h.2.2.1, h.2.2.2.symm.trans hpu⟩
                  rw [h.1, heq]; exact hr.edges (sn, true) _ _ (.inr (.inr (.inl ⟨hcd, h1⟩)))
                · cases h1
              · split at h2
                · rename_i h
                  have hcd : b.Child (mergeSrc v) drop := ⟨h.1, h.2.1.symm⟩
                  have huk : mergeSrc u = keep := hcb.2.symm.trans h.2.2.2.2
                  rw [huk, heq]
                  exact (orientation_flip i (sn, false) _ _).mpr
                    (hr.edges (sn, false) _ _ (.inr (.inr (.inl ⟨hcd, h2⟩))))
                · cases h2
            · split at h3
              · rename_i h
                obtain ⟨⟨trel, tt⟩, htm, htres⟩ := List.mem_filterMap.mp h3
                by_cases hcond : (tt == drop && !trel.2) = true
                · simp only [hcond, ↓reduceIte, Option.some.injEq] at htres
                  subst htres
                  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
                  have huk : mergeSrc u = keep := hcb.2.symm.trans h.2.2
                  have he1 := hr.edges trel (mergeSrc v) tt (.inr (.inr (.inr (.inr (.inl htm)))))
                  have hte : env (mergeSrc u) = env tt := by rw [huk, heq, hcond.1]
                  rw [hte]
                  rcases trel with ⟨tn, _ | _⟩
                  · exact (orientation_flip i (tn, false) _ _).mpr he1
                  · cases hcond.2
                · simp [hcond] at htres
              · cases h3
          · split at h4
            · rename_i h
              obtain ⟨⟨trel, tt⟩, htm, htres⟩ := List.mem_filterMap.mp h4
              by_cases hcond : (tt == b.parent keep && !trel.2) = true
              · simp only [hcond, ↓reduceIte, Option.some.injEq] at htres
                subst htres
                simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
                have hu : mergeSrc u = b.parent keep := hcb.2.symm.trans (congrArg b.parent h.2.1)
                have he1 := hr.edges trel drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
                have hue : env (mergeSrc u) = env tt := by rw [hu, hcond.1]
                have hve : env (mergeSrc v) = env drop := by rw [h.2.1, heq]
                rw [hue, hve]
                rcases trel with ⟨tn, _ | _⟩
                · exact (orientation_flip i (tn, false) _ _).mpr he1
                · cases hcond.2
              · simp [hcond] at htres
            · cases h4
    intro s u v huv
    rcases huv with ⟨rfl, hl⟩ | ⟨hu, hv, hre⟩ | ⟨hc, hd'⟩ | ⟨hc, hd'⟩ | htr | htr
    · rcases List.mem_append.mp hl with h1 | h2
      · exact hr.edges s _ _ (.inl ⟨rfl, h1⟩)
      · split at h2
        · rename_i hsu
          have hsu' : mergeSrc u = keep := hsu
          rcases List.mem_append.mp h2 with hdl | hex
          · rw [hsu', heq]; exact hr.edges s drop drop (.inl ⟨rfl, hdl⟩)
          · unfold mergeExtraLoops at hex
            rcases List.mem_append.mp hex with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · split at h1
                · obtain ⟨⟨rn, a, d⟩, hrm, hres⟩ := List.mem_filterMap.mp h1
                  by_cases hcond : ((a == keep && d == drop) || (a == drop && d == keep)) = true
                  · simp only [hcond, ↓reduceIte, Option.some.injEq] at hres
                    have he1 := hr.edges (rn, false) a d
                      (.inr (.inl ⟨(b.rootEdges_valid _ hrm).1, (b.rootEdges_valid _ hrm).2.1, hrm⟩))
                    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
                    rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rw [hsu']; rcases s with ⟨sn, _ | _⟩ <;> (dsimp at hres; subst hres; simpa [heq, holdsOriented] using he1)
                    · rw [hsu']; rcases s with ⟨sn, _ | _⟩ <;> (dsimp at hres; subst hres; simpa [heq, holdsOriented] using he1)
                  · simp [hcond] at hres
                · cases h1
              · split at h2
                · rename_i h
                  have hcd : b.Child keep drop := ⟨h.1, h.2⟩
                  rcases List.mem_append.mp h2 with hdn | hup
                  · have he1 := hr.edges (s.1, false) keep drop (.inr (.inr (.inl ⟨hcd, hdn⟩)))
                    rw [hsu']; rcases s with ⟨sn, _ | _⟩ <;> simpa [heq, holdsOriented] using he1
                  · have he1 := hr.edges (s.1, true) keep drop (.inr (.inr (.inl ⟨hcd, hup⟩)))
                    rw [hsu']; rcases s with ⟨sn, _ | _⟩ <;> simpa [heq, holdsOriented] using he1
                · cases h2
            · split at h3
              · obtain ⟨⟨trel, tt⟩, htm, htres⟩ := List.mem_filterMap.mp h3
                by_cases htk : (tt == keep) = true
                · simp only [htk, ↓reduceIte, Option.some.injEq] at htres
                  have ht : tt = keep := beq_iff_eq.mp htk
                  have he1 := hr.edges trel drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
                  rw [ht, ← heq] at he1
                  rw [hsu']
                  rcases trel with ⟨tn, _ | _⟩ <;> rcases s with ⟨sn, _ | _⟩ <;>
                    (dsimp at htres; subst htres; simpa [holdsOriented] using he1)
                · simp [htk] at htres
              · cases h3
        · cases h2
    · have rootHelper (sn : IRI) (a c : (b.mergeForest keep drop hd hk hvalid).Node)
          (h : (sn, a, c) ∈ (b.mergeForest keep drop hd hk hvalid).rootEdges) :
          holdsOriented i (sn, false) (env (mergeSrc a)) (env (mergeSrc c)) := by
        rcases List.mem_append.mp h with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · obtain ⟨⟨rn, x, y⟩, hrm, hres⟩ := List.mem_filterMap.mp h1
            cases hx : mergeIdx hd hk hvalid x <;> cases hy : mergeIdx hd hk hvalid y <;>
              simp [hx, hy] at hres
            obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
            rw [envIdx x _ hx, envIdx y _ hy]
            exact hr.edges (sn, false) x y
              (.inr (.inl ⟨(b.rootEdges_valid _ hrm).1, (b.rootEdges_valid _ hrm).2.1, hrm⟩))
          · split at h2
            · rename_i hcond
              have hcd : b.Child (b.parent drop) drop := ⟨hcond.2.1, rfl⟩
              rcases List.mem_append.mp h2 with hdn | hup
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hdn
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, prunedSrc_compact, heq]
                exact hr.edges (sn, false) (b.parent drop) drop (.inr (.inr (.inl ⟨hcd, hrm⟩)))
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hup
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, prunedSrc_compact, heq]
                exact (orientation_flip i (sn, false) _ _).mp
                  (hr.edges (sn, true) (b.parent drop) drop (.inr (.inr (.inl ⟨hcd, hrm⟩))))
            · cases h2
        · split at h3
          · obtain ⟨⟨trel, tt⟩, htm, hres⟩ := List.mem_filterMap.mp h3
            cases ht : mergeIdx hd hk hvalid tt <;> simp [ht] at hres
            obtain ⟨_, heq'⟩ := ite_none_some_eq_some hres
            have he1 := hr.edges trel drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
            rcases trel with ⟨tn, _ | _⟩ <;> simp at heq'
            · obtain ⟨rfl, rfl, rfl⟩ := heq'
              dsimp only [mergeSrc]
              rw [prunedSrc_compact, heq, envIdx tt _ ht]; exact he1
            · obtain ⟨rfl, rfl, rfl⟩ := heq'
              dsimp only [mergeSrc]
              rw [prunedSrc_compact, heq, envIdx tt _ ht]
              exact (orientation_flip i (sn, false) _ _).mp he1
          · cases h3
      rcases s with ⟨sn, _ | _⟩
      · exact rootHelper sn u v hre
      · exact (orientation_flip i (sn, false) _ _).mpr (rootHelper sn v u hre)
    · exact childHelper s u v hc hd'
    · exact (orientation_flip i s _ _).mp (childHelper (converse s) v u hc hd')
    · have toRootHelper (s' : OrientedRole) (a c : (b.mergeForest keep drop hd hk hvalid).Node)
          (h : (s', c) ∈ (b.mergeForest keep drop hd hk hvalid).toRoot a) :
          holdsOriented i s' (env (mergeSrc a)) (env (mergeSrc c)) := by
        rcases List.mem_append.mp h with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · obtain ⟨⟨trel, tt⟩, htm, hres⟩ := List.mem_filterMap.mp h1
            cases ht : mergeIdx hd hk hvalid tt <;> simp [ht] at hres
            obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
            rw [envIdx tt _ ht]
            exact hr.edges s' (mergeSrc a) tt (.inr (.inr (.inr (.inr (.inl htm)))))
          · split at h2
            · rename_i hcond
              have hcd : b.Child (mergeSrc a) drop := ⟨hcond.2.1, hcond.2.2.1.symm⟩
              rcases List.mem_append.mp h2 with hdn | hup
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hdn
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, heq]
                exact hr.edges (rn, false) (prunedSrc hd a) drop (.inr (.inr (.inl ⟨hcd, hrm⟩)))
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hup
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, heq]
                exact hr.edges (rn, true) (prunedSrc hd a) drop (.inr (.inr (.inl ⟨hcd, hrm⟩)))
            · cases h2
        · split at h3
          · rename_i hcond
            obtain ⟨⟨trel, tt⟩, htm, hres⟩ := List.mem_filterMap.mp h3
            cases ht : mergeIdx hd hk hvalid tt <;> simp [ht] at hres
            obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
            have hae : env (mergeSrc a) = env drop := by dsimp only [mergeSrc]; rw [hcond.2.2, heq]
            rw [hae, envIdx tt _ ht]
            exact hr.edges s' drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
          · cases h3
      exact toRootHelper s u v htr
    · have toRootHelper (s' : OrientedRole) (a c : (b.mergeForest keep drop hd hk hvalid).Node)
          (h : (s', c) ∈ (b.mergeForest keep drop hd hk hvalid).toRoot a) :
          holdsOriented i s' (env (mergeSrc a)) (env (mergeSrc c)) := by
        rcases List.mem_append.mp h with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · obtain ⟨⟨trel, tt⟩, htm, hres⟩ := List.mem_filterMap.mp h1
            cases ht : mergeIdx hd hk hvalid tt <;> simp [ht] at hres
            obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
            rw [envIdx tt _ ht]
            exact hr.edges s' (mergeSrc a) tt (.inr (.inr (.inr (.inr (.inl htm)))))
          · split at h2
            · rename_i hcond
              have hcd : b.Child (mergeSrc a) drop := ⟨hcond.2.1, hcond.2.2.1.symm⟩
              rcases List.mem_append.mp h2 with hdn | hup
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hdn
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, heq]
                exact hr.edges (rn, false) (prunedSrc hd a) drop (.inr (.inr (.inl ⟨hcd, hrm⟩)))
              · obtain ⟨rn, hrm, heq'⟩ := List.mem_map.mp hup
                cases heq'
                dsimp only [mergeSrc]
                rw [prunedSrc_compact, heq]
                exact hr.edges (rn, true) (prunedSrc hd a) drop (.inr (.inr (.inl ⟨hcd, hrm⟩)))
            · cases h2
        · split at h3
          · rename_i hcond
            obtain ⟨⟨trel, tt⟩, htm, hres⟩ := List.mem_filterMap.mp h3
            cases ht : mergeIdx hd hk hvalid tt <;> simp [ht] at hres
            obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
            have hae : env (mergeSrc a) = env drop := by dsimp only [mergeSrc]; rw [hcond.2.2, heq]
            rw [hae, envIdx tt _ ht]
            exact hr.edges s' drop tt (.inr (.inr (.inr (.inr (.inl htm)))))
          · cases h3
      exact (orientation_flip i s _ _).mp (toRootHelper (converse s) v u htr)

theorem mergeForest_within {b : BlockedForest} {rank : Rank} {p : Problem}
    (hw : b.Within rank p) {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) :
    (b.mergeForest keep drop hd hk hvalid).Within rank p := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · intro y c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hw.labels _ h1
    · split at h2
      · exact hw.labels drop h2
      · cases h2
  · intro y g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hw.guards _ h1
    · split at h2
      · exact hw.guards drop h2
      · cases h2
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hw.roles.1 _).1 h1
      · unfold mergeExtraDown at h2
        rcases List.mem_append.mp h2 with h123 | h4
        · rcases List.mem_append.mp h123 with h12 | h3
          · rcases List.mem_append.mp h12 with ha | hb
            · split at ha; exact (hw.roles.1 drop).1 ha; cases ha
            · split at hb; exact (hw.roles.1 drop).2.1 hb; cases hb
          · split at h3
            · obtain ⟨⟨s, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
              by_cases hc : (t == drop && s.2) = true
              · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.2 _ (s, t) hm
              · simp [hc] at hres
            · cases h3
        · split at h4
          · obtain ⟨⟨s, t⟩, hm, hres⟩ := List.mem_filterMap.mp h4
            by_cases hc : (t == b.parent keep && s.2) = true
            · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.2 drop (s, t) hm
            · simp [hc] at hres
          · cases h4
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hw.roles.1 _).2.1 h1
      · unfold mergeExtraUp at h2
        rcases List.mem_append.mp h2 with h123 | h4
        · rcases List.mem_append.mp h123 with h12 | h3
          · rcases List.mem_append.mp h12 with ha | hb
            · split at ha; exact (hw.roles.1 drop).2.1 ha; cases ha
            · split at hb; exact (hw.roles.1 drop).1 hb; cases hb
          · split at h3
            · obtain ⟨⟨s, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
              by_cases hc : (t == drop && !s.2) = true
              · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.2 _ (s, t) hm
              · simp [hc] at hres
            · cases h3
        · split at h4
          · obtain ⟨⟨s, t⟩, hm, hres⟩ := List.mem_filterMap.mp h4
            by_cases hc : (t == b.parent keep && !s.2) = true
            · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.2 drop (s, t) hm
            · simp [hc] at hres
          · cases h4
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hw.roles.1 _).2.2 h1
      · split at h2
        · rcases List.mem_append.mp h2 with ha | hb
          · exact (hw.roles.1 drop).2.2 ha
          · unfold mergeExtraLoops at hb
            rcases List.mem_append.mp hb with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · split at h1
                · obtain ⟨⟨rn, u, v⟩, hm, hres⟩ := List.mem_filterMap.mp h1
                  by_cases hc : ((u == keep && v == drop) || (u == drop && v == keep)) = true
                  · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.1 (rn, u, v) hm
                  · simp [hc] at hres
                · cases h1
              · split at h2
                · exact (List.mem_append.mp h2).elim (fun h => (hw.roles.1 drop).1 h) (fun h => (hw.roles.1 drop).2.1 h)
                · cases h2
            · split at h3
              · obtain ⟨⟨s, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
                by_cases hc : (t == keep) = true
                · simp only [hc, ↓reduceIte, Option.some.injEq] at hres; exact hres ▸ hw.roles.2.2 drop (s, t) hm
                · simp [hc] at hres
              · cases h3
        · cases h2
  · intro e he
    rcases List.mem_append.mp he with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · obtain ⟨e0, hm, hres⟩ := List.mem_filterMap.mp h1
        cases hu : mergeIdx hd hk hvalid e0.2.1 <;> cases hv : mergeIdx hd hk hvalid e0.2.2 <;>
          simp [hu, hv] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1; exact hw.roles.2.1 e0 hm
      · split at h2
        · rcases List.mem_append.mp h2 with hdn | hup
          · obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hdn; exact (hw.roles.1 drop).1 hm
          · obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hup; exact (hw.roles.1 drop).2.1 hm
        · cases h2
    · split at h3
      · obtain ⟨e0, hm, hres⟩ := List.mem_filterMap.mp h3
        cases ht : mergeIdx hd hk hvalid e0.2 <;> simp [ht] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1; cases e0.1.2 <;> exact hw.roles.2.2 drop e0 hm
      · cases h3
  · intro y e he
    rcases List.mem_append.mp he with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · obtain ⟨e0, hm, hres⟩ := List.mem_filterMap.mp h1
        cases ht : mergeIdx hd hk hvalid e0.2 <;> simp [ht] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1; exact hw.roles.2.2 _ e0 hm
      · split at h2
        · rcases List.mem_append.mp h2 with hdn | hup
          · obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hdn; exact (hw.roles.1 drop).1 hm
          · obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hup; exact (hw.roles.1 drop).2.1 hm
        · cases h2
    · split at h3
      · obtain ⟨e0, hm, hres⟩ := List.mem_filterMap.mp h3
        cases ht : mergeIdx hd hk hvalid e0.2 <;> simp [ht] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1; exact hw.roles.2.2 drop e0 hm
      · cases h3

theorem mergeForest_bindings {b : BlockedForest} {p : Problem}
    (hb : b.BindingsValid p) {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) :
    (b.mergeForest keep drop hd hk hvalid).BindingsValid p := by
  constructor
  · intro a ha
    obtain ⟨u, hu⟩ := hb.nomComplete a ha
    obtain ⟨u', hu'⟩ := mergeIdx_of_isRoot (hd := hd) (hk := hk) (hvalid := hvalid) (b.noms_valid _ hu)
    refine ⟨u', List.mem_filterMap.mpr ⟨(a, u), hu, ?_⟩⟩
    change Option.map (a, ·) (mergeIdx hd hk hvalid u) = some (a, u')
    rw [hu']; rfl
  · intro k hk'
    obtain ⟨u, hu⟩ := hb.anonComplete k hk'
    obtain ⟨u', hu'⟩ := mergeIdx_of_isRoot (hd := hd) (hk := hk) (hvalid := hvalid) (b.anons_valid _ hu)
    refine ⟨u', List.mem_filterMap.mpr ⟨(k, u), hu, ?_⟩⟩
    change Option.map (k, ·) (mergeIdx hd hk hvalid u) = some (k, u')
    rw [hu']; rfl
  · intro a r₁ r₂ h1 h2
    obtain ⟨⟨a1, u1⟩, hu1, hr1⟩ := List.mem_filterMap.mp h1
    obtain ⟨⟨a2, u2⟩, hu2, hr2⟩ := List.mem_filterMap.mp h2
    obtain ⟨x1, hx1, he1⟩ := Option.map_eq_some_iff.mp hr1
    obtain ⟨x2, hx2, he2⟩ := Option.map_eq_some_iff.mp hr2
    cases he1; cases he2
    obtain rfl := hb.nomFunctional _ u1 u2 hu1 hu2
    exact Option.some.inj (hx1.symm.trans hx2)
  · intro k r₁ r₂ h1 h2
    obtain ⟨⟨k1, u1⟩, hu1, hr1⟩ := List.mem_filterMap.mp h1
    obtain ⟨⟨k2, u2⟩, hu2, hr2⟩ := List.mem_filterMap.mp h2
    obtain ⟨x1, hx1, he1⟩ := Option.map_eq_some_iff.mp hr1
    obtain ⟨x2, hx2, he2⟩ := Option.map_eq_some_iff.mp hr2
    cases he1; cases he2
    obtain rfl := hb.anonFunctional _ u1 u2 hu1 hu2
    exact Option.some.inj (hx1.symm.trans hx2)

theorem mergeForest_geom {b : BlockedForest} {rank : Rank} {p : Problem}
    (hg : b.ForestGeom rank p) {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop)
    (hbr : b.isRoot keep = true → b.isRoot drop = false →
      b.isRoot (b.parent drop) = false → b.parent (b.parent drop) ≠ keep →
      b.depth (b.parent drop) + b.nomLevel keep ≤ sroiqMaxDepth rank p) :
    (b.mergeForest keep drop hd hk hvalid).ForestGeom rank p := by
  have nomLeIdx : ∀ z y, b.isRoot z = true → mergeIdx hd hk hvalid z = some y →
      b.nomLevel (mergeSrc y) ≤ b.nomLevel z := by
    intro z y hzr hm
    rw [mergeIdx_src hm]
    split
    · subst z
      rcases hvalid with ⟨_, hle⟩ | ⟨_, hdnf, _⟩
      · exact hle hzr
      · rw [hzr] at hdnf; cases hdnf
    · exact Nat.le_refl _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change b.nomLevel (source hd ⟨0, retained_pos hd⟩) = 0
    rw [source_zero hd]; exact hg.nomLevel0
  · intro a y hy
    obtain ⟨⟨a', u⟩, hm, hres⟩ := List.mem_filterMap.mp hy
    obtain ⟨u', hu', heq⟩ := Option.map_eq_some_iff.mp hres
    cases heq
    have hle := nomLeIdx u y (b.noms_valid _ hm) hu'
    have hz := hg.boundNomZero a u hm
    change b.nomLevel (mergeSrc y) = 0
    omega
  · intro k y hy
    obtain ⟨⟨k', u⟩, hm, hres⟩ := List.mem_filterMap.mp hy
    obtain ⟨u', hu', heq⟩ := Option.map_eq_some_iff.mp hres
    cases heq
    have hle := nomLeIdx u y (b.anons_valid _ hm) hu'
    have hz := hg.boundAnonZero k u hm
    change b.nomLevel (mergeSrc y) = 0
    omega
  · intro y; rw [mergeForest_depth]; exact hg.depthBound _
  · intro y hy; exact hg.nomLevelBound _ hy
  · intro y e he
    rw [mergeForest_depth]
    rcases List.mem_append.mp he with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · obtain ⟨⟨r, t⟩, hm, hres⟩ := List.mem_filterMap.mp h1
        cases ht : mergeIdx hd hk hvalid t <;> simp [ht] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
        have hle := nomLeIdx t _ (b.toRoot_valid _ _ hm).2.1 ht
        have htb := hg.toRootBound (mergeSrc y) (r, t) hm
        change b.depth (mergeSrc y) + b.nomLevel (mergeSrc _) ≤ sroiqMaxDepth rank p
        dsimp only at htb ⊢; omega
      · split at h2
        · rename_i h
          rcases List.mem_append.mp h2 with hdn | hup
          · obtain ⟨rn, _, rfl⟩ := List.mem_map.mp hdn
            change b.depth (prunedSrc hd y) + b.nomLevel (prunedSrc hd (prunedFrom hd (compact hd hk))) ≤ sroiqMaxDepth rank p
            rw [prunedSrc_compact, h.2.2.1]
            exact hbr h.1 h.2.1 (h.2.2.1 ▸ h.2.2.2.1) (h.2.2.1 ▸ h.2.2.2.2)
          · obtain ⟨rn, _, rfl⟩ := List.mem_map.mp hup
            change b.depth (prunedSrc hd y) + b.nomLevel (prunedSrc hd (prunedFrom hd (compact hd hk))) ≤ sroiqMaxDepth rank p
            rw [prunedSrc_compact, h.2.2.1]
            exact hbr h.1 h.2.1 (h.2.2.1 ▸ h.2.2.2.1) (h.2.2.1 ▸ h.2.2.2.2)
        · cases h2
    · split at h3
      · rename_i h
        obtain ⟨⟨r, t⟩, hm, hres⟩ := List.mem_filterMap.mp h3
        cases ht : mergeIdx hd hk hvalid t <;> simp [ht] at hres
        obtain ⟨_, h1⟩ := ite_none_some_eq_some hres; cases h1
        have hle := nomLeIdx t _ (b.toRoot_valid drop _ hm).2.1 ht
        have htb := hg.toRootBound drop (r, t) hm
        have hdk : b.depth keep ≤ b.depth drop := by
          rcases hvalid with ⟨hkr, _⟩ | ⟨_, _, hpar | hch | hgp⟩
          · rw [h.1] at hkr; cases hkr
          · have hc1 : b.Child (b.parent keep) keep := ⟨h.1, rfl⟩
            have hc2 : b.Child (b.parent drop) drop := ⟨h.2.1, rfl⟩
            rw [depth_child hc1, depth_child hc2, hpar]; exact Nat.le_refl _
          · exact Nat.le_of_lt (Anc.parent hch).depth_lt
          · have hc : b.Child (b.parent drop) drop := ⟨h.2.1, rfl⟩
            exact Nat.le_of_lt (Anc.step (.parent hgp) hc).depth_lt
        change b.depth (prunedSrc hd y) + b.nomLevel (mergeSrc _) ≤ sroiqMaxDepth rank p
        rw [h.2.2]; dsimp only at htb ⊢; omega
      · cases h3

theorem mergeForest_edge_transport {b : BlockedForest} {keep drop x y : b.Node}
    {hd : drop ≠ 0} {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    {r : OrientedRole}
    (hx : x ∈ b.retained drop)
    (hroot : b.isRoot x = true → b.isRoot y = true ∨ b.Child x y)
    (he : b.Edge r x y) :
    ∃ x' y', mergeIdx hd hk hvalid x = some x' ∧ mergeIdx hd hk hvalid y = some y' ∧
      (b.mergeForest keep drop hd hk hvalid).Edge r x' y' ∧
      ((b.mergeForest keep drop hd hk hvalid).isRoot x' = true →
        (b.mergeForest keep drop hd hk hvalid).isRoot y' = true ∨
        (b.mergeForest keep drop hd hk hvalid).Child x' y') := by
  obtain ⟨x', hx', hsx⟩ := mergeIdx_kept (hd := hd) (hk := hk) (hvalid := hvalid) hx
  have hkeepRootOfDropRoot : b.isRoot drop = true → b.isRoot keep = true := by
    intro hdr
    rcases hvalid with ⟨hkr, _⟩ | ⟨_, hdnf, _⟩
    · exact hkr
    · rw [hdr] at hdnf; cases hdnf
  have hy_cases : y ∈ b.retained drop ∨ y = drop := by
    by_cases hyd : y = drop
    · exact .inr hyd
    · refine .inl (mem_retained.mpr ⟨hyd, fun hanc => ?_⟩)
      rcases he with ⟨rfl, _⟩ | ⟨_, hyr, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | htr | htr
      · exact (mem_retained.mp hx).2 hanc
      · have hf := hanc.not_root_right; rw [hyr] at hf; cases hf
      · rcases (Anc.child_iff hc).mp hanc with rfl | ha
        · exact (mem_retained.mp hx).1 rfl
        · exact (mem_retained.mp hx).2 ha
      · exact (mem_retained.mp hx).2 (.step hanc hc)
      · have hf := hanc.not_root_right; rw [(b.toRoot_valid x _ htr).2.1] at hf; cases hf
      · rcases hroot (b.toRoot_valid y _ htr).2.1 with hyr | hcx
        · have hf := (b.toRoot_valid y _ htr).1; rw [hyr] at hf; cases hf
        · exact (b.toRoot_valid y _ htr).2.2 hcx.2
  rcases hy_cases with hy | hyd
  · obtain ⟨y', hy', hsy⟩ := mergeIdx_kept (hd := hd) (hk := hk) (hvalid := hvalid) hy
    refine ⟨x', y', hx', hy', ?_, ?_⟩
    · have hx'p : prunedIdx hd hk x = some x' := hx'
      have hy'p : prunedIdx hd hk y = some y' := hy'
      rcases he with ⟨rfl, hl⟩ | ⟨hxr, hyr, hre⟩ | ⟨hc, hdwn⟩ | ⟨hc, hdwn⟩ | htr | htr
      · obtain rfl : x' = y' := mergeSrc_inj (hsx.trans hsy.symm)
        refine .inl ⟨rfl, List.mem_append_left _ ?_⟩
        change r.1 ∈ b.loops (mergeSrc x'); rw [hsx]; exact hl
      · have hne : x' ≠ y' := by
          intro h; have := (hsx.symm.trans (congrArg mergeSrc h)).trans hsy
          rcases r with ⟨rn, _ | _⟩ <;> exact (b.rootEdges_valid _ hre).2.2 (by first | exact this | exact this.symm)
        refine .inr (.inl ⟨by change b.isRoot (mergeSrc x') = true; rw [hsx]; exact hxr,
          by change b.isRoot (mergeSrc y') = true; rw [hsy]; exact hyr, ?_⟩)
        rcases r with ⟨rn, _ | _⟩
        · exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_filterMap.mpr ⟨(rn, x, y), hre, by dsimp only; rw [hx'p, hy'p]; exact ite_eq_left hne⟩))
        · exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_filterMap.mpr ⟨(rn, y, x), hre, by dsimp only; rw [hy'p, hx'p]; exact ite_eq_left (Ne.symm hne)⟩))
      · refine .inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsx, hsy]; exact hc), ?_⟩))
        rcases r with ⟨rn, _ | _⟩
        · exact List.mem_append_left _ (by change rn ∈ b.down (mergeSrc y'); rw [hsy]; exact hdwn)
        · exact List.mem_append_left _ (by change rn ∈ b.up (mergeSrc y'); rw [hsy]; exact hdwn)
      · refine .inr (.inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsx, hsy]; exact hc), ?_⟩)))
        rcases r with ⟨rn, _ | _⟩
        · exact List.mem_append_left _ (by change rn ∈ b.up (mergeSrc x'); rw [hsx]; exact hdwn)
        · exact List.mem_append_left _ (by change rn ∈ b.down (mergeSrc x'); rw [hsx]; exact hdwn)
      · have hnp : prunedPar hd x' ≠ y' := by
          intro h
          have h1 := congrArg (prunedSrc hd) h
          have h2 : prunedSrc hd (prunedPar hd x') = b.parent x := by
            have := compactParent_source hd (y := prunedTo hd x') (by change b.isRoot (mergeSrc x') = false; rw [hsx]; exact (b.toRoot_valid x _ htr).1)
            exact this.trans (congrArg b.parent hsx)
          exact (b.toRoot_valid x _ htr).2.2 (h2.symm.trans (h1.trans hsy))
        exact .inr (.inr (.inr (.inr (.inl (List.mem_append_left _ (List.mem_append_left _
          (List.mem_filterMap.mpr ⟨(r, y), by change (r, y) ∈ b.toRoot (mergeSrc x'); rw [hsx]; exact htr,
            by dsimp only; rw [hy'p]; exact ite_eq_left hnp⟩)))))))
      · have hnp : prunedPar hd y' ≠ x' := by
          intro h
          have h1 := congrArg (prunedSrc hd) h
          have h2 : prunedSrc hd (prunedPar hd y') = b.parent y := by
            have := compactParent_source hd (y := prunedTo hd y') (by change b.isRoot (mergeSrc y') = false; rw [hsy]; exact (b.toRoot_valid y _ htr).1)
            exact this.trans (congrArg b.parent hsy)
          exact (b.toRoot_valid y _ htr).2.2 (h2.symm.trans (h1.trans hsx))
        exact .inr (.inr (.inr (.inr (.inr (List.mem_append_left _ (List.mem_append_left _
          (List.mem_filterMap.mpr ⟨(converse r, x), by change (converse r, x) ∈ b.toRoot (mergeSrc y'); rw [hsy]; exact htr,
            by dsimp only; rw [hx'p]; exact ite_eq_left hnp⟩)))))))
    · intro hxr'
      change b.isRoot (mergeSrc x') = true at hxr'
      rw [hsx] at hxr'
      rcases hroot hxr' with hyr | hc
      · exact .inl (by change b.isRoot (mergeSrc y') = true; rw [hsy]; exact hyr)
      · exact .inr (mergeForest_child_iff.mpr (by rw [hsx, hsy]; exact hc))
  · subst y
    obtain ⟨k', hk', hsk⟩ := mergeIdx_drop (hd := hd) (hk := hk) (hvalid := hvalid)
    have hx'p : prunedIdx hd hk x = some x' := hx'
    have hk'p : prunedIdx hd hk drop = some k' := hk'
    have hskp : prunedSrc hd k' = keep := hsk
    have hsxp : prunedSrc hd x' = x := hsx
    refine ⟨x', k', hx', hk', ?_, ?_⟩
    · rcases he with ⟨hxd, _⟩ | ⟨hxr, hdr, hre⟩ | ⟨hc, hdwn⟩ | ⟨hc, _⟩ | htr | htr
      · exact ((mem_retained.mp hx).1 hxd).elim
      · by_cases hxk : x = keep
        · obtain rfl : x' = k' := mergeSrc_inj (hsx.trans (hxk.trans hsk.symm))
          refine .inl ⟨rfl, List.mem_append_right _ ?_⟩
          change r.1 ∈ if prunedSrc hd x' = keep then b.loops drop ++ mergeExtraLoops b keep drop else []
          rw [hskp]; simp only [↓reduceIte]
          refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ ?_))
          simp only [hdr, ↓reduceIte]
          rcases r with ⟨rn, _ | _⟩
          · exact List.mem_filterMap.mpr ⟨(rn, keep, drop), hxk ▸ hre, by simp⟩
          · exact List.mem_filterMap.mpr ⟨(rn, drop, keep), hxk ▸ hre, by simp⟩
        · have hne : x' ≠ k' := fun h => hxk ((hsx.symm.trans (congrArg mergeSrc h)).trans hsk)
          refine .inr (.inl ⟨by change b.isRoot (mergeSrc x') = true; rw [hsx]; exact hxr,
            by change b.isRoot (mergeSrc k') = true; rw [hsk]; exact hkeepRootOfDropRoot hdr, ?_⟩)
          rcases r with ⟨rn, _ | _⟩
          · exact List.mem_append_left _ (List.mem_append_left _
              (List.mem_filterMap.mpr ⟨(rn, x, drop), hre, by dsimp only; rw [hx'p, hk'p]; exact ite_eq_left hne⟩))
          · exact List.mem_append_left _ (List.mem_append_left _
              (List.mem_filterMap.mpr ⟨(rn, drop, x), hre, by dsimp only; rw [hk'p, hx'p]; exact ite_eq_left (Ne.symm hne)⟩))
      · have hvalid' := hvalid
        rcases hvalid' with ⟨hkr, _⟩ | ⟨hknr, _, hpar | hch | hgp⟩
        · by_cases hxr : b.isRoot x = true
          · by_cases hxk : x = keep
            · obtain rfl : x' = k' := mergeSrc_inj (hsx.trans (hxk.trans hsk.symm))
              refine .inl ⟨rfl, List.mem_append_right _ ?_⟩
              change r.1 ∈ if prunedSrc hd x' = keep then b.loops drop ++ mergeExtraLoops b keep drop else []
              rw [hskp]; simp only [↓reduceIte]
              refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
              have hp : b.parent drop = keep := hc.2.trans hxk
              simp only [hc.1, hp, and_self, ↓reduceIte]
              rcases r with ⟨rn, _ | _⟩
              · exact List.mem_append_left _ hdwn
              · exact List.mem_append_right _ hdwn
            · have hne : x' ≠ k' := fun h => hxk ((hsx.symm.trans (congrArg mergeSrc h)).trans hsk)
              refine .inr (.inl ⟨by change b.isRoot (mergeSrc x') = true; rw [hsx]; exact hxr,
                by change b.isRoot (mergeSrc k') = true; rw [hsk]; exact hkr, ?_⟩)
              have hcond : b.isRoot keep = true ∧ b.isRoot drop = false ∧
                  b.isRoot (b.parent drop) = true ∧ b.parent drop ≠ keep :=
                ⟨hkr, hc.1, hc.2.symm ▸ hxr, hc.2.symm ▸ hxk⟩
              have hx_eq : x' = prunedFrom hd (compact hd (retained_of_isRoot hcond.2.2.1
                  (fun heq => by rw [heq, hcond.2.1] at hcond; exact Bool.noConfusion hcond.2.2.1))) :=
                mergeSrc_inj (by rw [hsx, ← hc.2]; exact (prunedSrc_compact hd _).symm)
              have hk_eq : k' = prunedFrom hd (compact hd hk) :=
                mergeSrc_inj (by rw [hsk]; exact (prunedSrc_compact hd hk).symm)
              rcases r with ⟨rn, _ | _⟩
              · refine List.mem_append_left _ (List.mem_append_right _ ?_)
                dsimp only; rw [dite_eq_left hcond]
                exact List.mem_append_left _ (List.mem_map.mpr ⟨rn, hdwn, by rw [hx_eq, hk_eq]; rfl⟩)
              · refine List.mem_append_left _ (List.mem_append_right _ ?_)
                dsimp only; rw [dite_eq_left hcond]
                exact List.mem_append_right _ (List.mem_map.mpr ⟨rn, hdwn, by rw [hx_eq, hk_eq]; rfl⟩)
          · have hxnr : b.isRoot x = false := Bool.eq_false_iff.mpr hxr
            by_cases hpxk : b.parent x = keep
            · have hcx : b.Child keep x := ⟨hxnr, hpxk⟩
              refine .inr (.inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsk, hsx]; exact hcx), ?_⟩)))
              have hxk : x ≠ keep := fun h => by rw [h, hkr] at hxnr; cases hxnr
              have hcond : b.isRoot drop = false ∧ x = b.parent drop ∧ x ≠ keep ∧
                  b.isRoot x = false ∧ b.parent x = keep := ⟨hc.1, hc.2.symm, hxk, hxnr, hpxk⟩
              rcases r with ⟨rn, _ | _⟩
              · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
                change rn ∈ if b.isRoot drop = false ∧ prunedSrc hd x' = b.parent drop ∧ prunedSrc hd x' ≠ keep ∧
                    b.isRoot (prunedSrc hd x') = false ∧ b.parent (prunedSrc hd x') = keep then b.down drop else []
                rw [hsxp, ite_eq_left hcond]; exact hdwn
              · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
                change rn ∈ if b.isRoot drop = false ∧ prunedSrc hd x' = b.parent drop ∧ prunedSrc hd x' ≠ keep ∧
                    b.isRoot (prunedSrc hd x') = false ∧ b.parent (prunedSrc hd x') = keep then b.up drop else []
                rw [hsxp, ite_eq_left hcond]; exact hdwn
            · have hcond : b.isRoot keep = true ∧ b.isRoot drop = false ∧ x = b.parent drop ∧
                  b.isRoot x = false ∧ b.parent x ≠ keep := ⟨hkr, hc.1, hc.2.symm, hxnr, hpxk⟩
              have hk_eq : k' = prunedFrom hd (compact hd hk) :=
                mergeSrc_inj (by rw [hsk]; exact (prunedSrc_compact hd hk).symm)
              refine .inr (.inr (.inr (.inr (.inl (List.mem_append_left _ (List.mem_append_right _ ?_))))))
              have hmem : (r, prunedFrom hd (compact hd hk)) ∈
                  (if _ : b.isRoot keep = true ∧ b.isRoot drop = false ∧ prunedSrc hd x' = b.parent drop ∧
                      b.isRoot (prunedSrc hd x') = false ∧ b.parent (prunedSrc hd x') ≠ keep then
                    let k' := prunedFrom hd (compact hd hk)
                    (b.down drop).map (fun r => ((r, false), k')) ++ (b.up drop).map (fun r => ((r, true), k'))
                  else []) := by
                rw [hsxp, dite_eq_left hcond]
                rcases r with ⟨rn, _ | _⟩
                · exact List.mem_append_left _ (List.mem_map.mpr ⟨rn, hdwn, rfl⟩)
                · exact List.mem_append_right _ (List.mem_map.mpr ⟨rn, hdwn, rfl⟩)
              rw [hk_eq]; exact hmem
        · have hck : b.Child x keep := ⟨hknr, hpar.trans hc.2⟩
          refine .inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsx, hsk]; exact hck), ?_⟩))
          have hcond : keep = keep ∧ b.isRoot keep = false ∧ b.isRoot drop = false ∧
              b.parent keep = b.parent drop := ⟨rfl, hknr, hc.1, hpar⟩
          rcases r with ⟨rn, _ | _⟩
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
            change rn ∈ if prunedSrc hd k' = keep ∧ b.isRoot keep = false ∧ b.isRoot drop = false ∧
                b.parent keep = b.parent drop then b.down drop else []
            rw [hskp, ite_eq_left hcond]; exact hdwn
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
            change rn ∈ if prunedSrc hd k' = keep ∧ b.isRoot keep = false ∧ b.isRoot drop = false ∧
                b.parent keep = b.parent drop then b.up drop else []
            rw [hskp, ite_eq_left hcond]; exact hdwn
        · have hxk : x = keep := hc.2.symm.trans hch.2
          obtain rfl : x' = k' := mergeSrc_inj (hsx.trans (hxk.trans hsk.symm))
          refine .inl ⟨rfl, List.mem_append_right _ ?_⟩
          change r.1 ∈ if prunedSrc hd x' = keep then b.loops drop ++ mergeExtraLoops b keep drop else []
          rw [hskp]; simp only [↓reduceIte]
          refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
          simp only [hc.1, hch.2, and_self, ↓reduceIte]
          rcases r with ⟨rn, _ | _⟩
          · exact List.mem_append_left _ hdwn
          · exact List.mem_append_right _ hdwn
        · have hcx : b.Child keep x := hc.2.symm ▸ hgp
          have hxk : x ≠ keep := fun h => Nat.lt_irrefl _ (h ▸ child_lt hcx)
          refine .inr (.inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsk, hsx]; exact hcx), ?_⟩)))
          have hcond : b.isRoot drop = false ∧ x = b.parent drop ∧ x ≠ keep ∧
              b.isRoot x = false ∧ b.parent x = keep := ⟨hc.1, hc.2.symm, hxk, hcx.1, hcx.2⟩
          rcases r with ⟨rn, _ | _⟩
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
            change rn ∈ if b.isRoot drop = false ∧ prunedSrc hd x' = b.parent drop ∧ prunedSrc hd x' ≠ keep ∧
                b.isRoot (prunedSrc hd x') = false ∧ b.parent (prunedSrc hd x') = keep then b.down drop else []
            rw [hsxp, ite_eq_left hcond]; exact hdwn
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
            change rn ∈ if b.isRoot drop = false ∧ prunedSrc hd x' = b.parent drop ∧ prunedSrc hd x' ≠ keep ∧
                b.isRoot (prunedSrc hd x') = false ∧ b.parent (prunedSrc hd x') = keep then b.up drop else []
            rw [hsxp, ite_eq_left hcond]; exact hdwn
      · exact ((mem_retained.mp hx).2 (.parent hc)).elim
      · have ⟨hxnr, hdr, _⟩ := b.toRoot_valid x _ htr
        have hkr : b.isRoot keep = true := hkeepRootOfDropRoot hdr
        by_cases hpxk : b.parent x = keep
        · have hcx : b.Child keep x := ⟨hxnr, hpxk⟩
          refine .inr (.inr (.inr (.inl ⟨mergeForest_child_iff.mpr (by rw [hsk, hsx]; exact hcx), ?_⟩)))
          have hcond : b.isRoot drop = true ∧ b.isRoot x = false ∧ b.parent x = keep := ⟨hdr, hxnr, hpxk⟩
          rcases r with ⟨rn, _ | _⟩
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
            change rn ∈ if b.isRoot drop = true ∧ b.isRoot (prunedSrc hd x') = false ∧
                b.parent (prunedSrc hd x') = keep then _ else []
            rw [hsxp, ite_eq_left hcond]
            exact List.mem_filterMap.mpr ⟨((rn, false), drop), htr, by simp⟩
          · refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
            change rn ∈ if b.isRoot drop = true ∧ b.isRoot (prunedSrc hd x') = false ∧
                b.parent (prunedSrc hd x') = keep then _ else []
            rw [hsxp, ite_eq_left hcond]
            exact List.mem_filterMap.mpr ⟨((rn, true), drop), htr, by simp⟩
        · have hnp : prunedPar hd x' ≠ k' := by
            intro h
            have h1 := congrArg (prunedSrc hd) h
            have h2 : prunedSrc hd (prunedPar hd x') = b.parent x := by
              have := compactParent_source hd (y := prunedTo hd x') (by change b.isRoot (mergeSrc x') = false; rw [hsx]; exact hxnr)
              exact this.trans (congrArg b.parent hsx)
            exact hpxk (h2.symm.trans (h1.trans hsk))
          exact .inr (.inr (.inr (.inr (.inl (List.mem_append_left _ (List.mem_append_left _
            (List.mem_filterMap.mpr ⟨(r, drop), by change (r, drop) ∈ b.toRoot (mergeSrc x'); rw [hsx]; exact htr,
              by dsimp only; rw [hk'p]; exact ite_eq_left hnp⟩)))))))
      · have ⟨hdnr, hxr, _⟩ := b.toRoot_valid drop _ htr
        rcases hroot hxr with hdr | hcx
        · rw [hdnr] at hdr; cases hdr
        · exact ((b.toRoot_valid drop _ htr).2.2 hcx.2).elim
    · intro hxr'
      change b.isRoot (mergeSrc x') = true at hxr'
      rw [hsx] at hxr'
      rcases hroot hxr' with hdr | hcd
      · exact .inl (by change b.isRoot (mergeSrc k') = true; rw [hsk]; exact hkeepRootOfDropRoot hdr)
      · have hvalid' := hvalid
        rcases hvalid' with ⟨hkr, _⟩ | ⟨hknr, _, hpar | hch | hgp⟩
        · exact .inl (by change b.isRoot (mergeSrc k') = true; rw [hsk]; exact hkr)
        · exact .inr (mergeForest_child_iff.mpr (by rw [hsx, hsk]; exact ⟨hknr, hpar.trans hcd.2⟩))
        · exfalso
          have hf := hch.2.symm.trans hcd.2; rw [hf, hxr'] at hknr; cases hknr
        · exfalso
          have hpx : b.parent drop = x := hcd.2
          rw [hpx] at hgp
          have hf := hgp.1; rw [hxr'] at hf; cases hf

theorem mergeForest_aboxSeeded {b : BlockedForest} {p : Problem}
    (ha : b.ABoxSeeded p) {keep drop : b.Node} (hd : drop ≠ 0)
    (hk : keep ∈ b.retained drop) (hvalid : b.MergeValid keep drop) :
    (b.mergeForest keep drop hd hk hvalid).ABoxSeeded p := by
  have boundSrc (ind : Individual) (y : (b.mergeForest keep drop hd hk hvalid).Node)
      (h : (b.mergeForest keep drop hd hk hvalid).BoundTo ind y) :
      ∃ u, b.BoundTo ind u ∧ mergeIdx hd hk hvalid u = some y := by
    cases ind with
    | named a =>
      obtain ⟨⟨a', u⟩, hm, hres⟩ := List.mem_filterMap.mp h
      obtain ⟨u', hu', heq⟩ := Option.map_eq_some_iff.mp hres
      cases heq
      exact ⟨u, hm, hu'⟩
    | anonymous d l =>
      obtain ⟨⟨k', u⟩, hm, hres⟩ := List.mem_filterMap.mp h
      obtain ⟨u', hu', heq⟩ := Option.map_eq_some_iff.mp hres
      cases heq
      exact ⟨u, hm, hu'⟩
  have labelFromIdx (u : b.Node) (y : (b.mergeForest keep drop hd hk hvalid).Node)
      (hm : mergeIdx hd hk hvalid u = some y) (c : Concept) (hc : c ∈ b.labels u) :
      c ∈ (b.mergeForest keep drop hd hk hvalid).labels y := by
    have hs := mergeIdx_src hm
    by_cases hud : u = drop
    · subst hud
      refine List.mem_append_right _ ?_
      change c ∈ if mergeSrc y = keep then b.labels u else []
      simp [hs, hc]
    · refine List.mem_append_left _ ?_
      change c ∈ b.labels (mergeSrc y)
      simp [hs, hud, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.mem_append_left _ ?_
    change p.root ∈ b.labels (source hd ⟨0, retained_pos hd⟩)
    rw [source_zero hd]; exact ha.root
  · intro ac hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc ac.1 y hy
    exact labelFromIdx u y hm' ac.2 (ha.classAssertions ac hm u hu)
  · intro rab hm y₁ y₂ h1 h2
    obtain ⟨u₁, hu1, hm1⟩ := boundSrc rab.2.1 y₁ h1
    obtain ⟨u₂, hu2, hm2⟩ := boundSrc rab.2.2 y₂ h2
    have hedge := ha.objAssertions rab hm u₁ u₂ hu1 hu2
    by_cases hu1d : u₁ = drop
    · subst u₁
      have hne : u₂ = drop ∨ u₂ ∈ b.retained drop := by
        by_cases h2d : u₂ = drop
        · exact .inl h2d
        · exact .inr (retained_of_isRoot hu2.isRoot h2d)
      rcases hne with h2d | hu2r
      · subst u₂
        have hy : y₁ = y₂ := Option.some.inj (hm1.symm.trans hm2)
        subst hy
        have hl : rab.1 ∈ b.loops drop := (edge_loop_iff b (rab.1, false) drop).mp hedge
        refine .inl ⟨rfl, List.mem_append_right _ ?_⟩
        change rab.1 ∈ if mergeSrc y₁ = keep then b.loops drop ++ mergeExtraLoops b keep drop else []
        have hs1 := mergeIdx_src hm1; simp at hs1
        simp [hs1, hl]
      · have hedge' := (b.edge_converse (rab.1, false) drop u₂).mpr hedge
        obtain ⟨x', z', hx', hz', he', _⟩ := mergeForest_edge_transport (hd := hd) (hk := hk)
          (hvalid := hvalid) hu2r (fun _ => .inl hu1.isRoot) hedge'
        have ex : x' = y₂ := Option.some.inj (hx'.symm.trans hm2)
        have ez : z' = y₁ := Option.some.inj (hz'.symm.trans hm1)
        subst x'; subst z'
        exact ((b.mergeForest keep drop hd hk hvalid).edge_converse (rab.1, false) y₁ y₂).mp he'
    · have hu1r := retained_of_isRoot hu1.isRoot hu1d
      obtain ⟨x', z', hx', hz', he', _⟩ := mergeForest_edge_transport (hd := hd) (hk := hk)
        (hvalid := hvalid) hu1r (fun _ => .inl hu2.isRoot) hedge
      have ex : x' = y₁ := Option.some.inj (hx'.symm.trans hm1)
      have ez : z' = y₂ := Option.some.inj (hz'.symm.trans hm2)
      subst ex; subst ez; exact he'
  · intro rab hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc rab.2.1 y hy
    exact labelFromIdx u y hm' _ (ha.negObjAssertions rab hm u hu)
  · intro ab hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc ab.1 y hy
    exact labelFromIdx u y hm' _ (ha.sameInds ab hm u hu)
  · intro ab hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc ab.1 y hy
    exact labelFromIdx u y hm' _ (ha.diffInds ab hm u hu)
  · intro dal hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc dal.2.1 y hy
    exact labelFromIdx u y hm' _ (ha.dataAssertions dal hm u hu)
  · intro dal hm y hy
    obtain ⟨u, hu, hm'⟩ := boundSrc dal.2.1 y hy
    exact labelFromIdx u y hm' _ (ha.negDataAssertions dal hm u hu)

theorem mergeForest_protected {b : BlockedForest} {keep drop : b.Node} {hd : drop ≠ 0}
    {hk : keep ∈ b.retained drop} {hvalid : b.MergeValid keep drop}
    (allowed : ¬ b.RecordedDistinct keep drop)
    {y : (b.mergeForest keep drop hd hk hvalid).Node} {r : OrientedRole} {c : Concept} {n : Nat}
    (hp : b.ProtectedWitnesses (mergeSrc y) r c n) :
    (b.mergeForest keep drop hd hk hvalid).ProtectedWitnesses y r c n := by
  obtain ⟨ys, hlen, hnd, hdist, hspec⟩ := hp
  have hx : mergeSrc y ∈ b.retained drop := mergeSrc_mem y
  have hy_idx : mergeIdx hd hk hvalid (mergeSrc y) = some y := by
    obtain ⟨y', hy', hsy'⟩ := mergeIdx_kept (hd := hd) (hk := hk) (hvalid := hvalid) hx
    have : y' = y := mergeSrc_inj hsy'
    exact this ▸ hy'
  let f (w : b.Node) : (b.mergeForest keep drop hd hk hvalid).Node :=
    (mergeIdx hd hk hvalid w).getD 0
  have hlift (w : b.Node) (hw : w ∈ ys) :
      mergeIdx hd hk hvalid w = some (f w) ∧
      ((b.mergeForest keep drop hd hk hvalid).isRoot y = true →
        (b.mergeForest keep drop hd hk hvalid).isRoot (f w) = true ∨
        (b.mergeForest keep drop hd hk hvalid).Child y (f w)) ∧
      (b.mergeForest keep drop hd hk hvalid).Edge r y (f w) ∧
      c ∈ (b.mergeForest keep drop hd hk hvalid).labels (f w) := by
    have ⟨hroot, hedge, hlab⟩ := hspec w hw
    obtain ⟨x', w', hx', hw', he', hrt'⟩ := mergeForest_edge_transport (hd := hd) (hk := hk)
      (hvalid := hvalid) hx hroot hedge
    have ex : x' = y := Option.some.inj (hx'.symm.trans hy_idx)
    subst ex
    have ef : f w = w' := by simp [f, hw']
    rw [ef]
    refine ⟨hw', hrt', he', ?_⟩
    have hs := mergeIdx_src hw'
    by_cases hwd : w = drop
    · subst hwd; refine List.mem_append_right _ ?_
      change c ∈ if mergeSrc w' = keep then b.labels w else []
      simp [hs, hlab]
    · refine List.mem_append_left _ ?_
      change c ∈ b.labels (mergeSrc w')
      simp [hs, hwd, hlab]
  have hsep (u v : b.Node) (hu : u ∈ ys) (hv : v ∈ ys) (hne : u ≠ v) (hrec : b.RecordedDistinct u v) :
      f u ≠ f v ∧ (b.mergeForest keep drop hd hk hvalid).RecordedDistinct (f u) (f v) := by
    have hmu := (hlift u hu).1
    have hmv := (hlift v hv).1
    constructor
    · intro heq
      have hsrc := (mergeIdx_src hmu).symm.trans ((congrArg mergeSrc heq).trans (mergeIdx_src hmv))
      by_cases hud : u = drop <;> by_cases hvd : v = drop
      · exact hne (hud.trans hvd.symm)
      · have : keep = v := by simpa [hud, hvd] using hsrc
        exact allowed (this.symm ▸ hud ▸ hrec.symm)
      · have : u = keep := by simpa [hud, hvd] using hsrc
        exact allowed (this ▸ hvd ▸ hrec)
      · exact hne (by simpa [hud, hvd] using hsrc)
    · have hmup : prunedIdx hd hk u = some (f u) := hmu
      have hmvp : prunedIdx hd hk v = some (f v) := hmv
      rcases hrec with h | h
      · exact .inl (List.mem_filterMap.mpr ⟨(u, v), h, by dsimp only; rw [hmup, hmvp]; rfl⟩)
      · exact .inr (List.mem_filterMap.mpr ⟨(v, u), h, by dsimp only; rw [hmvp, hmup]; rfl⟩)
  refine ⟨ys.map f, by simp [hlen], ?_, ?_, ?_⟩
  · exact List.pairwise_map.mpr ((hnd.and hdist).imp_of_mem fun ha hb h => (hsep _ _ ha hb h.1 h.2).1)
  · exact List.pairwise_map.mpr ((hnd.and hdist).imp_of_mem fun ha hb h => (hsep _ _ ha hb h.1 h.2).2)
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact (hlift w hw).2

/-! ### Maximal finite witness extraction for the NN-rule -/

/-- If a predicate `P` holds for at least `1` element and NOT for `n + 1`
elements, then there exists an exact maximal finite witness list `ws` of
length `m` with `1 ≤ m ≤ n` covering every element satisfying `P`. -/
theorem exists_maximal_witnesses {α : Type} {P : α → Prop} {n : Nat}
    (h1 : AtLeast 1 P) (hmax : ¬ AtLeast (n + 1) P) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ ∃ ws : List α, ws.length = m ∧ ws.Nodup ∧
      (∀ w ∈ ws, P w) ∧ (∀ z, P z → z ∈ ws) := by
  classical
  have aux : ∀ d k, n - k = d → k ≤ n → AtLeast k P →
      ∃ m, k ≤ m ∧ m ≤ n ∧ ∃ ws : List α, ws.length = m ∧ ws.Nodup ∧
        (∀ w ∈ ws, P w) ∧ (∀ z, P z → z ∈ ws) := by
    intro d
    induction d with
    | zero =>
      intro k hd hk hAt
      have hkn : k = n := by omega
      subst hkn
      obtain ⟨ws, hlen, hnd, hsp⟩ := hAt
      refine ⟨k, Nat.le_refl k, Nat.le_refl k, ws, hlen, hnd, hsp, fun z hz => ?_⟩
      apply Classical.byContradiction
      intro hnot
      exact hmax ⟨z :: ws, by simp [hlen], List.nodup_cons.mpr ⟨hnot, hnd⟩, by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hz
        · exact hsp y hy'⟩
    | succ d ih =>
      intro k hd hk hAt
      by_cases hex : AtLeast (k + 1) P
      · obtain ⟨m, hm1, hm2, ws, hlen, hnd, hsp, hcov⟩ := ih (k + 1) (by omega) (by omega) hex
        exact ⟨m, by omega, hm2, ws, hlen, hnd, hsp, hcov⟩
      · obtain ⟨ws, hlen, hnd, hsp⟩ := hAt
        refine ⟨k, Nat.le_refl k, hk, ws, hlen, hnd, hsp, fun z hz => ?_⟩
        apply Classical.byContradiction
        intro hnot
        exact hex ⟨z :: ws, by simp [hlen], List.nodup_cons.mpr ⟨hnot, hnd⟩, by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hz
          · exact hsp y hy'⟩
  by_cases hn0 : n = 0
  · subst hn0; exact (hmax h1).elim
  · exact aux (n - 1) 1 rfl (by omega) h1

#print axioms initial_sat_iff
#print axioms addEdge_realizes
#print axioms appendChildren_realizes
#print axioms appendNNRoots_realizes
#print axioms mergeForest_realizes
#print axioms mergeForest_protected
#print axioms exists_maximal_witnesses

end BlockedForest
end Termination
end Sabrina.OWL2.SROIQD
