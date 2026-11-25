import Sabrina.Graded.Steps

namespace Sabrina.Graded

open ALC RoleChains

private def toModel (s : Branch) : NominalGraph :=
  let nodes := s.nodes
  let additional := nodes.length - 1
  let index := fun a =>
    let n := nodes.idxOf a
    if h : n < additional + 1 then some (⟨n,h⟩ : Fin (additional + 1)) else none
  let g : Graph :=
    ⟨additional,
     s.labels.filterMap fun
      | (n,.lit c true) => (index n).map (c, ·)
      | _ => none,
     s.edges.filterMap fun (r,a,b) => do
      return (r,← index a,← index b)⟩
  ⟨g, s.noms.filterMap fun (a, n) => (index n).map (a, ·)⟩

private def nodeLabels (s : Branch) (x : Nat) : List Concept :=
  (s.labels.filterMap fun (n, c) => if n == x then some c else none).eraseDups

private def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private def pairEdgeRoles (s : Branch) (x y : Nat) : List String :=
  (s.edges.filterMap fun (r, a, b) => if a == x && b == y then some r else none).eraseDups

private def isNominalNode (s : Branch) (x : Nat) : Bool :=
  s.noms.any fun (_, n) => n == x

private def pairwiseBlocker (s : Branch) (y : Nat) : Option Nat := Id.run do
  if isNominalNode s y then return none
  let ly := nodeLabels s y
  let parents := (s.edges.filterMap fun (_, x, b) => if b == y && x < y then some x else none).eraseDups
  for x in parents do
    let lx := nodeLabels s x
    let fwd := pairEdgeRoles s x y
    let bwd := pairEdgeRoles s y x
    for y' in s.nodes do
      if y' >= y || isNominalNode s y' then continue
      if !sameSet ly (nodeLabels s y') then continue
      let parents' := (s.edges.filterMap fun (_, x', b') => if b' == y' && x' < y' then some x' else none).eraseDups
      for x' in parents' do
        if sameSet lx (nodeLabels s x') &&
           sameSet fwd (pairEdgeRoles s x' y') &&
           sameSet bwd (pairEdgeRoles s y' x') then
          return some y'
  return none

private def subsetBlocker (s : Branch) (y : Nat) : Option Nat := Id.run do
  if isNominalNode s y then return none
  let ly := nodeLabels s y
  for y' in s.nodes do
    if y' >= y || isNominalNode s y' then continue
    let ly' := nodeLabels s y'
    if ly.all (ly'.contains ·) then return some y'
  return none

private def buildQuotientModel (s : Branch) (redirects : List (Nat × Nat)) : Option NominalGraph :=
  if redirects.isEmpty then none
  else
    let remap (n : Nat) : Nat := (redirects.lookup n).getD n
    let kept := s.nodes.filter fun n => (redirects.lookup n).isNone
    if kept.isEmpty then none
    else
      let additional := kept.length - 1
      let index := fun a =>
        let n := kept.idxOf (remap a)
        if h : n < additional + 1 then some (⟨n, h⟩ : Fin (additional + 1)) else none
      let g : Graph :=
        ⟨additional,
         (s.labels.filterMap fun
          | (n, .lit c true) => if (redirects.lookup n).isNone then (index n).map (c, ·) else none
          | _ => none).eraseDups,
         (s.edges.filterMap fun (r, a, b) => do
            return (r, ← index (remap a), ← index (remap b))).eraseDups⟩
      some ⟨g, (s.noms.filterMap fun (a, n) => (index (remap n)).map (a, ·)).eraseDups⟩

private def toBlockedModels (s : Branch) : List NominalGraph :=
  let pairRedirs := s.nodes.filterMap fun y => (pairwiseBlocker s y).map (y, ·)
  let leafRedirs := s.nodes.filterMap fun y =>
    if s.edges.any (fun (_, a, b) => a == y && b > y) then none
    else (subsetBlocker s y).map (y, ·)
  ([buildQuotientModel s pairRedirs, buildQuotientModel s leafRedirs]).filterMap id

structure Limits where
  worlds : Nat := 16
  depth : Nat := 256
  visits : Nat := 20000

inductive Evidence where
  | model (model : NominalGraph)
  | refutation (depth : Nat)

def Evidence.isModel : Evidence → Bool
  | .model _ => true
  | .refutation _ => false

/-- Reconstruct all the local steps in the refutation. At depth zero the
    checker has no refutation, even if search failed to find a model. -/
def checkClosed (p : Problem) (maxNodes : Nat) : Nat → Branch → Bool
  | 0, _ => false
  | depth + 1, s =>
    match next p s maxNodes with
    | none => false
    | some t => t.branches.all (checkClosed p maxNodes depth)

theorem checkClosed_sound {p : Problem} {maxNodes depth : Nat} {s : Branch}
    (h : checkClosed p maxNodes depth s = true) : ¬ s.Sat p := by
  induction depth generalizing s with
  | zero => cases h
  | succ n ih =>
    intro hs
    simp only [checkClosed] at h
    split at h
    · contradiction
    · rename_i t _
      obtain ⟨u,hu,hmodel⟩ := t.preserves hs
      exact ih (List.all_eq_true.mp h u hu) hmodel

def checkEvidence (p : Problem) (maxNodes : Nat) : Evidence → Bool
  | .model g => checkModel p g
  | .refutation d => checkClosed p maxNodes d (initial p)

def evidenceClaim (p : Problem) (e : Evidence) : Prop :=
  if e.isModel then p.Sat else ¬ p.Sat

theorem checkEvidence_sound {p : Problem} {maxNodes : Nat} {e : Evidence}
    (h : checkEvidence p maxNodes e = true) : evidenceClaim p e := by
  cases e with
  | model g => exact checkModel_sound h
  | refutation depth => exact fun hs => checkClosed_sound h (initial_sat hs)

private def combine (a b : Option Evidence) : Option Evidence :=
  match a,b with
  | some (.model g), _ | _, some (.model g) => some (.model g)
  | some (.refutation d), some (.refutation e) => some (.refutation (max d e))
  | _, _ => none

private def probe (p : Problem) (maxNodes : Nat) :
    Nat → Nat → Branch → Option Evidence × Nat
  | 0, fuel, _ => (none,fuel)
  | _ + 1, 0, _ => (none,0)
  | depth + 1, fuel + 1, s => Id.run do
    if s.nodes.length > maxNodes then return (none,fuel)
    let g := toModel s
    if checkModel p g then return (some (.model g),fuel)
    for bg in toBlockedModels s do
      if checkModel p bg then return (some (.model bg),fuel)
    let some t := next p s maxNodes | return (none,fuel)
    let mut rest := fuel
    let mut result : Option Evidence := some (.refutation 0)
    for branch in t.branches do
      let (sub,remaining) := probe p maxNodes depth rest branch
      if let some (.model g) := sub then return (some (.model g),remaining)
      rest := remaining
      result := combine result sub
    return (result.map fun
      | .refutation d => .refutation (d + 1)
      | .model g => .model g,rest)

/-- Bounded proof/model proposal. All successful results are subsequently
    checked against the problem rather than relying on this search. -/
def propose (p : Problem) (limits : Limits) : Option Evidence :=
  (probe p limits.worlds limits.depth limits.visits (initial p)).1

structure InclusionEvidence where
  counterexample : Evidence
  inclusion : Evidence

def InclusionEvidence.verdict (e : InclusionEvidence) : InclusionVerdict :=
  match e.counterexample.isModel,e.inclusion.isModel with
  | false,true => .entailed
  | true,false => .refuted
  | true,true => .independent
  | false,false => .inconsistent

def counterProblem (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (q : Inclusion)
    (chars : RoleChars := {}) : Problem := ⟨rules,chains,tbox,.conj q.sub q.sup.dual,chars⟩

def inclusionProblem (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (q : Inclusion)
    (chars : RoleChars := {}) : Problem := ⟨rules,chains,q :: tbox,.top,chars⟩

def checkInclusion (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (q : Inclusion)
    (maxNodes : Nat) (e : InclusionEvidence) (chars : RoleChars := {}) : Bool :=
  checkSimple rules chains tbox q chars &&
  checkEvidence (counterProblem rules chains tbox q chars) maxNodes e.counterexample &&
  checkEvidence (inclusionProblem rules chains tbox q chars) maxNodes e.inclusion

def verdictClaim (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (q : Inclusion)
    (chars : RoleChars := {}) : InclusionVerdict → Prop
  | .entailed => ¬ (counterProblem rules chains tbox q chars).Sat ∧ ConceptSat rules chains tbox .top chars
  | .refuted => ¬ (inclusionProblem rules chains tbox q chars).Sat ∧ ConceptSat rules chains tbox .top chars
  | .independent => (counterProblem rules chains tbox q chars).Sat ∧ (inclusionProblem rules chains tbox q chars).Sat
  | .inconsistent => ¬ ConceptSat rules chains tbox .top chars

theorem checkInclusion_sound {rules chains tbox q maxNodes e chars}
    (h : checkInclusion rules chains tbox q maxNodes e chars = true) :
    ((∀ r ∈ countedRoles tbox q, SimpleRoles.Simple rules chains (r,false)) ∧
     (∀ r ∈ chars.simpleRoles, SimpleRoles.Simple rules chains r)) ∧
      verdictClaim rules chains tbox q chars e.verdict := by
  rcases e with ⟨a,b⟩
  simp only [checkInclusion,Bool.and_eq_true] at h
  refine ⟨checkSimple_iff.mp h.1.1,?_⟩
  have ha := checkEvidence_sound h.1.2
  have hb := checkEvidence_sound h.2
  cases he : a.isModel <;> cases hf : b.isModel <;>
    simp only [evidenceClaim,he,hf,Bool.false_eq_true,↓reduceIte] at ha hb <;>
    simp only [InclusionEvidence.verdict,he,hf,verdictClaim]
  · intro ht
    obtain ⟨i,nom,hr,hc,hrc,hm,x,_⟩ := ht
    apply hb
    refine ⟨i,nom,hr,hc,hrc,?_,x,trivial⟩
    intro ax hax y hy
    rcases List.mem_cons.mp hax with heq | hax
    · subst ax
      apply Classical.byContradiction
      intro hneg
      exact ha ⟨i,nom,hr,hc,hrc,hm,y,hy,(holds_dual i nom y q.sup).mpr hneg⟩
    · exact hm ax hax y hy
  · obtain ⟨i,nom,hr,hc,hrc,hm,x,_⟩ := hb
    exact ⟨ha,⟨i,nom,hr,hc,hrc,fun ax hax => hm ax (List.mem_cons_of_mem _ hax),x,trivial⟩⟩
  · obtain ⟨i,nom,hr,hc,hrc,hm,x,_⟩ := ha
    exact ⟨hb,⟨i,nom,hr,hc,hrc,hm,x,trivial⟩⟩
  · exact ⟨ha,hb⟩

end Sabrina.Graded
