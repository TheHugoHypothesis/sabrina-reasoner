import Sabrina.RoleChains.RankedSearch

namespace Sabrina.RoleChains

open Sabrina.ALC

private def Graph.closeRound (g : Graph) (rules : RoleTheory) (chains : List Chain) : Graph :=
  let fromInclusions := rules.flatMap fun (r,s) =>
    g.worlds.flatMap fun x =>
      g.worlds.filterMap fun y =>
        if g.oriented r x y then some (if s.2 then (s.1,y,x) else (s.1,x,y)) else none
  let fromChains := chains.flatMap fun c =>
    g.worlds.flatMap fun x =>
      g.worlds.filterMap fun y =>
        if g.path c.body x y then some (c.head,x,y) else none
  { g with edges := (g.edges ++ fromInclusions ++ fromChains).eraseDups }

private def Graph.saturate (rules : RoleTheory) (chains : List Chain) (g : Graph) : Nat → Graph
  | 0 => g
  | fuel + 1 =>
    let next := g.closeRound rules chains
    if next.edges == g.edges then g else next.saturate rules chains fuel

private def graphFromRows (rules : RoleTheory) (chains : List Chain) (cs : List Concept)
    (row : Row) (rest : List Row) : Graph := Id.run do
  let empty : Graph := ⟨rest.length, [], []⟩
  let rows := (row :: rest).toArray
  let atWorld := fun (x : empty.World) => rows[x.val]!
  let atoms := cs.filterMap fun
    | .atom p => some p
    | _ => none
  let roles := ((cs.filterMap fun
    | .some r _ => some r
    | _ => none) ++ rules.flatMap (fun (r,s) => [r.1,s.1]) ++
      chains.flatMap (fun c => c.head :: c.bodyNames)).eraseDups
  let admissible := admitsUnder cs rules
  let seed := { empty with
    atoms := empty.worlds.flatMap fun x =>
      atoms.filterMap fun p => if (atWorld x).contains (.atom p) then some (p,x) else none
    edges := roles.flatMap fun r =>
      empty.worlds.flatMap fun x =>
        empty.worlds.filterMap fun y =>
          if admissible r (atWorld x) (atWorld y) then some (r,x,y) else none }
  if TransitivePaths.onlyTransitive chains then
    return TransitivePaths.completeGraph seed rules (chains.map Chain.head) roles
  else
    let n := seed.additionalWorlds + 1
    return seed.saturate rules chains (roles.length * n * n)

inductive Evidence where
  | graph (model : Graph)
  | refutation (rounds : Nat)
  | guarded (certificate : Certificate)
  | ranked (certificate : Certificate)

def Evidence.isModel : Evidence → Bool
  | .graph _ | .guarded (.model _) | .ranked (.model _) => true
  | .refutation _ | .guarded (.refutation _) | .ranked (.refutation _) => false

def checkEvidence (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) : Evidence → Bool
  | .graph g => checkGraph rules chains tbox root g
  | .refutation rounds => checkRefutationUnder rules (augment rules chains tbox root) root rounds
  | .guarded cert => TransitivePaths.onlyTransitive chains &&
      TransitivePaths.check rules (chains.map Chain.head) tbox root cert
  | .ranked cert =>
      let rank := inferRank rules chains
      checkRegular rank rules chains && RankedPaths.check rank rules chains tbox root cert

def evidenceClaim (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) (e : Evidence) : Prop :=
  if e.isModel then ConceptSat rules chains tbox root else ¬ ConceptSat rules chains tbox root

theorem checkEvidence_sound {rules chains tbox root e}
    (h : checkEvidence rules chains tbox root e = true) : evidenceClaim rules chains tbox root e := by
  cases e with
  | graph _ => exact checkGraph_sound h
  | refutation _ => exact checkRefutation_sound h
  | guarded cert =>
    simp only [checkEvidence, Bool.and_eq_true] at h
    have hs := TransitivePaths.check_sound h.2
    have he := TransitivePaths.chainSat_iff (rules := rules) (tbox := tbox) (root := root) h.1
    cases cert with
    | model _ => exact he.mpr hs
    | refutation _ => exact fun hc => hs (he.mp hc)
  | ranked cert =>
    simp only [checkEvidence, Bool.and_eq_true] at h
    have hs := RankedPaths.check_sound (checkRegular_sound h.1) h.2
    cases cert <;> exact hs

/-- Model generation is bounded. The verifier always checks the original constraints. -/
def propose (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) (maxWorlds : Nat) : Option Evidence := do
  let augmented := augment rules chains tbox root
  match searchUnder rules augmented root with
  | .refutation rounds => return .refutation rounds
  | .model pool =>
    if maxWorlds == 0 then none else
    let empty : Graph := ⟨0, [], []⟩
    if checkGraph rules chains tbox root empty then return .graph empty
    let row ← pool.find? (·.contains root)
    let rest := pool.erase row
    let limits := ([1, 2, 4, 8, 16].filter (· ≤ maxWorlds) ++ [maxWorlds]).eraseDups
    let graph ← limits.findSome? fun limit =>
      let candidate := graphFromRows rules chains (closure augmented root) row (rest.take (limit - 1))
      if checkGraph rules chains tbox root candidate then some candidate else none
    return .graph graph

/-- Prefer compact evidence and fall back to the appropriate complete guard
    translation when the compiled closure fits the interactive limit. -/
def proposeWithin (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) (maxWorlds maxConcepts : Nat) : Option Evidence := do
  if (closure (augment rules chains tbox root) root).length ≤ maxConcepts then
    if let some evidence := propose rules chains tbox root maxWorlds then
      return evidence
  if TransitivePaths.onlyTransitive chains then
    let p := TransitivePaths.prepare rules (chains.map Chain.head) tbox root
    if (closure p.tbox p.root).length ≤ maxConcepts then
      return .guarded (searchUnder p.rules p.tbox p.root)
  let rank := inferRank rules chains
  if !checkRegular rank rules chains then none else
    let p := RankedPaths.prepare rank rules chains tbox root
    if (closure p.tbox p.root).length ≤ maxConcepts then
      some (.ranked (searchUnder p.rules p.tbox p.root))
    else none

structure InclusionEvidence where
  counterexample : Evidence
  inclusion : Evidence

def InclusionEvidence.verdict (e : InclusionEvidence) : InclusionVerdict :=
  match e.counterexample.isModel, e.inclusion.isModel with
  | false, true => .entailed
  | true, false => .refuted
  | true, true => .independent
  | false, false => .inconsistent

def counterRoot (q : Inclusion) : Concept := .conj q.sub (.neg q.sup)

def checkInclusion (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (q : Inclusion) (e : InclusionEvidence) : Bool :=
  checkEvidence rules chains tbox (counterRoot q) e.counterexample &&
  checkEvidence rules chains (q :: tbox) .top e.inclusion

def verdictClaim (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (q : Inclusion) : InclusionVerdict → Prop
  | .entailed => ¬ ConceptSat rules chains tbox (counterRoot q) ∧ ConceptSat rules chains tbox .top
  | .refuted => ¬ ConceptSat rules chains (q :: tbox) .top ∧ ConceptSat rules chains tbox .top
  | .independent => ConceptSat rules chains tbox (counterRoot q) ∧ ConceptSat rules chains (q :: tbox) .top
  | .inconsistent => ¬ ConceptSat rules chains tbox .top

private theorem consistent_of_sat {rules chains tbox root} :
    ConceptSat rules chains tbox root → ConceptSat rules chains tbox .top := by
  rintro ⟨i, hr, hc, hm, x, _⟩
  exact ⟨i, hr, hc, hm, x, trivial⟩

/-- Each result is scoped to the original axioms and both sides of the query. -/
theorem checkInclusion_sound {rules chains tbox q e}
    (h : checkInclusion rules chains tbox q e = true) : verdictClaim rules chains tbox q e.verdict := by
  rcases e with ⟨counter, inclusion⟩
  simp only [checkInclusion, Bool.and_eq_true] at h
  have hc := checkEvidence_sound h.1
  have hi := checkEvidence_sound h.2
  cases h₁ : counter.isModel <;> cases h₂ : inclusion.isModel <;>
    simp only [evidenceClaim, h₁, h₂, Bool.false_eq_true, ↓reduceIte] at hc hi <;>
    simp only [InclusionEvidence.verdict, h₁, h₂, verdictClaim]
  case false.false =>
    rintro ⟨i, hr, hs, hm, x, hx⟩
    have hq : ∀ y, holds i y q.sub → holds i y q.sup := by
      classical
      intro y hsub
      exact Classical.byContradiction fun hn => hc ⟨i, hr, hs, hm, y, hsub, hn⟩
    exact hi ⟨i, hr, hs, (models_cons i q tbox).mpr ⟨hq, hm⟩, x, hx⟩
  case false.true =>
    obtain ⟨i, hr, hs, hm, x, hx⟩ := hi
    exact ⟨hc, ⟨i, hr, hs, ((models_cons i q tbox).mp hm).2, x, hx⟩⟩
  case true.false => exact ⟨hi, consistent_of_sat hc⟩
  case true.true => exact ⟨hc, hi⟩

def searchTransitiveInclusion (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (q : Inclusion) : InclusionEvidence :=
  let ts := chains.map Chain.head
  ⟨.guarded (TransitivePaths.search rules ts tbox (counterRoot q)),
    .guarded (TransitivePaths.search rules ts (q :: tbox) .top)⟩

theorem searchTransitiveInclusion_checked (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (q : Inclusion) (h : TransitivePaths.onlyTransitive chains = true) :
    checkInclusion rules chains tbox q (searchTransitiveInclusion rules chains tbox q) = true := by
  simp [searchTransitiveInclusion, checkInclusion, checkEvidence, h, TransitivePaths.search_checked]

theorem searchTransitiveInclusion_correct (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (q : Inclusion) (h : TransitivePaths.onlyTransitive chains = true) :
    verdictClaim rules chains tbox q (searchTransitiveInclusion rules chains tbox q).verdict :=
  checkInclusion_sound (searchTransitiveInclusion_checked rules chains tbox q h)

/-- Complete two-sided search for inputs with a validated inferred rank.
    The interactive entry point separately bounds formula enumeration. -/
def searchRankedInclusion (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (q : Inclusion) : InclusionEvidence :=
  let rank := inferRank rules chains
  ⟨.ranked (RankedPaths.search rank rules chains tbox (counterRoot q)),
    .ranked (RankedPaths.search rank rules chains (q :: tbox) .top)⟩

theorem searchRankedInclusion_checked (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (q : Inclusion) (h : checkRegular (inferRank rules chains) rules chains = true) :
    checkInclusion rules chains tbox q (searchRankedInclusion rules chains tbox q) = true := by
  simp [searchRankedInclusion, checkInclusion, checkEvidence, h, RankedPaths.search_checked]

theorem searchRankedInclusion_correct (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (q : Inclusion) (h : checkRegular (inferRank rules chains) rules chains = true) :
    verdictClaim rules chains tbox q (searchRankedInclusion rules chains tbox q).verdict :=
  checkInclusion_sound (searchRankedInclusion_checked rules chains tbox q h)

end Sabrina.RoleChains
