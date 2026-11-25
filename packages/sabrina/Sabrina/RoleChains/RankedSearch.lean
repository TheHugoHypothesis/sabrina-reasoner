import Sabrina.RoleChains.RankedCompletion
import Sabrina.RoleChains.TransitiveSearch

namespace Sabrina.RoleChains.RankedPaths

open Sabrina.ALC
open TransitivePaths (WordPath atomName flagName roleName readRole read_roleName encode
  encodeInclusion project holds_encode signedName project_signed Problem)

private structure Automaton where
  target : String
  filler : Concept
  initial : PathRegex

private structure State where
  filler : Concept
  residual : PathRegex
  deriving DecidableEq

private def state (g : Automaton) (p : PathRegex) : State := ⟨g.filler, p.simplify⟩

private def automata (rank : Rank) (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (root : Concept) : List Automaton :=
  (closure tbox root).filterMap fun
    | .some r c => some ⟨r,c,(compile rank rules (normalize chains) (r,false)).simplify⟩
    | _ => none

private theorem mem_automata {rank rules chains tbox root g} :
    g ∈ automata rank rules chains tbox root ↔
      .some g.target g.filler ∈ closure tbox root ∧
      g.initial = (compile rank rules (normalize chains) (g.target,false)).simplify := by
  simp only [automata, List.mem_filterMap]
  constructor
  · rintro ⟨c,hc,he⟩
    cases c <;> simp at he
    case some r f => cases he; exact ⟨hc,rfl⟩
  · rintro ⟨hc,hi⟩
    refine ⟨.some g.target g.filler,hc,?_⟩
    cases g
    simp_all

private def states (gs : List Automaton) : List State :=
  (gs.flatMap fun g => g.initial.residuals.map (state g)).eraseDups

private theorem mem_states {gs g p} (hg : g ∈ gs) (hp : p ∈ g.initial.residuals) :
    state g p ∈ states gs :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨g,hg,List.mem_map_of_mem hp⟩)

private def stateConcept (ss : List State) (s : State) : Concept :=
  if s.residual = .epsilon then encode s.filler else .atom (flagName (ss.idxOf s))

private def rulesAt (ss : List State) (g : Automaton) (p : PathRegex)
    (result : Concept) : TBox :=
  (if p.nullable then [⟨encode g.filler,result⟩] else []) ++
    p.letters.flatMap fun s => (p.derivative s).map fun q =>
      ⟨.some (roleName s) (stateConcept ss (state g q)),result⟩

private def initialResult (g : Automaton) : Concept := encode (.some g.target g.filler)

private def guardBox (gs : List Automaton) : TBox :=
  (gs.flatMap fun g => rulesAt (states gs) g g.initial (initialResult g) ++
    g.initial.residuals.flatMap fun p => rulesAt (states gs) g p (stateConcept (states gs) (state g p))).eraseDups

private def inverseNames (gs : List Automaton) : List String :=
  (gs.flatMap fun g => (g.initial :: g.initial.residuals).flatMap fun p =>
    p.letters.filterMap fun s => if s.2 then some s.1 else none).eraseDups

private def guardRules (gs : List Automaton) (rules : RoleTheory) : RoleTheory :=
  rules.map (fun (r,s) => (signedName r,signedName s)) ++
    (inverseNames gs).flatMap fun r => ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))

def prepare (rank : Rank) (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) : Problem :=
  let gs := automata rank rules chains tbox root
  ⟨guardRules gs rules,tbox.map encodeInclusion ++ guardBox gs,encode root⟩

private def reach (i : Interpretation) (s : State) (x : i.Domain) : Prop :=
  ∃ w y, s.residual.Matches w ∧ WordPath i w x y ∧ holds i y s.filler

private def expand (i : Interpretation) (ss : List State) : Interpretation :=
  {i with
    atom := fun s x => match s.toList with
      | 'a' :: rest => i.atom (String.ofList rest) x
      | 'g' :: rest => match ss[rest.length]? with
        | some s => reach i s x
        | none => False
      | _ => False
    role := fun r x y => holdsRole i (readRole r) x y}

private theorem expand_role (i : Interpretation) (ss : List State) (s : OrientedRole)
    (x y : i.Domain) : (expand i ss).role (roleName s) x y ↔ holdsRole i s x y := by
  simp only [expand, read_roleName]

private theorem holds_expand (i : Interpretation) (ss : List State) (x : i.Domain) (c : Concept) :
    holds (expand i ss) x (encode c) ↔ holds i x c := by
  induction c generalizing x with
  | top => rfl
  | atom p => simp [encode, holds, expand, atomName]
  | neg c ih => simp only [encode, holds, ih]
  | conj a b ih₁ ih₂ => simp only [encode, holds, ih₁, ih₂]
  | some r c ih =>
    change (∃ y : i.Domain, (expand i ss).role (roleName (r,false)) x y ∧
      holds (expand i ss) y (encode c)) ↔ _
    simp only [expand_role, ih, holdsRole, Bool.false_eq_true, ↓reduceIte, holds]

private theorem expand_state {i : Interpretation} {ss : List State} {s : State}
    (hs : s ∈ ss) (x : i.Domain) :
    holds (expand i ss) x (stateConcept ss s) ↔ reach i s x := by
  by_cases he : s.residual = .epsilon
  · rw [stateConcept, ite_eq_left he, holds_expand]
    unfold reach
    rw [he]
    constructor
    · intro h
      exact ⟨[],x,rfl,rfl,h⟩
    · rintro ⟨w,y,hw,hxy,hy⟩
      change w = [] at hw
      subst w
      change x = y at hxy
      exact hxy ▸ hy
  · rw [stateConcept, ite_eq_right he]
    have hn := List.idxOf_lt_length_of_mem hs
    have hget : ss[ss.idxOf s]? = some s :=
      List.getElem?_eq_some_iff.mpr ⟨hn,List.getElem_idxOf hn⟩
    simp [holds, expand, flagName, hget]

private theorem reach_state (i : Interpretation) (g : Automaton) (p : PathRegex)
    (x : i.Domain) :
    reach i (state g p) x ↔ ∃ w y, p.Matches w ∧ WordPath i w x y ∧ holds i y g.filler := by
  simp only [reach, state, PathRegex.simplify_correct]

private theorem expand_rules {i : Interpretation} {rules : RoleTheory}
    (hi : modelsRoles i rules) (gs : List Automaton) :
    modelsRoles (expand i (states gs)) (guardRules gs rules) := by
  have hs (r : OrientedRole) (x y : i.Domain) :
      holdsRole (expand i (states gs)) (signedName r) x y ↔ holdsRole i r x y := by
    rcases r with ⟨r,_ | _⟩
    · exact expand_role i (states gs) (r,false) x y
    · exact expand_role i (states gs) (r,false) y x
  intro r s hm x y he
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨⟨a,b⟩,hab,eq⟩ := List.mem_map.mp hm
    cases eq
    exact (hs b x y).mpr (hi a b hab x y ((hs a x y).mp he))
  · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hm
    have hinv : modelsRoles (expand i (states gs))
        (ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))) := by
      apply (ALCHI.models_inverseRules_iff _ _ _).mpr
      intro x y
      exact (expand_role i (states gs) (r,false) x y).trans
        (expand_role i (states gs) (r,true) y x).symm
    exact hinv _ _ hr x y he

private theorem expand_at {i : Interpretation} {gs : List Automaton} {g : Automaton}
    (hg : g ∈ gs) {p : PathRegex} (hp : p ∈ g.initial :: g.initial.residuals) {res : Concept}
    (finish : ∀ x w y, p.Matches w → WordPath i w x y → holds i y g.filler →
      holds (expand i (states gs)) x res) :
    models (expand i (states gs)) (rulesAt (states gs) g p res) := by
  intro q hq x hsub
  rcases List.mem_append.mp hq with hq | hq
  · by_cases hn : p.nullable = true
    · have hq' : q = ⟨encode g.filler,res⟩ := by simpa [hn] using hq
      subst q
      exact finish x [] x (p.nullable_iff.mp hn) rfl
        ((holds_expand i (states gs) x g.filler).mp hsub)
    · simp [hn] at hq
  · obtain ⟨s,_,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    obtain ⟨z,hxz,hstate⟩ := hsub
    have hn : r ∈ g.initial.residuals := by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact PathRegex.derivative_subset _ _ hr
      · exact PathRegex.residuals_closed hp _ hr
    have hre := (reach_state i g r z).mp ((expand_state (i := i) (mem_states hg hn) z).mp hstate)
    obtain ⟨w,y,hw,hy,hf⟩ := hre
    exact finish x (s :: w) y ((p.matches_derivative s w).mpr ⟨r,hr,hw⟩)
      ⟨z,(expand_role i (states gs) s x z).mp hxz,hy⟩ hf

private theorem expand_guards {rank rules chains tbox root i}
    (h : Ranked rank rules chains) (hr : modelsRoles i rules) (hc : modelsChains i chains) :
    let gs := automata rank rules chains tbox root
    models (expand i (states gs)) (guardBox gs) := by
  dsimp only
  intro q hq
  obtain ⟨g,hg,hq⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hq)
  rcases List.mem_append.mp hq with hq | hq
  · refine expand_at hg (List.mem_cons_self ..) (fun x w y hw hp hf => ?_) q hq
    have he := (mem_automata.mp hg).2
    rw [he, PathRegex.simplify_correct, compile_correct h] at hw
    exact (holds_expand i _ x (.some g.target g.filler)).mpr ⟨y,hw.sound hr hc hp,hf⟩
  · obtain ⟨p,hp,hq⟩ := List.mem_flatMap.mp hq
    exact expand_at hg (List.mem_cons_of_mem _ hp)
      (fun x w y hw hxy hy => (expand_state (i := i) (mem_states hg hp) x).mpr
        ((reach_state i g p x).mpr ⟨w,y,hw,hxy,hy⟩)) q hq

private theorem prepare_forward {rank rules chains tbox root}
    (h : Ranked rank rules chains) (hs : RoleChains.ConceptSat rules chains tbox root) :
    let p := prepare rank rules chains tbox root
    ConceptSatUnder p.rules p.tbox p.root := by
  obtain ⟨i,hr,hc,hm,x,hx⟩ := hs
  let gs := automata rank rules chains tbox root
  refine ⟨expand i (states gs),expand_rules hr gs,?_,x,(holds_expand i _ x root).mpr hx⟩
  intro q hq u hu
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨ax,ha,rfl⟩ := List.mem_map.mp hq
    exact (holds_expand i _ u ax.sup).mpr (hm ax ha u ((holds_expand i _ u ax.sub).mp hu))
  · exact expand_guards h hr hc q hq u hu

private theorem project_role {j : Interpretation} {gs : List Automaton} {rules : RoleTheory}
    (h : modelsRoles j (guardRules gs rules)) {g : Automaton} (hg : g ∈ gs)
    {p : PathRegex} (hp : p ∈ g.initial :: g.initial.residuals)
    {s : OrientedRole} (hs : s ∈ p.letters) (x y : j.Domain) :
    j.role (roleName s) x y ↔ holdsRole (project j) s x y := by
  rcases s with ⟨r,_ | _⟩
  · rfl
  · have hn : r ∈ inverseNames gs := List.mem_eraseDups.mpr (List.mem_flatMap.mpr
      ⟨g,hg,List.mem_flatMap.mpr ⟨p,hp,List.mem_filterMap.mpr ⟨(r,true),hs,rfl⟩⟩⟩)
    have hi : modelsRoles j (ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))) := by
      intro a b hb
      exact h a b (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r,hn,hb⟩))
    exact ((ALCHI.models_inverseRules_iff j _ _).mp hi y x).symm

private theorem initial_at {j : Interpretation} {gs : List Automaton}
    (hm : models j (guardBox gs)) {g : Automaton} (hg : g ∈ gs) :
    models j (rulesAt (states gs) g g.initial (initialResult g)) :=
  fun q hq => hm q (List.mem_eraseDups.mpr (List.mem_flatMap.mpr
    ⟨g,hg,List.mem_append_left _ hq⟩))

private theorem residual_at {j : Interpretation} {gs : List Automaton}
    (hm : models j (guardBox gs)) {g : Automaton} (hg : g ∈ gs)
    {p : PathRegex} (hp : p ∈ g.initial.residuals) :
    models j (rulesAt (states gs) g p (stateConcept (states gs) (state g p))) :=
  fun q hq => hm q (List.mem_eraseDups.mpr (List.mem_flatMap.mpr
    ⟨g,hg,List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,hq⟩)⟩))

private theorem reaches_result {j : Interpretation} {gs : List Automaton} {rules : RoleTheory}
    (hr : modelsRoles j (guardRules gs rules)) (hm : models j (guardBox gs))
    {g : Automaton} (hg : g ∈ gs) {w : Word} {y : j.Domain}
    (hf : holds (project j) y g.filler) {p : PathRegex}
    (hp : p ∈ g.initial :: g.initial.residuals) {result : Concept}
    (ha : models j (rulesAt (states gs) g p result))
    (x : j.Domain) (hw : p.Matches w) (hx : WordPath (project j) w x y) :
    holds j x result := by
  induction w generalizing p result x with
  | nil =>
    change x = y at hx
    subst x
    have he := p.nullable_iff.mpr hw
    apply ha ⟨encode g.filler,result⟩ _ y ((holds_encode j y g.filler).mpr hf)
    exact List.mem_append_left _ (by simp [he])
  | cons s tail ih =>
    obtain ⟨q,hq,ht⟩ := (p.matches_derivative s tail).mp hw
    obtain ⟨z,he,hpz⟩ := hx
    have hs := PathRegex.letters_of_matches hw (List.mem_cons_self ..)
    have hres : q ∈ g.initial.residuals := by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact PathRegex.derivative_subset _ _ hq
      · exact PathRegex.residuals_closed hp _ hq
    have hfin := ih (List.mem_cons_of_mem _ hres) (residual_at hm hg hres) z ht hpz
    exact ha ⟨.some (roleName s) (stateConcept (states gs) (state g q)),result⟩
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s,hs,List.mem_map_of_mem hq⟩))
      x ⟨z,(project_role hr hg hp hs x z).mpr he,hfin⟩

private theorem preserves {rank rules chains tbox root j}
    (h : Ranked rank rules chains)
    (hr : modelsRoles j (prepare rank rules chains tbox root).rules)
    (hm : models j (prepare rank rules chains tbox root).tbox)
    (x : j.Domain) {c : Concept} (hc : c ∈ closure tbox root) :
    holds (complete (project j) rules chains) x c ↔ holds (project j) x c := by
  apply holds_complete_iff (i := project j) _ x hc
  intro r c hsome u v hedge hf
  obtain ⟨w,hw,hp⟩ := hedge
  let gs := automata rank rules chains tbox root
  let g : Automaton := ⟨r,c,(compile rank rules (normalize chains) (r,false)).simplify⟩
  have hg : g ∈ gs := mem_automata.mpr ⟨hsome,rfl⟩
  have hguard : models j (guardBox gs) := fun q hq => hm q (List.mem_append_right _ hq)
  have hmatch : g.initial.Matches w :=
    (PathRegex.simplify_correct _ _).mpr ((compile_correct h _ _).mpr hw)
  exact (holds_encode j u (.some r c)).mp
    (reaches_result hr hguard hg hf (List.mem_cons_self ..)
      (initial_at hguard hg) u hmatch hp)

private theorem completed_models {rank rules chains tbox root j}
    (h : Ranked rank rules chains)
    (hr : modelsRoles j (prepare rank rules chains tbox root).rules)
    (hm : models j (prepare rank rules chains tbox root).tbox) :
    models (complete (project j) rules chains) tbox := by
  intro q hq u hu
  obtain ⟨hs,hp⟩ := axiom_mem_closure root hq
  have hin := (holds_encode j u q.sub).mpr ((preserves h hr hm u hs).mp hu)
  have hout := hm (encodeInclusion q) (List.mem_append_left _ (List.mem_map_of_mem hq)) u hin
  exact (preserves h hr hm u hp).mpr ((holds_encode j u q.sup).mp hout)

/-- The guard translation preserves satisfiability, including cyclic paths,
    with the same domain and the same truths for the source subformulas. -/
theorem prepare_iff {rank rules chains} (h : Ranked rank rules chains)
    (tbox : TBox) (root : Concept) :
    let p := prepare rank rules chains tbox root
    ConceptSatUnder p.rules p.tbox p.root ↔ RoleChains.ConceptSat rules chains tbox root := by
  constructor
  · rintro ⟨j,hr,hm,x,hx⟩
    exact ⟨complete (project j) rules chains,complete_roles _ _ _,complete_chains _ _ _,
      completed_models h hr hm,x,
      (preserves h hr hm x (root_mem_closure tbox root)).mpr ((holds_encode j x root).mp hx)⟩
  · exact prepare_forward h

def check (rank : Rank) (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) (e : Certificate) : Bool :=
  let p := prepare rank rules chains tbox root
  checkCertificateUnder p.rules p.tbox p.root e

def search (rank : Rank) (rules : RoleTheory) (chains : List Chain) (tbox : TBox)
    (root : Concept) : Certificate :=
  let p := prepare rank rules chains tbox root
  searchUnder p.rules p.tbox p.root

theorem search_checked (rank : Rank) (rules : RoleTheory) (chains : List Chain)
    (tbox : TBox) (root : Concept) : check rank rules chains tbox root (search rank rules chains tbox root) = true :=
  searchUnder_checked _ _ _

def claim (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (root : Concept) : Certificate → Prop
  | .model _ => RoleChains.ConceptSat rules chains tbox root
  | .refutation _ => ¬ RoleChains.ConceptSat rules chains tbox root

theorem check_sound {rank rules chains tbox root e} (h : Ranked rank rules chains)
    (hc : check rank rules chains tbox root e = true) : claim rules chains tbox root e := by
  have hs := checkCertificateUnder_sound hc
  have he := prepare_iff h tbox root
  cases e with
  | model _ => exact he.mp hs
  | refutation _ => exact fun hh => hs (he.mpr hh)

theorem search_correct {rank rules chains} (h : Ranked rank rules chains) (tbox : TBox) (root : Concept) :
    claim rules chains tbox root (search rank rules chains tbox root) :=
  check_sound h (search_checked rank rules chains tbox root)

theorem search_model_iff {rank rules chains} (h : Ranked rank rules chains)
    (tbox : TBox) (root : Concept) :
    (∃ pool, search rank rules chains tbox root = .model pool) ↔
      RoleChains.ConceptSat rules chains tbox root := by
  have hc := search_correct h tbox root
  cases he : search rank rules chains tbox root with
  | model pool =>
    rw [he] at hc
    exact ⟨fun _ => hc,fun _ => ⟨pool,rfl⟩⟩
  | refutation n =>
    rw [he] at hc
    constructor
    · rintro ⟨_,hn⟩; cases hn
    · intro hh; exact (hc hh).elim

theorem search_refutation_iff {rank rules chains} (h : Ranked rank rules chains)
    (tbox : TBox) (root : Concept) :
    (∃ rounds, search rank rules chains tbox root = .refutation rounds) ↔
      ¬ RoleChains.ConceptSat rules chains tbox root := by
  have hc := search_correct h tbox root
  cases he : search rank rules chains tbox root with
  | model pool =>
    rw [he] at hc
    constructor
    · rintro ⟨_,hn⟩; cases hn
    · intro hh; exact (hh hc).elim
  | refutation n =>
    rw [he] at hc
    exact ⟨fun _ => hc,fun _ => ⟨n,rfl⟩⟩

theorem finite_model_property {rank rules chains tbox root} (h : Ranked rank rules chains)
    (hs : RoleChains.ConceptSat rules chains tbox root) :
    ∃ i : Interpretation, modelsRoles i rules ∧ modelsChains i chains ∧ models i tbox ∧
      (∃ carrier : List i.Domain, ∀ x, x ∈ carrier) ∧ ∃ x, holds i x root := by
  obtain ⟨pool,he⟩ := (search_model_iff h tbox root).mpr hs
  have hc := search_checked rank rules chains tbox root
  rw [he] at hc
  obtain ⟨j,hr,hm,carrier,x,hx⟩ := checkModelUnder_finite_sound hc
  exact ⟨complete (project j) rules chains,complete_roles _ _ _,complete_chains _ _ _,
    completed_models h hr hm,carrier,x,
    (preserves h hr hm x (root_mem_closure tbox root)).mpr ((holds_encode j x root).mp hx)⟩

end Sabrina.RoleChains.RankedPaths
