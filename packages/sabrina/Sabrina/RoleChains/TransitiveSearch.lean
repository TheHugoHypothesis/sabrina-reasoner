import Sabrina.RoleChains.TransitiveCompletion

namespace Sabrina.RoleChains.TransitivePaths

open Sabrina.ALC

def atomName (p : String) : String := String.ofList ('a' :: p.toList)
def flagName (n : Nat) : String := String.ofList ('g' :: List.replicate n 'g')
def roleName (r : OrientedRole) : String :=
  String.ofList ((if r.2 then '-' else '+') :: r.1.toList)

def readRole (s : String) : OrientedRole :=
  match s.toList with
  | '-' :: rest => (String.ofList rest, true)
  | _ :: rest => (String.ofList rest, false)
  | [] => ("",false)

theorem read_roleName (r : OrientedRole) : readRole (roleName r) = r := by
  rcases r with ⟨r, _ | _⟩ <;> simp [readRole, roleName]

def encode : Concept → Concept
  | .top => .top
  | .atom p => .atom (atomName p)
  | .neg c => .neg (encode c)
  | .conj a b => .conj (encode a) (encode b)
  | .some r c => .some (roleName (r,false)) (encode c)

def encodeInclusion (q : Inclusion) : Inclusion := ⟨encode q.sub, encode q.sup⟩

def project (j : Interpretation) : Interpretation :=
  {j with
    atom := fun p x => j.atom (atomName p) x
    role := fun r x y => j.role (roleName (r,false)) x y}

theorem holds_encode (j : Interpretation) (x : j.Domain) (c : Concept) :
    holds j x (encode c) ↔ holds (project j) x c := by
  induction c generalizing x with
  | top | atom => rfl
  | neg c ih => simp only [encode, holds, ih]
  | conj a b ih₁ ih₂ => simp only [encode, holds, ih₁, ih₂]
  | some r c ih => simp only [encode, holds, ih, project]

private structure Guard where
  target : String
  filler : Concept
  letters : List OrientedRole

private def guardList (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    List Guard :=
  (closure tbox root).flatMap fun
    | .some r c => (compile rules ts (r,false)).repeats.map fun letters => ⟨r,c,letters⟩
    | _ => []

private theorem mem_guardList {rules ts tbox root g} :
    g ∈ guardList rules ts tbox root ↔
      .some g.target g.filler ∈ closure tbox root ∧
      g.letters ∈ (compile rules ts (g.target,false)).repeats := by
  simp only [guardList, List.mem_flatMap]
  constructor
  · rintro ⟨c,hc,hm⟩
    cases c with
    | some r d =>
      obtain ⟨letters, hr, rfl⟩ := List.mem_map.mp hm
      exact ⟨hc,hr⟩
    | top | atom | neg | conj => simp at hm
  · rintro ⟨hc,hr⟩
    exact ⟨.some g.target g.filler, hc, List.mem_map.mpr ⟨g.letters,hr,by cases g; rfl⟩⟩

/-- A flag means that the filler is reachable by zero or more letters
    from the chosen repeat branch. The last axiom uses a positive first step. -/
private def guardAxioms (g : Guard) (n : Nat) : TBox :=
  let p : Concept := .atom (flagName n)
  ⟨encode g.filler, p⟩ :: g.letters.flatMap fun s =>
    let step := Concept.some (roleName s) p
    [⟨step, p⟩, ⟨step, encode (.some g.target g.filler)⟩]

private def guardBox (gs : List Guard) : TBox :=
  (List.finRange gs.length).flatMap fun n => guardAxioms gs[n.val] n.val

def signedName (r : OrientedRole) : OrientedRole := (roleName (r.1,false),r.2)

private def guardRules (gs : List Guard) (rules : RoleTheory) : RoleTheory :=
  let names := (gs.flatMap fun g => g.letters.filterMap fun s =>
    if s.2 then some s.1 else none).eraseDups
  rules.map (fun (r,s) => (signedName r,signedName s)) ++
    names.flatMap fun r => ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))

structure Problem where
  rules : RoleTheory
  tbox : TBox
  root : Concept

def prepare (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) : Problem :=
  let gs := guardList rules ts tbox root
  ⟨guardRules gs rules, tbox.map encodeInclusion ++ guardBox gs, encode root⟩

/-- Satisfiability under the original signed hierarchy and declared transitivity. -/
def ConceptSat (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) : Prop :=
  ∃ i : Interpretation, modelsRoles i rules ∧ TransitiveRoles i ts ∧ models i tbox ∧
    ∃ x, holds i x root

private def reaches (i : Interpretation) (g : Guard) (x : i.Domain) : Prop :=
  ∃ word y, (∀ r ∈ word, r ∈ g.letters) ∧ WordPath i word x y ∧ holds i y g.filler

private def expand (i : Interpretation) (gs : List Guard) : Interpretation :=
  {i with
    atom := fun s x => match s.toList with
      | 'a' :: rest => i.atom (String.ofList rest) x
      | 'g' :: rest => match gs[rest.length]? with
        | some g => reaches i g x
        | none => False
      | _ => False
    role := fun r x y => holdsRole i (readRole r) x y}

private theorem expand_role (i : Interpretation) (gs : List Guard) (r : OrientedRole)
    (x y : i.Domain) : (expand i gs).role (roleName r) x y ↔ holdsRole i r x y := by
  simp only [expand, read_roleName]

private theorem expand_flag (i : Interpretation) (gs : List Guard) (n : Fin gs.length)
    (x : i.Domain) : holds (expand i gs) x (.atom (flagName n.val)) ↔ reaches i gs[n.val] x := by
  simp [holds, expand, flagName]

private theorem holds_expand (i : Interpretation) (gs : List Guard) (x : i.Domain) (c : Concept) :
    holds (expand i gs) x (encode c) ↔ holds i x c := by
  induction c generalizing x with
  | top => rfl
  | atom p => simp [encode, holds, expand, atomName]
  | neg c ih => simp only [encode, holds, ih]
  | conj a b ih₁ ih₂ => simp only [encode, holds, ih₁, ih₂]
  | some r c ih =>
    change (∃ y : i.Domain, (expand i gs).role (roleName (r,false)) x y ∧
      holds (expand i gs) y (encode c)) ↔ _
    simp only [expand_role, ih, holdsRole, Bool.false_eq_true, ↓reduceIte, holds]

private theorem expand_signed (i : Interpretation) (gs : List Guard) (r : OrientedRole)
    (x y : i.Domain) : holdsRole (expand i gs) (signedName r) x y ↔ holdsRole i r x y := by
  rcases r with ⟨r,_ | _⟩
  · exact expand_role i gs (r,false) x y
  · exact expand_role i gs (r,false) y x

private theorem expand_rules {i : Interpretation} {rules : RoleTheory}
    (hi : modelsRoles i rules) (gs : List Guard) :
    modelsRoles (expand i gs) (guardRules gs rules) := by
  intro r s hm x y he
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨⟨a,b⟩, hab, eq⟩ := List.mem_map.mp hm
    cases eq
    exact (expand_signed i gs b x y).mpr (hi a b hab x y ((expand_signed i gs a x y).mp he))
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hm
    have hi : modelsRoles (expand i gs)
        (ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))) := by
      apply (ALCHI.models_inverseRules_iff _ _ _).mpr
      intro x y
      exact (expand_role i gs (r,false) x y).trans (expand_role i gs (r,true) y x).symm
    exact hi _ _ hr x y he

private theorem repeat_accepts {rules ts r letters word} (hr : letters ∈ (compile rules ts r).repeats)
    (hn : word ≠ []) (hletters : ∀ s ∈ word, s ∈ letters) :
    (compile rules ts r).accepts word = true := by
  cases word with
  | nil => exact (hn rfl).elim
  | cons s rest =>
    simp only [Automaton.accepts, Bool.or_eq_true]
    exact Or.inr (List.any_eq_true.mpr ⟨letters, hr,
      List.all_eq_true.mpr fun t ht => List.contains_iff_mem.mpr (hletters t ht)⟩)

private theorem expand_guards {i : Interpretation} {rules : RoleTheory} {ts : List String}
    (hi : modelsRoles i rules) (ht : TransitiveRoles i ts) (gs : List Guard)
    (valid : ∀ g ∈ gs, g.letters ∈ (compile rules ts (g.target,false)).repeats) :
    models (expand i gs) (guardBox gs) := by
  intro q hq x hsub
  obtain ⟨n, _, hn⟩ := List.mem_flatMap.mp hq
  let g := gs[n.val]
  change q ∈ guardAxioms g n.val at hn
  rcases List.mem_cons.mp hn with hq | hq
  · subst q
    exact (expand_flag i gs n x).mpr ⟨[], x, by simp, rfl,
      (holds_expand i gs x g.filler).mp hsub⟩
  · obtain ⟨s, hs, h⟩ := List.mem_flatMap.mp hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have witness (hw : holds (expand i gs) x (.some (roleName s) (.atom (flagName n.val)))) :
        ∃ word y, (∀ r ∈ s :: word, r ∈ g.letters) ∧ WordPath i (s :: word) x y ∧
          holds i y g.filler := by
      obtain ⟨z, hz, hflag⟩ := hw
      obtain ⟨word, y, hw, hp, hf⟩ := (expand_flag i gs n z).mp hflag
      exact ⟨word, y, fun r hr => (List.mem_cons.mp hr).elim (fun eq => eq.symm ▸ hs) (hw r),
        ⟨z, (expand_role i gs s x z).mp hz, hp⟩, hf⟩
    rcases h with h | h
    · subst q
      obtain ⟨word,y,hw,hp,hf⟩ := witness hsub
      exact (expand_flag i gs n x).mpr ⟨s :: word,y,hw,hp,hf⟩
    · subst q
      obtain ⟨word,y,hw,hp,hf⟩ := witness hsub
      have ha := repeat_accepts (valid g (List.getElem_mem n.isLt)) (by simp) hw
      have hd := (compile_correct rules ts (s :: word) (g.target,false)).mp ha
      exact (holds_expand i gs x (.some g.target g.filler)).mpr ⟨y, hd.sound hi ht hp, hf⟩

private theorem prepare_forward {rules ts tbox root}
    (h : ConceptSat rules ts tbox root) :
    ConceptSatUnder (prepare rules ts tbox root).rules (prepare rules ts tbox root).tbox
      (prepare rules ts tbox root).root := by
  obtain ⟨i, hr, ht, hm, x, hx⟩ := h
  let gs := guardList rules ts tbox root
  refine ⟨expand i gs, expand_rules hr gs, ?_, x, (holds_expand i gs x root).mpr hx⟩
  intro q hq u hu
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨ax, ha, rfl⟩ := List.mem_map.mp hq
    exact (holds_expand i gs u ax.sup).mpr (hm ax ha u ((holds_expand i gs u ax.sub).mp hu))
  · exact expand_guards hr ht gs (fun _ hg => (mem_guardList.mp hg).2) q hq u hu

theorem project_signed (j : Interpretation) (r : OrientedRole) (x y : j.Domain) :
    holdsRole j (signedName r) x y ↔ holdsRole (project j) r x y := by
  rcases r with ⟨r,_ | _⟩ <;> rfl

private theorem project_rules {j : Interpretation} {gs : List Guard} {rules : RoleTheory}
    (h : modelsRoles j (guardRules gs rules)) : modelsRoles (project j) rules := by
  intro r s hrs x y hx
  exact (project_signed j s x y).mp
    (h _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨(r,s), hrs,rfl⟩)) x y
      ((project_signed j r x y).mpr hx))

private theorem project_letter {j : Interpretation} {gs : List Guard} {rules : RoleTheory}
    (h : modelsRoles j (guardRules gs rules)) {g : Guard} (hg : g ∈ gs)
    {s : OrientedRole} (hs : s ∈ g.letters) (x y : j.Domain) :
    j.role (roleName s) x y ↔ holdsRole (project j) s x y := by
  rcases s with ⟨r,_ | _⟩
  · rfl
  · have hname : r ∈ (gs.flatMap fun g => g.letters.filterMap fun s =>
        if s.2 then some s.1 else none).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_flatMap.mpr
        ⟨g, hg, List.mem_filterMap.mpr ⟨(r,true), hs,rfl⟩⟩)
    have hInv : modelsRoles j (ALCHI.inverseRules (roleName (r,false)) (roleName (r,true))) := by
      intro a b hab
      exact h a b (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r,hname,hab⟩))
    exact ((ALCHI.models_inverseRules_iff j _ _).mp hInv y x).symm

private theorem guardAt {j : Interpretation} {gs : List Guard}
    (hm : models j (guardBox gs)) (n : Fin gs.length) :
    models j (guardAxioms gs[n.val] n.val) := by
  intro q hq
  exact hm q (List.mem_flatMap.mpr ⟨n, List.mem_finRange _, hq⟩)

private theorem generatedGuards {j : Interpretation} {rules : RoleTheory} {ts : List String}
    {tbox : TBox} {root : Concept}
    (hr : modelsRoles j (prepare rules ts tbox root).rules)
    (hm : models j (prepare rules ts tbox root).tbox)
    (r : String) (c : Concept) (hc : .some r c ∈ closure tbox root) (x : j.Domain)
    (hn : ¬ holds (project j) x (.some r c)) :
    (compile rules ts (r,false)).guards (project j) x (fun y => ¬ holds (project j) y c) := by
  let gs := guardList rules ts tbox root
  have hsource := project_rules (gs := gs) hr
  have hguards : models j (guardBox gs) := fun q hq => hm q (List.mem_append_right _ hq)
  have hnot : ¬ holds j x (encode (.some r c)) := fun h => hn ((holds_encode j x _).mp h)
  refine ⟨?_, ?_⟩
  · intro s hs y hxy hy
    apply hn
    have hs' : Below rules s (r,false) := ALCH.mem_subroles.mp hs
    refine ⟨y, ?_, hy⟩
    rcases hs' with rfl | hs'
    · exact hxy
    · exact modelsClosure hsource _ _ hs' x y hxy
  · intro letters hl
    let g : Guard := ⟨r,c,letters⟩
    have hg : g ∈ gs := mem_guardList.mpr ⟨hc, hl⟩
    obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hg
    have hguard := guardAt hguards ⟨n,hn⟩
    change models j (guardAxioms gs[n] n) at hguard
    rw [hget] at hguard
    let flag : Concept := .atom (flagName n)
    have step (s : OrientedRole) (hs : s ∈ letters) (y z : j.Domain)
        (he : holdsRole (project j) s y z) (hf : holds j z flag) :
        holds j y (.some (roleName s) flag) :=
      ⟨z, (project_letter hr hg hs y z).mpr he, hf⟩
    refine ⟨fun y => ¬ holds j y flag, ?_, ?_, ?_⟩
    · intro s hs y hxy hy
      apply hnot
      exact hguard ⟨.some (roleName s) flag, encode (.some r c)⟩
        (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨s,hs,by simp [g, flag]⟩))
        x (step s hs x y hxy hy)
    · intro s hs y z hy hyz hz
      apply hy
      exact hguard ⟨.some (roleName s) flag, flag⟩
        (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨s,hs,by simp [g, flag]⟩))
        y (step s hs y z hyz hz)
    · intro y hy hcy
      exact hy (hguard ⟨encode c, flag⟩ (List.mem_cons_self ..) y ((holds_encode j y c).mpr hcy))

private theorem complete_models {rules ts tbox root} {j : Interpretation}
    (hr : modelsRoles j (prepare rules ts tbox root).rules)
    (hm : models j (prepare rules ts tbox root).tbox) :
    models (complete (project j) rules ts) tbox := by
  intro q hq x hx
  obtain ⟨hs, hp⟩ := axiom_mem_closure root hq
  have hpre := holds_complete_of_automatonGuards (i := project j) (generatedGuards hr hm) x hs
  have hpost := holds_complete_of_automatonGuards (i := project j) (generatedGuards hr hm) x hp
  exact hpost.mpr ((holds_encode j x q.sup).mp
    (hm (encodeInclusion q) (List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) x
      ((holds_encode j x q.sub).mpr (hpre.mp hx))))

/-- Automaton guards preserve satisfiability in both directions. -/
theorem prepare_iff (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    let p := prepare rules ts tbox root
    ConceptSatUnder p.rules p.tbox p.root ↔ ConceptSat rules ts tbox root := by
  constructor
  · rintro ⟨j, hr, hm, x, hx⟩
    exact ⟨complete (project j) rules ts, complete_modelsRoles _ _ _,
      complete_transitive _ _ _, complete_models hr hm, x,
      (holds_complete_of_automatonGuards (i := project j) (generatedGuards hr hm) x (root_mem_closure tbox root)).mpr
        ((holds_encode j x root).mp hx)⟩
  · exact prepare_forward

def check (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept)
    (e : Certificate) : Bool :=
  let p := prepare rules ts tbox root
  checkCertificateUnder p.rules p.tbox p.root e

def search (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) : Certificate :=
  let p := prepare rules ts tbox root
  searchUnder p.rules p.tbox p.root

theorem search_checked (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    check rules ts tbox root (search rules ts tbox root) = true :=
  searchUnder_checked _ _ _

def claim (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) : Certificate → Prop
  | .model _ => ConceptSat rules ts tbox root
  | .refutation _ => ¬ ConceptSat rules ts tbox root

theorem check_sound {rules ts tbox root e}
    (h : check rules ts tbox root e = true) : claim rules ts tbox root e := by
  have hs := checkCertificateUnder_sound h
  have hsat := prepare_iff rules ts tbox root
  cases e with
  | model _ => exact hsat.mp hs
  | refutation _ => exact fun he => hs (hsat.mpr he)

theorem search_correct (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    claim rules ts tbox root (search rules ts tbox root) :=
  check_sound (search_checked rules ts tbox root)

theorem search_model_iff (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    (∃ pool, search rules ts tbox root = .model pool) ↔ ConceptSat rules ts tbox root := by
  have h := search_correct rules ts tbox root
  cases he : search rules ts tbox root with
  | model pool =>
    rw [he] at h
    exact ⟨fun _ => h, fun _ => ⟨pool,rfl⟩⟩
  | refutation n =>
    rw [he] at h
    constructor
    · rintro ⟨_, he⟩
      cases he
    · intro hs
      exact (h hs).elim

theorem search_refutation_iff (rules : RoleTheory) (ts : List String) (tbox : TBox) (root : Concept) :
    (∃ rounds, search rules ts tbox root = .refutation rounds) ↔ ¬ ConceptSat rules ts tbox root := by
  have h := search_correct rules ts tbox root
  cases he : search rules ts tbox root with
  | model pool =>
    rw [he] at h
    constructor
    · rintro ⟨_, he⟩
      cases he
    · intro hs
      exact (hs h).elim
  | refutation n =>
    rw [he] at h
    exact ⟨fun _ => h, fun _ => ⟨n,rfl⟩⟩

theorem finite_model_property {rules ts tbox root} (hs : ConceptSat rules ts tbox root) :
    ∃ i : Interpretation, modelsRoles i rules ∧ TransitiveRoles i ts ∧ models i tbox ∧
      (∃ carrier : List i.Domain, ∀ x, x ∈ carrier) ∧ ∃ x, holds i x root := by
  obtain ⟨pool, he⟩ := (search_model_iff rules ts tbox root).mpr hs
  have hc := search_checked rules ts tbox root
  rw [he] at hc
  obtain ⟨j, hr, hm, carrier, x, hx⟩ := checkModelUnder_finite_sound hc
  exact ⟨complete (project j) rules ts, complete_modelsRoles _ _ _,
    complete_transitive _ _ _, complete_models hr hm, carrier, x,
    (holds_complete_of_automatonGuards (i := project j) (generatedGuards hr hm)
      x (root_mem_closure tbox root)).mpr ((holds_encode j x root).mp hx)⟩

def onlyTransitive (chains : List RoleChains.Chain) : Bool :=
  chains.all fun c => c.body == [(c.head,false),(c.head,false)]

theorem chains_iff_transitive (i : Interpretation) (chains : List RoleChains.Chain)
    (h : onlyTransitive chains = true) :
    modelsChains i chains ↔ TransitiveRoles i (chains.map RoleChains.Chain.head) := by
  simp only [onlyTransitive, List.all_eq_true, beq_iff_eq] at h
  constructor
  · intro hm r hr x y z hx hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    apply hm c hc x z
    rw [h c hc]
    exact ⟨y, hx, z, hy, rfl⟩
  · intro ht c hc x z hp
    rw [h c hc] at hp
    obtain ⟨y, hx, v, hy, eq⟩ := hp
    change v = z at eq
    exact ht c.head (List.mem_map.mpr ⟨c,hc,rfl⟩) x y z hx (eq ▸ hy)

theorem chainSat_iff {rules chains tbox root} (h : onlyTransitive chains = true) :
    RoleChains.ConceptSat rules chains tbox root ↔
      ConceptSat rules (chains.map RoleChains.Chain.head) tbox root := by
  constructor
  · rintro ⟨i, hr, hc, hm, hx⟩
    exact ⟨i, hr, (chains_iff_transitive i chains h).mp hc, hm, hx⟩
  · rintro ⟨i, hr, ht, hm, hx⟩
    exact ⟨i, hr, (chains_iff_transitive i chains h).mpr ht, hm, hx⟩

end Sabrina.RoleChains.TransitivePaths
