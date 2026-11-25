import Sabrina.ALCHI.Query

namespace Sabrina.RoleChains

open Sabrina.ALC

/-- The composition of the oriented relations in `body` is contained in
the forward relation named by `head`. -/
structure Chain where
  body : List OrientedRole
  head : String
  deriving DecidableEq, Repr

def Chain.named (body : List String) (head : String) : Chain :=
  ⟨body.map (·, false), head⟩

def Chain.bodyNames (c : Chain) : List String := c.body.map Prod.fst

namespace TransitivePaths

def WordPath (i : Interpretation) : List OrientedRole → i.Domain → i.Domain → Prop
  | [], x, y => x = y
  | r :: tail, x, y => ∃ z, holdsRole i r x z ∧ WordPath i tail z y

end TransitivePaths

def Path (i : Interpretation) : List String → i.Domain → i.Domain → Prop
  | [], x, y => x = y
  | r :: tail, x, y => ∃ z, i.role r x z ∧ Path i tail z y

def modelsChains (i : Interpretation) (chains : List Chain) : Prop :=
  ∀ c ∈ chains, ∀ x y, TransitivePaths.WordPath i c.body x y → i.role c.head x y

def ConceptSat (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (root : Concept) : Prop :=
  ∃ i : Interpretation, modelsRoles i rules ∧ modelsChains i chains ∧ models i tbox ∧
    ∃ x, holds i x root

def diamond (word : List String) (c : Concept) : Concept :=
  word.foldr Concept.some c

theorem holds_diamond (i : Interpretation) (word : List String) (x : i.Domain) (c : Concept) :
    holds i x (diamond word c) ↔ ∃ y, Path i word x y ∧ holds i y c := by
  induction word generalizing x with
  | nil => simp [diamond, Path]
  | cons r tail ih =>
    change (∃ z, i.role r x z ∧ holds i z (diamond tail c)) ↔
      ∃ y, (∃ z, i.role r x z ∧ Path i tail z y) ∧ holds i y c
    constructor
    · rintro ⟨z, hr, hz⟩
      obtain ⟨y, hp, hy⟩ := (ih z).mp hz
      exact ⟨y, ⟨z, hr, hp⟩, hy⟩
    · rintro ⟨y, ⟨z, hr, hp⟩, hy⟩
      exact ⟨z, hr, (ih z).mpr ⟨y, hp, hy⟩⟩

def chainHint (a : Chain) (c : Concept) : Inclusion :=
  if a.body.all (fun r => !r.2) then ⟨diamond a.bodyNames c, .some a.head c⟩
  else ⟨.top, .top⟩

private theorem wordPath_of_forward {i : Interpretation} {word : List OrientedRole}
    (hf : word.all (fun r => !r.2) = true) {x y : i.Domain}
    (hp : Path i (word.map Prod.fst) x y) : TransitivePaths.WordPath i word x y := by
  induction word generalizing x with
  | nil => exact hp
  | cons r tail ih =>
    obtain ⟨hdir, htail⟩ := Bool.and_eq_true_iff.mp hf
    obtain ⟨z, hr, ht⟩ := hp
    have hforward : r.2 = false := by simpa using hdir
    exact ⟨z, by simpa [holdsRole, hforward] using hr, ih htail ht⟩

private theorem chainHint_sound {i : Interpretation} {chains : List Chain}
    (hi : modelsChains i chains) {a : Chain} (ha : a ∈ chains) (c : Concept)
    (x : i.Domain) (hx : holds i x (chainHint a c).sub) : holds i x (chainHint a c).sup := by
  by_cases hforward : a.body.all (fun r => !r.2) = true
  · simp only [chainHint, hforward, ite_true] at hx ⊢
    obtain ⟨y, hp, hc⟩ := (holds_diamond i a.bodyNames x c).mp hx
    exact ⟨y, hi a ha x y (wordPath_of_forward hforward hp), hc⟩
  · simp [chainHint, hforward, holds]

/-- Modal consequences used to search for a refutation. These are entailed by the
    role axioms. The independent finite-model checker checks the role axioms themselves. -/
def augment (rules : RoleTheory) (chains : List Chain) (tbox : TBox) (root : Concept) : TBox :=
  let concepts := closure tbox root
  let closed := roleClosure rules
  let below := fun r s => r == s || closed.contains ((r,false), (s,false))
  tbox ++ chains.flatMap fun chain =>
    let fillers := concepts.filterMap fun
      | .some r c =>
        if below chain.head r || chain.bodyNames.getLast?.any (below r) then some c else none
      | _ => none
    fillers.eraseDups.map (chainHint chain)

theorem models_augment {i : Interpretation} {rules : RoleTheory} {chains : List Chain}
    {tbox : TBox} {root : Concept}
    (hc : modelsChains i chains) (ht : models i tbox) : models i (augment rules chains tbox root) := by
  intro a ha x hx
  rcases List.mem_append.mp ha with ha | ha
  · exact ht a ha x hx
  · obtain ⟨chain, hm, hchain⟩ := List.mem_flatMap.mp ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hchain
    exact chainHint_sound hc hm c x hx

theorem checkRefutation_sound {rules chains tbox root rounds}
    (h : checkRefutationUnder rules (augment rules chains tbox root) root rounds = true) :
    ¬ ConceptSat rules chains tbox root := by
  rintro ⟨i, hr, hc, ht, x, hx⟩
  exact checkRefutationUnder_sound h ⟨i, hr, models_augment hc ht, x, hx⟩

end Sabrina.RoleChains
