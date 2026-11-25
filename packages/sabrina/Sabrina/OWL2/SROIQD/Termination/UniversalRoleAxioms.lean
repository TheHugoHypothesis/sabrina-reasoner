import Sabrina.OWL2.SROIQD.Termination.UniversalRoleRestrictions

/-! Verified support for `owl:topObjectProperty` (and its inverse) in OWL 2 DL
role axioms: unary role inclusions (`R ⊑ U`, `U ⊑ R`, `EquivalentObjectProperties`,
`InverseObjectProperties`), role characteristics (`Reflexive`, `Irreflexive`,
`Asymmetric`, `Disjoint`), `HasKey` axioms, positive and negative object property
assertions, and role chain bodies (`R₁ ∘ ... ∘ U ∘ ... ∘ Rₖ ⊑ S`), together with
OWL 2 DL §11.1–§11.2 global simplicity enforcement.

Pipeline:
1. Enforce OWL 2 DL simplicity on the original normalized problem
   (`Problem.checkSimpleWithTop`), treating `owl:topObjectProperty` and every
   role reachable from it via `roleClosure p.rules` as non-simple.
2. Eliminate bottom properties (`Problem.lowerBottom`).
3. Compute the closure `univRoles p` of all object properties forced universal
   by `p.rules` and nonempty all-universal `p.chains`, and collapse them to
   `topObjectProperty` (`Problem.collapseUnivRoles`).
4. Eliminate all non-chain-body occurrences of `topObjectProperty` from `rules`,
   tautological top-headed `chains`, `chars`, `keys` (dropping `U` from
   `k.objProps` via `hnx : i.named x`), `objAssertions`, and `negObjAssertions`
   (`Problem.lowerTopRoleAxioms`).
5. Eliminate every chain whose body contains `topObjectProperty` via the
   Rudolph–Krötzsch–Hitzler nominal bridge (`A ⊑ ∃w₁.{o}`, `B ⊑ ∃w₂⁻.{o}`,
   `w₁ ∘ w₂ ⊑ head`) using two provably fresh ordinary roles `w₁, w₂` and a
   provably fresh anonymous individual `o` so `i.named` and `HasKey` are
   preserved (`Problem.lowerTopChains`).
6. Lower chain aliases and run the verified fuel-free solver
   `decideSROIQDWithTopBool`. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole RoleTheory roleClosure)
open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Chain Rank checkRegular findRank)
open Sabrina.RoleChains.TransitivePaths (flipWord)

/-! ### 1. OWL 2 DL simplicity with `owl:topObjectProperty` -/

/-- W3C OWL 2 DL §11.1–§11.2 simplicity check: in addition to `p.checkSimple`
(no chain-head sub-roles), `owl:topObjectProperty` is composite, so neither
`owl:topObjectProperty` nor any role reachable from it via `roleClosure p.rules`
may appear in `p.simpleRoles`. -/
def Problem.checkSimpleWithTop (p : Problem) : Bool :=
  let closed := roleClosure p.rules
  p.checkSimple &&
  p.simpleRoles.all fun r =>
    r.1 != topObjectProperty &&
    !closed.contains ((topObjectProperty, false), r) &&
    !closed.contains ((topObjectProperty, true), r)

private theorem topRole_holds' (i : Interpretation datatypeMap)
    (r : OrientedRole) (hr : r.1 = topObjectProperty) (x y : i.Object) :
    holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩
  · change i.objectProperties name x y
    rw [show name = topObjectProperty from hr]
    exact i.topObjectExt x y
  · change i.objectProperties name y x
    rw [show name = topObjectProperty from hr]
    exact i.topObjectExt y x

private theorem atLeast_congr' {α : Type} {p q : α → Prop} (h : ∀ x, p x ↔ q x) (n : Nat) :
    AtLeast n p ↔ AtLeast n q := by
  simp only [AtLeast, h]

/-! ### 2. Universal-role closure (`univRoles`) and collapsing (`collapseUnivRoles`) -/

private def univRolesStep (p : Problem) (cur : List IRI) : List IRI :=
  let fromRules := p.rules.filterMap fun rs =>
    if cur.contains rs.1.1 then Option.some rs.2.1 else none
  let fromChains := p.chains.filterMap fun c =>
    if !c.body.isEmpty && c.body.all (fun r => cur.contains r.1) then Option.some c.head else none
  (cur ++ fromRules ++ fromChains).eraseDups

private def univRolesCand (p : Problem) : List IRI :=
  (topObjectProperty :: p.rules.map (fun rs => rs.2.1) ++ p.chains.map Chain.head).eraseDups

private def univRolesLoop (p : Problem) : Nat → List IRI → List IRI
  | 0, cur => cur
  | n + 1, cur =>
    let next := univRolesStep p cur
    if next.all (cur.contains ·) then cur
    else univRolesLoop p n next

/-- All object-property IRIs forced universal in every model of `p` by
`topObjectProperty`, `p.rules`, and nonempty all-universal `p.chains`. -/
def univRoles (p : Problem) : List IRI :=
  univRolesLoop p (univRolesCand p).length [topObjectProperty]

private theorem mem_univRolesStep_of_mem {p : Problem} {cur : List IRI} {r : IRI}
    (h : r ∈ cur) : r ∈ univRolesStep p cur :=
  List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _ h))

private theorem top_mem_univRolesLoop (p : Problem) (n : Nat) (cur : List IRI)
    (ht : topObjectProperty ∈ cur) : topObjectProperty ∈ univRolesLoop p n cur := by
  induction n generalizing cur with
  | zero => exact ht
  | succ n ih =>
    dsimp only [univRolesLoop]
    split
    · exact ht
    · exact ih _ (mem_univRolesStep_of_mem ht)

theorem top_mem_univRoles (p : Problem) : topObjectProperty ∈ univRoles p :=
  top_mem_univRolesLoop p _ _ (List.mem_cons_self ..)

private theorem objPath_of_all_universal (i : Interpretation datatypeMap)
    {rs : List OrientedRole} (hne : rs ≠ [])
    (h : ∀ r ∈ rs, ∀ x y : i.Object, i.objectProperties r.1 x y)
    (x y : i.Object) :
    objPath i rs x y := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rest =>
    induction rest generalizing r x with
    | nil =>
      refine ⟨y, ?_, rfl⟩
      have hr := h r (List.mem_cons_self ..)
      rcases r with ⟨name, _ | _⟩
      · exact hr x y
      · exact hr y x
    | cons r₂ tail ih =>
      obtain ⟨z⟩ := i.objectNonempty
      refine ⟨z, ?_, ih (r := r₂) (hne := List.cons_ne_nil r₂ tail)
        (h := fun s hs => h s (List.mem_cons_of_mem _ hs)) (x := z)⟩
      have hr := h r (List.mem_cons_self ..)
      rcases r with ⟨name, _ | _⟩
      · exact hr x z
      · exact hr z x

private theorem univRolesStep_universal {p : Problem} {i : Interpretation datatypeMap}
    (hm : p.Models i) {cur : List IRI}
    (hcur : ∀ r ∈ cur, ∀ x y : i.Object, i.objectProperties r x y) :
    ∀ r ∈ univRolesStep p cur, ∀ x y : i.Object, i.objectProperties r x y := by
  intro r hr x y
  have hm' := List.mem_eraseDups.mp hr
  rcases List.mem_append.mp hm' with h1 | hch
  · rcases List.mem_append.mp h1 with hmem | hru
    · exact hcur r hmem x y
    · obtain ⟨rs, hrs, heq⟩ := List.mem_filterMap.mp hru
      by_cases hc : cur.contains rs.1.1 = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at heq
        subst heq
        have h1u : ∀ a b : i.Object, holdsOriented i rs.1 a b := by
          intro a b
          have hu := hcur rs.1.1 (List.contains_iff_mem.mp hc)
          rcases h1r : rs.1 with ⟨name, _ | _⟩
          · rw [h1r] at hu; exact hu a b
          · rw [h1r] at hu; exact hu b a
        rcases h2 : rs.2 with ⟨name2, _ | _⟩
        · have h := hm.rules rs hrs x y (h1u x y)
          simpa [holdsOriented, h2] using h
        · have h := hm.rules rs hrs y x (h1u y x)
          simpa [holdsOriented, h2] using h
      · simp only [hc] at heq; cases heq
  · obtain ⟨c, hc, heq⟩ := List.mem_filterMap.mp hch
    by_cases hb : (!c.body.isEmpty && c.body.all (fun s => cur.contains s.1)) = true
    · simp only [hb, ↓reduceIte, Option.some.injEq] at heq
      subst heq
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true, List.contains_iff_mem] at hb
      have hall : ∀ s ∈ c.body, ∀ a b : i.Object, i.objectProperties s.1 a b :=
        fun s hs => hcur s.1 (hb.2 s hs)
      exact hm.chains c hc x y (objPath_of_all_universal i hb.1 hall x y)
    · simp only [hb] at heq; cases heq

private theorem univRolesLoop_universal {p : Problem} {i : Interpretation datatypeMap}
    (hm : p.Models i) (n : Nat) {cur : List IRI}
    (hcur : ∀ r ∈ cur, ∀ x y : i.Object, i.objectProperties r x y) :
    ∀ r ∈ univRolesLoop p n cur, ∀ x y : i.Object, i.objectProperties r x y := by
  induction n generalizing cur with
  | zero => exact hcur
  | succ n ih =>
    dsimp only [univRolesLoop]
    split
    · exact hcur
    · exact ih (univRolesStep_universal hm hcur)

theorem univRoles_universal {p : Problem} {i : Interpretation datatypeMap} (hm : p.Models i) :
    ∀ r ∈ univRoles p, ∀ x y : i.Object, i.objectProperties r x y := by
  apply univRolesLoop_universal hm
  intro r hr x y
  rw [List.mem_singleton.mp hr]
  exact i.topObjectExt x y

private theorem univRolesStep_subset_cand (p : Problem) {cur : List IRI}
    (hsub : ∀ r ∈ cur, r ∈ univRolesCand p) :
    ∀ r ∈ univRolesStep p cur, r ∈ univRolesCand p := by
  intro r hr
  have hm := List.mem_eraseDups.mp hr
  rcases List.mem_append.mp hm with h1 | hch
  · rcases List.mem_append.mp h1 with hmem | hru
    · exact hsub r hmem
    · obtain ⟨rs, hrs, heq⟩ := List.mem_filterMap.mp hru
      split at heq
      · cases heq
        exact List.mem_eraseDups.mpr (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨rs, hrs, rfl⟩)))
      · cases heq
  · obtain ⟨c, hc, heq⟩ := List.mem_filterMap.mp hch
    split at heq
    · cases heq
      exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    · cases heq

private theorem countP_lt_of_new {α : Type} [DecidableEq α] {xs a b : List α}
    (hsub : ∀ x ∈ a, x ∈ b) {y : α} (hyx : y ∈ xs) (hyb : y ∈ b) (hya : y ∉ a) :
    xs.countP (fun x => a.contains x) < xs.countP (fun x => b.contains x) := by
  induction xs with
  | nil => simp at hyx
  | cons z rest ih =>
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hyx with rfl | hrest
    · have hza : a.contains y = false := Bool.eq_false_iff.mpr (fun h => hya (List.contains_iff_mem.mp h))
      have hzb : b.contains y = true := List.contains_iff_mem.mpr hyb
      have hle : rest.countP (fun x => a.contains x) ≤ rest.countP (fun x => b.contains x) :=
        List.countP_mono_left fun x _ hx => List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp hx))
      simp only [hza, hzb, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hlt := ih hrest
      have hstep : (if a.contains z = true then 1 else 0) ≤ (if b.contains z = true then 1 else 0) := by
        cases hza : a.contains z
        · simp
        · have hzb : z ∈ b := hsub z (List.contains_iff_mem.mp hza)
          simp [hzb]
      omega

private theorem univRolesLoop_fixed (p : Problem) (n : Nat) {cur : List IRI}
    (hsub : ∀ r ∈ cur, r ∈ univRolesCand p)
    (hlen : (univRolesCand p).length - (univRolesCand p).countP (fun x => cur.contains x) ≤ n) :
    ∀ r ∈ univRolesStep p (univRolesLoop p n cur), r ∈ univRolesLoop p n cur := by
  induction n generalizing cur with
  | zero =>
    have hge : (univRolesCand p).length ≤ (univRolesCand p).countP (fun x => cur.contains x) := by omega
    intro r hr
    have hrc : r ∈ univRolesCand p := univRolesStep_subset_cand p hsub r hr
    exact Classical.byContradiction fun hnr => by
      have hlt : (univRolesCand p).countP (fun x => cur.contains x) < (univRolesCand p).length := by
        have := countP_lt_of_new (xs := univRolesCand p) (a := cur) (b := r :: cur)
          (fun x hx => List.mem_cons_of_mem _ hx) hrc (List.mem_cons_self ..) hnr
        have hle := List.countP_le_length (p := fun x => (r :: cur).contains x) (l := univRolesCand p)
        omega
      omega
  | succ n ih =>
    dsimp only [univRolesLoop]
    split
    · rename_i hfix
      intro r hr
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hfix r hr)
    · rename_i hnofix
      have hex : ∃ y ∈ univRolesStep p cur, y ∉ cur :=
        Classical.byContradiction fun hall => by
          apply hnofix
          apply List.all_eq_true.mpr
          intro y hy
          exact Classical.byContradiction fun hny =>
            hall ⟨y, hy, fun hm => hny (List.contains_iff_mem.mpr hm)⟩
      obtain ⟨y, hyStep, hyNot⟩ := hex
      have hlt := countP_lt_of_new (xs := univRolesCand p) (a := cur) (b := univRolesStep p cur)
        (fun x hx => mem_univRolesStep_of_mem hx)
        (univRolesStep_subset_cand p hsub y hyStep) hyStep hyNot
      exact ih (univRolesStep_subset_cand p hsub) (by omega)

theorem univRoles_closed_rules {p : Problem} {rs : OrientedRole × OrientedRole}
    (hrs : rs ∈ p.rules) (h1 : rs.1.1 ∈ univRoles p) : rs.2.1 ∈ univRoles p := by
  have hsub0 : ∀ r ∈ [topObjectProperty], r ∈ univRolesCand p := by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_cons_self ..))
  have hfix := univRolesLoop_fixed p (univRolesCand p).length hsub0 (Nat.sub_le _ _)
  unfold univRoles at h1 ⊢
  apply hfix
  apply List.mem_eraseDups.mpr
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_filterMap.mpr ⟨rs, hrs, by simp [h1]⟩

theorem univRoles_closed_chains {p : Problem} {c : Chain}
    (hc : c ∈ p.chains) (hne : c.body ≠ []) (hall : ∀ r ∈ c.body, r.1 ∈ univRoles p) :
    c.head ∈ univRoles p := by
  have hsub0 : ∀ r ∈ [topObjectProperty], r ∈ univRolesCand p := by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_cons_self ..))
  have hfix := univRolesLoop_fixed p (univRolesCand p).length hsub0 (Nat.sub_le _ _)
  unfold univRoles at hall ⊢
  apply hfix
  apply List.mem_eraseDups.mpr
  apply List.mem_append_right
  refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
  have hcond : (!c.body.isEmpty && c.body.all (fun r => (univRolesLoop p (univRolesCand p).length [topObjectProperty]).contains r.1)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, List.contains_iff_mem]
    exact ⟨hne, hall⟩
  simp only [hcond, ↓reduceIte]

private theorem reachable_of_name_rule {rules : RoleTheory} {rs : OrientedRole × OrientedRole}
    (hrs : rs ∈ rules) (b : Bool) :
    ∃ b', Sabrina.RoleChains.SimpleRoles.Reachable rules (rs.1.1, b) (rs.2.1, b') := by
  rcases rs with ⟨⟨n1, o1⟩, ⟨n2, o2⟩⟩
  by_cases hb : b = o1
  · subst hb
    exact ⟨o2, .step (List.mem_append_left _ hrs)⟩
  · have hne : b = !o1 := by cases b <;> cases o1 <;> simp_all
    subst hne
    refine ⟨!o2, .step (List.mem_append_right _ ?_)⟩
    exact List.mem_map.mpr ⟨((n1, o1), (n2, o2)), hrs, rfl⟩

theorem univRoles_nonSimple {p : Problem} (hlen : ∀ c ∈ p.chains, 2 ≤ c.body.length) :
    ∀ u ∈ univRoles p, ∀ b : Bool,
      ¬ Sabrina.RoleChains.SimpleRoles.Simple p.rules p.chains (u, b) := by
  have hstep : ∀ cur : List IRI,
      (∀ u ∈ cur, ∀ b, ¬ Sabrina.RoleChains.SimpleRoles.Simple p.rules p.chains (u, b)) →
      ∀ u ∈ univRolesStep p cur, ∀ b, ¬ Sabrina.RoleChains.SimpleRoles.Simple p.rules p.chains (u, b) := by
    intro cur hcur u hu b hsim
    have hm := List.mem_eraseDups.mp hu
    rcases List.mem_append.mp hm with h1 | hch
    · rcases List.mem_append.mp h1 with hmem | hru
      · exact hcur u hmem b hsim
      · obtain ⟨rs, hrs, heq⟩ := List.mem_filterMap.mp hru
        split at heq
        · rename_i hmem1
          cases heq
          obtain ⟨b', hreach⟩ := reachable_of_name_rule hrs true
          have hreach' : ∃ b0, Sabrina.RoleChains.SimpleRoles.Reachable p.rules (rs.1.1, b0) (rs.2.1, b) := by
            by_cases hbb : b = b'
            · exact ⟨true, hbb ▸ hreach⟩
            · have hflip := Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mp
                (Sabrina.RoleChains.SimpleRoles.below_iff_reachable.mpr hreach).flip
              have heqB : (!b') = b := by cases b <;> cases b' <;> simp_all
              exact ⟨false, by simpa [Sabrina.ALC.converse, heqB] using hflip⟩
          obtain ⟨b0, hr0⟩ := hreach'
          apply hcur rs.1.1 (List.contains_iff_mem.mp hmem1) b0
          intro s hs hc
          exact hsim s (hs.trans hr0) hc
        · cases heq
    · obtain ⟨c, hc, heq⟩ := List.mem_filterMap.mp hch
      split at heq
      · cases heq
        exact hsim (c.head, b) (.refl _) (Or.inr ⟨c, hc, hlen c hc, rfl⟩)
      · cases heq
  have hloop : ∀ n cur,
      (∀ u ∈ cur, ∀ b, ¬ Sabrina.RoleChains.SimpleRoles.Simple p.rules p.chains (u, b)) →
      ∀ u ∈ univRolesLoop p n cur, ∀ b, ¬ Sabrina.RoleChains.SimpleRoles.Simple p.rules p.chains (u, b) := by
    intro n
    induction n with
    | zero => intro cur hcur; exact hcur
    | succ n ih =>
      intro cur hcur
      dsimp only [univRolesLoop]
      split
      · exact hcur
      · exact ih _ (hstep cur hcur)
  apply hloop
  intro u hu b hsim
  rw [List.mem_singleton.mp hu] at hsim
  exact hsim (topObjectProperty, b) (.refl _) (Or.inl (List.mem_cons_self ..))

def canonUniv (U : List IRI) (r : IRI) : IRI :=
  if U.contains r then topObjectProperty else r

def canonUnivOriented (U : List IRI) (r : OrientedRole) : OrientedRole :=
  (canonUniv U r.1, r.2)

def Concept.canonUniv (U : List IRI) : Concept → Concept
  | .self r b => .self (canonUnivOriented U r) b
  | .conj a b => .conj (a.canonUniv U) (b.canonUniv U)
  | .disj a b => .disj (a.canonUniv U) (b.canonUniv U)
  | .some r c => .some (canonUnivOriented U r) (c.canonUniv U)
  | .all r c => .all (canonUnivOriented U r) (c.canonUniv U)
  | .min n r c => .min n (canonUnivOriented U r) (c.canonUniv U)
  | .max n r c => .max n (canonUnivOriented U r) (c.canonUniv U)
  | c => c

/-- Collapse every object property in `univRoles p` to `topObjectProperty`.
If `bottomObjectProperty ∈ univRoles p`, the problem is immediately unsatisfiable
and lowers to `{ root := .bottom }`. -/
def Problem.collapseUnivRoles (p : Problem) : Problem :=
  let U := univRoles p
  if U.contains bottomObjectProperty then
    { root := .bottom }
  else
    { p with
      tbox := p.tbox.map fun q => ⟨q.sub.canonUniv U, q.sup.canonUniv U⟩
      rules := p.rules.map fun rs => (canonUnivOriented U rs.1, canonUnivOriented U rs.2)
      chains := p.chains.map fun c => ⟨c.body.map (canonUnivOriented U), canonUniv U c.head⟩
      chars := {
        reflexive := p.chars.reflexive.map (canonUniv U)
        irreflexive := p.chars.irreflexive.map (canonUniv U)
        asymmetric := p.chars.asymmetric.map (canonUniv U)
        disjoint := p.chars.disjoint.map fun rs => (canonUnivOriented U rs.1, canonUnivOriented U rs.2) }
      keys := p.keys.map fun k =>
        { k with cls := k.cls.canonUniv U, objProps := k.objProps.map (canonUnivOriented U) }
      classAssertions := p.classAssertions.map fun (a, c) => (a, c.canonUniv U)
      objAssertions := p.objAssertions.map fun (r, a, b) => (canonUniv U r, a, b)
      negObjAssertions := p.negObjAssertions.map fun (r, a, b) => (canonUniv U r, a, b)
      root := p.root.canonUniv U }

/-- Expand an interpretation by making every role in `U` universal (assuming
`bottomObjectProperty ∉ U`). Preserves `Object`, `Data`, `classes`,
`dataProperties`, `individuals`, `datatypes`, `literalValue`, and `named`
definitionally. -/
def withUniversalRoles (i : Interpretation datatypeMap) (U : List IRI)
    (hnb : bottomObjectProperty ∉ U) : Interpretation datatypeMap :=
  { i with
    objectProperties := fun r x y => if U.contains r then True else i.objectProperties r x y
    topObjectExt := fun x y => by
      by_cases ht : topObjectProperty ∈ U
      · simp [ht]
      · simp [ht, i.topObjectExt x y]
    bottomObjectExt := fun x y => by
      simp [hnb, i.bottomObjectExt x y] }

private theorem dataHolds_withUniversalRoles_iff (i : Interpretation datatypeMap)
    (U : List IRI) (hnb : bottomObjectProperty ∉ U) (y : i.Data) (d : DataRange) :
    dataHolds (withUniversalRoles i U hnb) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ iha ihb => exact and_congr iha ihb
  | union _ _ iha ihb => exact or_congr iha ihb

private theorem holdsOriented_canonUniv_iff_same (i : Interpretation datatypeMap)
    {U : List IRI} (hu : ∀ r ∈ U, ∀ x y : i.Object, i.objectProperties r x y)
    (r : OrientedRole) (x y : i.Object) :
    holdsOriented i (canonUnivOriented U r) x y ↔ holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩ <;>
  · unfold canonUnivOriented canonUniv holdsOriented
    by_cases hc : name ∈ U
    · simp [hc, i.topObjectExt, hu name hc]
    · simp [hc]

private theorem objPath_canonUniv_iff_same (i : Interpretation datatypeMap)
    {U : List IRI} (hu : ∀ r ∈ U, ∀ x y : i.Object, i.objectProperties r x y)
    (rs : List OrientedRole) (x y : i.Object) :
    objPath i (rs.map (canonUnivOriented U)) x y ↔ objPath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    simp only [List.map_cons, objPath, holdsOriented_canonUniv_iff_same i hu, ih]

private theorem holds_canonUniv_iff_same (i : Interpretation datatypeMap)
    {U : List IRI} (hu : ∀ r ∈ U, ∀ x y : i.Object, i.objectProperties r x y)
    (x : i.Object) (c : Concept) :
    holds i x (c.canonUniv U) ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom | lit | nom | dataSome | dataAll | dataValue | dataMin | dataMax => rfl
  | self r b =>
    cases b <;> simp [Concept.canonUniv, holds, holdsOriented_canonUniv_iff_same i hu]
  | conj a b iha ihb => exact and_congr (iha x) (ihb x)
  | disj a b iha ihb => exact or_congr (iha x) (ihb x)
  | some r c ih =>
    simp only [Concept.canonUniv, holds, holdsOriented_canonUniv_iff_same i hu, ih]
  | all r c ih =>
    simp only [Concept.canonUniv, holds, holdsOriented_canonUniv_iff_same i hu, ih]
  | min n r c ih =>
    simpa only [Concept.canonUniv, holds] using
      atLeast_congr' (fun y => and_congr (holdsOriented_canonUniv_iff_same i hu r x y) (ih y)) n
  | max n r c ih =>
    simpa only [Concept.canonUniv, holds] using
      not_congr (atLeast_congr' (fun y => and_congr (holdsOriented_canonUniv_iff_same i hu r x y) (ih y)) (n + 1))

private theorem objProp_withUniversalRoles_iff (i : Interpretation datatypeMap)
    (U : List IRI) (hnb : bottomObjectProperty ∉ U) (r : IRI) (x y : i.Object) :
    (withUniversalRoles i U hnb).objectProperties r x y ↔
      i.objectProperties (canonUniv U r) x y := by
  unfold withUniversalRoles canonUniv
  by_cases hc : r ∈ U
  · simp [hc, i.topObjectExt]
  · simp [hc]

private theorem holdsOriented_withUniversalRoles_iff (i : Interpretation datatypeMap)
    (U : List IRI) (hnb : bottomObjectProperty ∉ U) (r : OrientedRole) (x y : i.Object) :
    holdsOriented (withUniversalRoles i U hnb) r x y ↔
      holdsOriented i (canonUnivOriented U r) x y := by
  rcases r with ⟨name, _ | _⟩
  · exact objProp_withUniversalRoles_iff i U hnb name x y
  · exact objProp_withUniversalRoles_iff i U hnb name y x

private theorem objPath_withUniversalRoles_iff (i : Interpretation datatypeMap)
    (U : List IRI) (hnb : bottomObjectProperty ∉ U) (rs : List OrientedRole) (x y : i.Object) :
    objPath (withUniversalRoles i U hnb) rs x y ↔
      objPath i (rs.map (canonUnivOriented U)) x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    change (∃ z : i.Object, holdsOriented (withUniversalRoles i U hnb) r x z ∧
        objPath (withUniversalRoles i U hnb) tail z y) ↔
      ∃ z : i.Object, holdsOriented i (canonUnivOriented U r) x z ∧
        objPath i (tail.map (canonUnivOriented U)) z y
    exact exists_congr fun z =>
      and_congr (holdsOriented_withUniversalRoles_iff i U hnb r x z) (ih z)

private theorem holds_withUniversalRoles_iff (i : Interpretation datatypeMap)
    (U : List IRI) (hnb : bottomObjectProperty ∉ U) (x : i.Object) (c : Concept) :
    holds (withUniversalRoles i U hnb) x c ↔ holds i x (c.canonUniv U) := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b => cases b <;> rfl
  | nom _ b => cases b <;> rfl
  | dataValue _ _ b => cases b <;> rfl
  | dataSome r d =>
    change (∃ y : i.Data, i.dataProperties r x y ∧ dataHolds (withUniversalRoles i U hnb) y d) ↔
      ∃ y : i.Data, i.dataProperties r x y ∧ dataHolds i y d
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withUniversalRoles_iff i U hnb y d)
  | dataAll r d =>
    change (∀ y : i.Data, i.dataProperties r x y → dataHolds (withUniversalRoles i U hnb) y d) ↔
      ∀ y : i.Data, i.dataProperties r x y → dataHolds i y d
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withUniversalRoles_iff i U hnb y d)
  | dataMin n r d =>
    change AtLeast n (fun y : i.Data => i.dataProperties r x y ∧ dataHolds (withUniversalRoles i U hnb) y d) ↔
      AtLeast n (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_withUniversalRoles_iff i U hnb y d)) n
  | dataMax n r d =>
    change (¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧ dataHolds (withUniversalRoles i U hnb) y d)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact not_congr (atLeast_congr'
      (fun y => and_congr Iff.rfl (dataHolds_withUniversalRoles_iff i U hnb y d)) (n + 1))
  | self r b =>
    cases b <;> simp [Concept.canonUniv, holds, holdsOriented_withUniversalRoles_iff i U hnb]
  | conj a b iha ihb => exact and_congr (iha x) (ihb x)
  | disj a b iha ihb => exact or_congr (iha x) (ihb x)
  | some r c ih =>
    change (∃ y : i.Object, holdsOriented (withUniversalRoles i U hnb) r x y ∧
        holds (withUniversalRoles i U hnb) y c) ↔
      ∃ y : i.Object, holdsOriented i (canonUnivOriented U r) x y ∧ holds i y (c.canonUniv U)
    exact exists_congr fun y =>
      and_congr (holdsOriented_withUniversalRoles_iff i U hnb r x y) (ih y)
  | all r c ih =>
    change (∀ y : i.Object, holdsOriented (withUniversalRoles i U hnb) r x y →
        holds (withUniversalRoles i U hnb) y c) ↔
      ∀ y : i.Object, holdsOriented i (canonUnivOriented U r) x y → holds i y (c.canonUniv U)
    exact forall_congr' fun y =>
      imp_congr (holdsOriented_withUniversalRoles_iff i U hnb r x y) (ih y)
  | min n r c ih =>
    change AtLeast n (fun y : i.Object => holdsOriented (withUniversalRoles i U hnb) r x y ∧
        holds (withUniversalRoles i U hnb) y c) ↔
      AtLeast n (fun y : i.Object => holdsOriented i (canonUnivOriented U r) x y ∧ holds i y (c.canonUniv U))
    exact atLeast_congr' (fun y => and_congr (holdsOriented_withUniversalRoles_iff i U hnb r x y) (ih y)) n
  | max n r c ih =>
    change (¬ AtLeast (n + 1) (fun y : i.Object => holdsOriented (withUniversalRoles i U hnb) r x y ∧
        holds (withUniversalRoles i U hnb) y c)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Object => holdsOriented i (canonUnivOriented U r) x y ∧ holds i y (c.canonUniv U))
    exact not_congr (atLeast_congr'
      (fun y => and_congr (holdsOriented_withUniversalRoles_iff i U hnb r x y) (ih y)) (n + 1))

theorem Problem.collapseUnivRoles_sat_iff (p : Problem) :
    p.collapseUnivRoles.Sat ↔ p.Sat := by
  unfold Problem.collapseUnivRoles
  by_cases hbot : (univRoles p).contains bottomObjectProperty = true
  · simp only [hbot, ↓reduceIte]
    constructor
    · rintro ⟨i, _, x, hx⟩; cases hx
    · rintro ⟨i, hm, x, _⟩
      have hu := univRoles_universal hm bottomObjectProperty (List.contains_iff_mem.mp hbot) x x
      exact (i.bottomObjectExt x x hu).elim
  · simp only [hbot, Bool.false_eq_true, ↓reduceIte]
    have hnb : bottomObjectProperty ∉ univRoles p := fun hm =>
      hbot (List.contains_iff_mem.mpr hm)
    constructor
    · rintro ⟨i, hm, x₀, hroot⟩
      let U := univRoles p
      let j := withUniversalRoles i U hnb
      have hobj (r : IRI) (x y : i.Object) :
          j.objectProperties r x y ↔ i.objectProperties (canonUniv U r) x y :=
        objProp_withUniversalRoles_iff i U hnb r x y
      refine ⟨j, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
        ?_, ?_, ?_, ?_, ?_, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩,
        x₀, (holds_withUniversalRoles_iff i U hnb x₀ p.root).mpr hroot⟩
      · intro q hq x hx
        have h1 := hm.tbox _ (List.mem_map_of_mem hq) x ((holds_withUniversalRoles_iff i U hnb x q.sub).mp hx)
        exact (holds_withUniversalRoles_iff i U hnb x q.sup).mpr h1
      · intro rs hrs x y hxy
        have h1 := hm.rules _ (List.mem_map_of_mem hrs) x y
          ((holdsOriented_withUniversalRoles_iff i U hnb rs.1 x y).mp hxy)
        exact (holdsOriented_withUniversalRoles_iff i U hnb rs.2 x y).mpr h1
      · intro c hc x y hp
        have h1 := hm.chains _ (List.mem_map_of_mem hc) x y
          ((objPath_withUniversalRoles_iff i U hnb c.body x y).mp hp)
        exact (hobj c.head x y).mpr h1
      · intro r hr x
        exact (hobj r x x).mpr (hm.reflexive _ (List.mem_map_of_mem hr) x)
      · intro r hr x h
        exact hm.irreflexive _ (List.mem_map_of_mem hr) x ((hobj r x x).mp h)
      · intro r hr x y h1 h2
        exact hm.asymmetric _ (List.mem_map_of_mem hr) x y ((hobj r x y).mp h1) ((hobj r y x).mp h2)
      · intro rs hrs x y ⟨h1, h2⟩
        exact hm.disjoint _ (List.mem_map_of_mem hrs) x y
          ⟨(holdsOriented_withUniversalRoles_iff i U hnb rs.1 x y).mp h1,
           (holdsOriented_withUniversalRoles_iff i U hnb rs.2 x y).mp h2⟩
      · intro rd hrd x y hxy
        exact (dataHolds_withUniversalRoles_iff i U hnb y rd.2).mpr (hm.dataRanges rd hrd x y hxy)
      · intro k hk x y hx hy hnx hny ho hd
        refine hm.keys _ (List.mem_map_of_mem hk) x y
          ((holds_withUniversalRoles_iff i U hnb x k.cls).mp hx)
          ((holds_withUniversalRoles_iff i U hnb y k.cls).mp hy)
          hnx hny ?_ hd
        intro r hr
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
        obtain ⟨z, hnz, hxz, hyz⟩ := ho r₀ hr₀
        exact ⟨z, hnz,
          (holdsOriented_withUniversalRoles_iff i U hnb r₀ x z).mp hxz,
          (holdsOriented_withUniversalRoles_iff i U hnb r₀ y z).mp hyz⟩
      · intro ac hac
        exact (holds_withUniversalRoles_iff i U hnb _ ac.2).mpr (hm.classAssertions _ (List.mem_map_of_mem hac))
      · intro rab hrab
        exact (hobj rab.1 _ _).mpr (hm.objAssertions _ (List.mem_map_of_mem hrab))
      · intro rab hrab h
        exact hm.negObjAssertions _ (List.mem_map_of_mem hrab) ((hobj rab.1 _ _).mp h)
    · rintro ⟨i, hm, x₀, hroot⟩
      let U := univRoles p
      have hu : ∀ r ∈ U, ∀ x y : i.Object, i.objectProperties r x y := univRoles_universal hm
      have hobj (r : IRI) (x y : i.Object) :
          i.objectProperties (canonUniv U r) x y ↔ i.objectProperties r x y := by
        unfold canonUniv
        by_cases hc : r ∈ U
        · simp [hc, i.topObjectExt, hu r hc]
        · simp [hc]
      refine ⟨i, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
        hm.dataRanges, ?_, ?_, ?_, ?_, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩, x₀, (holds_canonUniv_iff_same i hu x₀ p.root).mpr hroot⟩
      · intro q hq x hx
        obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
        exact (holds_canonUniv_iff_same i hu x q₀.sup).mpr
          (hm.tbox q₀ hq₀ x ((holds_canonUniv_iff_same i hu x q₀.sub).mp hx))
      · intro rs hrs x y hxy
        obtain ⟨rs₀, hrs₀, rfl⟩ := List.mem_map.mp hrs
        exact (holdsOriented_canonUniv_iff_same i hu rs₀.2 x y).mpr
          (hm.rules rs₀ hrs₀ x y ((holdsOriented_canonUniv_iff_same i hu rs₀.1 x y).mp hxy))
      · intro c hc x y hp
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
        exact (hobj c₀.head x y).mpr
          (hm.chains c₀ hc₀ x y ((objPath_canonUniv_iff_same i hu c₀.body x y).mp hp))
      · intro r hr x
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
        exact (hobj r₀ x x).mpr (hm.reflexive r₀ hr₀ x)
      · intro r hr x h
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
        exact hm.irreflexive r₀ hr₀ x ((hobj r₀ x x).mp h)
      · intro r hr x y h1 h2
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
        exact hm.asymmetric r₀ hr₀ x y ((hobj r₀ x y).mp h1) ((hobj r₀ y x).mp h2)
      · intro rs hrs x y ⟨h1, h2⟩
        obtain ⟨rs₀, hrs₀, rfl⟩ := List.mem_map.mp hrs
        exact hm.disjoint rs₀ hrs₀ x y
          ⟨(holdsOriented_canonUniv_iff_same i hu rs₀.1 x y).mp h1,
           (holdsOriented_canonUniv_iff_same i hu rs₀.2 x y).mp h2⟩
      · intro k hk x y hx hy hnx hny ho hd
        obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.mp hk
        refine hm.keys k₀ hk₀ x y
          ((holds_canonUniv_iff_same i hu x k₀.cls).mp hx)
          ((holds_canonUniv_iff_same i hu y k₀.cls).mp hy)
          hnx hny ?_ hd
        intro r hr
        obtain ⟨z, hnz, hxz, hyz⟩ := ho (canonUnivOriented U r) (List.mem_map_of_mem hr)
        exact ⟨z, hnz,
          (holdsOriented_canonUniv_iff_same i hu r x z).mp hxz,
          (holdsOriented_canonUniv_iff_same i hu r y z).mp hyz⟩
      · intro ac hac
        obtain ⟨ac₀, hac₀, rfl⟩ := List.mem_map.mp hac
        exact (holds_canonUniv_iff_same i hu _ ac₀.2).mpr (hm.classAssertions ac₀ hac₀)
      · intro rab hrab
        obtain ⟨rab₀, hrab₀, rfl⟩ := List.mem_map.mp hrab
        exact (hobj rab₀.1 _ _).mpr (hm.objAssertions rab₀ hrab₀)
      · intro rab hrab h
        obtain ⟨rab₀, hrab₀, rfl⟩ := List.mem_map.mp hrab
        exact hm.negObjAssertions rab₀ hrab₀ ((hobj rab₀.1 _ _).mp h)

/-! ### 3. Model-preserving elimination of non-chain `owl:topObjectProperty` axioms -/

def isTopObj (r : IRI) : Bool := r == topObjectProperty

inductive TopRed where
  | keep
  | discard
  | forbid (c : Concept)

def topRetained (f : α → TopRed) (xs : List α) : List α :=
  xs.filter fun a => match f a with | .keep => true | _ => false

def topProhibs (f : α → TopRed) (xs : List α) : List Concept :=
  xs.filterMap fun a => match f a with | .forbid c => Option.some c | _ => none

private theorem topRed_iff (i : Interpretation datatypeMap) (f : α → TopRed)
    (xs : List α) (P : α → Prop)
    (h : ∀ a, P a ↔ match f a with
      | .keep => P a
      | .discard => True
      | .forbid c => ∀ x, ¬ holds i x c) :
    (∀ a ∈ xs, P a) ↔
      (∀ a ∈ topRetained f xs, P a) ∧ ∀ c ∈ topProhibs f xs, ∀ x, ¬ holds i x c := by
  constructor
  · intro hp
    refine ⟨fun a ha => hp a (List.mem_filter.mp ha).1, ?_⟩
    intro c hc
    obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hc
    have hpa := (h a).mp (hp a ha)
    cases hf : f a <;> simp [hf] at he hpa
    exact he ▸ hpa
  · rintro ⟨hk, hf⟩ a ha
    apply (h a).mpr
    cases he : f a with
    | keep => exact hk a (List.mem_filter.mpr ⟨ha, by simp [he]⟩)
    | discard => trivial
    | forbid c => exact hf c (List.mem_filterMap.mpr ⟨a, ha, by simp [he]⟩)

def topDiscardWhen (bad : α → Bool) (a : α) : TopRed :=
  if bad a then .discard else .keep

def topForbidWhen (bad : α → Bool) (a : α) : TopRed :=
  if bad a then .forbid .top else .keep

def topDisjRed (rs : OrientedRole × OrientedRole) : TopRed :=
  if isTopObj rs.1.1 && isTopObj rs.2.1 then .forbid .top
  else if isTopObj rs.1.1 then .forbid (.some rs.2 .top)
  else if isTopObj rs.2.1 then .forbid (.some rs.1 .top)
  else .keep

/-- Eliminate every non-chain-body occurrence of `owl:topObjectProperty` from
role axioms, characteristics, `HasKey`, and object property assertions while
preserving every interpretation identically. -/
def Problem.lowerTopRoleAxioms (p : Problem) : Problem :=
  let extra :=
    topProhibs (topForbidWhen isTopObj) p.chars.irreflexive ++
    topProhibs (topForbidWhen isTopObj) p.chars.asymmetric ++
    topProhibs topDisjRed p.chars.disjoint ++
    topProhibs (topForbidWhen fun e : IRI × Individual × Individual => isTopObj e.1) p.negObjAssertions
  { p with
    tbox := p.tbox ++ extra.map fun c => ⟨c, .bottom⟩
    rules := topRetained (topDiscardWhen fun rs => isTopObj rs.2.1) p.rules
    chains := topRetained (topDiscardWhen fun c => isTopObj c.head) p.chains
    chars := {
      reflexive := topRetained (topDiscardWhen isTopObj) p.chars.reflexive
      irreflexive := topRetained (topForbidWhen isTopObj) p.chars.irreflexive
      asymmetric := topRetained (topForbidWhen isTopObj) p.chars.asymmetric
      disjoint := topRetained topDisjRed p.chars.disjoint }
    keys := p.keys.map fun k => { k with objProps := k.objProps.filter (fun r => !isTopObj r.1) }
    objAssertions := topRetained (topDiscardWhen fun e => isTopObj e.1) p.objAssertions
    negObjAssertions := topRetained (topForbidWhen fun e => isTopObj e.1) p.negObjAssertions }

private theorem topDiscardWhen_iff (bad : α → Bool) (xs : List α) (P : α → Prop)
    (h : ∀ a, bad a = true → P a) :
    (∀ a ∈ xs, P a) ↔ ∀ a ∈ topRetained (topDiscardWhen bad) xs, P a := by
  constructor
  · intro hp a ha; exact hp a (List.mem_filter.mp ha).1
  · intro hp a ha
    by_cases hb : bad a = true
    · exact h a hb
    · exact hp a (List.mem_filter.mpr ⟨ha, by simp [topDiscardWhen, hb]⟩)

private theorem topForbidWhen_iff (i : Interpretation datatypeMap)
    (bad : α → Bool) (P : α → Prop) (a : α) (h : bad a = true → ¬ P a) :
    P a ↔ match topForbidWhen bad a with
      | .keep => P a
      | .discard => True
      | .forbid c => ∀ x, ¬ holds i x c := by
  by_cases hb : bad a = true
  · simp only [topForbidWhen, hb, ↓reduceIte]
    exact ⟨fun hp => (h hb hp).elim, fun hf => i.objectNonempty.elim fun x => (hf x trivial).elim⟩
  · simp [topForbidWhen, hb]

private theorem topDisjRed_iff (i : Interpretation datatypeMap) (rs : OrientedRole × OrientedRole) :
    (∀ x y, ¬ (holdsOriented i rs.1 x y ∧ holdsOriented i rs.2 x y)) ↔
    match topDisjRed rs with
    | .keep => ∀ x y, ¬ (holdsOriented i rs.1 x y ∧ holdsOriented i rs.2 x y)
    | .discard => True
    | .forbid c => ∀ x, ¬ holds i x c := by
  by_cases h1 : isTopObj rs.1.1 = true
  · have ht1 : rs.1.1 = topObjectProperty := beq_iff_eq.mp h1
    by_cases h2 : isTopObj rs.2.1 = true
    · have ht2 : rs.2.1 = topObjectProperty := beq_iff_eq.mp h2
      simp only [topDisjRed, h1, h2, Bool.and_self, ↓reduceIte, holds]
      exact ⟨fun h x _ => h x x ⟨topRole_holds' i rs.1 ht1 x x, topRole_holds' i rs.2 ht2 x x⟩,
             fun hf x _ _ => hf x trivial⟩
    · simp only [topDisjRed, h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, holds]
      exact ⟨fun h x ⟨y, hy, _⟩ => h x y ⟨topRole_holds' i rs.1 ht1 x y, hy⟩,
             fun h x y ⟨_, h2'⟩ => h x ⟨y, h2', trivial⟩⟩
  · by_cases h2 : isTopObj rs.2.1 = true
    · have ht2 : rs.2.1 = topObjectProperty := beq_iff_eq.mp h2
      simp only [topDisjRed, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, holds]
      exact ⟨fun h x ⟨y, hy, _⟩ => h x y ⟨hy, topRole_holds' i rs.2 ht2 x y⟩,
             fun h x y ⟨h1', _⟩ => h x ⟨y, h1', trivial⟩⟩
    · simp [topDisjRed, h1, h2]

private theorem dropTopKey_iff (i : Interpretation datatypeMap) (k : KeyAxiom) :
    (∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
      (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
      (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) ↔
    (∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
      (∀ r ∈ k.objProps.filter (fun r => !isTopObj r.1),
        ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
      (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) := by
  constructor
  · intro hk x y hx hy hnx hny ho hd
    refine hk x y hx hy hnx hny ?_ hd
    intro r hr
    by_cases ht : isTopObj r.1 = true
    · have htop : r.1 = topObjectProperty := beq_iff_eq.mp ht
      exact ⟨x, hnx, topRole_holds' i r htop x x, topRole_holds' i r htop y x⟩
    · exact ho r (List.mem_filter.mpr ⟨hr, by simp [ht]⟩)
  · intro hk x y hx hy hnx hny ho hd
    exact hk x y hx hy hnx hny (fun r hr => ho r (List.mem_filter.mp hr).1) hd

theorem Problem.lowerTopRoleAxioms_models_iff (p : Problem) (i : Interpretation datatypeMap) :
    p.lowerTopRoleAxioms.Models i ↔ p.Models i := by
  have hrules := topDiscardWhen_iff (fun rs : OrientedRole × OrientedRole => isTopObj rs.2.1)
    p.rules (fun rs => ∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y)
    (fun rs hb x y _ => topRole_holds' i rs.2 (beq_iff_eq.mp hb) x y)
  have hchains := topDiscardWhen_iff (fun c : Chain => isTopObj c.head)
    p.chains (fun c => ∀ x y, objPath i c.body x y → i.objectProperties c.head x y)
    (fun c hb x y _ => by rw [beq_iff_eq.mp hb]; exact i.topObjectExt x y)
  have hrefl := topDiscardWhen_iff isTopObj p.chars.reflexive
    (fun r => ∀ x, i.objectProperties r x x)
    (fun r hb x => by rw [beq_iff_eq.mp hb]; exact i.topObjectExt x x)
  have hirr := topRed_iff i (topForbidWhen isTopObj) p.chars.irreflexive
    (fun r => ∀ x, ¬ i.objectProperties r x x)
    (fun r => topForbidWhen_iff i isTopObj (fun r => ∀ x, ¬ i.objectProperties r x x) r fun hb h =>
      i.objectNonempty.elim fun x => h x (by rw [beq_iff_eq.mp hb]; exact i.topObjectExt x x))
  have hasym := topRed_iff i (topForbidWhen isTopObj) p.chars.asymmetric
    (fun r => ∀ x y, i.objectProperties r x y → ¬ i.objectProperties r y x)
    (fun r => topForbidWhen_iff i isTopObj
      (fun r => ∀ x y, i.objectProperties r x y → ¬ i.objectProperties r y x) r fun hb h =>
      i.objectNonempty.elim fun x =>
        h x x (by rw [beq_iff_eq.mp hb]; exact i.topObjectExt x x)
              (by rw [beq_iff_eq.mp hb]; exact i.topObjectExt x x))
  have hdisj := topRed_iff i topDisjRed p.chars.disjoint
    (fun rs => ∀ x y, ¬ (holdsOriented i rs.1 x y ∧ holdsOriented i rs.2 x y))
    (topDisjRed_iff i)
  have hoa := topDiscardWhen_iff (fun e : IRI × Individual × Individual => isTopObj e.1)
    p.objAssertions (fun e => i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2))
    (fun e hb => by rw [beq_iff_eq.mp hb]; exact i.topObjectExt _ _)
  have hnoa := topRed_iff i (topForbidWhen fun e : IRI × Individual × Individual => isTopObj e.1)
    p.negObjAssertions
    (fun e => ¬ i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2))
    (fun e => topForbidWhen_iff i (fun e => isTopObj e.1)
      (fun e => ¬ i.objectProperties e.1 (i.individuals e.2.1) (i.individuals e.2.2)) e fun hb h =>
      h (by rw [beq_iff_eq.mp hb]; exact i.topObjectExt _ _))
  have hkeys :
      (∀ k ∈ p.keys, ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
        (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
        (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) ↔
      (∀ k ∈ p.lowerTopRoleAxioms.keys, ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
        (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
        (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y) := by
    simp only [Problem.lowerTopRoleAxioms, List.forall_mem_map]
    exact forall_congr' fun k => imp_congr Iff.rfl (dropTopKey_iff i k)
  constructor
  · intro h
    have ht := h.tbox
    simp only [Problem.lowerTopRoleAxioms, List.forall_mem_append, List.forall_mem_map,
      holds, and_assoc] at ht
    obtain ⟨htbox, hpi, hpa, hpd, hpn⟩ := ht
    exact ⟨htbox, hrules.mpr h.rules, hchains.mpr h.chains, hrefl.mpr h.reflexive,
      hirr.mpr ⟨h.irreflexive, hpi⟩, hasym.mpr ⟨h.asymmetric, hpa⟩,
      hdisj.mpr ⟨h.disjoint, hpd⟩, h.subData, h.disjointData, h.funcData, h.dataRanges,
      hkeys.mpr h.keys, h.classAssertions, hoa.mpr h.objAssertions,
      hnoa.mpr ⟨h.negObjAssertions, hpn⟩, h.sameInds, h.diffInds, h.dataAssertions,
      h.negDataAssertions⟩
  · intro h
    obtain ⟨hir1, hpi⟩ := hirr.mp h.irreflexive
    obtain ⟨has1, hpa⟩ := hasym.mp h.asymmetric
    obtain ⟨hdj1, hpd⟩ := hdisj.mp h.disjoint
    obtain ⟨hno1, hpn⟩ := hnoa.mp h.negObjAssertions
    refine ⟨?_, hrules.mp h.rules, hchains.mp h.chains, hrefl.mp h.reflexive,
      hir1, has1, hdj1, h.subData, h.disjointData, h.funcData, h.dataRanges,
      hkeys.mp h.keys, h.classAssertions, hoa.mp h.objAssertions, hno1,
      h.sameInds, h.diffInds, h.dataAssertions, h.negDataAssertions⟩
    simp only [Problem.lowerTopRoleAxioms, List.forall_mem_append, List.forall_mem_map,
      holds, and_assoc]
    exact ⟨h.tbox, hpi, hpa, hpd, hpn⟩

theorem Problem.lowerTopRoleAxioms_sat_iff (p : Problem) :
    p.lowerTopRoleAxioms.Sat ↔ p.Sat :=
  exists_congr fun i => and_congr (p.lowerTopRoleAxioms_models_iff i) Iff.rfl

/-! ### 4. Chain-body universal-role elimination (`lowerTopChains`) -/

def hasTopInBody (c : Chain) : Bool :=
  c.body.any fun r => r.1 == topObjectProperty

private def splitFirst {α : Type} (f : α → Bool) : List α → Option (List α × α × List α)
  | [] => none
  | a :: rest =>
    if f a then Option.some ([], a, rest)
    else match splitFirst f rest with
      | none => none
      | Option.some (pre, x, post) => Option.some (a :: pre, x, post)

private theorem splitFirst_some {α : Type} {f : α → Bool} {xs pre post : List α} {x : α}
    (h : splitFirst f xs = Option.some (pre, x, post)) :
    xs = pre ++ x :: post ∧ f x = true := by
  induction xs generalizing pre with
  | nil => simp [splitFirst] at h
  | cons a rest ih =>
    unfold splitFirst at h
    split at h
    · rename_i hfa
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hfa⟩
    · cases hs : splitFirst f rest with
      | none => simp [hs] at h
      | some triple =>
        rcases triple with ⟨pre', y, post'⟩
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨heq, hfx⟩ := ih hs
        exact ⟨by simp [heq], hfx⟩

private theorem splitFirst_none {α : Type} {f : α → Bool} {xs : List α}
    (h : splitFirst f xs = none) :
    ∀ a ∈ xs, f a = false := by
  induction xs with
  | nil => intro a ha; cases ha
  | cons a rest ih =>
    unfold splitFirst at h
    split at h
    · cases h
    · rename_i hna
      have haf : f a = false := by
        cases hf : f a
        · rfl
        · exact (hna hf).elim
      cases hs : splitFirst f rest with
      | none =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hm
        · exact haf
        · exact ih hs x hm
      | some _ => simp [hs] at h

/-- Split a chain body at every step whose IRI is `topObjectProperty`.
Returns `(prefix_before_first_U, segments_after_first_U)`. -/
def splitAtTop : List OrientedRole → List OrientedRole × List (List OrientedRole)
  | [] => ([], [])
  | r :: rs =>
    let (hd, tl) := splitAtTop rs
    if r.1 == topObjectProperty then ([], hd :: tl)
    else (r :: hd, tl)

private theorem splitAtTop_nil_iff (rs : List OrientedRole) :
    (splitAtTop rs).2 = [] ↔ ∀ r ∈ rs, r.1 ≠ topObjectProperty := by
  induction rs with
  | nil => simp [splitAtTop]
  | cons r rest ih =>
    simp only [splitAtTop]
    by_cases hr : r.1 == topObjectProperty
    · simp only [hr, ↓reduceIte, List.cons_ne_nil, false_iff]
      intro hall
      exact hall r (List.mem_cons_self ..) (beq_iff_eq.mp hr)
    · have hne : r.1 ≠ topObjectProperty := fun he => hr (beq_iff_eq.mpr he)
      simp only [hr, Bool.false_eq_true, ↓reduceIte, ih, List.forall_mem_cons]
      exact ⟨fun h => ⟨hne, h⟩, fun h => h.2⟩

private theorem holds_foldr_some (i : Interpretation datatypeMap) (rs : List OrientedRole)
    (x : i.Object) :
    holds i x (rs.foldr Concept.some .top) ↔ ∃ y, objPath i rs x y := by
  induction rs generalizing x with
  | nil => simp [holds, objPath]
  | cons r rest ih =>
    change (∃ z, holdsOriented i r x z ∧ holds i z (rest.foldr Concept.some .top)) ↔
      ∃ y z, holdsOriented i r x z ∧ objPath i rest z y
    constructor
    · rintro ⟨z, hr, hp⟩
      obtain ⟨y, hy⟩ := (ih z).mp hp
      exact ⟨y, z, hr, hy⟩
    · rintro ⟨y, z, hr, hy⟩
      exact ⟨z, hr, (ih z).mpr ⟨y, hy⟩⟩

private theorem objPath_splitAtTop_iff (i : Interpretation datatypeMap)
    (rs : List OrientedRole) (x y : i.Object) :
    objPath i rs x y ↔
      match splitAtTop rs with
      | (hd, []) => objPath i hd x y
      | (hd, seg :: rest) =>
        holds i x (hd.foldr Concept.some .top) ∧
        (∀ m ∈ (seg :: rest).dropLast, ∃ a, holds i a (m.foldr Concept.some .top)) ∧
        holds i y ((flipWord ((seg :: rest).getLast (List.cons_ne_nil seg rest))).foldr Concept.some .top) := by
  induction rs generalizing x with
  | nil => simp [splitAtTop]
  | cons r rest ih =>
    unfold splitAtTop
    cases hs : splitAtTop rest with
    | mk hd tl =>
      simp only [hs] at ih
      by_cases hr : r.1 == topObjectProperty
      · have htop : r.1 = topObjectProperty := beq_iff_eq.mp hr
        simp only [hr, ↓reduceIte]
        have hstep : objPath i (r :: rest) x y ↔ ∃ z, objPath i rest z y := by
          constructor
          · rintro ⟨z, _, hz⟩; exact ⟨z, hz⟩
          · rintro ⟨z, hz⟩; exact ⟨z, topRole_holds' i r htop x z, hz⟩
        rw [hstep]
        cases tl with
        | nil =>
          simp only [List.dropLast_singleton, List.not_mem_nil, false_implies, implies_true,
            true_and, List.getLast_singleton, List.foldr_nil, holds]
          simp only [ih]
          rw [holds_foldr_some]
          exact exists_congr fun z => (objPath_flip_iff i hd z y).symm
        | cons seg tail =>
          simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil seg tail),
            List.mem_cons, forall_eq_or_imp,
            List.getLast_cons (List.cons_ne_nil seg tail), List.foldr_nil, holds, true_and]
          simp only [ih]
          constructor
          · rintro ⟨z, h1, h2, h3⟩; exact ⟨⟨⟨z, h1⟩, h2⟩, h3⟩
          · rintro ⟨⟨⟨z, h1⟩, h2⟩, h3⟩; exact ⟨z, h1, h2, h3⟩
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        cases tl with
        | nil =>
          change (∃ z, holdsOriented i r x z ∧ objPath i rest z y) ↔
            ∃ z, holdsOriented i r x z ∧ objPath i hd z y
          exact exists_congr fun z => and_congr Iff.rfl (ih z)
        | cons seg tail =>
          change (∃ z, holdsOriented i r x z ∧ objPath i rest z y) ↔
            (∃ z, holdsOriented i r x z ∧ holds i z (hd.foldr Concept.some .top)) ∧
            (∀ m ∈ (seg :: tail).dropLast, ∃ a, holds i a (m.foldr Concept.some .top)) ∧
            holds i y ((flipWord ((seg :: tail).getLast (List.cons_ne_nil seg tail))).foldr Concept.some .top)
          simp only [ih]
          constructor
          · rintro ⟨z, hrz, h1, h2, h3⟩; exact ⟨⟨z, hrz, h1⟩, h2, h3⟩
          · rintro ⟨⟨z, hrz, h1⟩, h2, h3⟩; exact ⟨z, hrz, h1, h2, h3⟩

/-- Left and right concepts `(A, B)` encoding a chain body with at least one
universal-role step: `objPath i body x y ↔ holds i x A ∧ holds i y B`. -/
def chainTopEndpoints (body : List OrientedRole) : Concept × Concept :=
  match splitAtTop body with
  | (_, []) => (.top, .top)
  | (pre, seg :: rest) =>
    let suf := (seg :: rest).getLast (List.cons_ne_nil seg rest)
    let mids := (seg :: rest).dropLast
    let lhs := mids.foldr
      (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc)
      (pre.foldr Concept.some .top)
    let rhs := (flipWord suf).foldr Concept.some .top
    (lhs, rhs)

private theorem holds_mids_foldr (i : Interpretation datatypeMap) (x : i.Object)
    (mids : List (List OrientedRole)) (base : Concept) :
    holds i x (mids.foldr
      (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc) base) ↔
      (∀ m ∈ mids, ∃ a, holds i a (m.foldr Concept.some .top)) ∧ holds i x base := by
  induction mids with
  | nil => simp
  | cons m tail ih =>
    simp only [List.foldr_cons, holds, List.mem_cons, forall_eq_or_imp, ih]
    have htop : (∃ a, holdsOriented i (topObjectProperty, false) x a ∧ holds i a (m.foldr Concept.some .top)) ↔
        ∃ a, holds i a (m.foldr Concept.some .top) :=
      exists_congr fun a => ⟨fun h => h.2, fun h => ⟨i.topObjectExt x a, h⟩⟩
    rw [htop]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem objPath_chainTopEndpoints_iff (i : Interpretation datatypeMap)
    {c : Chain} (htop : hasTopInBody c = true) (x y : i.Object) :
    objPath i c.body x y ↔
      holds i x (chainTopEndpoints c.body).1 ∧ holds i y (chainTopEndpoints c.body).2 := by
  have hne : (splitAtTop c.body).2 ≠ [] := by
    intro hnil
    have hno := (splitAtTop_nil_iff c.body).mp hnil
    obtain ⟨r, hr, heq⟩ := List.any_eq_true.mp htop
    exact hno r hr (beq_iff_eq.mp heq)
  rw [objPath_splitAtTop_iff i c.body x y]
  unfold chainTopEndpoints
  cases hs : splitAtTop c.body with
  | mk pre tl =>
    cases tl with
    | nil => simp [hs] at hne
    | cons seg rest =>
      dsimp only
      rw [holds_mids_foldr]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h1⟩, h3⟩, fun ⟨⟨h2, h1⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-! Constructive fresh role pair `(w₁, w₂)` and fresh anonymous individual `o` -/

private def maxLen : List String → Nat
  | [] => 0
  | s :: ss => max s.length (maxLen ss)

private theorem len_le_maxLen {s : String} {ss : List String} (h : s ∈ ss) :
    s.length ≤ maxLen ss := by
  induction ss with
  | nil => cases h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

private def padChar : Nat → String → String
  | 0, acc => acc
  | n + 1, acc => padChar n (acc.push 'x')

private theorem padChar_length (n : Nat) (acc : String) :
    (padChar n acc).length = acc.length + n := by
  induction n generalizing acc with
  | zero => simp [padChar]
  | succ n ih => simp only [padChar, ih, String.length_push]; omega

private def freshRole1 (p : Problem) : IRI :=
  let forbidden := topObjectProperty :: bottomObjectProperty :: p.objProps
  padChar (maxLen forbidden + 1) "urn:sabrina:tc:"

private def freshRole2 (p : Problem) : IRI :=
  let forbidden := topObjectProperty :: bottomObjectProperty :: p.objProps
  padChar (maxLen forbidden + 2) "urn:sabrina:tc:"

private def indLocalIds (p : Problem) : List String :=
  p.allIndividuals.filterMap fun
    | .anonymous _ lid => Option.some lid
    | .named _ => none

private def freshAnonInd (p : Problem) : Individual :=
  .anonymous "urn:sabrina:tc" (padChar (maxLen (indLocalIds p) + 1) "o")

private theorem freshRole1_ne_role2 (p : Problem) : freshRole1 p ≠ freshRole2 p := by
  intro he
  have h1 := congrArg String.length he
  simp only [freshRole1, freshRole2, padChar_length] at h1
  omega

private theorem freshRole1_not_forbidden (p : Problem) :
    freshRole1 p ∉ topObjectProperty :: bottomObjectProperty :: p.objProps := by
  intro hm
  have hle := len_le_maxLen hm
  have hlen : (freshRole1 p).length =
      "urn:sabrina:tc:".length +
      (maxLen (topObjectProperty :: bottomObjectProperty :: p.objProps) + 1) :=
    padChar_length _ _
  omega

private theorem freshRole2_not_forbidden (p : Problem) :
    freshRole2 p ∉ topObjectProperty :: bottomObjectProperty :: p.objProps := by
  intro hm
  have hle := len_le_maxLen hm
  have hlen : (freshRole2 p).length =
      "urn:sabrina:tc:".length +
      (maxLen (topObjectProperty :: bottomObjectProperty :: p.objProps) + 2) :=
    padChar_length _ _
  omega

private theorem freshAnonInd_not_mem (p : Problem) : freshAnonInd p ∉ p.allIndividuals := by
  intro hm
  have hlid : padChar (maxLen (indLocalIds p) + 1) "o" ∈ indLocalIds p :=
    List.mem_filterMap.mpr ⟨freshAnonInd p, hm, rfl⟩
  have hle := len_le_maxLen hlid
  have hlen : (padChar (maxLen (indLocalIds p) + 1) "o").length =
      "o".length + (maxLen (indLocalIds p) + 1) := padChar_length _ _
  omega

private theorem freshAnonInd_ne_named (p : Problem) (a : IRI) : freshAnonInd p ≠ .named a := by
  intro h; cases h

/-- Expand an interpretation with fresh roles `w₁, w₂` and fresh anonymous
individual `o` witnessing a product chain `A × B ⊑ head`, while preserving
`named`, `Data`, `classes`, `dataProperties`, and all existing roles/individuals. -/
def withTopChainWitness (i : Interpretation datatypeMap)
    (w₁ w₂ : IRI) (o : Individual) (A B : Concept) (x₀ : i.Object)
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name) :
    Interpretation datatypeMap :=
  { i with
    objectProperties := fun r x y =>
      if r = w₁ then holds i x A ∧ y = x₀
      else if r = w₂ then x = x₀ ∧ holds i y B
      else i.objectProperties r x y
    individuals := fun ind => if ind = o then x₀ else i.individuals ind
    namedIndividual := fun a => by simp [(ho_anon a).symm, i.namedIndividual a]
    topObjectExt := fun x y => by simp [hw1_nt.symm, hw2_nt.symm, i.topObjectExt x y]
    bottomObjectExt := fun x y => by simp [hw1_nb.symm, hw2_nb.symm, i.bottomObjectExt x y] }

private theorem dataHolds_withTopChainWitness_iff (i : Interpretation datatypeMap)
    {w₁ w₂ : IRI} {o : Individual} {A B : Concept} {x₀ : i.Object}
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name) (y : i.Data) (d : DataRange) :
    dataHolds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y d ↔
      dataHolds i y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ iha ihb => exact and_congr iha ihb
  | union _ _ iha ihb => exact or_congr iha ihb

private theorem holdsOriented_withTopChainWitness_ne (i : Interpretation datatypeMap)
    {w₁ w₂ : IRI} {o : Individual} {A B : Concept} {x₀ : i.Object}
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name)
    {r : OrientedRole} (h1 : r.1 ≠ w₁) (h2 : r.1 ≠ w₂) (x y : i.Object) :
    holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x y ↔
      holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩ <;> simp [holdsOriented, withTopChainWitness, h1, h2]

private theorem objPath_withTopChainWitness_iff (i : Interpretation datatypeMap)
    {w₁ w₂ : IRI} {o : Individual} {A B : Concept} {x₀ : i.Object}
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name)
    {rs : List OrientedRole} (h1 : ∀ r ∈ rs, r.1 ≠ w₁) (h2 : ∀ r ∈ rs, r.1 ≠ w₂) (x y : i.Object) :
    objPath (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) rs x y ↔
      objPath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    have hr1 : r.1 ≠ w₁ := h1 r (List.mem_cons_self ..)
    have hr2 : r.1 ≠ w₂ := h2 r (List.mem_cons_self ..)
    change (∃ z : i.Object,
        holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x z ∧
        objPath (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) tail z y) ↔
      ∃ z : i.Object, holdsOriented i r x z ∧ objPath i tail z y
    exact exists_congr fun z => and_congr
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2 x z)
      (ih (fun s hs => h1 s (List.mem_cons_of_mem _ hs))
          (fun s hs => h2 s (List.mem_cons_of_mem _ hs)) z)

private theorem holds_withTopChainWitness_iff (i : Interpretation datatypeMap)
    {w₁ w₂ : IRI} {o : Individual} {A B : Concept} {x₀ : i.Object}
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name)
    {c : Concept} (h1 : w₁ ∉ c.objProps) (h2 : w₂ ∉ c.objProps) (ho : o ∉ c.individuals)
    (x : i.Object) :
    holds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) x c ↔
      holds i x c := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b => cases b <;> rfl
  | dataValue _ _ b => cases b <;> rfl
  | nom a b =>
    have hne : a ≠ o := fun he => ho (by simp [Concept.individuals, he])
    cases b <;> simp [holds, withTopChainWitness, hne]
  | dataSome r d =>
    change (∃ y : i.Data, i.dataProperties r x y ∧
        dataHolds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y d) ↔
      ∃ y : i.Data, i.dataProperties r x y ∧ dataHolds i y d
    exact exists_congr fun y => and_congr Iff.rfl
      (dataHolds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon y d)
  | dataAll r d =>
    change (∀ y : i.Data, i.dataProperties r x y →
        dataHolds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y d) ↔
      ∀ y : i.Data, i.dataProperties r x y → dataHolds i y d
    exact forall_congr' fun y => imp_congr Iff.rfl
      (dataHolds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon y d)
  | dataMin n r d =>
    change AtLeast n (fun y : i.Data => i.dataProperties r x y ∧
        dataHolds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y d) ↔
      AtLeast n (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact atLeast_congr' (fun y => and_congr Iff.rfl
      (dataHolds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon y d)) n
  | dataMax n r d =>
    change (¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧
        dataHolds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y d)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Data => i.dataProperties r x y ∧ dataHolds i y d)
    exact not_congr (atLeast_congr' (fun y => and_congr Iff.rfl
      (dataHolds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon y d)) (n + 1))
  | self r b =>
    have hr1 : r.1 ≠ w₁ := fun he => h1 (by simp [Concept.objProps, he])
    have hr2 : r.1 ≠ w₂ := fun he => h2 (by simp [Concept.objProps, he])
    cases b <;> simp [holds,
      holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2]
  | conj a b iha ihb =>
    simp only [Concept.objProps, Concept.individuals, List.mem_append, not_or] at h1 h2 ho
    exact and_congr (iha h1.1 h2.1 ho.1 x) (ihb h1.2 h2.2 ho.2 x)
  | disj a b iha ihb =>
    simp only [Concept.objProps, Concept.individuals, List.mem_append, not_or] at h1 h2 ho
    exact or_congr (iha h1.1 h2.1 ho.1 x) (ihb h1.2 h2.2 ho.2 x)
  | some r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at h1 h2
    have hr1 : r.1 ≠ w₁ := Ne.symm h1.1
    have hr2 : r.1 ≠ w₂ := Ne.symm h2.1
    change (∃ y : i.Object,
        holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x y ∧
        holds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y c) ↔
      ∃ y : i.Object, holdsOriented i r x y ∧ holds i y c
    exact exists_congr fun y => and_congr
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2 x y)
      (ih h1.2 h2.2 ho y)
  | all r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at h1 h2
    have hr1 : r.1 ≠ w₁ := Ne.symm h1.1
    have hr2 : r.1 ≠ w₂ := Ne.symm h2.1
    change (∀ y : i.Object,
        holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x y →
        holds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y c) ↔
      ∀ y : i.Object, holdsOriented i r x y → holds i y c
    exact forall_congr' fun y => imp_congr
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2 x y)
      (ih h1.2 h2.2 ho y)
  | min n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at h1 h2
    have hr1 : r.1 ≠ w₁ := Ne.symm h1.1
    have hr2 : r.1 ≠ w₂ := Ne.symm h2.1
    change AtLeast n (fun y : i.Object =>
        holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x y ∧
        holds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y c) ↔
      AtLeast n (fun y : i.Object => holdsOriented i r x y ∧ holds i y c)
    exact atLeast_congr' (fun y => and_congr
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2 x y)
      (ih h1.2 h2.2 ho y)) n
  | max n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at h1 h2
    have hr1 : r.1 ≠ w₁ := Ne.symm h1.1
    have hr2 : r.1 ≠ w₂ := Ne.symm h2.1
    change (¬ AtLeast (n + 1) (fun y : i.Object =>
        holdsOriented (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) r x y ∧
        holds (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) y c)) ↔
      ¬ AtLeast (n + 1) (fun y : i.Object => holdsOriented i r x y ∧ holds i y c)
    exact not_congr (atLeast_congr' (fun y => and_congr
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hr1 hr2 x y)
      (ih h1.2 h2.2 ho y)) (n + 1))

private theorem objProps_parts {p : Problem} {w : IRI} (h : w ∉ p.objProps) :
    (w ∉ p.root.objProps) ∧
    (∀ q ∈ p.tbox, w ∉ q.sub.objProps ∧ w ∉ q.sup.objProps) ∧
    (∀ rs ∈ p.rules, rs.1.1 ≠ w ∧ rs.2.1 ≠ w) ∧
    (∀ c ∈ p.chains, c.head ≠ w ∧ ∀ r ∈ c.body, r.1 ≠ w) ∧
    (∀ r ∈ p.chars.reflexive, r ≠ w) ∧
    (∀ r ∈ p.chars.irreflexive, r ≠ w) ∧
    (∀ r ∈ p.chars.asymmetric, r ≠ w) ∧
    (∀ rs ∈ p.chars.disjoint, rs.1.1 ≠ w ∧ rs.2.1 ≠ w) ∧
    (∀ k ∈ p.keys, w ∉ k.cls.objProps ∧ ∀ r ∈ k.objProps, r.1 ≠ w) ∧
    (∀ ac ∈ p.classAssertions, w ∉ ac.2.objProps) ∧
    (∀ rab ∈ p.objAssertions, rab.1 ≠ w) ∧
    (∀ rab ∈ p.negObjAssertions, rab.1 ≠ w) := by
  simp only [Problem.objProps, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and] at h
  refine ⟨h.1.1.1.1.1.1.1.1.1.1.1, fun q hq => h.1.1.1.1.1.1.1.1.1.1.2 q hq,
    fun rs hrs => ⟨Ne.symm (h.1.1.1.1.1.1.1.1.1.2 rs hrs).1, Ne.symm (h.1.1.1.1.1.1.1.1.1.2 rs hrs).2⟩,
    fun c hc => ⟨Ne.symm (h.1.1.1.1.1.1.1.1.2 c hc).1, fun r hr => (h.1.1.1.1.1.1.1.1.2 c hc).2 r hr⟩,
    fun r hr he => h.1.1.1.1.1.1.1.2 (he ▸ hr),
    fun r hr he => h.1.1.1.1.1.1.2 (he ▸ hr),
    fun r hr he => h.1.1.1.1.1.2 (he ▸ hr),
    fun rs hrs => ⟨Ne.symm (h.1.1.1.1.2 rs hrs).1, Ne.symm (h.1.1.1.1.2 rs hrs).2⟩,
    fun k hk => h.1.1.1.2 k hk, fun ac hac => h.1.1.2 ac hac,
    fun rab hrab => h.1.2 rab hrab, fun rab hrab => h.2 rab hrab⟩

private theorem allIndividuals_parts {p : Problem} {o : Individual} (h : o ∉ p.allIndividuals) :
    (o ∉ p.root.individuals) ∧
    (∀ q ∈ p.tbox, o ∉ q.sub.individuals ∧ o ∉ q.sup.individuals) ∧
    (∀ k ∈ p.keys, o ∉ k.cls.individuals) ∧
    (∀ ac ∈ p.classAssertions, ac.1 ≠ o ∧ o ∉ ac.2.individuals) ∧
    (∀ rab ∈ p.objAssertions, rab.2.1 ≠ o ∧ rab.2.2 ≠ o) ∧
    (∀ rab ∈ p.negObjAssertions, rab.2.1 ≠ o ∧ rab.2.2 ≠ o) ∧
    (∀ ab ∈ p.sameInds, ab.1 ≠ o ∧ ab.2 ≠ o) ∧
    (∀ ab ∈ p.diffInds, ab.1 ≠ o ∧ ab.2 ≠ o) ∧
    (∀ dal ∈ p.dataAssertions, dal.2.1 ≠ o) ∧
    (∀ dal ∈ p.negDataAssertions, dal.2.1 ≠ o) := by
  simp only [Problem.allIndividuals, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and] at h
  refine ⟨h.1.1.1.1.1.1.1.1.1, fun q hq => h.1.1.1.1.1.1.1.1.2 q hq,
    fun k hk => h.1.1.1.1.1.1.1.2 k hk,
    fun ac hac => ⟨Ne.symm (h.1.1.1.1.1.1.2 ac hac).1, (h.1.1.1.1.1.1.2 ac hac).2⟩,
    fun rab hrab => ⟨Ne.symm (h.1.1.1.1.1.2 rab hrab).1, Ne.symm (h.1.1.1.1.1.2 rab hrab).2⟩,
    fun rab hrab => ⟨Ne.symm (h.1.1.1.1.2 rab hrab).1, Ne.symm (h.1.1.1.1.2 rab hrab).2⟩,
    fun ab hab => ⟨Ne.symm (h.1.1.1.2 ab hab).1, Ne.symm (h.1.1.1.2 ab hab).2⟩,
    fun ab hab => ⟨Ne.symm (h.1.1.2 ab hab).1, Ne.symm (h.1.1.2 ab hab).2⟩,
    fun dal hdal => h.1.2 dal hdal, fun dal hdal => h.2 dal hdal⟩

private theorem models_withTopChainWitness_of_models {p : Problem} {i : Interpretation datatypeMap}
    (hm : p.Models i) {w₁ w₂ : IRI} {o : Individual} {A B : Concept} {x₀ : i.Object}
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (ho_anon : ∀ name, o ≠ .named name)
    (hw1_p : w₁ ∉ p.objProps) (hw2_p : w₂ ∉ p.objProps) (ho_p : o ∉ p.allIndividuals) :
    p.Models (withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon) := by
  obtain ⟨_, ht1, hr1, hc1, hrf1, hir1, has1, hdj1, hk1, hca1, hoa1, hno1⟩ := objProps_parts hw1_p
  obtain ⟨_, ht2, hr2, hc2, hrf2, hir2, has2, hdj2, hk2, hca2, hoa2, hno2⟩ := objProps_parts hw2_p
  obtain ⟨_, hto, hko, hcao, hoao, hnoo, hsamo, hdifo, hdao, hndao⟩ := allIndividuals_parts ho_p
  let j := withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
  have hobj (r : IRI) (h1 : r ≠ w₁) (h2 : r ≠ w₂) (x y : i.Object) :
      j.objectProperties r x y ↔ i.objectProperties r x y := by
    simp [j, withTopChainWitness, h1, h2]
  have hind (a : Individual) (ha : a ≠ o) : j.individuals a = i.individuals a := by
    simp [j, withTopChainWitness, ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq x hx
    exact (holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
      (ht1 q hq).2 (ht2 q hq).2 (hto q hq).2 x).mpr
      (hm.tbox q hq x ((holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (ht1 q hq).1 (ht2 q hq).1 (hto q hq).1 x).mp hx))
  · intro rs hrs x y hxy
    exact (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
      (hr1 rs hrs).2 (hr2 rs hrs).2 x y).mpr
      (hm.rules rs hrs x y ((holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (hr1 rs hrs).1 (hr2 rs hrs).1 x y).mp hxy))
  · intro c hc x y hp
    exact (hobj c.head (hc1 c hc).1 (hc2 c hc).1 x y).mpr
      (hm.chains c hc x y ((objPath_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (hc1 c hc).2 (hc2 c hc).2 x y).mp hp))
  · intro r hr x; exact (hobj r (hrf1 r hr) (hrf2 r hr) x x).mpr (hm.reflexive r hr x)
  · intro r hr x h; exact hm.irreflexive r hr x ((hobj r (hir1 r hr) (hir2 r hr) x x).mp h)
  · intro r hr x y h1 h2
    exact hm.asymmetric r hr x y
      ((hobj r (has1 r hr) (has2 r hr) x y).mp h1)
      ((hobj r (has1 r hr) (has2 r hr) y x).mp h2)
  · intro rs hrs x y ⟨h1, h2⟩
    exact hm.disjoint rs hrs x y
      ⟨(holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
         (hdj1 rs hrs).1 (hdj2 rs hrs).1 x y).mp h1,
       (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
         (hdj1 rs hrs).2 (hdj2 rs hrs).2 x y).mp h2⟩
  · intro rd hrd x y hxy
    exact (dataHolds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon y rd.2).mpr
      (hm.dataRanges rd hrd x y hxy)
  · intro k hk x y hx hy hnx hny ho hd
    refine hm.keys k hk x y
      ((holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (hk1 k hk).1 (hk2 k hk).1 (hko k hk) x).mp hx)
      ((holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (hk1 k hk).1 (hk2 k hk).1 (hko k hk) y).mp hy)
      hnx hny ?_ hd
    intro r hr
    obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
    exact ⟨z, hnz,
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        ((hk1 k hk).2 r hr) ((hk2 k hk).2 r hr) x z).mp hxz,
      (holdsOriented_withTopChainWitness_ne i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        ((hk1 k hk).2 r hr) ((hk2 k hk).2 r hr) y z).mp hyz⟩
  · intro ac hac
    rw [hind ac.1 (hcao ac hac).1]
    exact (holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
      (hca1 ac hac) (hca2 ac hac) (hcao ac hac).2 _).mpr (hm.classAssertions ac hac)
  · intro rab hrab
    rw [hind rab.2.1 (hoao rab hrab).1, hind rab.2.2 (hoao rab hrab).2]
    exact (hobj rab.1 (hoa1 rab hrab) (hoa2 rab hrab) _ _).mpr (hm.objAssertions rab hrab)
  · intro rab hrab h
    rw [hind rab.2.1 (hnoo rab hrab).1, hind rab.2.2 (hnoo rab hrab).2] at h
    exact hm.negObjAssertions rab hrab ((hobj rab.1 (hno1 rab hrab) (hno2 rab hrab) _ _).mp h)
  · intro ab hab
    rw [hind ab.1 (hsamo ab hab).1, hind ab.2 (hsamo ab hab).2]
    exact hm.sameInds ab hab
  · intro ab hab
    rw [hind ab.1 (hdifo ab hab).1, hind ab.2 (hdifo ab hab).2]
    exact hm.diffInds ab hab
  · intro dal hdal
    rw [hind dal.2.1 (hdao dal hdal)]
    exact hm.dataAssertions dal hdal
  · intro dal hdal
    rw [hind dal.2.1 (hndao dal hdal)]
    exact hm.negDataAssertions dal hdal

private theorem foldr_some_objProps_subset (rs : List OrientedRole) :
    ∀ r ∈ (rs.foldr Concept.some .top).objProps, r ∈ rs.map Prod.fst := by
  induction rs with
  | nil => intro r hr; simp [Concept.objProps] at hr
  | cons a rest ih =>
    intro r hr
    simp only [List.foldr_cons, Concept.objProps, List.mem_cons, List.map_cons] at hr ⊢
    exact hr.elim Or.inl (Or.inr ∘ ih r)

private theorem foldr_some_individuals_nil (rs : List OrientedRole) :
    (rs.foldr Concept.some .top).individuals = [] := by
  induction rs with
  | nil => rfl
  | cons a rest ih => simpa [List.foldr_cons, Concept.individuals] using ih

private theorem splitAtTop_roles_subset (rs : List OrientedRole) :
    (∀ r ∈ (splitAtTop rs).1, r ∈ rs) ∧
    (∀ seg ∈ (splitAtTop rs).2, ∀ r ∈ seg, r ∈ rs) := by
  induction rs with
  | nil => simp [splitAtTop]
  | cons a rest ih =>
    unfold splitAtTop
    cases hs : splitAtTop rest with
    | mk hd tl =>
      simp only [hs] at ih
      by_cases ha : a.1 == topObjectProperty
      · simp only [ha, ↓reduceIte]
        refine ⟨by simp, fun seg hseg r hr => ?_⟩
        rcases List.mem_cons.mp hseg with rfl | htl
        · exact List.mem_cons_of_mem _ (ih.1 r hr)
        · exact List.mem_cons_of_mem _ (ih.2 seg htl r hr)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun r hr => ?_, fun seg hseg r hr => List.mem_cons_of_mem _ (ih.2 seg hseg r hr)⟩
        rcases List.mem_cons.mp hr with rfl | hhd
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih.1 r hhd)

private theorem chainTopEndpoints_fresh {c : Chain} {w : IRI} {o : Individual}
    (hw_nt : w ≠ topObjectProperty) (hw_body : ∀ r ∈ c.body, r.1 ≠ w) :
    w ∉ (chainTopEndpoints c.body).1.objProps ∧
    w ∉ (chainTopEndpoints c.body).2.objProps ∧
    o ∉ (chainTopEndpoints c.body).1.individuals ∧
    o ∉ (chainTopEndpoints c.body).2.individuals := by
  have hsub := splitAtTop_roles_subset c.body
  unfold chainTopEndpoints
  cases hs : splitAtTop c.body with
  | mk pre tl =>
    simp only [hs] at hsub
    cases tl with
    | nil => simp [Concept.objProps, Concept.individuals]
    | cons seg rest =>
      dsimp only
      have hmidsObj : ∀ ms : List (List OrientedRole),
          (∀ m ∈ ms, ∀ r ∈ m, r.1 ≠ w) →
          w ∉ (ms.foldr (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc)
            (pre.foldr Concept.some .top)).objProps := by
        intro ms hms
        induction ms with
        | nil =>
          intro hm
          obtain ⟨r, hr, heq⟩ := List.mem_map.mp (foldr_some_objProps_subset pre w hm)
          exact hw_body r (hsub.1 r hr) heq
        | cons m tail iht =>
          intro hm
          simp only [List.foldr_cons, Concept.objProps, List.mem_append, List.mem_cons] at hm
          rcases hm with (heq | hmo) | hto
          · exact hw_nt heq
          · obtain ⟨r, hr, heq⟩ := List.mem_map.mp (foldr_some_objProps_subset m w hmo)
            exact hms m (List.mem_cons_self ..) r hr heq
          · exact iht (fun x hx => hms x (List.mem_cons_of_mem _ hx)) hto
      have hmidsInd : ∀ ms : List (List OrientedRole),
          (ms.foldr (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc)
            (pre.foldr Concept.some .top)).individuals = [] := by
        intro ms
        induction ms with
        | nil => exact foldr_some_individuals_nil pre
        | cons m tail iht =>
          simp [List.foldr_cons, Concept.individuals, foldr_some_individuals_nil m, iht]
      refine ⟨hmidsObj _ ?_, ?_, by rw [hmidsInd]; simp, by rw [foldr_some_individuals_nil]; simp⟩
      · intro m hm r hr
        have hm' : m ∈ seg :: rest := List.dropLast_subset _ hm
        exact hw_body r (hsub.2 m hm' r hr)
      · intro hm
        obtain ⟨r, hr, heq⟩ := List.mem_map.mp (foldr_some_objProps_subset _ w hm)
        simp only [flipWord, List.mem_reverse, List.mem_map] at hr
        obtain ⟨r₀, hr₀, rfl⟩ := hr
        have hlast : (seg :: rest).getLast (List.cons_ne_nil seg rest) ∈ seg :: rest :=
          List.getLast_mem _
        exact hw_body r₀ (hsub.2 _ hlast r₀ hr₀) (by rcases r₀ with ⟨_, _ | _⟩ <;> exact heq)

/-- Replace one chain `c` (at `p.chains = pre ++ c :: post`) whose body contains
`owl:topObjectProperty` with a nominal bridge `A ⊑ ∃w₁.{o}`, `B ⊑ ∃w₂⁻.{o}`,
`w₁ ∘ w₂ ⊑ c.head` using fresh ordinary roles `w₁, w₂` and fresh anonymous `o`. -/
def replaceTopChainWith (p : Problem) (pre : List Chain) (c : Chain) (post : List Chain)
    (w₁ w₂ : IRI) (o : Individual) : Problem :=
  let (A, B) := chainTopEndpoints c.body
  { p with
    tbox := ⟨A, .some (w₁, false) (.nom o true)⟩ ::
            ⟨B, .some (w₂, true) (.nom o true)⟩ :: p.tbox
    chains := pre ++ Chain.named [w₁, w₂] c.head :: post }

def replaceTopChainAt (p : Problem) (pre : List Chain) (c : Chain) (post : List Chain) : Problem :=
  replaceTopChainWith p pre c post (freshRole1 p) (freshRole2 p) (freshAnonInd p)

private theorem replaceTopChainWith_sat_iff {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true)
    (w₁ w₂ : IRI) (o : Individual)
    (hne12 : w₁ ≠ w₂)
    (hw1_nt : w₁ ≠ topObjectProperty) (hw1_nb : w₁ ≠ bottomObjectProperty)
    (hw2_nt : w₂ ≠ topObjectProperty) (hw2_nb : w₂ ≠ bottomObjectProperty)
    (hw1_p : w₁ ∉ p.objProps) (hw2_p : w₂ ∉ p.objProps)
    (ho_p : o ∉ p.allIndividuals) (ho_anon : ∀ name, o ≠ .named name) :
    (replaceTopChainWith p pre c post w₁ w₂ o).Sat ↔ p.Sat := by
  let A := (chainTopEndpoints c.body).1
  let B := (chainTopEndpoints c.body).2
  have hcMem : c ∈ p.chains := by rw [hsplit]; simp
  have hcBody1 : ∀ r ∈ c.body, r.1 ≠ w₁ := (objProps_parts hw1_p).2.2.2.1 c hcMem |>.2
  have hcBody2 : ∀ r ∈ c.body, r.1 ≠ w₂ := (objProps_parts hw2_p).2.2.2.1 c hcMem |>.2
  have hcHead1 : c.head ≠ w₁ := (objProps_parts hw1_p).2.2.2.1 c hcMem |>.1
  have hcHead2 : c.head ≠ w₂ := (objProps_parts hw2_p).2.2.2.1 c hcMem |>.1
  have hAB1 := chainTopEndpoints_fresh (o := o) hw1_nt hcBody1
  have hAB2 := chainTopEndpoints_fresh (o := o) hw2_nt hcBody2
  constructor
  · rintro ⟨i, hm, x₀, hroot⟩
    have hgA := hm.tbox ⟨A, .some (w₁, false) (.nom o true)⟩ (by simp [replaceTopChainWith, A])
    have hgB := hm.tbox ⟨B, .some (w₂, true) (.nom o true)⟩ (by simp [replaceTopChainWith, B])
    have hchW := hm.chains (Chain.named [w₁, w₂] c.head) (by simp [replaceTopChainWith])
    refine ⟨i, ⟨?_, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩, x₀, hroot⟩
    · intro q hq
      exact hm.tbox q (by simp [replaceTopChainWith, hq])
    · intro c' hc' x y hp
      rw [hsplit] at hc'
      rcases List.mem_append.mp hc' with hpre | hrest
      · exact hm.chains c' (by simp [replaceTopChainWith, hpre]) x y hp
      · rcases List.mem_cons.mp hrest with rfl | hpost
        · obtain ⟨hAx, hBy⟩ := (objPath_chainTopEndpoints_iff i htop x y).mp hp
          obtain ⟨z₁, hw1, hz1⟩ := hgA x hAx
          obtain ⟨z₂, hw2, hz2⟩ := hgB y hBy
          have hz1' : z₁ = i.individuals o := hz1
          have hz2' : z₂ = i.individuals o := hz2
          have hw1' : i.objectProperties w₁ x (i.individuals o) := by
            rw [← hz1']; exact hw1
          have hw2' : i.objectProperties w₂ (i.individuals o) y := by
            rw [← hz2']; exact hw2
          exact hchW x y ⟨i.individuals o, hw1', y, hw2', rfl⟩
        · exact hm.chains c' (by simp [replaceTopChainWith, hpost]) x y hp
  · rintro ⟨i, hm, x₀, hroot⟩
    let j := withTopChainWitness i w₁ w₂ o A B x₀ hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
    have hmj : p.Models j :=
      models_withTopChainWitness_of_models hm hw1_nt hw1_nb hw2_nt hw2_nb ho_anon hw1_p hw2_p ho_p
    have hrootj : holds j x₀ p.root :=
      (holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
        (objProps_parts hw1_p).1 (objProps_parts hw2_p).1 (allIndividuals_parts ho_p).1 x₀).mpr hroot
    refine ⟨j, ⟨?_, hmj.rules, ?_, hmj.reflexive, hmj.irreflexive, hmj.asymmetric, hmj.disjoint,
      hmj.subData, hmj.disjointData, hmj.funcData, hmj.dataRanges, hmj.keys, hmj.classAssertions,
      hmj.objAssertions, hmj.negObjAssertions, hmj.sameInds, hmj.diffInds, hmj.dataAssertions,
      hmj.negDataAssertions⟩, x₀, hrootj⟩
    · intro q hq
      simp only [replaceTopChainWith, List.mem_cons] at hq
      rcases hq with rfl | rfl | hmem
      · intro x hAx
        have hAi : holds i x A :=
          (holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
            hAB1.1 hAB2.1 hAB1.2.2.1 x).mp hAx
        refine ⟨x₀, ?_, ?_⟩
        · simp [j, holdsOriented, withTopChainWitness, hAi]
        · simp [j, holds, withTopChainWitness]
      · intro y hBy
        have hBi : holds i y B :=
          (holds_withTopChainWitness_iff i hw1_nt hw1_nb hw2_nt hw2_nb ho_anon
            hAB1.2.1 hAB2.2.1 hAB1.2.2.2 y).mp hBy
        refine ⟨x₀, ?_, ?_⟩
        · simp [j, holdsOriented, withTopChainWitness, hne12.symm, hBi]
        · simp [j, holds, withTopChainWitness]
      · exact hmj.tbox q hmem
    · intro c' hc' x y hp
      simp only [replaceTopChainWith, List.mem_append, List.mem_cons] at hc'
      rcases hc' with hpre | rfl | hpost
      · exact hmj.chains c' (by rw [hsplit]; simp [hpre]) x y hp
      · obtain ⟨z, hw1, y', hw2, hy'⟩ := hp
        simp only [j, holdsOriented, withTopChainWitness, ↓reduceIte, hne12.symm] at hw1 hw2
        have hAx : holds i x A := hw1.1
        have hBy' : holds i y' B := hw2.2
        have hyeq : y' = y := hy'
        rw [hyeq] at hBy'
        have hpath : objPath i c.body x y :=
          (objPath_chainTopEndpoints_iff i htop x y).mpr ⟨hAx, hBy'⟩
        have hhead : i.objectProperties c.head x y := hm.chains c hcMem x y hpath
        simpa [j, withTopChainWitness, Chain.named, hcHead1, hcHead2] using hhead
      · exact hmj.chains c' (by rw [hsplit]; simp [hpost]) x y hp

theorem replaceTopChainAt_sat_iff {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true) :
    (replaceTopChainAt p pre c post).Sat ↔ p.Sat :=
  replaceTopChainWith_sat_iff hsplit htop
    (freshRole1 p) (freshRole2 p) (freshAnonInd p)
    (freshRole1_ne_role2 p)
    (fun h => freshRole1_not_forbidden p (h ▸ List.mem_cons_self ..))
    (fun h => freshRole1_not_forbidden p (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (fun h => freshRole2_not_forbidden p (h ▸ List.mem_cons_self ..))
    (fun h => freshRole2_not_forbidden p (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (fun h => freshRole1_not_forbidden p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    (fun h => freshRole2_not_forbidden p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    (freshAnonInd_not_mem p) (freshAnonInd_ne_named p)

private theorem replaceTopChainAt_count_lt {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true) :
    ((replaceTopChainAt p pre c post).chains.filter hasTopInBody).length <
      (p.chains.filter hasTopInBody).length := by
  have hnt1 : (freshRole1 p == topObjectProperty) = false :=
    beq_false_of_ne (fun h => freshRole1_not_forbidden p (h ▸ List.mem_cons_self ..))
  have hnt2 : (freshRole2 p == topObjectProperty) = false :=
    beq_false_of_ne (fun h => freshRole2_not_forbidden p (h ▸ List.mem_cons_self ..))
  have hnew : hasTopInBody (Chain.named [freshRole1 p, freshRole2 p] c.head) = false := by
    simp [hasTopInBody, Chain.named, hnt1, hnt2]
  simp only [replaceTopChainAt, replaceTopChainWith, List.filter_append, List.filter_cons, hnew,
    Bool.false_eq_true, ↓reduceIte, List.length_append]
  rw [hsplit]
  simp only [List.filter_append, List.filter_cons, htop, ↓reduceIte,
    List.length_append, List.length_cons]
  omega

/-! Fast nominal-free expansion for non-simple, key-free, sink product chains -/

private def Concept.noSimpleRole (h : IRI) : Concept → Bool
  | .conj a b | .disj a b => a.noSimpleRole h && b.noSimpleRole h
  | .some _ c | .all _ c => c.noSimpleRole h
  | .min _ r c | .max _ r c => !(r.1 == h) && c.noSimpleRole h
  | .self r _ => !(r.1 == h)
  | _ => true

/-- Expand every existential/universal restriction over `h` under `h ↦ h ∪ (A × B)`. -/
def Concept.expandProdRole (h : IRI) (A B : Concept) : Concept → Concept
  | .conj a b => .conj (Concept.expandProdRole h A B a) (Concept.expandProdRole h A B b)
  | .disj a b => .disj (Concept.expandProdRole h A B a) (Concept.expandProdRole h A B b)
  | .some r c =>
    let c' := Concept.expandProdRole h A B c
    if r.1 == h then
      if r.2 then
        .disj (.some r c') (.conj B (.some (topObjectProperty, false) (.conj A c')))
      else
        .disj (.some r c') (.conj A (.some (topObjectProperty, false) (.conj B c')))
    else .some r c'
  | .all r c =>
    let c' := Concept.expandProdRole h A B c
    if r.1 == h then
      if r.2 then
        .conj (.all r c') (.disj B.dual (.all (topObjectProperty, false) (.disj A.dual c')))
      else
        .conj (.all r c') (.disj A.dual (.all (topObjectProperty, false) (.disj B.dual c')))
    else .all r c'
  | .min n r c => .min n r (Concept.expandProdRole h A B c)
  | .max n r c => .max n r (Concept.expandProdRole h A B c)
  | c => c

private def canExpandTopChain (p : Problem) (pre : List Chain) (c : Chain) (post : List Chain) : Bool :=
  let h := c.head
  let A := (chainTopEndpoints c.body).1
  let B := (chainTopEndpoints c.body).2
  !(h == topObjectProperty) &&
  !(h == bottomObjectProperty) &&
  !A.objProps.contains h &&
  !B.objProps.contains h &&
  p.root.noSimpleRole h &&
  p.tbox.all (fun q => q.sub.noSimpleRole h && q.sup.noSimpleRole h) &&
  p.keys.all (fun k => k.cls.noSimpleRole h && k.objProps.all (fun r => !(r.1 == h))) &&
  p.classAssertions.all (fun ac => ac.2.noSimpleRole h) &&
  !p.chars.irreflexive.contains h &&
  !p.chars.asymmetric.contains h &&
  p.chars.disjoint.all (fun rs => !(rs.1.1 == h) && !(rs.2.1 == h)) &&
  p.rules.all (fun rs => !(rs.1.1 == h)) &&
  (pre ++ post).all (fun c' => c'.body.all (fun r => !(r.1 == h)))

/-- Eliminate a product chain `A × B ⊑ h` without introducing fresh nominals
or roles by expanding `h ↦ h ∪ (A × B)` directly in concepts and negative
object property assertions. -/
def expandTopChainAt (p : Problem) (pre : List Chain) (c : Chain) (post : List Chain) : Problem :=
  let h := c.head
  let A := (chainTopEndpoints c.body).1
  let B := (chainTopEndpoints c.body).2
  let f := Concept.expandProdRole h A B
  let extraNeg := p.negObjAssertions.filterMap fun (r, a, b) =>
    if r == h then
      Option.some (a, .disj A.dual (.all (topObjectProperty, false) (.disj (.nom b false) B.dual)))
    else none
  { p with
    root := f p.root
    tbox := p.tbox.map fun q => ⟨f q.sub, f q.sup⟩
    chains := pre ++ post
    keys := p.keys.map fun k => { k with cls := f k.cls }
    classAssertions := p.classAssertions.map (fun ac => (ac.1, f ac.2)) ++ extraNeg }

private def addProdRole (i : Interpretation datatypeMap) (h : IRI) (A B : Concept)
    (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty) :
    Interpretation datatypeMap :=
  { i with
    objectProperties := fun r x y =>
      if r = h then i.objectProperties h x y ∨ (holds i x A ∧ holds i y B)
      else i.objectProperties r x y
    topObjectExt := fun x y => by simp [hnt.symm, i.topObjectExt x y]
    bottomObjectExt := fun x y => by simp [hnb.symm, i.bottomObjectExt x y] }

private theorem dataHolds_addProdRole_iff (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    (y : i.Data) (d : DataRange) :
    dataHolds (addProdRole i h A B hnt hnb) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ iha ihb => exact and_congr iha ihb
  | union _ _ iha ihb => exact or_congr iha ihb

private theorem holdsOriented_addProdRole_ne (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    {r : OrientedRole} (hne : r.1 ≠ h) (x y : i.Object) :
    holdsOriented (addProdRole i h A B hnt hnb) r x y ↔ holdsOriented i r x y := by
  rcases r with ⟨name, _ | _⟩ <;> simp [holdsOriented, addProdRole, hne]

private theorem objPath_addProdRole_ne (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    {rs : List OrientedRole} (hne : ∀ r ∈ rs, r.1 ≠ h) (x y : i.Object) :
    objPath (addProdRole i h A B hnt hnb) rs x y ↔ objPath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rest ih =>
    have hr := hne r (List.mem_cons_self ..)
    change (∃ z : i.Object,
        holdsOriented (addProdRole i h A B hnt hnb) r x z ∧
        objPath (addProdRole i h A B hnt hnb) rest z y) ↔
      ∃ z : i.Object, holdsOriented i r x z ∧ objPath i rest z y
    exact exists_congr fun z => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb hr x z)
      (ih (fun s hs => hne s (List.mem_cons_of_mem _ hs)) z)

private theorem holds_addProdRole_not_mem (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    {c : Concept} (hnm : h ∉ c.objProps) (x : i.Object) :
    holds (addProdRole i h A B hnt hnb) x c ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b | nom _ b | dataValue _ _ b => cases b <;> rfl
  | dataSome r d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataAll r d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataMin n r d =>
    exact atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) n
  | dataMax n r d =>
    exact not_congr (atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) (n + 1))
  | self r b =>
    have hr : r.1 ≠ h := fun he => hnm (by simp [Concept.objProps, he])
    cases b <;> simp [holds, holdsOriented_addProdRole_ne i hnt hnb hr]
  | conj a b iha ihb =>
    simp only [Concept.objProps, List.mem_append, not_or] at hnm
    exact and_congr (iha hnm.1 x) (ihb hnm.2 x)
  | disj a b iha ihb =>
    simp only [Concept.objProps, List.mem_append, not_or] at hnm
    exact or_congr (iha hnm.1 x) (ihb hnm.2 x)
  | some r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hnm
    exact exists_congr fun y => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb (Ne.symm hnm.1) x y) (ih hnm.2 y)
  | all r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hnm
    exact forall_congr' fun y => imp_congr
      (holdsOriented_addProdRole_ne i hnt hnb (Ne.symm hnm.1) x y) (ih hnm.2 y)
  | min n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hnm
    exact atLeast_congr' (fun y => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb (Ne.symm hnm.1) x y) (ih hnm.2 y)) n
  | max n r c ih =>
    simp only [Concept.objProps, List.mem_cons, not_or] at hnm
    exact not_congr (atLeast_congr' (fun y => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb (Ne.symm hnm.1) x y) (ih hnm.2 y)) (n + 1))

private theorem holds_addProdRole_expandProdRole (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    {c : Concept} (hns : c.noSimpleRole h = true) (x : i.Object) :
    holds (addProdRole i h A B hnt hnb) x c ↔ holds i x (Concept.expandProdRole h A B c) := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b | nom _ b | dataValue _ _ b => cases b <;> rfl
  | dataSome r d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataAll r d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataMin n r d =>
    exact atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) n
  | dataMax n r d =>
    exact not_congr (atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) (n + 1))
  | self r b =>
    simp only [Concept.noSimpleRole, Bool.not_eq_true', beq_eq_false_iff_ne] at hns
    cases b <;> simp [Concept.expandProdRole, holds, holdsOriented_addProdRole_ne i hnt hnb hns]
  | conj a b iha ihb =>
    simp only [Concept.noSimpleRole, Bool.and_eq_true] at hns
    exact and_congr (iha hns.1 x) (ihb hns.2 x)
  | disj a b iha ihb =>
    simp only [Concept.noSimpleRole, Bool.and_eq_true] at hns
    exact or_congr (iha hns.1 x) (ihb hns.2 x)
  | min n r c ih =>
    simp only [Concept.noSimpleRole, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hns
    exact atLeast_congr' (fun y => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb hns.1 x y) (ih hns.2 y)) n
  | max n r c ih =>
    simp only [Concept.noSimpleRole, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hns
    exact not_congr (atLeast_congr' (fun y => and_congr
      (holdsOriented_addProdRole_ne i hnt hnb hns.1 x y) (ih hns.2 y)) (n + 1))
  | some r c ih =>
    simp only [Concept.noSimpleRole] at hns
    rcases r with ⟨rn, inv⟩
    by_cases heq : rn == h
    · have hr : rn = h := beq_iff_eq.mp heq
      subst hr
      cases inv with
      | false =>
        simp only [Concept.expandProdRole, beq_self_eq_true, ↓reduceIte, holds, holdsOriented, addProdRole]
        constructor
        · rintro ⟨y, hy | ⟨hAx, hBy⟩, hc⟩
          · exact Or.inl ⟨y, hy, (ih hns y).mp hc⟩
          · exact Or.inr ⟨hAx, y, i.topObjectExt x y, hBy, (ih hns y).mp hc⟩
        · rintro (⟨y, hy, hc⟩ | ⟨hAx, y, _, hBy, hc⟩)
          · exact ⟨y, Or.inl hy, (ih hns y).mpr hc⟩
          · exact ⟨y, Or.inr ⟨hAx, hBy⟩, (ih hns y).mpr hc⟩
      | true =>
        simp only [Concept.expandProdRole, beq_self_eq_true, ↓reduceIte, holds, holdsOriented, addProdRole]
        constructor
        · rintro ⟨y, hy | ⟨hAy, hBx⟩, hc⟩
          · exact Or.inl ⟨y, hy, (ih hns y).mp hc⟩
          · exact Or.inr ⟨hBx, y, i.topObjectExt x y, hAy, (ih hns y).mp hc⟩
        · rintro (⟨y, hy, hc⟩ | ⟨hBx, y, _, hAy, hc⟩)
          · exact ⟨y, Or.inl hy, (ih hns y).mpr hc⟩
          · exact ⟨y, Or.inr ⟨hAy, hBx⟩, (ih hns y).mpr hc⟩
    · have hne : rn ≠ h := fun e => heq (beq_iff_eq.mpr e)
      simp only [Concept.expandProdRole, heq, Bool.false_eq_true, ↓reduceIte]
      exact exists_congr fun y => and_congr
        (holdsOriented_addProdRole_ne i hnt hnb hne x y) (ih hns y)
  | all r c ih =>
    simp only [Concept.noSimpleRole] at hns
    rcases r with ⟨rn, inv⟩
    by_cases heq : rn == h
    · have hr : rn = h := beq_iff_eq.mp heq
      subst hr
      cases inv with
      | false =>
        simp only [Concept.expandProdRole, beq_self_eq_true, ↓reduceIte, holds, holdsOriented, addProdRole]
        constructor
        · intro hall
          refine ⟨fun y hy => (ih hns y).mp (hall y (Or.inl hy)), ?_⟩
          by_cases hAx : holds i x A
          · refine Or.inr fun y _ => ?_
            by_cases hBy : holds i y B
            · exact Or.inr ((ih hns y).mp (hall y (Or.inr ⟨hAx, hBy⟩)))
            · exact Or.inl ((holds_dual i y B).mpr hBy)
          · exact Or.inl ((holds_dual i x A).mpr hAx)
        · rintro ⟨hall, hprod⟩ y (hy | ⟨hAx, hBy⟩)
          · exact (ih hns y).mpr (hall y hy)
          · rcases hprod with hna | hB
            · exact ((holds_dual i x A).mp hna hAx).elim
            · rcases hB y (i.topObjectExt x y) with hnb' | hc
              · exact ((holds_dual i y B).mp hnb' hBy).elim
              · exact (ih hns y).mpr hc
      | true =>
        simp only [Concept.expandProdRole, beq_self_eq_true, ↓reduceIte, holds, holdsOriented, addProdRole]
        constructor
        · intro hall
          refine ⟨fun y hy => (ih hns y).mp (hall y (Or.inl hy)), ?_⟩
          by_cases hBx : holds i x B
          · refine Or.inr fun y _ => ?_
            by_cases hAy : holds i y A
            · exact Or.inr ((ih hns y).mp (hall y (Or.inr ⟨hAy, hBx⟩)))
            · exact Or.inl ((holds_dual i y A).mpr hAy)
          · exact Or.inl ((holds_dual i x B).mpr hBx)
        · rintro ⟨hall, hprod⟩ y (hy | ⟨hAy, hBx⟩)
          · exact (ih hns y).mpr (hall y hy)
          · rcases hprod with hnb' | hA
            · exact ((holds_dual i x B).mp hnb' hBx).elim
            · rcases hA y (i.topObjectExt x y) with hna | hc
              · exact ((holds_dual i y A).mp hna hAy).elim
              · exact (ih hns y).mpr hc
    · have hne : rn ≠ h := fun e => heq (beq_iff_eq.mpr e)
      simp only [Concept.expandProdRole, heq, Bool.false_eq_true, ↓reduceIte]
      exact forall_congr' fun y => imp_congr
        (holdsOriented_addProdRole_ne i hnt hnb hne x y) (ih hns y)

private theorem holds_addProdRole_same_of_sub (i : Interpretation datatypeMap)
    {h : IRI} {A B : Concept} (hnt : h ≠ topObjectProperty) (hnb : h ≠ bottomObjectProperty)
    (hsub : ∀ x y, holds i x A → holds i y B → i.objectProperties h x y)
    (c : Concept) (x : i.Object) :
    holds (addProdRole i h A B hnt hnb) x c ↔ holds i x c := by
  have hrel : ∀ r x y, holdsOriented (addProdRole i h A B hnt hnb) r x y ↔ holdsOriented i r x y := by
    rintro ⟨rn, _ | _⟩ x y
    · by_cases he : rn = h
      · subst he; simp only [holdsOriented, addProdRole, ↓reduceIte]
        exact ⟨fun o => o.elim id (fun p => hsub x y p.1 p.2), Or.inl⟩
      · simp [holdsOriented, addProdRole, he]
    · by_cases he : rn = h
      · subst he; simp only [holdsOriented, addProdRole, ↓reduceIte]
        exact ⟨fun o => o.elim id (fun p => hsub y x p.1 p.2), Or.inl⟩
      · simp [holdsOriented, addProdRole, he]
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b | nom _ b | dataValue _ _ b => cases b <;> rfl
  | dataSome r d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataAll r d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)
  | dataMin n r d =>
    exact atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) n
  | dataMax n r d =>
    exact not_congr (atLeast_congr' (fun y => and_congr Iff.rfl (dataHolds_addProdRole_iff i hnt hnb y d)) (n + 1))
  | self r b => cases b <;> simp [holds, hrel r x x]
  | conj a b iha ihb => exact and_congr (iha x) (ihb x)
  | disj a b iha ihb => exact or_congr (iha x) (ihb x)
  | some r c ih => exact exists_congr fun y => and_congr (hrel r x y) (ih y)
  | all r c ih => exact forall_congr' fun y => imp_congr (hrel r x y) (ih y)
  | min n r c ih => exact atLeast_congr' (fun y => and_congr (hrel r x y) (ih y)) n
  | max n r c ih => exact not_congr (atLeast_congr' (fun y => and_congr (hrel r x y) (ih y)) (n + 1))

theorem expandTopChainAt_sat_iff {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true)
    (hcan : canExpandTopChain p pre c post = true) :
    (expandTopChainAt p pre c post).Sat ↔ p.Sat := by
  let h := c.head
  let A := (chainTopEndpoints c.body).1
  let B := (chainTopEndpoints c.body).2
  simp only [canExpandTopChain, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, List.all_eq_true] at hcan
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnt, hnb⟩, hAnC⟩, hBnC⟩, hrootNs⟩, htboxNs⟩, hkeysNs⟩, hcaNs⟩,
    hirrC⟩, hasymC⟩, hdisj⟩, hrules⟩, hchains⟩ := hcan
  have hAn : h ∉ A.objProps := fun hm => by rw [List.contains_iff_mem.mpr hm] at hAnC; cases hAnC
  have hBn : h ∉ B.objProps := fun hm => by rw [List.contains_iff_mem.mpr hm] at hBnC; cases hBnC
  have hirr : h ∉ p.chars.irreflexive := fun hm => by rw [List.contains_iff_mem.mpr hm] at hirrC; cases hirrC
  have hasym : h ∉ p.chars.asymmetric := fun hm => by rw [List.contains_iff_mem.mpr hm] at hasymC; cases hasymC
  constructor
  · rintro ⟨i, hm, x₀, hroot⟩
    let j := addProdRole i h A B hnt hnb
    have hmono : ∀ r x y, i.objectProperties r x y → j.objectProperties r x y := by
      intro r x y hr
      by_cases he : r = h
      · subst he; simp only [j, addProdRole, ↓reduceIte]; exact Or.inl hr
      · simpa [j, addProdRole, he] using hr
    have hmonoO : ∀ r x y, holdsOriented i r x y → holdsOriented j r x y := by
      rintro ⟨rn, _ | _⟩ x y hr <;> exact hmono rn _ _ hr
    refine ⟨j, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.subData, hm.disjointData, hm.funcData,
      ?_, ?_, ?_, ?_, ?_, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩,
      x₀, (holds_addProdRole_expandProdRole i hnt hnb hrootNs x₀).mpr hroot⟩
    · intro q hq x hx
      have ⟨hs1, hs2⟩ := htboxNs q hq
      exact (holds_addProdRole_expandProdRole i hnt hnb hs2 x).mpr
        (hm.tbox ⟨Concept.expandProdRole h A B q.sub, Concept.expandProdRole h A B q.sup⟩
          (List.mem_map.mpr ⟨q, hq, rfl⟩) x
          ((holds_addProdRole_expandProdRole i hnt hnb hs1 x).mp hx))
    · intro rs hrs x y hxy
      have hne : rs.1.1 ≠ h := hrules rs hrs
      exact hmonoO rs.2 x y (hm.rules rs hrs x y
        ((holdsOriented_addProdRole_ne i hnt hnb hne x y).mp hxy))
    · intro c' hc' x y hp
      rw [hsplit] at hc'
      rcases List.mem_append.mp hc' with hpre | hrest
      · have hmem : c' ∈ pre ++ post := List.mem_append_left _ hpre
        have hne : ∀ r ∈ c'.body, r.1 ≠ h := fun r hr => hchains c' hmem r hr
        exact hmono c'.head x y (hm.chains c' hmem x y ((objPath_addProdRole_ne i hnt hnb hne x y).mp hp))
      · rcases List.mem_cons.mp hrest with rfl | hpost
        · obtain ⟨hAx, hBy⟩ := (objPath_chainTopEndpoints_iff j htop x y).mp hp
          have hAi : holds i x A := (holds_addProdRole_not_mem i hnt hnb hAn x).mp hAx
          have hBi : holds i y B := (holds_addProdRole_not_mem i hnt hnb hBn y).mp hBy
          simp only [j, addProdRole, h, ↓reduceIte]
          exact Or.inr ⟨hAi, hBi⟩
        · have hmem : c' ∈ pre ++ post := List.mem_append_right _ hpost
          have hne : ∀ r ∈ c'.body, r.1 ≠ h := fun r hr => hchains c' hmem r hr
          exact hmono c'.head x y (hm.chains c' hmem x y ((objPath_addProdRole_ne i hnt hnb hne x y).mp hp))
    · intro r hr x; exact hmono r x x (hm.reflexive r hr x)
    · intro r hr x hxx
      have hne : r ≠ h := fun he => hirr (he ▸ hr)
      exact hm.irreflexive r hr x (by simpa [j, addProdRole, hne] using hxx)
    · intro r hr x y h1 h2
      have hne : r ≠ h := fun he => hasym (he ▸ hr)
      exact hm.asymmetric r hr x y (by simpa [j, addProdRole, hne] using h1)
        (by simpa [j, addProdRole, hne] using h2)
    · intro rs hrs x y ⟨h1, h2⟩
      have ⟨hne1, hne2⟩ := hdisj rs hrs
      exact hm.disjoint rs hrs x y
        ⟨(holdsOriented_addProdRole_ne i hnt hnb hne1 x y).mp h1,
         (holdsOriented_addProdRole_ne i hnt hnb hne2 x y).mp h2⟩
    · intro rd hrd x y hxy
      exact (dataHolds_addProdRole_iff i hnt hnb y rd.2).mpr (hm.dataRanges rd hrd x y hxy)
    · intro k hk x y hx hy hnx hny ho hd
      have ⟨hclsNs, hobjNe⟩ := hkeysNs k hk
      refine hm.keys { k with cls := Concept.expandProdRole h A B k.cls }
        (List.mem_map.mpr ⟨k, hk, rfl⟩) x y
        ((holds_addProdRole_expandProdRole i hnt hnb hclsNs x).mp hx)
        ((holds_addProdRole_expandProdRole i hnt hnb hclsNs y).mp hy)
        hnx hny ?_ hd
      intro r hr
      obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
      exact ⟨z, hnz,
        (holdsOriented_addProdRole_ne i hnt hnb (hobjNe r hr) x z).mp hxz,
        (holdsOriented_addProdRole_ne i hnt hnb (hobjNe r hr) y z).mp hyz⟩
    · intro ac hac
      exact (holds_addProdRole_expandProdRole i hnt hnb (hcaNs ac hac) _).mpr
        (hm.classAssertions (ac.1, Concept.expandProdRole h A B ac.2)
          (List.mem_append_left _ (List.mem_map.mpr ⟨ac, hac, rfl⟩)))
    · intro rab hrab; exact hmono rab.1 _ _ (hm.objAssertions rab hrab)
    · intro rab hrab hrel
      rcases rab with ⟨r, a, b⟩
      by_cases he : r = h
      · subst he
        simp only [j, addProdRole, ↓reduceIte] at hrel
        rcases hrel with hdirect | ⟨hAa, hBb⟩
        · exact hm.negObjAssertions (h, a, b) hrab hdirect
        · have hmem : (a, .disj A.dual (.all (topObjectProperty, false) (.disj (.nom b false) B.dual))) ∈
              (expandTopChainAt p pre c post).classAssertions := by
            apply List.mem_append_right
            exact List.mem_filterMap.mpr ⟨(h, a, b), hrab, by simp [h, A, B]⟩
          have hca := hm.classAssertions _ hmem
          rcases hca with hna | hall
          · exact (holds_dual i (i.individuals a) A).mp hna hAa
          · rcases hall (i.individuals b) (i.topObjectExt _ _) with hneq | hnb'
            · exact hneq rfl
            · exact (holds_dual i (i.individuals b) B).mp hnb' hBb
      · exact hm.negObjAssertions (r, a, b) hrab (by simpa [j, addProdRole, he] using hrel)
  · rintro ⟨i, hm, x₀, hroot⟩
    have hcMem : c ∈ p.chains := by rw [hsplit]; simp
    have hsub : ∀ x y, holds i x A → holds i y B → i.objectProperties h x y := fun x y hAx hBy =>
      hm.chains c hcMem x y ((objPath_chainTopEndpoints_iff i htop x y).mpr ⟨hAx, hBy⟩)
    have hexp (d : Concept) (hns : d.noSimpleRole h = true) (x : i.Object) :
        holds i x (Concept.expandProdRole h A B d) ↔ holds i x d :=
      (holds_addProdRole_expandProdRole i hnt hnb hns x).symm.trans
        (holds_addProdRole_same_of_sub i hnt hnb hsub d x)
    refine ⟨i, ⟨?_, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, ?_, ?_, hm.objAssertions,
      hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩,
      x₀, (hexp p.root hrootNs x₀).mpr hroot⟩
    · intro q hq x hx
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
      have ⟨hs1, hs2⟩ := htboxNs q₀ hq₀
      exact (hexp q₀.sup hs2 x).mpr (hm.tbox q₀ hq₀ x ((hexp q₀.sub hs1 x).mp hx))
    · intro c' hc' x y hp
      rcases List.mem_append.mp hc' with hpre | hpost
      · exact hm.chains c' (by rw [hsplit]; simp [hpre]) x y hp
      · exact hm.chains c' (by rw [hsplit]; simp [hpost]) x y hp
    · intro k hk x y hx hy hnx hny ho hd
      obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.mp hk
      have ⟨hclsNs, _⟩ := hkeysNs k₀ hk₀
      exact hm.keys k₀ hk₀ x y ((hexp k₀.cls hclsNs x).mp hx) ((hexp k₀.cls hclsNs y).mp hy)
        hnx hny ho hd
    · intro ac hac
      rcases List.mem_append.mp hac with hmap | hextra
      · obtain ⟨ac₀, hac₀, rfl⟩ := List.mem_map.mp hmap
        exact (hexp ac₀.2 (hcaNs ac₀ hac₀) _).mpr (hm.classAssertions ac₀ hac₀)
      · obtain ⟨⟨r, a, b⟩, hrab, hres⟩ := List.mem_filterMap.mp hextra
        dsimp only at hres
        split at hres
        · rename_i he
          have hr : r = h := beq_iff_eq.mp he
          subst hr
          have hpair := Option.some.inj hres
          rw [← hpair]
          by_cases hAa : holds i (i.individuals a) A
          · refine Or.inr fun y _ => ?_
            by_cases hy : y = i.individuals b
            · subst hy
              refine Or.inr ((holds_dual i _ B).mpr fun hBb => ?_)
              exact hm.negObjAssertions (h, a, b) hrab (hsub _ _ hAa hBb)
            · exact Or.inl hy
          · exact Or.inl ((holds_dual i _ A).mpr hAa)
        · cases hres

private theorem expandTopChainAt_count_lt {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true) :
    ((expandTopChainAt p pre c post).chains.filter hasTopInBody).length <
      (p.chains.filter hasTopInBody).length := by
  simp only [expandTopChainAt, List.filter_append, List.length_append]
  rw [hsplit]
  simp only [List.filter_append, List.filter_cons, htop, ↓reduceIte,
    List.length_append, List.length_cons]
  omega

def lowerTopChainStep (p : Problem) (pre : List Chain) (c : Chain) (post : List Chain) : Problem :=
  if canExpandTopChain p pre c post then expandTopChainAt p pre c post
  else replaceTopChainAt p pre c post

private theorem lowerTopChainStep_sat_iff {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true) :
    (lowerTopChainStep p pre c post).Sat ↔ p.Sat := by
  unfold lowerTopChainStep
  split
  · rename_i hcan
    exact expandTopChainAt_sat_iff hsplit htop hcan
  · exact replaceTopChainAt_sat_iff hsplit htop

private theorem lowerTopChainStep_count_lt {p : Problem} {pre post : List Chain} {c : Chain}
    (hsplit : p.chains = pre ++ c :: post) (htop : hasTopInBody c = true) :
    ((lowerTopChainStep p pre c post).chains.filter hasTopInBody).length <
      (p.chains.filter hasTopInBody).length := by
  unfold lowerTopChainStep
  split
  · exact expandTopChainAt_count_lt hsplit htop
  · exact replaceTopChainAt_count_lt hsplit htop

/-- Exhaustively eliminate every chain whose body contains `owl:topObjectProperty`,
expanding sink non-simple chains directly via `expandTopChainAt` and falling back
to the nominal bridge `replaceTopChainAt` when the head feeds further role axioms
or `HasKey`. -/
def Problem.lowerTopChains (p : Problem) : Problem :=
  match h : splitFirst hasTopInBody p.chains with
  | none => p
  | Option.some (pre, c, post) =>
    have hs := splitFirst_some h
    have _ : ((lowerTopChainStep p pre c post).chains.filter hasTopInBody).length <
        (p.chains.filter hasTopInBody).length :=
      lowerTopChainStep_count_lt hs.1 hs.2
    (lowerTopChainStep p pre c post).lowerTopChains
termination_by (p.chains.filter hasTopInBody).length

theorem Problem.lowerTopChains_sat_iff (p : Problem) :
    p.lowerTopChains.Sat ↔ p.Sat := by
  fun_induction Problem.lowerTopChains p with
  | case1 p hnone => exact Iff.rfl
  | case2 p pre c post hsome hs _ ih =>
    exact ih.trans (lowerTopChainStep_sat_iff hs.1 hs.2)

theorem Problem.lowerTopChains_noTopInBody (p : Problem) :
    ∀ c ∈ p.lowerTopChains.chains, hasTopInBody c = false := by
  fun_induction Problem.lowerTopChains p with
  | case1 p hnone => exact splitFirst_none hnone
  | case2 p pre c post hsome hs _ ih => exact ih

/-- Structural invariant preserved across every step of `Problem.lowerTopChains`. -/
structure TopChainInv (p : Problem) : Prop where
  root : p.root.isSROIQDWithTop = true
  tbox : ∀ q ∈ p.tbox, q.sub.isSROIQDWithTop = true ∧ q.sup.isSROIQDWithTop = true
  rules : ∀ rs ∈ p.rules, isCoreObjPropIRI rs.1.1 = true ∧ isCoreObjPropIRI rs.2.1 = true
  chains : ∀ c ∈ p.chains, isCoreObjPropIRI c.head = true ∧ 2 ≤ c.body.length ∧
    ∀ r ∈ c.body, isObjPropOrTop r.1 = true
  reflexive : ∀ r ∈ p.chars.reflexive, isCoreObjPropIRI r = true
  irreflexive : ∀ r ∈ p.chars.irreflexive, isCoreObjPropIRI r = true
  asymmetric : ∀ r ∈ p.chars.asymmetric, isCoreObjPropIRI r = true
  disjoint : ∀ rs ∈ p.chars.disjoint, isCoreObjPropIRI rs.1.1 = true ∧ isCoreObjPropIRI rs.2.1 = true
  classAssertions : ∀ ac ∈ p.classAssertions, ac.2.isSROIQDWithTop = true
  objAssertions : ∀ rab ∈ p.objAssertions, isCoreObjPropIRI rab.1 = true
  negObjAssertions : ∀ rab ∈ p.negObjAssertions, isCoreObjPropIRI rab.1 = true
  keys : ∀ k ∈ p.keys, k.cls.isSROIQDWithTop = true ∧
    (∀ r ∈ k.objProps, isCoreObjPropIRI r.1 = true) ∧
    (∀ dp ∈ k.dataProps, isCoreDataPropIRI dp = true)
  subData : ∀ rs ∈ p.subData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  disjointData : ∀ rs ∈ p.disjointData, isCoreDataPropIRI rs.1 = true ∧ isCoreDataPropIRI rs.2 = true
  funcData : ∀ dp ∈ p.funcData, isCoreDataPropIRI dp = true
  dataRanges : ∀ rd ∈ p.dataRanges, isCoreDataPropIRI rd.1 = true ∧ rd.2.isSROIQD = true
  dataAssertions : ∀ dal ∈ p.dataAssertions, isCoreDataPropIRI dal.1 = true ∧
    (Sabrina.OWL2.Datatypes.decodeLiteral dal.2.2).isSome = true
  negDataAssertions : ∀ dal ∈ p.negDataAssertions, isCoreDataPropIRI dal.1 = true ∧
    (Sabrina.OWL2.Datatypes.decodeLiteral dal.2.2).isSome = true
  simple : p.checkSimple = true
  ranked : ∃ rank : Rank,
    Sabrina.RoleChains.Ranked rank p.rules (p.chains.filter fun c => !hasTopInBody c)

private theorem foldr_some_isSROIQDWithTop {rs : List OrientedRole}
    (h : ∀ r ∈ rs, isObjPropOrTop r.1 = true) :
    (rs.foldr Concept.some .top).isSROIQDWithTop = true := by
  induction rs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldr_cons, Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨h a (List.mem_cons_self ..), ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

private theorem foldr_some_countedRoles_nil (rs : List OrientedRole) :
    (rs.foldr Concept.some .top).countedRoles = [] := by
  induction rs with
  | nil => rfl
  | cons a rest ih => simpa [List.foldr_cons, Concept.countedRoles] using ih

private theorem chainTopEndpoints_isSROIQDWithTop {body : List OrientedRole}
    (h : ∀ r ∈ body, isObjPropOrTop r.1 = true) :
    (chainTopEndpoints body).1.isSROIQDWithTop = true ∧
    (chainTopEndpoints body).2.isSROIQDWithTop = true ∧
    (chainTopEndpoints body).1.countedRoles = [] ∧
    (chainTopEndpoints body).2.countedRoles = [] := by
  have hsub := splitAtTop_roles_subset body
  unfold chainTopEndpoints
  cases hs : splitAtTop body with
  | mk pre tl =>
    simp only [hs] at hsub
    cases tl with
    | nil => simp [Concept.isSROIQDWithTop, Concept.countedRoles]
    | cons seg rest =>
      dsimp only
      have hmids : ∀ ms : List (List OrientedRole),
          (∀ m ∈ ms, ∀ r ∈ m, isObjPropOrTop r.1 = true) →
          (ms.foldr (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc)
            (pre.foldr Concept.some .top)).isSROIQDWithTop = true ∧
          (ms.foldr (fun m acc => .conj (.some (topObjectProperty, false) (m.foldr Concept.some .top)) acc)
            (pre.foldr Concept.some .top)).countedRoles = [] := by
        intro ms hms
        induction ms with
        | nil =>
          exact ⟨foldr_some_isSROIQDWithTop (fun r hr => h r (hsub.1 r hr)),
            foldr_some_countedRoles_nil pre⟩
        | cons m tail iht =>
          have ih' := iht fun x hx => hms x (List.mem_cons_of_mem _ hx)
          simp only [List.foldr_cons, Concept.isSROIQDWithTop, Concept.countedRoles,
            Bool.and_eq_true, List.append_eq_nil_iff]
          refine ⟨⟨⟨by simp [isObjPropOrTop],
            foldr_some_isSROIQDWithTop (hms m (List.mem_cons_self ..))⟩, ih'.1⟩,
            ⟨foldr_some_countedRoles_nil m, ih'.2⟩⟩
      have h1 := hmids _ (fun m hm r hr => h r (hsub.2 m (List.dropLast_subset _ hm) r hr))
      have hlast : (seg :: rest).getLast (List.cons_ne_nil seg rest) ∈ seg :: rest :=
        List.getLast_mem _
      have h2 : ((flipWord ((seg :: rest).getLast (List.cons_ne_nil seg rest))).foldr Concept.some .top).isSROIQDWithTop = true := by
        apply foldr_some_isSROIQDWithTop
        intro r hr
        simp only [flipWord, List.mem_reverse, List.mem_map] at hr
        obtain ⟨r0, hr0, rfl⟩ := hr
        exact h r0 (hsub.2 _ hlast r0 hr0)
      exact ⟨h1.1, h2, h1.2, foldr_some_countedRoles_nil _⟩

private theorem expandProdRole_isSROIQDWithTop {h : IRI} {A B : Concept}
    (hA : A.isSROIQDWithTop = true) (hB : B.isSROIQDWithTop = true) :
    ∀ c, c.isSROIQDWithTop = true → (Concept.expandProdRole h A B c).isSROIQDWithTop = true := by
  intro c hc
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => exact hc
  | conj a b iha ihb | disj a b iha ihb =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at hc
    simp only [Concept.expandProdRole, Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨iha hc.1, ihb hc.2⟩
  | some r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at hc
    have htopOr : isObjPropOrTop topObjectProperty = true := by simp [isObjPropOrTop]
    unfold Concept.expandProdRole
    dsimp only
    by_cases hr : r.1 == h
    · cases hb : r.2 <;> simp [hr, Concept.isSROIQDWithTop, htopOr, hc.1, hA, hB, ih hc.2]
    · simp [hr, Concept.isSROIQDWithTop, hc.1, ih hc.2]
  | all r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at hc
    have htopOr : isObjPropOrTop topObjectProperty = true := by simp [isObjPropOrTop]
    unfold Concept.expandProdRole
    dsimp only
    by_cases hr : r.1 == h
    · cases hb : r.2 <;> simp [hr, Concept.isSROIQDWithTop, Concept.isSROIQDWithTop_dual, htopOr, hc.1, hA, hB, ih hc.2]
    · simp [hr, Concept.isSROIQDWithTop, hc.1, ih hc.2]
  | min n r c ih | max n r c ih =>
    simp only [Concept.isSROIQDWithTop, Bool.and_eq_true] at hc
    simp only [Concept.expandProdRole, Concept.isSROIQDWithTop, Bool.and_eq_true]
    exact ⟨hc.1, ih hc.2⟩

private theorem expandProdRole_countedRoles_subset {h : IRI} {A B : Concept}
    (hAc : A.countedRoles = []) (hBc : B.countedRoles = []) (c : Concept) :
    ∀ r ∈ (Concept.expandProdRole h A B c).countedRoles, r ∈ c.countedRoles := by
  induction c with
  | top | bottom | lit | nom | self
  | dataSome | dataAll | dataValue | dataMin | dataMax => intro r hr; exact hr
  | conj a b iha ihb | disj a b iha ihb =>
    intro r hr
    simp only [Concept.expandProdRole, Concept.countedRoles, List.mem_append] at hr ⊢
    exact hr.elim (Or.inl ∘ iha r) (Or.inr ∘ ihb r)
  | some r c ih =>
    intro s hs
    unfold Concept.expandProdRole at hs
    split at hs
    · split at hs <;> simp [Concept.countedRoles, hAc, hBc] at hs <;> exact ih s hs
    · exact ih s hs
  | all r c ih =>
    intro s hs
    unfold Concept.expandProdRole at hs
    split at hs
    · split at hs <;> simp [Concept.countedRoles, Concept.countedRoles_dual, hAc, hBc] at hs <;> exact ih s hs
    · exact ih s hs
  | min n r c ih | max n r c ih =>
    intro s hs
    simp only [Concept.expandProdRole, Concept.countedRoles, List.mem_cons] at hs ⊢
    exact hs.elim Or.inl (Or.inr ∘ ih s)

private theorem simpleRoles_subset_checkSimple {p q : Problem}
    (hsim : p.checkSimple = true)
    (hrules : q.rules = p.rules)
    (hsub : ∀ r ∈ q.simpleRoles, r ∈ p.simpleRoles)
    (hheads : ∀ c ∈ q.chains, 2 ≤ c.body.length → ∃ c0 ∈ p.chains, 2 ≤ c0.body.length ∧ c0.head = c.head) :
    q.checkSimple = true := by
  rw [Problem.checkSimple_iff] at hsim ⊢
  intro r hr s hs hc
  rw [hrules] at hs
  apply hsim r (hsub r hr) s hs
  rcases hc with hb | ⟨c, hcm, hlen, hhd⟩
  · exact Or.inl hb
  · obtain ⟨c0, hc0, hl0, hh0⟩ := hheads c hcm hlen
    exact Or.inr ⟨c0, hc0, hl0, hh0.trans hhd⟩

private theorem expandTopChainAt_inv {p : Problem} {pre post : List Chain} {c : Chain}
    (hinv : TopChainInv p) (hsplit : p.chains = pre ++ c :: post) (_htop : hasTopInBody c = true) :
    TopChainInv (expandTopChainAt p pre c post) := by
  have hcMem : c ∈ p.chains := by rw [hsplit]; simp
  obtain ⟨hA, hB, hAc, hBc⟩ := chainTopEndpoints_isSROIQDWithTop (hinv.chains c hcMem).2.2
  have hsubSimple : ∀ r ∈ (expandTopChainAt p pre c post).simpleRoles, r ∈ p.simpleRoles := by
    intro r hr
    simp only [expandTopChainAt, Problem.simpleRoles, List.mem_eraseDups, List.mem_append,
      List.mem_flatMap, List.mem_map] at hr ⊢
    rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (expandProdRole_countedRoles_subset hAc hBc _ r h1)))))
    · rcases h2 with ⟨q, ⟨q0, hq0, rfl⟩, hrq⟩
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q0, hq0,
        hrq.elim (Or.inl ∘ expandProdRole_countedRoles_subset hAc hBc _ r)
                 (Or.inr ∘ expandProdRole_countedRoles_subset hAc hBc _ r)⟩))))
    · rcases h3 with ⟨k, ⟨k0, hk0, rfl⟩, hrk⟩
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k0, hk0, expandProdRole_countedRoles_subset hAc hBc _ r hrk⟩)))
    · rcases h4 with ⟨ac, hac, hrac⟩
      rcases hac with ⟨ac0, hac0, rfl⟩ | hneg
      · exact Or.inl (Or.inl (Or.inr ⟨ac0, hac0, expandProdRole_countedRoles_subset hAc hBc _ r hrac⟩))
      · obtain ⟨e, _, he⟩ := List.mem_filterMap.mp hneg
        split at he
        · cases he
          simp [Concept.countedRoles, Concept.countedRoles_dual, hAc, hBc] at hrac
        · cases he
    · exact Or.inl (Or.inr h5)
    · exact Or.inr h6
  refine ⟨expandProdRole_isSROIQDWithTop hA hB _ hinv.root, ?_, hinv.rules, ?_,
    hinv.reflexive, hinv.irreflexive, hinv.asymmetric, hinv.disjoint, ?_,
    hinv.objAssertions, hinv.negObjAssertions, ?_,
    hinv.subData, hinv.disjointData, hinv.funcData, hinv.dataRanges,
    hinv.dataAssertions, hinv.negDataAssertions, ?_, ?_⟩
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact ⟨expandProdRole_isSROIQDWithTop hA hB _ (hinv.tbox q0 hq0).1,
           expandProdRole_isSROIQDWithTop hA hB _ (hinv.tbox q0 hq0).2⟩
  · intro c' hc'
    refine hinv.chains c' ?_
    rw [hsplit]
    rcases List.mem_append.mp hc' with h1 | h2
    · simp [h1]
    · simp [h2]
  · intro ac hac
    rcases List.mem_append.mp hac with hmap | hneg
    · obtain ⟨ac0, hac0, rfl⟩ := List.mem_map.mp hmap
      exact expandProdRole_isSROIQDWithTop hA hB _ (hinv.classAssertions ac0 hac0)
    · obtain ⟨⟨r, a, b⟩, _, he⟩ := List.mem_filterMap.mp hneg
      by_cases heq : r == c.head
      · simp only [heq, ↓reduceIte, Option.some.injEq] at he
        subst he
        simp [Concept.isSROIQDWithTop, Concept.isSROIQDWithTop_dual, isObjPropOrTop, hA, hB]
      · simp [heq] at he
  · intro k hk
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    exact ⟨expandProdRole_isSROIQDWithTop hA hB _ (hinv.keys k0 hk0).1, (hinv.keys k0 hk0).2⟩
  · refine simpleRoles_subset_checkSimple hinv.simple rfl hsubSimple ?_
    intro c' hc' hlen'
    refine ⟨c', ?_, hlen', rfl⟩
    rw [hsplit]
    rcases List.mem_append.mp hc' with h1 | h2
    · simp [h1]
    · simp [h2]
  · obtain ⟨rank, hrank⟩ := hinv.ranked
    refine ⟨rank, hrank.1, ?_⟩
    intro c' hc'
    have h1 := List.mem_filter.mp hc'
    refine hrank.2 c' (List.mem_filter.mpr ⟨?_, h1.2⟩)
    rw [hsplit]
    rcases List.mem_append.mp h1.1 with hpre | hpost
    · simp [hpre]
    · simp [hpost]

private theorem replaceTopChainAt_inv {p : Problem} {pre post : List Chain} {c : Chain}
    (hinv : TopChainInv p) (hsplit : p.chains = pre ++ c :: post) (_htop : hasTopInBody c = true) :
    TopChainInv (replaceTopChainAt p pre c post) := by
  have hcMem : c ∈ p.chains := by rw [hsplit]; simp
  obtain ⟨hA, hB, hAc, hBc⟩ := chainTopEndpoints_isSROIQDWithTop (hinv.chains c hcMem).2.2
  have hw1_forb := freshRole1_not_forbidden p
  have hw2_forb := freshRole2_not_forbidden p
  have hw1_nt : freshRole1 p ≠ topObjectProperty := fun h => hw1_forb (h ▸ List.mem_cons_self ..)
  have hw1_nb : freshRole1 p ≠ bottomObjectProperty :=
    fun h => hw1_forb (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hw2_nt : freshRole2 p ≠ topObjectProperty := fun h => hw2_forb (h ▸ List.mem_cons_self ..)
  have hw2_nb : freshRole2 p ≠ bottomObjectProperty :=
    fun h => hw2_forb (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hw1_p : freshRole1 p ∉ p.objProps :=
    fun h => hw1_forb (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hw2_p : freshRole2 p ∉ p.objProps :=
    fun h => hw2_forb (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hw1_core : isCoreObjPropIRI (freshRole1 p) = true := by
    simp [isCoreObjPropIRI, hw1_nt, hw1_nb]
  have hw2_core : isCoreObjPropIRI (freshRole2 p) = true := by
    simp [isCoreObjPropIRI, hw2_nt, hw2_nb]
  have hparts1 := objProps_parts hw1_p
  have hparts2 := objProps_parts hw2_p
  have hsubSimple : ∀ r ∈ (replaceTopChainAt p pre c post).simpleRoles, r ∈ p.simpleRoles := by
    intro r hr
    simp only [replaceTopChainAt, replaceTopChainWith, Problem.simpleRoles, List.mem_eraseDups,
      List.mem_append, List.mem_flatMap, List.mem_cons] at hr ⊢
    rcases hr with ((((h1 | h2) | h3) | h4) | h5) | h6
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))
    · rcases h2 with ⟨q, hq, hrq⟩
      rcases hq with rfl | rfl | hq0
      · simp [Concept.countedRoles, hAc] at hrq
      · simp [Concept.countedRoles, hBc] at hrq
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq0, hrq⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
    · exact Or.inl (Or.inl (Or.inr h4))
    · exact Or.inl (Or.inr h5)
    · exact Or.inr h6
  refine ⟨hinv.root, ?_, hinv.rules, ?_,
    hinv.reflexive, hinv.irreflexive, hinv.asymmetric, hinv.disjoint,
    hinv.classAssertions, hinv.objAssertions, hinv.negObjAssertions, hinv.keys,
    hinv.subData, hinv.disjointData, hinv.funcData, hinv.dataRanges,
    hinv.dataAssertions, hinv.negDataAssertions, ?_, ?_⟩
  · intro q hq
    simp only [replaceTopChainAt, replaceTopChainWith, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq0
    · exact ⟨hA, by simp [Concept.isSROIQDWithTop, isObjPropOrTop, hw1_core]⟩
    · exact ⟨hB, by simp [Concept.isSROIQDWithTop, isObjPropOrTop, hw2_core]⟩
    · exact hinv.tbox q hq0
  · intro c' hc'
    simp only [replaceTopChainAt, replaceTopChainWith, List.mem_append, List.mem_cons] at hc'
    rcases hc' with hpre | rfl | hpost
    · exact hinv.chains c' (by rw [hsplit]; simp [hpre])
    · refine ⟨(hinv.chains c hcMem).1, by simp [Chain.named], ?_⟩
      intro r hr
      simp only [Chain.named, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨n, rfl | rfl, rfl⟩ := hr
      · simp [isObjPropOrTop, hw1_core]
      · simp [isObjPropOrTop, hw2_core]
    · exact hinv.chains c' (by rw [hsplit]; simp [hpost])
  · refine simpleRoles_subset_checkSimple hinv.simple rfl hsubSimple ?_
    intro c' hc' hlen'
    simp only [replaceTopChainAt, replaceTopChainWith, List.mem_append, List.mem_cons] at hc'
    rcases hc' with hpre | rfl | hpost
    · exact ⟨c', by rw [hsplit]; simp [hpre], hlen', rfl⟩
    · exact ⟨c, hcMem, (hinv.chains c hcMem).2.1, rfl⟩
    · exact ⟨c', by rw [hsplit]; simp [hpost], hlen', rfl⟩
  · obtain ⟨rank, hrank⟩ := hinv.ranked
    let rank' : Rank := fun r => if r == freshRole1 p || r == freshRole2 p then 0 else rank r + 1
    have hshift (r : IRI) (h1 : r ≠ freshRole1 p) (h2 : r ≠ freshRole2 p) :
        rank' r = rank r + 1 := by
      simp [rank', h1, h2]
    refine ⟨rank', ?_, ?_⟩
    · intro r s hrs
      have hr := hparts1.2.2.1 (r, s) hrs
      have hs := hparts2.2.2.1 (r, s) hrs
      rw [hshift r.1 hr.1 hs.1, hshift s.1 hr.2 hs.2]
      exact Nat.add_le_add_right (hrank.1 r s hrs) 1
    · intro c' hc'
      have hfm := List.mem_filter.mp hc'
      simp only [replaceTopChainAt, replaceTopChainWith, List.mem_append, List.mem_cons] at hfm
      rcases hfm.1 with hpre | rfl | hpost
      · have hc0 : c' ∈ p.chains := by rw [hsplit]; simp [hpre]
        have horig := hrank.2 c' (List.mem_filter.mpr ⟨hc0, hfm.2⟩)
        refine ⟨horig.1, ?_⟩
        have hch1 := hparts1.2.2.2.1 c' hc0
        have hch2 := hparts2.2.2.2.1 c' hc0
        have hlt : ∀ r ∈ c'.body, rank r.1 < rank c'.head → rank' r.1 < rank' c'.head := by
          intro r hr hlt
          rw [hshift r.1 (hch1.2 r hr) (hch2.2 r hr), hshift c'.head hch1.1 hch2.1]
          omega
        rcases horig.2 with h1 | h2 | ⟨rest, h3, h4⟩ | ⟨rest, h3, h4⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl fun r hr => hlt r hr (h2 r hr))
        · exact Or.inr (Or.inr (Or.inl ⟨rest, h3, fun r hr => hlt r (by rw [h3]; simp [hr]) (h4 r hr)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rest, h3, fun r hr => hlt r (by rw [h3]; simp [hr]) (h4 r hr)⟩))
      · refine ⟨by simp [Chain.named], Or.inr (Or.inl ?_)⟩
        have hchHead : rank' c.head = rank c.head + 1 :=
          hshift c.head (hparts1.2.2.2.1 c hcMem).1 (hparts2.2.2.2.1 c hcMem).1
        have hw1z : rank' (freshRole1 p) = 0 := by
          dsimp only [rank']
          rw [beq_self_eq_true, Bool.true_or]; rfl
        have hw2z : rank' (freshRole2 p) = 0 := by
          dsimp only [rank']
          rw [beq_self_eq_true, Bool.or_true]; rfl
        intro r hr
        simp only [Chain.named, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨n, hn, rfl⟩ := hr
        change rank' n < rank' c.head
        rw [hchHead]
        rcases hn with he | he
        · rw [he, hw1z]; exact Nat.zero_lt_succ _
        · rw [he, hw2z]; exact Nat.zero_lt_succ _
      · have hc0 : c' ∈ p.chains := by rw [hsplit]; simp [hpost]
        have horig := hrank.2 c' (List.mem_filter.mpr ⟨hc0, hfm.2⟩)
        refine ⟨horig.1, ?_⟩
        have hch1 := hparts1.2.2.2.1 c' hc0
        have hch2 := hparts2.2.2.2.1 c' hc0
        have hlt : ∀ r ∈ c'.body, rank r.1 < rank c'.head → rank' r.1 < rank' c'.head := by
          intro r hr hlt
          rw [hshift r.1 (hch1.2 r hr) (hch2.2 r hr), hshift c'.head hch1.1 hch2.1]
          omega
        rcases horig.2 with h1 | h2 | ⟨rest, h3, h4⟩ | ⟨rest, h3, h4⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl fun r hr => hlt r hr (h2 r hr))
        · exact Or.inr (Or.inr (Or.inl ⟨rest, h3, fun r hr => hlt r (by rw [h3]; simp [hr]) (h4 r hr)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rest, h3, fun r hr => hlt r (by rw [h3]; simp [hr]) (h4 r hr)⟩))

theorem Problem.lowerTopChains_inv {p : Problem} (hinv : TopChainInv p) :
    TopChainInv p.lowerTopChains := by
  fun_induction Problem.lowerTopChains p with
  | case1 p _ => exact hinv
  | case2 p pre c post hsome hs _ ih =>
    apply ih
    unfold lowerTopChainStep
    split
    · exact expandTopChainAt_inv hinv hs.1 hs.2
    · exact replaceTopChainAt_inv hinv hs.1 hs.2

/-! ### 5. Composed verified decision adapter (`decideWithTopRoleAxioms?`) -/

/-- Complete verified lowering pass for bottom properties, recursive chain aliases,
universal-role closure, non-chain universal role axioms, and universal-role chain bodies. -/
def Problem.lowerAllTopRoleAxioms (p : Problem) : Problem :=
  p.lowerBottom.lowerChainAliases.collapseUnivRoles.lowerTopRoleAxioms.lowerTopChains.lowerChainAliases

theorem Problem.lowerAllTopRoleAxioms_sat_iff (p : Problem) :
    p.lowerAllTopRoleAxioms.Sat ↔ p.Sat :=
  p.lowerBottom.lowerChainAliases.collapseUnivRoles.lowerTopRoleAxioms.lowerTopChains.lowerChainAliases_sat_iff.trans
    (p.lowerBottom.lowerChainAliases.collapseUnivRoles.lowerTopRoleAxioms.lowerTopChains_sat_iff.trans
      (p.lowerBottom.lowerChainAliases.collapseUnivRoles.lowerTopRoleAxioms_sat_iff.trans
        (p.lowerBottom.lowerChainAliases.collapseUnivRoles_sat_iff.trans
          (p.lowerBottom.lowerChainAliases_sat_iff.trans p.lowerBottom_sat_iff))))

namespace Termination.BlockedForest

/-- Unified verified fuel-free decision adapter supporting `owl:topObjectProperty`
(and its inverse) across class restrictions, unary role inclusions, role
characteristics, `HasKey`, object property assertions, and role chain bodies,
together with OWL 2 DL §11.1–§11.2 simplicity validation, bottom-property
elimination, and recursive chain-alias lowering. -/
def decideWithTopRoleAxioms? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (_, p) =>
    if p.root = .top ∧ p.checkSimpleWithTop = true then
      let q := p.lowerAllTopRoleAxioms
      (findRank q.rules q.chains).bind fun rank =>
        if h : q.isSROIQDWithTop rank = true then
          Option.some (decideSROIQDWithTopBool h)
        else none
    else none

theorem decideWithTopRoleAxioms_iff {o : Ontology} {b : Bool}
    (h : decideWithTopRoleAxioms? o = Option.some b) :
    b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideWithTopRoleAxioms?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, hrest⟩ := h
  split at hrest
  · rename_i hroot
    simp only [Option.bind_eq_some_iff] at hrest
    obtain ⟨rank, _, hb⟩ := hrest
    split at hb
    · rename_i hadmit
      cases hb
      exact (decideSROIQDWithTopBool_iff hadmit).trans
        (p.lowerAllTopRoleAxioms_sat_iff.trans
          ((Normalize.normalizeWithDefs_sat_iff hnorm).trans
            (satisfiable_iff_sat p hroot.1)).symm)
    · contradiction
  · contradiction

theorem decideWithTopRoleAxioms_unsat_iff {o : Ontology} {b : Bool}
    (h : decideWithTopRoleAxioms? o = Option.some b) :
    b = false ↔ ¬ Satisfiable datatypeMap o := by
  rw [← decideWithTopRoleAxioms_iff h]
  cases b <;> simp

#print axioms univRoles_universal
#print axioms Problem.collapseUnivRoles_sat_iff
#print axioms Problem.lowerTopRoleAxioms_models_iff
#print axioms Problem.lowerTopRoleAxioms_sat_iff
#print axioms objPath_chainTopEndpoints_iff
#print axioms replaceTopChainAt_sat_iff
#print axioms expandTopChainAt_sat_iff
#print axioms Problem.lowerTopChains_sat_iff
#print axioms Problem.lowerTopChains_noTopInBody
#print axioms Problem.lowerAllTopRoleAxioms_sat_iff
#print axioms decideWithTopRoleAxioms_iff
#print axioms decideWithTopRoleAxioms_unsat_iff

end Termination.BlockedForest
end Sabrina.OWL2.SROIQD
