import Sabrina.OWL2.SROIQD.Termination.BlockedBranch
import Sabrina.OWL2.SROIQD.Termination.FiniteLeaves

namespace Sabrina.OWL2.SROIQD.Termination

open Sabrina.ALC (OrientedRole converse holdsRole)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)
open Sabrina.RoleChains (Rank PathRegex)
open Sabrina.RoleChains.SimpleRoles (Simple)
open Sabrina.RoleChains.TransitivePaths (WordPath converse_converse)
open Sabrina.RoleChains.RankedPaths (Generated Edge complete normalize)

namespace BlockedBranch

variable {b : BlockedBranch}

/-- Each entry records the actual child; its target is determined by the
blocking map. Entries are stored with the newest child first. -/
def walkTail (b : BlockedBranch) : List b.Node → b.Node
  | [] => 0
  | c :: _ => b.target c

inductive Walk (b : BlockedBranch) : List b.Node → Prop where
  | root : Walk b []
  | step {xs c} : Walk b xs → b.Child (b.walkTail xs) c → Walk b (c :: xs)

abbrev Path (b : BlockedBranch) := {xs : List b.Node // b.Walk xs}

namespace Path

def root (b : BlockedBranch) : b.Path := ⟨[],.root⟩

def tailNode (x : b.Path) : b.Node := b.walkTail x.val

def extend (x : b.Path) (c : b.Node) (hc : b.Child x.tailNode c) : b.Path :=
  ⟨c :: x.val,.step x.property hc⟩

theorem valid_cons {xs : List b.Node} {c : b.Node} (h : b.Walk (c :: xs)) :
    b.Walk xs ∧ b.Child (b.walkTail xs) c := by
  cases h with
  | step hs hc => exact ⟨hs,hc⟩

theorem tail_unblocked (hw : b.BlockingValid) (x : b.Path) : b.Unblocked x.tailNode := by
  cases x with
  | mk xs hx =>
    induction hx with
    | root => exact root_unblocked hw
    | step _ hc ih => exact child_target_unblocked hw ih hc

/-- Two distinct children stay distinct even when their continuation targets
coincide. The recorded entry is recoverable from the extended path. -/
theorem extend_injective (x : b.Path) {c d : b.Node}
    {hc : b.Child x.tailNode c} {hd : b.Child x.tailNode d}
    (h : x.extend c hc = x.extend d hd) : c = d :=
  (List.cons.inj (congrArg Subtype.val h)).1

theorem lift_sibling_inequality {p : Problem} (cf : b.BlockedClashFree p)
    (x : b.Path) {c d : b.Node} (hc : b.Child x.tailNode c) (hne : (c,d) ∈ b.unequal) :
    ∃ hd : b.Child x.tailNode d, x.extend c hc ≠ x.extend d hd := by
  have h := b.unequal_siblings c d hne
  refine ⟨⟨h.2.1,h.2.2.symm.trans hc.2⟩,?_⟩
  intro he
  obtain rfl := extend_injective x he
  exact cf.unequal c hne

end Path

/-- The third argument is the corresponding neighbor in the template at
`x.tailNode`. The incoming path corresponds to the tail's template parent. -/
def Neighbor (x y : b.Path) (n : b.Node) : Prop :=
  (y = x ∧ n = x.tailNode) ∨ y.val = n :: x.val ∨
    (∃ c, x.val = c :: y.val ∧ n = b.parent x.tailNode)

private theorem neighbor_cases (hw : b.BlockingValid) {x y : b.Path} {n : b.Node}
    (h : Neighbor x y n) :
    (y = x ∧ n = x.tailNode) ∨
    (y.val = n :: x.val ∧ b.Child x.tailNode n) ∨
    (∃ c, x.val = c :: y.val ∧ n = b.parent x.tailNode ∧ b.Child n x.tailNode) := by
  rcases h with h | h | ⟨c,h,e⟩
  · exact .inl h
  · exact .inr (.inl ⟨h,(Path.valid_cons (h ▸ y.property)).2⟩)
  · have hc := (Path.valid_cons (h ▸ x.property)).2
    have ht : x.tailNode = b.target c := congrArg b.walkTail h
    exact .inr (.inr ⟨c,h,e,target_nonroot hw hc.1 ∘ (ht.symm.trans ·),e.symm⟩)

theorem neighbor_functional {x y : b.Path} {v w : b.Node} (hv : Neighbor x y v)
    (hw : Neighbor x y w) : v = w := by
  rcases hv with ⟨rfl,rfl⟩ | hv | ⟨c,hv,rfl⟩ <;>
    rcases hw with ⟨he,rfl⟩ | hw | ⟨d,hw,rfl⟩
  all_goals first
    | rfl
    | exact (List.cons.inj (hv.symm.trans hw)).1
    | (exfalso
       first | subst y | skip
       repeat
         first
         | have h₁ := congrArg List.length hv; clear hv; simp only [List.length_cons] at h₁
         | have h₂ := congrArg List.length hw; clear hw; simp only [List.length_cons] at h₂
       omega)

theorem neighbor_injective (hw : b.BlockingValid) {x y z : b.Path} {n : b.Node}
    (hy : Neighbor x y n) (hz : Neighbor x z n) : y = z := by
  have cmp (w : b.Path) (h : Neighbor x w n) :=
    neighbor_cases hw h
  rcases cmp y hy with ⟨ey,en⟩ | ⟨ey,cy⟩ | ⟨a,ey,en,cy⟩ <;>
    rcases cmp z hz with ⟨ez,em⟩ | ⟨ez,cz⟩ | ⟨c,ez,em,cz⟩
  all_goals first
    | exact ey.trans ez.symm
    | exact Subtype.ext (ey.trans ez.symm)
    | exact Subtype.ext (List.cons.inj (ey.symm.trans ez)).2
    | (exfalso; first
       | exact Nat.lt_irrefl _ (en ▸ child_lt cz)
       | exact Nat.lt_irrefl _ (em ▸ child_lt cy)
       | exact Nat.lt_asymm (child_lt cy) (child_lt cz))

private theorem neighbor_transfer {α : Type} {L : b.Node → List α}
    (matching : ∀ c a, a ∈ L c ↔ a ∈ L (b.target c))
    (parents : ∀ c a, a ∈ L (b.parent c) ↔ a ∈ L (b.parent (b.target c)))
    {x y : b.Path} {n : b.Node} (h : Neighbor x y n) (a : α) :
    a ∈ L n ↔ a ∈ L y.tailNode := by
  rcases h with ⟨rfl,rfl⟩ | h | ⟨c,h,rfl⟩
  · rfl
  · have ht : y.tailNode = b.target n := congrArg b.walkTail h
    rw [ht]
    exact matching n a
  · have ht : x.tailNode = b.target c := congrArg b.walkTail h
    have hc : b.parent c = y.tailNode := (Path.valid_cons (h ▸ x.property)).2.2
    rw [ht,←hc]
    exact (parents c a).symm

theorem neighbor_labels (hw : b.BlockingValid) {x y : b.Path} {n : b.Node}
    (h : Neighbor x y n) (c : Concept) : c ∈ b.labels n ↔ c ∈ b.labels y.tailNode :=
  neighbor_transfer (L := b.labels) (fun n => (target_match (x := n) hw).labels) (fun n => (target_match (x := n) hw).parentLabels) h c

theorem neighbor_guards (hw : b.BlockingValid) {x y : b.Path} {n : b.Node}
    (h : Neighbor x y n) (g : Guard) : g ∈ b.guardLabels n ↔ g ∈ b.guardLabels y.tailNode :=
  neighbor_transfer (L := b.guardLabels) (fun n => (target_match (x := n) hw).guards) (fun n => (target_match (x := n) hw).parentGuards) h g

private theorem neighbor_exists {x : b.Path} {n : b.Node} {r : OrientedRole}
    (h : b.Edge r x.tailNode n) : ∃ y, Neighbor x y n := by
  rcases h with ⟨he,_⟩ | ⟨hc,_⟩ | ⟨hc,_⟩
  · exact ⟨x,.inl ⟨rfl,he.symm⟩⟩
  · exact ⟨x.extend n hc,.inr (.inl rfl)⟩
  · cases hlist : x.val with
    | nil => exact (hc.1 (congrArg b.walkTail hlist)).elim
    | cons c xs =>
      let y : b.Path := ⟨xs,(Path.valid_cons (hlist ▸ x.property)).1⟩
      exact ⟨y,.inr (.inr ⟨c,hlist,hc.2.symm⟩)⟩

def Base (b : BlockedBranch) (r : OrientedRole) (x y : b.Path) : Prop :=
  ∃ n, Neighbor x y n ∧ b.Edge r x.tailNode n

private theorem down_edge_match (hw : b.BlockingValid) {x : b.Path}
    {c : b.Node} (h : b.Child x.tailNode c) (r : OrientedRole) :
    b.Edge r x.tailNode c ↔ b.Edge r (b.parent (b.target c)) (b.target c) :=
  (edge_child_iff (r := r) h).trans (((target_match hw).roles r).trans
    (edge_child_iff ⟨target_nonroot hw h.1,rfl⟩).symm)

theorem base_flip (hw : b.BlockingValid) {r : OrientedRole} {x y : b.Path}
    (he : b.Base r x y) : b.Base (converse r) y x := by
  obtain ⟨n,hn,he⟩ := he
  rcases hn with ⟨rfl,rfl⟩ | h | ⟨c,h,rfl⟩
  · exact ⟨y.tailNode,.inl ⟨rfl,rfl⟩,(b.edge_converse r _ _).mpr he⟩
  · have hc := (Path.valid_cons (h ▸ y.property)).2
    have ht : y.tailNode = b.target n := congrArg b.walkTail h
    refine ⟨b.parent y.tailNode,.inr (.inr ⟨n,h,rfl⟩),?_⟩
    rw [ht]
    exact (b.edge_converse r _ _).mpr ((down_edge_match hw (x := x) hc r).mp he)
  · have hc := (Path.valid_cons (h ▸ x.property)).2
    have ht : x.tailNode = b.target c := congrArg b.walkTail h
    refine ⟨c,.inr (.inl h),?_⟩
    rw [ht] at he
    exact (down_edge_match hw (x := y) hc (converse r)).mpr
      ((b.edge_converse r _ _).mpr he)

theorem base_loop_iff (r : OrientedRole) (x : b.Path) :
    b.Base r x x ↔ b.Edge r x.tailNode x.tailNode := by
  constructor
  · rintro ⟨n,hn,he⟩
    have hself : Neighbor x x x.tailNode := .inl ⟨rfl,rfl⟩
    exact neighbor_functional hn hself ▸ he
  · exact fun h => ⟨x.tailNode,.inl ⟨rfl,rfl⟩,h⟩

def baseInterpretation (b : BlockedBranch) : Sabrina.ALC.Interpretation where
  Domain := b.Path
  nonempty := ⟨Path.root b⟩
  atom := fun c x => .lit c true ∈ b.labels x.tailNode
  role := fun r => b.Base (r,false)

theorem base_role_iff (hw : b.BlockingValid) (r : OrientedRole) (x y : b.Path) :
    holdsRole b.baseInterpretation r x y ↔ b.Base r x y := by
  rcases r with ⟨r,_ | _⟩
  · rfl
  · exact ⟨base_flip hw (r := (r,false)),base_flip hw (r := (r,true))⟩

theorem base_modelsRoles {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p) :
    Sabrina.ALC.modelsRoles b.baseInterpretation p.rules := by
  intro r s hm x y hr
  obtain ⟨n,hn,he⟩ := (base_role_iff hs.blocking r x y).mp hr
  exact (base_role_iff hs.blocking s x y).mpr ⟨n,hn,hs.rules (r,s) hm _ _ he⟩


private theorem ordinaryRole {r : IRI} (h : isCoreObjPropIRI r = true) :
    r ≠ topObjectProperty ∧ r ≠ bottomObjectProperty := by
  simpa [isCoreObjPropIRI] using h

private theorem ordinaryClass {c : IRI} (h : isCoreClassIRI c = true) :
    c ≠ thing ∧ c ≠ nothing := by
  simpa [isCoreClassIRI] using h

/-- Objects are walks of arbitrary finite length. The data component provides
the fixed OWL datatype map, with no ordinary data edges. -/
def toUnraveledInterpretation (b : BlockedBranch) (p : Problem) : Interpretation datatypeMap where
  Object := b.Path
  objectNonempty := ⟨Path.root b⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes c x := if c = thing then True else if c = nothing then False
    else .lit c true ∈ b.labels x.tailNode
  objectProperties r x y := if r = topObjectProperty then True else if r = bottomObjectProperty then False
    else (complete b.baseInterpretation p.rules p.chains).role r x y
  dataProperties r _ _ := r = topDataProperty
  individuals := fun _ => Path.root b
  named := fun x => x = Path.root b
  namedIndividual := fun _ => rfl
  datatypes t y := t = literalDatatype ∨ ∃ v, datatypeMap.valueSpace t v ∧ some v = y
  literalValue := decodeLiteral
  lexicalAgreement := fun _ _ h => h
  thingExt := by simp
  nothingExt := by
    have h : nothing ≠ thing := by decide
    simp [h]
  topObjectExt := by simp
  bottomObjectExt := by
    have h : bottomObjectProperty ≠ topObjectProperty := by decide
    simp [h]
  topDataExt := by simp
  bottomDataExt := by intro _ _; decide
  literalDatatypeExt := by simp
  datatypeAgreement := by
    intro t ht y
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp [hn]
    exact Iff.rfl

theorem unraveled_role_iff (p : Problem) (r : OrientedRole) (hr : isCoreObjPropIRI r.1 = true)
    (x y : b.Path) :
    holdsOriented (b.toUnraveledInterpretation p) r x y ↔
      holdsRole (complete b.baseInterpretation p.rules p.chains) r x y := by
  obtain ⟨h₁,h₂⟩ := ordinaryRole hr
  rcases r with ⟨r,_ | _⟩ <;>
    simp [holdsOriented, holdsRole, toUnraveledInterpretation, h₁, h₂]

theorem extension {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true) {x y : b.Path}
    (he : b.Base r x y) : holdsOriented (b.toUnraveledInterpretation p) r x y := by
  apply (unraveled_role_iff p r hr x y).mpr
  apply (Sabrina.RoleChains.RankedPaths.holdsRole_complete _ _ _ _ _ _).mpr
  refine ⟨[r],(Sabrina.RoleChains.RankedPaths.generated_closed _ _).letter r,?_⟩
  exact ⟨y,(base_role_iff hs.blocking r x y).mpr he,rfl⟩

/-- A chain-generated edge at a simple role must come from one original
oriented edge. Unary promotions already hold on the lifted tree. -/
theorem simple_role_localizes {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    (hSimple : Simple p.rules p.chains r) (x y : b.Path) :
    holdsOriented (b.toUnraveledInterpretation p) r x y ↔ b.Base r x y := by
  constructor
  · intro h
    obtain ⟨word,hw,hpath⟩ := (Sabrina.RoleChains.RankedPaths.holdsRole_complete
      _ _ _ _ _ _).mp ((unraveled_role_iff p r hr x y).mp h)
    obtain ⟨s,rfl,below⟩ := Sabrina.RoleChains.SimpleRoles.generated_simple
      (Sabrina.RoleChains.checkRegular_sound hi.regular) hw hSimple
    obtain ⟨z,hxz,hzy⟩ := hpath
    change z = y at hzy
    subst z
    apply (base_role_iff hs.blocking r x y).mp
    rcases below with he | hbelow
    · exact he ▸ hxz
    · exact Sabrina.ALC.modelsClosure (base_modelsRoles hs) s r hbelow x y hxz
  · exact extension hs hr

private theorem guard_on_path {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {w : List OrientedRole} {x y : b.Path} {g : Guard}
    (hp : WordPath b.baseInterpretation w x y) (hg : g ∈ b.guardLabels x.tailNode)
    (hw : g.state.Matches w) : g.filler ∈ b.labels y.tailNode := by
  induction w generalizing x g with
  | nil =>
    change x = y at hp
    subst x
    exact hs.guardAccept _ g hg (g.state.nullable_iff.mpr hw)
  | cons r w ih =>
    obtain ⟨z,hz,ht⟩ := hp
    obtain ⟨n,hn,he⟩ := (base_role_iff hs.blocking r x z).mp hz
    obtain ⟨state,hm,ha⟩ := (PathRegex.matches_derivative _ _ _).mp hw
    let next : Guard := ⟨state,g.filler⟩
    have hnext : next ∈ g.advance r := List.mem_map.mpr ⟨state,hm,rfl⟩
    have hlocal := hs.guardStep _ _ _ he g hg next hnext
    exact ih (g := next) ht ((neighbor_guards hs.blocking hn next).mp hlocal) ha

theorem universal_label {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    {x y : b.Path} {c : Concept} (hl : .all r c ∈ b.labels x.tailNode)
    (he : holdsOriented (b.toUnraveledInterpretation p) r x y) :
    c ∈ b.labels y.tailNode := by
  obtain ⟨word,hw,hp⟩ := (Sabrina.RoleChains.RankedPaths.holdsRole_complete
    _ _ _ _ _ _).mp ((unraveled_role_iff p r hr x y).mp he)
  have hm := (roleLanguage_accepts hi.regular r word).mpr hw
  exact guard_on_path hs hp
    (hs.guardStart _ (x.tail_unblocked hs.blocking) r c hl)
    (((roleLanguage rank p r).accepts_iff word).mp hm)

private theorem transfer_list {α β : Type} {P : α → Prop} {Q : β → Prop} {R : α → β → Prop}
    (choose : ∀ a, P a → ∃ c, R a c ∧ Q c)
    (inj : ∀ a a' c, R a c → R a' c → a = a') {xs : List α}
    (hn : xs.Nodup) (hp : ∀ a ∈ xs, P a) :
    ∃ ys : List β, ys.length = xs.length ∧ ys.Nodup ∧
      ∀ c ∈ ys, ∃ a ∈ xs, R a c ∧ Q c := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons a xs ih =>
    obtain ⟨c,hr,hq⟩ := choose a (hp a (List.mem_cons_self ..))
    have hnodup := List.nodup_cons.mp hn
    obtain ⟨ys,hlen,hnd,hall⟩ := ih hnodup.2 (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    refine ⟨c :: ys, by simp [hlen], List.nodup_cons.mpr ⟨?_,hnd⟩,?_⟩
    · intro hc
      obtain ⟨a',ha',he,_⟩ := hall c hc
      exact hnodup.1 (inj _ _ _ he hr ▸ ha')
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨a,List.mem_cons_self ..,hr,hq⟩
      · obtain ⟨a',ha',he,hq'⟩ := hall z hz
        exact ⟨a',List.mem_cons_of_mem _ ha',he,hq'⟩

private theorem transfer_atLeast {α β : Type} {P : α → Prop} {Q : β → Prop} {R : α → β → Prop}
    (choose : ∀ a, P a → ∃ c, R a c ∧ Q c)
    (inj : ∀ a a' c, R a c → R a' c → a = a') {n : Nat} (h : AtLeast n P) :
    AtLeast n Q := by
  obtain ⟨xs,hlen,hnd,hp⟩ := h
  obtain ⟨ys,hl,hn,hq⟩ := transfer_list choose inj hnd hp
  exact ⟨ys,hl.trans hlen,hn,fun c hc => (hq c hc).choose_spec.2.2⟩

theorem lift_witness {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true) {x : b.Path} {n : b.Node}
    {c : Concept} (he : b.Edge r x.tailNode n) (hl : c ∈ b.labels n) :
    ∃ y, Neighbor x y n ∧ holdsOriented (b.toUnraveledInterpretation p) r x y ∧
      c ∈ b.labels y.tailNode := by
  obtain ⟨y,hy⟩ := neighbor_exists he
  exact ⟨y,hy,extension hs hr ⟨n,hy,he⟩,(neighbor_labels hs.blocking hy c).mp hl⟩

theorem lift_lower_bound {rank : Rank} {p : Problem} (hs : b.BlockedSaturated rank p)
    {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true) {x : b.Path} {c : Concept} {n : Nat}
    (h : AtLeast n (fun y => b.Edge r x.tailNode y ∧ c ∈ b.labels y)) :
    AtLeast n (fun y : b.Path =>
      holdsOriented (b.toUnraveledInterpretation p) r x y ∧ c ∈ b.labels y.tailNode) :=
  transfer_atLeast (R := fun a y => Neighbor x y a)
    (fun _ ha => lift_witness hs hr ha.1 ha.2) (fun _ _ _ => neighbor_functional) h

theorem reflect_upper_count {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    (hSimple : Simple p.rules p.chains r) {x : b.Path} {c : Concept} {n : Nat}
    (qualify : ∀ y : b.Path, holdsOriented (b.toUnraveledInterpretation p) r x y →
      holds (b.toUnraveledInterpretation p) y c → c ∈ b.labels y.tailNode)
    (h : AtLeast n (fun y : b.Path =>
      holdsOriented (b.toUnraveledInterpretation p) r x y ∧ holds (b.toUnraveledInterpretation p) y c)) :
    AtLeast n (fun y => b.Edge r x.tailNode y ∧ c ∈ b.labels y) := by
  apply transfer_atLeast (R := Neighbor x) _ (fun _ _ _ => neighbor_injective hs.blocking) h
  rintro y ⟨he,hc⟩
  obtain ⟨v,hv,hedge⟩ := (simple_role_localizes hi hs hr hSimple x y).mp he
  exact ⟨v,hv,hedge,(neighbor_labels hs.blocking hv c).mpr (qualify y he hc)⟩


private theorem maximum_holds {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    (hSimple : Simple p.rules p.chains r) {x : b.Path} {c : Concept} {n : Nat}
    (neg : ∀ y : b.Path, c.dual ∈ b.labels y.tailNode →
      ¬ holds (b.toUnraveledInterpretation p) y c)
    (hl : .max n r c ∈ b.labels x.tailNode) :
    holds (b.toUnraveledInterpretation p) x (.max n r c) := by
  have hx := x.tail_unblocked hs.blocking
  intro h
  apply hs.maxBound _ hx n r c hl
  apply reflect_upper_count hi hs hr hSimple _ h
  intro y he hy
  obtain ⟨v,hv,hvEdge⟩ := (simple_role_localizes hi hs hr hSimple x y).mp he
  rcases hs.maxQual _ hx n r c hl v hvEdge with hc | hd
  · exact (neighbor_labels hs.blocking hv c).mp hc
  · exact (neg y ((neighbor_labels hs.blocking hv c.dual).mp hd) hy).elim

private theorem minimum_holds {rank : Rank} {p : Problem}
    (hs : b.BlockedSaturated rank p) {r : OrientedRole} (hr : isCoreObjPropIRI r.1 = true)
    {x : b.Path} {c : Concept} {n : Nat}
    (pos : ∀ y : b.Path, c ∈ b.labels y.tailNode → holds (b.toUnraveledInterpretation p) y c)
    (hl : .min n r c ∈ b.labels x.tailNode) :
    holds (b.toUnraveledInterpretation p) x (.min n r c) := by
  obtain ⟨ys,hlen,hnd,hq⟩ := lift_lower_bound hs hr (x := x)
    (hs.min _ (x.tail_unblocked hs.blocking) n r c hl)
  exact ⟨ys,hlen,hnd,fun y hy => ⟨(hq y hy).1,pos y (hq y hy).2⟩⟩

/-- Simultaneous positive and dual truth for every object-only concept in the
fragment. The counted roles of the concept must be simple for this problem. -/
theorem sriq_unraveled_holds_pair {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (cf : b.BlockedClashFree p) (hs : b.BlockedSaturated rank p)
    {c : Concept} (hc : c.isSRIQ = true) (counted : ∀ r ∈ c.countedRoles, Simple p.rules p.chains r) :
    (∀ x : b.Path, c ∈ b.labels x.tailNode → holds (b.toUnraveledInterpretation p) x c) ∧
    (∀ x : b.Path, c.dual ∈ b.labels x.tailNode → ¬ holds (b.toUnraveledInterpretation p) x c) := by
  have hu (x : b.Path) := x.tail_unblocked hs.blocking
  induction c with
  | top => exact ⟨fun _ _ => trivial,fun x hl _ => cf.bottom x.tailNode hl⟩
  | bottom => exact ⟨fun x hl => cf.bottom x.tailNode hl,fun _ _ h => h⟩
  | lit a sign =>
    obtain ⟨hn₁,hn₂⟩ := ordinaryClass hc
    cases sign with
    | false =>
      refine ⟨fun x hl hp => ?_,fun x hl hn => hn ?_⟩
      · exact cf.literal _ a (by simpa [toUnraveledInterpretation,hn₁,hn₂] using hp) hl
      · simpa [Concept.dual,toUnraveledInterpretation,hn₁,hn₂] using hl
    | true =>
      refine ⟨fun x hl => ?_,fun x hl hp => ?_⟩
      · simpa [holds,toUnraveledInterpretation,hn₁,hn₂] using hl
      · exact cf.literal _ a (by simpa [holds,toUnraveledInterpretation,hn₁,hn₂] using hp) hl
  | self r sign =>
    have hr : isCoreObjPropIRI r.1 = true := hc
    have hsim := counted r (by simp [Concept.countedRoles])
    have eq (x : b.Path) := (simple_role_localizes hi hs hr hsim x x).trans (base_loop_iff r x)
    cases sign with
    | false => exact ⟨fun x hl he => cf.selfNeg _ r hl ((eq x).mp he),
        fun x hl hn => hn ((eq x).mpr (hs.selfPos _ (hu x) r hl))⟩
    | true => exact ⟨fun x hl => (eq x).mpr (hs.selfPos _ (hu x) r hl),
        fun x hl he => cf.selfNeg _ r hl ((eq x).mp he)⟩
  | conj a c ia ic =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have ⟨pa,na⟩ := ia hc.1 (fun r hr => counted r (List.mem_append_left _ hr))
    have ⟨pc,nc⟩ := ic hc.2 (fun r hr => counted r (List.mem_append_right _ hr))
    refine ⟨fun x hl => ?_,fun x hl ⟨ha,hc⟩ => ?_⟩
    · obtain ⟨ha,hc⟩ := hs.conj _ (hu x) a c hl
      exact ⟨pa x ha,pc x hc⟩
    · exact (hs.disj _ (hu x) a.dual c.dual hl).elim (fun h => na x h ha) (fun h => nc x h hc)
  | disj a c ia ic =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have ⟨pa,na⟩ := ia hc.1 (fun r hr => counted r (List.mem_append_left _ hr))
    have ⟨pc,nc⟩ := ic hc.2 (fun r hr => counted r (List.mem_append_right _ hr))
    refine ⟨fun x hl => ?_,fun x hl hv => ?_⟩
    · exact (hs.disj _ (hu x) a c hl).imp (pa x) (pc x)
    · obtain ⟨ha,hc⟩ := hs.conj _ (hu x) a.dual c.dual hl
      exact hv.elim (na x ha) (nc x hc)
  | some r c ih =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have ⟨pc,nc⟩ := ih hc.2 counted
    refine ⟨fun x hl => ?_,fun x hl ⟨y,he,hy⟩ => ?_⟩
    · obtain ⟨v,hv,hfill⟩ := hs.some _ (hu x) r c hl
      obtain ⟨y,_,he,hy⟩ := lift_witness hs hc.1 (x := x) hv hfill
      exact ⟨y,he,pc y hy⟩
    · exact nc y (universal_label hi hs hc.1 hl he) hy
  | all r c ih =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have ⟨pc,nc⟩ := ih hc.2 counted
    refine ⟨fun x hl y he => pc y (universal_label hi hs hc.1 hl he),fun x hl ha => ?_⟩
    obtain ⟨v,hv,hd⟩ := hs.some _ (hu x) r c.dual hl
    obtain ⟨y,_,he,hy⟩ := lift_witness hs hc.1 (x := x) hv hd
    exact nc y hy (ha y he)
  | min n r c ih =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have hsim := counted r (List.mem_cons_self ..)
    have ⟨pc,nc⟩ := ih hc.2 (fun s hm => counted s (List.mem_cons_of_mem _ hm))
    refine ⟨fun x hl => minimum_holds hs hc.1 pc hl,fun x hl => ?_⟩
    cases n with
    | zero =>
      exact (cf.bottom _ (hs.conj _ (hu x) .bottom (.min 0 r c) hl).1).elim
    | succ m => exact maximum_holds hi hs hc.1 hsim nc hl
  | max n r c ih =>
    simp only [Concept.isSRIQ, Bool.and_eq_true] at hc
    have hsim := counted r (List.mem_cons_self ..)
    have ⟨pc,nc⟩ := ih hc.2 (fun s hm => counted s (List.mem_cons_of_mem _ hm))
    refine ⟨fun x hl => maximum_holds hi hs hc.1 hsim nc hl,fun x hl hn => ?_⟩
    exact hn (minimum_holds hs hc.1 pc hl)
  | nom | dataSome | dataAll | dataValue | dataMin | dataMax => contradiction

private theorem simple_for {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    {r : OrientedRole} (hr : r ∈ p.simpleRoles) : Simple p.rules p.chains r :=
  Problem.checkSimple_iff.mp hi.simple r hr

private theorem tbox_counted {p : Problem} {q : Inclusion} (hq : q ∈ p.tbox)
    {r : OrientedRole} (hr : r ∈ q.sub.countedRoles ∨ r ∈ q.sup.countedRoles) :
    r ∈ p.simpleRoles := by
  have hm : r ∈ p.tbox.flatMap (fun a => a.sub.countedRoles ++ a.sup.countedRoles) :=
    List.mem_flatMap.mpr ⟨q,hq,List.mem_append.mpr hr⟩
  simp [Problem.simpleRoles,hm]

private theorem chain_path {p : Problem} {body : List OrientedRole}
    (ho : ∀ r ∈ body, isCoreObjPropIRI r.1 = true) (x y : b.Path) :
    objPath (b.toUnraveledInterpretation p) body x y ↔
      Sabrina.RoleChains.TransitivePaths.WordPath (complete b.baseInterpretation p.rules p.chains) body x y := by
  induction body generalizing x with
  | nil => rfl
  | cons r rs ih =>
    have h := unraveled_role_iff (b := b) p r (ho r (List.mem_cons_self ..))
    constructor <;> rintro ⟨z,he,ht⟩
    · exact ⟨z,(h x z).mp he,(ih (fun s hs => ho s (List.mem_cons_of_mem _ hs)) z).mp ht⟩
    · exact ⟨z,(h x z).mpr he,(ih (fun s hs => ho s (List.mem_cons_of_mem _ hs)) z).mpr ht⟩

theorem sriq_unraveled_models {rank : Rank} {p : Problem} (hi : p.SRIQInput rank)
    (cf : b.BlockedClashFree p) (hs : b.BlockedSaturated rank p) :
    p.Models (b.toUnraveledInterpretation p) := by
  constructor
  case tbox =>
    intro q hq x hsub
    obtain ⟨hsubSyn,hsupSyn⟩ := hi.tbox q hq
    rcases hs.tbox q hq x.tailNode (x.tail_unblocked hs.blocking) with hd | hp
    · exact ((sriq_unraveled_holds_pair hi cf hs hsubSyn
        (fun _ hr => simple_for hi (tbox_counted hq (.inl hr)))).2 x hd hsub).elim
    · exact (sriq_unraveled_holds_pair hi cf hs hsupSyn
        (fun _ hr => simple_for hi (tbox_counted hq (.inr hr)))).1 x hp
  case rules =>
    intro q hq x y hxy
    obtain ⟨hr,hs⟩ := hi.rules q hq
    apply (unraveled_role_iff p q.2 hs x y).mpr
    exact Sabrina.RoleChains.RankedPaths.complete_roles b.baseInterpretation p.rules p.chains q.1 q.2 hq x y
      ((unraveled_role_iff p q.1 hr x y).mp hxy)
  case chains =>
    intro c hc x y hxy
    obtain ⟨hr,hbody⟩ := hi.chains c hc
    apply (unraveled_role_iff p (c.head,false) hr x y).mpr
    exact Sabrina.RoleChains.RankedPaths.complete_chains b.baseInterpretation p.rules p.chains c hc x y
      ((chain_path (fun r hr => hbody r.1 (List.mem_map_of_mem hr)) x y).mp hxy)
  case reflexive =>
    intro r hr x
    exact extension hs (r := (r,false)) (hi.reflexive r hr)
      ((base_loop_iff (r,false) x).mpr (hs.reflexive r hr _))
  case irreflexive =>
    intro r hr x he
    have hsim : Simple p.rules p.chains (r,false) := simple_for hi (by simp [Problem.simpleRoles,hr])
    have hbase := (simple_role_localizes hi hs (hi.irreflexive r hr) hsim x x).mp he
    exact cf.irreflexive r hr _ ((base_loop_iff (r,false) x).mp hbase)
  case asymmetric =>
    intro r hr x y hxy hyx
    have hsim : Simple p.rules p.chains (r,false) := simple_for hi (by simp [Problem.simpleRoles,hr])
    have h := simple_role_localizes hi hs (hi.asymmetric r hr) hsim
    obtain ⟨n,hn,he⟩ := (h x y).mp hxy
    obtain ⟨m,hm,hrv⟩ := base_flip hs.blocking (r := (r,false)) ((h y x).mp hyx)
    obtain rfl := neighbor_functional hn hm
    exact cf.asymmetric r hr _ _ he ((b.edge_converse (r,false) n x.tailNode).mp hrv)
  case disjoint =>
    intro q hq x y ⟨he,he'⟩
    obtain ⟨h₁,h₂⟩ := hi.disjoint q hq
    have mem (r : OrientedRole) (hr : r ∈ [q.1,q.2]) : r ∈ p.simpleRoles := by
      have hm : r ∈ p.chars.disjoint.flatMap (fun (s,t) => [s,t]) :=
        List.mem_flatMap.mpr ⟨q,hq,hr⟩
      simp [Problem.simpleRoles,hm]
    obtain ⟨n,hn,hx⟩ := (simple_role_localizes hi hs h₁ (simple_for hi (mem q.1 (by simp))) x y).mp he
    obtain ⟨m,hm,hy⟩ := (simple_role_localizes hi hs h₂ (simple_for hi (mem q.2 (by simp))) x y).mp he'
    obtain rfl := neighbor_functional hn hm
    exact cf.disjoint q hq _ _ ⟨hx,hy⟩
  all_goals simp [hi.subData,hi.disjointData,hi.funcData,hi.dataRanges,hi.keys,
    hi.classAssertions,hi.objAssertions,hi.negObjAssertions,hi.sameInds,hi.diffInds,
    hi.dataAssertions,hi.negDataAssertions]

end BlockedBranch

theorem sriq_blocked_saturated_sat {rank : Rank} {p : Problem} {b : BlockedBranch}
    (hsriq : p.isSRIQ rank = true) (hcf : b.BlockedClashFree p)
    (hsat : b.BlockedSaturated rank p) : p.Sat := by
  have hi := p.sriqInput hsriq
  refine ⟨b.toUnraveledInterpretation p,b.sriq_unraveled_models hi hcf hsat,BlockedBranch.Path.root b,?_⟩
  apply (b.sriq_unraveled_holds_pair hi hcf hsat hi.root
    (fun _ hr => BlockedBranch.simple_for hi (by simp [Problem.simpleRoles,hr]))).1
  exact hsat.root

#print axioms BlockedBranch.neighbor_injective
#print axioms BlockedBranch.simple_role_localizes
#print axioms BlockedBranch.lift_lower_bound
#print axioms BlockedBranch.reflect_upper_count
#print axioms BlockedBranch.universal_label
#print axioms BlockedBranch.sriq_unraveled_holds_pair
#print axioms sriq_blocked_saturated_sat


section InfiniteChain

open BlockedBranch

private def successorName : IRI := "urn:sabrina:termination:successor"
private def fwd : OrientedRole := (successorName,false)
private def bwd : OrientedRole := (successorName,true)
private def nextLabel : Concept := .some fwd .top
private def onePrev : Concept := .max 1 bwd .top
private def noPrev : Concept := .max 0 bwd .top

/-- Move the single named assertion of the litmus test into the designated
root. This leaves the TBox unchanged and uses the empty-ABox fragment. -/
def infiniteChainRooted : Problem :=
  { infiniteChain with root := noPrev, classAssertions := [] }

def infiniteChainBlocked : BlockedBranch where
  size := 3
  parent x := ⟨x.val - 1, by have := x.isLt; omega⟩
  parent_lt := by
    intro x h
    have hpos : x.val ≠ 0 := fun e => h (Fin.ext e)
    change x.val - 1 < x.val
    omega
  labels x := [.top,nextLabel,onePrev] ++ if x = 0 then [noPrev] else []
  guardLabels _ := []
  down _ := [successorName]
  up _ := []
  loops _ := []
  unequal := []
  unequal_siblings := by simp
  blockedBy x := if x = 3 then some 2 else none

private abbrev ChainNode := infiniteChainBlocked.Node

private theorem chain_labels (x : ChainNode) (c : Concept) :
    c ∈ infiniteChainBlocked.labels x ↔
      c = .top ∨ c = nextLabel ∨ c = onePrev ∨ (x = 0 ∧ c = noPrev) := by
  change c ∈ ([.top,nextLabel,onePrev] ++ if x = 0 then [noPrev] else []) ↔ _
  by_cases h : x = 0 <;> simp [h]

private theorem chain_forward (x y : ChainNode) :
    infiniteChainBlocked.Edge fwd x y ↔ infiniteChainBlocked.Child x y := by
  simp [BlockedBranch.Edge,BlockedBranch.Down,infiniteChainBlocked,fwd,converse]

private theorem chain_backward (x y : ChainNode) :
    infiniteChainBlocked.Edge bwd x y ↔ infiniteChainBlocked.Child y x := by
  exact (infiniteChainBlocked.edge_converse fwd y x).trans (chain_forward y x)

private theorem chain_direct {x : ChainNode} (hx : infiniteChainBlocked.DirectlyBlocked x) : x = 3 := by
  by_cases hn : x = 3
  · exact hn
  · change (if x = 3 then some (2 : ChainNode) else none).isSome = true at hx
    simp [hn] at hx

private theorem chain_not_indirect (x : ChainNode) : ¬ infiniteChainBlocked.IndirectlyBlocked x := by
  rintro ⟨a,ha,hb⟩
  have e := chain_direct hb
  have ht := ha.lt
  rw [show a.val = 3 from congrArg Fin.val e] at ht
  have hx : x.val < 4 := x.isLt
  omega

private theorem chain_child (x : ChainNode) (h : x.val < 3) :
    infiniteChainBlocked.Child x (⟨x.val+1,by change x.val + 1 < 4; omega⟩ : ChainNode) := by
  constructor
  · intro e
    have hval := congrArg Fin.val e
    change x.val + 1 = 0 at hval
    omega
  · apply Fin.ext
    change (x.val + 1) - 1 = x.val
    omega

private theorem chain_blocking : infiniteChainBlocked.BlockingValid := by
  constructor
  intro x y he
  have hx : x = 3 := chain_direct (by simp [BlockedBranch.DirectlyBlocked,he])
  subst x
  have hy : y = 2 := by
    have he' : some (2 : ChainNode) = some y := he
    exact (Option.some.inj he').symm
  subst y
  refine ⟨.parent ⟨by decide,rfl⟩,by decide,⟨rfl,chain_not_indirect _⟩,
    chain_not_indirect _,?_⟩
  constructor <;> intro _ <;> rfl

theorem infiniteChainBlocked_clashFree :
    infiniteChainBlocked.BlockedClashFree infiniteChainRooted := by
  constructor
  case bottom =>
    intro x hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case literal =>
    intro x a hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case unequal => intro x he; exact List.not_mem_nil he
  case selfNeg =>
    intro x r hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  all_goals simp [infiniteChainRooted,infiniteChain,infiniteChainBlocked]

theorem infiniteChainBlocked_saturated :
    infiniteChainBlocked.BlockedSaturated (fun _ => 0) infiniteChainRooted := by
  constructor
  case blocking => exact chain_blocking
  case root => simp [infiniteChainRooted,chain_labels]
  case conj =>
    intro x _ a c hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case disj =>
    intro x _ a c hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case some =>
    intro x hx r c hc
    have hc' : r = fwd ∧ c = .top := by
      simp [chain_labels,nextLabel,onePrev,noPrev] at hc
      exact hc
    rcases hc' with ⟨rfl,rfl⟩
    have hn : x ≠ 3 := by
      intro e
      have he := hx.1
      rw [e] at he
      contradiction
    have ht : x.val < 3 := by
      have hb : x.val < 4 := x.isLt
      by_cases hw : x.val < 3
      · exact hw
      · exact (hn (Fin.ext (by change x.val = 3; omega))).elim
    exact ⟨⟨x.val+1,by change x.val + 1 < 4; omega⟩,(chain_forward _ _).mpr (chain_child x ht),by simp [chain_labels]⟩
  case min =>
    intro x _ n r c hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case maxQual =>
    intro x _ n r c hl y _
    have hc : c = .top := by
      simp [chain_labels,nextLabel,onePrev,noPrev] at hl
      grind
    subst c
    exact .inl (by simp [chain_labels])
  case maxBound =>
    intro x _ n r c hl
    have hc : (n = 1 ∧ r = bwd ∧ c = .top) ∨
        (x = 0 ∧ n = 0 ∧ r = bwd ∧ c = .top) := by
      simpa [chain_labels,nextLabel,onePrev,noPrev,and_assoc] using hl
    rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
    · apply (atMostOne_iff _).mpr
      intro y z hy hz
      exact ((chain_backward _ _).mp hy.1).2.symm.trans ((chain_backward _ _).mp hz.1).2
    · rintro ⟨ys,hlen,_,hall⟩
      cases ys with
      | nil => simp at hlen
      | cons y tail => exact ((chain_backward _ _).mp (hall y (List.mem_cons_self ..)).1).1 rfl
  case selfPos =>
    intro x _ r hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  case tbox =>
    intro q hq x _
    have hq' : q = ⟨.top,nextLabel⟩ ∨ q = ⟨.top,onePrev⟩ := by
      change q ∈ ([⟨.top,nextLabel⟩,⟨.top,onePrev⟩] : List Inclusion) at hq
      simpa using hq
    rcases hq' with rfl | rfl <;> exact .inr (by simp [chain_labels])
  case guardStart =>
    intro x _ r c hc
    simp [chain_labels,nextLabel,onePrev,noPrev] at hc
  all_goals simp [infiniteChainRooted,infiniteChain,infiniteChainBlocked]

theorem infiniteChain_sat_via_unraveling : infiniteChain.Sat := by
  have hsyn : infiniteChainRooted.isSRIQ (fun _ => 0) = true := by decide
  obtain ⟨i,hm,x,hx⟩ := sriq_blocked_saturated_sat hsyn
    infiniteChainBlocked_clashFree infiniteChainBlocked_saturated
  let j : Interpretation datatypeMap := { i with
    individuals := fun _ => x
    named := fun y => y = x
    namedIndividual := fun _ => rfl }
  refine ⟨j,?_,x,trivial⟩
  constructor
  case tbox =>
    intro q hq y hy
    have hq' : q = ⟨.top,nextLabel⟩ ∨ q = ⟨.top,onePrev⟩ := by
      change q ∈ ([⟨.top,nextLabel⟩,⟨.top,onePrev⟩] : List Inclusion) at hq
      simpa using hq
    rcases hq' with rfl | rfl <;> exact hm.tbox _ hq y hy
  case classAssertions =>
    intro ac ha
    have he : ac = (.named "urn:sabrina:termination:start",noPrev) := by
      change ac ∈ [(.named "urn:sabrina:termination:start",noPrev)] at ha
      exact List.mem_singleton.mp ha
    subst ac
    exact hx
  all_goals simp [infiniteChain]

private def chainEntries : Nat → List ChainNode
  | 0 => [2,1]
  | n+1 => 3 :: chainEntries n

private theorem chain_tail (n : Nat) : infiniteChainBlocked.walkTail (chainEntries n) = 2 := by
  cases n <;> rfl

private theorem chain_walk (n : Nat) : infiniteChainBlocked.Walk (chainEntries n) := by
  induction n with
  | zero =>
    exact .step (.step .root ⟨by decide,rfl⟩) ⟨by decide,rfl⟩
  | succ n ih =>
    apply Walk.step ih
    exact ⟨by decide,(chain_tail n).symm⟩

/-- Iterating the recorded entry `3` yields arbitrarily long paths while the
tail always continues at node `2`. -/
def infiniteChainPath (n : Nat) : infiniteChainBlocked.Path := ⟨chainEntries n,chain_walk n⟩

theorem infiniteChainPath_injective {m n : Nat} (h : infiniteChainPath m = infiniteChainPath n) :
    m = n := by
  have len (k : Nat) : (chainEntries k).length = k + 2 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [chainEntries,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have hl := congrArg (fun x : infiniteChainBlocked.Path => x.val.length) h
  change (chainEntries m).length = (chainEntries n).length at hl
  rw [len,len] at hl
  omega

end InfiniteChain

#print axioms infiniteChain_sat_via_unraveling
#print axioms infiniteChainPath_injective

end Sabrina.OWL2.SROIQD.Termination
