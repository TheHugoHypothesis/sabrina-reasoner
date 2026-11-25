import Sabrina.ALC.Types
import Sabrina.ALCH.Hierarchy

namespace Sabrina.ALC

/-- The Boolean selects the converse of the named relation. -/
abbrev OrientedRole := String × Bool
abbrev RoleTheory := ALCH.HierarchyOf OrientedRole

def converse (r : OrientedRole) : OrientedRole := (r.1, !r.2)

def holdsRole (i : Interpretation) (r : OrientedRole) (x y : i.Domain) : Prop :=
  if r.2 then i.role r.1 y x else i.role r.1 x y

def modelsRoles (i : Interpretation) (rules : RoleTheory) : Prop :=
  ∀ r s, (r, s) ∈ rules → ∀ x y, holdsRole i r x y → holdsRole i s x y

def mirrored (rules : RoleTheory) : RoleTheory :=
  rules ++ rules.map (fun (r, s) => (converse r, converse s))

def roleClosure (rules : RoleTheory) : RoleTheory := ALCH.close (mirrored rules)

private theorem holdsRole_converse (i : Interpretation) (r : OrientedRole) (x y : i.Domain) :
    holdsRole i (converse r) y x ↔ holdsRole i r x y := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

theorem modelsMirrored {i : Interpretation} {rules : RoleTheory}
    (hm : modelsRoles i rules) : modelsRoles i (mirrored rules) := by
  intro r s h x y hr
  rcases List.mem_append.mp h with h | h
  · exact hm r s h x y hr
  · obtain ⟨⟨a,b⟩, hmab, he⟩ := List.mem_map.mp h
    cases he
    exact (holdsRole_converse i b y x).mpr
      (hm a b hmab y x ((holdsRole_converse i a y x).mp hr))

theorem modelsClosure {i : Interpretation} {rules : RoleTheory}
    (hm : modelsRoles i rules) : modelsRoles i (roleClosure rules) := by
  intro r s h x y
  exact ALCH.close_sound (R := fun a b => holdsRole i a x y → holdsRole i b x y)
    (fun {a b} hab => modelsMirrored hm a b hab x y) (fun h₁ h₂ h₃ => h₂ (h₁ h₃)) h

private def superroles (closed : RoleTheory) (r : OrientedRole) : List OrientedRole :=
  r :: ((closed.filter fun e => e.1 == r).map Prod.snd)

private theorem mem_superroles {closed : RoleTheory} {r s : OrientedRole} :
    s ∈ superroles closed r ↔ s = r ∨ (r,s) ∈ closed := by
  simp only [superroles, List.mem_cons, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro (h | ⟨⟨a,b⟩, ⟨hm, ha⟩, hb⟩)
    · exact Or.inl h
    · change a = r at ha
      change b = s at hb
      subst a; subst b
      exact Or.inr hm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨(r,s), ⟨h,rfl⟩, rfl⟩

private theorem superroles_mono {rules : RoleTheory} {r s : OrientedRole}
    (h : (r,s) ∈ mirrored rules) : superroles (roleClosure rules) s ⊆ superroles (roleClosure rules) r := by
  intro t ht
  apply mem_superroles.mpr
  apply Or.inr
  rcases mem_superroles.mp ht with rfl | ht
  · exact ALCH.mem_close h
  · exact ALCH.close_prepend h ht

private def permits (cs : List Concept) (r : OrientedRole) (src dst : Row) : Bool :=
  if r.2 then admitsEdge cs r.1 dst src else admitsEdge cs r.1 src dst

def allowsRole (cs : List Concept) (closed : RoleTheory)
    (r : OrientedRole) (src dst : Row) : Bool :=
  (superroles closed r).all (fun s => permits cs s src dst) &&
  (superroles closed (converse r)).all (fun s => permits cs s dst src)

theorem allowsRole_converse (cs : List Concept) (closed : RoleTheory)
    (r : OrientedRole) (x y : Row) :
    allowsRole cs closed (converse r) y x = allowsRole cs closed r x y := by
  have hh : converse (converse r) = r := by
    rcases r with ⟨r, _ | _⟩ <;> rfl
  simp only [allowsRole, hh, Bool.and_comm]

theorem allowsRole_admits {cs : List Concept} {closed : RoleTheory} {r : String} {x y : Row}
    (h : allowsRole cs closed (r,false) x y = true) : admitsEdge cs r x y = true := by
  simp only [allowsRole, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 _ (mem_superroles.mpr (Or.inl rfl))

theorem allowsRole_step {cs : List Concept} {rules : RoleTheory} {r s : OrientedRole} {x y : Row}
    (hrs : (r,s) ∈ rules)
    (h : allowsRole cs (roleClosure rules) r x y = true) :
    allowsRole cs (roleClosure rules) s x y = true := by
  simp only [allowsRole, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun t ht => h.1 t (superroles_mono (List.mem_append_left _ hrs) ht),
    fun t ht => h.2 t (superroles_mono
      (List.mem_append_right _ (List.mem_map.mpr ⟨(r,s), hrs, rfl⟩)) ht)⟩

theorem allowsRole_of_model {cs : List Concept} {i : Interpretation} {rules : RoleTheory}
    (hm : modelsRoles i rules) (row : i.Domain → Row)
    (hrow : ∀ r x y, i.role r x y → admitsEdge cs r (row x) (row y) = true)
    {r : OrientedRole} {x y : i.Domain} (he : holdsRole i r x y) :
    allowsRole cs (roleClosure rules) r (row x) (row y) = true := by
  have hperm : ∀ s u v, holdsRole i s u v → permits cs s (row u) (row v) = true := by
    rintro ⟨s, _ | _⟩ u v h <;> exact hrow _ _ _ h
  have hup : ∀ a u v, holdsRole i a u v → ∀ s ∈ superroles (roleClosure rules) a,
      permits cs s (row u) (row v) = true := by
    intro a u v ha s hs
    apply hperm
    rcases mem_superroles.mp hs with rfl | hs
    · exact ha
    · exact modelsClosure hm a s hs u v ha
  simp only [allowsRole, Bool.and_eq_true, List.all_eq_true]
  exact ⟨hup r x y he, hup (converse r) y x ((holdsRole_converse i r x y).mpr he)⟩

def admitsUnder (cs : List Concept) (rules : RoleTheory) : String → Row → Row → Bool :=
  let closed := roleClosure rules
  fun r => allowsRole cs closed (r,false)

def ConceptSatUnder (rules : RoleTheory) (tbox : TBox) (c : Concept) : Prop :=
  ∃ i : Interpretation, modelsRoles i rules ∧ models i tbox ∧ ∃ x, holds i x c

def FiniteConceptSatUnder (rules : RoleTheory) (tbox : TBox) (c : Concept) : Prop :=
  ∃ i : Interpretation, modelsRoles i rules ∧ models i tbox ∧
    (∃ carrier : List i.Domain, ∀ x, x ∈ carrier) ∧ ∃ x, holds i x c

end Sabrina.ALC
