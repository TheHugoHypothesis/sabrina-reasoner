import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.DirectSemantics

/-! # H.1: Integer-Interned Horn-$\mathcal{SHIQ}$ Extractor and Normalizer

Extracts the maximal Horn-$\mathcal{SHIQ}$ lower-bound axiom set from any OWL 2 DL
ontology into integer-interned Kazakov normal form, with:

- `ClassId := Nat`, mapped directly to `ClassExpr` via `CBTable.classes`
  (`0 = owl:Thing`, `1 = owl:Nothing`), eliminating fresh-IRI hygiene and
  interpretation extension in soundness proofs.
- `RoleId := Nat`, stored in converse pairs (`2 * k` = path `ps`,
  `2 * k + 1` = `conversePath ps`), making role converse an $O(1)$ parity toggle
  (`invRole`).
- `isPureHornSHIQ : Bool` tracking whether every axiom in the input ontology
  was faithfully captured (enabling future zero-tableau complete classification
  on pure Horn-$\mathcal{SHIQ}$ TBoxes).
- Kernel-verified soundness theorem `extractHornSHIQ_sound`: every extracted
  `HornAxiom` holds in every OWL 2 Direct Semantics model of the input ontology.

Zero `sorry`, zero `admit`, strictly standard Lean 4 core axioms
(`[propext, Classical.choice, Quot.sound]`). -/

namespace Sabrina.OWL2.FastCB

open Sabrina.OWL2

/-! ### 0. Local `Hashable` Instances for Syntax Interning -/

private def hashIndividual : Individual → UInt64
  | .named s => mixHash 1 (hash s)
  | .anonymous d l => mixHash 2 (mixHash (hash d) (hash l))

private local instance : Hashable Individual := ⟨hashIndividual⟩

private def hashObjectProperty : ObjectProperty → UInt64
  | .named s => mixHash 3 (hash s)
  | .inverse s => mixHash 4 (hash s)

private local instance : Hashable ObjectProperty := ⟨hashObjectProperty⟩

private def hashLiteral (l : Literal) : UInt64 :=
  mixHash (hash l.lexical) (hash l.datatype)

private local instance : Hashable Literal := ⟨hashLiteral⟩

private def hashFacet (f : Facet) : UInt64 :=
  mixHash (hash f.name) (hashLiteral f.bound)

private local instance : Hashable Facet := ⟨hashFacet⟩

private def hashDataRange : DataRange → UInt64
  | .datatype s => mixHash 10 (hash s)
  | .complement r => mixHash 11 (hashDataRange r)
  | .intersection a b => mixHash 12 (mixHash (hashDataRange a) (hashDataRange b))
  | .union a b => mixHash 13 (mixHash (hashDataRange a) (hashDataRange b))
  | .oneOf ls => mixHash 14 (hash ls)
  | .restriction s fs => mixHash 15 (mixHash (hash s) (hash fs))

private local instance : Hashable DataRange := ⟨hashDataRange⟩

private def hashClassExpr : ClassExpr → UInt64
  | .named s => mixHash 20 (hash s)
  | .complement c => mixHash 21 (hashClassExpr c)
  | .intersection a b => mixHash 22 (mixHash (hashClassExpr a) (hashClassExpr b))
  | .union a b => mixHash 23 (mixHash (hashClassExpr a) (hashClassExpr b))
  | .oneOf is => mixHash 24 (hash is)
  | .objectSome r c => mixHash 25 (mixHash (hashObjectProperty r) (hashClassExpr c))
  | .objectAll r c => mixHash 26 (mixHash (hashObjectProperty r) (hashClassExpr c))
  | .objectValue r a => mixHash 27 (mixHash (hashObjectProperty r) (hashIndividual a))
  | .objectSelf r => mixHash 28 (hashObjectProperty r)
  | .objectMin n r c => mixHash 29 (mixHash (hash n) (mixHash (hashObjectProperty r) (hashClassExpr c)))
  | .objectMax n r c => mixHash 30 (mixHash (hash n) (mixHash (hashObjectProperty r) (hashClassExpr c)))
  | .objectExact n r c => mixHash 31 (mixHash (hash n) (mixHash (hashObjectProperty r) (hashClassExpr c)))
  | .dataSome r d => mixHash 32 (mixHash (hash r) (hashDataRange d))
  | .dataAll r d => mixHash 33 (mixHash (hash r) (hashDataRange d))
  | .dataValue r l => mixHash 34 (mixHash (hash r) (hashLiteral l))
  | .dataMin n r d => mixHash 35 (mixHash (hash n) (mixHash (hash r) (hashDataRange d)))
  | .dataMax n r d => mixHash 36 (mixHash (hash n) (mixHash (hash r) (hashDataRange d)))
  | .dataExact n r d => mixHash 37 (mixHash (hash n) (mixHash (hash r) (hashDataRange d)))

private local instance : Hashable ClassExpr := ⟨hashClassExpr⟩

/-! ### 1. Role Paths & Converse Pairs -/

/-- Reverse a role path and flip each step to its converse. -/
def conversePath (ps : List ObjectProperty) : List ObjectProperty :=
  (ps.map ObjectProperty.converse).reverse

theorem rolePath_append {dm : DatatypeMap} (i : Interpretation dm)
    (p1 p2 : List ObjectProperty) (x z : i.Object) :
    rolePath i (p1 ++ p2) x z ↔ ∃ y, rolePath i p1 x y ∧ rolePath i p2 y z := by
  induction p1 generalizing x with
  | nil =>
    simp only [List.nil_append, rolePath]
    exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩
  | cons r rs ih =>
    simp only [List.cons_append, rolePath, ih]
    constructor
    · rintro ⟨w, hr, y, hrs, hp2⟩
      exact ⟨y, ⟨w, hr, hrs⟩, hp2⟩
    · rintro ⟨y, ⟨w, hr, hrs⟩, hp2⟩
      exact ⟨w, hr, y, hrs, hp2⟩

theorem rolePath_singleton {dm : DatatypeMap} (i : Interpretation dm)
    (r : ObjectProperty) (x y : i.Object) :
    rolePath i [r] x y ↔ objectHolds i r x y := by
  simp only [rolePath]
  exact ⟨fun ⟨_, hr, h⟩ => h ▸ hr, fun hr => ⟨y, hr, rfl⟩⟩

theorem rolePath_conversePath {dm : DatatypeMap} (i : Interpretation dm)
    (ps : List ObjectProperty) (x y : i.Object) :
    rolePath i (conversePath ps) x y ↔ rolePath i ps y x := by
  induction ps generalizing x y with
  | nil =>
    simp only [conversePath, List.map_nil, List.reverse_nil, rolePath, eq_comm]
  | cons r rs ih =>
    simp only [conversePath, List.map_cons, List.reverse_cons, rolePath_append, rolePath]
    constructor
    · rintro ⟨w, hrev, z, hr, rfl⟩
      have h1 : rolePath i rs w x := (ih x w).mp hrev
      have h2 : objectHolds i r z w := (objectHolds_converse i r w z).mp hr
      exact ⟨w, h2, h1⟩
    · rintro ⟨w, hr, hrs⟩
      have h1 : rolePath i (conversePath rs) x w := (ih x w).mpr hrs
      have h2 : objectHolds i r.converse w y := (objectHolds_converse i r w y).mpr hr
      exact ⟨w, h1, y, h2, rfl⟩

/-- $O(1)$ parity toggle inverse role ID on converse-paired role tables (`2k ↔ 2k + 1`). -/
@[inline] def invRole (r : Nat) : Nat := if r % 2 == 0 then r + 1 else r - 1

theorem invRole_even (k : Nat) : invRole (2 * k) = 2 * k + 1 := by
  unfold invRole; simp

theorem invRole_odd (k : Nat) : invRole (2 * k + 1) = 2 * k := by
  unfold invRole; simp

theorem invRole_involutive (r : Nat) : invRole (invRole r) = r := by
  unfold invRole
  by_cases h : r % 2 = 0
  · have h1 : (r + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (r - 1) % 2 = 0 := by omega
    simp [h, h1]; omega

/-! ### 2. `CBTable` and `HornAxiom` Semantics -/

/-- Vocabulary table mapping integer class IDs to OWL 2 `ClassExpr`s and
    converse-paired integer role IDs to `List ObjectProperty` paths. -/
structure CBTable where
  classes : Array ClassExpr
  roles : Array (List ObjectProperty)
  deriving Repr, Inhabited

def CBTable.exprOf (t : CBTable) (c : Nat) : ClassExpr :=
  (t.classes[c]?).getD (.named nothing)

def CBTable.roleOf (t : CBTable) (r : Nat) : List ObjectProperty :=
  (t.roles[r]?).getD [.named bottomObjectProperty]

/-- Structural invariant of `CBTable`:
    - `0` is `owl:Thing`, `1` is `owl:Nothing`,
    - `roles` has even length with every `2k + 1` equal to `conversePath (roles[2k])`. -/
def CBTable.WF (t : CBTable) : Prop :=
  t.classes[0]? = some (.named thing) ∧
  t.classes[1]? = some (.named nothing) ∧
  t.roles.size % 2 = 0 ∧
  ∀ k, 2 * k + 1 < t.roles.size →
    t.roles[2 * k + 1]? = (t.roles[2 * k]?).map conversePath

theorem CBTable.exprOf_zero {t : CBTable} (hwf : t.WF) :
    t.exprOf 0 = .named thing := by
  simp [CBTable.exprOf, hwf.1]

theorem CBTable.exprOf_one {t : CBTable} (hwf : t.WF) :
    t.exprOf 1 = .named nothing := by
  simp [CBTable.exprOf, hwf.2.1]

theorem CBTable.roleOf_invRole {dm : DatatypeMap} {t : CBTable} (hwf : t.WF)
    (i : Interpretation dm) (r : Nat) (x y : i.Object) :
    rolePath i (t.roleOf (invRole r)) x y ↔ rolePath i (t.roleOf r) y x := by
  by_cases hpar : r % 2 = 0
  · let k := r / 2
    have hr : r = 2 * k := by omega
    rw [hr, invRole_even]
    by_cases hlt : 2 * k + 1 < t.roles.size
    · have hpair := hwf.2.2.2 k hlt
      have hlt0 : 2 * k < t.roles.size := by omega
      simp only [CBTable.roleOf, hpair, Array.getElem?_eq_getElem hlt0, Option.map_some,
        Option.getD_some]
      exact rolePath_conversePath i _ x y
    · have hge0 : t.roles.size ≤ 2 * k := by have := hwf.2.2.1; omega
      have hge1 : t.roles.size ≤ 2 * k + 1 := by omega
      simp only [CBTable.roleOf, Array.getElem?_eq_none hge0, Array.getElem?_eq_none hge1,
        Option.getD_none, rolePath_singleton, objectHolds]
      exact ⟨fun h => absurd h (i.bottomObjectExt x y),
             fun h => absurd h (i.bottomObjectExt y x)⟩
  · let k := r / 2
    have hr : r = 2 * k + 1 := by omega
    rw [hr, invRole_odd]
    by_cases hlt : 2 * k + 1 < t.roles.size
    · have hpair := hwf.2.2.2 k hlt
      have hlt0 : 2 * k < t.roles.size := by omega
      simp only [CBTable.roleOf, hpair, Array.getElem?_eq_getElem hlt0, Option.map_some,
        Option.getD_some]
      exact (rolePath_conversePath i _ y x).symm
    · have hge0 : t.roles.size ≤ 2 * k := by have := hwf.2.2.1; omega
      have hge1 : t.roles.size ≤ 2 * k + 1 := by omega
      simp only [CBTable.roleOf, Array.getElem?_eq_none hge0, Array.getElem?_eq_none hge1,
        Option.getD_none, rolePath_singleton, objectHolds]
      exact ⟨fun h => absurd h (i.bottomObjectExt x y),
             fun h => absurd h (i.bottomObjectExt y x)⟩

/-- Integer-interned Horn-$\mathcal{SHIQ}$ normal-form axiom. -/
inductive HornAxiom where
  | sub (lhs : Array Nat) (rhs : Nat)
  | existR (a r b : Nat)
  | existL (r a b : Nat)
  | allR (a r b : Nat)
  | maxOne (a r b : Nat)
  | roleSub (r s : Nat)
  | roleChain (r1 r2 s : Nat)
  | roleRefl (r : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Direct semantics of a `HornAxiom` in an arbitrary OWL 2 interpretation `i`. -/
def HornAxiom.holds {dm : DatatypeMap} (t : CBTable) (i : Interpretation dm) : HornAxiom → Prop
  | .sub lhs rhs =>
    ∀ x, (∀ c ∈ lhs.toList, classHolds i x (t.exprOf c)) → classHolds i x (t.exprOf rhs)
  | .existR a r b =>
    ∀ x, classHolds i x (t.exprOf a) →
      ∃ y, rolePath i (t.roleOf r) x y ∧ classHolds i y (t.exprOf b)
  | .existL r a b =>
    ∀ x y, rolePath i (t.roleOf r) x y → classHolds i y (t.exprOf a) →
      classHolds i x (t.exprOf b)
  | .allR a r b =>
    ∀ x, classHolds i x (t.exprOf a) →
      ∀ y, rolePath i (t.roleOf r) x y → classHolds i y (t.exprOf b)
  | .maxOne a r b =>
    ∀ x, classHolds i x (t.exprOf a) →
      ∀ y z, rolePath i (t.roleOf r) x y → classHolds i y (t.exprOf b) →
             rolePath i (t.roleOf r) x z → classHolds i z (t.exprOf b) → y = z
  | .roleSub r s =>
    ∀ x y, rolePath i (t.roleOf r) x y → rolePath i (t.roleOf s) x y
  | .roleChain r1 r2 s =>
    ∀ x y z, rolePath i (t.roleOf r1) x y → rolePath i (t.roleOf r2) y z →
      rolePath i (t.roleOf s) x z
  | .roleRefl r =>
    ∀ x, rolePath i (t.roleOf r) x x

/-- Output of Horn-$\mathcal{SHIQ}$ extraction. -/
structure NormResult where
  table : CBTable
  axioms : Array HornAxiom
  namedClassIds : Array (IRI × Nat)
  isPureHornSHIQ : Bool
  deriving Repr, Inhabited

/-! ### 3. Stateful Extractor with Append-Only Table & Self-Checking Interning -/

private structure ExtState where
  table : CBTable
  axioms : Array HornAxiom
  exprMap : Std.HashMap ClassExpr Nat
  roleMap : Std.HashMap (List ObjectProperty) Nat
  namedClassIds : Array (IRI × Nat)
  namedSeen : Std.HashSet IRI
  isPureHornSHIQ : Bool

private def ExtState.empty : ExtState :=
  let thingExpr := ClassExpr.named thing
  let nothingExpr := ClassExpr.named nothing
  let topR : List ObjectProperty := [.named topObjectProperty]
  let botR : List ObjectProperty := [.named bottomObjectProperty]
  { table := {
      classes := #[thingExpr, nothingExpr]
      roles := #[topR, conversePath topR, botR, conversePath botR]
    }
    axioms := #[]
    exprMap := ({} : Std.HashMap ClassExpr Nat).insert thingExpr 0 |>.insert nothingExpr 1
    roleMap := ({} : Std.HashMap (List ObjectProperty) Nat)
      |>.insert topR 0 |>.insert (conversePath topR) 1
      |>.insert botR 2 |>.insert (conversePath botR) 3
    namedClassIds := #[(thing, 0), (nothing, 1)]
    namedSeen := ({} : Std.HashSet IRI).insert thing |>.insert nothing
    isPureHornSHIQ := true }

/-- Monotonicity predicate: `t2` extends `t1` only by appending to `classes` and `roles`. -/
private def CBTable.Extends (t1 t2 : CBTable) : Prop :=
  t1.classes.size ≤ t2.classes.size ∧
  t1.roles.size ≤ t2.roles.size ∧
  (∀ k, k < t1.classes.size → t2.classes[k]? = t1.classes[k]?) ∧
  (∀ k, k < t1.roles.size → t2.roles[k]? = t1.roles[k]?)

private theorem CBTable.Extends.refl (t : CBTable) : t.Extends t :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

private theorem CBTable.Extends.trans {t1 t2 t3 : CBTable}
    (h12 : t1.Extends t2) (h23 : t2.Extends t3) : t1.Extends t3 :=
  ⟨Nat.le_trans h12.1 h23.1, Nat.le_trans h12.2.1 h23.2.1,
   fun k hk => by rw [h23.2.2.1 k (Nat.lt_of_lt_of_le hk h12.1), h12.2.2.1 k hk],
   fun k hk => by rw [h23.2.2.2 k (Nat.lt_of_lt_of_le hk h12.2.1), h12.2.2.2 k hk]⟩

private theorem CBTable.Extends.exprOf_eq {t1 t2 : CBTable} (hext : t1.Extends t2)
    {c : Nat} (hc : c < t1.classes.size) : t2.exprOf c = t1.exprOf c := by
  simp [CBTable.exprOf, hext.2.2.1 c hc]

private theorem CBTable.Extends.roleOf_eq {t1 t2 : CBTable} (hext : t1.Extends t2)
    {r : Nat} (hr : r < t1.roles.size) : t2.roleOf r = t1.roleOf r := by
  simp [CBTable.roleOf, hext.2.2.2 r hr]

/-- Bounds invariant for a `HornAxiom` so its semantics is preserved under table extension. -/
def HornAxiom.inBounds (t : CBTable) : HornAxiom → Prop
  | .sub lhs rhs => (∀ c ∈ lhs.toList, c < t.classes.size) ∧ rhs < t.classes.size
  | .existR a r b => a < t.classes.size ∧ r < t.roles.size ∧ b < t.classes.size
  | .existL r a b => r < t.roles.size ∧ a < t.classes.size ∧ b < t.classes.size
  | .allR a r b => a < t.classes.size ∧ r < t.roles.size ∧ b < t.classes.size
  | .maxOne a r b => a < t.classes.size ∧ r < t.roles.size ∧ b < t.classes.size
  | .roleSub r s => r < t.roles.size ∧ s < t.roles.size
  | .roleChain r1 r2 s => r1 < t.roles.size ∧ r2 < t.roles.size ∧ s < t.roles.size
  | .roleRefl r => r < t.roles.size

private theorem HornAxiom.inBounds_mono {t1 t2 : CBTable} (hext : t1.Extends t2)
    {ax : HornAxiom} (hb : ax.inBounds t1) : ax.inBounds t2 := by
  cases ax with
  | sub lhs rhs =>
    exact ⟨fun c hc => Nat.lt_of_lt_of_le (hb.1 c hc) hext.1, Nat.lt_of_lt_of_le hb.2 hext.1⟩
  | existR a r b =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.1, Nat.lt_of_lt_of_le hb.2.1 hext.2.1,
           Nat.lt_of_lt_of_le hb.2.2 hext.1⟩
  | existL r a b =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.2.1, Nat.lt_of_lt_of_le hb.2.1 hext.1,
           Nat.lt_of_lt_of_le hb.2.2 hext.1⟩
  | allR a r b =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.1, Nat.lt_of_lt_of_le hb.2.1 hext.2.1,
           Nat.lt_of_lt_of_le hb.2.2 hext.1⟩
  | maxOne a r b =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.1, Nat.lt_of_lt_of_le hb.2.1 hext.2.1,
           Nat.lt_of_lt_of_le hb.2.2 hext.1⟩
  | roleSub r s =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.2.1, Nat.lt_of_lt_of_le hb.2 hext.2.1⟩
  | roleChain r1 r2 s =>
    exact ⟨Nat.lt_of_lt_of_le hb.1 hext.2.1, Nat.lt_of_lt_of_le hb.2.1 hext.2.1,
           Nat.lt_of_lt_of_le hb.2.2 hext.2.1⟩
  | roleRefl r =>
    exact Nat.lt_of_lt_of_le hb hext.2.1

private theorem HornAxiom.holds_mono {dm : DatatypeMap} {t1 t2 : CBTable}
    (hext : t1.Extends t2) {i : Interpretation dm} {ax : HornAxiom}
    (hb : ax.inBounds t1) (hh : ax.holds t1 i) : ax.holds t2 i := by
  cases ax with
  | sub lhs rhs =>
    intro x hpre
    rw [hext.exprOf_eq hb.2]
    exact hh x (fun c hc => by rw [← hext.exprOf_eq (hb.1 c hc)]; exact hpre c hc)
  | existR a r b =>
    intro x ha
    rw [hext.exprOf_eq hb.1] at ha
    obtain ⟨y, hry, hyb⟩ := hh x ha
    exact ⟨y, by rw [hext.roleOf_eq hb.2.1]; exact hry, by rw [hext.exprOf_eq hb.2.2]; exact hyb⟩
  | existL r a b =>
    intro x y hry hya
    rw [hext.roleOf_eq hb.1] at hry; rw [hext.exprOf_eq hb.2.1] at hya; rw [hext.exprOf_eq hb.2.2]
    exact hh x y hry hya
  | allR a r b =>
    intro x ha y hry
    rw [hext.exprOf_eq hb.1] at ha; rw [hext.roleOf_eq hb.2.1] at hry; rw [hext.exprOf_eq hb.2.2]
    exact hh x ha y hry
  | maxOne a r b =>
    intro x ha y z hry hyb hrz hzb
    rw [hext.exprOf_eq hb.1] at ha; rw [hext.roleOf_eq hb.2.1] at hry hrz
    rw [hext.exprOf_eq hb.2.2] at hyb hzb
    exact hh x ha y z hry hyb hrz hzb
  | roleSub r s =>
    intro x y hry
    rw [hext.roleOf_eq hb.1] at hry; rw [hext.roleOf_eq hb.2]
    exact hh x y hry
  | roleChain r1 r2 s =>
    intro x y z h1 h2
    rw [hext.roleOf_eq hb.1] at h1; rw [hext.roleOf_eq hb.2.1] at h2; rw [hext.roleOf_eq hb.2.2]
    exact hh x y z h1 h2
  | roleRefl r =>
    intro x
    rw [hext.roleOf_eq hb]
    exact hh x

/-- Full state soundness invariant relative to an interpretation `i`. -/
private def ExtState.Valid {dm : DatatypeMap} (i : Interpretation dm) (st : ExtState) : Prop :=
  st.table.WF ∧
  (∀ ax ∈ st.axioms.toList, ax.inBounds st.table ∧ ax.holds st.table i) ∧
  (∀ p ∈ st.namedClassIds.toList, p.2 < st.table.classes.size ∧ st.table.classes[p.2]? = some (.named p.1))

private theorem ExtState.valid_empty {dm : DatatypeMap} (i : Interpretation dm) :
    ExtState.empty.Valid i := by
  refine ⟨⟨rfl, rfl, by decide, ?_⟩, ?_, ?_⟩
  · intro k hk
    change 2 * k + 1 < 4 at hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> rfl
  · intro ax hax; simp [ExtState.empty] at hax
  · intro p hp
    simp only [ExtState.empty, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨by decide, rfl⟩

private theorem getElem?_push_lt {α : Type} (xs : Array α) (v : α) {k : Nat} (hk : k < xs.size) :
    (xs.push v)[k]? = xs[k]? := by
  rw [Array.getElem?_push_lt hk, Array.getElem?_eq_getElem hk]

private theorem getElem?_push_eq {α : Type} (xs : Array α) (v : α) :
    (xs.push v)[xs.size]? = some v := by
  rw [Array.getElem?_push_size]

private theorem pushClass_extends (t : CBTable) (e : ClassExpr) :
    t.Extends { t with classes := t.classes.push e } := by
  refine ⟨by simp, Nat.le_refl _, ?_, fun _ _ => rfl⟩
  intro k hk
  exact getElem?_push_lt t.classes e hk

private theorem wf_zero_lt {t : CBTable} (hwf : t.WF) : 0 < t.classes.size :=
  Classical.byContradiction fun h => by
    have hle : t.classes.size ≤ 0 := Nat.le_of_not_lt h
    have h0 := hwf.1
    rw [Array.getElem?_eq_none hle] at h0
    cases h0

private theorem wf_one_lt {t : CBTable} (hwf : t.WF) : 1 < t.classes.size :=
  Classical.byContradiction fun h => by
    have hle : t.classes.size ≤ 1 := Nat.le_of_not_lt h
    have h1 := hwf.2.1
    rw [Array.getElem?_eq_none hle] at h1
    cases h1

private theorem pushClass_wf {t : CBTable} (hwf : t.WF) (e : ClassExpr) :
    ({ t with classes := t.classes.push e } : CBTable).WF := by
  have hext := pushClass_extends t e
  exact ⟨by rw [hext.2.2.1 0 (wf_zero_lt hwf), hwf.1],
         by rw [hext.2.2.1 1 (wf_one_lt hwf), hwf.2.1],
         hwf.2.2.1, hwf.2.2.2⟩

private def internExprRaw (e : ClassExpr) (st : ExtState) : Nat × ExtState :=
  match st.exprMap[e]? with
  | some id =>
    if id < st.table.classes.size && st.table.classes[id]? == some e then
      (id, st)
    else
      let newId := st.table.classes.size
      (newId, { st with
        table := { st.table with classes := st.table.classes.push e }
        exprMap := st.exprMap.insert e newId })
  | none =>
    let newId := st.table.classes.size
    (newId, { st with
      table := { st.table with classes := st.table.classes.push e }
      exprMap := st.exprMap.insert e newId })

private theorem internExprRaw_spec {dm : DatatypeMap} {i : Interpretation dm}
    (e : ClassExpr) {st : ExtState} (hv : st.Valid i) :
    let res := internExprRaw e st
    res.2.Valid i ∧ st.table.Extends res.2.table ∧
    res.1 < res.2.table.classes.size ∧ res.2.table.classes[res.1]? = some e := by
  have hpush :
      let st' : ExtState := { st with
        table := { st.table with classes := st.table.classes.push e }
        exprMap := st.exprMap.insert e st.table.classes.size }
      st'.Valid i ∧ st.table.Extends st'.table ∧
      st.table.classes.size < st'.table.classes.size ∧
      st'.table.classes[st.table.classes.size]? = some e := by
    have hext := pushClass_extends st.table e
    refine ⟨⟨pushClass_wf hv.1 e, ?_, ?_⟩, hext, by simp, getElem?_push_eq st.table.classes e⟩
    · intro ax hax
      obtain ⟨hb, hh⟩ := hv.2.1 ax hax
      exact ⟨HornAxiom.inBounds_mono hext hb, HornAxiom.holds_mono hext hb hh⟩
    · intro p hp
      obtain ⟨hlt, heq⟩ := hv.2.2 p hp
      exact ⟨Nat.lt_of_lt_of_le hlt hext.1, by rw [hext.2.2.1 p.2 hlt, heq]⟩
  unfold internExprRaw
  cases hm : st.exprMap[e]? with
  | none => exact hpush
  | some id =>
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact ⟨hv, CBTable.Extends.refl _, hc.1, hc.2⟩
    · exact hpush

/-- Self-verifying class expression interning: returns `(id, st')` with `st'.table.classes[id]? = some e`
    unconditionally (independent of `HashMap` invariants). -/
private def internExpr (e : ClassExpr) (st : ExtState) : Nat × ExtState :=
  let (id, st1) := internExprRaw e st
  match e with
  | .named iri =>
    if st1.namedSeen.contains iri then (id, st1)
    else
      (id, { st1 with
        namedClassIds := st1.namedClassIds.push (iri, id)
        namedSeen := st1.namedSeen.insert iri })
  | _ => (id, st1)

private theorem internExpr_spec {dm : DatatypeMap} {i : Interpretation dm}
    (e : ClassExpr) {st : ExtState} (hv : st.Valid i) :
    let res := internExpr e st
    res.2.Valid i ∧ st.table.Extends res.2.table ∧
    res.1 < res.2.table.classes.size ∧ res.2.table.classes[res.1]? = some e := by
  unfold internExpr
  have hsp := internExprRaw_spec e hv
  rcases h1 : internExprRaw e st with ⟨id, st1⟩
  rw [h1] at hsp
  dsimp only
  obtain ⟨hv1, hext1, hlt1, heq1⟩ := hsp
  cases e with
  | named iri =>
    dsimp only
    split
    · exact ⟨hv1, hext1, hlt1, heq1⟩
    · refine ⟨⟨hv1.1, hv1.2.1, ?_⟩, hext1, hlt1, heq1⟩
      intro p hp
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hv1.2.2 p hp
      · exact ⟨hlt1, heq1⟩
  | _ => exact ⟨hv1, hext1, hlt1, heq1⟩

/-- Self-verifying role path interning: always allocates converse pairs `(2k, 2k+1)` so
    `invRole` is exact converse. -/
private def internRolePath (ps : List ObjectProperty) (st : ExtState) : Nat × ExtState :=
  match st.roleMap[ps]? with
  | some id =>
    if id < st.table.roles.size && st.table.roles[id]? == some ps then
      (id, st)
    else
      let newId := st.table.roles.size
      let rev := conversePath ps
      let roles' := (st.table.roles.push ps).push rev
      let rmap' := (st.roleMap.insert ps newId).insert rev (newId + 1)
      (newId, { st with table := { st.table with roles := roles' }, roleMap := rmap' })
  | none =>
    let newId := st.table.roles.size
    let rev := conversePath ps
    let roles' := (st.table.roles.push ps).push rev
    let rmap' := (st.roleMap.insert ps newId).insert rev (newId + 1)
    (newId, { st with table := { st.table with roles := roles' }, roleMap := rmap' })

private def internRole (r : ObjectProperty) (st : ExtState) : Nat × ExtState :=
  internRolePath [r] st

private theorem pushRolePair_extends (t : CBTable) (ps : List ObjectProperty) :
    t.Extends { t with roles := (t.roles.push ps).push (conversePath ps) } := by
  refine ⟨Nat.le_refl _, by simp; omega, fun _ _ => rfl, ?_⟩
  intro k hk
  have hk1 : k < (t.roles.push ps).size := by simp; omega
  rw [getElem?_push_lt _ _ hk1, getElem?_push_lt _ _ hk]

private theorem pushRolePair_wf {t : CBTable} (hwf : t.WF) (ps : List ObjectProperty) :
    ({ t with roles := (t.roles.push ps).push (conversePath ps) } : CBTable).WF := by
  have hext := pushRolePair_extends t ps
  refine ⟨hwf.1, hwf.2.1, ?_, ?_⟩
  · simp [Array.size_push]; have := hwf.2.2.1; omega
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hlt : 2 * k + 1 < t.roles.size
    · have hlt0 : 2 * k < t.roles.size := by omega
      rw [hext.2.2.2 (2 * k + 1) hlt, hext.2.2.2 (2 * k) hlt0]
      exact hwf.2.2.2 k hlt
    · have hev := hwf.2.2.1
      have h2k : 2 * k = t.roles.size := by omega
      have h2k1 : 2 * k + 1 = (t.roles.push ps).size := by simp; omega
      have hlt_p : 2 * k < (t.roles.push ps).size := by simp; omega
      rw [h2k1, getElem?_push_eq]
      rw [getElem?_push_lt _ _ hlt_p, h2k, getElem?_push_eq]
      rfl

private theorem internRolePath_spec {dm : DatatypeMap} {i : Interpretation dm}
    (ps : List ObjectProperty) {st : ExtState} (hv : st.Valid i) :
    let res := internRolePath ps st
    res.2.Valid i ∧ st.table.Extends res.2.table ∧
    res.1 < res.2.table.roles.size ∧ res.2.table.roles[res.1]? = some ps := by
  have hpush :
      let newId := st.table.roles.size
      let rev := conversePath ps
      let roles' := (st.table.roles.push ps).push rev
      let st' : ExtState :=
        { st with table := { st.table with roles := roles' },
                  roleMap := (st.roleMap.insert ps newId).insert rev (newId + 1) }
      st'.Valid i ∧ st.table.Extends st'.table ∧
      newId < st'.table.roles.size ∧ st'.table.roles[newId]? = some ps := by
    have hext := pushRolePair_extends st.table ps
    refine ⟨⟨pushRolePair_wf hv.1 ps, ?_, hv.2.2⟩, hext, by simp; omega, ?_⟩
    · intro ax hax
      obtain ⟨hb, hh⟩ := hv.2.1 ax hax
      exact ⟨HornAxiom.inBounds_mono hext hb, HornAxiom.holds_mono hext hb hh⟩
    · have hlt : st.table.roles.size < (st.table.roles.push ps).size := by simp
      rw [getElem?_push_lt _ _ hlt, getElem?_push_eq]
  unfold internRolePath
  cases hm : st.roleMap[ps]? with
  | none => exact hpush
  | some id =>
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact ⟨hv, CBTable.Extends.refl _, hc.1, hc.2⟩
    · exact hpush

private theorem internRole_spec {dm : DatatypeMap} {i : Interpretation dm}
    (r : ObjectProperty) {st : ExtState} (hv : st.Valid i) :
    let res := internRole r st
    res.2.Valid i ∧ st.table.Extends res.2.table ∧
    res.1 < res.2.table.roles.size ∧ res.2.table.roles[res.1]? = some [r] :=
  internRolePath_spec [r] hv

private def emitAxiom (ax : HornAxiom) (st : ExtState) : ExtState :=
  { st with axioms := st.axioms.push ax }

private theorem emitAxiom_valid {dm : DatatypeMap} {i : Interpretation dm}
    {st : ExtState} (hv : st.Valid i) {ax : HornAxiom}
    (hb : ax.inBounds st.table) (hh : ax.holds st.table i) :
    (emitAxiom ax st).Valid i := by
  refine ⟨hv.1, ?_, hv.2.2⟩
  intro ax' hax'
  simp only [emitAxiom, Array.toList_push, List.mem_append, List.mem_singleton] at hax'
  rcases hax' with h | rfl
  · exact hv.2.1 ax' h
  · exact ⟨hb, hh⟩

private def markNonHorn (st : ExtState) : ExtState :=
  { st with isPureHornSHIQ := false }

private theorem markNonHorn_valid {dm : DatatypeMap} {i : Interpretation dm}
    {st : ExtState} (hv : st.Valid i) : (markNonHorn st).Valid i := hv

private theorem exprOf_of_getElem? {t : CBTable} {c : Nat} {e : ClassExpr}
    (h : t.classes[c]? = some e) : t.exprOf c = e := by
  simp [CBTable.exprOf, h]

private theorem roleOf_of_getElem? {t : CBTable} {r : Nat} {ps : List ObjectProperty}
    (h : t.roles[r]? = some ps) : t.roleOf r = ps := by
  simp [CBTable.roleOf, h]

private theorem atLeast_zero {α : Type} (p : α → Prop) : AtLeast 0 p :=
  ⟨[], rfl, List.nodup_nil, fun _ h => nomatch h⟩

private theorem atLeast_one_iff {α : Type} (p : α → Prop) : AtLeast 1 p ↔ ∃ y, p y := by
  constructor
  · rintro ⟨xs, hlen, _, hp⟩
    cases xs with
    | nil => simp at hlen
    | cons y _ => exact ⟨y, hp y (List.mem_cons_self ..)⟩
  · rintro ⟨y, hy⟩
    exact ⟨[y], rfl, by simp, fun z hz => (List.mem_singleton.mp hz) ▸ hy⟩

private theorem atLeast_succ_exists {α : Type} {n : Nat} {p : α → Prop}
    (h : AtLeast (n + 1) p) : ∃ y, p y := by
  obtain ⟨xs, hlen, _, hp⟩ := h
  cases xs with
  | nil => simp at hlen
  | cons y _ => exact ⟨y, hp y (List.mem_cons_self ..)⟩

private theorem invRole_lt {t : CBTable} (hwf : t.WF) {r : Nat} (hr : r < t.roles.size) :
    invRole r < t.roles.size := by
  have hev := hwf.2.2.1
  unfold invRole
  by_cases h : r % 2 = 0
  · simp [h]; omega
  · simp [h]; omega

/-! ### 4. Positive-Body Normalization (`normPosBody`) -/

/-- Normalize a positive-polarity LHS class expression `e`, returning `(some id, st')`
    where `st'.table.classes[id]? = some e` and all structural upward Horn axioms
    (conjunction, union, existential, min-1) have been emitted.
    Returns `(none, st')` (and marks `isPureHornSHIQ := false`) on non-positive LHS expressions. -/
private def normPosBody : ClassExpr → ExtState → Option Nat × ExtState
  | e@(.named _), st =>
    let (id, st1) := internExpr e st
    (some id, st1)
  | e@(.intersection a b), st =>
    let (oa, st1) := normPosBody a st
    let (ob, st2) := normPosBody b st1
    match oa, ob with
    | some ca, some cb =>
      let (id, st3) := internExpr e st2
      (some id, emitAxiom (.sub #[ca, cb] id) st3)
    | _, _ => (none, markNonHorn st2)
  | e@(.union a b), st =>
    let (oa, st1) := normPosBody a st
    let (ob, st2) := normPosBody b st1
    match oa, ob with
    | some ca, some cb =>
      let (id, st3) := internExpr e st2
      let st4 := emitAxiom (.sub #[ca] id) st3
      let st5 := emitAxiom (.sub #[cb] id) st4
      (some id, st5)
    | _, _ => (none, markNonHorn st2)
  | e@(.objectSome r f), st =>
    let (of, st1) := normPosBody f st
    match of with
    | some cf =>
      let (rid, st2) := internRole r st1
      let (id, st3) := internExpr e st2
      (some id, emitAxiom (.existL rid cf id) st3)
    | none => (none, markNonHorn st1)
  | e@(.objectMin 0 _ _), st =>
    let (id, st1) := internExpr e st
    (some id, emitAxiom (.sub #[0] id) st1)
  | e@(.objectMin 1 r f), st =>
    let (of, st1) := normPosBody f st
    match of with
    | some cf =>
      let (rid, st2) := internRole r st1
      let (id, st3) := internExpr e st2
      (some id, emitAxiom (.existL rid cf id) st3)
    | none => (none, markNonHorn st1)
  | _, st => (none, markNonHorn st)

private theorem normPosBody_spec {dm : DatatypeMap} {i : Interpretation dm} :
    ∀ (e : ClassExpr) {st : ExtState}, st.Valid i →
      let res := normPosBody e st
      res.2.Valid i ∧ st.table.Extends res.2.table ∧
      (∀ id, res.1 = some id →
        id < res.2.table.classes.size ∧ res.2.table.classes[id]? = some e)
  | .named name, st, hv => by
    unfold normPosBody
    have hsp := internExpr_spec (.named name) hv
    rcases h1 : internExpr (.named name) st with ⟨id, st1⟩
    rw [h1] at hsp; dsimp only
    exact ⟨hsp.1, hsp.2.1, fun id' hid => by cases hid; exact hsp.2.2⟩
  | .intersection a b, st, hv => by
    unfold normPosBody
    have hsp1 := normPosBody_spec a hv
    rcases h1 : normPosBody a st with ⟨oa, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    have hsp2 := normPosBody_spec b hv1
    rcases h2 : normPosBody b st1 with ⟨ob, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hpos2⟩ := hsp2
    cases oa with
    | none => exact ⟨markNonHorn_valid hv2, hext1.trans hext2, fun _ h => nomatch h⟩
    | some ca =>
      cases ob with
      | none => exact ⟨markNonHorn_valid hv2, hext1.trans hext2, fun _ h => nomatch h⟩
      | some cb =>
        dsimp only
        obtain ⟨hlta, heqa⟩ := hpos1 ca rfl
        obtain ⟨hltb, heqb⟩ := hpos2 cb rfl
        have hsp3 := internExpr_spec (.intersection a b) hv2
        rcases h3 : internExpr (.intersection a b) st2 with ⟨id, st3⟩
        rw [h3] at hsp3; dsimp only
        obtain ⟨hv3, hext3, hlt3, heq3⟩ := hsp3
        have hext13 := hext2.trans hext3
        have hlta3 : ca < st3.table.classes.size := Nat.lt_of_lt_of_le hlta hext13.1
        have hltb3 : cb < st3.table.classes.size := Nat.lt_of_lt_of_le hltb hext3.1
        have heqa3 : st3.table.classes[ca]? = some a := by rw [hext13.2.2.1 ca hlta, heqa]
        have heqb3 : st3.table.classes[cb]? = some b := by rw [hext3.2.2.1 cb hltb, heqb]
        have hv4 : (emitAxiom (.sub #[ca, cb] id) st3).Valid i := by
          apply emitAxiom_valid hv3
          · refine ⟨fun c hc => ?_, hlt3⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> assumption
          · intro x hpre
            rw [exprOf_of_getElem? heq3]
            have ha' := hpre ca (by simp)
            have hb' := hpre cb (by simp)
            rw [exprOf_of_getElem? heqa3] at ha'
            rw [exprOf_of_getElem? heqb3] at hb'
            exact ⟨ha', hb'⟩
        exact ⟨hv4, (hext1.trans hext2).trans hext3, fun id' hid => by cases hid; exact ⟨hlt3, heq3⟩⟩
  | .union a b, st, hv => by
    unfold normPosBody
    have hsp1 := normPosBody_spec a hv
    rcases h1 : normPosBody a st with ⟨oa, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    have hsp2 := normPosBody_spec b hv1
    rcases h2 : normPosBody b st1 with ⟨ob, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hpos2⟩ := hsp2
    cases oa with
    | none => exact ⟨markNonHorn_valid hv2, hext1.trans hext2, fun _ h => nomatch h⟩
    | some ca =>
      cases ob with
      | none => exact ⟨markNonHorn_valid hv2, hext1.trans hext2, fun _ h => nomatch h⟩
      | some cb =>
        dsimp only
        obtain ⟨hlta, heqa⟩ := hpos1 ca rfl
        obtain ⟨hltb, heqb⟩ := hpos2 cb rfl
        have hsp3 := internExpr_spec (.union a b) hv2
        rcases h3 : internExpr (.union a b) st2 with ⟨id, st3⟩
        rw [h3] at hsp3; dsimp only
        obtain ⟨hv3, hext3, hlt3, heq3⟩ := hsp3
        have hext13 := hext2.trans hext3
        have hlta3 : ca < st3.table.classes.size := Nat.lt_of_lt_of_le hlta hext13.1
        have hltb3 : cb < st3.table.classes.size := Nat.lt_of_lt_of_le hltb hext3.1
        have heqa3 : st3.table.classes[ca]? = some a := by rw [hext13.2.2.1 ca hlta, heqa]
        have heqb3 : st3.table.classes[cb]? = some b := by rw [hext3.2.2.1 cb hltb, heqb]
        have hv4 : (emitAxiom (.sub #[ca] id) st3).Valid i := by
          apply emitAxiom_valid hv3
          · refine ⟨fun c hc => ?_, hlt3⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact hlta3
          · intro x hpre
            rw [exprOf_of_getElem? heq3]
            have ha' := hpre ca (by simp)
            rw [exprOf_of_getElem? heqa3] at ha'
            exact Or.inl ha'
        have hv5 : (emitAxiom (.sub #[cb] id) (emitAxiom (.sub #[ca] id) st3)).Valid i := by
          apply emitAxiom_valid hv4
          · refine ⟨fun c hc => ?_, hlt3⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact hltb3
          · intro x hpre
            simp only [emitAxiom] at hpre ⊢
            rw [exprOf_of_getElem? heq3]
            have hb' := hpre cb (by simp)
            rw [exprOf_of_getElem? heqb3] at hb'
            exact Or.inr hb'
        exact ⟨hv5, (hext1.trans hext2).trans hext3, fun id' hid => by cases hid; exact ⟨hlt3, heq3⟩⟩
  | .objectSome r f, st, hv => by
    simp only [normPosBody]
    have hsp1 := normPosBody_spec f hv
    rcases h1 : normPosBody f st with ⟨of, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    cases of with
    | none => exact ⟨markNonHorn_valid hv1, hext1, fun _ h => nomatch h⟩
    | some cf =>
      dsimp only
      obtain ⟨hltf, heqf⟩ := hpos1 cf rfl
      have hsp2 := internRole_spec r hv1
      rcases h2 : internRole r st1 with ⟨rid, st2⟩
      rw [h2] at hsp2; dsimp only
      obtain ⟨hv2, hext2, hltr, heqr⟩ := hsp2
      have hsp3 := internExpr_spec (.objectSome r f) hv2
      rcases h3 : internExpr (.objectSome r f) st2 with ⟨id, st3⟩
      rw [h3] at hsp3; dsimp only
      obtain ⟨hv3, hext3, hlt3, heq3⟩ := hsp3
      have hext13 := hext2.trans hext3
      have hltf3 : cf < st3.table.classes.size := Nat.lt_of_lt_of_le hltf hext13.1
      have hltr3 : rid < st3.table.roles.size := Nat.lt_of_lt_of_le hltr hext3.2.1
      have heqf3 : st3.table.classes[cf]? = some f := by rw [hext13.2.2.1 cf hltf, heqf]
      have heqr3 : st3.table.roles[rid]? = some [r] := by rw [hext3.2.2.2 rid hltr, heqr]
      have hv4 : (emitAxiom (.existL rid cf id) st3).Valid i := by
        apply emitAxiom_valid hv3
        · exact ⟨hltr3, hltf3, hlt3⟩
        · intro x y hry hyf
          rw [roleOf_of_getElem? heqr3, rolePath_singleton] at hry
          rw [exprOf_of_getElem? heqf3] at hyf
          rw [exprOf_of_getElem? heq3]
          exact ⟨y, hry, hyf⟩
      exact ⟨hv4, (hext1.trans hext2).trans hext3, fun id' hid => by cases hid; exact ⟨hlt3, heq3⟩⟩
  | .objectMin 0 r f, st, hv => by
    simp only [normPosBody]
    have hsp1 := internExpr_spec (.objectMin 0 r f) hv
    rcases h1 : internExpr (.objectMin 0 r f) st with ⟨id, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hlt1, heq1⟩ := hsp1
    have hv2 : (emitAxiom (.sub #[0] id) st1).Valid i := by
      apply emitAxiom_valid hv1
      · refine ⟨fun c hc => ?_, hlt1⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact wf_zero_lt hv1.1
      · intro x _
        rw [exprOf_of_getElem? heq1]
        exact atLeast_zero _
    exact ⟨hv2, hext1, fun id' hid => by cases hid; exact ⟨hlt1, heq1⟩⟩
  | .objectMin 1 r f, st, hv => by
    simp only [normPosBody]
    have hsp1 := normPosBody_spec f hv
    rcases h1 : normPosBody f st with ⟨of, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    cases of with
    | none => exact ⟨markNonHorn_valid hv1, hext1, fun _ h => nomatch h⟩
    | some cf =>
      dsimp only
      obtain ⟨hltf, heqf⟩ := hpos1 cf rfl
      have hsp2 := internRole_spec r hv1
      rcases h2 : internRole r st1 with ⟨rid, st2⟩
      rw [h2] at hsp2; dsimp only
      obtain ⟨hv2, hext2, hltr, heqr⟩ := hsp2
      have hsp3 := internExpr_spec (.objectMin 1 r f) hv2
      rcases h3 : internExpr (.objectMin 1 r f) st2 with ⟨id, st3⟩
      rw [h3] at hsp3; dsimp only
      obtain ⟨hv3, hext3, hlt3, heq3⟩ := hsp3
      have hext13 := hext2.trans hext3
      have hltf3 : cf < st3.table.classes.size := Nat.lt_of_lt_of_le hltf hext13.1
      have hltr3 : rid < st3.table.roles.size := Nat.lt_of_lt_of_le hltr hext3.2.1
      have heqf3 : st3.table.classes[cf]? = some f := by rw [hext13.2.2.1 cf hltf, heqf]
      have heqr3 : st3.table.roles[rid]? = some [r] := by rw [hext3.2.2.2 rid hltr, heqr]
      have hv4 : (emitAxiom (.existL rid cf id) st3).Valid i := by
        apply emitAxiom_valid hv3
        · exact ⟨hltr3, hltf3, hlt3⟩
        · intro x y hry hyf
          rw [roleOf_of_getElem? heqr3, rolePath_singleton] at hry
          rw [exprOf_of_getElem? heqf3] at hyf
          rw [exprOf_of_getElem? heq3]
          exact (atLeast_one_iff _).mpr ⟨y, hry, hyf⟩
      exact ⟨hv4, (hext1.trans hext2).trans hext3, fun id' hid => by cases hid; exact ⟨hlt3, heq3⟩⟩
  | .objectMin (_ + 2) _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .complement _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .oneOf _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .objectAll _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .objectValue _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .objectSelf _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .objectMax _ _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .objectExact _ _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataSome _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataAll _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataValue _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataMin _ _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataMax _ _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩
  | .dataExact _ _ _, _, hv => ⟨markNonHorn_valid hv, CBTable.Extends.refl _, fun _ h => nomatch h⟩

/-! ### 5. Horn-Head Normalization (`normHornHead`) -/

/-- Normalize `lhs ⊑ rhs` where `lhs` is an already-interned `ClassId` and `rhs` is
    a Horn-$\mathcal{SHIQ}$ head expression. Emits normal-form axioms entailed by
    `lhs ⊑ rhs` and marks `isPureHornSHIQ := false` on any non-Horn sub-expression. -/
private def normHornHead (lhs : Nat) : ClassExpr → ExtState → ExtState
  | e@(.named _), st =>
    let (rhsId, st1) := internExpr e st
    if lhs == rhsId then st1 else emitAxiom (.sub #[lhs] rhsId) st1
  | .intersection a b, st =>
    let st1 := normHornHead lhs a st
    normHornHead lhs b st1
  | .objectSome r f, st =>
    let (rid, st1) := internRole r st
    let (cf, st2) := internExpr f st1
    let st3 := emitAxiom (.existR lhs rid cf) st2
    normHornHead cf f st3
  | .objectMin 0 _ _, st => st
  | .objectMin (k + 1) r f, st =>
    let (rid, st1) := internRole r st
    let (cf, st2) := internExpr f st1
    let st3 := emitAxiom (.existR lhs rid cf) st2
    let st4 := if k == 0 then st3 else markNonHorn st3
    normHornHead cf f st4
  | .objectAll r f, st =>
    let (rid, st1) := internRole r st
    let (cf, st2) := internExpr f st1
    let st3 := emitAxiom (.allR lhs rid cf) st2
    normHornHead cf f st3
  | .complement body, st =>
    let (ob, st1) := normPosBody body st
    match ob with
    | some cb => emitAxiom (.sub #[lhs, cb] 1) st1
    | none => markNonHorn st1
  | .objectMax 0 r f, st =>
    let (ob, st1) := normPosBody f st
    match ob with
    | some cf =>
      let (rid, st2) := internRole r st1
      let (cNotF, st3) := internExpr (.complement f) st2
      let st4 := emitAxiom (.allR lhs rid cNotF) st3
      emitAxiom (.sub #[cNotF, cf] 1) st4
    | none => markNonHorn st1
  | .objectMax 1 r f, st =>
    let (ob, st1) := normPosBody f st
    match ob with
    | some cf =>
      let (rid, st2) := internRole r st1
      emitAxiom (.maxOne lhs rid cf) st2
    | none => markNonHorn st1
  | .objectExact 1 r f, st =>
    let (rid, st1) := internRole r st
    let (cf, st2) := internExpr f st1
    let st3 := emitAxiom (.existR lhs rid cf) st2
    let st4 := normHornHead cf f st3
    let (ob, st5) := normPosBody f st4
    match ob with
    | some cfPos => emitAxiom (.maxOne lhs rid cfPos) st5
    | none => markNonHorn st5
  | .union a b, st =>
    match a, b with
    | .complement a', b =>
      let (oa, st1) := normPosBody a' st
      match oa with
      | some ca =>
        let lhsExpr := st1.table.exprOf lhs
        let (conjId, st2) := internExpr (.intersection lhsExpr a') st1
        let st3 := emitAxiom (.sub #[lhs, ca] conjId) st2
        normHornHead conjId b st3
      | none => markNonHorn st1
    | a, .complement b' =>
      let (ob, st1) := normPosBody b' st
      match ob with
      | some cb =>
        let lhsExpr := st1.table.exprOf lhs
        let (conjId, st2) := internExpr (.intersection lhsExpr b') st1
        let st3 := emitAxiom (.sub #[lhs, cb] conjId) st2
        normHornHead conjId a st3
      | none => markNonHorn st1
    | _, _ => markNonHorn st
  | _, st => markNonHorn st

/-- Shared proof helper for `.union (.complement a') b` / `.union a (.complement b')`. -/
private theorem hornUnionNeg_helper {dm : DatatypeMap} {i : Interpretation dm}
    {lhs : Nat} {negBody other : ClassExpr} {st : ExtState}
    (hv : st.Valid i) (hlhs : lhs < st.table.classes.size)
    (hstep : ∀ x, classHolds i x (st.table.exprOf lhs) → classHolds i x negBody → classHolds i x other)
    (ihOther : ∀ (l : Nat) {s : ExtState}, s.Valid i → l < s.table.classes.size →
      (∀ x, classHolds i x (s.table.exprOf l) → classHolds i x other) →
      (normHornHead l other s).Valid i ∧ s.table.Extends (normHornHead l other s).table) :
    let (oa, st1) := normPosBody negBody st
    let res := match oa with
      | some ca =>
        let lhsExpr := st1.table.exprOf lhs
        let (conjId, st2) := internExpr (.intersection lhsExpr negBody) st1
        let st3 := emitAxiom (.sub #[lhs, ca] conjId) st2
        normHornHead conjId other st3
      | none => markNonHorn st1
    res.Valid i ∧ st.table.Extends res.table := by
  have hsp1 := normPosBody_spec negBody hv
  rcases h1 : normPosBody negBody st with ⟨oa, st1⟩
  rw [h1] at hsp1; dsimp only
  obtain ⟨hv1, hext1, hpos1⟩ := hsp1
  cases oa with
  | none => exact ⟨markNonHorn_valid hv1, hext1⟩
  | some ca =>
    dsimp only
    obtain ⟨hlta, heqa⟩ := hpos1 ca rfl
    let lhsExpr := st1.table.exprOf lhs
    have hsp2 := internExpr_spec (.intersection lhsExpr negBody) hv1
    rcases h2 : internExpr (.intersection lhsExpr negBody) st1 with ⟨conjId, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltc, heqc⟩ := hsp2
    have hlhs1 : lhs < st1.table.classes.size := Nat.lt_of_lt_of_le hlhs hext1.1
    have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs1 hext2.1
    have hlta2 : ca < st2.table.classes.size := Nat.lt_of_lt_of_le hlta hext2.1
    have heqa2 : st2.table.classes[ca]? = some negBody := by rw [hext2.2.2.1 ca hlta, heqa]
    have hv3 : (emitAxiom (.sub #[lhs, ca] conjId) st2).Valid i := by
      apply emitAxiom_valid hv2
      · refine ⟨fun c hc => ?_, hltc⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> assumption
      · intro x hpre
        rw [exprOf_of_getElem? heqc]
        have h1' := hpre lhs (by simp)
        have h2' := hpre ca (by simp)
        rw [hext2.exprOf_eq hlhs1] at h1'
        rw [exprOf_of_getElem? heqa2] at h2'
        exact ⟨h1', h2'⟩
    have hentO : ∀ x, classHolds i x ((emitAxiom (.sub #[lhs, ca] conjId) st2).table.exprOf conjId) →
        classHolds i x other := by
      intro x hx
      simp only [emitAxiom, exprOf_of_getElem? heqc] at hx
      obtain ⟨hlx, hnx⟩ := hx
      have heql : lhsExpr = st.table.exprOf lhs := hext1.exprOf_eq hlhs
      rw [heql] at hlx
      exact hstep x hlx hnx
    obtain ⟨hv4, hext4⟩ := ihOther conjId hv3 hltc hentO
    exact ⟨hv4, (hext1.trans hext2).trans hext4⟩

private theorem normHornHead_spec {dm : DatatypeMap} {i : Interpretation dm} :
    ∀ (rhs : ClassExpr) (lhs : Nat) {st : ExtState},
      st.Valid i →
      lhs < st.table.classes.size →
      (∀ x, classHolds i x (st.table.exprOf lhs) → classHolds i x rhs) →
      let st' := normHornHead lhs rhs st
      st'.Valid i ∧ st.table.Extends st'.table
  | .named name, lhs, st, hv, hlhs, hent => by
    unfold normHornHead
    have hsp1 := internExpr_spec (.named name) hv
    rcases h1 : internExpr (.named name) st with ⟨rhsId, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hlt1, heq1⟩ := hsp1
    split
    · exact ⟨hv1, hext1⟩
    · have hlhs1 : lhs < st1.table.classes.size := Nat.lt_of_lt_of_le hlhs hext1.1
      have hv2 : (emitAxiom (.sub #[lhs] rhsId) st1).Valid i := by
        apply emitAxiom_valid hv1
        · refine ⟨fun c hc => ?_, hlt1⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact hlhs1
        · intro x hpre
          rw [exprOf_of_getElem? heq1]
          have h1' := hpre lhs (by simp)
          rw [hext1.exprOf_eq hlhs] at h1'
          exact hent x h1'
      exact ⟨hv2, hext1⟩
  | .intersection a b, lhs, st, hv, hlhs, hent => by
    unfold normHornHead
    obtain ⟨hv1, hext1⟩ := normHornHead_spec a lhs hv hlhs (fun x hx => (hent x hx).1)
    have hlhs1 : lhs < (normHornHead lhs a st).table.classes.size := Nat.lt_of_lt_of_le hlhs hext1.1
    obtain ⟨hv2, hext2⟩ := normHornHead_spec b lhs hv1 hlhs1 (fun x hx => by
      rw [hext1.exprOf_eq hlhs] at hx; exact (hent x hx).2)
    exact ⟨hv2, hext1.trans hext2⟩
  | .objectSome r f, lhs, st, hv, hlhs, hent => by
    unfold normHornHead
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec f hv1
    rcases h2 : internExpr f st1 with ⟨cf, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltf, heqf⟩ := hsp2
    have hext12 := hext1.trans hext2
    have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs hext12.1
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.existR lhs rid cf) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨hlhs2, hltr2, hltf⟩
      · intro x hx
        rw [hext12.exprOf_eq hlhs] at hx
        obtain ⟨y, hry, hyf⟩ := hent x hx
        exact ⟨y, by rw [roleOf_of_getElem? heqr2, rolePath_singleton]; exact hry,
                  by rw [exprOf_of_getElem? heqf]; exact hyf⟩
    obtain ⟨hv4, hext4⟩ := normHornHead_spec f cf hv3 hltf (fun x hx => by
      simpa [emitAxiom, exprOf_of_getElem? heqf] using hx)
    exact ⟨hv4, hext12.trans hext4⟩
  | .objectMin 0 _ _, _, _, hv, _, _ => ⟨hv, CBTable.Extends.refl _⟩
  | .objectMin (k + 1) r f, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec f hv1
    rcases h2 : internExpr f st1 with ⟨cf, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltf, heqf⟩ := hsp2
    have hext12 := hext1.trans hext2
    have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs hext12.1
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.existR lhs rid cf) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨hlhs2, hltr2, hltf⟩
      · intro x hx
        rw [hext12.exprOf_eq hlhs] at hx
        obtain ⟨y, hry, hyf⟩ := atLeast_succ_exists (hent x hx)
        exact ⟨y, by rw [roleOf_of_getElem? heqr2, rolePath_singleton]; exact hry,
                  by rw [exprOf_of_getElem? heqf]; exact hyf⟩
    let st3 := emitAxiom (.existR lhs rid cf) st2
    let st4 := if k == 0 then st3 else markNonHorn st3
    have hv4 : st4.Valid i := by
      dsimp only [st4]
      split
      · exact hv3
      · exact markNonHorn_valid hv3
    have htbl4 : st4.table = st2.table := by
      dsimp only [st4, st3]
      split <;> rfl
    obtain ⟨hv5, hext5⟩ := normHornHead_spec f cf hv4 (htbl4 ▸ hltf) (fun x hx => by
      rw [htbl4, exprOf_of_getElem? heqf] at hx; exact hx)
    rw [htbl4] at hext5
    exact ⟨hv5, hext12.trans hext5⟩
  | .objectAll r f, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec f hv1
    rcases h2 : internExpr f st1 with ⟨cf, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltf, heqf⟩ := hsp2
    have hext12 := hext1.trans hext2
    have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs hext12.1
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.allR lhs rid cf) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨hlhs2, hltr2, hltf⟩
      · intro x hx y hry
        rw [hext12.exprOf_eq hlhs] at hx
        rw [roleOf_of_getElem? heqr2, rolePath_singleton] at hry
        rw [exprOf_of_getElem? heqf]
        exact hent x hx y hry
    obtain ⟨hv4, hext4⟩ := normHornHead_spec f cf hv3 hltf (fun x hx => by
      simpa [emitAxiom, exprOf_of_getElem? heqf] using hx)
    exact ⟨hv4, hext12.trans hext4⟩
  | .complement body, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := normPosBody_spec body hv
    rcases h1 : normPosBody body st with ⟨ob, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    cases ob with
    | none => exact ⟨markNonHorn_valid hv1, hext1⟩
    | some cb =>
      dsimp only
      obtain ⟨hltb, heqb⟩ := hpos1 cb rfl
      have hlhs1 : lhs < st1.table.classes.size := Nat.lt_of_lt_of_le hlhs hext1.1
      have hv2 : (emitAxiom (.sub #[lhs, cb] 1) st1).Valid i := by
        apply emitAxiom_valid hv1
        · refine ⟨fun c hc => ?_, wf_one_lt hv1.1⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> assumption
        · intro x hpre
          have h1' := hpre lhs (by simp)
          have h2' := hpre cb (by simp)
          rw [hext1.exprOf_eq hlhs] at h1'
          rw [exprOf_of_getElem? heqb] at h2'
          exact absurd h2' (hent x h1')
      exact ⟨hv2, hext1⟩
  | .objectMax 0 r f, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := normPosBody_spec f hv
    rcases h1 : normPosBody f st with ⟨ob, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    cases ob with
    | none => exact ⟨markNonHorn_valid hv1, hext1⟩
    | some cf =>
      dsimp only
      obtain ⟨hltf, heqf⟩ := hpos1 cf rfl
      have hsp2 := internRole_spec r hv1
      rcases h2 : internRole r st1 with ⟨rid, st2⟩
      rw [h2] at hsp2; dsimp only
      obtain ⟨hv2, hext2, hltr, heqr⟩ := hsp2
      have hsp3 := internExpr_spec (.complement f) hv2
      rcases h3 : internExpr (.complement f) st2 with ⟨cNotF, st3⟩
      rw [h3] at hsp3; dsimp only
      obtain ⟨hv3, hext3, hltc, heqc⟩ := hsp3
      have hext13 := (hext1.trans hext2).trans hext3
      have hext23 := hext2.trans hext3
      have hlhs3 : lhs < st3.table.classes.size := Nat.lt_of_lt_of_le hlhs hext13.1
      have hltf3 : cf < st3.table.classes.size := Nat.lt_of_lt_of_le hltf hext23.1
      have hltr3 : rid < st3.table.roles.size := Nat.lt_of_lt_of_le hltr hext3.2.1
      have heqr3 : st3.table.roles[rid]? = some [r] := by rw [hext3.2.2.2 rid hltr, heqr]
      have heqf3 : st3.table.classes[cf]? = some f := by rw [hext23.2.2.1 cf hltf, heqf]
      have hv4 : (emitAxiom (.allR lhs rid cNotF) st3).Valid i := by
        apply emitAxiom_valid hv3
        · exact ⟨hlhs3, hltr3, hltc⟩
        · intro x hx y hry
          rw [hext13.exprOf_eq hlhs] at hx
          rw [roleOf_of_getElem? heqr3, rolePath_singleton] at hry
          rw [exprOf_of_getElem? heqc]
          intro hyf
          exact hent x hx ((atLeast_one_iff _).mpr ⟨y, hry, hyf⟩)
      have hv5 : (emitAxiom (.sub #[cNotF, cf] 1) (emitAxiom (.allR lhs rid cNotF) st3)).Valid i := by
        apply emitAxiom_valid hv4
        · refine ⟨fun c hc => ?_, wf_one_lt hv3.1⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> assumption
        · intro x hpre
          have h1' := hpre cNotF (by simp)
          have h2' := hpre cf (by simp)
          simp only [emitAxiom] at h1' h2' ⊢
          rw [exprOf_of_getElem? heqc] at h1'
          rw [exprOf_of_getElem? heqf3] at h2'
          exact absurd h2' h1'
      exact ⟨hv5, hext13⟩
  | .objectMax 1 r f, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := normPosBody_spec f hv
    rcases h1 : normPosBody f st with ⟨ob, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hpos1⟩ := hsp1
    cases ob with
    | none => exact ⟨markNonHorn_valid hv1, hext1⟩
    | some cf =>
      dsimp only
      obtain ⟨hltf, heqf⟩ := hpos1 cf rfl
      have hsp2 := internRole_spec r hv1
      rcases h2 : internRole r st1 with ⟨rid, st2⟩
      rw [h2] at hsp2; dsimp only
      obtain ⟨hv2, hext2, hltr, heqr⟩ := hsp2
      have hext12 := hext1.trans hext2
      have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs hext12.1
      have hltf2 : cf < st2.table.classes.size := Nat.lt_of_lt_of_le hltf hext2.1
      have heqf2 : st2.table.classes[cf]? = some f := by rw [hext2.2.2.1 cf hltf, heqf]
      have hv3 : (emitAxiom (.maxOne lhs rid cf) st2).Valid i := by
        apply emitAxiom_valid hv2
        · exact ⟨hlhs2, hltr, hltf2⟩
        · intro x hx y z hry hyf hrz hzf
          rw [hext12.exprOf_eq hlhs] at hx
          rw [roleOf_of_getElem? heqr, rolePath_singleton] at hry hrz
          rw [exprOf_of_getElem? heqf2] at hyf hzf
          exact (atMostOne_iff _).mp (hent x hx) y z ⟨hry, hyf⟩ ⟨hrz, hzf⟩
      exact ⟨hv3, hext12⟩
  | .objectMax (_ + 2) _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .objectExact 1 r f, lhs, st, hv, hlhs, hent => by
    simp only [normHornHead]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec f hv1
    rcases h2 : internExpr f st1 with ⟨cf, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltf, heqf⟩ := hsp2
    have hext12 := hext1.trans hext2
    have hlhs2 : lhs < st2.table.classes.size := Nat.lt_of_lt_of_le hlhs hext12.1
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.existR lhs rid cf) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨hlhs2, hltr2, hltf⟩
      · intro x hx
        rw [hext12.exprOf_eq hlhs] at hx
        obtain ⟨y, hry, hyf⟩ := (atLeast_one_iff _).mp (hent x hx).1
        exact ⟨y, by rw [roleOf_of_getElem? heqr2, rolePath_singleton]; exact hry,
                  by rw [exprOf_of_getElem? heqf]; exact hyf⟩
    obtain ⟨hv4, hext4⟩ := normHornHead_spec f cf hv3 hltf (fun x hx => by
      simpa [emitAxiom, exprOf_of_getElem? heqf] using hx)
    have hsp5 := normPosBody_spec f hv4
    rcases h5 : normPosBody f (normHornHead cf f (emitAxiom (.existR lhs rid cf) st2)) with ⟨ob, st5⟩
    rw [h5] at hsp5; dsimp only
    obtain ⟨hv5, hext5, hpos5⟩ := hsp5
    have hext15 := (hext12.trans hext4).trans hext5
    cases ob with
    | none => exact ⟨markNonHorn_valid hv5, hext15⟩
    | some cfPos =>
      dsimp only
      obtain ⟨hltp, heqp⟩ := hpos5 cfPos rfl
      have hext25 := (hext2.trans hext4).trans hext5
      have hlhs5 : lhs < st5.table.classes.size := Nat.lt_of_lt_of_le hlhs hext15.1
      have hltr5 : rid < st5.table.roles.size := Nat.lt_of_lt_of_le hltr hext25.2.1
      have heqr5 : st5.table.roles[rid]? = some [r] := by rw [hext25.2.2.2 rid hltr, heqr]
      have hv6 : (emitAxiom (.maxOne lhs rid cfPos) st5).Valid i := by
        apply emitAxiom_valid hv5
        · exact ⟨hlhs5, hltr5, hltp⟩
        · intro x hx y z hry hyf hrz hzf
          rw [hext15.exprOf_eq hlhs] at hx
          rw [roleOf_of_getElem? heqr5, rolePath_singleton] at hry hrz
          rw [exprOf_of_getElem? heqp] at hyf hzf
          exact (atMostOne_iff _).mp (hent x hx).2 y z ⟨hry, hyf⟩ ⟨hrz, hzf⟩
      exact ⟨hv6, hext15⟩
  | .objectExact 0 _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .objectExact (_ + 2) _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .union a b, lhs, st, hv, hlhs, hent => by
    cases a with
    | complement a' =>
      exact hornUnionNeg_helper hv hlhs
        (fun x hl ha => (hent x hl).elim (fun hna => absurd ha hna) id)
        (fun l {s} hvs hls h => normHornHead_spec b l hvs hls h)
    | _ =>
      cases b with
      | complement b' =>
        exact hornUnionNeg_helper hv hlhs
          (fun x hl hb => (hent x hl).elim id (fun hnb => absurd hb hnb))
          (fun l {s} hvs hls h => normHornHead_spec _ l hvs hls h)
      | _ => exact ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .oneOf _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .objectValue _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .objectSelf _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataSome _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataAll _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataValue _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataMin _ _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataMax _ _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩
  | .dataExact _ _ _, _, _, hv, _, _ => ⟨markNonHorn_valid hv, CBTable.Extends.refl _⟩

/-! ### 6. Axiom-Level Extraction -/

private def addSubClass (a b : ClassExpr) (st : ExtState) : ExtState :=
  let (oa, st1) := normPosBody a st
  match oa with
  | some ca => normHornHead ca b st1
  | none => markNonHorn st1

private theorem addSubClass_valid {dm : DatatypeMap} {i : Interpretation dm}
    {a b : ClassExpr} {st : ExtState} (hv : st.Valid i)
    (hsub : ∀ x, classHolds i x a → classHolds i x b) :
    (addSubClass a b st).Valid i := by
  unfold addSubClass
  have hsp1 := normPosBody_spec a hv
  rcases h1 : normPosBody a st with ⟨oa, st1⟩
  rw [h1] at hsp1; dsimp only
  obtain ⟨hv1, _, hpos1⟩ := hsp1
  cases oa with
  | none => exact markNonHorn_valid hv1
  | some ca =>
    dsimp only
    obtain ⟨hlta, heqa⟩ := hpos1 ca rfl
    refine (normHornHead_spec b ca hv1 hlta ?_).1
    intro x hx
    rw [exprOf_of_getElem? heqa] at hx
    exact hsub x hx

private def addDisjointPair (a b : ClassExpr) (st : ExtState) : ExtState :=
  let (oa, st1) := normPosBody a st
  let (ob, st2) := normPosBody b st1
  match oa, ob with
  | some ca, some cb => emitAxiom (.sub #[ca, cb] 1) st2
  | _, _ => markNonHorn st2

private theorem addDisjointPair_valid {dm : DatatypeMap} {i : Interpretation dm}
    {a b : ClassExpr} {st : ExtState} (hv : st.Valid i)
    (hdisj : ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) :
    (addDisjointPair a b st).Valid i := by
  unfold addDisjointPair
  have hsp1 := normPosBody_spec a hv
  rcases h1 : normPosBody a st with ⟨oa, st1⟩
  rw [h1] at hsp1; dsimp only
  obtain ⟨hv1, _, hpos1⟩ := hsp1
  have hsp2 := normPosBody_spec b hv1
  rcases h2 : normPosBody b st1 with ⟨ob, st2⟩
  rw [h2] at hsp2; dsimp only
  obtain ⟨hv2, hext2, hpos2⟩ := hsp2
  cases oa with
  | none => exact markNonHorn_valid hv2
  | some ca =>
    cases ob with
    | none => exact markNonHorn_valid hv2
    | some cb =>
      dsimp only
      obtain ⟨hlta, heqa⟩ := hpos1 ca rfl
      obtain ⟨hltb, heqb⟩ := hpos2 cb rfl
      have hlta2 : ca < st2.table.classes.size := Nat.lt_of_lt_of_le hlta hext2.1
      have heqa2 : st2.table.classes[ca]? = some a := by rw [hext2.2.2.1 ca hlta, heqa]
      apply emitAxiom_valid hv2
      · refine ⟨fun c hc => ?_, wf_one_lt hv2.1⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> assumption
      · intro x hpre
        have h1' := hpre ca (by simp)
        have h2' := hpre cb (by simp)
        rw [exprOf_of_getElem? heqa2] at h1'
        rw [exprOf_of_getElem? heqb] at h2'
        exact absurd ⟨h1', h2'⟩ (hdisj x)

private def addDisjointList : List ClassExpr → ExtState → ExtState
  | [], st => st
  | a :: rest, st =>
    let st1 := rest.foldl (fun acc b => addDisjointPair a b acc) st
    addDisjointList rest st1

private theorem addDisjointList_valid {dm : DatatypeMap} {i : Interpretation dm} :
    ∀ {cs : List ClassExpr} {st : ExtState}, st.Valid i →
      cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) →
      (addDisjointList cs st).Valid i
  | [], _, hv, _ => hv
  | a :: rest, st, hv, hpw => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    have hfold : ∀ (bs : List ClassExpr) (s : ExtState), s.Valid i →
        (∀ b ∈ bs, ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) →
        (bs.foldl (fun acc b => addDisjointPair a b acc) s).Valid i := by
      intro bs
      induction bs with
      | nil => intro s hs _; exact hs
      | cons b bs' ih =>
        intro s hs hdisj
        exact ih _ (addDisjointPair_valid hs (hdisj b (List.mem_cons_self ..)))
          (fun b' hb' => hdisj b' (List.mem_cons_of_mem _ hb'))
    exact addDisjointList_valid (cs := rest) (st := rest.foldl (fun acc b => addDisjointPair a b acc) st)
      (hfold rest st hv hhead) htail

private def addRoleSubWithInv (r s : Nat) (st : ExtState) : ExtState :=
  let st1 := emitAxiom (.roleSub r s) st
  emitAxiom (.roleSub (invRole r) (invRole s)) st1

private theorem addRoleSubWithInv_valid {dm : DatatypeMap} {i : Interpretation dm}
    {r s : Nat} {st : ExtState} (hv : st.Valid i)
    (hr : r < st.table.roles.size) (hs : s < st.table.roles.size)
    (hsub : ∀ x y, rolePath i (st.table.roleOf r) x y → rolePath i (st.table.roleOf s) x y) :
    (addRoleSubWithInv r s st).Valid i := by
  have hv1 : (emitAxiom (.roleSub r s) st).Valid i :=
    emitAxiom_valid hv ⟨hr, hs⟩ hsub
  apply emitAxiom_valid hv1
  · exact ⟨invRole_lt hv.1 hr, invRole_lt hv.1 hs⟩
  · intro x y hxy
    have h1 := (CBTable.roleOf_invRole hv.1 i r x y).mp hxy
    exact (CBTable.roleOf_invRole hv.1 i s x y).mpr (hsub y x h1)

private def addRoleChainWithInv (r1 r2 s : Nat) (st : ExtState) : ExtState :=
  let st1 := emitAxiom (.roleChain r1 r2 s) st
  emitAxiom (.roleChain (invRole r2) (invRole r1) (invRole s)) st1

private theorem addRoleChainWithInv_valid {dm : DatatypeMap} {i : Interpretation dm}
    {r1 r2 s : Nat} {st : ExtState} (hv : st.Valid i)
    (h1 : r1 < st.table.roles.size) (h2 : r2 < st.table.roles.size) (hs : s < st.table.roles.size)
    (hch : ∀ x y z, rolePath i (st.table.roleOf r1) x y → rolePath i (st.table.roleOf r2) y z →
      rolePath i (st.table.roleOf s) x z) :
    (addRoleChainWithInv r1 r2 s st).Valid i := by
  have hv1 : (emitAxiom (.roleChain r1 r2 s) st).Valid i :=
    emitAxiom_valid hv ⟨h1, h2, hs⟩ hch
  apply emitAxiom_valid hv1
  · exact ⟨invRole_lt hv.1 h2, invRole_lt hv.1 h1, invRole_lt hv.1 hs⟩
  · intro x y z hxy hyz
    have hxy' := (CBTable.roleOf_invRole hv.1 i r2 x y).mp hxy
    have hyz' := (CBTable.roleOf_invRole hv.1 i r1 y z).mp hyz
    exact (CBTable.roleOf_invRole hv.1 i s x z).mpr (hch z y x hyz' hxy')

/-- Binarize an arbitrary role chain `p0 ++ rest` into binary `roleChain` steps, returning the
    interned `RoleId` representing the full path `p0 ++ rest`. -/
private def binarizeChain (curId : Nat) (curPath : List ObjectProperty) :
    List ObjectProperty → ExtState → Nat × ExtState
  | [], st => (curId, st)
  | r :: rest, st =>
    let (rid, st1) := internRole r st
    let nextPath := curPath ++ [r]
    let (nextId, st2) := internRolePath nextPath st1
    let st3 := addRoleChainWithInv curId rid nextId st2
    binarizeChain nextId nextPath rest st3

private theorem binarizeChain_spec {dm : DatatypeMap} {i : Interpretation dm} :
    ∀ (rest : List ObjectProperty) (curId : Nat) (curPath : List ObjectProperty) {st : ExtState},
      st.Valid i →
      curId < st.table.roles.size →
      st.table.roles[curId]? = some curPath →
      let res := binarizeChain curId curPath rest st
      res.2.Valid i ∧ st.table.Extends res.2.table ∧
      res.1 < res.2.table.roles.size ∧ res.2.table.roles[res.1]? = some (curPath ++ rest)
  | [], curId, curPath, st, hv, hlt, heq => by
    simp only [binarizeChain, List.append_nil]
    exact ⟨hv, CBTable.Extends.refl _, hlt, heq⟩
  | r :: rest, curId, curPath, st, hv, hlt, heq => by
    unfold binarizeChain
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, hext1, hltr, heqr⟩ := hsp1
    have hsp2 := internRolePath_spec (curPath ++ [r]) hv1
    rcases h2 : internRolePath (curPath ++ [r]) st1 with ⟨nextId, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltn, heqn⟩ := hsp2
    have hext12 := hext1.trans hext2
    have hcur2 : curId < st2.table.roles.size := Nat.lt_of_lt_of_le hlt hext12.2.1
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have hcurEq2 : st2.table.roles[curId]? = some curPath := by rw [hext12.2.2.2 curId hlt, heq]
    have hrEq2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (addRoleChainWithInv curId rid nextId st2).Valid i := by
      apply addRoleChainWithInv_valid hv2 hcur2 hltr2 hltn
      intro x y z h1' h2'
      rw [roleOf_of_getElem? hcurEq2] at h1'
      rw [roleOf_of_getElem? hrEq2] at h2'
      rw [roleOf_of_getElem? heqn, rolePath_append]
      exact ⟨y, h1', h2'⟩
    have hsp4 := binarizeChain_spec rest nextId (curPath ++ [r]) hv3 hltn heqn
    have hpath : curPath ++ [r] ++ rest = curPath ++ (r :: rest) := by simp
    rw [hpath] at hsp4
    exact ⟨hsp4.1, hext12.trans hsp4.2.1, hsp4.2.2⟩

private def addEquivClassesCycle (cs : List ClassExpr) (st : ExtState) : ExtState :=
  match cs with
  | [] | [_] => st
  | c0 :: rest =>
    let rec go (prev : ClassExpr) : List ClassExpr → ExtState → ExtState
      | [], s => addSubClass prev c0 s
      | nxt :: tl, s => go nxt tl (addSubClass prev nxt s)
    go c0 rest st

private theorem addEquivClassesCycle_valid {dm : DatatypeMap} {i : Interpretation dm}
    {cs : List ClassExpr} {st : ExtState} (hv : st.Valid i)
    (heq : ∀ a ∈ cs, ∀ b ∈ cs, ∀ x, classHolds i x a ↔ classHolds i x b) :
    (addEquivClassesCycle cs st).Valid i := by
  cases cs with
  | nil => exact hv
  | cons c0 rest =>
    cases rest with
    | nil => exact hv
    | cons c1 tl =>
      unfold addEquivClassesCycle
      have hgo : ∀ (ls : List ClassExpr) (prev : ClassExpr) (s : ExtState),
          s.Valid i → prev ∈ c0 :: c1 :: tl → (∀ c ∈ ls, c ∈ c0 :: c1 :: tl) →
          (addEquivClassesCycle.go c0 prev ls s).Valid i := by
        intro ls
        induction ls with
        | nil =>
          intro prev s hs hprev _
          exact addSubClass_valid hs (fun x hx => (heq prev hprev c0 (List.mem_cons_self ..) x).mp hx)
        | cons nxt ls' ih =>
          intro prev s hs hprev hls
          have hnxt : nxt ∈ c0 :: c1 :: tl := hls nxt (List.mem_cons_self ..)
          have hs' := addSubClass_valid hs (fun x hx => (heq prev hprev nxt hnxt x).mp hx)
          exact ih nxt (addSubClass prev nxt s) hs' hnxt (fun c hc => hls c (List.mem_cons_of_mem _ hc))
      exact hgo (c1 :: tl) c0 st hv (List.mem_cons_self ..) (fun c hc => List.mem_cons_of_mem _ hc)

private def addRolePair (p q : ObjectProperty) (st : ExtState) : ExtState :=
  let (pId, s1) := internRole p st
  let (qId, s2) := internRole q s1
  addRoleSubWithInv pId qId s2

private theorem addRolePair_valid {dm : DatatypeMap} {i : Interpretation dm}
    {p q : ObjectProperty} {st : ExtState} (hv : st.Valid i)
    (hpq : ∀ x y, objectHolds i p x y → objectHolds i q x y) :
    (addRolePair p q st).Valid i := by
  unfold addRolePair
  have hsp1 := internRole_spec p hv
  rcases h1 : internRole p st with ⟨pId, s1⟩
  rw [h1] at hsp1; dsimp only
  obtain ⟨hv1, _, hlt1, heq1⟩ := hsp1
  have hsp2 := internRole_spec q hv1
  rcases h2 : internRole q s1 with ⟨qId, s2⟩
  rw [h2] at hsp2; dsimp only
  obtain ⟨hv2, hext2, hlt2, heq2⟩ := hsp2
  have hlt12 : pId < s2.table.roles.size := Nat.lt_of_lt_of_le hlt1 hext2.2.1
  have heq12 : s2.table.roles[pId]? = some [p] := by rw [hext2.2.2.2 pId hlt1, heq1]
  apply addRoleSubWithInv_valid hv2 hlt12 hlt2
  intro x y hxy
  rw [roleOf_of_getElem? heq12, rolePath_singleton] at hxy
  rw [roleOf_of_getElem? heq2, rolePath_singleton]
  exact hpq x y hxy

private def addEquivRolesCycle (rs : List ObjectProperty) (st : ExtState) : ExtState :=
  match rs with
  | [] | [_] => st
  | r0 :: rest =>
    let rec go (prev : ObjectProperty) : List ObjectProperty → ExtState → ExtState
      | [], s => addRolePair prev r0 s
      | nxt :: tl, s => go nxt tl (addRolePair prev nxt s)
    go r0 rest st

private theorem addEquivRolesCycle_valid {dm : DatatypeMap} {i : Interpretation dm}
    {rs : List ObjectProperty} {st : ExtState} (hv : st.Valid i)
    (heq : ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, objectHolds i r x y ↔ objectHolds i s x y) :
    (addEquivRolesCycle rs st).Valid i := by
  cases rs with
  | nil => exact hv
  | cons r0 rest =>
    cases rest with
    | nil => exact hv
    | cons r1 tl =>
      unfold addEquivRolesCycle
      have hgo : ∀ (ls : List ObjectProperty) (prev : ObjectProperty) (s : ExtState),
          s.Valid i → prev ∈ r0 :: r1 :: tl → (∀ r ∈ ls, r ∈ r0 :: r1 :: tl) →
          (addEquivRolesCycle.go r0 prev ls s).Valid i := by
        intro ls
        induction ls with
        | nil =>
          intro prev s hs hprev _
          exact addRolePair_valid hs (fun x y h => (heq prev hprev r0 (List.mem_cons_self ..) x y).mp h)
        | cons nxt ls' ih =>
          intro prev s hs hprev hls
          have hnxt : nxt ∈ r0 :: r1 :: tl := hls nxt (List.mem_cons_self ..)
          have hs' := addRolePair_valid hs (fun x y h => (heq prev hprev nxt hnxt x y).mp h)
          exact ih nxt (addRolePair prev nxt s) hs' hnxt (fun r hr => hls r (List.mem_cons_of_mem _ hr))
      exact hgo (r1 :: tl) r0 st hv (List.mem_cons_self ..) (fun r hr => List.mem_cons_of_mem _ hr)

/-- Process a single OWL 2 `Axiom` into Horn-$\mathcal{SHIQ}$ normal form. -/
private def extractAxiom (ax : Axiom) (st : ExtState) : ExtState :=
  match ax with
  | .subClassOf a b => addSubClass a b st
  | .equivalentClasses cs => addEquivClassesCycle cs st
  | .disjointClasses cs => addDisjointList cs st
  | .disjointUnion h cs =>
    let st1 := cs.foldl (fun acc c => addSubClass c (.named h) acc) st
    let st2 := addDisjointList cs st1
    match cs with
    | [] => addSubClass (.named h) (.named nothing) st2
    | [c] => addSubClass (.named h) c st2
    | _ :: _ :: _ => markNonHorn st2
  | .subObjectProperty r s => addRolePair r s st
  | .equivalentObjectProperties rs => addEquivRolesCycle rs st
  | .inverseObjectProperties r s =>
    let (rid, st1) := internRole r st
    let (sid, st2) := internRole s st1
    let st3 := addRoleSubWithInv rid (invRole sid) st2
    addRoleSubWithInv sid (invRole rid) st3
  | .symmetricObjectProperty r =>
    let (rid, st1) := internRole r st
    addRoleSubWithInv rid (invRole rid) st1
  | .transitiveObjectProperty r =>
    let (rid, st1) := internRole r st
    addRoleChainWithInv rid rid rid st1
  | .subObjectPropertyChain rs s =>
    match rs with
    | [] =>
      let (sid, st1) := internRole s st
      let st2 := emitAxiom (.roleRefl sid) st1
      emitAxiom (.roleRefl (invRole sid)) st2
    | [r] => addRolePair r s st
    | r0 :: rest =>
      let (r0Id, st1) := internRole r0 st
      let (fullId, st2) := binarizeChain r0Id [r0] rest st1
      let (sid, st3) := internRole s st2
      addRoleSubWithInv fullId sid st3
  | .reflexiveObjectProperty r =>
    let (rid, st1) := internRole r st
    let st2 := emitAxiom (.roleRefl rid) st1
    emitAxiom (.roleRefl (invRole rid)) st2
  | .objectPropertyDomain r dom =>
    let (rid, st1) := internRole r st
    let (domLhs, st2) := internExpr (.objectSome r (.named thing)) st1
    let st3 := emitAxiom (.existL rid 0 domLhs) st2
    normHornHead domLhs dom st3
  | .objectPropertyRange r rng =>
    let (rid, st1) := internRole r st
    let (rngId, st2) := internExpr rng st1
    let st3 := emitAxiom (.allR 0 rid rngId) st2
    let st4 := normHornHead rngId rng st3
    let (rngLhs, st5) := internExpr (.objectSome r.converse (.named thing)) st4
    let st6 := emitAxiom (.existL (invRole rid) 0 rngLhs) st5
    normHornHead rngLhs rng st6
  | .functionalObjectProperty r =>
    let (rid, st1) := internRole r st
    emitAxiom (.maxOne 0 rid 0) st1
  | .inverseFunctionalObjectProperty r =>
    let (rid, st1) := internRole r st
    emitAxiom (.maxOne 0 (invRole rid) 0) st1
  | _ => markNonHorn st

private theorem extractAxiom_valid {dm : DatatypeMap} {i : Interpretation dm}
    {ax : Axiom} {st : ExtState} (hv : st.Valid i) (hax : axiomHolds i ax) :
    (extractAxiom ax st).Valid i := by
  cases ax with
  | subClassOf a b => exact addSubClass_valid hv hax
  | equivalentClasses cs => exact addEquivClassesCycle_valid hv hax
  | disjointClasses cs => exact addDisjointList_valid hv hax
  | disjointUnion h cs =>
    obtain ⟨hequiv, hpw⟩ := hax
    have hfold : ∀ (ls : List ClassExpr) (s : ExtState), s.Valid i →
        (∀ c ∈ ls, ∀ x, classHolds i x c → classHolds i x (.named h)) →
        (ls.foldl (fun acc c => addSubClass c (.named h) acc) s).Valid i := by
      intro ls
      induction ls with
      | nil => intro s hs _; exact hs
      | cons c ls' ih =>
        intro s hs hsub
        exact ih _ (addSubClass_valid hs (hsub c (List.mem_cons_self ..)))
          (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc'))
    have hv1 := hfold cs st hv (fun c hc x hcx => (hequiv x).mpr ⟨c, hc, hcx⟩)
    have hv2 := addDisjointList_valid hv1 hpw
    unfold extractAxiom
    cases cs with
    | nil =>
      exact addSubClass_valid hv2 (fun x hx => by
        obtain ⟨_, hmem, _⟩ := (hequiv x).mp hx; cases hmem)
    | cons c rest =>
      cases rest with
      | nil =>
        exact addSubClass_valid hv2 (fun x hx => by
          obtain ⟨c', hmem, hc'⟩ := (hequiv x).mp hx
          have := List.mem_singleton.mp hmem; subst this; exact hc')
      | cons _ _ => exact markNonHorn_valid hv2
  | subObjectProperty r s => exact addRolePair_valid hv hax
  | equivalentObjectProperties rs => exact addEquivRolesCycle_valid hv hax
  | inverseObjectProperties r s =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    have hsp2 := internRole_spec s hv1
    rcases h2 : internRole s st1 with ⟨sid, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hlts, heqs⟩ := hsp2
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (addRoleSubWithInv rid (invRole sid) st2).Valid i := by
      apply addRoleSubWithInv_valid hv2 hltr2 (invRole_lt hv2.1 hlts)
      intro x y hxy
      rw [roleOf_of_getElem? heqr2, rolePath_singleton] at hxy
      rw [CBTable.roleOf_invRole hv2.1 i sid x y, roleOf_of_getElem? heqs, rolePath_singleton]
      exact (hax x y).mp hxy
    apply addRoleSubWithInv_valid hv3 hlts (invRole_lt hv2.1 hltr2)
    intro x y hxy
    simp only [addRoleSubWithInv, emitAxiom] at hxy ⊢
    rw [roleOf_of_getElem? heqs, rolePath_singleton] at hxy
    rw [CBTable.roleOf_invRole hv2.1 i rid x y, roleOf_of_getElem? heqr2, rolePath_singleton]
    exact (hax y x).mpr hxy
  | symmetricObjectProperty r =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    apply addRoleSubWithInv_valid hv1 hltr (invRole_lt hv1.1 hltr)
    intro x y hxy
    rw [roleOf_of_getElem? heqr, rolePath_singleton] at hxy
    rw [CBTable.roleOf_invRole hv1.1 i rid x y, roleOf_of_getElem? heqr, rolePath_singleton]
    exact hax x y hxy
  | transitiveObjectProperty r =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    apply addRoleChainWithInv_valid hv1 hltr hltr hltr
    intro x y z h1' h2'
    rw [roleOf_of_getElem? heqr, rolePath_singleton] at h1' h2' ⊢
    exact hax x y z h1' h2'
  | subObjectPropertyChain rs s =>
    simp only [extractAxiom]
    cases rs with
    | nil =>
      dsimp only
      have hsp1 := internRole_spec s hv
      rcases h1 : internRole s st with ⟨sid, st1⟩
      rw [h1] at hsp1; dsimp only
      obtain ⟨hv1, _, hlts, heqs⟩ := hsp1
      have hv2 : (emitAxiom (.roleRefl sid) st1).Valid i := by
        apply emitAxiom_valid hv1
        · exact hlts
        · intro x
          rw [roleOf_of_getElem? heqs, rolePath_singleton]
          exact hax x x rfl
      apply emitAxiom_valid hv2
      · exact invRole_lt hv1.1 hlts
      · intro x
        simp only [emitAxiom]
        rw [CBTable.roleOf_invRole hv1.1 i sid x x, roleOf_of_getElem? heqs, rolePath_singleton]
        exact hax x x rfl
    | cons r0 rest =>
      cases rest with
      | nil =>
        exact addRolePair_valid hv (fun x y hxy => hax x y ((rolePath_singleton i r0 x y).mpr hxy))
      | cons r1 tl =>
        dsimp only
        have hsp1 := internRole_spec r0 hv
        rcases h1 : internRole r0 st with ⟨r0Id, st1⟩
        rw [h1] at hsp1; dsimp only
        obtain ⟨hv1, _, hltr0, heqr0⟩ := hsp1
        have hsp2 := binarizeChain_spec (r1 :: tl) r0Id [r0] hv1 hltr0 heqr0
        rcases h2 : binarizeChain r0Id [r0] (r1 :: tl) st1 with ⟨fullId, st2⟩
        rw [h2] at hsp2; dsimp only
        obtain ⟨hv2, _, hltf, heqf⟩ := hsp2
        have hsp3 := internRole_spec s hv2
        rcases h3 : internRole s st2 with ⟨sid, st3⟩
        rw [h3] at hsp3; dsimp only
        obtain ⟨hv3, hext3, hlts, heqs⟩ := hsp3
        have hltf3 : fullId < st3.table.roles.size := Nat.lt_of_lt_of_le hltf hext3.2.1
        have heqf3 : st3.table.roles[fullId]? = some (r0 :: r1 :: tl) := by
          rw [hext3.2.2.2 fullId hltf, heqf]; rfl
        apply addRoleSubWithInv_valid hv3 hltf3 hlts
        intro x y hxy
        rw [roleOf_of_getElem? heqf3] at hxy
        rw [roleOf_of_getElem? heqs, rolePath_singleton]
        exact hax x y hxy
  | reflexiveObjectProperty r =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    have hv2 : (emitAxiom (.roleRefl rid) st1).Valid i := by
      apply emitAxiom_valid hv1
      · exact hltr
      · intro x
        rw [roleOf_of_getElem? heqr, rolePath_singleton]
        exact hax x
    apply emitAxiom_valid hv2
    · exact invRole_lt hv1.1 hltr
    · intro x
      simp only [emitAxiom]
      rw [CBTable.roleOf_invRole hv1.1 i rid x x, roleOf_of_getElem? heqr, rolePath_singleton]
      exact hax x
  | objectPropertyDomain r dom =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec (.objectSome r (.named thing)) hv1
    rcases h2 : internExpr (.objectSome r (.named thing)) st1 with ⟨domLhs, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltd, heqd⟩ := hsp2
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.existL rid 0 domLhs) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨hltr2, wf_zero_lt hv2.1, hltd⟩
      · intro x y hry _
        rw [roleOf_of_getElem? heqr2, rolePath_singleton] at hry
        rw [exprOf_of_getElem? heqd]
        exact ⟨y, hry, i.thingExt y⟩
    refine (normHornHead_spec dom domLhs hv3 hltd ?_).1
    intro x hx
    simp only [emitAxiom, exprOf_of_getElem? heqd] at hx
    obtain ⟨y, hry, _⟩ := hx
    exact hax x y hry
  | objectPropertyRange r rng =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    have hsp2 := internExpr_spec rng hv1
    rcases h2 : internExpr rng st1 with ⟨rngId, st2⟩
    rw [h2] at hsp2; dsimp only
    obtain ⟨hv2, hext2, hltrng, heqrng⟩ := hsp2
    have hltr2 : rid < st2.table.roles.size := Nat.lt_of_lt_of_le hltr hext2.2.1
    have heqr2 : st2.table.roles[rid]? = some [r] := by rw [hext2.2.2.2 rid hltr, heqr]
    have hv3 : (emitAxiom (.allR 0 rid rngId) st2).Valid i := by
      apply emitAxiom_valid hv2
      · exact ⟨wf_zero_lt hv2.1, hltr2, hltrng⟩
      · intro x _ y hry
        rw [roleOf_of_getElem? heqr2, rolePath_singleton] at hry
        rw [exprOf_of_getElem? heqrng]
        exact hax x y hry
    obtain ⟨hv4, hext4⟩ := normHornHead_spec rng rngId hv3 hltrng (fun x hx => by
      simpa [emitAxiom, exprOf_of_getElem? heqrng] using hx)
    have hsp5 := internExpr_spec (.objectSome r.converse (.named thing)) hv4
    rcases h5 : internExpr (.objectSome r.converse (.named thing))
        (normHornHead rngId rng (emitAxiom (.allR 0 rid rngId) st2)) with ⟨rngLhs, st5⟩
    rw [h5] at hsp5; dsimp only
    obtain ⟨hv5, hext5, hltl, heql⟩ := hsp5
    have hext25 := hext4.trans hext5
    have hltr5 : rid < st5.table.roles.size := Nat.lt_of_lt_of_le hltr2 hext25.2.1
    have heqr5 : st5.table.roles[rid]? = some [r] := by rw [hext25.2.2.2 rid hltr2]; exact heqr2
    have hv6 : (emitAxiom (.existL (invRole rid) 0 rngLhs) st5).Valid i := by
      apply emitAxiom_valid hv5
      · exact ⟨invRole_lt hv5.1 hltr5, wf_zero_lt hv5.1, hltl⟩
      · intro x y hry _
        rw [CBTable.roleOf_invRole hv5.1 i rid x y, roleOf_of_getElem? heqr5,
          rolePath_singleton] at hry
        rw [exprOf_of_getElem? heql]
        exact ⟨y, (objectHolds_converse i r x y).mpr hry, i.thingExt y⟩
    refine (normHornHead_spec rng rngLhs hv6 hltl ?_).1
    intro x hx
    simp only [emitAxiom, exprOf_of_getElem? heql] at hx
    obtain ⟨y, hry, _⟩ := hx
    exact hax y x ((objectHolds_converse i r x y).mp hry)
  | functionalObjectProperty r =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    apply emitAxiom_valid hv1
    · exact ⟨wf_zero_lt hv1.1, hltr, wf_zero_lt hv1.1⟩
    · intro x _ y z hry _ hrz _
      rw [roleOf_of_getElem? heqr, rolePath_singleton] at hry hrz
      exact hax x y z hry hrz
  | inverseFunctionalObjectProperty r =>
    simp only [extractAxiom]
    have hsp1 := internRole_spec r hv
    rcases h1 : internRole r st with ⟨rid, st1⟩
    rw [h1] at hsp1; dsimp only
    obtain ⟨hv1, _, hltr, heqr⟩ := hsp1
    apply emitAxiom_valid hv1
    · exact ⟨wf_zero_lt hv1.1, invRole_lt hv1.1 hltr, wf_zero_lt hv1.1⟩
    · intro x _ y z hry _ hrz _
      rw [CBTable.roleOf_invRole hv1.1 i rid x y, roleOf_of_getElem? heqr, rolePath_singleton] at hry
      rw [CBTable.roleOf_invRole hv1.1 i rid x z, roleOf_of_getElem? heqr, rolePath_singleton] at hrz
      exact hax x y z hry hrz
  | _ => exact markNonHorn_valid hv

private def extractAxioms : List Axiom → ExtState → ExtState
  | [], st => st
  | ax :: rest, st => extractAxioms rest (extractAxiom ax st)

private theorem extractAxioms_valid {dm : DatatypeMap} {i : Interpretation dm} :
    ∀ {o : Ontology} {st : ExtState}, st.Valid i → satisfies i o →
      (extractAxioms o st).Valid i
  | [], _, hv, _ => hv
  | ax :: rest, st, hv, hsat =>
    extractAxioms_valid (o := rest) (st := extractAxiom ax st)
      (extractAxiom_valid hv (hsat ax (List.mem_cons_self ..)))
      (fun a ha => hsat a (List.mem_cons_of_mem _ ha))

/-- Extract the integer-interned Horn-$\mathcal{SHIQ}$ normal-form representation of `o`. -/
def extractHornSHIQ (o : Ontology) : NormResult :=
  let st := extractAxioms o ExtState.empty
  { table := st.table
    axioms := st.axioms
    namedClassIds := st.namedClassIds
    isPureHornSHIQ := st.isPureHornSHIQ }

/-- Soundness of Horn-$\mathcal{SHIQ}$ extraction:
    1. The output `CBTable` is well-formed (`0 = Thing`, `1 = Nothing`, converse-paired roles).
    2. Every extracted `HornAxiom` holds in every model of `o`.
    3. Every `(iri, id)` in `namedClassIds` maps to `ClassExpr.named iri`. -/
theorem extractHornSHIQ_sound {dm : DatatypeMap} {o : Ontology} {i : Interpretation dm}
    (hsat : satisfies i o) :
    let res := extractHornSHIQ o
    res.table.WF ∧
    (∀ ax ∈ res.axioms.toList, ax.holds res.table i) ∧
    (∀ p ∈ res.namedClassIds.toList, res.table.exprOf p.2 = .named p.1) := by
  have hv := extractAxioms_valid (ExtState.valid_empty i) hsat
  refine ⟨hv.1, fun ax hax => (hv.2.1 ax hax).2, fun p hp => exprOf_of_getElem? (hv.2.2 p hp).2⟩

end Sabrina.OWL2.FastCB
