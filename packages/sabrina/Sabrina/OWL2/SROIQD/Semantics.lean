import Sabrina.OWL2.DataRanges
import Sabrina.RoleChains.SimpleRoles

/-! Unified SROIQ(D) syntax, OWL 2 Direct Semantics interpretation, and
    global simple-role validation over the full 33-datatype map. -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole RoleTheory roleClosure)
open Sabrina.RoleChains (Chain)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)

def orientedToObjProp (r : OrientedRole) : ObjectProperty :=
  if r.2 then .inverse r.1 else .named r.1

def holdsOriented {dm : DatatypeMap} (i : Interpretation dm)
    (r : OrientedRole) (x y : i.Object) : Prop :=
  if r.2 then i.objectProperties r.1 y x else i.objectProperties r.1 x y

theorem objectHolds_oriented {dm : DatatypeMap} (i : Interpretation dm)
    (r : OrientedRole) (x y : i.Object) :
    objectHolds i (orientedToObjProp r) x y ↔ holdsOriented i r x y := by
  rcases r with ⟨r, _ | _⟩ <;> rfl

inductive Concept where
  | top | bottom
  | lit (name : IRI) (positive : Bool)
  | nom (ind : Individual) (positive : Bool)
  | self (role : OrientedRole) (positive : Bool)
  | conj (left right : Concept)
  | disj (left right : Concept)
  | some (role : OrientedRole) (filler : Concept)
  | all (role : OrientedRole) (filler : Concept)
  | min (count : Nat) (role : OrientedRole) (filler : Concept)
  | max (count : Nat) (role : OrientedRole) (filler : Concept)
  | dataSome (role : IRI) (range : DataRange)
  | dataAll (role : IRI) (range : DataRange)
  | dataValue (role : IRI) (lit : Literal) (positive : Bool)
  | dataMin (count : Nat) (role : IRI) (range : DataRange)
  | dataMax (count : Nat) (role : IRI) (range : DataRange)
  deriving DecidableEq, Repr

abbrev Concept.atom (name : IRI) : Concept := .lit name true

def Concept.oneOf (individuals : List Individual) : Concept :=
  individuals.foldr (fun a acc => .disj (.nom a true) acc) .bottom

def Concept.hasValue (role : OrientedRole) (individual : Individual) : Concept :=
  .some role (.nom individual true)

def Concept.exact (n : Nat) (r : OrientedRole) (c : Concept) : Concept :=
  .conj (.min n r c) (.max n r c)

def Concept.dataExact (n : Nat) (r : IRI) (d : DataRange) : Concept :=
  .conj (.dataMin n r d) (.dataMax n r d)

def Concept.dual : Concept → Concept
  | .top => .bottom
  | .bottom => .top
  | .lit p b => .lit p (!b)
  | .nom a b => .nom a (!b)
  | .self r b => .self r (!b)
  | .conj a b => .disj a.dual b.dual
  | .disj a b => .conj a.dual b.dual
  | .some r c => .all r c.dual
  | .all r c => .some r c.dual
  | .min 0 r c => .conj .bottom (.min 0 r c)
  | .min (n + 1) r c => .max n r c
  | .max n r c => .min (n + 1) r c
  | .dataSome r d => .dataAll r (.complement d)
  | .dataAll r d => .dataSome r (.complement d)
  | .dataValue r l b => .dataValue r l (!b)
  | .dataMin 0 r d => .conj .bottom (.dataMin 0 r d)
  | .dataMin (n + 1) r d => .dataMax n r d
  | .dataMax n r d => .dataMin (n + 1) r d

def Concept.toClassExpr : Concept → ClassExpr
  | .top => .named thing
  | .bottom => .named nothing
  | .lit s true => .named s
  | .lit s false => .complement (.named s)
  | .nom a true => .oneOf [a]
  | .nom a false => .complement (.oneOf [a])
  | .self r true => .objectSelf (orientedToObjProp r)
  | .self r false => .complement (.objectSelf (orientedToObjProp r))
  | .conj a b => .intersection a.toClassExpr b.toClassExpr
  | .disj a b => .union a.toClassExpr b.toClassExpr
  | .some r c => .objectSome (orientedToObjProp r) c.toClassExpr
  | .all r c => .objectAll (orientedToObjProp r) c.toClassExpr
  | .min n r c => .objectMin n (orientedToObjProp r) c.toClassExpr
  | .max n r c => .objectMax n (orientedToObjProp r) c.toClassExpr
  | .dataSome r d => .dataSome r d
  | .dataAll r d => .dataAll r d
  | .dataValue r l true => .dataValue r l
  | .dataValue r l false => .complement (.dataValue r l)
  | .dataMin n r d => .dataMin n r d
  | .dataMax n r d => .dataMax n r d

def holds {dm : DatatypeMap} (i : Interpretation dm) (x : i.Object) : Concept → Prop
  | .top => True
  | .bottom => False
  | .lit p true => i.classes p x
  | .lit p false => ¬ i.classes p x
  | .nom a true => x = i.individuals a
  | .nom a false => x ≠ i.individuals a
  | .self r true => holdsOriented i r x x
  | .self r false => ¬ holdsOriented i r x x
  | .conj a b => holds i x a ∧ holds i x b
  | .disj a b => holds i x a ∨ holds i x b
  | .some r c => ∃ y, holdsOriented i r x y ∧ holds i y c
  | .all r c => ∀ y, holdsOriented i r x y → holds i y c
  | .min n r c => AtLeast n (fun y => holdsOriented i r x y ∧ holds i y c)
  | .max n r c => ¬ AtLeast (n + 1) (fun y => holdsOriented i r x y ∧ holds i y c)
  | .dataSome r d => ∃ y, i.dataProperties r x y ∧ dataHolds i y d
  | .dataAll r d => ∀ y, i.dataProperties r x y → dataHolds i y d
  | .dataValue r l true => i.dataProperties r x (i.literalValue l)
  | .dataValue r l false => ¬ i.dataProperties r x (i.literalValue l)
  | .dataMin n r d => AtLeast n (fun y => i.dataProperties r x y ∧ dataHolds i y d)
  | .dataMax n r d => ¬ AtLeast (n + 1) (fun y => i.dataProperties r x y ∧ dataHolds i y d)

theorem toClassExpr_iff {dm : DatatypeMap} (i : Interpretation dm) (x : i.Object) (c : Concept) :
    classHolds i x c.toClassExpr ↔ holds i x c := by
  induction c generalizing x with
  | top => exact ⟨fun _ => trivial, fun _ => i.thingExt x⟩
  | bottom => exact ⟨i.nothingExt x, False.elim⟩
  | lit s bit => cases bit <;> rfl
  | nom a bit => cases bit <;> simp [Concept.toClassExpr, classHolds, holds, eq_comm] <;> exact Iff.rfl
  | self r bit => cases bit <;> simp [Concept.toClassExpr, classHolds, holds, objectHolds_oriented]
  | conj a b ha hb => simp only [Concept.toClassExpr, classHolds, holds, ha, hb]
  | disj a b ha hb => simp only [Concept.toClassExpr, classHolds, holds, ha, hb]
  | some r c ih => simp only [Concept.toClassExpr, classHolds, objectHolds_oriented, holds, ih]
  | all r c ih => simp only [Concept.toClassExpr, classHolds, objectHolds_oriented, holds, ih]
  | min n r c ih => simp only [Concept.toClassExpr, classHolds, objectHolds_oriented, holds, AtLeast, ih]
  | max n r c ih => simp only [Concept.toClassExpr, classHolds, objectHolds_oriented, holds, AtLeast, ih]
  | dataSome r d => rfl
  | dataAll r d => rfl
  | dataValue r l bit => cases bit <;> rfl
  | dataMin n r d => rfl
  | dataMax n r d => rfl

theorem holds_dual (i : Interpretation dm) (x : i.Object) (c : Concept) :
    holds i x c.dual ↔ ¬ holds i x c := by
  classical
  induction c generalizing x with
  | top | bottom => simp [Concept.dual, holds]
  | lit p sign => cases sign <;> simp [Concept.dual, holds]
  | nom a sign => cases sign <;> simp [Concept.dual, holds]
  | self r sign => cases sign <;> simp [Concept.dual, holds]
  | conj a b ha hb =>
    simp only [Concept.dual, holds, ha, hb]
    exact Classical.not_and_iff_not_or_not.symm
  | disj a b ha hb => simp [Concept.dual, holds, ha, hb]
  | some r c ih => simp [Concept.dual, holds, ih]
  | all r c ih => simp [Concept.dual, holds, ih, Classical.not_imp]
  | min n r c =>
    cases n with
    | zero =>
      have h : AtLeast 0 (fun y => holdsOriented i r x y ∧ holds i y c) :=
        ⟨[], rfl, List.nodup_nil, by simp⟩
      simp [Concept.dual, holds, h]
    | succ n => rfl
  | max n r c => simp [Concept.dual, holds]
  | dataSome r d => simp [Concept.dual, holds, dataHolds]
  | dataAll r d => simp [Concept.dual, holds, dataHolds, Classical.not_imp]
  | dataValue r l sign => cases sign <;> simp [Concept.dual, holds]
  | dataMin n r d =>
    cases n with
    | zero =>
      have h : AtLeast 0 (fun y => i.dataProperties r x y ∧ dataHolds i y d) :=
        ⟨[], rfl, List.nodup_nil, by simp⟩
      simp [Concept.dual, holds, h]
    | succ n => rfl
  | dataMax n r d => simp [Concept.dual, holds]

structure Inclusion where
  sub : Concept
  sup : Concept
  deriving DecidableEq, Repr

structure RoleChars where
  reflexive : List IRI := []
  irreflexive : List IRI := []
  asymmetric : List IRI := []
  disjoint : List (OrientedRole × OrientedRole) := []
  deriving DecidableEq, Repr

structure KeyAxiom where
  cls : Concept
  objProps : List OrientedRole := []
  dataProps : List IRI := []
  deriving DecidableEq, Repr

structure Problem where
  tbox : List Inclusion := []
  rules : RoleTheory := []
  chains : List Chain := []
  chars : RoleChars := {}
  subData : List (IRI × IRI) := []
  disjointData : List (IRI × IRI) := []
  funcData : List IRI := []
  dataRanges : List (IRI × DataRange) := []
  keys : List KeyAxiom := []
  classAssertions : List (Individual × Concept) := []
  objAssertions : List (IRI × Individual × Individual) := []
  negObjAssertions : List (IRI × Individual × Individual) := []
  sameInds : List (Individual × Individual) := []
  diffInds : List (Individual × Individual) := []
  dataAssertions : List (IRI × Individual × Literal) := []
  negDataAssertions : List (IRI × Individual × Literal) := []
  root : Concept := .top
  deriving Repr

def objPath {dm : DatatypeMap} (i : Interpretation dm) : List OrientedRole → i.Object → i.Object → Prop
  | [], x, y => x = y
  | r :: rs, x, y => ∃ z, holdsOriented i r x z ∧ objPath i rs z y

theorem rolePath_objPath {dm : DatatypeMap} (i : Interpretation dm)
    (rs : List OrientedRole) (x y : i.Object) :
    rolePath i (rs.map orientedToObjProp) x y ↔ objPath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih => simp only [List.map_cons, rolePath, objectHolds_oriented, objPath, ih]

private theorem objPath_append (i : Interpretation dm) (u v : List OrientedRole)
    (x y : i.Object) :
    objPath i (u ++ v) x y ↔ ∃ z, objPath i u x z ∧ objPath i v z y := by
  induction u generalizing x with
  | nil => simp [objPath]
  | cons r tail ih =>
    constructor
    · rintro ⟨a, hr, hp⟩
      obtain ⟨z, ht, hv⟩ := (ih a).mp hp
      exact ⟨z, ⟨a, hr, ht⟩, hv⟩
    · rintro ⟨z, ⟨a, hr, ht⟩, hv⟩
      exact ⟨a, hr, (ih a).mpr ⟨z, ht, hv⟩⟩

theorem objPath_flip {i : Interpretation dm} {rs : List OrientedRole}
    {x y : i.Object} (h : objPath i rs x y) :
    objPath i (RoleChains.TransitivePaths.flipWord rs) y x := by
  induction rs generalizing x with
  | nil => exact h.symm
  | cons r rs ih =>
    obtain ⟨z, hr, htail⟩ := h
    simp only [RoleChains.TransitivePaths.flipWord, List.map_cons, List.reverse_cons]
    refine (objPath_append i _ _ _ _).mpr ⟨z, ih htail, x, ?_, rfl⟩
    rcases r with ⟨_, _ | _⟩ <;> exact hr

theorem objPath_flip_iff (i : Interpretation dm) (rs : List OrientedRole)
    (x y : i.Object) :
    objPath i (RoleChains.TransitivePaths.flipWord rs) y x ↔ objPath i rs x y := by
  exact ⟨fun h => by simpa using objPath_flip h, objPath_flip⟩

def Problem.toOntology (p : Problem) : Ontology :=
  p.tbox.map (fun q => .subClassOf q.sub.toClassExpr q.sup.toClassExpr) ++
  p.rules.map (fun (r, s) => .subObjectProperty (orientedToObjProp r) (orientedToObjProp s)) ++
  p.chains.map (fun c => .subObjectPropertyChain (c.body.map orientedToObjProp) (.named c.head)) ++
  p.chars.reflexive.map (fun r => .reflexiveObjectProperty (.named r)) ++
  p.chars.irreflexive.map (fun r => .irreflexiveObjectProperty (.named r)) ++
  p.chars.asymmetric.map (fun r => .asymmetricObjectProperty (.named r)) ++
  p.chars.disjoint.map (fun (r, s) => .disjointObjectProperties [orientedToObjProp r, orientedToObjProp s]) ++
  p.subData.map (fun (r, s) => .subDataProperty r s) ++
  p.disjointData.map (fun (r, s) => .disjointDataProperties [r, s]) ++
  p.funcData.map Axiom.functionalDataProperty ++
  p.dataRanges.map (fun (r, d) => .dataPropertyRange r d) ++
  p.keys.map (fun k => .hasKey k.cls.toClassExpr (k.objProps.map orientedToObjProp) k.dataProps) ++
  p.classAssertions.map (fun (a, c) => .classAssertion c.toClassExpr a) ++
  p.objAssertions.map (fun (r, a, b) => .objectAssertion (.named r) a b) ++
  p.negObjAssertions.map (fun (r, a, b) => .negativeObjectAssertion (.named r) a b) ++
  p.sameInds.map (fun (a, b) => .sameIndividuals [a, b]) ++
  p.diffInds.map (fun (a, b) => .differentIndividuals [a, b]) ++
  p.dataAssertions.map (fun (r, a, l) => .dataAssertion r a l) ++
  p.negDataAssertions.map (fun (r, a, l) => .negativeDataAssertion r a l)

structure Problem.Models {dm : DatatypeMap} (i : Interpretation dm) (p : Problem) : Prop where
  tbox : ∀ q ∈ p.tbox, ∀ x, holds i x q.sub → holds i x q.sup
  rules : ∀ rs ∈ p.rules, ∀ x y, holdsOriented i rs.1 x y → holdsOriented i rs.2 x y
  chains : ∀ c ∈ p.chains, ∀ x y, objPath i c.body x y → i.objectProperties c.head x y
  reflexive : ∀ r ∈ p.chars.reflexive, ∀ x, i.objectProperties r x x
  irreflexive : ∀ r ∈ p.chars.irreflexive, ∀ x, ¬ i.objectProperties r x x
  asymmetric : ∀ r ∈ p.chars.asymmetric, ∀ x y, i.objectProperties r x y → ¬ i.objectProperties r y x
  disjoint : ∀ rs ∈ p.chars.disjoint, ∀ x y, ¬ (holdsOriented i rs.1 x y ∧ holdsOriented i rs.2 x y)
  subData : ∀ rs ∈ p.subData, ∀ x y, i.dataProperties rs.1 x y → i.dataProperties rs.2 x y
  disjointData : ∀ rs ∈ p.disjointData, ∀ x y, ¬ (i.dataProperties rs.1 x y ∧ i.dataProperties rs.2 x y)
  funcData : ∀ r ∈ p.funcData, ∀ x y z, i.dataProperties r x y → i.dataProperties r x z → y = z
  dataRanges : ∀ rd ∈ p.dataRanges, ∀ x y, i.dataProperties rd.1 x y → dataHolds i y rd.2
  keys : ∀ k ∈ p.keys, ∀ x y, holds i x k.cls → holds i y k.cls → i.named x → i.named y →
    (∀ r ∈ k.objProps, ∃ z, i.named z ∧ holdsOriented i r x z ∧ holdsOriented i r y z) →
    (∀ dp ∈ k.dataProps, ∃ z, i.dataProperties dp x z ∧ i.dataProperties dp y z) → x = y
  classAssertions : ∀ ac ∈ p.classAssertions, holds i (i.individuals ac.1) ac.2
  objAssertions : ∀ rab ∈ p.objAssertions,
    i.objectProperties rab.1 (i.individuals rab.2.1) (i.individuals rab.2.2)
  negObjAssertions : ∀ rab ∈ p.negObjAssertions,
    ¬ i.objectProperties rab.1 (i.individuals rab.2.1) (i.individuals rab.2.2)
  sameInds : ∀ ab ∈ p.sameInds, i.individuals ab.1 = i.individuals ab.2
  diffInds : ∀ ab ∈ p.diffInds, i.individuals ab.1 ≠ i.individuals ab.2
  dataAssertions : ∀ ral ∈ p.dataAssertions,
    i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2)
  negDataAssertions : ∀ ral ∈ p.negDataAssertions,
    ¬ i.dataProperties ral.1 (i.individuals ral.2.1) (i.literalValue ral.2.2)

def Problem.SatWith (p : Problem) (dm : DatatypeMap) : Prop :=
  ∃ i : Interpretation dm, p.Models i ∧ ∃ x, holds i x p.root

def Problem.Sat (p : Problem) : Prop :=
  ∃ i : Interpretation datatypeMap, p.Models i ∧ ∃ x, holds i x p.root

private theorem sat_append {dm : DatatypeMap} {i : Interpretation dm} {a b : Ontology} :
    satisfies i (a ++ b) ↔ satisfies i a ∧ satisfies i b :=
  ⟨fun h => ⟨fun ax hx => h ax (List.mem_append_left _ hx),
             fun ax hx => h ax (List.mem_append_right _ hx)⟩,
   fun ⟨ha, hb⟩ ax hx => (List.mem_append.mp hx).elim (ha ax) (hb ax)⟩

private theorem sat_map {α : Type} {dm : DatatypeMap} {i : Interpretation dm}
    {xs : List α} {f : α → Axiom} :
    satisfies i (xs.map f) ↔ ∀ a ∈ xs, axiomHolds i (f a) :=
  ⟨fun h a ha => h _ (List.mem_map_of_mem ha),
   fun h _ hx => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact h a ha⟩

theorem satisfies_toOntology_iff {dm : DatatypeMap} (i : Interpretation dm) (p : Problem) :
    satisfies i p.toOntology ↔ p.Models i := by
  simp only [Problem.toOntology, sat_append, sat_map]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq x hx
      exact (toClassExpr_iff i x q.sup).mp (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 q hq x ((toClassExpr_iff i x q.sub).mpr hx))
    · intro rs hrs x y hxy
      exact (objectHolds_oriented i rs.2 x y).mp (h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rs hrs x y ((objectHolds_oriented i rs.1 x y).mpr hxy))
    · intro c hc x y hp
      exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 c hc x y ((rolePath_objPath i c.body x y).mpr hp)
    · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · intro rs hrs x y ⟨h1, h2⟩
      have hd := h.1.1.1.1.1.1.1.1.1.1.1.1.2 rs hrs
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true, objectHolds_oriented] at hd
      exact hd.1 x y ⟨h1, h2⟩
    · exact h.1.1.1.1.1.1.1.1.1.1.1.2
    · intro rs hrs x y ⟨h1, h2⟩
      have hd := h.1.1.1.1.1.1.1.1.1.1.2 rs hrs
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true] at hd
      exact hd.1 x y ⟨h1, h2⟩
    · exact h.1.1.1.1.1.1.1.1.1.2
    · exact h.1.1.1.1.1.1.1.1.2
    · intro k hk x y hx hy hnx hny ho hd
      refine h.1.1.1.1.1.1.1.2 k hk x y ((toClassExpr_iff i x k.cls).mpr hx)
        ((toClassExpr_iff i y k.cls).mpr hy) hnx hny ?_ hd
      intro r hr
      obtain ⟨rn, hrn, rfl⟩ := List.mem_map.mp hr
      obtain ⟨z, hnz, hxz, hyz⟩ := ho rn hrn
      exact ⟨z, hnz, (objectHolds_oriented i rn x z).mpr hxz, (objectHolds_oriented i rn y z).mpr hyz⟩
    · intro ac hac
      exact (toClassExpr_iff i _ ac.2).mp (h.1.1.1.1.1.1.2 ac hac)
    · exact h.1.1.1.1.1.2
    · exact h.1.1.1.1.2
    · intro ab hab
      have hs := h.1.1.1.2 ab hab
      exact hs ab.1 (by simp) ab.2 (by simp)
    · intro ab hab
      have hd := h.1.1.2 ab hab
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true] at hd
      exact hd.1
    · exact h.1.2
    · exact h.2
  · intro hm
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro q hq x hx
      exact (toClassExpr_iff i x q.sup).mpr (hm.tbox q hq x ((toClassExpr_iff i x q.sub).mp hx))
    · intro rs hrs x y hxy
      exact (objectHolds_oriented i rs.2 x y).mpr (hm.rules rs hrs x y ((objectHolds_oriented i rs.1 x y).mp hxy))
    · intro c hc x y hp
      exact hm.chains c hc x y ((rolePath_objPath i c.body x y).mp hp)
    · exact hm.reflexive
    · exact hm.irreflexive
    · exact hm.asymmetric
    · intro rs hrs
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true, objectHolds_oriented]
      exact ⟨hm.disjoint rs hrs, by simp⟩
    · exact hm.subData
    · intro rs hrs
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true]
      exact ⟨hm.disjointData rs hrs, by simp⟩
    · exact hm.funcData
    · exact hm.dataRanges
    · intro k hk x y hx hy hnx hny ho hd
      refine hm.keys k hk x y ((toClassExpr_iff i x k.cls).mp hx)
        ((toClassExpr_iff i y k.cls).mp hy) hnx hny ?_ hd
      intro rn hrn
      obtain ⟨z, hnz, hxz, hyz⟩ := ho (orientedToObjProp rn) (List.mem_map_of_mem hrn)
      exact ⟨z, hnz, (objectHolds_oriented i rn x z).mp hxz, (objectHolds_oriented i rn y z).mp hyz⟩
    · intro ac hac
      exact (toClassExpr_iff i _ ac.2).mpr (hm.classAssertions ac hac)
    · exact hm.objAssertions
    · exact hm.negObjAssertions
    · intro ab hab a ha b hb
      have heq := hm.sameInds ab hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact heq
      · exact heq.symm
      · rfl
    · intro ab hab
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
        and_true]
      exact ⟨hm.diffInds ab hab, by simp⟩
    · exact hm.dataAssertions
    · exact hm.negDataAssertions

theorem satisfiable_iff_sat (p : Problem) (hroot : p.root = .top) :
    Satisfiable datatypeMap p.toOntology ↔ p.Sat := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    let j := i.withAnonymous assign
    obtain ⟨x⟩ := j.objectNonempty
    exact ⟨j, (satisfies_toOntology_iff j p).mp hsat, x, by rw [hroot]; trivial⟩
  · rintro ⟨i, hm, _⟩
    exact ⟨i, satisfies_models ((satisfies_toOntology_iff i p).mpr hm)⟩

private theorem dataHolds_withAnonymous (i : Interpretation datatypeMap)
    (assign : String → String → i.Object) (y : i.Data) (d : DataRange) :
    dataHolds (i.withAnonymous assign) y d ↔ dataHolds i y d := by
  induction d with
  | datatype _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ha hb => exact and_congr ha hb
  | union _ _ ha hb => exact or_congr ha hb
  | oneOf _ => rfl
  | restriction _ _ => rfl

def Concept.hasNoAnon : Concept → Bool
  | .top | .bottom | .lit _ _ | .self _ _
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _
  | .dataMin _ _ _ | .dataMax _ _ _ => true
  | .nom (.named _) _ => true
  | .nom (.anonymous _ _) _ => false
  | .conj a b | .disj a b => a.hasNoAnon && b.hasNoAnon
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.hasNoAnon

theorem holds_withAnonymous_of_noAnon (i : Interpretation datatypeMap)
    (assign : String → String → i.Object) (x : i.Object) (c : Concept)
    (hno : c.hasNoAnon = true) :
    holds (i.withAnonymous assign) x c ↔ holds i x c := by
  induction c generalizing x with
  | top | bottom => rfl
  | lit _ b => cases b <;> rfl
  | nom ind b =>
    cases ind with
    | anonymous _ _ => simp [Concept.hasNoAnon] at hno
    | named _ => cases b <;> rfl
  | self r b => rcases r with ⟨_, _ | _⟩ <;> cases b <;> rfl
  | conj a b ha hb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hno
    exact and_congr (ha x h1) (hb x h2)
  | disj a b ha hb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hno
    exact or_congr (ha x h1) (hb x h2)
  | some r c ih =>
    rcases r with ⟨_, _ | _⟩ <;>
    · simp only [holds, holdsOriented, Interpretation.withAnonymous]
      exact exists_congr fun y => and_congr Iff.rfl (ih y hno)
  | all r c ih =>
    rcases r with ⟨_, _ | _⟩ <;>
    · simp only [holds, holdsOriented, Interpretation.withAnonymous]
      exact forall_congr' fun y => imp_congr Iff.rfl (ih y hno)
  | min n r c ih =>
    rcases r with ⟨_, _ | _⟩ <;>
    · simp only [holds, holdsOriented, Interpretation.withAnonymous]
      exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y hno).mp (hp y hy).2⟩⟩,
             fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y hno).mpr (hp y hy).2⟩⟩⟩
  | max n r c ih =>
    rcases r with ⟨_, _ | _⟩ <;>
    · simp only [holds, holdsOriented, Interpretation.withAnonymous]
      exact not_congr
        ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y hno).mp (hp y hy).2⟩⟩,
         fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y hno).mpr (hp y hy).2⟩⟩⟩
  | dataSome r d =>
    simp only [holds, Interpretation.withAnonymous]
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withAnonymous i assign y d)
  | dataAll r d =>
    simp only [holds, Interpretation.withAnonymous]
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withAnonymous i assign y d)
  | dataValue _ _ b => cases b <;> rfl
  | dataMin n r d =>
    simp only [holds, Interpretation.withAnonymous]
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous i assign y d).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous i assign y d).mpr (hp y hy).2⟩⟩⟩
  | dataMax n r d =>
    simp only [holds, Interpretation.withAnonymous]
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous i assign y d).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (dataHolds_withAnonymous i assign y d).mpr (hp y hy).2⟩⟩⟩

def Concept.individuals : Concept → List Individual
  | .top | .bottom | .lit _ _ | .self _ _
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _
  | .dataMin _ _ _ | .dataMax _ _ _ => []
  | .nom a _ => [a]
  | .conj a b | .disj a b => a.individuals ++ b.individuals
  | .some _ c | .all _ c | .min _ _ c | .max _ _ c => c.individuals

def Problem.allIndividuals (p : Problem) : List Individual :=
  let tboxInds : List Individual := p.tbox.flatMap fun (q : Inclusion) => q.sub.individuals ++ q.sup.individuals
  let keyInds : List Individual := p.keys.flatMap fun (k : KeyAxiom) => k.cls.individuals
  let caInds : List Individual := p.classAssertions.flatMap fun ((a, c) : Individual × Concept) => a :: c.individuals
  let oaInds : List Individual := p.objAssertions.flatMap fun (_, a, b) => [a, b]
  let noaInds : List Individual := p.negObjAssertions.flatMap fun (_, a, b) => [a, b]
  let sameInds' : List Individual := p.sameInds.flatMap fun (a, b) => [a, b]
  let diffInds' : List Individual := p.diffInds.flatMap fun (a, b) => [a, b]
  let daInds : List Individual := p.dataAssertions.map fun (_, a, _) => a
  let ndaInds : List Individual := p.negDataAssertions.map fun (_, a, _) => a
  (p.root.individuals ++ tboxInds ++ keyInds ++ caInds ++ oaInds ++ noaInds ++
    sameInds' ++ diffInds' ++ daInds ++ ndaInds).eraseDups

def Problem.nominals (p : Problem) : List IRI :=
  p.allIndividuals.filterMap fun | .named a => some a | .anonymous _ _ => none

def Problem.anons (p : Problem) : List (String × String) :=
  p.allIndividuals.filterMap fun | .anonymous doc lid => some (doc, lid) | .named _ => none

def Concept.countedRoles : Concept → List OrientedRole
  | .top | .bottom | .lit _ _ | .nom _ _
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _ _
  | .dataMin _ _ _ | .dataMax _ _ _ => []
  | .self r _ => [r]
  | .conj a b | .disj a b => a.countedRoles ++ b.countedRoles
  | .some _ c | .all _ c => c.countedRoles
  | .min _ r c | .max _ r c => r :: c.countedRoles

def Problem.simpleRoles (p : Problem) : List OrientedRole :=
  let tboxCounted : List OrientedRole := p.tbox.flatMap fun (q : Inclusion) => q.sub.countedRoles ++ q.sup.countedRoles
  let keyCounted : List OrientedRole := p.keys.flatMap fun (k : KeyAxiom) => k.cls.countedRoles
  let caCounted : List OrientedRole := p.classAssertions.flatMap fun ((_, c) : Individual × Concept) => c.countedRoles
  let namedSimple : List IRI := p.chars.irreflexive ++ p.chars.asymmetric
  let disjSimple : List OrientedRole := p.chars.disjoint.flatMap fun (r, s) => [r, s]
  (p.root.countedRoles ++ tboxCounted ++ keyCounted ++ caCounted ++
    namedSimple.map (·, false) ++ disjSimple).eraseDups

def Problem.checkSimple (p : Problem) : Bool :=
  let closed := roleClosure p.rules
  p.simpleRoles.all fun r => (RoleChains.SimpleRoles.firstComposite closed p.chains r).isNone

theorem Problem.checkSimple_iff {p : Problem} :
    p.checkSimple = true ↔ ∀ r ∈ p.simpleRoles, RoleChains.SimpleRoles.Simple p.rules p.chains r := by
  unfold Problem.checkSimple
  rw [List.all_eq_true]
  exact ⟨fun h r hr => RoleChains.SimpleRoles.check_iff.mp (h r hr),
         fun h r hr => RoleChains.SimpleRoles.check_iff.mpr (h r hr)⟩

end Sabrina.OWL2.SROIQD
