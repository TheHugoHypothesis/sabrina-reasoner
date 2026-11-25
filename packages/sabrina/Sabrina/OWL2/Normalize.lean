import Sabrina.OWL2.SROIQD.Search
import Sabrina.OWL2.SROIQD.CoreCompleteness
import Sabrina.RoleChains.Regularity

/-! Verified OWL 2 DL normalization from `Sabrina.OWL2.Ontology` to
    `Sabrina.OWL2.SROIQD.Problem` with two-way model preservation,
    acyclic `DatatypeDefinition` unfolding, `ObjectInverseOf` support,
    data property hierarchy & disjointness, anonymous individuals,
    global restriction validation, and M10 query service reductions. -/

namespace Sabrina.OWL2.Normalize

open Sabrina.OWL2
open Sabrina.OWL2.SROIQD
open Sabrina.OWL2.Datatypes (datatypeMap supportedDatatype)
open Sabrina.OWL2.DataRanges (lowerSmallRanges)
open Sabrina.ALC (OrientedRole InclusionVerdict)

def toOriented : ObjectProperty → OrientedRole
  | .named r => (r, false)
  | .inverse r => (r, true)

private def objPropName : ObjectProperty → IRI
  | .named r => r
  | .inverse r => r

theorem oriented_iff (i : Interpretation dm) (r : ObjectProperty) (x y : i.Object) :
    objectHolds i r x y ↔ holdsOriented i (toOriented r) x y := by
  cases r <;> rfl

private def normalizeChain (rs : List ObjectProperty) (head : ObjectProperty) :
    RoleChains.Chain :=
  let body := rs.map toOriented
  match head with
  | .named r => ⟨body, r⟩
  | .inverse r => ⟨RoleChains.TransitivePaths.flipWord body, r⟩

private theorem mappedOrientedPath (i : Interpretation dm)
    (rs : List ObjectProperty) (x y : i.Object) :
    rolePath i rs x y ↔ objPath i (rs.map toOriented) x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, rolePath, objPath, oriented_iff, ih]

private theorem normalizeChain_iff (i : Interpretation dm)
    (rs : List ObjectProperty) (s : ObjectProperty) :
    axiomHolds i (.subObjectPropertyChain rs s) ↔
      ∀ x y, objPath i (normalizeChain rs s).body x y →
        i.objectProperties (normalizeChain rs s).head x y := by
  cases s with
  | named r =>
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr (mappedOrientedPath i rs x y) Iff.rfl
  | inverse r =>
    constructor
    · intro h x y hp
      exact h y x ((mappedOrientedPath i rs y x).mpr ((objPath_flip_iff i _ y x).mp hp))
    · intro h x y hp
      exact h y x (objPath_flip ((mappedOrientedPath i rs x y).mp hp))

def normClassExpr : ClassExpr → Concept
  | .named c =>
    if c == thing then .top
    else if c == nothing then .bottom
    else .lit c true
  | .complement c => (normClassExpr c).dual
  | .intersection a b => .conj (normClassExpr a) (normClassExpr b)
  | .union a b => .disj (normClassExpr a) (normClassExpr b)
  | .oneOf inds => Concept.oneOf inds
  | .objectSome r c => .some (toOriented r) (normClassExpr c)
  | .objectAll r c => .all (toOriented r) (normClassExpr c)
  | .objectValue r a => .hasValue (toOriented r) a
  | .objectSelf r => .self (toOriented r) true
  | .objectMin n r c => .min n (toOriented r) (normClassExpr c)
  | .objectMax n r c => .max n (toOriented r) (normClassExpr c)
  | .objectExact n r c => .exact n (toOriented r) (normClassExpr c)
  | .dataSome dp d => .dataSome dp (lowerSmallRanges d).1
  | .dataAll dp d => .dataAll dp (lowerSmallRanges d).1
  | .dataValue dp l => .dataValue dp l true
  | .dataMin n dp d => .dataMin n dp (lowerSmallRanges d).1
  | .dataMax n dp d => .dataMax n dp (lowerSmallRanges d).1
  | .dataExact n dp d => .dataExact n dp (lowerSmallRanges d).1

private theorem oneOf_holds_iff (i : Interpretation dm) (x : i.Object)
    (inds : List Individual) :
    (∃ a ∈ inds, i.individuals a = x) ↔ SROIQD.holds i x (Concept.oneOf inds) := by
  induction inds with
  | nil => simp [Concept.oneOf, SROIQD.holds]
  | cons ind tail ih =>
    simp only [Concept.oneOf, List.foldr_cons, SROIQD.holds, List.mem_cons, exists_eq_or_imp]
    exact or_congr eq_comm ih

section Lowering

variable {dm : DatatypeMap}
variable (lower : ∀ (d : DataRange) (i : Interpretation dm) (y : i.Data),
  dataHolds i y (lowerSmallRanges d).1 ↔ dataHolds i y d)

include lower in
private theorem atLeast_lowerSmallRanges (i : Interpretation dm)
    (x : i.Object) (dp : IRI) (d : DataRange) (n : Nat) :
    AtLeast n (fun y => i.dataProperties dp x y ∧ dataHolds i y d) ↔
      AtLeast n (fun y => i.dataProperties dp x y ∧ dataHolds i y (lowerSmallRanges d).1) := by
  constructor
  · rintro ⟨xs, hl, hn, hp⟩
    exact ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (lower d i y).mpr (hp y hy).2⟩⟩
  · rintro ⟨xs, hl, hn, hp⟩
    exact ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (lower d i y).mp (hp y hy).2⟩⟩

include lower in
theorem normClassExpr_iff_with (i : Interpretation dm) (x : i.Object) (c : ClassExpr) :
    classHolds i x c ↔ SROIQD.holds i x (normClassExpr c) := by
  induction c generalizing x with
  | named s =>
    simp only [normClassExpr]
    by_cases h1 : s = thing
    · subst h1; simp [classHolds, SROIQD.holds, i.thingExt x]
    · by_cases h2 : s = nothing
      · subst h2; simp [h1, classHolds, SROIQD.holds, i.nothingExt x]
      · simp [h1, h2, classHolds, SROIQD.holds]
  | complement body ih =>
    simp only [normClassExpr, holds_dual, ← ih x]; rfl
  | intersection a b ha hb => exact and_congr (ha x) (hb x)
  | union a b ha hb => exact or_congr (ha x) (hb x)
  | oneOf inds => exact oneOf_holds_iff i x inds
  | objectSome r body ih =>
    simp only [normClassExpr, classHolds, SROIQD.holds, oriented_iff]
    exact exists_congr fun y => and_congr Iff.rfl (ih y)
  | objectAll r body ih =>
    simp only [normClassExpr, classHolds, SROIQD.holds, oriented_iff]
    exact forall_congr' fun y => imp_congr Iff.rfl (ih y)
  | objectValue r ind =>
    simp only [normClassExpr, classHolds, Concept.hasValue, SROIQD.holds, oriented_iff]
    exact ⟨fun hr => ⟨i.individuals ind, hr, rfl⟩, fun ⟨y, hr, hy⟩ => hy ▸ hr⟩
  | objectSelf r =>
    simp only [normClassExpr, classHolds, SROIQD.holds, oriented_iff]
  | objectMin n r body ih =>
    simp only [normClassExpr, classHolds, SROIQD.holds, oriented_iff]
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mpr (hp y hy).2⟩⟩⟩
  | objectMax n r body ih =>
    simp only [normClassExpr, classHolds, SROIQD.holds, oriented_iff]
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mpr (hp y hy).2⟩⟩⟩
  | objectExact n r body ih =>
    simp only [normClassExpr, classHolds, Exactly, Concept.exact, SROIQD.holds, oriented_iff]
    have hAt : ∀ k, AtLeast k (fun y => holdsOriented i (toOriented r) x y ∧ classHolds i y body) ↔
        AtLeast k (fun y => holdsOriented i (toOriented r) x y ∧ SROIQD.holds i y (normClassExpr body)) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih y).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr Iff.rfl (lower d i y).symm
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (lower d i y).symm
  | dataValue _ _ => rfl
  | dataMin n dp d => exact atLeast_lowerSmallRanges lower i x dp d n
  | dataMax n dp d => exact not_congr (atLeast_lowerSmallRanges lower i x dp d (n + 1))
  | dataExact n dp d =>
    exact and_congr (atLeast_lowerSmallRanges lower i x dp d n)
      (not_congr (atLeast_lowerSmallRanges lower i x dp d (n + 1)))

private def allPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ allPairs xs

private theorem pairwise_iff_allPairs {α : Type} {R : α → α → Prop} (xs : List α) :
    xs.Pairwise R ↔ ∀ p ∈ allPairs xs, R p.1 p.2 := by
  induction xs with
  | nil => simp [allPairs]
  | cons a tail ih =>
    simp only [List.pairwise_cons, allPairs, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨ha, htail⟩ p hp
      rcases hp with ⟨b, hb, rfl⟩ | hp
      · exact ha b hb
      · exact ih.mp htail p hp
    · intro h
      exact ⟨fun b hb => h (a, b) (Or.inl ⟨b, hb, rfl⟩),
             ih.mpr fun p hp => h p (Or.inr hp)⟩

private def uniteConcepts (cs : List Concept) : Concept :=
  cs.foldr Concept.disj .bottom

private theorem holds_uniteConcepts (i : Interpretation dm) (x : i.Object)
    (cs : List Concept) :
    SROIQD.holds i x (uniteConcepts cs) ↔ ∃ c ∈ cs, SROIQD.holds i x c := by
  induction cs with
  | nil => simp [uniteConcepts, SROIQD.holds]
  | cons a tail ih =>
    simp only [uniteConcepts, List.foldr_cons, SROIQD.holds, List.mem_cons, exists_eq_or_imp]
    exact or_congr Iff.rfl ih

/-- Add one OWL 2 `Axiom` into an `SROIQD.Problem`. Datatype definitions are
    handled by `normalizeWithDefs`. A property chain must have at least two steps. -/
def addAxiom (p : Problem) : Axiom → Option Problem
  | .subClassOf a b =>
    some { p with tbox := ⟨normClassExpr a, normClassExpr b⟩ :: p.tbox }
  | .equivalentClasses cs =>
    let ncs := cs.map normClassExpr
    let incs := (allPairs ncs).flatMap fun (a, b) => [⟨a, b⟩, ⟨b, a⟩]
    some { p with tbox := incs ++ p.tbox }
  | .disjointClasses cs =>
    let ncs := cs.map normClassExpr
    let incs := (allPairs ncs).map fun (a, b) => ⟨.conj a b, .bottom⟩
    some { p with tbox := incs ++ p.tbox }
  | .disjointUnion h cs =>
    let ncs := cs.map normClassExpr
    let cover : Inclusion := ⟨.lit h true, uniteConcepts ncs⟩
    let subs : List Inclusion := ncs.map fun c => ⟨c, .lit h true⟩
    let disjs : List Inclusion := (allPairs ncs).map fun (a, b) => ⟨.conj a b, .bottom⟩
    some { p with tbox := cover :: subs ++ disjs ++ p.tbox }
  | .subObjectProperty r s =>
    some { p with rules := (toOriented r, toOriented s) :: p.rules }
  | .subObjectPropertyChain rs h =>
    if rs.length < 2 then none
    else some { p with chains := normalizeChain rs h :: p.chains }
  | .equivalentObjectProperties rs =>
    let pairs := (allPairs rs).flatMap fun (r, s) =>
      [(toOriented r, toOriented s), (toOriented s, toOriented r)]
    some { p with rules := pairs ++ p.rules }
  | .disjointObjectProperties rs =>
    let pairs := (allPairs rs).map fun (r, s) => (toOriented r, toOriented s)
    some { p with chars := { p.chars with disjoint := pairs ++ p.chars.disjoint } }
  | .inverseObjectProperties r s =>
    some { p with rules := (toOriented r, toOriented s.converse) ::
                           (toOriented s.converse, toOriented r) :: p.rules }
  | .objectPropertyDomain r c =>
    some { p with tbox := ⟨.some (toOriented r) .top, normClassExpr c⟩ :: p.tbox }
  | .objectPropertyRange r c =>
    some { p with tbox := ⟨.top, .all (toOriented r) (normClassExpr c)⟩ :: p.tbox }
  | .functionalObjectProperty r =>
    some { p with tbox := ⟨.top, .max 1 (toOriented r) .top⟩ :: p.tbox }
  | .inverseFunctionalObjectProperty r =>
    some { p with tbox := ⟨.top, .max 1 (toOriented r.converse) .top⟩ :: p.tbox }
  | .reflexiveObjectProperty r =>
    some { p with chars := { p.chars with reflexive := objPropName r :: p.chars.reflexive } }
  | .irreflexiveObjectProperty r =>
    some { p with chars := { p.chars with irreflexive := objPropName r :: p.chars.irreflexive } }
  | .symmetricObjectProperty r =>
    let rn := objPropName r
    some { p with rules := ((rn, true), (rn, false)) :: p.rules }
  | .asymmetricObjectProperty r =>
    some { p with chars := { p.chars with asymmetric := objPropName r :: p.chars.asymmetric } }
  | .transitiveObjectProperty r =>
    let rn := objPropName r
    some { p with chains := RoleChains.Chain.named [rn, rn] rn :: p.chains }
  | .subDataProperty r s =>
    some { p with subData := (r, s) :: p.subData }
  | .equivalentDataProperties rs =>
    let pairs := (allPairs rs).flatMap fun (r, s) => [(r, s), (s, r)]
    some { p with subData := pairs ++ p.subData }
  | .disjointDataProperties rs =>
    some { p with disjointData := allPairs rs ++ p.disjointData }
  | .dataPropertyDomain dp c =>
    some { p with tbox := ⟨.dataSome dp (.datatype literalDatatype), normClassExpr c⟩ :: p.tbox }
  | .dataPropertyRange dp d =>
    some { p with dataRanges := (dp, (lowerSmallRanges d).1) :: p.dataRanges }
  | .functionalDataProperty dp =>
    some { p with funcData := dp :: p.funcData }
  | .datatypeDefinition _ _ => none
  | .hasKey c rs ds =>
    some { p with keys := ⟨normClassExpr c, rs.map toOriented, ds⟩ :: p.keys }
  | .sameIndividuals inds =>
    some { p with sameInds := allPairs inds ++ p.sameInds }
  | .differentIndividuals inds =>
    some { p with diffInds := allPairs inds ++ p.diffInds }
  | .classAssertion c a =>
    some { p with classAssertions := (a, normClassExpr c) :: p.classAssertions }
  | .objectAssertion (.named r) a b =>
    some { p with objAssertions := (r, a, b) :: p.objAssertions }
  | .objectAssertion (.inverse r) a b =>
    some { p with objAssertions := (r, b, a) :: p.objAssertions }
  | .negativeObjectAssertion (.named r) a b =>
    some { p with negObjAssertions := (r, a, b) :: p.negObjAssertions }
  | .negativeObjectAssertion (.inverse r) a b =>
    some { p with negObjAssertions := (r, b, a) :: p.negObjAssertions }
  | .dataAssertion dp a l =>
    some { p with dataAssertions := (dp, a, l) :: p.dataAssertions }
  | .negativeDataAssertion dp a l =>
    some { p with negDataAssertions := (dp, a, l) :: p.negDataAssertions }

def normalize (o : Ontology) : Option Problem :=
  o.foldlM addAxiom {}

private theorem eq_allPairs_iff {α : Type} {R : α → α → Prop}
    (hrefl : ∀ x, R x x) (_hsym : ∀ x y, R x y → R y x) (xs : List α) :
    (∀ a ∈ xs, ∀ b ∈ xs, R a b) ↔ ∀ p ∈ allPairs xs, R p.1 p.2 ∧ R p.2 p.1 := by
  induction xs with
  | nil => simp [allPairs]
  | cons x tail ih =>
    simp only [allPairs, List.mem_append, List.mem_map, List.mem_cons]
    constructor
    · intro h p hp
      rcases hp with ⟨b, hb, rfl⟩ | hp
      · exact ⟨h x (Or.inl rfl) b (Or.inr hb), h b (Or.inr hb) x (Or.inl rfl)⟩
      · exact ih.mp (fun a ha b hb => h a (Or.inr ha) b (Or.inr hb)) p hp
    · intro h a ha b hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hrefl _
      · exact (h (_, b) (Or.inl ⟨b, hb, rfl⟩)).1
      · exact (h (_, a) (Or.inl ⟨a, ha, rfl⟩)).2
      · exact ih.mpr (fun p hp => h p (Or.inr hp)) a ha b hb

include lower in
theorem addAxiom_models_iff_with (i : Interpretation dm) (p p' : Problem) (ax : Axiom)
    (h : addAxiom p ax = some p') :
    p'.Models i ↔ axiomHolds i ax ∧ p.Models i := by
  cases ax with
  | subClassOf a b =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x hx => (normClassExpr_iff_with lower i x b).mpr (hm.tbox _ (List.mem_cons_self ..) x ((normClassExpr_iff_with lower i x a).mp hx)),
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (normClassExpr_iff_with lower i x b).mp (hax x ((normClassExpr_iff_with lower i x a).mpr hx))
      · exact hm.tbox q hq x hx
  | equivalentClasses cs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have heq_iff : (∀ (q : Inclusion), q ∈ (allPairs (cs.map normClassExpr)).flatMap (fun (a, b) => [⟨a, b⟩, ⟨b, a⟩]) →
        ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup) ↔
        ∀ a ∈ cs, ∀ b ∈ cs, ∀ x, classHolds i x a ↔ classHolds i x b := by
      have h1 : (∀ (q : Inclusion), q ∈ (allPairs (cs.map normClassExpr)).flatMap (fun (a, b) => [⟨a, b⟩, ⟨b, a⟩]) →
          ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup) ↔
          ∀ pr ∈ allPairs (cs.map normClassExpr), (∀ x, SROIQD.holds i x pr.1 ↔ SROIQD.holds i x pr.2) ∧
                              (∀ x, SROIQD.holds i x pr.2 ↔ SROIQD.holds i x pr.1) := by
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hall pr hpr
          have hlr := hall ⟨pr.1, pr.2⟩ ⟨pr, hpr, Or.inl rfl⟩
          have hrl := hall ⟨pr.2, pr.1⟩ ⟨pr, hpr, Or.inr rfl⟩
          exact ⟨fun x => ⟨hlr x, hrl x⟩, fun x => ⟨hrl x, hlr x⟩⟩
        · rintro hall q ⟨pr, hpr, rfl | rfl⟩ x hx
          · exact ((hall pr hpr).1 x).mp hx
          · exact ((hall pr hpr).1 x).mpr hx
      rw [h1, ← eq_allPairs_iff (R := fun a b => ∀ x, SROIQD.holds i x a ↔ SROIQD.holds i x b)
        (fun _ _ => Iff.rfl) (fun _ _ h x => (h x).symm)]
      constructor
      · intro hall a ha b hb' x
        exact (normClassExpr_iff_with lower i x a).trans
          ((hall _ (List.mem_map_of_mem ha) _ (List.mem_map_of_mem hb') x).trans
            (normClassExpr_iff_with lower i x b).symm)
      · intro hall na hna nb hnb x
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hna
        obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hnb
        exact (normClassExpr_iff_with lower i x a).symm.trans ((hall a ha b hb' x).trans (normClassExpr_iff_with lower i x b))
    constructor
    · intro hmod
      refine ⟨heq_iff.mp (fun q hq => hmod.tbox q (List.mem_append_left _ hq)),
        ⟨fun q hq => hmod.tbox q (List.mem_append_right _ hq), hmod.rules, hmod.chains,
         hmod.reflexive, hmod.irreflexive, hmod.asymmetric, hmod.disjoint, hmod.subData,
         hmod.disjointData, hmod.funcData, hmod.dataRanges, hmod.keys, hmod.classAssertions,
         hmod.objAssertions, hmod.negObjAssertions, hmod.sameInds, hmod.diffInds,
         hmod.dataAssertions, hmod.negDataAssertions⟩⟩
    · rintro ⟨hax, hmod⟩
      refine ⟨fun q hq => (List.mem_append.mp hq).elim (heq_iff.mpr hax q) (hmod.tbox q),
        hmod.rules, hmod.chains, hmod.reflexive, hmod.irreflexive, hmod.asymmetric,
        hmod.disjoint, hmod.subData, hmod.disjointData, hmod.funcData, hmod.dataRanges,
        hmod.keys, hmod.classAssertions, hmod.objAssertions, hmod.negObjAssertions,
        hmod.sameInds, hmod.diffInds, hmod.dataAssertions, hmod.negDataAssertions⟩
  | disjointClasses cs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hdisj : (∀ (q : Inclusion), q ∈ (allPairs (cs.map normClassExpr)).map (fun (a, b) => ⟨.conj a b, .bottom⟩) →
        ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup) ↔
        cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) := by
      have hp : cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) ↔
          (cs.map normClassExpr).Pairwise (fun a b => ∀ x, ¬ (SROIQD.holds i x a ∧ SROIQD.holds i x b)) := by
        rw [List.pairwise_map]
        exact ⟨fun h => h.imp fun h1 x ⟨ha, hb⟩ => h1 x ⟨(normClassExpr_iff_with lower i x _).mpr ha, (normClassExpr_iff_with lower i x _).mpr hb⟩,
               fun h => h.imp fun h1 x ⟨ha, hb⟩ => h1 x ⟨(normClassExpr_iff_with lower i x _).mp ha, (normClassExpr_iff_with lower i x _).mp hb⟩⟩
      rw [hp, pairwise_iff_allPairs]
      simp only [List.mem_map]
      exact ⟨fun hall pr hpr x hboth => hall ⟨.conj pr.1 pr.2, .bottom⟩ ⟨pr, hpr, rfl⟩ x hboth,
             fun hall _ ⟨pr, hpr, hq⟩ x hboth => by subst hq; exact hall pr hpr x hboth⟩
    constructor
    · intro hmod
      refine ⟨hdisj.mp (fun q hq => hmod.tbox q (List.mem_append_left _ hq)),
        ⟨fun q hq => hmod.tbox q (List.mem_append_right _ hq), hmod.rules, hmod.chains,
         hmod.reflexive, hmod.irreflexive, hmod.asymmetric, hmod.disjoint, hmod.subData,
         hmod.disjointData, hmod.funcData, hmod.dataRanges, hmod.keys, hmod.classAssertions,
         hmod.objAssertions, hmod.negObjAssertions, hmod.sameInds, hmod.diffInds,
         hmod.dataAssertions, hmod.negDataAssertions⟩⟩
    · rintro ⟨hax, hmod⟩
      refine ⟨fun q hq => (List.mem_append.mp hq).elim (hdisj.mpr hax q) (hmod.tbox q),
        hmod.rules, hmod.chains, hmod.reflexive, hmod.irreflexive, hmod.asymmetric,
        hmod.disjoint, hmod.subData, hmod.disjointData, hmod.funcData, hmod.dataRanges,
        hmod.keys, hmod.classAssertions, hmod.objAssertions, hmod.negObjAssertions,
        hmod.sameInds, hmod.diffInds, hmod.dataAssertions, hmod.negDataAssertions⟩
  | disjointUnion head cs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hdisj : (∀ (q : Inclusion), q ∈ (allPairs (cs.map normClassExpr)).map (fun (a, b) => ⟨.conj a b, .bottom⟩) →
        ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup) ↔
        cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) := by
      have hp : cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) ↔
          (cs.map normClassExpr).Pairwise (fun a b => ∀ x, ¬ (SROIQD.holds i x a ∧ SROIQD.holds i x b)) := by
        rw [List.pairwise_map]
        exact ⟨fun h => h.imp fun h1 x ⟨ha, hb⟩ => h1 x ⟨(normClassExpr_iff_with lower i x _).mpr ha, (normClassExpr_iff_with lower i x _).mpr hb⟩,
               fun h => h.imp fun h1 x ⟨ha, hb⟩ => h1 x ⟨(normClassExpr_iff_with lower i x _).mp ha, (normClassExpr_iff_with lower i x _).mp hb⟩⟩
      rw [hp, pairwise_iff_allPairs]
      simp only [List.mem_map]
      exact ⟨fun hall pr hpr x hboth => hall ⟨.conj pr.1 pr.2, .bottom⟩ ⟨pr, hpr, rfl⟩ x hboth,
             fun hall _ ⟨pr, hpr, hq⟩ x hboth => by subst hq; exact hall pr hpr x hboth⟩
    constructor
    · intro hmod
      have hcov := hmod.tbox ⟨.lit head true, uniteConcepts (cs.map normClassExpr)⟩ (by simp)
      have hsubs : ∀ q ∈ (cs.map normClassExpr).map (fun c => (⟨c, .lit head true⟩ : Inclusion)),
          ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup :=
        fun q hq => hmod.tbox q (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hq)))
      have hds : ∀ q ∈ (allPairs (cs.map normClassExpr)).map (fun (a, b) => (⟨.conj a b, .bottom⟩ : Inclusion)),
          ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup :=
        fun q hq => hmod.tbox q (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hq)))
      refine ⟨⟨fun x => ⟨fun hx => by
          obtain ⟨nc, hnc, hhold⟩ := (holds_uniteConcepts i x _).mp (hcov x hx)
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnc
          exact ⟨c, hc, (normClassExpr_iff_with lower i x c).mpr hhold⟩,
        fun ⟨c, hc, hcx⟩ =>
          hsubs ⟨normClassExpr c, .lit head true⟩ (List.mem_map_of_mem (List.mem_map_of_mem hc)) x
            ((normClassExpr_iff_with lower i x c).mp hcx)⟩,
        hdisj.mp hds⟩,
        ⟨fun q hq => hmod.tbox q (by simp [hq]), hmod.rules, hmod.chains,
         hmod.reflexive, hmod.irreflexive, hmod.asymmetric, hmod.disjoint, hmod.subData,
         hmod.disjointData, hmod.funcData, hmod.dataRanges, hmod.keys, hmod.classAssertions,
         hmod.objAssertions, hmod.negObjAssertions, hmod.sameInds, hmod.diffInds,
         hmod.dataAssertions, hmod.negDataAssertions⟩⟩
    · rintro ⟨⟨hunion, hpair⟩, hmod⟩
      refine ⟨?_, hmod.rules, hmod.chains, hmod.reflexive, hmod.irreflexive, hmod.asymmetric,
        hmod.disjoint, hmod.subData, hmod.disjointData, hmod.funcData, hmod.dataRanges,
        hmod.keys, hmod.classAssertions, hmod.objAssertions, hmod.negObjAssertions,
        hmod.sameInds, hmod.diffInds, hmod.dataAssertions, hmod.negDataAssertions⟩
      intro q hq x hx
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hq
      rcases hq with ((rfl | ⟨nc, ⟨c, hc, rfl⟩, rfl⟩) | ⟨pr, hpr, rfl⟩) | hq
      · obtain ⟨c, hc, hcx⟩ := (hunion x).mp hx
        exact (holds_uniteConcepts i x _).mpr ⟨normClassExpr c, List.mem_map_of_mem hc, (normClassExpr_iff_with lower i x c).mp hcx⟩
      · exact (hunion x).mpr ⟨c, hc, (normClassExpr_iff_with lower i x c).mpr hx⟩
      · exact hdisj.mpr hpair _ (List.mem_map_of_mem hpr) x hx
      · exact hmod.tbox q hq x hx
  | subObjectProperty r s =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y hxy => (oriented_iff i s x y).mpr (hm.rules _ (List.mem_cons_self ..) x y ((oriented_iff i r x y).mp hxy)),
        ⟨hm.tbox, fun rs hrs => hm.rules rs (List.mem_cons_of_mem _ hrs), hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, ?_, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro rs hrs x y hxy
      rcases List.mem_cons.mp hrs with rfl | hrs
      · exact (oriented_iff i s x y).mp (hax x y ((oriented_iff i r x y).mpr hxy))
      · exact hm.rules rs hrs x y hxy
  | subObjectPropertyChain rs s =>
    simp only [addAxiom] at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h; subst h
      constructor
      · intro hm
        exact ⟨(normalizeChain_iff i rs s).mpr (hm.chains _ (List.mem_cons_self ..)),
          ⟨hm.tbox, hm.rules, fun c hc => hm.chains c (List.mem_cons_of_mem _ hc), hm.reflexive,
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
      · rintro ⟨hax, hm⟩
        refine ⟨hm.tbox, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
          hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
          hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
          hm.negDataAssertions⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact (normalizeChain_iff i rs s).mp hax
        · exact hm.chains c hc
  | equivalentObjectProperties rs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have heq_iff : (∀ e ∈ (allPairs rs).flatMap (fun (r, s) => [(toOriented r, toOriented s), (toOriented s, toOriented r)]),
        ∀ x y, holdsOriented i e.1 x y → holdsOriented i e.2 x y) ↔
        ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, objectHolds i r x y ↔ objectHolds i s x y := by
      have h1 : (∀ e ∈ (allPairs rs).flatMap (fun (r, s) => [(toOriented r, toOriented s), (toOriented s, toOriented r)]),
          ∀ x y, holdsOriented i e.1 x y → holdsOriented i e.2 x y) ↔
          ∀ pr ∈ allPairs rs, (∀ x y, objectHolds i pr.1 x y ↔ objectHolds i pr.2 x y) ∧
                              (∀ x y, objectHolds i pr.2 x y ↔ objectHolds i pr.1 x y) := by
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hall pr hpr
          have hlr := hall _ ⟨pr, hpr, Or.inl rfl⟩
          have hrl := hall _ ⟨pr, hpr, Or.inr rfl⟩
          have heq : ∀ x y, objectHolds i pr.1 x y ↔ objectHolds i pr.2 x y := fun x y =>
            ⟨fun h1 => (oriented_iff i pr.2 x y).mpr (hlr x y ((oriented_iff i pr.1 x y).mp h1)),
             fun h2 => (oriented_iff i pr.1 x y).mpr (hrl x y ((oriented_iff i pr.2 x y).mp h2))⟩
          exact ⟨heq, fun x y => (heq x y).symm⟩
        · rintro hall e ⟨pr, hpr, rfl | rfl⟩ x y hxy
          · exact (oriented_iff i pr.2 x y).mp (((hall pr hpr).1 x y).mp ((oriented_iff i pr.1 x y).mpr hxy))
          · exact (oriented_iff i pr.1 x y).mp (((hall pr hpr).1 x y).mpr ((oriented_iff i pr.2 x y).mpr hxy))
      rw [h1, ← eq_allPairs_iff (R := fun r s => ∀ x y, objectHolds i r x y ↔ objectHolds i s x y)
        (fun _ _ _ => Iff.rfl) (fun _ _ h x y => (h x y).symm)]
    constructor
    · intro hm
      refine ⟨heq_iff.mp (fun e he => hm.rules e (List.mem_append_left _ he)),
        ⟨hm.tbox, fun e he => hm.rules e (List.mem_append_right _ he), hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, fun e he => (List.mem_append.mp he).elim (heq_iff.mpr hax e) (hm.rules e),
        hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData,
        hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
  | disjointObjectProperties rs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hdisj : (∀ pr ∈ (allPairs rs).map (fun (r, s) => (toOriented r, toOriented s)),
        ∀ x y, ¬ (holdsOriented i pr.1 x y ∧ holdsOriented i pr.2 x y)) ↔
        rs.Pairwise (fun r s => ∀ x y, ¬ (objectHolds i r x y ∧ objectHolds i s x y)) := by
      rw [pairwise_iff_allPairs]
      simp only [List.mem_map]
      constructor
      · intro hall pr hpr x y ⟨h1, h2⟩
        exact hall _ ⟨pr, hpr, rfl⟩ x y ⟨(oriented_iff i pr.1 x y).mp h1, (oriented_iff i pr.2 x y).mp h2⟩
      · rintro hall _ ⟨pr, hpr, rfl⟩ x y ⟨h1, h2⟩
        exact hall pr hpr x y ⟨(oriented_iff i pr.1 x y).mpr h1, (oriented_iff i pr.2 x y).mpr h2⟩
    constructor
    · intro hm
      refine ⟨hdisj.mp (fun pr hpr => hm.disjoint pr (List.mem_append_left _ hpr)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
         fun pr hpr => hm.disjoint pr (List.mem_append_right _ hpr), hm.subData, hm.disjointData,
         hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions,
         hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        fun pr hpr => (List.mem_append.mp hpr).elim (hdisj.mpr hax pr) (hm.disjoint pr),
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
  | inverseObjectProperties r s =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y => ⟨fun h1 => (objectHolds_converse i s x y).mp ((oriented_iff i s.converse x y).mpr
            (hm.rules _ (List.mem_cons_self ..) x y ((oriented_iff i r x y).mp h1))),
          fun h2 => (oriented_iff i r x y).mpr (hm.rules _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            x y ((oriented_iff i s.converse x y).mp ((objectHolds_converse i s x y).mpr h2)))⟩,
        ⟨hm.tbox, fun e he => hm.rules e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)),
         hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData,
         hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
         hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
         hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, ?_, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro e he x y hxy
      rcases List.mem_cons.mp he with rfl | he
      · exact (oriented_iff i s.converse x y).mp ((objectHolds_converse i s x y).mpr ((hax x y).mp ((oriented_iff i r x y).mpr hxy)))
      · rcases List.mem_cons.mp he with rfl | he
        · exact (oriented_iff i r x y).mp ((hax x y).mpr ((objectHolds_converse i s x y).mp ((oriented_iff i s.converse x y).mpr hxy)))
        · exact hm.rules e he x y hxy
  | objectPropertyDomain r c =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y hxy => (normClassExpr_iff_with lower i x c).mpr
          (hm.tbox _ (List.mem_cons_self ..) x ⟨y, (oriented_iff i r x y).mp hxy, trivial⟩),
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · obtain ⟨y, hxy, _⟩ := hx
        exact (normClassExpr_iff_with lower i x c).mp (hax x y ((oriented_iff i r x y).mpr hxy))
      · exact hm.tbox q hq x hx
  | objectPropertyRange r c =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y hxy => (normClassExpr_iff_with lower i y c).mpr
          (hm.tbox _ (List.mem_cons_self ..) x trivial y ((oriented_iff i r x y).mp hxy)),
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · intro y hxy
        exact (normClassExpr_iff_with lower i y c).mp (hax x y ((oriented_iff i r x y).mpr hxy))
      · exact hm.tbox q hq x hx
  | functionalObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y z hxy hxz => ((atMostOne_iff _).mp (hm.tbox _ (List.mem_cons_self ..) x trivial))
          y z ⟨(oriented_iff i r x y).mp hxy, trivial⟩ ⟨(oriented_iff i r x z).mp hxz, trivial⟩,
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (atMostOne_iff _).mpr fun y z hy hz =>
          hax x y z ((oriented_iff i r x y).mpr hy.1) ((oriented_iff i r x z).mpr hz.1)
      · exact hm.tbox q hq x hx
  | inverseFunctionalObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y z hyx hzx => ((atMostOne_iff _).mp (hm.tbox _ (List.mem_cons_self ..) x trivial))
          y z ⟨(oriented_iff i r.converse x y).mp ((objectHolds_converse i r x y).mpr hyx), trivial⟩
              ⟨(oriented_iff i r.converse x z).mp ((objectHolds_converse i r x z).mpr hzx), trivial⟩,
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (atMostOne_iff _).mpr fun y z hy hz =>
          hax x y z ((objectHolds_converse i r x y).mp ((oriented_iff i r.converse x y).mpr hy.1))
            ((objectHolds_converse i r x z).mp ((oriented_iff i r.converse x z).mpr hz.1))
      · exact hm.tbox q hq x hx
  | reflexiveObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    cases r with
    | named rn | inverse rn =>
      exact ⟨fun hm => ⟨hm.reflexive rn (List.mem_cons_self ..),
          ⟨hm.tbox, hm.rules, hm.chains, fun s hs => hm.reflexive s (List.mem_cons_of_mem _ hs),
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains,
          fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ hax) (hm.reflexive s),
          hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
          hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
          hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | irreflexiveObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    cases r with
    | named rn | inverse rn =>
      exact ⟨fun hm => ⟨hm.irreflexive rn (List.mem_cons_self ..),
          ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive,
           fun s hs => hm.irreflexive s (List.mem_cons_of_mem _ hs),
           hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges,
           hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds,
           hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive,
          fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ hax) (hm.irreflexive s),
          hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges,
          hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds,
          hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | symmetricObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    cases r with
    | named rn =>
      exact ⟨fun hm => ⟨fun x y hxy => hm.rules _ (List.mem_cons_self ..) y x hxy,
          ⟨hm.tbox, fun e he => hm.rules e (List.mem_cons_of_mem _ he), hm.chains, hm.reflexive,
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox,
          fun e he => (List.mem_cons.mp he).elim (fun heq x y hxy => by rw [heq] at hxy ⊢; exact hax y x hxy) (hm.rules e),
          hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData,
          hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
          hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
          hm.negDataAssertions⟩⟩
    | inverse rn =>
      exact ⟨fun hm => ⟨fun x y hxy => hm.rules _ (List.mem_cons_self ..) x y hxy,
          ⟨hm.tbox, fun e he => hm.rules e (List.mem_cons_of_mem _ he), hm.chains, hm.reflexive,
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox,
          fun e he => (List.mem_cons.mp he).elim (fun heq x y hxy => by rw [heq] at hxy ⊢; exact hax x y hxy) (hm.rules e),
          hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData,
          hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
          hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
          hm.negDataAssertions⟩⟩
  | asymmetricObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    cases r with
    | named rn =>
      exact ⟨fun hm => ⟨hm.asymmetric rn (List.mem_cons_self ..),
          ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive,
           fun s hs => hm.asymmetric s (List.mem_cons_of_mem _ hs),
           hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
           hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
           hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive,
          fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ hax) (hm.asymmetric s),
          hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
          hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
          hm.dataAssertions, hm.negDataAssertions⟩⟩
    | inverse rn =>
      exact ⟨fun hm => ⟨fun x y hxy hyx => hm.asymmetric rn (List.mem_cons_self ..) y x hxy hyx,
          ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive,
           fun s hs => hm.asymmetric s (List.mem_cons_of_mem _ hs),
           hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
           hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
           hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive,
          fun s hs => (List.mem_cons.mp hs).elim (fun e x y hxy hyx => by rw [e] at hxy hyx; exact hax y x hxy hyx) (hm.asymmetric s),
          hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
          hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
          hm.dataAssertions, hm.negDataAssertions⟩⟩
  | transitiveObjectProperty r =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    cases r with
    | named rn =>
      constructor
      · intro hm
        refine ⟨fun x y z hxy hyz => hm.chains _ (List.mem_cons_self ..) x z ⟨y, hxy, z, hyz, rfl⟩,
          ⟨hm.tbox, hm.rules, fun c hc => hm.chains c (List.mem_cons_of_mem _ hc), hm.reflexive,
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
      · rintro ⟨hax, hm⟩
        refine ⟨hm.tbox, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
          hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
          hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
          hm.negDataAssertions⟩
        intro c hc x z hp
        rcases List.mem_cons.mp hc with rfl | hc
        · obtain ⟨y, hxy, w, hyw, rfl⟩ := hp; exact hax x y w hxy hyw
        · exact hm.chains c hc x z hp
    | inverse rn =>
      constructor
      · intro hm
        refine ⟨fun x y z hyx hzy => hm.chains _ (List.mem_cons_self ..) z x ⟨y, hzy, x, hyx, rfl⟩,
          ⟨hm.tbox, hm.rules, fun c hc => hm.chains c (List.mem_cons_of_mem _ hc), hm.reflexive,
           hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
           hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
      · rintro ⟨hax, hm⟩
        refine ⟨hm.tbox, hm.rules, ?_, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
          hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
          hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
          hm.negDataAssertions⟩
        intro c hc x z hp
        rcases List.mem_cons.mp hc with rfl | hc
        · obtain ⟨y, hxy, w, hyw, rfl⟩ := hp; exact hax w y x hyw hxy
        · exact hm.chains c hc x z hp
  | subDataProperty r s =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨hm.subData _ (List.mem_cons_self ..),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         fun pr hpr => hm.subData pr (List.mem_cons_of_mem _ hpr), hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, fun pr hpr => (List.mem_cons.mp hpr).elim (fun e => e ▸ hax) (hm.subData pr),
        hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions,
        hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | equivalentDataProperties rs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have heq_iff : (∀ e ∈ (allPairs rs).flatMap (fun (r, s) => [(r, s), (s, r)]),
        ∀ x y, i.dataProperties e.1 x y → i.dataProperties e.2 x y) ↔
        ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, i.dataProperties r x y ↔ i.dataProperties s x y := by
      have h1 : (∀ e ∈ (allPairs rs).flatMap (fun (r, s) => [(r, s), (s, r)]),
          ∀ x y, i.dataProperties e.1 x y → i.dataProperties e.2 x y) ↔
          ∀ pr ∈ allPairs rs, (∀ x y, i.dataProperties pr.1 x y ↔ i.dataProperties pr.2 x y) ∧
                              (∀ x y, i.dataProperties pr.2 x y ↔ i.dataProperties pr.1 x y) := by
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hall pr hpr
          have hlr := hall _ ⟨pr, hpr, Or.inl rfl⟩
          have hrl := hall _ ⟨pr, hpr, Or.inr rfl⟩
          exact ⟨fun x y => ⟨hlr x y, hrl x y⟩, fun x y => ⟨hrl x y, hlr x y⟩⟩
        · rintro hall e ⟨pr, hpr, rfl | rfl⟩ x y hxy
          · exact ((hall pr hpr).1 x y).mp hxy
          · exact ((hall pr hpr).1 x y).mpr hxy
      rw [h1, ← eq_allPairs_iff (R := fun r s => ∀ x y, i.dataProperties r x y ↔ i.dataProperties s x y)
        (fun _ _ _ => Iff.rfl) (fun _ _ h x y => (h x y).symm)]
    constructor
    · intro hm
      refine ⟨heq_iff.mp (fun e he => hm.subData e (List.mem_append_left _ he)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         fun e he => hm.subData e (List.mem_append_right _ he), hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        fun e he => (List.mem_append.mp he).elim (heq_iff.mpr hax e) (hm.subData e),
        hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions,
        hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩
  | disjointDataProperties rs =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hdisj : (∀ pr ∈ allPairs rs, ∀ x y, ¬ (i.dataProperties pr.1 x y ∧ i.dataProperties pr.2 x y)) ↔
        rs.Pairwise (fun r s => ∀ x y, ¬ (i.dataProperties r x y ∧ i.dataProperties s x y)) :=
      (pairwise_iff_allPairs (R := fun r s => ∀ x y, ¬ (i.dataProperties r x y ∧ i.dataProperties s x y)) rs).symm
    constructor
    · intro hm
      refine ⟨hdisj.mp (fun pr hpr => hm.disjointData pr (List.mem_append_left _ hpr)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, fun pr hpr => hm.disjointData pr (List.mem_append_right _ hpr), hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, fun pr hpr => (List.mem_append.mp hpr).elim (hdisj.mpr hax pr) (hm.disjointData pr),
        hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions,
        hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩
  | dataPropertyDomain dp c =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y hxy => (normClassExpr_iff_with lower i x c).mpr
            (hm.tbox _ (List.mem_cons_self ..) x ⟨y, hxy, i.literalDatatypeExt y⟩),
        ⟨fun q hq => hm.tbox q (List.mem_cons_of_mem _ hq), hm.rules, hm.chains, hm.reflexive,
         hm.irreflexive, hm.asymmetric, hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨?_, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · obtain ⟨y, hxy, _⟩ := hx
        exact (normClassExpr_iff_with lower i x c).mp (hax x y hxy)
      · exact hm.tbox q hq x hx
  | dataPropertyRange dp d =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨fun x y hy => (lower d i y).mp
          (hm.dataRanges _ (List.mem_cons_self ..) x y hy),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData,
         fun rd hrd => hm.dataRanges rd (List.mem_cons_of_mem _ hrd), hm.keys,
         hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
         hm.dataAssertions, hm.negDataAssertions⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, hm.subData, hm.disjointData, hm.funcData,
        fun rd hrd => (List.mem_cons.mp hrd).elim
          (fun e => e ▸ fun x y hy => (lower d i y).mpr (hax x y hy))
          (hm.dataRanges rd), hm.keys,
        hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        hm.dataAssertions, hm.negDataAssertions⟩⟩
  | functionalDataProperty dp =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨hm.funcData _ (List.mem_cons_self ..),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, fun r hr => hm.funcData r (List.mem_cons_of_mem _ hr),
         hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
         hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, hm.subData, hm.disjointData,
        fun r hr => (List.mem_cons.mp hr).elim (fun e => e ▸ hax) (hm.funcData r),
        hm.dataRanges, hm.keys, hm.classAssertions, hm.objAssertions, hm.negObjAssertions,
        hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | datatypeDefinition _ _ => simp [addAxiom] at h
  | hasKey c rs ds =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    constructor
    · intro hm
      refine ⟨fun x y hx hy hnx hny ho hd => hm.keys _ (List.mem_cons_self ..) x y
          ((normClassExpr_iff_with lower i x c).mp hx) ((normClassExpr_iff_with lower i y c).mp hy) hnx hny
          (by
            intro rn hrn
            obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrn
            obtain ⟨z, hnz, hxz, hyz⟩ := ho r hr
            exact ⟨z, hnz, (oriented_iff i r x z).mp hxz, (oriented_iff i r y z).mp hyz⟩) hd,
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges,
         fun k hk => hm.keys k (List.mem_cons_of_mem _ hk),
         hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
         hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, ?_, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩
      intro k hk x y hx hy hnx hny ho hd
      rcases List.mem_cons.mp hk with rfl | hk
      · refine hax x y ((normClassExpr_iff_with lower i x c).mpr hx) ((normClassExpr_iff_with lower i y c).mpr hy)
          hnx hny ?_ hd
        intro r hr'
        obtain ⟨z, hnz, hxz, hyz⟩ := ho (toOriented r) (List.mem_map_of_mem hr')
        exact ⟨z, hnz, (oriented_iff i r x z).mpr hxz, (oriented_iff i r y z).mpr hyz⟩
      · exact hm.keys k hk x y hx hy hnx hny ho hd
  | sameIndividuals inds =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hsame : (∀ pr ∈ allPairs inds, i.individuals pr.1 = i.individuals pr.2) ↔
        ∀ a ∈ inds, ∀ b ∈ inds, i.individuals a = i.individuals b := by
      have h1 := eq_allPairs_iff (R := fun a b => i.individuals a = i.individuals b)
        (fun _ => rfl) (fun _ _ e => e.symm) inds
      exact ⟨fun hall => h1.mpr fun p hp => ⟨hall p hp, (hall p hp).symm⟩,
             fun hall p hp => (h1.mp hall p hp).1⟩
    constructor
    · intro hm
      refine ⟨hsame.mp (fun pr hpr => hm.sameInds pr (List.mem_append_left _ hpr)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
         hm.objAssertions, hm.negObjAssertions,
         fun pr hpr => hm.sameInds pr (List.mem_append_right _ hpr),
         hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions,
        fun pr hpr => (List.mem_append.mp hpr).elim (hsame.mpr hax pr) (hm.sameInds pr),
        hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩
  | differentIndividuals inds =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    have hdiff : (∀ pr ∈ allPairs inds, i.individuals pr.1 ≠ i.individuals pr.2) ↔
        inds.Pairwise (fun a b => i.individuals a ≠ i.individuals b) :=
      (pairwise_iff_allPairs (R := fun a b => i.individuals a ≠ i.individuals b) inds).symm
    constructor
    · intro hm
      refine ⟨hdiff.mp (fun pr hpr => hm.diffInds pr (List.mem_append_left _ hpr)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
         hm.objAssertions, hm.negObjAssertions, hm.sameInds,
         fun pr hpr => hm.diffInds pr (List.mem_append_right _ hpr),
         hm.dataAssertions, hm.negDataAssertions⟩⟩
    · rintro ⟨hax, hm⟩
      refine ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds,
        fun pr hpr => (List.mem_append.mp hpr).elim (hdiff.mpr hax pr) (hm.diffInds pr),
        hm.dataAssertions, hm.negDataAssertions⟩
  | classAssertion c ind =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨(normClassExpr_iff_with lower i _ c).mpr (hm.classAssertions _ (List.mem_cons_self ..)),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
         fun ac hac => hm.classAssertions ac (List.mem_cons_of_mem _ hac), hm.objAssertions,
         hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
        fun ac hac => (List.mem_cons.mp hac).elim (fun e => e ▸ (normClassExpr_iff_with lower i _ c).mp hax)
          (hm.classAssertions ac), hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        hm.dataAssertions, hm.negDataAssertions⟩⟩
  | objectAssertion r a b =>
    cases r with
    | named rn | inverse rn =>
      simp only [addAxiom, Option.some.injEq] at h; subst h
      exact ⟨fun hm => ⟨hm.objAssertions _ (List.mem_cons_self ..),
          ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
           hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
           fun x hx => hm.objAssertions x (List.mem_cons_of_mem _ hx), hm.negObjAssertions,
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
          hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
          hm.classAssertions,
          fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hax) (hm.objAssertions x),
          hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | negativeObjectAssertion r a b =>
    cases r with
    | named rn | inverse rn =>
      simp only [addAxiom, Option.some.injEq] at h; subst h
      exact ⟨fun hm => ⟨hm.negObjAssertions _ (List.mem_cons_self ..),
          ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
           hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
           hm.objAssertions, fun x hx => hm.negObjAssertions x (List.mem_cons_of_mem _ hx),
           hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩,
        fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
          hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
          hm.classAssertions, hm.objAssertions,
          fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hax) (hm.negObjAssertions x),
          hm.sameInds, hm.diffInds, hm.dataAssertions, hm.negDataAssertions⟩⟩
  | dataAssertion dp a l =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨hm.dataAssertions _ (List.mem_cons_self ..),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
         hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
         fun x hx => hm.dataAssertions x (List.mem_cons_of_mem _ hx), hm.negDataAssertions⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
        hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hax) (hm.dataAssertions x),
        hm.negDataAssertions⟩⟩
  | negativeDataAssertion dp a l =>
    simp only [addAxiom, Option.some.injEq] at h; subst h
    exact ⟨fun hm => ⟨hm.negDataAssertions _ (List.mem_cons_self ..),
        ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
         hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
         hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
         fun x hx => hm.negDataAssertions x (List.mem_cons_of_mem _ hx)⟩⟩,
      fun ⟨hax, hm⟩ => ⟨hm.tbox, hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric,
        hm.disjoint, hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys,
        hm.classAssertions, hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds,
        hm.dataAssertions,
        fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hax) (hm.negDataAssertions x)⟩⟩

include lower in
private theorem foldlM_addAxiom_iff (i : Interpretation dm) (o : Ontology)
    (acc p : Problem) (h : o.foldlM addAxiom acc = some p) :
    p.Models i ↔ satisfies i o ∧ acc.Models i := by
  induction o generalizing acc with
  | nil =>
    simp [List.foldlM_nil, pure] at h; subst h
    exact ⟨fun hm => ⟨fun _ hmem => (List.not_mem_nil hmem).elim, hm⟩, fun ⟨_, hm⟩ => hm⟩
  | cons ax tail ih =>
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases ha : addAxiom acc ax with
    | none => simp [ha] at h
    | some acc' =>
      simp only [ha] at h
      rw [ih acc' h, addAxiom_models_iff_with lower i acc acc' ax ha]
      constructor
      · rintro ⟨htail, hax, hacc⟩
        exact ⟨fun a ha' => (List.mem_cons.mp ha').elim (fun e => e ▸ hax) (htail a), hacc⟩
      · rintro ⟨hcons, hacc⟩
        exact ⟨fun a ha' => hcons a (List.mem_cons_of_mem _ ha'), hcons ax (List.mem_cons_self ..), hacc⟩

include lower in
/-- Two-way model preservation for OWL 2 DL normalization into `SROIQD.Problem`. -/
theorem normalize_satisfies_iff_with (i : Interpretation dm) (o : Ontology) {p : Problem}
    (h : normalize o = some p) :
    satisfies i o ↔ p.Models i := by
  have hf := foldlM_addAxiom_iff lower i o {} p h
  have hempty : ({} : Problem).Models i :=
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨fun hs => hf.mpr ⟨hs, hempty⟩, fun hm => (hf.mp hm).1⟩

include lower in
theorem normalize_models_iff_with (i : Interpretation dm) (o : Ontology) {p : Problem}
    (h : normalize o = some p) :
    models i o ↔ models i p.toOntology :=
  ⟨fun ⟨assign, hsat⟩ => ⟨assign, (satisfies_toOntology_iff _ p).mpr ((normalize_satisfies_iff_with lower _ o h).mp hsat)⟩,
   fun ⟨assign, hsat⟩ => ⟨assign, (normalize_satisfies_iff_with lower _ o h).mpr ((satisfies_toOntology_iff _ p).mp hsat)⟩⟩

include lower in
theorem normalize_sat_iff_with {o : Ontology} {p : Problem} (h : normalize o = some p) :
    Satisfiable dm o ↔ Satisfiable dm p.toOntology :=
  ⟨fun ⟨i, hi⟩ => ⟨i, (normalize_models_iff_with lower i o h).mp hi⟩,
   fun ⟨i, hi⟩ => ⟨i, (normalize_models_iff_with lower i o h).mpr hi⟩⟩

end Lowering

theorem normClassExpr_iff (i : Interpretation datatypeMap) (x : i.Object) (c : ClassExpr) :
    classHolds i x c ↔ SROIQD.holds i x (normClassExpr c) :=
  normClassExpr_iff_with (fun d => (lowerSmallRanges d).2) i x c
theorem addAxiom_models_iff (i : Interpretation datatypeMap) (p p' : Problem) (ax : Axiom)
    (h : addAxiom p ax = some p') :
    p'.Models i ↔ axiomHolds i ax ∧ p.Models i :=
  addAxiom_models_iff_with (fun d => (lowerSmallRanges d).2) i p p' ax h
theorem normalize_satisfies_iff (i : Interpretation datatypeMap) (o : Ontology) {p : Problem}
    (h : normalize o = some p) :
    satisfies i o ↔ p.Models i :=
  normalize_satisfies_iff_with (fun d => (lowerSmallRanges d).2) i o h
theorem normalize_models_iff (i : Interpretation datatypeMap) (o : Ontology) {p : Problem}
    (h : normalize o = some p) :
    models i o ↔ models i p.toOntology :=
  normalize_models_iff_with (fun d => (lowerSmallRanges d).2) i o h
theorem normalize_sat_iff {o : Ontology} {p : Problem} (h : normalize o = some p) :
    Satisfiable datatypeMap o ↔ Satisfiable datatypeMap p.toOntology :=
  normalize_sat_iff_with (fun d => (lowerSmallRanges d).2) h

/-! ### Acyclic `DatatypeDefinition` Unfolding -/

abbrev DatatypeDefs := List (IRI × DataRange)

def expandOnce (defs : DatatypeDefs) : DataRange → DataRange
  | .datatype d => match defs.lookup d with | some body => body | none => .datatype d
  | .complement r => .complement (expandOnce defs r)
  | .intersection a b => .intersection (expandOnce defs a) (expandOnce defs b)
  | .union a b => .union (expandOnce defs a) (expandOnce defs b)
  | .oneOf ls => .oneOf ls
  | .restriction t fs => .restriction t fs

def expandRange (defs : DatatypeDefs) : Nat → DataRange → DataRange
  | 0, r => r
  | n + 1, r => expandRange defs n (expandOnce defs r)

def hasDefinedDatatype (defs : DatatypeDefs) : DataRange → Bool
  | .datatype d => (defs.lookup d).isSome
  | .complement r => hasDefinedDatatype defs r
  | .intersection a b => hasDefinedDatatype defs a || hasDefinedDatatype defs b
  | .union a b => hasDefinedDatatype defs a || hasDefinedDatatype defs b
  | .oneOf _ => false
  | .restriction t _ => (defs.lookup t).isSome

def collectDefs : Ontology → Option DatatypeDefs
  | [] => some []
  | .datatypeDefinition d body :: rest =>
    if d == literalDatatype || supportedDatatype d then none
    else (collectDefs rest).bind fun tail =>
      if (tail.lookup d).isSome then none
      else some ((d, body) :: tail)
  | _ :: rest => collectDefs rest

def defsAcyclic (defs : DatatypeDefs) : Bool :=
  defs.all fun (_, body) => !hasDefinedDatatype defs (expandRange defs defs.length body)

def unfoldDataRange (defs : DatatypeDefs) (r : DataRange) : Option DataRange :=
  if hasDefinedDatatype defs (expandRange defs (defs.length + 1) r) then none
  else some (expandRange defs (defs.length + 1) r)

def unfoldClassExpr (defs : DatatypeDefs) : ClassExpr → Option ClassExpr
  | .named c => some (.named c)
  | .complement c => (unfoldClassExpr defs c).map .complement
  | .intersection a b => (unfoldClassExpr defs a).bind fun a' => (unfoldClassExpr defs b).map (.intersection a')
  | .union a b => (unfoldClassExpr defs a).bind fun a' => (unfoldClassExpr defs b).map (.union a')
  | .oneOf inds => some (.oneOf inds)
  | .objectSome r c => (unfoldClassExpr defs c).map (.objectSome r)
  | .objectAll r c => (unfoldClassExpr defs c).map (.objectAll r)
  | .objectValue r a => some (.objectValue r a)
  | .objectSelf r => some (.objectSelf r)
  | .objectMin n r c => (unfoldClassExpr defs c).map (.objectMin n r)
  | .objectMax n r c => (unfoldClassExpr defs c).map (.objectMax n r)
  | .objectExact n r c => (unfoldClassExpr defs c).map (.objectExact n r)
  | .dataSome dp d => (unfoldDataRange defs d).map (.dataSome dp)
  | .dataAll dp d => (unfoldDataRange defs d).map (.dataAll dp)
  | .dataValue dp l => some (.dataValue dp l)
  | .dataMin n dp d => (unfoldDataRange defs d).map (.dataMin n dp)
  | .dataMax n dp d => (unfoldDataRange defs d).map (.dataMax n dp)
  | .dataExact n dp d => (unfoldDataRange defs d).map (.dataExact n dp)

def unfoldAxiom (defs : DatatypeDefs) : Axiom → Option (Option Axiom)
  | .datatypeDefinition _ _ => some none
  | .subClassOf a b => (unfoldClassExpr defs a).bind fun a' => (unfoldClassExpr defs b).map fun b' => some (.subClassOf a' b')
  | .equivalentClasses cs => (cs.mapM (unfoldClassExpr defs)).map fun cs' => some (.equivalentClasses cs')
  | .disjointClasses cs => (cs.mapM (unfoldClassExpr defs)).map fun cs' => some (.disjointClasses cs')
  | .disjointUnion h cs => (cs.mapM (unfoldClassExpr defs)).map fun cs' => some (.disjointUnion h cs')
  | .objectPropertyDomain r c => (unfoldClassExpr defs c).map fun c' => some (.objectPropertyDomain r c')
  | .objectPropertyRange r c => (unfoldClassExpr defs c).map fun c' => some (.objectPropertyRange r c')
  | .dataPropertyDomain dp c => (unfoldClassExpr defs c).map fun c' => some (.dataPropertyDomain dp c')
  | .dataPropertyRange dp d => (unfoldDataRange defs d).map fun d' => some (.dataPropertyRange dp d')
  | .hasKey c rs ds => (unfoldClassExpr defs c).map fun c' => some (.hasKey c' rs ds)
  | .classAssertion c a => (unfoldClassExpr defs c).map fun c' => some (.classAssertion c' a)
  | ax => some (some ax)

def unfoldOntology (o : Ontology) : Option (DatatypeDefs × Ontology) :=
  (collectDefs o).bind fun defs =>
    if defsAcyclic defs then
      (o.mapM (unfoldAxiom defs)).map fun axs => (defs, axs.filterMap id)
    else none

/-- Normalize an OWL 2 DL ontology with acyclic `DatatypeDefinition` unfolding. -/
def normalizeWithDefs (o : Ontology) : Option (DatatypeDefs × Problem) :=
  (unfoldOntology o).bind fun (defs, o') =>
    (normalize o').map (defs, ·)

private def DefsHold (i : Interpretation dm) (defs : DatatypeDefs) : Prop :=
  ∀ d body, defs.lookup d = some body → ∀ y, i.datatypes d y ↔ dataHolds i y body

private theorem expandOnce_iff {i : Interpretation dm} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) : ∀ (r : DataRange) (y : i.Data),
    dataHolds i y (expandOnce defs r) ↔ dataHolds i y r
  | .datatype d, y => by
    simp only [expandOnce]
    cases h : defs.lookup d with
    | none => rfl
    | some body => exact (hdefs d body h y).symm
  | .complement r, y => not_congr (expandOnce_iff hdefs r y)
  | .intersection a b, y => and_congr (expandOnce_iff hdefs a y) (expandOnce_iff hdefs b y)
  | .union a b, y => or_congr (expandOnce_iff hdefs a y) (expandOnce_iff hdefs b y)
  | .oneOf _, _ => Iff.rfl
  | .restriction _ _, _ => Iff.rfl

private theorem expandRange_iff {i : Interpretation dm} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) : ∀ (n : Nat) (r : DataRange) (y : i.Data),
    dataHolds i y (expandRange defs n r) ↔ dataHolds i y r
  | 0, _, _ => Iff.rfl
  | n + 1, r, y => (expandRange_iff hdefs n (expandOnce defs r) y).trans (expandOnce_iff hdefs r y)

private theorem expandOnce_of_noDef {defs : DatatypeDefs} :
    ∀ {r : DataRange}, hasDefinedDatatype defs r = false → expandOnce defs r = r
  | .datatype d, h => by
    simp only [hasDefinedDatatype, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    simp [expandOnce, h]
  | .complement r, h => congrArg DataRange.complement (expandOnce_of_noDef h)
  | .intersection a b, h => by
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    simp only [expandOnce, expandOnce_of_noDef h.1, expandOnce_of_noDef h.2]
  | .union a b, h => by
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    simp only [expandOnce, expandOnce_of_noDef h.1, expandOnce_of_noDef h.2]
  | .oneOf _, _ => rfl
  | .restriction _ _, _ => rfl

private theorem expandRange_comm (defs : DatatypeDefs) (n : Nat) (r : DataRange) :
    expandRange defs n (expandOnce defs r) = expandOnce defs (expandRange defs n r) := by
  induction n generalizing r with
  | zero => rfl
  | succ k ih => exact ih (expandOnce defs r)

private theorem expandRange_succ_eq {defs : DatatypeDefs} {n : Nat} {r : DataRange}
    (h : hasDefinedDatatype defs (expandRange defs n r) = false) :
    expandRange defs (n + 1) r = expandRange defs n r := by
  rw [expandRange, expandRange_comm, expandOnce_of_noDef h]

private theorem expandRange_complement (defs : DatatypeDefs) (n : Nat) (r : DataRange) :
    expandRange defs n (.complement r) = .complement (expandRange defs n r) := by
  induction n generalizing r with | zero => rfl | succ k ih => exact ih (expandOnce defs r)

private theorem expandRange_intersection (defs : DatatypeDefs) (n : Nat) (a b : DataRange) :
    expandRange defs n (.intersection a b) = .intersection (expandRange defs n a) (expandRange defs n b) := by
  induction n generalizing a b with | zero => rfl | succ k ih => exact ih _ _

private theorem expandRange_union (defs : DatatypeDefs) (n : Nat) (a b : DataRange) :
    expandRange defs n (.union a b) = .union (expandRange defs n a) (expandRange defs n b) := by
  induction n generalizing a b with | zero => rfl | succ k ih => exact ih _ _

private theorem expandRange_oneOf (defs : DatatypeDefs) (n : Nat) (ls : List Literal) :
    expandRange defs n (.oneOf ls) = .oneOf ls := by
  induction n with | zero => rfl | succ k ih => exact ih

private theorem expandRange_restriction (defs : DatatypeDefs) (n : Nat) (t : IRI) (fs : List Facet) :
    expandRange defs n (.restriction t fs) = .restriction t fs := by
  induction n with | zero => rfl | succ k ih => exact ih

private theorem expandRange_none (defs : DatatypeDefs) (n : Nat) {d : IRI} (h : defs.lookup d = none) :
    expandRange defs n (.datatype d) = .datatype d := by
  induction n with
  | zero => rfl
  | succ k ih => simp [expandRange, expandOnce, h, ih]

private theorem collectDefs_props {o : Ontology} {defs : DatatypeDefs}
    (h : collectDefs o = some defs) :
    (∀ d body, defs.lookup d = some body → .datatypeDefinition d body ∈ o) ∧
    (∀ d body, .datatypeDefinition d body ∈ o → defs.lookup d = some body) ∧
    (defs.lookup literalDatatype = none) ∧
    (∀ t, datatypeMap.builtin t → defs.lookup t = none) := by
  induction o generalizing defs with
  | nil =>
    simp [collectDefs] at h; subst h
    exact ⟨by simp, by simp, rfl, fun _ _ => rfl⟩
  | cons ax tail ih =>
    cases ax with
    | datatypeDefinition d' b' =>
      simp only [collectDefs] at h
      split at h
      · cases h
      · rename_i hnot
        obtain ⟨tailDefs, ht, h2⟩ := Option.bind_eq_some_iff.mp h
        split at h2
        · cases h2
        · rename_i hdup
          simp only [Option.some.injEq] at h2; subst h2
          obtain ⟨hmem, hrev, hlit, hbi⟩ := ih ht
          have hnot' : d' ≠ literalDatatype ∧ supportedDatatype d' = false := by
            simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hnot
            exact hnot
          have hdupNone : tailDefs.lookup d' = none := by
            cases hl : tailDefs.lookup d' with
            | none => rfl
            | some _ => simp [hl] at hdup
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro d body hl
            simp only [List.lookup] at hl
            cases hbeq : (d == d') with
            | true =>
              simp only [hbeq, Option.some.injEq] at hl
              have hd := beq_iff_eq.mp hbeq; subst hd hl
              exact List.mem_cons_self ..
            | false =>
              simp only [hbeq] at hl
              exact List.mem_cons_of_mem _ (hmem d body hl)
          · intro d body hm
            rcases List.mem_cons.mp hm with heq | hm'
            · cases heq; simp [List.lookup]
            · have htl := hrev d body hm'
              simp only [List.lookup]
              cases hbeq : (d == d') with
              | true =>
                have hd := beq_iff_eq.mp hbeq; subst hd
                rw [hdupNone] at htl; cases htl
              | false => exact htl
          · simp only [List.lookup]
            have hne : (literalDatatype == d') = false := beq_false_of_ne hnot'.1.symm
            rw [hne]; exact hlit
          · intro t hbt
            have hsup : supportedDatatype t = true := hbt
            have hne : t ≠ d' := fun e => by subst e; rw [hsup] at hnot'; cases hnot'.2
            simp only [List.lookup, beq_false_of_ne hne]
            exact hbi t hbt
    | _ =>
      obtain ⟨hmem, hrev, hlit, hbi⟩ := ih h
      exact ⟨fun d b hl => List.mem_cons_of_mem _ (hmem d b hl),
             fun d b hm => hrev d b ((List.mem_cons.mp hm).resolve_left (by intro e; cases e)),
             hlit, hbi⟩

private abbrev withExpandedDefs (i : Interpretation dm) (defs : DatatypeDefs)
    (hlit : defs.lookup literalDatatype = none)
    (hbi : ∀ t, dm.builtin t → defs.lookup t = none) : Interpretation dm :=
  { i with
    datatypes := fun t y =>
      match defs.lookup t with
      | some body => dataHolds i y (expandRange defs defs.length body)
      | none => i.datatypes t y
    literalDatatypeExt := fun y => by simp [hlit, i.literalDatatypeExt y]
    datatypeAgreement := fun t ht y => by simp [hbi t ht, i.datatypeAgreement t ht y] }

private theorem withExpandedDefs_dataHolds (i : Interpretation dm) {defs : DatatypeDefs}
    (hlit : defs.lookup literalDatatype = none)
    (hbi : ∀ t, dm.builtin t → defs.lookup t = none) :
    ∀ (r : DataRange) (y : i.Data),
      hasDefinedDatatype defs (expandRange defs (defs.length + 1) r) = false →
      (dataHolds (withExpandedDefs i defs hlit hbi) y r ↔
        dataHolds i y (expandRange defs (defs.length + 1) r))
  | .datatype d, y, _ => by
    simp only [dataHolds]
    cases hl : defs.lookup d with
    | none => rw [expandRange_none defs _ hl]; rfl
    | some body => simp [expandRange, expandOnce, hl]
  | .complement r, y, h => by
    rw [expandRange_complement] at h ⊢
    exact not_congr (withExpandedDefs_dataHolds i hlit hbi r y h)
  | .intersection a b, y, h => by
    rw [expandRange_intersection] at h ⊢
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    exact and_congr (withExpandedDefs_dataHolds i hlit hbi a y h.1)
      (withExpandedDefs_dataHolds i hlit hbi b y h.2)
  | .union a b, y, h => by
    rw [expandRange_union] at h ⊢
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    exact or_congr (withExpandedDefs_dataHolds i hlit hbi a y h.1)
      (withExpandedDefs_dataHolds i hlit hbi b y h.2)
  | .oneOf ls, y, _ => by rw [expandRange_oneOf]; rfl
  | .restriction t fs, y, h => by
    rw [expandRange_restriction] at h ⊢
    simp only [hasDefinedDatatype, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    simp [dataHolds, withExpandedDefs, h, facetHolds]

private theorem unfoldAxiom_eq_none {defs : DatatypeDefs} {ax : Axiom}
    (h : unfoldAxiom defs ax = some none) : ∃ d b, ax = .datatypeDefinition d b := by
  cases ax with
  | datatypeDefinition d b => exact ⟨d, b, rfl⟩
  | subClassOf a b =>
    obtain ⟨_, _, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h2; cases heq
  | equivalentClasses cs | disjointClasses cs | disjointUnion _ cs
  | objectPropertyDomain _ _ | objectPropertyRange _ _ | dataPropertyDomain _ _
  | dataPropertyRange _ _ | hasKey _ _ _ | classAssertion _ _ =>
    obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
  | _ => simp [unfoldAxiom] at h

private theorem unfoldClassExpr_fwd {i : Interpretation dm} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) {c c' : ClassExpr} (h : unfoldClassExpr defs c = some c')
    (x : i.Object) : classHolds i x c' ↔ classHolds i x c := by
  induction c generalizing c' x with
  | named _ | oneOf _ | objectValue _ _ | objectSelf _ | dataValue _ _ =>
    simp [unfoldClassExpr] at h; subst h; rfl
  | complement a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact not_congr (ih ha x)
  | intersection a b iha ihb =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact and_congr (iha ha x) (ihb hb x)
  | union a b iha ihb =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact or_congr (iha ha x) (ihb hb x)
  | objectSome r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact exists_congr fun y => and_congr Iff.rfl (ih ha y)
  | objectAll r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact forall_congr' fun y => imp_congr Iff.rfl (ih ha y)
  | objectMin n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
  | objectMax n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
  | objectExact n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have hAt : ∀ k, AtLeast k (fun y => objectHolds i r x y ∧ classHolds i y a') ↔
        AtLeast k (fun y => objectHolds i r x y ∧ classHolds i y a) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))
  | dataSome dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact exists_congr fun y => and_congr Iff.rfl (expandRange_iff hdefs _ d y)
  | dataAll dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact forall_congr' fun y => imp_congr Iff.rfl (expandRange_iff hdefs _ d y)
  | dataMin n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mp (hp y hy).2⟩⟩,
             fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mpr (hp y hy).2⟩⟩⟩
  | dataMax n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact not_congr
        ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mp (hp y hy).2⟩⟩,
         fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mpr (hp y hy).2⟩⟩⟩
  | dataExact n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      have hAt : ∀ k, AtLeast k (fun y => i.dataProperties dp x y ∧ dataHolds i y (expandRange defs (defs.length + 1) d)) ↔
          AtLeast k (fun y => i.dataProperties dp x y ∧ dataHolds i y d) := fun k =>
        ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mp (hp y hy).2⟩⟩,
         fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (expandRange_iff hdefs _ d y).mpr (hp y hy).2⟩⟩⟩
      exact and_congr (hAt n) (not_congr (hAt (n + 1)))

private theorem unfoldClassExpr_bwd (i : Interpretation dm) {defs : DatatypeDefs}
    (hlit : defs.lookup literalDatatype = none)
    (hbi : ∀ t, dm.builtin t → defs.lookup t = none)
    {c c' : ClassExpr} (h : unfoldClassExpr defs c = some c') (x : i.Object) :
    classHolds (withExpandedDefs i defs hlit hbi) x c ↔ classHolds i x c' := by
  induction c generalizing c' x with
  | named _ | oneOf _ | objectValue _ _ | objectSelf _ | dataValue _ _ =>
    simp [unfoldClassExpr] at h; subst h; rfl
  | complement a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact not_congr (ih ha x)
  | intersection a b iha ihb =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact and_congr (iha ha x) (ihb hb x)
  | union a b iha ihb =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact or_congr (iha ha x) (ihb hb x)
  | objectSome r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact exists_congr fun y => and_congr Iff.rfl (ih ha y)
  | objectAll r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact forall_congr' fun y => imp_congr Iff.rfl (ih ha y)
  | objectMin n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
  | objectMax n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
  | objectExact n r a ih =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have hAt : ∀ k, AtLeast k (fun y => objectHolds (withExpandedDefs i defs hlit hbi) r x y ∧
            classHolds (withExpandedDefs i defs hlit hbi) y a) ↔
        AtLeast k (fun y => objectHolds i r x y ∧ classHolds i y a') := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih ha y).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))
  | dataSome dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact exists_congr fun y => and_congr Iff.rfl (withExpandedDefs_dataHolds i hlit hbi d y hdef)
  | dataAll dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact forall_congr' fun y => imp_congr Iff.rfl (withExpandedDefs_dataHolds i hlit hbi d y hdef)
  | dataMin n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mp (hp y hy).2⟩⟩,
             fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mpr (hp y hy).2⟩⟩⟩
  | dataMax n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact not_congr
        ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mp (hp y hy).2⟩⟩,
         fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mpr (hp y hy).2⟩⟩⟩
  | dataExact n dp d =>
    obtain ⟨d', hd, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      have hAt : ∀ k, AtLeast k (fun y => (withExpandedDefs i defs hlit hbi).dataProperties dp x y ∧
              dataHolds (withExpandedDefs i defs hlit hbi) y d) ↔
          AtLeast k (fun y => i.dataProperties dp x y ∧ dataHolds i y (expandRange defs (defs.length + 1) d)) := fun k =>
        ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mp (hp y hy).2⟩⟩,
         fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (withExpandedDefs_dataHolds i hlit hbi d y hdef).mpr (hp y hy).2⟩⟩⟩
      exact and_congr (hAt n) (not_congr (hAt (n + 1)))

private theorem mapM_unfoldClassExpr {i1 i2 : Interpretation dm}
    (heq : i1.Object = i2.Object)
    {defs : DatatypeDefs} {cs cs' : List ClassExpr}
    (h : cs.mapM (unfoldClassExpr defs) = some cs')
    (hiff : ∀ c c', unfoldClassExpr defs c = some c' → ∀ x : i1.Object, classHolds i1 x c ↔ classHolds i2 (heq ▸ x) c') :
    (∀ c ∈ cs, ∃ c' ∈ cs', ∀ x : i1.Object, classHolds i1 x c ↔ classHolds i2 (heq ▸ x) c') ∧
    (∀ c' ∈ cs', ∃ c ∈ cs, ∀ x : i1.Object, classHolds i1 x c ↔ classHolds i2 (heq ▸ x) c') ∧
    (∀ (R : ClassExpr → ClassExpr → Prop) (S : ClassExpr → ClassExpr → Prop),
      (∀ c1 c1' c2 c2', (∀ x : i1.Object, classHolds i1 x c1 ↔ classHolds i2 (heq ▸ x) c1') →
        (∀ x : i1.Object, classHolds i1 x c2 ↔ classHolds i2 (heq ▸ x) c2') → (R c1 c2 ↔ S c1' c2')) →
      (cs.Pairwise R ↔ cs'.Pairwise S)) := by
  induction cs generalizing cs' with
  | nil => simp [List.mapM_nil, pure] at h; subst h; simp
  | cons a tail ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases ha : unfoldClassExpr defs a with
    | none => simp [ha] at h
    | some a' =>
      simp only [ha] at h
      cases hrest : tail.mapM (unfoldClassExpr defs) with
      | none => simp [hrest] at h
      | some rest =>
        simp only [hrest, pure, Option.some.injEq] at h; subst h
        obtain ⟨hf, hb, hpw⟩ := ih hrest
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact ⟨a', List.mem_cons_self .., hiff c a' ha⟩
          · obtain ⟨c', hc'', hi⟩ := hf c hc'
            exact ⟨c', List.mem_cons_of_mem _ hc'', hi⟩
        · intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc''
          · exact ⟨a, List.mem_cons_self .., hiff a c' ha⟩
          · obtain ⟨c, hc, hi⟩ := hb c' hc''
            exact ⟨c, List.mem_cons_of_mem _ hc, hi⟩
        · intro R S hRS
          simp only [List.pairwise_cons, hpw R S hRS]
          refine and_congr ?_ Iff.rfl
          constructor
          · intro h1 b' hb'
            obtain ⟨b, hb, hi⟩ := hb b' hb'
            exact (hRS a a' b b' (hiff a a' ha) hi).mp (h1 b hb)
          · intro h1 b hb
            obtain ⟨b', hb', hi⟩ := hf b hb
            exact (hRS a a' b b' (hiff a a' ha) hi).mpr (h1 b' hb')

private theorem unfoldAxiom_fwd {i : Interpretation dm} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) {ax ax' : Axiom} (h : unfoldAxiom defs ax = some (some ax'))
    (hax : axiomHolds i ax) : axiomHolds i ax' := by
  cases ax with
  | datatypeDefinition _ _ => simp [unfoldAxiom] at h
  | subClassOf a b =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, heq⟩ := Option.map_eq_some_iff.mp h2; cases heq
    intro x hx
    exact (unfoldClassExpr_fwd hdefs hb x).mpr (hax x ((unfoldClassExpr_fwd hdefs ha x).mp hx))
  | equivalentClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, hb, _⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    intro a' ha' b' hb' x
    obtain ⟨a, ha, hia⟩ := hb a' ha'
    obtain ⟨b, hbm, hib⟩ := hb b' hb'
    exact (hia x).symm.trans ((hax a ha b hbm x).trans (hib x))
  | disjointClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, _, hpw⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    exact (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mp hax
  | disjointUnion head cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, hb, hpw⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    refine ⟨fun x => ⟨fun hx => ?_, fun ⟨c', hc', hcx⟩ => ?_⟩,
      (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mp hax.2⟩
    · obtain ⟨c, hc, hcx⟩ := (hax.1 x).mp hx
      obtain ⟨c', hc', hi⟩ := hf c hc
      exact ⟨c', hc', (hi x).mp hcx⟩
    · obtain ⟨c, hc, hi⟩ := hb c' hc'
      exact (hax.1 x).mpr ⟨c, hc, (hi x).mpr hcx⟩
  | objectPropertyDomain r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc x).mpr (hax x y hxy)
  | objectPropertyRange r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc y).mpr (hax x y hxy)
  | dataPropertyDomain dp c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc x).mpr (hax x y hxy)
  | dataPropertyRange dp d =>
    obtain ⟨d', hd, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact fun x y hxy => (expandRange_iff hdefs _ d y).mpr (hax x y hxy)
  | hasKey c rs ds =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hx hy hnx hny ho hd =>
      hax x y ((unfoldClassExpr_fwd hdefs hc x).mp hx) ((unfoldClassExpr_fwd hdefs hc y).mp hy) hnx hny ho hd
  | classAssertion c a =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact (unfoldClassExpr_fwd hdefs hc _).mpr hax
  | _ => simp [unfoldAxiom] at h; subst h; exact hax

private theorem unfoldAxiom_bwd (i : Interpretation dm) {defs : DatatypeDefs}
    (hlit : defs.lookup literalDatatype = none)
    (hbi : ∀ t, dm.builtin t → defs.lookup t = none)
    {ax ax' : Axiom} (h : unfoldAxiom defs ax = some (some ax'))
    (hax' : axiomHolds i ax') : axiomHolds (withExpandedDefs i defs hlit hbi) ax := by
  cases ax with
  | datatypeDefinition _ _ => simp [unfoldAxiom] at h
  | subClassOf a b =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, heq⟩ := Option.map_eq_some_iff.mp h2; cases heq
    intro x hx
    exact (unfoldClassExpr_bwd i hlit hbi hb x).mpr (hax' x ((unfoldClassExpr_bwd i hlit hbi ha x).mp hx))
  | equivalentClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, _, _⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    intro a ha b hb x
    obtain ⟨a', ha', hia⟩ := hf a ha
    obtain ⟨b', hb', hib⟩ := hf b hb
    exact (hia x).trans ((hax' a' ha' b' hb' x).trans (hib x).symm)
  | disjointClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, _, hpw⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    exact (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mpr hax'
  | disjointUnion head cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, hb, hpw⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    refine ⟨fun x => ⟨fun hx => ?_, fun ⟨c, hc, hcx⟩ => ?_⟩,
      (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mpr hax'.2⟩
    · obtain ⟨c', hc', hcx⟩ := (hax'.1 x).mp hx
      obtain ⟨c, hc, hi⟩ := hb c' hc'
      exact ⟨c, hc, (hi x).mpr hcx⟩
    · obtain ⟨c', hc', hi⟩ := hf c hc
      exact (hax'.1 x).mpr ⟨c', hc', (hi x).mp hcx⟩
  | objectPropertyDomain r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc x).mpr (hax' x y hxy)
  | objectPropertyRange r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc y).mpr (hax' x y hxy)
  | dataPropertyDomain dp c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc x).mpr (hax' x y hxy)
  | dataPropertyRange dp d =>
    obtain ⟨d', hd, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact fun x y hxy => (withExpandedDefs_dataHolds i hlit hbi d y hdef).mpr (hax' x y hxy)
  | hasKey c rs ds =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hx hy hnx hny ho hd =>
      hax' x y ((unfoldClassExpr_bwd i hlit hbi hc x).mp hx) ((unfoldClassExpr_bwd i hlit hbi hc y).mp hy) hnx hny ho hd
  | classAssertion c a =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact (unfoldClassExpr_bwd i hlit hbi hc _).mpr hax'
  | subObjectPropertyChain rs s =>
    simp [unfoldAxiom] at h; subst h
    have hrp : ∀ (ps : List ObjectProperty) (x y : i.Object),
        rolePath (withExpandedDefs i defs hlit hbi) ps x y → rolePath i ps x y := fun ps => by
      induction ps with
      | nil => intro _ _ hp; exact hp
      | cons r tail ih =>
        intro x y ⟨z, hxz, hzy⟩
        exact ⟨z, hxz, ih z y hzy⟩
    exact fun x y hp => hax' x y (hrp rs x y hp)
  | _ => simp [unfoldAxiom] at h; subst h; exact hax'

private theorem mapM_unfold_mem {α β : Type} {xs : List α} {f : α → Option β} {ys : List β}
    (h : xs.mapM f = some ys) :
    (∀ x ∈ xs, ∃ y ∈ ys, f x = some y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, f x = some y) := by
  induction xs generalizing ys with
  | nil => simp [List.mapM_nil, pure] at h; subst h; simp
  | cons a tail ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      simp only [ha] at h
      cases hr : tail.mapM f with
      | none => simp [hr] at h
      | some bs =>
        simp only [hr, pure, Option.some.injEq] at h; subst h
        obtain ⟨hf, hb⟩ := ih hr
        refine ⟨fun x hx => ?_, fun y hy => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨b, List.mem_cons_self .., ha⟩
          · obtain ⟨y, hy, hfy⟩ := hf x hx'; exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨a, List.mem_cons_self .., ha⟩
          · obtain ⟨x, hx, hfx⟩ := hb y hy'; exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private theorem mem_of_lookup_defs {defs : DatatypeDefs} {d : IRI} {body : DataRange}
    (h : defs.lookup d = some body) : (d, body) ∈ defs := by
  induction defs with
  | nil => simp [List.lookup] at h
  | cons hd tail ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.lookup] at h
    cases hb : (d == k) with
    | true =>
      simp only [hb, Option.some.injEq] at h
      have hk := beq_iff_eq.mp hb; subst hk h; exact List.mem_cons_self ..
    | false => simp only [hb] at h; exact List.mem_cons_of_mem _ (ih h)

/-- Two-way satisfiability preservation for acyclic `DatatypeDefinition` unfolding. -/
theorem unfoldOntology_sat_iff_with {dm : DatatypeMap}
    (builtin : ∀ t, dm.builtin t → datatypeMap.builtin t) {o o' : Ontology} {defs : DatatypeDefs}
    (h : unfoldOntology o = some (defs, o')) :
    Satisfiable dm o ↔ Satisfiable dm o' := by
  unfold unfoldOntology at h
  obtain ⟨defs', hcd, h2⟩ := Option.bind_eq_some_iff.mp h
  cases hacyc : defsAcyclic defs' with
  | false => simp [hacyc] at h2
  | true =>
    simp only [hacyc, ↓reduceIte] at h2
    obtain ⟨axs, hmap, heq⟩ := Option.map_eq_some_iff.mp h2
    cases heq
    obtain ⟨hmem, hrev, hlit, hbi₀⟩ := collectDefs_props hcd
    have hbi : ∀ t, dm.builtin t → defs.lookup t = none := fun t ht => hbi₀ t (builtin t ht)
    obtain ⟨hf, hb⟩ := mapM_unfold_mem hmap
    constructor
    · rintro ⟨i, assign, hsat⟩
      let j := i.withAnonymous assign
      have hdefs : DefsHold j defs := fun d body hl => hsat _ (hmem d body hl)
      refine ⟨i, assign, fun ax' hax' => ?_⟩
      obtain ⟨opt, hopt, hval⟩ := List.mem_filterMap.mp hax'
      cases opt with
      | none => cases hval
      | some a' =>
        cases hval
        obtain ⟨ax, hax, huf⟩ := hb (some ax') hopt
        exact unfoldAxiom_fwd hdefs huf (hsat ax hax)
    · rintro ⟨i, assign, hsat⟩
      let j := i.withAnonymous assign
      let j' := withExpandedDefs j defs hlit hbi
      refine ⟨j', satisfies_models fun ax hax => ?_⟩
      cases ax with
      | datatypeDefinition d body =>
        have hlu := hrev d body hax
        have hno : hasDefinedDatatype defs (expandRange defs defs.length body) = false := by
          have hall := List.all_eq_true.mp hacyc (d, body) (mem_of_lookup_defs hlu)
          simpa using hall
        have hstep : expandRange defs (defs.length + 1) body = expandRange defs defs.length body :=
          expandRange_succ_eq hno
        have hno1 : hasDefinedDatatype defs (expandRange defs (defs.length + 1) body) = false :=
          hstep ▸ hno
        intro y
        change (match defs.lookup d with
          | some b => dataHolds j y (expandRange defs defs.length b)
          | none => j.datatypes d y) ↔ dataHolds j' y body
        rw [hlu, withExpandedDefs_dataHolds j hlit hbi body y hno1, hstep]
      | _ =>
        obtain ⟨opt, hopt, huf⟩ := hf _ hax
        cases opt with
        | none =>
          obtain ⟨d, b, hEq⟩ := unfoldAxiom_eq_none huf
          cases hEq
        | some ax' =>
          exact unfoldAxiom_bwd j hlit hbi huf (hsat ax' (List.mem_filterMap.mpr ⟨some ax', hopt, rfl⟩))

/-- Two-way satisfiability preservation for `normalizeWithDefs`. -/
theorem normalizeWithDefs_sat_iff_with {dm : DatatypeMap}
    (builtin : ∀ t, dm.builtin t → datatypeMap.builtin t)
    (lower : ∀ (d : DataRange) (i : Interpretation dm) (y : i.Data),
      dataHolds i y (lowerSmallRanges d).1 ↔ dataHolds i y d) {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    (h : normalizeWithDefs o = some (defs, p)) :
    Satisfiable dm o ↔ Satisfiable dm p.toOntology := by
  unfold normalizeWithDefs at h
  obtain ⟨⟨defs', o'⟩, huf, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p', hnorm, heq⟩ := Option.map_eq_some_iff.mp h2
  cases heq
  exact (unfoldOntology_sat_iff_with builtin huf).trans (normalize_sat_iff_with lower hnorm)

theorem unfoldOntology_sat_iff {o o' : Ontology} {defs : DatatypeDefs}
    (h : unfoldOntology o = some (defs, o')) :
    Satisfiable datatypeMap o ↔ Satisfiable datatypeMap o' :=
  unfoldOntology_sat_iff_with (fun _ ht => ht) h
theorem normalizeWithDefs_sat_iff {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    (h : normalizeWithDefs o = some (defs, p)) :
    Satisfiable datatypeMap o ↔ Satisfiable datatypeMap p.toOntology :=
  normalizeWithDefs_sat_iff_with (fun _ ht => ht) (fun d => (lowerSmallRanges d).2) h

/-- Certified consistency of a normalized OWL 2 DL `Ontology` (including acyclic
    `DatatypeDefinition` unfolding). -/
theorem checkOntologyConsistency_sound {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    {maxNodes : Nat} {e : Evidence}
    (hnorm : normalizeWithDefs o = some (defs, p)) (hchk : checkConsistency p maxNodes e = true) :
    (∀ r ∈ p.simpleRoles, RoleChains.SimpleRoles.Simple p.rules p.chains r) ∧
      if e.isModel then Satisfiable datatypeMap o else ¬ Satisfiable datatypeMap o := by
  have ⟨hsim, hsat⟩ := checkConsistency_sound hchk
  refine ⟨hsim, ?_⟩
  rw [normalizeWithDefs_sat_iff hnorm]
  exact hsat

/-- Direct reduction of an unfolded OWL 2 DL query axiom into `SROIQD.Inclusion`s. -/
def rawQueryToInclusions : Axiom → Option (List Inclusion)
  | .subClassOf a b => some [⟨normClassExpr a, normClassExpr b⟩]
  | .equivalentClasses [a, b] =>
    let na := normClassExpr a
    let nb := normClassExpr b
    some [⟨na, nb⟩, ⟨nb, na⟩]
  | .disjointClasses [a, b] =>
    some [⟨.conj (normClassExpr a) (normClassExpr b), .bottom⟩]
  | .classAssertion c (.named a) =>
    some [⟨.nom (.named a) true, normClassExpr c⟩]
  | .objectAssertion r (.named a) (.named b) =>
    some [⟨.nom (.named a) true, .hasValue (toOriented r) (.named b)⟩]
  | .negativeObjectAssertion r (.named a) (.named b) =>
    some [⟨.nom (.named a) true, (Concept.hasValue (toOriented r) (.named b)).dual⟩]
  | .dataAssertion dp (.named a) l =>
    some [⟨.nom (.named a) true, .dataValue dp l true⟩]
  | .negativeDataAssertion dp (.named a) l =>
    some [⟨.nom (.named a) true, .dataValue dp l false⟩]
  | .sameIndividuals [.named a, .named b] =>
    some [⟨.nom (.named a) true, .nom (.named b) true⟩]
  | .differentIndividuals [.named a, .named b] =>
    some [⟨.nom (.named a) true, .nom (.named b) false⟩]
  | _ => none

/-- Certified entailment reduction of a single OWL 2 DL query axiom `qAx` (with
    optional `DatatypeDefinition` unfolding) into normalized `SROIQD.Inclusion`s. -/
def queryToInclusions (defs : DatatypeDefs := []) (ax : Axiom) : Option (List Inclusion) :=
  (unfoldAxiom defs ax).bind fun
  | some ax' => rawQueryToInclusions ax'
  | none => none

private theorem rawQueryToInclusions_holds_iff (i : Interpretation datatypeMap)
    {ax : Axiom} {qs : List Inclusion} (h : rawQueryToInclusions ax = some qs) :
    axiomHolds i ax ↔ ∀ q ∈ qs, ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup := by
  cases ax with
  | subClassOf a b =>
    simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
    simp only [axiomHolds, List.mem_singleton, forall_eq, normClassExpr_iff]
  | equivalentClasses cs =>
    rcases cs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [rawQueryToInclusions] at h
    subst h
    simp only [axiomHolds, List.mem_cons, List.not_mem_nil, or_false, normClassExpr_iff]
    constructor
    · intro heq q hq x hx
      rcases hq with rfl | rfl
      · exact (heq a (Or.inl rfl) b (Or.inr rfl) x).mp hx
      · exact (heq b (Or.inr rfl) a (Or.inl rfl) x).mp hx
    · intro hinc c1 hc1 c2 hc2 x
      have hab := hinc ⟨normClassExpr a, normClassExpr b⟩ (Or.inl rfl) x
      have hba := hinc ⟨normClassExpr b, normClassExpr a⟩ (Or.inr rfl) x
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
      · exact Iff.rfl
      · exact ⟨hab, hba⟩
      · exact ⟨hba, hab⟩
      · exact Iff.rfl
  | disjointClasses cs =>
    rcases cs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [rawQueryToInclusions] at h
    subst h
    simp [axiomHolds, normClassExpr_iff, SROIQD.holds]
  | classAssertion c ind =>
    cases ind with
    | anonymous _ _ => simp [rawQueryToInclusions] at h
    | named a =>
      simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
      simp only [axiomHolds, List.mem_singleton, forall_eq, normClassExpr_iff, SROIQD.holds]
  | objectAssertion r ind1 ind2 =>
    cases ind1 with | anonymous _ _ => simp [rawQueryToInclusions] at h | named a =>
    cases ind2 with | anonymous _ _ => simp [rawQueryToInclusions] at h | named b =>
    simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
    simp only [axiomHolds, List.mem_singleton, forall_eq, Concept.hasValue, SROIQD.holds, oriented_iff]
    exact ⟨fun hr => ⟨i.individuals (.named b), hr, rfl⟩,
           fun ⟨_, hy, heq⟩ => heq ▸ hy⟩
  | negativeObjectAssertion r ind1 ind2 =>
    cases ind1 with | anonymous _ _ => simp [rawQueryToInclusions] at h | named a =>
    cases ind2 with | anonymous _ _ => simp [rawQueryToInclusions] at h | named b =>
    simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
    simp only [axiomHolds, List.mem_singleton, forall_eq, Concept.hasValue, Concept.dual,
      SROIQD.holds, oriented_iff]
    exact ⟨fun hnr y hy heq => hnr (heq ▸ hy),
           fun h hnr => h _ hnr rfl⟩
  | dataAssertion dp ind l =>
    cases ind with
    | anonymous _ _ => simp [rawQueryToInclusions] at h
    | named a =>
      simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
      simp only [axiomHolds, List.mem_singleton, forall_eq, SROIQD.holds]
  | negativeDataAssertion dp ind l =>
    cases ind with
    | anonymous _ _ => simp [rawQueryToInclusions] at h
    | named a =>
      simp only [rawQueryToInclusions, Option.some.injEq] at h; subst h
      simp only [axiomHolds, List.mem_singleton, forall_eq, SROIQD.holds]
  | sameIndividuals inds =>
    rcases inds with _ | ⟨ind1, _ | ⟨ind2, _ | _⟩⟩ <;> simp [rawQueryToInclusions] at h
    cases ind1 with | anonymous _ _ => simp at h | named a =>
    cases ind2 with | anonymous _ _ => simp at h | named b =>
    simp only [Option.some.injEq] at h; subst h
    simp only [axiomHolds, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, SROIQD.holds]
    constructor
    · intro hs
      exact hs (.named a) (Or.inl rfl) (.named b) (Or.inr rfl)
    · intro hab u hu v hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hab
      · exact hab.symm
      · rfl
  | differentIndividuals inds =>
    rcases inds with _ | ⟨ind1, _ | ⟨ind2, _ | _⟩⟩ <;> simp [rawQueryToInclusions] at h
    cases ind1 with | anonymous _ _ => simp at h | named a =>
    cases ind2 with | anonymous _ _ => simp at h | named b =>
    simp only [Option.some.injEq] at h; subst h
    simp [axiomHolds, SROIQD.holds]
  | _ => simp [rawQueryToInclusions] at h

private theorem unfoldAxiom_fwd_iff {i : Interpretation datatypeMap} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) {ax ax' : Axiom} (h : unfoldAxiom defs ax = some (some ax')) :
    axiomHolds i ax' ↔ axiomHolds i ax := by
  refine ⟨fun hax' => ?_, unfoldAxiom_fwd hdefs h⟩
  cases ax with
  | datatypeDefinition _ _ => simp [unfoldAxiom] at h
  | subClassOf a b =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, heq⟩ := Option.map_eq_some_iff.mp h2; cases heq
    exact fun x hx => (unfoldClassExpr_fwd hdefs hb x).mp (hax' x ((unfoldClassExpr_fwd hdefs ha x).mpr hx))
  | equivalentClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, _, _⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    intro a ha b hb x
    obtain ⟨a', ha', hia⟩ := hf a ha
    obtain ⟨b', hb', hib⟩ := hf b hb
    exact (hia x).trans ((hax' a' ha' b' hb' x).trans (hib x).symm)
  | disjointClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, _, hpw⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    exact (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mpr hax'
  | disjointUnion head cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, hb, hpw⟩ := mapM_unfoldClassExpr (i1 := i) (i2 := i) rfl hcs
      (fun c c' hc x => (unfoldClassExpr_fwd hdefs hc x).symm)
    refine ⟨fun x => ⟨fun hx => ?_, fun ⟨c, hc, hcx⟩ => ?_⟩,
      (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mpr hax'.2⟩
    · obtain ⟨c', hc', hcx⟩ := (hax'.1 x).mp hx
      obtain ⟨c, hc, hi⟩ := hb c' hc'
      exact ⟨c, hc, (hi x).mpr hcx⟩
    · obtain ⟨c', hc', hi⟩ := hf c hc
      exact (hax'.1 x).mpr ⟨c', hc', (hi x).mp hcx⟩
  | objectPropertyDomain r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc x).mp (hax' x y hxy)
  | objectPropertyRange r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc y).mp (hax' x y hxy)
  | dataPropertyDomain dp c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_fwd hdefs hc x).mp (hax' x y hxy)
  | dataPropertyRange dp d =>
    obtain ⟨d', hd, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    unfold unfoldDataRange at hd
    split at hd
    · cases hd
    · cases hd
      exact fun x y hxy => (expandRange_iff hdefs _ d y).mp (hax' x y hxy)
  | hasKey c rs ds =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hx hy hnx hny ho hd =>
      hax' x y ((unfoldClassExpr_fwd hdefs hc x).mpr hx) ((unfoldClassExpr_fwd hdefs hc y).mpr hy) hnx hny ho hd
  | classAssertion c a =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact (unfoldClassExpr_fwd hdefs hc _).mp hax'
  | _ => simp [unfoldAxiom] at h; subst h; exact hax'

private theorem unfoldAxiom_bwd_iff (i : Interpretation datatypeMap) {defs : DatatypeDefs}
    (hlit : defs.lookup literalDatatype = none)
    (hbi : ∀ t, datatypeMap.builtin t → defs.lookup t = none)
    {ax ax' : Axiom} (h : unfoldAxiom defs ax = some (some ax')) :
    axiomHolds (withExpandedDefs i defs hlit hbi) ax ↔ axiomHolds i ax' := by
  refine ⟨fun hax => ?_, unfoldAxiom_bwd i hlit hbi h⟩
  cases ax with
  | datatypeDefinition _ _ => simp [unfoldAxiom] at h
  | subClassOf a b =>
    obtain ⟨a', ha, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, heq⟩ := Option.map_eq_some_iff.mp h2; cases heq
    exact fun x hx => (unfoldClassExpr_bwd i hlit hbi hb x).mp (hax x ((unfoldClassExpr_bwd i hlit hbi ha x).mpr hx))
  | equivalentClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, hb, _⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    intro a' ha' b' hb' x
    obtain ⟨a, ha, hia⟩ := hb a' ha'
    obtain ⟨b, hbm, hib⟩ := hb b' hb'
    exact (hia x).symm.trans ((hax a ha b hbm x).trans (hib x))
  | disjointClasses cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨_, _, hpw⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    exact (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mp hax
  | disjointUnion head cs =>
    obtain ⟨cs', hcs, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    obtain ⟨hf, hb, hpw⟩ := mapM_unfoldClassExpr (i1 := withExpandedDefs i defs hlit hbi) (i2 := i) rfl hcs
      (fun c c' hc x => unfoldClassExpr_bwd i hlit hbi hc x)
    refine ⟨fun x => ⟨fun hx => ?_, fun ⟨c', hc', hcx⟩ => ?_⟩,
      (hpw _ _ fun _ _ _ _ h1 h2 => forall_congr' fun x => not_congr (and_congr (h1 x) (h2 x))).mp hax.2⟩
    · obtain ⟨c, hc, hcx⟩ := (hax.1 x).mp hx
      obtain ⟨c', hc', hi⟩ := hf c hc
      exact ⟨c', hc', (hi x).mp hcx⟩
    · obtain ⟨c, hc, hi⟩ := hb c' hc'
      exact (hax.1 x).mpr ⟨c, hc, (hi x).mpr hcx⟩
  | objectPropertyDomain r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc x).mp (hax x y hxy)
  | objectPropertyRange r c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc y).mp (hax x y hxy)
  | dataPropertyDomain dp c =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hxy => (unfoldClassExpr_bwd i hlit hbi hc x).mp (hax x y hxy)
  | dataPropertyRange dp d =>
    obtain ⟨d', hd, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    unfold unfoldDataRange at hd
    cases hdef : hasDefinedDatatype defs (expandRange defs (defs.length + 1) d) with
    | true => simp [hdef] at hd
    | false =>
      simp only [hdef, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd; subst hd
      exact fun x y hxy => (withExpandedDefs_dataHolds i hlit hbi d y hdef).mp (hax x y hxy)
  | hasKey c rs ds =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact fun x y hx hy hnx hny ho hd =>
      hax x y ((unfoldClassExpr_bwd i hlit hbi hc x).mpr hx) ((unfoldClassExpr_bwd i hlit hbi hc y).mpr hy) hnx hny ho hd
  | classAssertion c a =>
    obtain ⟨c', hc, heq⟩ := Option.map_eq_some_iff.mp h; cases heq
    exact (unfoldClassExpr_bwd i hlit hbi hc _).mp hax
  | subObjectPropertyChain rs s =>
    simp [unfoldAxiom] at h; subst h
    have hrp : ∀ (ps : List ObjectProperty) (x y : i.Object),
        rolePath i ps x y → rolePath (withExpandedDefs i defs hlit hbi) ps x y := fun ps => by
      induction ps with
      | nil => intro _ _ hp; exact hp
      | cons r tail ih =>
        intro x y ⟨z, hxz, hzy⟩
        exact ⟨z, hxz, ih z y hzy⟩
    exact fun x y hp => hax x y (hrp rs x y hp)
  | _ => simp [unfoldAxiom] at h; subst h; exact hax

/-- Top-level semantic claim for an M10 ontology query verdict over the source
    `Ontology` and source query `Axiom`. -/
def queryVerdictClaim (o : Ontology) (qAx : Axiom) : InclusionVerdict → Prop
  | .entailed => Satisfiable datatypeMap o ∧ Entails datatypeMap o [qAx]
  | .refuted => Satisfiable datatypeMap o ∧ ¬ Satisfiable datatypeMap (qAx :: o)
  | .independent => ¬ Entails datatypeMap o [qAx] ∧ Satisfiable datatypeMap (qAx :: o)
  | .inconsistent => ¬ Satisfiable datatypeMap o

private theorem normalizeWithDefs_props {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    (hnorm : normalizeWithDefs o = some (defs, p)) :
    ∃ o' : Ontology,
      unfoldOntology o = some (defs, o') ∧
      normalize o' = some p ∧
      (∀ i : Interpretation datatypeMap, satisfies i o → DefsHold i defs ∧ p.Models i) ∧
      (defs.lookup literalDatatype = none) ∧
      (∀ t, datatypeMap.builtin t → defs.lookup t = none) ∧
      (∀ i : Interpretation datatypeMap, ∀ hlit hbi, p.Models i →
        satisfies (withExpandedDefs i defs hlit hbi) o) := by
  unfold normalizeWithDefs at hnorm
  obtain ⟨⟨defs', o'⟩, huf, h2⟩ := Option.bind_eq_some_iff.mp hnorm
  obtain ⟨p', hnp, heq⟩ := Option.map_eq_some_iff.mp h2
  cases heq
  have huf' := huf
  unfold unfoldOntology at huf
  obtain ⟨defs'', hcd, h3⟩ := Option.bind_eq_some_iff.mp huf
  cases hacyc : defsAcyclic defs'' with
  | false => simp [hacyc] at h3
  | true =>
    simp only [hacyc, ↓reduceIte] at h3
    obtain ⟨axs, hmap, heq2⟩ := Option.map_eq_some_iff.mp h3
    cases heq2
    obtain ⟨hmem, hrev, hlit, hbi⟩ := collectDefs_props hcd
    obtain ⟨hf, hb⟩ := mapM_unfold_mem hmap
    refine ⟨axs.filterMap id, huf', hnp, ?_, hlit, hbi, ?_⟩
    · intro i hsat
      have hdefs : DefsHold i defs := fun d body hl => hsat _ (hmem d body hl)
      have hsat' : satisfies i (axs.filterMap id) := by
        intro ax' hax'
        obtain ⟨opt, hopt, hval⟩ := List.mem_filterMap.mp hax'
        cases opt with
        | none => cases hval
        | some a' =>
          cases hval
          obtain ⟨ax, hax, hufAx⟩ := hb (some ax') hopt
          exact unfoldAxiom_fwd hdefs hufAx (hsat ax hax)
      exact ⟨hdefs, (normalize_satisfies_iff i _ hnp).mp hsat'⟩
    · intro i hlit' hbi' hm
      have hsat' : satisfies i (axs.filterMap id) := (normalize_satisfies_iff i _ hnp).mpr hm
      intro ax hax
      cases ax with
      | datatypeDefinition d body =>
        have hlu := hrev d body hax
        have hno : hasDefinedDatatype defs (expandRange defs defs.length body) = false := by
          have hall := List.all_eq_true.mp hacyc (d, body) (mem_of_lookup_defs hlu)
          simpa using hall
        have hstep : expandRange defs (defs.length + 1) body = expandRange defs defs.length body :=
          expandRange_succ_eq hno
        have hno1 : hasDefinedDatatype defs (expandRange defs (defs.length + 1) body) = false :=
          hstep ▸ hno
        intro y
        change (match defs.lookup d with
          | some b => dataHolds i y (expandRange defs defs.length b)
          | none => i.datatypes d y) ↔ dataHolds (withExpandedDefs i defs hlit' hbi') y body
        rw [hlu, withExpandedDefs_dataHolds i hlit' hbi' body y hno1, hstep]
      | _ =>
        obtain ⟨opt, hopt, hufAx⟩ := hf _ hax
        cases opt with
        | none =>
          obtain ⟨d, b, hEq⟩ := unfoldAxiom_eq_none hufAx
          cases hEq
        | some ax' =>
          exact unfoldAxiom_bwd i hlit' hbi' hufAx
            (hsat' ax' (List.mem_filterMap.mpr ⟨some ax', hopt, rfl⟩))

private theorem dataHolds_withAnonymous_eq (i : Interpretation datatypeMap)
    (assign : String → String → i.Object) (y : i.Data) (r : DataRange) :
    dataHolds (i.withAnonymous assign) y r = dataHolds i y r := by
  induction r with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement a ih => exact congrArg Not ih
  | intersection a b iha ihb => exact propext (and_congr (iff_of_eq iha) (iff_of_eq ihb))
  | union a b iha ihb => exact propext (or_congr (iff_of_eq iha) (iff_of_eq ihb))

private theorem query_entails_iff_inclusions {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    {qAx : Axiom} {qs : List Inclusion}
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hq : queryToInclusions defs qAx = some qs)
    (hnoAnon : ∀ q ∈ qs, q.sub.hasNoAnon = true ∧ q.sup.hasNoAnon = true) :
    (Entails datatypeMap o [qAx] ↔
      ∀ q ∈ qs, Entails datatypeMap p.toOntology [.subClassOf q.sub.toClassExpr q.sup.toClassExpr]) ∧
    (Satisfiable datatypeMap (qAx :: o) ↔
      ∃ i : Interpretation datatypeMap, p.Models i ∧ ∀ q ∈ qs, ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup) := by
  obtain ⟨o', _, _, hfwd, hlit, hbi, hbwd⟩ := normalizeWithDefs_props hnorm
  unfold queryToInclusions at hq
  obtain ⟨opt, hufQ, hraw⟩ := Option.bind_eq_some_iff.mp hq
  cases opt with
  | none => cases hraw
  | some qAx' =>
    have hqHolds : ∀ i : Interpretation datatypeMap,
        axiomHolds i qAx' ↔ ∀ q ∈ qs, ∀ x, SROIQD.holds i x q.sub → SROIQD.holds i x q.sup :=
      fun i => rawQueryToInclusions_holds_iff i hraw
    constructor
    · constructor
      · intro hent q hqMem i ⟨assign, hsatP⟩
        let j := i.withAnonymous assign
        have hm : p.Models j := (satisfies_toOntology_iff j p).mp hsatP
        let j' := withExpandedDefs j defs hlit hbi
        have hsatO : satisfies j' o := hbwd j hlit hbi hm
        obtain ⟨assign', hqSat⟩ := hent j' (satisfies_models hsatO)
        have hcomm : j'.withAnonymous assign' = withExpandedDefs (j.withAnonymous assign') defs hlit hbi := by
          dsimp only [j', Interpretation.withAnonymous, withExpandedDefs]
          congr 1; funext t y
          cases defs.lookup t with
          | none => rfl
          | some body => exact (dataHolds_withAnonymous_eq j assign' y _).symm
        have hqAx : axiomHolds (withExpandedDefs (j.withAnonymous assign') defs hlit hbi) qAx :=
          hcomm ▸ hqSat qAx (List.mem_singleton_self _)
        have hqAx' : axiomHolds (j.withAnonymous assign') qAx' :=
          (unfoldAxiom_bwd_iff (j.withAnonymous assign') hlit hbi hufQ).mp hqAx
        have hinc : ∀ x, SROIQD.holds (j.withAnonymous assign') x q.sub →
            SROIQD.holds (j.withAnonymous assign') x q.sup :=
          (hqHolds (j.withAnonymous assign')).mp hqAx' q hqMem
        have ⟨hsubNo, hsupNo⟩ := hnoAnon q hqMem
        refine ⟨assign, fun ax hax => ?_⟩
        rw [List.mem_singleton.mp hax]
        intro x hx
        rw [toClassExpr_iff] at hx ⊢
        have hx' := (holds_withAnonymous_of_noAnon j assign' x q.sub hsubNo).mpr hx
        exact (holds_withAnonymous_of_noAnon j assign' x q.sup hsupNo).mp (hinc x hx')
      · intro hall i ⟨assign, hsatO⟩
        let j := i.withAnonymous assign
        obtain ⟨hdefs, hm⟩ := hfwd j hsatO
        have hmodP : models j p.toOntology :=
          satisfies_models ((satisfies_toOntology_iff j p).mpr hm)
        have hallJ : ∀ q ∈ qs, ∀ x, SROIQD.holds j x q.sub → SROIQD.holds j x q.sup := by
          intro q hqMem x hx
          obtain ⟨assign', hqSat⟩ := hall q hqMem j hmodP
          have hax := hqSat _ (List.mem_singleton_self _)
          have ⟨hsubNo, hsupNo⟩ := hnoAnon q hqMem
          have hx' : classHolds (j.withAnonymous assign') x q.sub.toClassExpr :=
            (toClassExpr_iff (j.withAnonymous assign') x q.sub).mpr
              ((holds_withAnonymous_of_noAnon j assign' x q.sub hsubNo).mpr hx)
          have hy' := (toClassExpr_iff (j.withAnonymous assign') x q.sup).mp (hax x hx')
          exact (holds_withAnonymous_of_noAnon j assign' x q.sup hsupNo).mp hy'
        have hqAx' : axiomHolds j qAx' := (hqHolds j).mpr hallJ
        have hqAx : axiomHolds j qAx := (unfoldAxiom_fwd_iff hdefs hufQ).mp hqAx'
        exact ⟨assign, fun ax hax => (List.mem_singleton.mp hax) ▸ hqAx⟩
    · constructor
      · rintro ⟨i, assign, hsat⟩
        let j := i.withAnonymous assign
        have hsatO : satisfies j o := fun ax hax => hsat ax (List.mem_cons_of_mem _ hax)
        have hqAx : axiomHolds j qAx := hsat qAx (List.mem_cons_self ..)
        obtain ⟨hdefs, hm⟩ := hfwd j hsatO
        have hqAx' : axiomHolds j qAx' := (unfoldAxiom_fwd_iff hdefs hufQ).mpr hqAx
        exact ⟨j, hm, (hqHolds j).mp hqAx'⟩
      · rintro ⟨i, hm, hall⟩
        let j' := withExpandedDefs i defs hlit hbi
        have hsatO : satisfies j' o := hbwd i hlit hbi hm
        have hqAx' : axiomHolds i qAx' := (hqHolds i).mpr hall
        have hqAx : axiomHolds j' qAx := (unfoldAxiom_bwd_iff i hlit hbi hufQ).mpr hqAx'
        exact ⟨j', satisfies_models fun ax hax =>
          (List.mem_cons.mp hax).elim (fun e => e ▸ hqAx) (hsatO ax)⟩

/-- M10 soundness theorem for single-inclusion OWL 2 DL queries (`SubClassOf`,
    binary `DisjointClasses`, `ClassAssertion`, `ObjectPropertyAssertion`,
    `NegativeObjectPropertyAssertion`, `DataPropertyAssertion`,
    `NegativeDataPropertyAssertion`, binary `SameIndividual`, and binary
    `DifferentIndividuals`) over a normalized ontology. -/
theorem checkOntologyQuery_sound {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    {qAx : Axiom} {q : Inclusion} {maxNodes : Nat} {e : InclusionEvidence}
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hq : queryToInclusions defs qAx = some [q])
    (hchk : checkInclusion p q maxNodes e = true) :
    queryVerdictClaim o qAx e.verdict := by
  have hvc := checkInclusion_sound hchk
  have hchk' := hchk
  simp only [checkInclusion, Bool.and_eq_true] at hchk'
  have hsubNo : q.sub.hasNoAnon = true := hchk'.1.1.1.1
  have hsupNo : q.sup.hasNoAnon = true := hchk'.1.1.1.2
  have ⟨hentIff, hsatIff⟩ := query_entails_iff_inclusions hnorm hq
    (fun q' hq' => (List.mem_singleton.mp hq') ▸ ⟨hsubNo, hsupNo⟩)
  have hsatO : Satisfiable datatypeMap o ↔ Satisfiable datatypeMap p.toOntology :=
    normalizeWithDefs_sat_iff hnorm
  have hincSat : Satisfiable datatypeMap (inclusionProblem p q).toOntology ↔
      (∃ i : Interpretation datatypeMap, p.Models i ∧ ∀ q' ∈ [q], ∀ x, SROIQD.holds i x q'.sub → SROIQD.holds i x q'.sup) := by
    rw [satisfiable_iff_sat (inclusionProblem p q) rfl]
    constructor
    · rintro ⟨i, hm, _⟩
      refine ⟨i, ⟨fun ax hax => hm.tbox ax (List.mem_cons_of_mem _ hax),
        hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩, fun q' hq' => (List.mem_singleton.mp hq') ▸ hm.tbox q (List.mem_cons_self ..)⟩
    · rintro ⟨i, hm, hq1⟩
      obtain ⟨x0⟩ := i.objectNonempty
      refine ⟨i, ⟨fun ax hax => (List.mem_cons.mp hax).elim
          (fun e => e ▸ hq1 q (List.mem_singleton_self _)) (hm.tbox ax),
        hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
        hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
        hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
        hm.negDataAssertions⟩, x0, trivial⟩
  cases hv : e.verdict <;> simp only [hv, verdictClaim] at hvc <;> simp only [queryVerdictClaim]
  · exact ⟨hsatO.mpr hvc.1, hentIff.mpr fun q' hq' => (List.mem_singleton.mp hq') ▸ hvc.2⟩
  · exact ⟨hsatO.mpr hvc.1, fun hs => hvc.2 (hincSat.mpr (hsatIff.mp hs))⟩
  · exact ⟨fun he => hvc.1 (hentIff.mp he q (List.mem_singleton_self _)),
           hsatIff.mpr (hincSat.mp hvc.2)⟩
  · exact fun hs => hvc (hsatO.mp hs)

/-- Combined verdict for binary `EquivalentClasses` queries (`[q1, q2]`). -/
def equivVerdict (e1 e2 : InclusionEvidence) : InclusionVerdict :=
  if e1.verdict == .inconsistent || e2.verdict == .inconsistent then .inconsistent
  else if e1.verdict == .entailed && e2.verdict == .entailed then .entailed
  else if e1.verdict == .refuted || e2.verdict == .refuted then .refuted
  else .independent

/-- Semantic claim for a binary `EquivalentClasses` query verdict. -/
def equivQueryVerdictClaim (o : Ontology) (qAx : Axiom) : InclusionVerdict → Prop
  | .entailed => Satisfiable datatypeMap o ∧ Entails datatypeMap o [qAx]
  | .refuted => Satisfiable datatypeMap o ∧ ¬ Satisfiable datatypeMap (qAx :: o)
  | .independent => ¬ Entails datatypeMap o [qAx]
  | .inconsistent => ¬ Satisfiable datatypeMap o

/-- M10 soundness theorem for binary `EquivalentClasses` queries (`[q1, q2]`). -/
theorem checkOntologyEquivQuery_sound {o : Ontology} {defs : DatatypeDefs} {p : Problem}
    {qAx : Axiom} {q1 q2 : Inclusion} {maxNodes : Nat} {e1 e2 : InclusionEvidence}
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hq : queryToInclusions defs qAx = some [q1, q2])
    (hchk1 : checkInclusion p q1 maxNodes e1 = true)
    (hchk2 : checkInclusion p q2 maxNodes e2 = true) :
    equivQueryVerdictClaim o qAx (equivVerdict e1 e2) := by
  have hvc1 := checkInclusion_sound hchk1
  have hvc2 := checkInclusion_sound hchk2
  have hc1 := hchk1; simp only [checkInclusion, Bool.and_eq_true] at hc1
  have hc2 := hchk2; simp only [checkInclusion, Bool.and_eq_true] at hc2
  have ⟨hentIff, hsatIff⟩ := query_entails_iff_inclusions hnorm hq (fun q hq' => by
    rcases List.mem_cons.mp hq' with rfl | hq2
    · exact ⟨hc1.1.1.1.1, hc1.1.1.1.2⟩
    · rcases List.mem_singleton.mp hq2 with rfl
      exact ⟨hc2.1.1.1.1, hc2.1.1.1.2⟩)
  have hsatO : Satisfiable datatypeMap o ↔ Satisfiable datatypeMap p.toOntology :=
    normalizeWithDefs_sat_iff hnorm
  have hinc1 : (∃ i : Interpretation datatypeMap, p.Models i ∧ ∀ x, SROIQD.holds i x q1.sub → SROIQD.holds i x q1.sup) →
      Satisfiable datatypeMap (inclusionProblem p q1).toOntology := by
    rintro ⟨i, hm, hq1⟩
    rw [satisfiable_iff_sat (inclusionProblem p q1) rfl]
    obtain ⟨x0⟩ := i.objectNonempty
    exact ⟨i, ⟨fun ax hax => (List.mem_cons.mp hax).elim (fun e => e ▸ hq1) (hm.tbox ax),
      hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩, x0, trivial⟩
  have hinc2 : (∃ i : Interpretation datatypeMap, p.Models i ∧ ∀ x, SROIQD.holds i x q2.sub → SROIQD.holds i x q2.sup) →
      Satisfiable datatypeMap (inclusionProblem p q2).toOntology := by
    rintro ⟨i, hm, hq2⟩
    rw [satisfiable_iff_sat (inclusionProblem p q2) rfl]
    obtain ⟨x0⟩ := i.objectNonempty
    exact ⟨i, ⟨fun ax hax => (List.mem_cons.mp hax).elim (fun e => e ▸ hq2) (hm.tbox ax),
      hm.rules, hm.chains, hm.reflexive, hm.irreflexive, hm.asymmetric, hm.disjoint,
      hm.subData, hm.disjointData, hm.funcData, hm.dataRanges, hm.keys, hm.classAssertions,
      hm.objAssertions, hm.negObjAssertions, hm.sameInds, hm.diffInds, hm.dataAssertions,
      hm.negDataAssertions⟩, x0, trivial⟩
  cases hv1 : e1.verdict <;> cases hv2 : e2.verdict <;>
    simp only [hv1, hv2, verdictClaim] at hvc1 hvc2 <;>
    simp only [equivVerdict, hv1, hv2, equivQueryVerdictClaim]
  all_goals try exact fun hs => hvc1 (hsatO.mp hs)
  all_goals try exact fun hs => hvc2 (hsatO.mp hs)
  all_goals try exact ⟨hsatO.mpr hvc1.1, fun hs => by
    obtain ⟨i, hm, hall⟩ := hsatIff.mp hs
    exact hvc1.2 (hinc1 ⟨i, hm, hall q1 (by simp)⟩)⟩
  all_goals try exact ⟨hsatO.mpr hvc2.1, fun hs => by
    obtain ⟨i, hm, hall⟩ := hsatIff.mp hs
    exact hvc2.2 (hinc2 ⟨i, hm, hall q2 (by simp)⟩)⟩
  all_goals try exact fun he => hvc1.1 (hentIff.mp he q1 (by simp))
  all_goals try exact fun he => hvc2.1 (hentIff.mp he q2 (by simp))
  · refine ⟨hsatO.mpr hvc1.1, hentIff.mpr fun q hq' => ?_⟩
    rcases List.mem_cons.mp hq' with rfl | hq2
    · exact hvc1.2
    · rcases List.mem_singleton.mp hq2 with rfl
      exact hvc2.2

/-! ### M3 Definitional Conservative Extension, Fresh-Name Allocation & Worked Checkpoint -/

/-- Check whether class IRI `x` occurs in `ClassExpr`. -/
def exprUsesClass (x : IRI) : ClassExpr → Bool
  | .named c => c == x
  | .complement a => exprUsesClass x a
  | .intersection a b | .union a b => exprUsesClass x a || exprUsesClass x b
  | .oneOf _ | .objectValue _ _ | .objectSelf _ | .dataSome _ _
  | .dataAll _ _ | .dataValue _ _ | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => false
  | .objectSome _ a | .objectAll _ a | .objectMin _ _ a | .objectMax _ _ a | .objectExact _ _ a =>
    exprUsesClass x a

/-- Check whether class IRI `x` occurs in `Axiom`. -/
def axiomUsesClass (x : IRI) : Axiom → Bool
  | .subClassOf a b => exprUsesClass x a || exprUsesClass x b
  | .equivalentClasses cs | .disjointClasses cs => cs.any (exprUsesClass x)
  | .disjointUnion h cs => (h == x) || cs.any (exprUsesClass x)
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c
  | .hasKey c _ _ | .classAssertion c _ => exprUsesClass x c
  | _ => false

/-- Check whether class IRI `x` occurs in `Ontology`. -/
def ontologyUsesClass (x : IRI) (o : Ontology) : Bool :=
  o.any (axiomUsesClass x)

/-- Boolean freshness check across an ontology closure and query list,
    also excluding reserved `owl:Thing` and `owl:Nothing`. -/
def checkFreshClass (X : IRI) (o q : Ontology) : Bool :=
  !(thing == X) && !(nothing == X) && !ontologyUsesClass X o && !ontologyUsesClass X q

/-- Allocate a fresh auxiliary class IRI not occurring across `o` and `q`. -/
def freshClassIRI (o q : Ontology) (base : String := "urn:sabrina:aux:C") : IRI :=
  let rec go (k : Nat) (fuel : Nat) : IRI :=
    let cand := s!"{base}{k}"
    if checkFreshClass cand o q then cand
    else match fuel with
      | 0 => cand
      | fuel' + 1 => go (k + 1) fuel'
  go 0 ((o.length + q.length) * 16 + 64)

theorem checkFreshClass_iff (X : IRI) (o q : Ontology) :
    checkFreshClass X o q = true ↔
      (thing == X) = false ∧ (nothing == X) = false ∧
      ontologyUsesClass X o = false ∧ ontologyUsesClass X q = false := by
  simp [checkFreshClass, and_assoc]

/-- Reinterpret a single non-reserved class symbol `X` as `P` while preserving
    the object domain, data domain, properties, named individuals, anonymous
    individuals, and datatypes. -/
abbrev withClass {D : DatatypeMap} (i : Interpretation D) (X : IRI)
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) : Interpretation D :=
  { i with
    classes := fun c x => if c == X then P x else i.classes c x
    thingExt := fun x => by simp [hthing, i.thingExt x]
    nothingExt := fun x => by simp [hnothing, i.nothingExt x] }

/-- Internal auxiliary class extensions never alter named-individual membership
    (`i.named`), preserving `HasKey` semantics identically. -/
theorem withClass_named {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) (x : i.Object) :
    (withClass i X hthing hnothing P).named x ↔ i.named x := Iff.rfl

private theorem dataHolds_withClass_eq {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) (y : i.Data) (r : DataRange) :
    dataHolds (withClass i X hthing hnothing P) y r = dataHolds i y r := by
  induction r with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement a ih => exact congrArg Not ih
  | intersection a b iha ihb => exact propext (and_congr (iff_of_eq iha) (iff_of_eq ihb))
  | union a b iha ihb => exact propext (or_congr (iff_of_eq iha) (iff_of_eq ihb))

private theorem rolePath_withClass_iff {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) (rs : List ObjectProperty) (x y : i.Object) :
    rolePath (withClass i X hthing hnothing P) rs x y ↔ rolePath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih => exact exists_congr fun z => and_congr Iff.rfl (ih z)

theorem classHolds_withClass_self {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) (x : i.Object) :
    classHolds (withClass i X hthing hnothing P) x (.named X) ↔ P x := by
  simp [classHolds]

theorem classHolds_withClass_of_not_uses {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) {c : ClassExpr} (h : exprUsesClass X c = false) (x : i.Object) :
    classHolds (withClass i X hthing hnothing P) x c ↔ classHolds i x c := by
  induction c generalizing x with
  | named iri =>
    simp only [exprUsesClass] at h
    simp [classHolds, h]
  | complement a ih =>
    simp only [exprUsesClass] at h
    exact not_congr (ih h x)
  | intersection a b iha ihb =>
    simp only [exprUsesClass, Bool.or_eq_false_iff] at h
    exact and_congr (iha h.1 x) (ihb h.2 x)
  | union a b iha ihb =>
    simp only [exprUsesClass, Bool.or_eq_false_iff] at h
    exact or_congr (iha h.1 x) (ihb h.2 x)
  | oneOf _ | objectValue _ _ | objectSelf _ | dataValue _ _ => rfl
  | objectSome r a ih =>
    simp only [exprUsesClass] at h
    exact exists_congr fun y => and_congr Iff.rfl (ih h y)
  | objectAll r a ih =>
    simp only [exprUsesClass] at h
    exact forall_congr' fun y => imp_congr Iff.rfl (ih h y)
  | objectMin n r a ih =>
    simp only [exprUsesClass] at h
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mpr (hp y hy).2⟩⟩⟩
  | objectMax n r a ih =>
    simp only [exprUsesClass] at h
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mpr (hp y hy).2⟩⟩⟩
  | objectExact n r a ih =>
    simp only [exprUsesClass] at h
    have hAt : ∀ k, AtLeast k (fun y => objectHolds (withClass i X hthing hnothing P) r x y ∧
            classHolds (withClass i X hthing hnothing P) y a) ↔
        AtLeast k (fun y => objectHolds i r x y ∧ classHolds i y a) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (ih h y).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr Iff.rfl (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d))
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d))
  | dataMin n dp d =>
    exact ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mp (hp y hy).2⟩⟩,
           fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mpr (hp y hy).2⟩⟩⟩
  | dataMax n dp d =>
    exact not_congr
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mpr (hp y hy).2⟩⟩⟩
  | dataExact n dp d =>
    have hAt : ∀ k, AtLeast k (fun y => (withClass i X hthing hnothing P).dataProperties dp x y ∧
            dataHolds (withClass i X hthing hnothing P) y d) ↔
        AtLeast k (fun y => i.dataProperties dp x y ∧ dataHolds i y d) := fun k =>
      ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mp (hp y hy).2⟩⟩,
       fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun y hy => ⟨(hp y hy).1, (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d)).mpr (hp y hy).2⟩⟩⟩
    exact and_congr (hAt n) (not_congr (hAt (n + 1)))

private theorem pairwise_classHolds_withClass {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) {cs : List ClassExpr}
    (h : cs.any (exprUsesClass X) = false) :
    (cs.Pairwise fun a b => ∀ x, ¬ (classHolds (withClass i X hthing hnothing P) x a ∧
        classHolds (withClass i X hthing hnothing P) x b)) ↔
    (cs.Pairwise fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)) := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.pairwise_cons]
    refine and_congr (forall₂_congr fun d hd => forall_congr' fun x => not_congr ?_) (ih h.2)
    have hdNo : exprUsesClass X d = false := by
      cases hdu : exprUsesClass X d with
      | false => rfl
      | true => exact False.elim (Bool.false_ne_true (h.2 ▸ List.any_eq_true.mpr ⟨d, hd, hdu⟩))
    exact and_congr (classHolds_withClass_of_not_uses i X hthing hnothing P h.1 x)
      (classHolds_withClass_of_not_uses i X hthing hnothing P hdNo x)

theorem axiomHolds_withClass_of_not_uses {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) {ax : Axiom} (h : axiomUsesClass X ax = false) :
    axiomHolds (withClass i X hthing hnothing P) ax ↔ axiomHolds i ax := by
  cases ax with
  | subClassOf a b =>
    simp only [axiomUsesClass, Bool.or_eq_false_iff] at h
    exact forall_congr' fun x => imp_congr
      (classHolds_withClass_of_not_uses i X hthing hnothing P h.1 x)
      (classHolds_withClass_of_not_uses i X hthing hnothing P h.2 x)
  | equivalentClasses cs =>
    simp only [axiomUsesClass] at h
    have hmem : ∀ c ∈ cs, exprUsesClass X c = false := fun c hc => by
      cases hcu : exprUsesClass X c with
      | false => rfl
      | true => exact False.elim (Bool.false_ne_true (h ▸ List.any_eq_true.mpr ⟨c, hc, hcu⟩))
    exact forall₂_congr fun a ha => forall₂_congr fun b hb => forall_congr' fun x =>
      iff_congr (classHolds_withClass_of_not_uses i X hthing hnothing P (hmem a ha) x)
        (classHolds_withClass_of_not_uses i X hthing hnothing P (hmem b hb) x)
  | disjointClasses cs =>
    simp only [axiomUsesClass] at h
    exact pairwise_classHolds_withClass i X hthing hnothing P h
  | disjointUnion head cs =>
    simp only [axiomUsesClass, Bool.or_eq_false_iff] at h
    have hmem : ∀ c ∈ cs, exprUsesClass X c = false := fun c hc => by
      cases hcu : exprUsesClass X c with
      | false => rfl
      | true => exact False.elim (Bool.false_ne_true (h.2 ▸ List.any_eq_true.mpr ⟨c, hc, hcu⟩))
    refine and_congr (forall_congr' fun x => iff_congr ?_ ?_) (pairwise_classHolds_withClass i X hthing hnothing P h.2)
    · simp [h.1]
    · exact ⟨fun ⟨c, hc, hx⟩ => ⟨c, hc, (classHolds_withClass_of_not_uses i X hthing hnothing P (hmem c hc) x).mp hx⟩,
             fun ⟨c, hc, hx⟩ => ⟨c, hc, (classHolds_withClass_of_not_uses i X hthing hnothing P (hmem c hc) x).mpr hx⟩⟩
  | objectPropertyDomain r c =>
    simp only [axiomUsesClass] at h
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr Iff.rfl (classHolds_withClass_of_not_uses i X hthing hnothing P h x)
  | objectPropertyRange r c =>
    simp only [axiomUsesClass] at h
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr Iff.rfl (classHolds_withClass_of_not_uses i X hthing hnothing P h y)
  | dataPropertyDomain dp c =>
    simp only [axiomUsesClass] at h
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr Iff.rfl (classHolds_withClass_of_not_uses i X hthing hnothing P h x)
  | dataPropertyRange dp d =>
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr Iff.rfl (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d))
  | datatypeDefinition dt d =>
    exact forall_congr' fun y => iff_congr Iff.rfl (iff_of_eq (dataHolds_withClass_eq i X hthing hnothing P y d))
  | hasKey c os ds =>
    simp only [axiomUsesClass] at h
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr (classHolds_withClass_of_not_uses i X hthing hnothing P h x)
        (imp_congr (classHolds_withClass_of_not_uses i X hthing hnothing P h y) Iff.rfl)
  | classAssertion c a =>
    simp only [axiomUsesClass] at h
    exact classHolds_withClass_of_not_uses i X hthing hnothing P h (i.individuals a)
  | subObjectPropertyChain rs s =>
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr (rolePath_withClass_iff i X hthing hnothing P rs x y) Iff.rfl
  | _ => rfl

theorem satisfies_withClass_of_not_uses {D : DatatypeMap} (i : Interpretation D)
    (X : IRI) (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (P : i.Object → Prop) {o : Ontology} (h : ontologyUsesClass X o = false) :
    satisfies (withClass i X hthing hnothing P) o ↔ satisfies i o := by
  have hmem : ∀ ax ∈ o, axiomUsesClass X ax = false := fun ax hax => by
    cases hau : axiomUsesClass X ax with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true (h ▸ List.any_eq_true.mpr ⟨ax, hax, hau⟩))
  exact forall₂_congr fun ax hax => axiomHolds_withClass_of_not_uses i X hthing hnothing P (hmem ax hax)

/-- Model extension for definitional normalization: any model `i` of `o` extends
    along fresh class `X` (`X ∉ o`, `X ∉ D`) to a model of `(X ≡ D) :: o`. -/
theorem definitional_model_extension {D : DatatypeMap} (i : Interpretation D)
    {X : IRI} {defExpr : ClassExpr} {o : Ontology}
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (hDef : exprUsesClass X defExpr = false)
    (hOnt : ontologyUsesClass X o = false)
    (hsat : satisfies i o) :
    satisfies (withClass i X hthing hnothing (fun x => classHolds i x defExpr))
      (.equivalentClasses [.named X, defExpr] :: o) := by
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | hmem
  · intro a ha b hb x
    have hX : classHolds (withClass i X hthing hnothing (fun x => classHolds i x defExpr)) x (.named X) ↔
        classHolds i x defExpr := classHolds_withClass_self i X hthing hnothing _ x
    have hD : classHolds (withClass i X hthing hnothing (fun x => classHolds i x defExpr)) x defExpr ↔
        classHolds i x defExpr := classHolds_withClass_of_not_uses i X hthing hnothing _ hDef x
    rcases List.mem_cons.mp ha with rfl | ha2 <;> rcases List.mem_cons.mp hb with rfl | hb2
    · exact Iff.rfl
    · rcases List.mem_singleton.mp hb2 with rfl; exact hX.trans hD.symm
    · rcases List.mem_singleton.mp ha2 with rfl; exact hD.trans hX.symm
    · rcases List.mem_singleton.mp ha2 with rfl; rcases List.mem_singleton.mp hb2 with rfl; exact Iff.rfl
  · exact ((satisfies_withClass_of_not_uses i X hthing hnothing _ hOnt).mpr hsat) ax hmem

/-- Model reduct for definitional normalization: any model of `(X ≡ D) :: o`
    is a model of `o` in which `X` and `D` have identical extensions. -/
theorem definitional_model_reduct {D : DatatypeMap} (i : Interpretation D)
    {X : IRI} {defExpr : ClassExpr} {o : Ontology}
    (hsat : satisfies i (.equivalentClasses [.named X, defExpr] :: o)) :
    satisfies i o ∧ ∀ x : i.Object, classHolds i x (.named X) ↔ classHolds i x defExpr :=
  ⟨fun ax hax => hsat ax (List.mem_cons_of_mem _ hax),
   fun x => hsat (.equivalentClasses [.named X, defExpr]) (List.mem_cons_self ..)
     (.named X) (by simp) defExpr (by simp) x⟩

/-- Two-way satisfiability preservation for fresh definitional extension `(X ≡ D) :: o`. -/
theorem definitional_extension_sat_iff {D : DatatypeMap}
    {X : IRI} {defExpr : ClassExpr} {o : Ontology}
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (hDef : exprUsesClass X defExpr = false)
    (hOnt : ontologyUsesClass X o = false) :
    Satisfiable D (.equivalentClasses [.named X, defExpr] :: o) ↔ Satisfiable D o := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    exact ⟨i, assign, (definitional_model_reduct (i.withAnonymous assign) hsat).1⟩
  · rintro ⟨i, assign, hsat⟩
    let j := i.withAnonymous assign
    exact ⟨withClass j X hthing hnothing (fun x => classHolds j x defExpr), assign,
      definitional_model_extension j hthing hnothing hDef hOnt hsat⟩

/-- Two-way query entailment preservation for fresh definitional extension:
    every query `q` in the original vocabulary (`X ∉ q`) has identical entailment
    over `(X ≡ D) :: o` and `o`. -/
theorem definitional_extension_entails_iff {D : DatatypeMap}
    {X : IRI} {defExpr : ClassExpr} {o q : Ontology}
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (hDef : exprUsesClass X defExpr = false)
    (hOnt : ontologyUsesClass X o = false)
    (hQuery : ontologyUsesClass X q = false) :
    Entails D (.equivalentClasses [.named X, defExpr] :: o) q ↔ Entails D o q := by
  constructor
  · intro hent i ⟨assign, hsat⟩
    let j := i.withAnonymous assign
    let jExt := withClass j X hthing hnothing (fun x => classHolds j x defExpr)
    have hsatExt : satisfies jExt (.equivalentClasses [.named X, defExpr] :: o) :=
      definitional_model_extension j hthing hnothing hDef hOnt hsat
    obtain ⟨assign', hqExt⟩ := hent jExt ⟨assign, hsatExt⟩
    refine ⟨assign', ?_⟩
    exact (satisfies_withClass_of_not_uses (i.withAnonymous assign') X hthing hnothing
      (fun x => classHolds j x defExpr) hQuery).mp hqExt
  · intro hent i ⟨assign, hsat⟩
    obtain ⟨assign', hq⟩ := hent i ⟨assign, (definitional_model_reduct (i.withAnonymous assign) hsat).1⟩
    exact ⟨assign', hq⟩

/-- M3 Worked Proof Checkpoint: source axiom `A ⊑ ∃R.(B ⊓ ∃S.C)`. -/
def workedNestedAxiom (A : IRI) (R : ObjectProperty) (B : IRI) (S : ObjectProperty) (C : IRI) : Axiom :=
  .subClassOf (.named A) (.objectSome R (.intersection (.named B) (.objectSome S (.named C))))

/-- M3 Worked Proof Checkpoint: definitional compilation through fresh class `X`
    into `{X ≡ B ⊓ ∃S.C, A ⊑ ∃R.X}`. -/
def workedFlattenedAxioms (A : IRI) (R : ObjectProperty) (B : IRI) (S : ObjectProperty) (C : IRI) (X : IRI) :
    List Axiom :=
  [ .equivalentClasses [.named X, .intersection (.named B) (.objectSome S (.named C))],
    .subClassOf (.named A) (.objectSome R (.named X)) ]

/-- Worked Proof Checkpoint (Reduct): any model of `{X ≡ B ⊓ ∃S.C, A ⊑ ∃R.X} ∪ o`
    is a model of `{A ⊑ ∃R.(B ⊓ ∃S.C)} ∪ o`. -/
theorem workedCheckpoint_reduct {D : DatatypeMap} (i : Interpretation D)
    {A : IRI} {R : ObjectProperty} {B : IRI} {S : ObjectProperty} {C X : IRI} {o : Ontology}
    (hsat : satisfies i (workedFlattenedAxioms A R B S C X ++ o)) :
    satisfies i (workedNestedAxiom A R B S C :: o) := by
  have heq : ∀ y : i.Object, classHolds i y (.named X) ↔
      classHolds i y (.intersection (.named B) (.objectSome S (.named C))) :=
    fun y => hsat (.equivalentClasses [.named X, .intersection (.named B) (.objectSome S (.named C))])
      (by simp [workedFlattenedAxioms]) (.named X) (by simp)
      (.intersection (.named B) (.objectSome S (.named C))) (by simp) y
  have hsub : axiomHolds i (.subClassOf (.named A) (.objectSome R (.named X))) :=
    hsat (.subClassOf (.named A) (.objectSome R (.named X))) (by simp [workedFlattenedAxioms])
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | hmem
  · intro x hx
    obtain ⟨y, hxy, hyX⟩ := hsub x hx
    exact ⟨y, hxy, (heq y).mp hyX⟩
  · exact hsat ax (List.mem_append_right _ hmem)

/-- Worked Proof Checkpoint (Extension): any model `i` of `{A ⊑ ∃R.(B ⊓ ∃S.C)} ∪ o`
    extends along fresh `X` (`X ∉ {A, B, C}` and `X ∉ o`) to a model of
    `{X ≡ B ⊓ ∃S.C, A ⊑ ∃R.X} ∪ o`. -/
theorem workedCheckpoint_extension {D : DatatypeMap} (i : Interpretation D)
    {A : IRI} {R : ObjectProperty} {B : IRI} {S : ObjectProperty} {C X : IRI} {o : Ontology}
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (hXA : (A == X) = false) (hXB : (B == X) = false) (hXC : (C == X) = false)
    (hOnt : ontologyUsesClass X o = false)
    (hsat : satisfies i (workedNestedAxiom A R B S C :: o)) :
    satisfies (withClass i X hthing hnothing
      (fun y => classHolds i y (.intersection (.named B) (.objectSome S (.named C)))))
      (workedFlattenedAxioms A R B S C X ++ o) := by
  let defExpr := ClassExpr.intersection (.named B) (.objectSome S (.named C))
  have hDef : exprUsesClass X defExpr = false := by
    simp [defExpr, exprUsesClass, hXB, hXC]
  have hsatO : satisfies i o := fun ax hax => hsat ax (List.mem_cons_of_mem _ hax)
  have hExtO := definitional_model_extension i hthing hnothing hDef hOnt hsatO
  have hNested : axiomHolds i (workedNestedAxiom A R B S C) := hsat _ (List.mem_cons_self ..)
  intro ax hax
  rcases List.mem_append.mp hax with hflat | hmem
  · simp only [workedFlattenedAxioms, List.mem_cons, List.not_mem_nil, or_false] at hflat
    rcases hflat with rfl | rfl
    · exact hExtO _ (List.mem_cons_self ..)
    · intro x hx
      have hxA : classHolds i x (.named A) := by
        simpa [classHolds, withClass, hXA] using hx
      obtain ⟨y, hxy, hyDef⟩ := hNested x hxA
      exact ⟨y, hxy, (classHolds_withClass_self i X hthing hnothing _ y).mpr hyDef⟩
  · exact hExtO ax (List.mem_cons_of_mem _ hmem)

/-- Worked Proof Checkpoint (Query Preservation): compiling `A ⊑ ∃R.(B ⊓ ∃S.C)`
    through fresh class `X` preserves all query entailments in the original vocabulary. -/
theorem workedCheckpoint_entails_iff {D : DatatypeMap}
    {A : IRI} {R : ObjectProperty} {B : IRI} {S : ObjectProperty} {C X : IRI} {o q : Ontology}
    (hthing : (thing == X) = false) (hnothing : (nothing == X) = false)
    (hXA : (A == X) = false) (hXB : (B == X) = false) (hXC : (C == X) = false)
    (hOnt : ontologyUsesClass X o = false)
    (hQuery : ontologyUsesClass X q = false) :
    Entails D (workedFlattenedAxioms A R B S C X ++ o) q ↔
      Entails D (workedNestedAxiom A R B S C :: o) q := by
  constructor
  · intro hent i ⟨assign, hsat⟩
    let j := i.withAnonymous assign
    let jExt := withClass j X hthing hnothing
      (fun y => classHolds j y (.intersection (.named B) (.objectSome S (.named C))))
    have hsatExt := workedCheckpoint_extension j hthing hnothing hXA hXB hXC hOnt hsat
    obtain ⟨assign', hqExt⟩ := hent jExt ⟨assign, hsatExt⟩
    exact ⟨assign', (satisfies_withClass_of_not_uses (i.withAnonymous assign') X hthing hnothing
      (fun y => classHolds j y (.intersection (.named B) (.objectSome S (.named C)))) hQuery).mp hqExt⟩
  · intro hent i ⟨assign, hsat⟩
    exact hent i ⟨assign, workedCheckpoint_reduct (i.withAnonymous assign) hsat⟩

/-! ### M8 End-to-End Composition: Source Ontology Normalization + Full `SROIQ(D)` Refutation Completeness -/

/-- End-to-end M8 theorem composing source `Ontology` normalization
    (`normalizeWithDefs_sat_iff`), canonical `SROIQ(D)` model construction
    (`sroiqd_saturated_sat`), and tableau refutation soundness/completeness
    (`sroiqdDerivation_unsat_iff_refutation`): an OWL 2 DL `Ontology` `o` is
    unsatisfiable under Direct Semantics if and only if its normalized
    `SROIQ(D)` problem has a closed tableau refutation `CoreRefutation p s0`. -/
theorem ontology_unsat_iff_sroiqdRefutation {o : Ontology} {defs : DatatypeDefs}
    {p : Problem} {s0 : Branch}
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hroot : p.root = .top)
    (hord : p.isOrdinary = true)
    (hinit : initial p = some s0)
    (hd : SROIQDDerivation p s0) :
    ¬ Satisfiable datatypeMap o ↔ CoreRefutation p s0 := by
  have hsatIff : Satisfiable datatypeMap o ↔ p.Sat :=
    (normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)
  exact (not_congr hsatIff).trans (sroiqdDerivation_unsat_iff_refutation hord hinit hd)

/-- End-to-end M8 dichotomy for any normalized OWL 2 DL `Ontology` `o`:
    either `o` is satisfiable under OWL 2 Direct Semantics (`Satisfiable datatypeMap o`)
    or its initial tableau branch has a closed finite refutation (`CoreRefutation p s0`). -/
theorem ontology_sat_or_refutation {o : Ontology} {defs : DatatypeDefs}
    {p : Problem} {s0 : Branch}
    (hnorm : normalizeWithDefs o = some (defs, p))
    (hroot : p.root = .top)
    (hord : p.isOrdinary = true)
    (hd : SROIQDDerivation p s0) :
    Satisfiable datatypeMap o ∨ CoreRefutation p s0 := by
  have hsatIff : Satisfiable datatypeMap o ↔ p.Sat :=
    (normalizeWithDefs_sat_iff hnorm).trans (satisfiable_iff_sat p hroot)
  rcases sroiqdDerivation_dichotomy hord hd with hsat | href
  · exact Or.inl (hsatIff.mpr hsat)
  · exact Or.inr href

end Sabrina.OWL2.Normalize
