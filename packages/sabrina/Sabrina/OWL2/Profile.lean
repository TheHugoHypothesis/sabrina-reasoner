import Sabrina.OWL2.DirectSemantics

/-! Runtime OWL 2 DL fragment profiling and syntactic ⊥-locality module
    extraction (Grau–Horrocks–Kazakov–Sattler 2008).

    Given any OWL 2 DL ontology `o` and a query signature `seed`,
    `extractBotModule o seed` computes a subset `M ⊆ o` and covered signature `σ`
    such that every omitted axiom `a ∈ o \ M` is syntactically ⊥-local with
    respect to `σ`. We prove kernel-checked conservativity:
      * `extractBotModule_sat_iff : Satisfiable d o ↔ Satisfiable d M`
      * `extractBotModule_entails_iff : Entails d o Q ↔ Entails d M Q`

    We also classify both `o` and `M` into the least sufficient OWL 2 DL
    fragment (`EL++`, `DataOnly`, `ALC`, `ALCH`, `ALCHI`, `RankedRoleChains`,
    or full `SROIQ(D)`) so execution can dispatch to the fastest verified engine. -/

namespace Sabrina.OWL2.Profile

open Sabrina.OWL2

/-! ### Signatures and signature restriction -/

def addUnique (xs : List IRI) (x : IRI) : List IRI :=
  if xs.contains x then xs else x :: xs

theorem mem_addUnique {xs : List IRI} {x y : IRI} :
    y ∈ addUnique xs x ↔ y = x ∨ y ∈ xs := by
  unfold addUnique
  by_cases h : xs.contains x
  · simp only [h, ↓reduceIte]
    have hx : x ∈ xs := List.contains_iff_mem.mp h
    exact ⟨Or.inr, fun hy => hy.elim (fun he => he ▸ hx) id⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]

structure Sig where
  cls : List IRI := []
  obj : List IRI := []
  data : List IRI := []
  deriving Repr, DecidableEq

namespace Sig

def empty : Sig := {}

def hasCls (σ : Sig) (c : IRI) : Bool := σ.cls.contains c
def hasObj (σ : Sig) (r : IRI) : Bool := σ.obj.contains r
def hasData (σ : Sig) (p : IRI) : Bool := σ.data.contains p

def addCls (σ : Sig) (c : IRI) : Sig :=
  if c == thing || c == nothing then σ else { σ with cls := addUnique σ.cls c }

def addObj (σ : Sig) (r : IRI) : Sig :=
  if r == topObjectProperty || r == bottomObjectProperty then σ else { σ with obj := addUnique σ.obj r }

def addData (σ : Sig) (p : IRI) : Sig :=
  if p == topDataProperty || p == bottomDataProperty then σ else { σ with data := addUnique σ.data p }

def union (a b : Sig) : Sig :=
  { cls := b.cls.foldl addUnique a.cls
    obj := b.obj.foldl addUnique a.obj
    data := b.data.foldl addUnique a.data }

def Subset (a b : Sig) : Prop :=
  (∀ c, a.hasCls c = true → b.hasCls c = true) ∧
  (∀ r, a.hasObj r = true → b.hasObj r = true) ∧
  (∀ p, a.hasData p = true → b.hasData p = true)

theorem Subset.refl (σ : Sig) : Subset σ σ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.trans {a b c : Sig} (hab : Subset a b) (hbc : Subset b c) : Subset a c :=
  ⟨fun x h => hbc.1 x (hab.1 x h),
   fun x h => hbc.2.1 x (hab.2.1 x h),
   fun x h => hbc.2.2 x (hab.2.2 x h)⟩

private theorem mem_foldl_addUnique (xs ys : List IRI) (z : IRI) :
    z ∈ ys.foldl addUnique xs ↔ z ∈ xs ∨ z ∈ ys := by
  induction ys generalizing xs with
  | nil => simp
  | cons y tail ih =>
    simp only [List.foldl_cons, ih, mem_addUnique, List.mem_cons]
    exact ⟨fun h => h.elim (fun h1 => h1.elim (fun e => Or.inr (Or.inl e)) Or.inl) (fun h2 => Or.inr (Or.inr h2)),
           fun h => h.elim (fun h1 => Or.inl (Or.inr h1)) (fun h2 => h2.elim (fun e => Or.inl (Or.inl e)) Or.inr)⟩

theorem subset_union_left (a b : Sig) : Subset a (a.union b) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;>
    simp only [hasCls, hasObj, hasData, union, List.contains_iff_mem, mem_foldl_addUnique] at hx ⊢ <;>
    exact Or.inl hx

theorem subset_union_right (a b : Sig) : Subset b (a.union b) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;>
    simp only [hasCls, hasObj, hasData, union, List.contains_iff_mem, mem_foldl_addUnique] at hx ⊢ <;>
    exact Or.inr hx

theorem subset_addCls (σ : Sig) (c : IRI) : Subset σ (σ.addCls c) := by
  unfold addCls
  split
  · exact Subset.refl σ
  · refine ⟨?_, fun _ h => h, fun _ h => h⟩
    intro x hx
    simp only [hasCls, List.contains_iff_mem, mem_addUnique] at hx ⊢
    exact Or.inr hx

theorem subset_addObj (σ : Sig) (r : IRI) : Subset σ (σ.addObj r) := by
  unfold addObj
  split
  · exact Subset.refl σ
  · refine ⟨fun _ h => h, ?_, fun _ h => h⟩
    intro x hx
    simp only [hasObj, List.contains_iff_mem, mem_addUnique] at hx ⊢
    exact Or.inr hx

theorem subset_addData (σ : Sig) (p : IRI) : Subset σ (σ.addData p) := by
  unfold addData
  split
  · exact Subset.refl σ
  · refine ⟨fun _ h => h, fun _ h => h, ?_⟩
    intro x hx
    simp only [hasData, List.contains_iff_mem, mem_addUnique] at hx ⊢
    exact Or.inr hx

theorem hasCls_addCls_self (σ : Sig) (c : IRI) (h1 : c ≠ thing) (h2 : c ≠ nothing) :
    (σ.addCls c).hasCls c = true := by
  unfold addCls
  have hcond : (c == thing || c == nothing) = false := by simp [h1, h2]
  simp [hcond, hasCls, mem_addUnique]

theorem hasObj_addObj_self (σ : Sig) (r : IRI) (h1 : r ≠ topObjectProperty) (h2 : r ≠ bottomObjectProperty) :
    (σ.addObj r).hasObj r = true := by
  unfold addObj
  have hcond : (r == topObjectProperty || r == bottomObjectProperty) = false := by simp [h1, h2]
  simp [hcond, hasObj, mem_addUnique]

theorem hasData_addData_self (σ : Sig) (p : IRI) (h1 : p ≠ topDataProperty) (h2 : p ≠ bottomDataProperty) :
    (σ.addData p).hasData p = true := by
  unfold addData
  have hcond : (p == topDataProperty || p == bottomDataProperty) = false := by simp [h1, h2]
  simp [hcond, hasData, mem_addUnique]

end Sig

def objPropIRI : ObjectProperty → IRI
  | .named r => r
  | .inverse r => r

def exprSig : ClassExpr → Sig
  | .named c => Sig.empty.addCls c
  | .complement c => exprSig c
  | .intersection a b => (exprSig a).union (exprSig b)
  | .union a b => (exprSig a).union (exprSig b)
  | .oneOf _ => Sig.empty
  | .objectSome r c => (exprSig c).addObj (objPropIRI r)
  | .objectAll r c => (exprSig c).addObj (objPropIRI r)
  | .objectValue r _ => Sig.empty.addObj (objPropIRI r)
  | .objectSelf r => Sig.empty.addObj (objPropIRI r)
  | .objectMin _ r c => (exprSig c).addObj (objPropIRI r)
  | .objectMax _ r c => (exprSig c).addObj (objPropIRI r)
  | .objectExact _ r c => (exprSig c).addObj (objPropIRI r)
  | .dataSome p _ => Sig.empty.addData p
  | .dataAll p _ => Sig.empty.addData p
  | .dataValue p _ => Sig.empty.addData p
  | .dataMin _ p _ => Sig.empty.addData p
  | .dataMax _ p _ => Sig.empty.addData p
  | .dataExact _ p _ => Sig.empty.addData p

def exprListSig (cs : List ClassExpr) : Sig :=
  cs.foldl (fun acc c => acc.union (exprSig c)) Sig.empty

def objListSig (rs : List ObjectProperty) : Sig :=
  rs.foldl (fun acc r => acc.addObj (objPropIRI r)) Sig.empty

def dataListSig (ds : List IRI) : Sig :=
  ds.foldl (fun acc p => acc.addData p) Sig.empty

def axiomSig : Axiom → Sig
  | .subClassOf a b => (exprSig a).union (exprSig b)
  | .equivalentClasses cs => exprListSig cs
  | .disjointClasses cs => exprListSig cs
  | .disjointUnion h cs => (exprListSig cs).addCls h
  | .subObjectProperty r s => (Sig.empty.addObj (objPropIRI r)).addObj (objPropIRI s)
  | .subObjectPropertyChain rs s => (objListSig rs).addObj (objPropIRI s)
  | .equivalentObjectProperties rs => objListSig rs
  | .disjointObjectProperties rs => objListSig rs
  | .inverseObjectProperties r s => (Sig.empty.addObj (objPropIRI r)).addObj (objPropIRI s)
  | .objectPropertyDomain r c => (exprSig c).addObj (objPropIRI r)
  | .objectPropertyRange r c => (exprSig c).addObj (objPropIRI r)
  | .functionalObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .inverseFunctionalObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .reflexiveObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .irreflexiveObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .symmetricObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .asymmetricObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .transitiveObjectProperty r => Sig.empty.addObj (objPropIRI r)
  | .subDataProperty r s => (Sig.empty.addData r).addData s
  | .equivalentDataProperties rs => dataListSig rs
  | .disjointDataProperties rs => dataListSig rs
  | .dataPropertyDomain r c => (exprSig c).addData r
  | .dataPropertyRange r _ => Sig.empty.addData r
  | .functionalDataProperty r => Sig.empty.addData r
  | .datatypeDefinition _ _ => Sig.empty
  | .hasKey c rs ds => ((exprSig c).union (objListSig rs)).union (dataListSig ds)
  | .sameIndividuals _ => Sig.empty
  | .differentIndividuals _ => Sig.empty
  | .classAssertion c _ => exprSig c
  | .objectAssertion r _ _ => Sig.empty.addObj (objPropIRI r)
  | .negativeObjectAssertion r _ _ => Sig.empty.addObj (objPropIRI r)
  | .dataAssertion p _ _ => Sig.empty.addData p
  | .negativeDataAssertion p _ _ => Sig.empty.addData p

def ontologySig (o : Ontology) : Sig :=
  o.foldl (fun acc a => acc.union (axiomSig a)) Sig.empty

private theorem foldl_union_subset_acc {α : Type} (f : α → Sig) (xs : List α) (acc : Sig) :
    acc.Subset (xs.foldl (fun s x => s.union (f x)) acc) := by
  induction xs generalizing acc with
  | nil => exact Sig.Subset.refl acc
  | cons x tail ih =>
    simp only [List.foldl_cons]
    exact Sig.Subset.trans (Sig.subset_union_left acc (f x)) (ih _)

private theorem foldl_union_mem_subset {α : Type} (f : α → Sig) {xs : List α} {x : α} (hx : x ∈ xs) (acc : Sig) :
    (f x).Subset (xs.foldl (fun s y => s.union (f y)) acc) := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y tail ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | htail
    · exact Sig.Subset.trans (Sig.subset_union_right acc (f x)) (foldl_union_subset_acc f tail _)
    · exact ih htail _

private theorem exprListSig_mem {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) :
    (exprSig c).Subset (exprListSig cs) :=
  foldl_union_mem_subset exprSig hc Sig.empty

private theorem foldl_addObj_subset_acc (rs : List ObjectProperty) (acc : Sig) :
    acc.Subset (rs.foldl (fun s r => s.addObj (objPropIRI r)) acc) := by
  induction rs generalizing acc with
  | nil => exact Sig.Subset.refl acc
  | cons r tail ih =>
    simp only [List.foldl_cons]
    exact Sig.Subset.trans (Sig.subset_addObj acc (objPropIRI r)) (ih _)

private theorem objListSig_mem {rs : List ObjectProperty} {r : ObjectProperty} (hr : r ∈ rs)
    (h1 : objPropIRI r ≠ topObjectProperty) (h2 : objPropIRI r ≠ bottomObjectProperty) :
    (objListSig rs).hasObj (objPropIRI r) = true := by
  have go : ∀ (acc : Sig), (rs.foldl (fun s x => s.addObj (objPropIRI x)) acc).hasObj (objPropIRI r) = true := by
    induction rs with
    | nil => cases hr
    | cons x tail ih =>
      intro acc
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hr with rfl | htail
      · exact (foldl_addObj_subset_acc tail (acc.addObj (objPropIRI r))).2.1 _
          (Sig.hasObj_addObj_self acc (objPropIRI r) h1 h2)
      · exact ih htail _
  exact go Sig.empty

private theorem foldl_addData_subset_acc (ds : List IRI) (acc : Sig) :
    acc.Subset (ds.foldl (fun s p => s.addData p) acc) := by
  induction ds generalizing acc with
  | nil => exact Sig.Subset.refl acc
  | cons p tail ih =>
    simp only [List.foldl_cons]
    exact Sig.Subset.trans (Sig.subset_addData acc p) (ih _)

private theorem dataListSig_mem {ds : List IRI} {p : IRI} (hp : p ∈ ds)
    (h1 : p ≠ topDataProperty) (h2 : p ≠ bottomDataProperty) :
    (dataListSig ds).hasData p = true := by
  have go : ∀ (acc : Sig), (ds.foldl (fun s x => s.addData x) acc).hasData p = true := by
    induction ds with
    | nil => cases hp
    | cons x tail ih =>
      intro acc
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hp with rfl | htail
      · exact (foldl_addData_subset_acc tail (acc.addData p)).2.2 _
          (Sig.hasData_addData_self acc p h1 h2)
      · exact ih htail _
  exact go Sig.empty

/-! ### Restricting an interpretation to a signature (setting outside symbols to ∅) -/

def restrictToSig {d : DatatypeMap} (i : Interpretation d) (σ : Sig) : Interpretation d where
  Object := i.Object
  objectNonempty := i.objectNonempty
  Data := i.Data
  dataNonempty := i.dataNonempty
  embedValue := i.embedValue
  embedValue_injective := i.embedValue_injective
  classes c x :=
    if c = thing then True
    else if c = nothing then False
    else if σ.hasCls c then i.classes c x else False
  objectProperties r x y :=
    if r = topObjectProperty then True
    else if r = bottomObjectProperty then False
    else if σ.hasObj r then i.objectProperties r x y else False
  dataProperties p x y :=
    if p = topDataProperty then True
    else if p = bottomDataProperty then False
    else if σ.hasData p then i.dataProperties p x y else False
  individuals := i.individuals
  datatypes := i.datatypes
  literalValue := i.literalValue
  lexicalAgreement := i.lexicalAgreement
  named := i.named
  namedIndividual := i.namedIndividual
  thingExt := by intro x; simp
  nothingExt := by intro x; simp [thing, nothing]
  topObjectExt := by intro x y; simp
  bottomObjectExt := by intro x y; simp [topObjectProperty, bottomObjectProperty]
  topDataExt := by intro x y; simp
  bottomDataExt := by intro x y; simp [topDataProperty, bottomDataProperty]
  literalDatatypeExt := i.literalDatatypeExt
  datatypeAgreement := i.datatypeAgreement

theorem restrictToSig_withAnonymous {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    (assign : String → String → i.Object) :
    (restrictToSig i σ).withAnonymous assign = restrictToSig (i.withAnonymous assign) σ := rfl

private theorem restrictToSig_dataHolds {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    (y : i.Data) (dr : DataRange) :
    dataHolds (restrictToSig i σ) y dr ↔ dataHolds i y dr := by
  induction dr with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ha hb => exact and_congr ha hb
  | union _ _ ha hb => exact or_congr ha hb

private theorem restrictToSig_cls_eq {d : DatatypeMap} (i : Interpretation d) {σ : Sig} {c : IRI}
    (h : c ≠ thing → c ≠ nothing → σ.hasCls c = true) (x : i.Object) :
    (restrictToSig i σ).classes c x ↔ i.classes c x := by
  simp only [restrictToSig]
  by_cases h1 : c = thing
  · subst h1; simp [i.thingExt]
  · by_cases h2 : c = nothing
    · subst h2; simp [h1, i.nothingExt]
    · simp [h1, h2, h h1 h2]

private theorem restrictToSig_obj_eq {d : DatatypeMap} (i : Interpretation d) {σ : Sig} {r : ObjectProperty}
    (h : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true)
    (x y : i.Object) :
    objectHolds (restrictToSig i σ) r x y ↔ objectHolds i r x y := by
  cases r with
  | named rn | inverse rn =>
    simp only [objectHolds, restrictToSig, objPropIRI] at h ⊢
    by_cases h1 : rn = topObjectProperty
    · subst h1; simp [i.topObjectExt]
    · by_cases h2 : rn = bottomObjectProperty
      · subst h2; simp [h1, i.bottomObjectExt]
      · simp [h1, h2, h h1 h2]

private theorem restrictToSig_data_eq {d : DatatypeMap} (i : Interpretation d) {σ : Sig} {p : IRI}
    (h : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true)
    (x : i.Object) (y : i.Data) :
    (restrictToSig i σ).dataProperties p x y ↔ i.dataProperties p x y := by
  simp only [restrictToSig]
  by_cases h1 : p = topDataProperty
  · subst h1; simp [i.topDataExt]
  · by_cases h2 : p = bottomDataProperty
    · subst h2; simp [h1, i.bottomDataExt]
    · simp [h1, h2, h h1 h2]

private theorem atLeast_congr {α : Type} {n : Nat} {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    AtLeast n p ↔ AtLeast n q :=
  ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun x hx => (h x).mp (hp x hx)⟩,
   fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun x hx => (h x).mpr (hp x hx)⟩⟩

theorem restrictToSig_classHolds {d : DatatypeMap} (i : Interpretation d) {σ : Sig}
    {c : ClassExpr} (hsub : (exprSig c).Subset σ) (x : i.Object) :
    classHolds (restrictToSig i σ) x c ↔ classHolds i x c := by
  induction c generalizing x with
  | named cn =>
    exact restrictToSig_cls_eq i (fun h1 h2 => hsub.1 cn (Sig.hasCls_addCls_self Sig.empty cn h1 h2)) x
  | complement a ih =>
    exact not_congr (ih hsub x)
  | intersection a b iha ihb =>
    exact and_congr
      (iha (Sig.Subset.trans (Sig.subset_union_left _ _) hsub) x)
      (ihb (Sig.Subset.trans (Sig.subset_union_right _ _) hsub) x)
  | union a b iha ihb =>
    exact or_congr
      (iha (Sig.Subset.trans (Sig.subset_union_left _ _) hsub) x)
      (ihb (Sig.Subset.trans (Sig.subset_union_right _ _) hsub) x)
  | oneOf _ => rfl
  | objectSome r a ih =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have ha := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact exists_congr fun y => and_congr (restrictToSig_obj_eq i hr x y) (ih ha y)
  | objectAll r a ih =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have ha := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact forall_congr' fun y => imp_congr (restrictToSig_obj_eq i hr x y) (ih ha y)
  | objectValue r a =>
    exact restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)) x _
  | objectSelf r =>
    exact restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)) x x
  | objectMin n r a ih =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have ha := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact atLeast_congr fun y => and_congr (restrictToSig_obj_eq i hr x y) (ih ha y)
  | objectMax n r a ih =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have ha := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact not_congr (atLeast_congr fun y => and_congr (restrictToSig_obj_eq i hr x y) (ih ha y))
  | objectExact n r a ih =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have ha := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact and_congr
      (atLeast_congr fun y => and_congr (restrictToSig_obj_eq i hr x y) (ih ha y))
      (not_congr (atLeast_congr fun y => and_congr (restrictToSig_obj_eq i hr x y) (ih ha y)))
  | dataSome p dr =>
    have hp : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact exists_congr fun y => and_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr)
  | dataAll p dr =>
    have hp : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact forall_congr' fun y => imp_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr)
  | dataValue p l =>
    exact restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)) x _
  | dataMin n p dr =>
    have hp : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact atLeast_congr fun y => and_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr)
  | dataMax n p dr =>
    have hp : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact not_congr (atLeast_congr fun y => and_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr))
  | dataExact n p dr =>
    have hp : p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact and_congr
      (atLeast_congr fun y => and_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr))
      (not_congr (atLeast_congr fun y => and_congr (restrictToSig_data_eq i hp x y) (restrictToSig_dataHolds i σ y dr)))

private theorem pairwise_iff {α : Type} {P Q : α → α → Prop} {xs : List α}
    (h : ∀ a ∈ xs, ∀ b ∈ xs, P a b ↔ Q a b) :
    xs.Pairwise P ↔ xs.Pairwise Q := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
    simp only [List.pairwise_cons]
    refine and_congr ?_ (ih fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    exact forall_congr' fun y => imp_congr_right fun hy => h x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)

private theorem restrictToSig_rolePath {d : DatatypeMap} (i : Interpretation d) {σ : Sig}
    {rs : List ObjectProperty}
    (h : ∀ r ∈ rs, objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true)
    (x y : i.Object) :
    rolePath (restrictToSig i σ) rs x y ↔ rolePath i rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    exact exists_congr fun z => and_congr
      (restrictToSig_obj_eq i (h r (List.mem_cons_self ..)) x z)
      (ih (fun s hs => h s (List.mem_cons_of_mem _ hs)) z)

theorem restrictToSig_axiomHolds {d : DatatypeMap} (i : Interpretation d) {σ : Sig}
    {a : Axiom} (hsub : (axiomSig a).Subset σ) :
    axiomHolds (restrictToSig i σ) a ↔ axiomHolds i a := by
  cases a with
  | subClassOf c1 c2 =>
    exact forall_congr' fun x => imp_congr
      (restrictToSig_classHolds i (Sig.Subset.trans (Sig.subset_union_left _ _) hsub) x)
      (restrictToSig_classHolds i (Sig.Subset.trans (Sig.subset_union_right _ _) hsub) x)
  | equivalentClasses cs =>
    exact forall_congr' fun a => forall_congr' fun ha => forall_congr' fun b => forall_congr' fun hb =>
      forall_congr' fun x => iff_congr
        (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem ha) hsub) x)
        (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem hb) hsub) x)
  | disjointClasses cs =>
    exact pairwise_iff fun a ha b hb => forall_congr' fun x => not_congr (and_congr
      (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem ha) hsub) x)
      (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem hb) hsub) x))
  | disjointUnion h cs =>
    have hh : h ≠ thing → h ≠ nothing → σ.hasCls h = true :=
      fun h1 h2 => hsub.1 h (Sig.hasCls_addCls_self _ h h1 h2)
    have hcs := Sig.Subset.trans (Sig.subset_addCls _ h) hsub
    refine and_congr ?_ ?_
    · exact forall_congr' fun x => iff_congr (restrictToSig_cls_eq i hh x)
        (exists_congr fun c => and_congr_right fun hc =>
          restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem hc) hcs) x)
    · exact pairwise_iff fun a ha b hb => forall_congr' fun x => not_congr (and_congr
        (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem ha) hcs) x)
        (restrictToSig_classHolds i (Sig.Subset.trans (exprListSig_mem hb) hcs) x))
  | subObjectProperty r s =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ ((Sig.subset_addObj _ _).2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2))
    have hs : objPropIRI s ≠ topObjectProperty → objPropIRI s ≠ bottomObjectProperty → σ.hasObj (objPropIRI s) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_obj_eq i hr x y) (restrictToSig_obj_eq i hs x y)
  | subObjectPropertyChain rs s =>
    have hrs : ∀ r ∈ rs, objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun r hr h1 h2 => hsub.2.1 _ ((Sig.subset_addObj _ _).2.1 _ (objListSig_mem hr h1 h2))
    have hs : objPropIRI s ≠ topObjectProperty → objPropIRI s ≠ bottomObjectProperty → σ.hasObj (objPropIRI s) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_rolePath i hrs x y) (restrictToSig_obj_eq i hs x y)
  | equivalentObjectProperties rs =>
    exact forall_congr' fun r => forall_congr' fun hr => forall_congr' fun s => forall_congr' fun hs =>
      forall_congr' fun x => forall_congr' fun y => iff_congr
        (restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (objListSig_mem hr h1 h2)) x y)
        (restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (objListSig_mem hs h1 h2)) x y)
  | disjointObjectProperties rs =>
    exact pairwise_iff fun r hr s hs => forall_congr' fun x => forall_congr' fun y => not_congr (and_congr
      (restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (objListSig_mem hr h1 h2)) x y)
      (restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (objListSig_mem hs h1 h2)) x y))
  | inverseObjectProperties r s =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ ((Sig.subset_addObj _ _).2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2))
    have hs : objPropIRI s ≠ topObjectProperty → objPropIRI s ≠ bottomObjectProperty → σ.hasObj (objPropIRI s) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => iff_congr
      (restrictToSig_obj_eq i hr x y) (restrictToSig_obj_eq i hs y x)
  | objectPropertyDomain r c =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have hc := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_obj_eq i hr x y) (restrictToSig_classHolds i hc x)
  | objectPropertyRange r c =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    have hc := Sig.Subset.trans (Sig.subset_addObj _ _) hsub
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_obj_eq i hr x y) (restrictToSig_classHolds i hc y)
  | functionalObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z =>
      imp_congr (restrictToSig_obj_eq i hr x y) (imp_congr (restrictToSig_obj_eq i hr x z) Iff.rfl)
  | inverseFunctionalObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z =>
      imp_congr (restrictToSig_obj_eq i hr y x) (imp_congr (restrictToSig_obj_eq i hr z x) Iff.rfl)
  | reflexiveObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => restrictToSig_obj_eq i hr x x
  | irreflexiveObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => not_congr (restrictToSig_obj_eq i hr x x)
  | symmetricObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_obj_eq i hr x y) (restrictToSig_obj_eq i hr y x)
  | asymmetricObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_obj_eq i hr x y) (not_congr (restrictToSig_obj_eq i hr y x))
  | transitiveObjectProperty r =>
    have hr : objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z =>
      imp_congr (restrictToSig_obj_eq i hr x y)
        (imp_congr (restrictToSig_obj_eq i hr y z) (restrictToSig_obj_eq i hr x z))
  | subDataProperty r s =>
    have hr : r ≠ topDataProperty → r ≠ bottomDataProperty → σ.hasData r = true :=
      fun h1 h2 => hsub.2.2 _ ((Sig.subset_addData _ _).2.2 _ (Sig.hasData_addData_self _ _ h1 h2))
    have hs : s ≠ topDataProperty → s ≠ bottomDataProperty → σ.hasData s = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_data_eq i hr x y) (restrictToSig_data_eq i hs x y)
  | equivalentDataProperties rs =>
    exact forall_congr' fun r => forall_congr' fun hr => forall_congr' fun s => forall_congr' fun hs =>
      forall_congr' fun x => forall_congr' fun y => iff_congr
        (restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (dataListSig_mem hr h1 h2)) x y)
        (restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (dataListSig_mem hs h1 h2)) x y)
  | disjointDataProperties rs =>
    exact pairwise_iff fun r hr s hs => forall_congr' fun x => forall_congr' fun y => not_congr (and_congr
      (restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (dataListSig_mem hr h1 h2)) x y)
      (restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (dataListSig_mem hs h1 h2)) x y))
  | dataPropertyDomain r c =>
    have hr : r ≠ topDataProperty → r ≠ bottomDataProperty → σ.hasData r = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    have hc := Sig.Subset.trans (Sig.subset_addData _ _) hsub
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_data_eq i hr x y) (restrictToSig_classHolds i hc x)
  | dataPropertyRange r t =>
    have hr : r ≠ topDataProperty → r ≠ bottomDataProperty → σ.hasData r = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => imp_congr
      (restrictToSig_data_eq i hr x y) (restrictToSig_dataHolds i σ y t)
  | functionalDataProperty r =>
    have hr : r ≠ topDataProperty → r ≠ bottomDataProperty → σ.hasData r = true :=
      fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z =>
      imp_congr (restrictToSig_data_eq i hr x y) (imp_congr (restrictToSig_data_eq i hr x z) Iff.rfl)
  | datatypeDefinition r t =>
    exact forall_congr' fun y => iff_congr Iff.rfl (restrictToSig_dataHolds i σ y t)
  | hasKey c rs ds =>
    have hc := Sig.Subset.trans (Sig.subset_union_left _ _) (Sig.Subset.trans (Sig.subset_union_left _ _) hsub)
    have hrs : ∀ r ∈ rs, objPropIRI r ≠ topObjectProperty → objPropIRI r ≠ bottomObjectProperty → σ.hasObj (objPropIRI r) = true :=
      fun r hr h1 h2 => hsub.2.1 _ ((Sig.subset_union_left _ _).2.1 _ ((Sig.subset_union_right _ _).2.1 _ (objListSig_mem hr h1 h2)))
    have hds : ∀ p ∈ ds, p ≠ topDataProperty → p ≠ bottomDataProperty → σ.hasData p = true :=
      fun p hp h1 h2 => hsub.2.2 _ ((Sig.subset_union_right _ _).2.2 _ (dataListSig_mem hp h1 h2))
    exact forall_congr' fun x => forall_congr' fun y =>
      imp_congr (restrictToSig_classHolds i hc x)
        (imp_congr (restrictToSig_classHolds i hc y)
          (imp_congr Iff.rfl (imp_congr Iff.rfl
            (imp_congr
              (forall_congr' fun r => forall_congr' fun hr => exists_congr fun z =>
                and_congr Iff.rfl (and_congr (restrictToSig_obj_eq i (hrs r hr) x z) (restrictToSig_obj_eq i (hrs r hr) y z)))
              (imp_congr
                (forall_congr' fun p => forall_congr' fun hp => exists_congr fun z =>
                  and_congr (restrictToSig_data_eq i (hds p hp) x z) (restrictToSig_data_eq i (hds p hp) y z))
                Iff.rfl)))))
  | sameIndividuals _ | differentIndividuals _ => rfl
  | classAssertion c a => exact restrictToSig_classHolds i hsub (i.individuals a)
  | objectAssertion r a b =>
    exact restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)) _ _
  | negativeObjectAssertion r a b =>
    exact not_congr (restrictToSig_obj_eq i (fun h1 h2 => hsub.2.1 _ (Sig.hasObj_addObj_self _ _ h1 h2)) _ _)
  | dataAssertion p a l =>
    exact restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)) _ _
  | negativeDataAssertion p a l =>
    exact not_congr (restrictToSig_data_eq i (fun h1 h2 => hsub.2.2 _ (Sig.hasData_addData_self _ _ h1 h2)) _ _)

/-! ### Syntactic ⊥-locality check and soundness -/

def isBotObjProp (σ : Sig) (r : ObjectProperty) : Bool :=
  let iri := objPropIRI r
  iri == bottomObjectProperty || (iri != topObjectProperty && !σ.hasObj iri)

def isTopObjProp (r : ObjectProperty) : Bool :=
  objPropIRI r == topObjectProperty

def isBotDataProp (σ : Sig) (p : IRI) : Bool :=
  p == bottomDataProperty || (p != topDataProperty && !σ.hasData p)

private theorem isBotObjProp_sound {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    {r : ObjectProperty} (h : isBotObjProp σ r = true) (x y : i.Object) :
    ¬ objectHolds (restrictToSig i σ) r x y := by
  cases r with
  | named rn | inverse rn =>
    simp only [isBotObjProp, objPropIRI, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, Bool.not_eq_true'] at h
    simp only [objectHolds, restrictToSig]
    rcases h with rfl | ⟨hne, hns⟩
    · simp [topObjectProperty, bottomObjectProperty]
    · by_cases hb : rn = bottomObjectProperty
      · subst hb; simp [topObjectProperty, bottomObjectProperty]
      · simp [hne, hb, hns]

private theorem isTopObjProp_sound {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    {r : ObjectProperty} (h : isTopObjProp r = true) (x y : i.Object) :
    objectHolds (restrictToSig i σ) r x y := by
  cases r with
  | named rn | inverse rn =>
    simp only [isTopObjProp, objPropIRI, beq_iff_eq] at h
    subst h; simp [objectHolds, restrictToSig]

private theorem isBotDataProp_sound {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    {p : IRI} (h : isBotDataProp σ p = true) (x : i.Object) (y : i.Data) :
    ¬ (restrictToSig i σ).dataProperties p x y := by
  simp only [isBotDataProp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, Bool.not_eq_true'] at h
  simp only [restrictToSig]
  rcases h with rfl | ⟨hne, hns⟩
  · simp [topDataProperty, bottomDataProperty]
  · by_cases hb : p = bottomDataProperty
    · subst hb; simp [topDataProperty, bottomDataProperty]
    · simp [hne, hb, hns]

mutual
  def isBotExpr (σ : Sig) : ClassExpr → Bool
    | .named c => c == nothing || (c != thing && !σ.hasCls c)
    | .complement c => isTopExpr σ c
    | .intersection a b => isBotExpr σ a || isBotExpr σ b
    | .union a b => isBotExpr σ a && isBotExpr σ b
    | .oneOf inds => inds.isEmpty
    | .objectSome r c => isBotObjProp σ r || isBotExpr σ c
    | .objectAll _ _ => false
    | .objectValue r _ => isBotObjProp σ r
    | .objectSelf r => isBotObjProp σ r
    | .objectMin n r c => decide (n > 0) && (isBotObjProp σ r || isBotExpr σ c)
    | .objectMax _ _ _ => false
    | .objectExact n r c => decide (n > 0) && (isBotObjProp σ r || isBotExpr σ c)
    | .dataSome p _ => isBotDataProp σ p
    | .dataAll _ _ => false
    | .dataValue p _ => isBotDataProp σ p
    | .dataMin n p _ => decide (n > 0) && isBotDataProp σ p
    | .dataMax _ _ _ => false
    | .dataExact n p _ => decide (n > 0) && isBotDataProp σ p

  def isTopExpr (σ : Sig) : ClassExpr → Bool
    | .named c => c == thing
    | .complement c => isBotExpr σ c
    | .intersection a b => isTopExpr σ a && isTopExpr σ b
    | .union a b => isTopExpr σ a || isTopExpr σ b
    | .oneOf _ => false
    | .objectSome _ _ => false
    | .objectAll r c => isBotObjProp σ r || isTopExpr σ c
    | .objectValue _ _ => false
    | .objectSelf _ => false
    | .objectMin n _ _ => n == 0
    | .objectMax _ r c => isBotObjProp σ r || isBotExpr σ c
    | .objectExact _ _ _ => false
    | .dataSome _ _ => false
    | .dataAll p _ => isBotDataProp σ p
    | .dataValue _ _ => false
    | .dataMin n _ _ => n == 0
    | .dataMax _ p _ => isBotDataProp σ p
    | .dataExact _ _ _ => false
end

private theorem not_atLeast_of_empty {α : Type} {n : Nat} {p : α → Prop}
    (hn : n > 0) (he : ∀ x, ¬ p x) : ¬ AtLeast n p := by
  rintro ⟨xs, hl, _, hp⟩
  cases xs with
  | nil => simp at hl; omega
  | cons x _ => exact he x (hp x (List.mem_cons_self ..))

private theorem atLeast_zero {α : Type} (p : α → Prop) : AtLeast 0 p :=
  ⟨[], rfl, List.nodup_nil, fun _ h => by cases h⟩

theorem isBotTopExpr_sound {d : DatatypeMap} (i : Interpretation d) (σ : Sig) (c : ClassExpr) :
    (isBotExpr σ c = true → ∀ x, ¬ classHolds (restrictToSig i σ) x c) ∧
    (isTopExpr σ c = true → ∀ x, classHolds (restrictToSig i σ) x c) := by
  induction c with
  | named cn =>
    constructor
    · intro h x
      simp only [isBotExpr, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true'] at h
      simp only [classHolds, restrictToSig]
      rcases h with rfl | ⟨hne, hns⟩
      · simp [thing, nothing]
      · by_cases hb : cn = nothing
        · subst hb; simp [thing, nothing]
        · simp [hne, hb, hns]
    · intro h x
      simp only [isTopExpr, beq_iff_eq] at h; subst h
      simp [classHolds, restrictToSig]
  | complement a ih =>
    constructor
    · intro h x hx; exact hx (ih.2 h x)
    · intro h x hx; exact ih.1 h x hx
  | intersection a b iha ihb =>
    constructor
    · intro h x ⟨h1, h2⟩
      simp only [isBotExpr, Bool.or_eq_true] at h
      exact h.elim (fun ha => iha.1 ha x h1) (fun hb => ihb.1 hb x h2)
    · intro h x
      simp only [isTopExpr, Bool.and_eq_true] at h
      exact ⟨iha.2 h.1 x, ihb.2 h.2 x⟩
  | union a b iha ihb =>
    constructor
    · intro h x hx
      simp only [isBotExpr, Bool.and_eq_true] at h
      exact hx.elim (iha.1 h.1 x) (ihb.1 h.2 x)
    · intro h x
      simp only [isTopExpr, Bool.or_eq_true] at h
      exact h.elim (fun ha => Or.inl (iha.2 ha x)) (fun hb => Or.inr (ihb.2 hb x))
  | oneOf inds =>
    constructor
    · intro h x ⟨a, ha, _⟩
      cases inds with
      | nil => cases ha
      | cons _ _ => simp [isBotExpr] at h
    · intro h; simp [isTopExpr] at h
  | objectSome r a ih =>
    constructor
    · intro h x ⟨y, hry, hay⟩
      simp only [isBotExpr, Bool.or_eq_true] at h
      exact h.elim (fun hr => isBotObjProp_sound i σ hr x y hry) (fun ha => ih.1 ha y hay)
    · intro h; simp [isTopExpr] at h
  | objectAll r a ih =>
    constructor
    · intro h; simp [isBotExpr] at h
    · intro h x y hry
      simp only [isTopExpr, Bool.or_eq_true] at h
      exact h.elim (fun hr => absurd hry (isBotObjProp_sound i σ hr x y)) (fun ha => ih.2 ha y)
  | objectValue r a =>
    constructor
    · intro h x hx; exact isBotObjProp_sound i σ h x _ hx
    · intro h; simp [isTopExpr] at h
  | objectSelf r =>
    constructor
    · intro h x hx; exact isBotObjProp_sound i σ h x x hx
    · intro h; simp [isTopExpr] at h
  | objectMin n r a ih =>
    constructor
    · intro h x
      simp only [isBotExpr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      refine not_atLeast_of_empty h.1 fun y ⟨hry, hay⟩ => ?_
      exact h.2.elim (fun hr => isBotObjProp_sound i σ hr x y hry) (fun ha => ih.1 ha y hay)
    · intro h x
      simp only [isTopExpr, beq_iff_eq] at h; subst h
      exact atLeast_zero _
  | objectMax n r a ih =>
    constructor
    · intro h; simp [isBotExpr] at h
    · intro h x
      simp only [isTopExpr, Bool.or_eq_true] at h
      refine not_atLeast_of_empty (Nat.succ_pos n) fun y ⟨hry, hay⟩ => ?_
      exact h.elim (fun hr => isBotObjProp_sound i σ hr x y hry) (fun ha => ih.1 ha y hay)
  | objectExact n r a ih =>
    constructor
    · intro h x hx
      simp only [isBotExpr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      refine not_atLeast_of_empty h.1 (fun y ⟨hry, hay⟩ => ?_) hx.1
      exact h.2.elim (fun hr => isBotObjProp_sound i σ hr x y hry) (fun ha => ih.1 ha y hay)
    · intro h; simp [isTopExpr] at h
  | dataSome p dr =>
    constructor
    · intro h x ⟨y, hpy, _⟩; exact isBotDataProp_sound i σ h x y hpy
    · intro h; simp [isTopExpr] at h
  | dataAll p dr =>
    constructor
    · intro h; simp [isBotExpr] at h
    · intro h x y hpy; exact absurd hpy (isBotDataProp_sound i σ h x y)
  | dataValue p l =>
    constructor
    · intro h x hx; exact isBotDataProp_sound i σ h x _ hx
    · intro h; simp [isTopExpr] at h
  | dataMin n p dr =>
    constructor
    · intro h x
      simp only [isBotExpr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact not_atLeast_of_empty h.1 fun y ⟨hpy, _⟩ => isBotDataProp_sound i σ h.2 x y hpy
    · intro h x
      simp only [isTopExpr, beq_iff_eq] at h; subst h
      exact atLeast_zero _
  | dataMax n p dr =>
    constructor
    · intro h; simp [isBotExpr] at h
    · intro h x
      exact not_atLeast_of_empty (Nat.succ_pos n) fun y ⟨hpy, _⟩ => isBotDataProp_sound i σ h x y hpy
  | dataExact n p dr =>
    constructor
    · intro h x hx
      simp only [isBotExpr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact not_atLeast_of_empty h.1 (fun y ⟨hpy, _⟩ => isBotDataProp_sound i σ h.2 x y hpy) hx.1
    · intro h; simp [isTopExpr] at h

def atMostOne {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => if p x then xs.all (fun y => !p y) else atMostOne p xs

private theorem atMostOne_pairwise {α : Type} {p : α → Bool} {xs : List α}
    (h : atMostOne p xs = true) :
    xs.Pairwise fun a b => p a = false ∨ p b = false := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
    simp only [atMostOne] at h
    simp only [List.pairwise_cons]
    cases hx : p x
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      exact ⟨fun y _ => Or.inl rfl, ih h⟩
    · simp only [hx, ↓reduceIte, List.all_eq_true, Bool.not_eq_true'] at h
      refine ⟨fun y hy => Or.inr (h y hy), ?_⟩
      clear hx ih
      induction tail with
      | nil => simp
      | cons z rest ihr =>
        simp only [List.pairwise_cons]
        exact ⟨fun y _ => Or.inl (h z (List.mem_cons_self ..)),
          ihr (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

def isBotLocalAxiom (σ : Sig) : Axiom → Bool
  | .subClassOf a b => isBotExpr σ a || isTopExpr σ b
  | .equivalentClasses cs => cs.all (isBotExpr σ) || cs.all (isTopExpr σ)
  | .disjointClasses cs => atMostOne (fun c => !isBotExpr σ c) cs
  | .disjointUnion h cs => isBotExpr σ (.named h) && cs.all (isBotExpr σ)
  | .subObjectProperty r s => isBotObjProp σ r || isTopObjProp s
  | .subObjectPropertyChain rs s => (!rs.isEmpty && rs.any (isBotObjProp σ)) || isTopObjProp s
  | .equivalentObjectProperties rs => rs.all (isBotObjProp σ) || rs.all isTopObjProp
  | .disjointObjectProperties rs => atMostOne (fun r => !isBotObjProp σ r) rs
  | .inverseObjectProperties r s => (isBotObjProp σ r && isBotObjProp σ s) || (isTopObjProp r && isTopObjProp s)
  | .objectPropertyDomain r c => isBotObjProp σ r || isTopExpr σ c
  | .objectPropertyRange r c => isBotObjProp σ r || isTopExpr σ c
  | .functionalObjectProperty r => isBotObjProp σ r
  | .inverseFunctionalObjectProperty r => isBotObjProp σ r
  | .reflexiveObjectProperty r => isTopObjProp r
  | .irreflexiveObjectProperty r => isBotObjProp σ r
  | .symmetricObjectProperty r => isBotObjProp σ r
  | .asymmetricObjectProperty r => isBotObjProp σ r
  | .transitiveObjectProperty r => isBotObjProp σ r
  | .subDataProperty r s => isBotDataProp σ r || s == topDataProperty
  | .equivalentDataProperties rs => rs.all (isBotDataProp σ) || rs.all (fun p => p == topDataProperty)
  | .disjointDataProperties rs => atMostOne (fun p => !isBotDataProp σ p) rs
  | .dataPropertyDomain r c => isBotDataProp σ r || isTopExpr σ c
  | .dataPropertyRange r _ => isBotDataProp σ r
  | .functionalDataProperty r => isBotDataProp σ r
  | .datatypeDefinition _ _ => false
  | .hasKey c rs ds => isBotExpr σ c || rs.any (isBotObjProp σ) || ds.any (isBotDataProp σ)
  | .sameIndividuals _ => false
  | .differentIndividuals _ => false
  | .classAssertion c _ => isTopExpr σ c
  | .objectAssertion r _ _ => isTopObjProp r
  | .negativeObjectAssertion r _ _ => isBotObjProp σ r
  | .dataAssertion p _ _ => p == topDataProperty
  | .negativeDataAssertion p _ _ => isBotDataProp σ p

private theorem rolePath_bot {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    {rs : List ObjectProperty} (h : rs.any (isBotObjProp σ) = true) (x y : i.Object) :
    ¬ rolePath (restrictToSig i σ) rs x y := by
  induction rs generalizing x with
  | nil => simp at h
  | cons r tail ih =>
    simp only [List.any_cons, Bool.or_eq_true] at h
    rintro ⟨z, hrz, hrest⟩
    exact h.elim (fun hr => isBotObjProp_sound i σ hr x z hrz) (fun ht => ih ht z hrest)

theorem isBotLocalAxiom_sound {d : DatatypeMap} (i : Interpretation d) (σ : Sig)
    {a : Axiom} (h : isBotLocalAxiom σ a = true) :
    axiomHolds (restrictToSig i σ) a := by
  cases a with
  | subClassOf c1 c2 =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h
    intro x hx
    exact h.elim (fun h1 => absurd hx ((isBotTopExpr_sound i σ c1).1 h1 x))
      (fun h2 => (isBotTopExpr_sound i σ c2).2 h2 x)
  | equivalentClasses cs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true] at h
    intro a ha b hb x
    rcases h with hb' | ht'
    · exact ⟨fun h1 => absurd h1 ((isBotTopExpr_sound i σ a).1 (hb' a ha) x),
             fun h2 => absurd h2 ((isBotTopExpr_sound i σ b).1 (hb' b hb) x)⟩
    · exact ⟨fun _ => (isBotTopExpr_sound i σ b).2 (ht' b hb) x,
             fun _ => (isBotTopExpr_sound i σ a).2 (ht' a ha) x⟩
  | disjointClasses cs =>
    simp only [isBotLocalAxiom] at h
    refine List.Pairwise.imp ?_ (atMostOne_pairwise h)
    intro a b hab x ⟨ha, hb⟩
    simp only [Bool.not_eq_false'] at hab
    exact hab.elim (fun h1 => (isBotTopExpr_sound i σ a).1 h1 x ha)
      (fun h2 => (isBotTopExpr_sound i σ b).1 h2 x hb)
  | disjointUnion hd cs =>
    simp only [isBotLocalAxiom, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun x => ⟨fun hx => absurd hx ((isBotTopExpr_sound i σ (.named hd)).1 h.1 x),
      fun ⟨c, hc, hcx⟩ => absurd hcx ((isBotTopExpr_sound i σ c).1 (h.2 c hc) x)⟩, ?_⟩
    have hpw : cs.Pairwise (fun a b => isBotExpr σ a = true) :=
      List.pairwise_iff_getElem.mpr fun j k _ _ _ => h.2 _ (List.getElem_mem ..)
    exact List.Pairwise.imp (fun {a b} ha x ⟨hax, _⟩ => (isBotTopExpr_sound i σ a).1 ha x hax) hpw
  | subObjectProperty r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (isBotObjProp_sound i σ hr x y))
      (fun hs => isTopObjProp_sound i σ hs x y)
  | subObjectPropertyChain rs s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, Bool.and_eq_true] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (rolePath_bot i σ hr.2 x y))
      (fun hs => isTopObjProp_sound i σ hs x y)
  | equivalentObjectProperties rs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true] at h
    intro r hr s hs x y
    rcases h with hb | ht
    · exact ⟨fun h1 => absurd h1 (isBotObjProp_sound i σ (hb r hr) x y),
             fun h2 => absurd h2 (isBotObjProp_sound i σ (hb s hs) x y)⟩
    · exact ⟨fun _ => isTopObjProp_sound i σ (ht s hs) x y,
             fun _ => isTopObjProp_sound i σ (ht r hr) x y⟩
  | disjointObjectProperties rs =>
    simp only [isBotLocalAxiom] at h
    refine List.Pairwise.imp ?_ (atMostOne_pairwise h)
    intro r s hrs x y ⟨hr, hs⟩
    simp only [Bool.not_eq_false'] at hrs
    exact hrs.elim (fun h1 => isBotObjProp_sound i σ h1 x y hr)
      (fun h2 => isBotObjProp_sound i σ h2 x y hs)
  | inverseObjectProperties r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, Bool.and_eq_true] at h
    intro x y
    rcases h with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · exact ⟨fun h1 => absurd h1 (isBotObjProp_sound i σ hr x y),
             fun h2 => absurd h2 (isBotObjProp_sound i σ hs y x)⟩
    · exact ⟨fun _ => isTopObjProp_sound i σ hs y x,
             fun _ => isTopObjProp_sound i σ hr x y⟩
  | objectPropertyDomain r c =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (isBotObjProp_sound i σ hr x y))
      (fun hc => (isBotTopExpr_sound i σ c).2 hc x)
  | objectPropertyRange r c =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (isBotObjProp_sound i σ hr x y))
      (fun hc => (isBotTopExpr_sound i σ c).2 hc y)
  | functionalObjectProperty r =>
    intro x y z hxy _; exact absurd hxy (isBotObjProp_sound i σ h x y)
  | inverseFunctionalObjectProperty r =>
    intro x y z hyx _; exact absurd hyx (isBotObjProp_sound i σ h y x)
  | reflexiveObjectProperty r =>
    intro x; exact isTopObjProp_sound i σ h x x
  | irreflexiveObjectProperty r =>
    intro x; exact isBotObjProp_sound i σ h x x
  | symmetricObjectProperty r =>
    intro x y hxy; exact absurd hxy (isBotObjProp_sound i σ h x y)
  | asymmetricObjectProperty r =>
    intro x y hxy; exact absurd hxy (isBotObjProp_sound i σ h x y)
  | transitiveObjectProperty r =>
    intro x y z hxy _; exact absurd hxy (isBotObjProp_sound i σ h x y)
  | subDataProperty r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, beq_iff_eq] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (isBotDataProp_sound i σ hr x y))
      (fun hs => by subst hs; exact (restrictToSig i σ).topDataExt x y)
  | equivalentDataProperties rs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true, beq_iff_eq] at h
    intro r hr s hs x y
    rcases h with hb | ht
    · exact ⟨fun h1 => absurd h1 (isBotDataProp_sound i σ (hb r hr) x y),
             fun h2 => absurd h2 (isBotDataProp_sound i σ (hb s hs) x y)⟩
    · have hr' := ht r hr; have hs' := ht s hs; subst hr'; subst hs'
      exact ⟨fun _ => (restrictToSig i σ).topDataExt x y, fun _ => (restrictToSig i σ).topDataExt x y⟩
  | disjointDataProperties rs =>
    simp only [isBotLocalAxiom] at h
    refine List.Pairwise.imp ?_ (atMostOne_pairwise h)
    intro r s hrs x y ⟨hr, hs⟩
    simp only [Bool.not_eq_false'] at hrs
    exact hrs.elim (fun h1 => isBotDataProp_sound i σ h1 x y hr)
      (fun h2 => isBotDataProp_sound i σ h2 x y hs)
  | dataPropertyDomain r c =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h
    intro x y hxy
    exact h.elim (fun hr => absurd hxy (isBotDataProp_sound i σ hr x y))
      (fun hc => (isBotTopExpr_sound i σ c).2 hc x)
  | dataPropertyRange r t =>
    intro x y hxy; exact absurd hxy (isBotDataProp_sound i σ h x y)
  | functionalDataProperty r =>
    intro x y z hxy _; exact absurd hxy (isBotDataProp_sound i σ h x y)
  | datatypeDefinition _ _ | sameIndividuals _ | differentIndividuals _ =>
    simp [isBotLocalAxiom] at h
  | hasKey c rs ds =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.any_eq_true] at h
    intro x y hx _ _ _ hrs hds
    rcases h with (hc | ⟨r, hr, hrb⟩) | ⟨p, hp, hpb⟩
    · exact absurd hx ((isBotTopExpr_sound i σ c).1 hc x)
    · obtain ⟨z, _, hrz, _⟩ := hrs r hr
      exact absurd hrz (isBotObjProp_sound i σ hrb x z)
    · obtain ⟨z, hpz, _⟩ := hds p hp
      exact absurd hpz (isBotDataProp_sound i σ hpb x z)
  | classAssertion c a =>
    exact (isBotTopExpr_sound i σ c).2 h _
  | objectAssertion r a b =>
    exact isTopObjProp_sound i σ h _ _
  | negativeObjectAssertion r a b =>
    exact isBotObjProp_sound i σ h _ _
  | dataAssertion p a l =>
    simp only [isBotLocalAxiom, beq_iff_eq] at h; subst h
    exact (restrictToSig i σ).topDataExt _ _
  | negativeDataAssertion p a l =>
    exact isBotDataProp_sound i σ h _ _

/-! ### Syntactic ⊥-locality module extractor & conservativity theorems -/

private def extractStep (rem : Ontology) (σ : Sig) : Ontology × Ontology × Sig :=
  rem.foldl (fun (added, kept, s) a =>
    if isBotLocalAxiom s a then (added, a :: kept, s)
    else (a :: added, kept, s.union (axiomSig a))) ([], [], σ)

private theorem extractStep_props (rem : Ontology) (σ : Sig) :
    let res := extractStep rem σ
    res.1.length + res.2.1.length = rem.length ∧
    σ.Subset res.2.2 ∧
    (∀ a ∈ res.1, a ∈ rem ∧ (axiomSig a).Subset res.2.2) ∧
    (∀ a ∈ res.2.1, a ∈ rem) ∧
    (∀ a ∈ rem, a ∈ res.1 ∨ a ∈ res.2.1) ∧
    (res.1 = [] → res.2.2 = σ ∧ ∀ a ∈ rem, isBotLocalAxiom σ a = true) := by
  have go : ∀ (xs added kept : Ontology) (s : Sig),
      let res := xs.foldl (fun (ad, kp, st) a =>
        if isBotLocalAxiom st a then (ad, a :: kp, st)
        else (a :: ad, kp, st.union (axiomSig a))) (added, kept, s)
      res.1.length + res.2.1.length = added.length + kept.length + xs.length ∧
      s.Subset res.2.2 ∧
      (∀ a ∈ res.1, a ∈ added ∨ (a ∈ xs ∧ (axiomSig a).Subset res.2.2)) ∧
      (∀ a ∈ res.2.1, a ∈ kept ∨ a ∈ xs) ∧
      (∀ a ∈ xs, a ∈ res.1 ∨ a ∈ res.2.1) ∧
      (∀ a ∈ added, a ∈ res.1) ∧
      (∀ a ∈ kept, a ∈ res.2.1) ∧
      (res.1 = added → res.2.2 = s ∧ ∀ a ∈ xs, isBotLocalAxiom s a = true) := by
    intro xs
    induction xs with
    | nil =>
      intro added kept s
      exact ⟨by simp, Sig.Subset.refl s, fun _ h => Or.inl h, fun _ h => Or.inl h,
        (fun _ h => nomatch h), fun _ h => h, fun _ h => h, fun _ => ⟨rfl, (fun _ h => nomatch h)⟩⟩
    | cons a tail ih =>
      intro added kept s
      simp only [List.foldl_cons]
      by_cases hloc : isBotLocalAxiom s a = true
      · simp only [hloc, ↓reduceIte]
        obtain ⟨hlen, hsub, had, hkp, hcov, had_in, hkp_in, hnoop⟩ := ih added (a :: kept) s
        refine ⟨by simp at hlen ⊢; omega, hsub, ?_, ?_, ?_, had_in, ?_, ?_⟩
        · intro x hx
          rcases had x hx with h1 | ⟨h2, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨List.mem_cons_of_mem _ h2, h3⟩
        · intro x hx
          rcases hkp x hx with h1 | h2
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inr (List.mem_cons_self ..)
            · exact Or.inl h1'
          · exact Or.inr (List.mem_cons_of_mem _ h2)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | htail
          · exact Or.inr (hkp_in x (List.mem_cons_self ..))
          · exact hcov x htail
        · intro x hx; exact hkp_in x (List.mem_cons_of_mem _ hx)
        · intro heq
          obtain ⟨hs, hall⟩ := hnoop heq
          refine ⟨hs, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | htail
          · exact hloc
          · exact hall x htail
      · simp only [hloc]
        obtain ⟨hlen, hsub, had, hkp, hcov, had_in, hkp_in, _⟩ := ih (a :: added) kept (s.union (axiomSig a))
        have hsub' := Sig.Subset.trans (Sig.subset_union_left s (axiomSig a)) hsub
        have hasig := Sig.Subset.trans (Sig.subset_union_right s (axiomSig a)) hsub
        refine ⟨by simp at hlen ⊢; omega, hsub', ?_, ?_, ?_, ?_, hkp_in, ?_⟩
        · intro x hx
          rcases had x hx with h1 | ⟨h2, h3⟩
          · rcases List.mem_cons.mp h1 with rfl | h1'
            · exact Or.inr ⟨List.mem_cons_self .., hasig⟩
            · exact Or.inl h1'
          · exact Or.inr ⟨List.mem_cons_of_mem _ h2, h3⟩
        · intro x hx
          rcases hkp x hx with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (List.mem_cons_of_mem _ h2)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | htail
          · exact Or.inl (had_in x (List.mem_cons_self ..))
          · exact hcov x htail
        · intro x hx; exact had_in x (List.mem_cons_of_mem _ hx)
        · intro heq
          have hlen_ge : (a :: added).length ≤ (tail.foldl (fun (ad, kp, st) a =>
              if isBotLocalAxiom st a then (ad, a :: kp, st)
              else (a :: ad, kp, st.union (axiomSig a))) (a :: added, kept, s.union (axiomSig a))).1.length := by
            clear heq
            have : ∀ (l : List Axiom) (ad kp : Ontology) (st : Sig),
                ad.length ≤ (l.foldl (fun (ad, kp, st) a =>
                  if isBotLocalAxiom st a then (ad, a :: kp, st)
                  else (a :: ad, kp, st.union (axiomSig a))) (ad, kp, st)).1.length := by
              intro l; induction l with
              | nil => intro ad kp st; exact Nat.le_refl _
              | cons y ys ihy =>
                intro ad kp st; simp only [List.foldl_cons]
                split
                · exact ihy ad (y :: kp) st
                · exact Nat.le_trans (Nat.le_succ _) (ihy (y :: ad) kp _)
            exact this tail (a :: added) kept (s.union (axiomSig a))
          simp only [Bool.false_eq_true, ↓reduceIte] at heq
          change (tail.foldl (fun (ad, kp, st) a =>
              if isBotLocalAxiom st a then (ad, a :: kp, st)
              else (a :: ad, kp, st.union (axiomSig a))) (a :: added, kept, s.union (axiomSig a))).1 = added at heq
          rw [heq] at hlen_ge
          simp at hlen_ge
          omega
  dsimp only [extractStep]
  obtain ⟨hlen, hsub, had, hkp, hcov, _, _, hnoop⟩ := go rem [] [] σ
  refine ⟨by simpa using hlen, hsub, ?_, ?_, hcov, hnoop⟩
  · intro a ha; exact (had a ha).elim (fun h => nomatch h) id
  · intro a ha; exact (hkp a ha).elim (fun h => nomatch h) id

private def extractLoop (picked rem : Ontology) (σ : Sig) : Ontology × Sig :=
  let res := extractStep rem σ
  if h : res.1.isEmpty then
    (picked.reverse, σ)
  else
    have hlt : res.2.1.length < rem.length := by
      have hlen := (extractStep_props rem σ).1
      cases h1 : (extractStep rem σ).1 with
      | nil => simp [res, h1] at h
      | cons _ _ => rw [h1] at hlen; simp [res] at hlen ⊢; omega
    extractLoop (res.1 ++ picked) res.2.1 res.2.2
termination_by rem.length

/-- Extract a syntactically ⊥-local module `M ⊆ o` and covered signature `σ`
    starting from query signature `seed`. -/
def extractBotModule (o : Ontology) (seed : Sig) : Ontology × Sig :=
  extractLoop [] o seed

private theorem extractLoop_invariants (picked rem : Ontology) (σ : Sig)
    (hpick_sig : ∀ a ∈ picked, (axiomSig a).Subset σ) :
    let res := extractLoop picked rem σ
    σ.Subset res.2 ∧
    (∀ a ∈ res.1, a ∈ picked ∨ a ∈ rem) ∧
    (∀ a ∈ picked, a ∈ res.1) ∧
    (∀ a ∈ res.1, (axiomSig a).Subset res.2) ∧
    (∀ a ∈ rem, a ∈ res.1 ∨ isBotLocalAxiom res.2 a = true) := by
  unfold extractLoop
  dsimp only
  split
  · rename_i hemp
    have hnil : (extractStep rem σ).1 = [] := List.isEmpty_iff.mp hemp
    have hloc := ((extractStep_props rem σ).2.2.2.2.2 hnil).2
    refine ⟨Sig.Subset.refl σ, fun a ha => Or.inl (List.mem_reverse.mp ha),
      fun a ha => List.mem_reverse.mpr ha, fun a ha => hpick_sig a (List.mem_reverse.mp ha),
      fun a ha => Or.inr (hloc a ha)⟩
  · rename_i hne
    have hprops := extractStep_props rem σ
    have hpick' : ∀ a ∈ (extractStep rem σ).1 ++ picked, (axiomSig a).Subset (extractStep rem σ).2.2 := by
      intro a ha
      rcases List.mem_append.mp ha with h1 | h2
      · exact (hprops.2.2.1 a h1).2
      · exact Sig.Subset.trans (hpick_sig a h2) hprops.2.1
    have hlt : (extractStep rem σ).2.1.length < rem.length := by
      have hlen := hprops.1
      cases h1 : (extractStep rem σ).1 with
      | nil => simp [h1] at hne
      | cons _ _ => rw [h1] at hlen; simp at hlen; omega
    obtain ⟨hsub, hmem, hin, hsig, hrem⟩ :=
      extractLoop_invariants ((extractStep rem σ).1 ++ picked) (extractStep rem σ).2.1 (extractStep rem σ).2.2 hpick'
    refine ⟨Sig.Subset.trans hprops.2.1 hsub, ?_, ?_, hsig, ?_⟩
    · intro a ha
      rcases hmem a ha with h1 | h2
      · rcases List.mem_append.mp h1 with h1a | h1b
        · exact Or.inr (hprops.2.2.1 a h1a).1
        · exact Or.inl h1b
      · exact Or.inr (hprops.2.2.2.1 a h2)
    · intro a ha; exact hin a (List.mem_append_right _ ha)
    · intro a ha
      rcases hprops.2.2.2.2.1 a ha with h1 | h2
      · exact Or.inl (hin a (List.mem_append_left _ h1))
      · exact hrem a h2
termination_by rem.length

theorem extractBotModule_subset (o : Ontology) (seed : Sig) :
    ∀ a ∈ (extractBotModule o seed).1, a ∈ o := by
  have h := (extractLoop_invariants [] o seed (fun _ h => by cases h)).2.1
  intro a ha
  rcases h a ha with h1 | h2
  · cases h1
  · exact h2

theorem extractBotModule_seed_subset (o : Ontology) (seed : Sig) :
    seed.Subset (extractBotModule o seed).2 :=
  (extractLoop_invariants [] o seed (fun _ h => by cases h)).1

theorem extractBotModule_mod_sig (o : Ontology) (seed : Sig) :
    ∀ a ∈ (extractBotModule o seed).1, (axiomSig a).Subset (extractBotModule o seed).2 :=
  (extractLoop_invariants [] o seed (fun _ h => by cases h)).2.2.2.1

theorem extractBotModule_local (o : Ontology) (seed : Sig) :
    ∀ a ∈ o, a ∉ (extractBotModule o seed).1 → isBotLocalAxiom (extractBotModule o seed).2 a = true := by
  have h := (extractLoop_invariants [] o seed (fun _ h => by cases h)).2.2.2.2
  intro a ha hnot
  rcases h a ha with h1 | h2
  · exact absurd h1 hnot
  · exact h2

/-- Any model of the extracted ⊥-local module restricts to a model of the full ontology `o`. -/
theorem extractBotModule_models_ext {d : DatatypeMap} (o : Ontology) (seed : Sig)
    {i : Interpretation d} (hmod : models i (extractBotModule o seed).1) :
    models (restrictToSig i (extractBotModule o seed).2) o := by
  obtain ⟨assign, hsat⟩ := hmod
  refine ⟨assign, fun a ha => ?_⟩
  rw [restrictToSig_withAnonymous]
  by_cases hin : a ∈ (extractBotModule o seed).1
  · exact (restrictToSig_axiomHolds (i.withAnonymous assign) (extractBotModule_mod_sig o seed a hin)).mpr (hsat a hin)
  · exact isBotLocalAxiom_sound (i.withAnonymous assign) (extractBotModule o seed).2
      (extractBotModule_local o seed a ha hin)

theorem extractBotModule_sat_iff {d : DatatypeMap} (o : Ontology) (seed : Sig) :
    Satisfiable d o ↔ Satisfiable d (extractBotModule o seed).1 := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    exact ⟨i, assign, fun a ha => hsat a (extractBotModule_subset o seed a ha)⟩
  · rintro ⟨i, hmod⟩
    exact ⟨restrictToSig i (extractBotModule o seed).2, extractBotModule_models_ext o seed hmod⟩

/-- Master ⊥-locality conservativity theorem: for any query ontology `Q` whose
    signature is covered by `seed`, `o` entails `Q` under W3C OWL 2 Direct
    Semantics if and only if the extracted ⊥-local module entails `Q`. -/
theorem extractBotModule_entails_iff {d : DatatypeMap} (o Q : Ontology) (seed : Sig)
    (hQ : ∀ q ∈ Q, (axiomSig q).Subset seed) :
    Entails d o Q ↔ Entails d (extractBotModule o seed).1 Q := by
  constructor
  · intro hent i hmod
    have hfull := extractBotModule_models_ext o seed hmod
    obtain ⟨assign, hq⟩ := hent (restrictToSig i (extractBotModule o seed).2) hfull
    let assign' : String → String → i.Object := assign
    refine ⟨assign', fun q hqm => ?_⟩
    have hqsub := Sig.Subset.trans (hQ q hqm) (extractBotModule_seed_subset o seed)
    exact (restrictToSig_axiomHolds (i.withAnonymous assign') hqsub).mp (hq q hqm)
  · intro hent i ⟨assign, hsat⟩
    exact hent i ⟨assign, fun a ha => hsat a (extractBotModule_subset o seed a ha)⟩

/-! ### OWL 2 DL Fragment Lattice & Feature Profiler -/

inductive Fragment where
  | el
  | dataOnly
  | alc
  | alch
  | alchi
  | rankedRoleChains
  | sroiqd
  deriving DecidableEq, Repr

def Fragment.name : Fragment → String
  | .el => "EL++"
  | .dataOnly => "DataOnly"
  | .alc => "ALC"
  | .alch => "ALCH"
  | .alchi => "ALCHI"
  | .rankedRoleChains => "RankedRoleChains"
  | .sroiqd => "SROIQ(D)"

structure FeatureProfile where
  hasDisjunction : Bool := false
  hasNegation : Bool := false
  hasUniversal : Bool := false
  hasInverse : Bool := false
  hasSubRole : Bool := false
  hasTransitive : Bool := false
  hasRoleChain : Bool := false
  hasCardinality : Bool := false
  hasNominal : Bool := false
  hasSelf : Bool := false
  hasFunctional : Bool := false
  hasRoleChar : Bool := false
  hasObjectRange : Bool := false
  hasReflexive : Bool := false
  hasABox : Bool := false
  hasData : Bool := false
  hasHasKey : Bool := false
  hasDatatypeDef : Bool := false
  hasTopBotProp : Bool := false
  hasObjectLogic : Bool := false
  deriving DecidableEq, Repr

def FeatureProfile.merge (a b : FeatureProfile) : FeatureProfile where
  hasDisjunction := a.hasDisjunction || b.hasDisjunction
  hasNegation := a.hasNegation || b.hasNegation
  hasUniversal := a.hasUniversal || b.hasUniversal
  hasInverse := a.hasInverse || b.hasInverse
  hasSubRole := a.hasSubRole || b.hasSubRole
  hasTransitive := a.hasTransitive || b.hasTransitive
  hasRoleChain := a.hasRoleChain || b.hasRoleChain
  hasCardinality := a.hasCardinality || b.hasCardinality
  hasNominal := a.hasNominal || b.hasNominal
  hasSelf := a.hasSelf || b.hasSelf
  hasFunctional := a.hasFunctional || b.hasFunctional
  hasRoleChar := a.hasRoleChar || b.hasRoleChar
  hasObjectRange := a.hasObjectRange || b.hasObjectRange
  hasReflexive := a.hasReflexive || b.hasReflexive
  hasABox := a.hasABox || b.hasABox
  hasData := a.hasData || b.hasData
  hasHasKey := a.hasHasKey || b.hasHasKey
  hasDatatypeDef := a.hasDatatypeDef || b.hasDatatypeDef
  hasTopBotProp := a.hasTopBotProp || b.hasTopBotProp
  hasObjectLogic := a.hasObjectLogic || b.hasObjectLogic

private def profileObjProp (r : ObjectProperty) : FeatureProfile :=
  let topBot := objPropIRI r == topObjectProperty || objPropIRI r == bottomObjectProperty
  match r with
  | .named _ => { hasObjectLogic := true, hasTopBotProp := topBot }
  | .inverse _ => { hasObjectLogic := true, hasInverse := true, hasTopBotProp := topBot }

def profileClassExpr : ClassExpr → FeatureProfile
  | .named _ => {}
  | .complement c => ({ hasNegation := true, hasObjectLogic := true } : FeatureProfile).merge (profileClassExpr c)
  | .intersection a b => (profileClassExpr a).merge (profileClassExpr b)
  | .union a b => ({ hasDisjunction := true, hasObjectLogic := true } : FeatureProfile).merge
      ((profileClassExpr a).merge (profileClassExpr b))
  | .oneOf _ => { hasNominal := true, hasObjectLogic := true }
  | .objectSome r c => (profileObjProp r).merge (profileClassExpr c)
  | .objectAll r c => ({ hasUniversal := true } : FeatureProfile).merge ((profileObjProp r).merge (profileClassExpr c))
  | .objectValue r _ => ({ hasNominal := true } : FeatureProfile).merge (profileObjProp r)
  | .objectSelf r => ({ hasSelf := true } : FeatureProfile).merge (profileObjProp r)
  | .objectMin _ r c => ({ hasCardinality := true } : FeatureProfile).merge ((profileObjProp r).merge (profileClassExpr c))
  | .objectMax _ r c => ({ hasCardinality := true } : FeatureProfile).merge ((profileObjProp r).merge (profileClassExpr c))
  | .objectExact _ r c => ({ hasCardinality := true } : FeatureProfile).merge ((profileObjProp r).merge (profileClassExpr c))
  | .dataSome p _ => { hasData := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .dataAll p _ => { hasData := true, hasUniversal := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .dataValue p _ => { hasData := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .dataMin _ p _ => { hasData := true, hasCardinality := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .dataMax _ p _ => { hasData := true, hasCardinality := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .dataExact _ p _ => { hasData := true, hasCardinality := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }

def profileAxiom : Axiom → FeatureProfile
  | .subClassOf a b => (profileClassExpr a).merge (profileClassExpr b)
  | .equivalentClasses cs => cs.foldl (fun acc c => acc.merge (profileClassExpr c)) {}
  | .disjointClasses cs => cs.foldl (fun acc c => acc.merge (profileClassExpr c)) {}
  | .disjointUnion _ cs =>
    cs.foldl (fun acc c => acc.merge (profileClassExpr c)) { hasDisjunction := true, hasObjectLogic := true }
  | .subObjectProperty r s =>
    ({ hasSubRole := true } : FeatureProfile).merge ((profileObjProp r).merge (profileObjProp s))
  | .subObjectPropertyChain rs s =>
    let base : FeatureProfile := { hasRoleChain := true }
    let withRs := rs.foldl (fun acc r => acc.merge (profileObjProp r)) base
    withRs.merge (profileObjProp s)
  | .equivalentObjectProperties rs =>
    rs.foldl (fun acc r => acc.merge (profileObjProp r)) { hasSubRole := true }
  | .disjointObjectProperties rs =>
    rs.foldl (fun acc r => acc.merge (profileObjProp r)) { hasRoleChar := true }
  | .inverseObjectProperties r s =>
    ({ hasInverse := true } : FeatureProfile).merge ((profileObjProp r).merge (profileObjProp s))
  | .objectPropertyDomain r c => (profileObjProp r).merge (profileClassExpr c)
  | .objectPropertyRange r c =>
    ({ hasObjectRange := true } : FeatureProfile).merge ((profileObjProp r).merge (profileClassExpr c))
  | .functionalObjectProperty r => ({ hasFunctional := true } : FeatureProfile).merge (profileObjProp r)
  | .inverseFunctionalObjectProperty r =>
    ({ hasFunctional := true, hasInverse := true } : FeatureProfile).merge (profileObjProp r)
  | .reflexiveObjectProperty r => ({ hasReflexive := true } : FeatureProfile).merge (profileObjProp r)
  | .irreflexiveObjectProperty r => ({ hasRoleChar := true } : FeatureProfile).merge (profileObjProp r)
  | .symmetricObjectProperty r => ({ hasRoleChar := true } : FeatureProfile).merge (profileObjProp r)
  | .asymmetricObjectProperty r => ({ hasRoleChar := true } : FeatureProfile).merge (profileObjProp r)
  | .transitiveObjectProperty r => ({ hasTransitive := true } : FeatureProfile).merge (profileObjProp r)
  | .subDataProperty r s => { hasData := true, hasSubRole := true, hasTopBotProp := r == topDataProperty || r == bottomDataProperty || s == topDataProperty || s == bottomDataProperty }
  | .equivalentDataProperties rs => { hasData := true, hasSubRole := true, hasTopBotProp := rs.any (fun p => p == topDataProperty || p == bottomDataProperty) }
  | .disjointDataProperties rs => { hasData := true, hasRoleChar := true, hasTopBotProp := rs.any (fun p => p == topDataProperty || p == bottomDataProperty) }
  | .dataPropertyDomain r c => ({ hasData := true, hasTopBotProp := r == topDataProperty || r == bottomDataProperty } : FeatureProfile).merge (profileClassExpr c)
  | .dataPropertyRange r _ => { hasData := true, hasTopBotProp := r == topDataProperty || r == bottomDataProperty }
  | .functionalDataProperty r => { hasData := true, hasFunctional := true, hasTopBotProp := r == topDataProperty || r == bottomDataProperty }
  | .datatypeDefinition _ _ => { hasData := true, hasDatatypeDef := true }
  | .hasKey c rs ds =>
    let base : FeatureProfile := { hasHasKey := true, hasData := !ds.isEmpty }
    let withRs := rs.foldl (fun acc r => acc.merge (profileObjProp r)) (base.merge (profileClassExpr c))
    withRs
  | .sameIndividuals _ => { hasABox := true, hasNominal := true }
  | .differentIndividuals _ => { hasABox := true }
  | .classAssertion c _ => ({ hasABox := true } : FeatureProfile).merge (profileClassExpr c)
  | .objectAssertion r _ _ => ({ hasABox := true } : FeatureProfile).merge (profileObjProp r)
  | .negativeObjectAssertion r _ _ => ({ hasABox := true } : FeatureProfile).merge (profileObjProp r)
  | .dataAssertion p _ _ => { hasABox := true, hasData := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }
  | .negativeDataAssertion p _ _ => { hasABox := true, hasData := true, hasTopBotProp := p == topDataProperty || p == bottomDataProperty }

def profileOntology (o : Ontology) : FeatureProfile :=
  o.foldl (fun acc a => acc.merge (profileAxiom a)) {}

def FeatureProfile.isEL (fp : FeatureProfile) : Bool :=
  !fp.hasDisjunction && !fp.hasNegation && !fp.hasUniversal && !fp.hasInverse &&
  !fp.hasCardinality && !fp.hasNominal && !fp.hasSelf && !fp.hasFunctional &&
  !fp.hasRoleChar && !fp.hasObjectRange && !fp.hasABox && !fp.hasData &&
  !fp.hasHasKey && !fp.hasDatatypeDef && !fp.hasTopBotProp

def FeatureProfile.isDataOnly (fp : FeatureProfile) : Bool :=
  fp.hasData && !fp.hasObjectLogic && !fp.hasDisjunction && !fp.hasNegation &&
  !fp.hasUniversal && !fp.hasInverse && !fp.hasNominal && !fp.hasSelf && !fp.hasTopBotProp

def FeatureProfile.leastFragment (fp : FeatureProfile) : Fragment :=
  if fp.isEL then .el
  else if fp.isDataOnly then .dataOnly
  else if !fp.hasCardinality && !fp.hasNominal && !fp.hasSelf && !fp.hasFunctional &&
      !fp.hasRoleChar && !fp.hasReflexive && !fp.hasABox && !fp.hasData &&
      !fp.hasHasKey && !fp.hasDatatypeDef && !fp.hasTopBotProp then
    if !fp.hasSubRole && !fp.hasInverse && !fp.hasTransitive && !fp.hasRoleChain then .alc
    else if !fp.hasInverse && !fp.hasTransitive && !fp.hasRoleChain then .alch
    else if !fp.hasTransitive && !fp.hasRoleChain then .alchi
    else .rankedRoleChains
  else .sroiqd

def FeatureProfile.activeNames (fp : FeatureProfile) : List String :=
  let pairs : List (Bool × String) := [
    (fp.hasDisjunction, "disjunction"),
    (fp.hasNegation, "negation"),
    (fp.hasUniversal, "universal"),
    (fp.hasInverse, "inverse"),
    (fp.hasSubRole, "subrole"),
    (fp.hasTransitive, "transitive"),
    (fp.hasRoleChain, "role-chain"),
    (fp.hasCardinality, "cardinality"),
    (fp.hasNominal, "nominal"),
    (fp.hasSelf, "self"),
    (fp.hasFunctional, "functional"),
    (fp.hasRoleChar, "role-characteristics"),
    (fp.hasObjectRange, "object-range"),
    (fp.hasReflexive, "reflexive"),
    (fp.hasABox, "abox"),
    (fp.hasData, "datatypes"),
    (fp.hasHasKey, "has-key"),
    (fp.hasDatatypeDef, "datatype-definition"),
    (fp.hasTopBotProp, "top-or-bottom-property")]
  pairs.filterMap fun (b, s) => if b then some s else none

structure QueryProfile where
  fullAxiomCount : Nat
  moduleAxiomCount : Nat
  fullFeatures : FeatureProfile
  moduleFeatures : FeatureProfile
  fullFragment : Fragment
  moduleFragment : Fragment
  extractedModule : Ontology
  deriving Repr

/-- Profile an ontology `o` (optionally relative to a query axiom `q`).
    When `q = some qa`, extracts the syntactically ⊥-local module for `qa` and
    profiles both the full ontology and the minimal query-sufficient module. -/
def profileQuery (o : Ontology) (q : Option Axiom) : QueryProfile :=
  let fullFp := profileOntology o
  let (mod, modFp) := match q with
    | none => (o, fullFp)
    | some qa =>
      let m := (extractBotModule o (axiomSig qa)).1
      (m, (profileOntology m).merge (profileAxiom qa))
  { fullAxiomCount := o.length
    moduleAxiomCount := mod.length
    fullFeatures := fullFp
    moduleFeatures := modFp
    fullFragment := fullFp.leastFragment
    moduleFragment := modFp.leastFragment
    extractedModule := mod }

end Sabrina.OWL2.Profile
