import Sabrina.OWL2.Syntax

/-! Model theory for the typed axiom closure. The datatype map is a parameter.
Its value space embeds into the data domain, which may contain other values.
The object and data carriers are separate sorts, so they can always be
realized as disjoint sets by tagging them. -/

namespace Sabrina.OWL2

structure DatatypeMap where
  Value : Type
  builtin : IRI → Prop
  valueSpace : IRI → Value → Prop
  lexicalValue : Literal → Option Value
  applicableFacet : IRI → IRI → Value → Prop
  /-- The first IRI names the restricted datatype and the second names the facet. -/
  facetSpace : IRI → IRI → Value → Value → Prop
  literal_not_builtin : ¬ builtin literalDatatype
  lexical_typed : ∀ l v, lexicalValue l = some v → builtin l.datatype ∧ valueSpace l.datatype v
  facet_typed : ∀ t f v w, applicableFacet t f v → facetSpace t f v w → valueSpace t w

def DatatypeMap.validLiteral (d : DatatypeMap) (l : Literal) : Prop :=
  ∃ v, d.lexicalValue l = some v

def DatatypeMap.validFacet (d : DatatypeMap) (t : IRI) (f : Facet) : Prop :=
  d.builtin t ∧ ∃ v, d.lexicalValue f.bound = some v ∧ d.applicableFacet t f.name v

structure Interpretation (d : DatatypeMap) where
  Object : Type
  objectNonempty : Nonempty Object
  Data : Type
  dataNonempty : Nonempty Data
  embedValue : d.Value → Data
  embedValue_injective : ∀ {v w}, embedValue v = embedValue w → v = w
  classes : IRI → Object → Prop
  objectProperties : IRI → Object → Object → Prop
  dataProperties : IRI → Object → Data → Prop
  individuals : Individual → Object
  datatypes : IRI → Data → Prop
  literalValue : Literal → Data
  lexicalAgreement : ∀ l v, d.lexicalValue l = some v → literalValue l = embedValue v
  named : Object → Prop
  namedIndividual : ∀ a, named (individuals (.named a))
  thingExt : ∀ x, classes thing x
  nothingExt : ∀ x, ¬ classes nothing x
  topObjectExt : ∀ x y, objectProperties topObjectProperty x y
  bottomObjectExt : ∀ x y, ¬ objectProperties bottomObjectProperty x y
  topDataExt : ∀ x y, dataProperties topDataProperty x y
  bottomDataExt : ∀ x y, ¬ dataProperties bottomDataProperty x y
  literalDatatypeExt : ∀ y, datatypes literalDatatype y
  datatypeAgreement : ∀ r, d.builtin r → ∀ y,
    datatypes r y ↔ ∃ v, d.valueSpace r v ∧ embedValue v = y

variable {d : DatatypeMap}

def objectHolds (i : Interpretation d) (r : ObjectProperty) (x y : i.Object) : Prop :=
  match r with
  | .named r => i.objectProperties r x y
  | .inverse r => i.objectProperties r y x

theorem objectHolds_converse (i : Interpretation d) (r : ObjectProperty) (x y : i.Object) :
    objectHolds i r.converse x y ↔ objectHolds i r y x := by
  cases r <;> rfl

def facetHolds (i : Interpretation d) (t : IRI) (f : Facet) (x : i.Data) : Prop :=
  ∃ bound value, d.lexicalValue f.bound = some bound ∧ d.facetSpace t f.name bound value ∧
    i.embedValue value = x

theorem literal_value_typed (i : Interpretation d) (l : Literal) (h : d.validLiteral l) :
    i.datatypes l.datatype (i.literalValue l) := by
  obtain ⟨v,hv⟩ := h
  obtain ⟨ht,hm⟩ := d.lexical_typed l v hv
  exact (i.datatypeAgreement _ ht _).mpr ⟨v,hm,(i.lexicalAgreement _ _ hv).symm⟩

/-- Legal literal spellings denote the same domain element exactly when their
    decoded values are identical in the datatype map. -/
theorem literal_value_eq_iff (i : Interpretation d) {l r : Literal} {v w : d.Value}
    (hl : d.lexicalValue l = some v) (hr : d.lexicalValue r = some w) :
    i.literalValue l = i.literalValue r ↔ v = w := by
  rw [i.lexicalAgreement l v hl, i.lexicalAgreement r w hr]
  exact ⟨i.embedValue_injective, congrArg i.embedValue⟩

theorem facet_value_typed (i : Interpretation d) {t : IRI} {f : Facet} {x : i.Data}
    (hf : d.validFacet t f) (hx : facetHolds i t f x) : i.datatypes t x := by
  obtain ⟨ht,b,hb,ha⟩ := hf
  obtain ⟨b',v,hb',hv,hx⟩ := hx
  rw [hb] at hb'
  have he := Option.some.inj hb'
  subst b'
  exact (i.datatypeAgreement _ ht _).mpr ⟨v,d.facet_typed _ _ _ _ ha hv,hx⟩

def dataHolds (i : Interpretation d) (x : i.Data) : DataRange → Prop
  | .datatype r => i.datatypes r x
  | .complement r => ¬ dataHolds i x r
  | .intersection a b => dataHolds i x a ∧ dataHolds i x b
  | .union a b => dataHolds i x a ∨ dataHolds i x b
  | .oneOf ls => ∃ l ∈ ls, i.literalValue l = x
  | .restriction t fs => i.datatypes t x ∧ ∀ f ∈ fs, facetHolds i t f x

/-- Finite bounds count distinct denotations, even in an infinite domain. -/
def AtLeast {α : Type} (n : Nat) (p : α → Prop) : Prop :=
  ∃ xs : List α, xs.length = n ∧ xs.Nodup ∧ ∀ x ∈ xs, p x

theorem atMostOne_iff {α : Type} (p : α → Prop) :
    (¬ AtLeast 2 p) ↔ ∀ x y, p x → p y → x = y := by
  classical
  constructor
  · intro h x y hx hy
    apply Classical.byContradiction
    intro he
    apply h
    refine ⟨[x,y],rfl,by simp [he],?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact (List.mem_singleton.mp hz).symm ▸ hy
  · rintro h ⟨xs,hl,hn,hp⟩
    cases xs with
    | nil => simp at hl
    | cons x tail =>
      cases tail with
      | nil => simp at hl
      | cons y rest =>
        have hx := hp x (List.mem_cons_self ..)
        have hy := hp y (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have he := h x y hx hy
        exact (List.nodup_cons.mp hn).1 (he.symm ▸ List.mem_cons_self ..)

def Exactly {α : Type} (n : Nat) (p : α → Prop) : Prop :=
  AtLeast n p ∧ ¬ AtLeast (n+1) p

def classHolds (i : Interpretation d) (x : i.Object) : ClassExpr → Prop
  | .named c => i.classes c x
  | .complement c => ¬ classHolds i x c
  | .intersection a b => classHolds i x a ∧ classHolds i x b
  | .union a b => classHolds i x a ∨ classHolds i x b
  | .oneOf inds => ∃ a ∈ inds, i.individuals a = x
  | .objectSome r c => ∃ y, objectHolds i r x y ∧ classHolds i y c
  | .objectAll r c => ∀ y, objectHolds i r x y → classHolds i y c
  | .objectValue r a => objectHolds i r x (i.individuals a)
  | .objectSelf r => objectHolds i r x x
  | .objectMin n r c => AtLeast n (fun y => objectHolds i r x y ∧ classHolds i y c)
  | .objectMax n r c => ¬ AtLeast (n+1) (fun y => objectHolds i r x y ∧ classHolds i y c)
  | .objectExact n r c => Exactly n (fun y => objectHolds i r x y ∧ classHolds i y c)
  | .dataSome r t => ∃ y, i.dataProperties r x y ∧ dataHolds i y t
  | .dataAll r t => ∀ y, i.dataProperties r x y → dataHolds i y t
  | .dataValue r l => i.dataProperties r x (i.literalValue l)
  | .dataMin n r t => AtLeast n (fun y => i.dataProperties r x y ∧ dataHolds i y t)
  | .dataMax n r t => ¬ AtLeast (n+1) (fun y => i.dataProperties r x y ∧ dataHolds i y t)
  | .dataExact n r t => Exactly n (fun y => i.dataProperties r x y ∧ dataHolds i y t)

theorem classHolds_intersect (i : Interpretation d) (x : i.Object) (cs : List ClassExpr) :
    classHolds i x (ClassExpr.intersect cs) ↔ ∀ c ∈ cs, classHolds i x c := by
  induction cs with
  | nil => simp [ClassExpr.intersect,classHolds,i.thingExt]
  | cons a tail ih =>
    change classHolds i x a ∧ classHolds i x (ClassExpr.intersect tail) ↔ _
    simp [ih]

theorem classHolds_unite (i : Interpretation d) (x : i.Object) (cs : List ClassExpr) :
    classHolds i x (ClassExpr.unite cs) ↔ ∃ c ∈ cs, classHolds i x c := by
  induction cs with
  | nil => simp [ClassExpr.unite,classHolds,i.nothingExt]
  | cons a tail ih =>
    change classHolds i x a ∨ classHolds i x (ClassExpr.unite tail) ↔ _
    rw [ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨c,hc,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨c,Or.inr hc,h⟩
    · rintro ⟨c,(rfl | hc),h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c,hc,h⟩

theorem dataHolds_intersect (i : Interpretation d) (x : i.Data) (rs : List DataRange) :
    dataHolds i x (DataRange.intersect rs) ↔ ∀ r ∈ rs, dataHolds i x r := by
  induction rs with
  | nil => simp [DataRange.intersect,dataHolds,i.literalDatatypeExt]
  | cons a tail ih =>
    change dataHolds i x a ∧ dataHolds i x (DataRange.intersect tail) ↔ _
    simp [ih]

theorem dataHolds_unite (i : Interpretation d) (x : i.Data) (rs : List DataRange) :
    dataHolds i x (DataRange.unite rs) ↔ ∃ r ∈ rs, dataHolds i x r := by
  induction rs with
  | nil => simp [DataRange.unite,dataHolds,i.literalDatatypeExt]
  | cons a tail ih =>
    change dataHolds i x a ∨ dataHolds i x (DataRange.unite tail) ↔ _
    rw [ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨c,hc,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨c,Or.inr hc,h⟩
    · rintro ⟨c,(rfl | hc),h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c,hc,h⟩

def rolePath (i : Interpretation d) : List ObjectProperty → i.Object → i.Object → Prop
  | [], x, y => x = y
  | r :: rs, x, y => ∃ z, objectHolds i r x z ∧ rolePath i rs z y

def axiomHolds (i : Interpretation d) : Axiom → Prop
  | .subClassOf a b => ∀ x, classHolds i x a → classHolds i x b
  | .equivalentClasses cs =>
    ∀ a ∈ cs, ∀ b ∈ cs, ∀ x, classHolds i x a ↔ classHolds i x b
  | .disjointClasses cs =>
    cs.Pairwise fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b)
  | .disjointUnion h cs =>
    (∀ x, i.classes h x ↔ ∃ c ∈ cs, classHolds i x c) ∧
      cs.Pairwise (fun a b => ∀ x, ¬ (classHolds i x a ∧ classHolds i x b))
  | .subObjectProperty r s => ∀ x y, objectHolds i r x y → objectHolds i s x y
  | .subObjectPropertyChain rs s => ∀ x y, rolePath i rs x y → objectHolds i s x y
  | .equivalentObjectProperties rs =>
    ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, objectHolds i r x y ↔ objectHolds i s x y
  | .disjointObjectProperties rs =>
    rs.Pairwise fun r s => ∀ x y, ¬ (objectHolds i r x y ∧ objectHolds i s x y)
  | .inverseObjectProperties r s => ∀ x y, objectHolds i r x y ↔ objectHolds i s y x
  | .objectPropertyDomain r c => ∀ x y, objectHolds i r x y → classHolds i x c
  | .objectPropertyRange r c => ∀ x y, objectHolds i r x y → classHolds i y c
  | .functionalObjectProperty r => ∀ x y z, objectHolds i r x y → objectHolds i r x z → y = z
  | .inverseFunctionalObjectProperty r =>
    ∀ x y z, objectHolds i r y x → objectHolds i r z x → y = z
  | .reflexiveObjectProperty r => ∀ x, objectHolds i r x x
  | .irreflexiveObjectProperty r => ∀ x, ¬ objectHolds i r x x
  | .symmetricObjectProperty r => ∀ x y, objectHolds i r x y → objectHolds i r y x
  | .asymmetricObjectProperty r => ∀ x y, objectHolds i r x y → ¬ objectHolds i r y x
  | .transitiveObjectProperty r =>
    ∀ x y z, objectHolds i r x y → objectHolds i r y z → objectHolds i r x z
  | .subDataProperty r s => ∀ x y, i.dataProperties r x y → i.dataProperties s x y
  | .equivalentDataProperties rs =>
    ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, i.dataProperties r x y ↔ i.dataProperties s x y
  | .disjointDataProperties rs =>
    rs.Pairwise fun r s => ∀ x y, ¬ (i.dataProperties r x y ∧ i.dataProperties s x y)
  | .dataPropertyDomain r c => ∀ x y, i.dataProperties r x y → classHolds i x c
  | .dataPropertyRange r t => ∀ x y, i.dataProperties r x y → dataHolds i y t
  | .functionalDataProperty r => ∀ x y z, i.dataProperties r x y → i.dataProperties r x z → y = z
  | .datatypeDefinition r t => ∀ y, i.datatypes r y ↔ dataHolds i y t
  | .hasKey c rs ds =>
    ∀ x y, classHolds i x c → classHolds i y c → i.named x → i.named y →
      (∀ r ∈ rs, ∃ z, i.named z ∧ objectHolds i r x z ∧ objectHolds i r y z) →
      (∀ r ∈ ds, ∃ z, i.dataProperties r x z ∧ i.dataProperties r y z) → x = y
  | .sameIndividuals as => ∀ a ∈ as, ∀ b ∈ as, i.individuals a = i.individuals b
  | .differentIndividuals as => as.Pairwise fun a b => i.individuals a ≠ i.individuals b
  | .classAssertion c a => classHolds i (i.individuals a) c
  | .objectAssertion r a b => objectHolds i r (i.individuals a) (i.individuals b)
  | .negativeObjectAssertion r a b => ¬ objectHolds i r (i.individuals a) (i.individuals b)
  | .dataAssertion r a l => i.dataProperties r (i.individuals a) (i.literalValue l)
  | .negativeDataAssertion r a l => ¬ i.dataProperties r (i.individuals a) (i.literalValue l)

def satisfies (i : Interpretation d) (o : Ontology) : Prop :=
  ∀ a ∈ o, axiomHolds i a

/-- Section 2.4 varies only the interpretation of anonymous individuals. -/
def Interpretation.withAnonymous (i : Interpretation d) (assign : String → String → i.Object) :
    Interpretation d :=
  {i with
    individuals := fun
      | .named a => i.individuals (.named a)
      | .anonymous doc key => assign doc key
    namedIndividual := i.namedIndividual}

def models (i : Interpretation d) (o : Ontology) : Prop :=
  ∃ assign : String → String → i.Object, satisfies (i.withAnonymous assign) o

theorem satisfies_models {i : Interpretation d} {o : Ontology} (h : satisfies i o) :
    models i o := by
  let assign := fun doc key => i.individuals (.anonymous doc key)
  have he : i.withAnonymous assign = i := by
    have reassemble {α : Type} (f : Individual → α) :
        (fun a => match a with
          | .named name => f (.named name)
          | .anonymous doc key => f (.anonymous doc key)) = f := by
      funext a
      cases a <;> rfl
    cases i
    simp [assign,Interpretation.withAnonymous,reassemble]
  exact ⟨assign,he.symm ▸ h⟩


def Satisfiable (d : DatatypeMap) (o : Ontology) : Prop :=
  ∃ i : Interpretation d, models i o

/-- A functional data property cannot relate one subject to distinct decoded
    values. This applies to every model, including after anonymous reassignment. -/
theorem functional_data_conflict {o : Ontology} {r : IRI} {a : Individual}
    {l m : Literal} {v w : d.Value}
    (hfun : .functionalDataProperty r ∈ o)
    (hl : .dataAssertion r a l ∈ o) (hm : .dataAssertion r a m ∈ o)
    (hv : d.lexicalValue l = some v) (hw : d.lexicalValue m = some w) (hne : v ≠ w) :
    ¬ Satisfiable d o := by
  rintro ⟨i,assign,hs⟩
  let j := i.withAnonymous assign
  change satisfies j o at hs
  have h := hs _ hfun (j.individuals a) (j.literalValue l) (j.literalValue m)
    (hs _ hl) (hs _ hm)
  exact hne ((literal_value_eq_iff j hv hw).mp h)

def Entails (d : DatatypeMap) (o q : Ontology) : Prop :=
  ∀ i : Interpretation d, models i o → models i q

end Sabrina.OWL2
