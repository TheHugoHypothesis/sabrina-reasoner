import Sabrina.OWL2.GradedBridge
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQ

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

/-- The typed translation reserves OWL built-in names for their OWL meanings. -/
def encodeName : String → IRI := GradedBridge.symbol

def Role.toOWL : Role → ObjectProperty
  | .named name => .named (encodeName name)
  | .inverse name => .inverse (encodeName name)

def Concept.toOWL : Concept → ClassExpr
  | .atom name => .named (encodeName name)
  | .top => .named thing
  | .bottom => .named nothing
  | .neg c => .complement c.toOWL
  | .conj c e => .intersection c.toOWL e.toOWL
  | .disj c e => .union c.toOWL e.toOWL
  | .some r c => .objectSome r.toOWL c.toOWL
  | .all r c => .objectAll r.toOWL c.toOWL
  | .self r => .objectSelf r.toOWL
  | .min n r c => .objectMin n r.toOWL c.toOWL
  | .max n r c => .objectMax n r.toOWL c.toOWL

def Inclusion.toOWL (a : Inclusion) : Axiom :=
  match a.rest with
  | [] => .subObjectProperty a.first.toOWL (.named (encodeName a.head))
  | r :: rs => .subObjectPropertyChain ((a.first :: r :: rs).map Role.toOWL)
      (.named (encodeName a.head))

def RoleAssertion.toOWL : RoleAssertion → Axiom
  | .localReflexive r => .subClassOf (.objectSome r.toOWL (.named thing)) (.objectSelf r.toOWL)
  | .irreflexive r => .irreflexiveObjectProperty r.toOWL
  | .symmetric r => .symmetricObjectProperty r.toOWL
  | .transitive r => .transitiveObjectProperty r.toOWL
  | .disjoint r s => .disjointObjectProperties [r.toOWL, s.toOWL]

private def gciToOWL (gci : Concept × Concept) : Axiom :=
  .subClassOf gci.1.toOWL gci.2.toOWL

def TBoxRBox.toOWL (o : TBoxRBox) : Ontology :=
  o.tbox.map gciToOWL ++ o.hierarchy.map Inclusion.toOWL ++
    o.assertions.map RoleAssertion.toOWL

private def Model.fromALC (i : ALC.Interpretation) : Model :=
  ⟨i.Domain, i.nonempty, i.atom, i.role⟩

private def Model.toALC (m : Model) : ALC.Interpretation :=
  ⟨m.Object, m.nonempty, m.classes, m.relations⟩

/-- Forget the data component and read the translated object signature. -/
def Model.fromOWL {d : DatatypeMap} (i : Interpretation d) : Model :=
  fromALC (GradedBridge.reduct i)

/-- Expand an object model with the OWL built-ins and an auxiliary data domain.
The object carrier and all relations on translated names are preserved. -/
noncomputable def Model.toOWL (m : Model) (d : DatatypeMap) : Interpretation d :=
  GradedBridge.extend d m.toALC

theorem Model.fromOWL_toOWL (m : Model) (d : DatatypeMap) :
    fromOWL (m.toOWL d) = m := by
  exact congrArg fromALC (GradedBridge.reduct_extend d m.toALC)

theorem cardinalityAtLeast_iff {α : Type} {p : α → Prop} {n : Nat} :
    AtLeast n p ↔ HasCardinalityAtLeast n p := by
  constructor
  · rintro ⟨xs, rfl, hdistinct, hall⟩
    refine ⟨fun i => xs[i.val]'i.isLt, ?_, fun i => hall _ (List.getElem_mem i.isLt)⟩
    intro a b hab
    exact Fin.ext (hdistinct.eq_of_getElem_eq a.isLt b.isLt hab)
  · rintro ⟨f, hinj, hall⟩
    refine ⟨List.ofFn f, List.length_ofFn, ?_, ?_⟩
    · change (List.ofFn f).Pairwise (· ≠ ·)
      rw [List.pairwise_iff_getElem]
      intro a b ha hb hlt he
      simp only [List.getElem_ofFn] at he
      exact Nat.ne_of_lt hlt (congrArg Fin.val (hinj _ _ he))
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hall i

theorem edge_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (r : Role)
    (x y : i.Object) : objectHolds i r.toOWL x y ↔ (Model.fromOWL i).edge r x y := by
  cases r <;> rfl

theorem path_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (rs : List Role)
    (x y : i.Object) : rolePath i (rs.map Role.toOWL) x y ↔ (Model.fromOWL i).path rs x y := by
  induction rs generalizing x with
  | nil =>
    exact ((Model.fromOWL i).path_nil_iff x y).symm
  | cons r rs ih =>
    change (∃ z, objectHolds i r.toOWL x z ∧ rolePath i (rs.map Role.toOWL) z y) ↔ _
    simp only [edge_fromOWL_iff, ih]
    exact ((Model.fromOWL i).path_cons_iff r rs x y).symm

theorem holds_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (c : Concept)
    (x : i.Object) : classHolds i x c.toOWL ↔ (Model.fromOWL i).holds x c := by
  induction c generalizing x <;>
    simp [Concept.toOWL, classHolds, Model.holds, Model.fromOWL, Model.fromALC,
      GradedBridge.reduct, encodeName, i.thingExt, i.nothingExt, edge_fromOWL_iff,
      cardinalityAtLeast_iff, *]

theorem assertion_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (a : RoleAssertion) :
    axiomHolds i a.toOWL ↔ (Model.fromOWL i).holdsAssertion a := by
  cases a with
  | localReflexive _ =>
    simp only [RoleAssertion.toOWL, axiomHolds, classHolds, i.thingExt, and_true,
      Model.holdsAssertion, edge_fromOWL_iff]
    rfl
  | disjoint _ _ =>
    simp [RoleAssertion.toOWL, axiomHolds, List.pairwise_cons,
      Model.holdsAssertion, edge_fromOWL_iff]
    rfl
  | irreflexive _ | symmetric _ | transitive _ =>
    simp only [RoleAssertion.toOWL, axiomHolds, Model.holdsAssertion, edge_fromOWL_iff]
    rfl

private theorem inclusion_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (a : Inclusion) :
    axiomHolds i a.toOWL ↔
      ∀ x y, (Model.fromOWL i).path a.body x y → (Model.fromOWL i).edge (.named a.head) x y := by
  have head (x y : i.Object) :
      objectHolds i (.named (encodeName a.head)) x y ↔
        (Model.fromOWL i).edge (.named a.head) x y := Iff.rfl
  obtain ⟨first, rest, name⟩ := a
  cases rest with
  | nil =>
    have hpath (x y : (Model.fromOWL i).Object) :
        (Model.fromOWL i).path [first] x y ↔ (Model.fromOWL i).edge first x y := by
      rw [Model.path_cons_iff]
      constructor
      · rintro ⟨z, hz, hp⟩
        exact ((Model.fromOWL i).path_nil_iff z y).mp hp ▸ hz
      · intro h
        exact ⟨y, h, .nil y⟩
    simp only [Inclusion.toOWL, Inclusion.body, axiomHolds, hpath, edge_fromOWL_iff, head]
    rfl
  | cons r rs =>
    change (∀ x y, rolePath i ((first :: r :: rs).map Role.toOWL) x y →
      objectHolds i (.named (encodeName name)) x y) ↔ _
    simp only [path_fromOWL_iff, head, Inclusion.body]
    rfl

theorem models_fromOWL_iff {d : DatatypeMap} (i : Interpretation d) (o : TBoxRBox) :
    satisfies i o.toOWL ↔ (Model.fromOWL i).Models o := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro gci hg
      have hm := h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))
      intro x hx
      exact (holds_fromOWL_iff i gci.2 x).mp
        (hm x ((holds_fromOWL_iff i gci.1 x).mpr hx))
    · intro a ha
      have hm := h _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
      exact (inclusion_fromOWL_iff i a).mp hm
    · intro a ha
      exact (assertion_fromOWL_iff i a).mp (h _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
  · rintro ⟨hgci, hinc, hassert⟩ a ha
    simp only [TBoxRBox.toOWL, List.mem_append, List.mem_map] at ha
    rcases ha with (⟨gci, hg, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨r, hr, rfl⟩
    · intro x hx
      exact (holds_fromOWL_iff i gci.2 x).mpr
        (hgci gci hg x ((holds_fromOWL_iff i gci.1 x).mp hx))
    · exact (inclusion_fromOWL_iff i c).mpr (hinc c hc)
    · exact (assertion_fromOWL_iff i r).mpr (hassert r hr)

theorem satisfiable_toOWL_iff (d : DatatypeMap) (o : TBoxRBox) :
    Satisfiable d o.toOWL ↔ o.Sat := by
  constructor
  · rintro ⟨i, assign, hi⟩
    exact ⟨_, (models_fromOWL_iff (i.withAnonymous assign) o).mp hi⟩
  · rintro ⟨m, hm⟩
    refine ⟨m.toOWL d, satisfies_models ((models_fromOWL_iff _ _).mpr ?_)⟩
    rwa [Model.fromOWL_toOWL]

#print axioms satisfiable_toOWL_iff

end Sabrina.OWL2.SROIQD.TextbookSRIQ
