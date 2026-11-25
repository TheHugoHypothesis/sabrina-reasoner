import Sabrina.OWL2.GradedBridge
import Sabrina.OWL2.WellFormed
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQABox
import Sabrina.OWL2.SROIQD.Termination.ObjectRoleBounds

/-!
Translation from a typed OWL object fragment to the reference SRIQ semantics,
with decision adapters using universal grounding and ranked role bounds.
Named individuals and document-scoped anonymous individuals both become
reference constants. The translation preserves satisfiability under OWL
Direct Semantics without imposing a unique-name assumption.
-/

namespace Sabrina.OWL2.OWLUniversal

open Sabrina.OWL2.SROIQD.TextbookSRIQ
open Sabrina.OWL2.Datatypes (datatypeMap)

private def individualKey (a : Individual) : String :=
  match a with
  | .named n => String.ofList ('n' :: n.toList)
  | .anonymous doc key => String.ofList
      ('a' :: (doc.toList.flatMap fun c => ['d', c]) ++ 'k' :: key.toList)

private def readAnonymousKey : List Char → Option (List Char × List Char)
  | 'd' :: c :: rest => (readAnonymousKey rest).map fun (doc, key) => (c :: doc, key)
  | 'k' :: key => some ([], key)
  | _ => none

private theorem readAnonymousKey_roundtrip (doc key : List Char) :
    readAnonymousKey ((doc.flatMap fun c => ['d', c]) ++ 'k' :: key) = some (doc, key) := by
  induction doc with
  | nil => rfl
  | cons c doc ih => simp [readAnonymousKey, ih]

private def readIndividualKey (s : String) : Option Individual :=
  match s.toList with
  | 'n' :: rest => some (.named (String.ofList rest))
  | 'a' :: rest =>
    (readAnonymousKey rest).map fun (doc, key) => .anonymous (String.ofList doc) (String.ofList key)
  | _ => none

private theorem readIndividualKey_roundtrip (a : Individual) :
    readIndividualKey (individualKey a) = some a := by
  cases a <;> simp [readIndividualKey, individualKey, readAnonymousKey_roundtrip]

private abbrev referenceModel (i : Interpretation d) (classes : String → i.Object → Prop)
    (roles : String → i.Object → i.Object → Prop) : Model :=
  ⟨i.Object, i.objectNonempty, classes, roles⟩

private abbrev referenceABox (i : Interpretation d) (classes : String → i.Object → Prop)
    (roles : String → i.Object → i.Object → Prop) (names : String → i.Object) : ABoxModel :=
  ⟨referenceModel i classes roles, names⟩

private structure Agreement (i : Interpretation d) (classes : String → i.Object → Prop)
    (roles : String → i.Object → i.Object → Prop) (names : String → i.Object) : Prop where
  atoms : ∀ c, c ≠ thing → c ≠ nothing → ∀ x, i.classes c x ↔ classes c x
  edges : ∀ r, r ≠ topObjectProperty → r ≠ bottomObjectProperty → ∀ x y,
    i.objectProperties r x y ↔ roles r x y
  individuals : ∀ a, i.individuals a = names (individualKey a)

private noncomputable def readIndividuals (i : Interpretation d) (s : String) : i.Object :=
  match readIndividualKey s with
  | some a => i.individuals a
  | none => Classical.choice i.objectNonempty

private noncomputable def reduct (i : Interpretation d) : ABoxModel :=
  referenceABox i i.classes i.objectProperties (readIndividuals i)

private theorem reductAgreement (i : Interpretation d) :
    Agreement i i.classes i.objectProperties (readIndividuals i) :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
    fun a => by simp [readIndividuals, readIndividualKey_roundtrip]⟩

private noncomputable def expand (m : ABoxModel) (d : DatatypeMap) : Interpretation d :=
  let i := GradedBridge.extend d
    ⟨m.toModel.Object, m.toModel.nonempty, m.toModel.classes, m.toModel.relations⟩
  { i with
    classes := fun c x => if c = thing then True else if c = nothing then False else m.toModel.classes c x
    objectProperties := fun r x y =>
      if r = topObjectProperty then True else if r = bottomObjectProperty then False
      else m.toModel.relations r x y
    individuals := fun a => m.individuals (individualKey a)
    namedIndividual := fun _ => trivial
    thingExt := by simp
    nothingExt := by intro x; simp [show nothing ≠ thing by decide]
    topObjectExt := by simp
    bottomObjectExt := by intro x y; simp [show bottomObjectProperty ≠ topObjectProperty by decide] }

private theorem expandAgreement (m : ABoxModel) (d : DatatypeMap) :
    Agreement (expand m d) m.toModel.classes m.toModel.relations m.individuals := by
  constructor
  · intro c ht hn x
    simp [expand, ht, hn]
  · intro r ht hb x y
    simp [expand, ht, hb]
  · intro a
    rfl

private def ordinaryRole (r : IRI) : Bool := r != topObjectProperty && r != bottomObjectProperty

private def translateRole : ObjectProperty → Option Role
  | .named r => if ordinaryRole r then some (.named r) else none
  | .inverse r => if ordinaryRole r then some (.inverse r) else none

private theorem translateRole_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) {r : ObjectProperty} {s : Role}
    (hr : translateRole r = some s) (x y : i.Object) :
    objectHolds i r x y ↔ (referenceModel i classes roles).edge s x y := by
  cases r <;> simp only [translateRole] at hr <;> split at hr
  all_goals try contradiction
  all_goals
    rename_i he
    obtain ⟨ht, hb⟩ : _ ∧ _ := Bool.and_eq_true_iff.mp he
    cases hr
    exact h.edges _ (bne_iff_ne.mp ht) (bne_iff_ne.mp hb) _ _

private def translateConcept : ClassExpr → Option Concept
  | .named c => some (if c = thing then .top else if c = nothing then .bottom else .atom c)
  | .complement c => (translateConcept c).map .neg
  | .intersection c e => (translateConcept c).bind fun a => (translateConcept e).map (.conj a)
  | .union c e => (translateConcept c).bind fun a => (translateConcept e).map (.disj a)
  | .objectSome r c => (translateRole r).bind fun s => (translateConcept c).map (.some s)
  | .objectAll r c => (translateRole r).bind fun s => (translateConcept c).map (.all s)
  | .objectMin n r c => (translateRole r).bind fun s => (translateConcept c).map (.min n s)
  | .objectMax n r c => (translateRole r).bind fun s => (translateConcept c).map (.max n s)
  | .objectExact n r c => (translateRole r).bind fun s => (translateConcept c).map fun a =>
      .conj (.min n s a) (.max n s a)
  | .objectSelf r => (translateRole r).map .self
  | _ => none

private theorem translateConcept_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) (c : ClassExpr) {e : Concept}
    (hc : translateConcept c = some e) (x : i.Object) :
    classHolds i x c ↔ (referenceModel i classes roles).holds x e := by
  induction c generalizing e x with
  | named c =>
    simp only [translateConcept] at hc
    split at hc
    · rename_i he
      subst c
      cases hc
      exact ⟨fun _ => trivial, fun _ => i.thingExt x⟩
    · rename_i ht
      split at hc
      · rename_i he
        subst c
        cases hc
        exact ⟨i.nothingExt x, False.elim⟩
      · rename_i hn
        cases hc
        exact h.atoms c ht hn x
  | complement c ih =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact not_congr (ih hp x)
  | intersection c e ihc ihe | union c e ihc ihe =>
    simp only [translateConcept, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨p, hp, q, hq, he⟩ := hc
    cases he
    simp only [classHolds, Model.holds, ihc hp, ihe hq]
  | objectSome r c ih | objectAll r c ih =>
    simp only [translateConcept, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨s, hs, p, hp, he⟩ := hc
    cases he
    simp only [classHolds, Model.holds, translateRole_iff h hs, ih hp]
  | objectMin n r c ih | objectMax n r c ih | objectExact n r c ih =>
    simp only [translateConcept, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨s, hs, a, ha, he⟩ := hc
    cases he
    simp only [classHolds, Exactly, Model.holds, cardinalityAtLeast_iff, translateRole_iff h hs, ih ha]
  | objectSelf r =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact translateRole_iff h hs x x
  | _ => contradiction


private def Role.flip : Role → Role
  | .named r => .inverse r
  | .inverse r => .named r

private theorem flipEdge (m : Model) (r : Role) (x y : m.Object) :
    m.edge (Role.flip r) x y ↔ m.edge r y x := by
  cases r <;> rfl

private theorem pathAppend (m : Model) (as bs : List Role) (x z : m.Object) :
    m.path (as ++ bs) x z ↔ ∃ y, m.path as x y ∧ m.path bs y z := by
  induction as generalizing x with
  | nil => simp [m.path_nil_iff]
  | cons a as ih =>
    simp only [List.cons_append, m.path_cons_iff, ih]
    constructor
    · rintro ⟨v, hv, y, h₁, h₂⟩
      exact ⟨y, ⟨v, hv, h₁⟩, h₂⟩
    · rintro ⟨y, ⟨v, hv, h₁⟩, h₂⟩
      exact ⟨v, hv, y, h₁, h₂⟩

private theorem pathFlip (m : Model) (rs : List Role) (x y : m.Object) :
    m.path (rs.reverse.map Role.flip) y x ↔ m.path rs x y := by
  induction rs generalizing x y with
  | nil => simp [m.path_nil_iff, eq_comm]
  | cons r rs ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton, pathAppend, m.path_cons_iff,
      m.path_nil_iff, exists_eq_right, ih, flipEdge]
    exact exists_congr fun _ => and_comm

private def Inclusion.toNamedHead (first : Role) (rest : List Role) (head : Role) : Inclusion :=
  match head with
  | .named r => ⟨first, rest, r⟩
  | .inverse r =>
    match rest.reverse.map Role.flip with
    | [] => ⟨Role.flip first, [], r⟩
    | s :: ss => ⟨s, ss ++ [Role.flip first], r⟩

private def ModelsInclusion (m : Model) (a : Inclusion) : Prop :=
  ∀ x y, m.path a.body x y → m.edge (.named a.head) x y

private theorem toNamedHead_iff (m : Model) (first : Role) (rest : List Role) (head : Role) :
    ModelsInclusion m (Inclusion.toNamedHead first rest head) ↔
      ∀ x y, m.path (first :: rest) x y → m.edge head x y := by
  cases head with
  | named r => rfl
  | inverse r =>
    have hbody : (Inclusion.toNamedHead first rest (.inverse r)).body =
        (first :: rest).reverse.map Role.flip := by
      unfold Inclusion.toNamedHead
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      split <;> simp_all [Inclusion.body]
    have hhead : (Inclusion.toNamedHead first rest (.inverse r)).head = r := by
      simp only [Inclusion.toNamedHead]
      split <;> rfl
    simp only [ModelsInclusion, hbody, hhead, pathFlip]
    exact ⟨fun h x y hp => h y x hp, fun h x y hp => h y x hp⟩

private theorem translatePath_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) (rs : List ObjectProperty) {ss : List Role}
    (hrs : rs.mapM translateRole = some ss) (x y : i.Object) :
    rolePath i rs x y ↔ (referenceModel i classes roles).path ss x y := by
  induction rs generalizing ss x y with
  | nil =>
    cases hrs
    exact ((referenceModel i classes roles).path_nil_iff x y).symm
  | cons r rs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure] at hrs
    obtain ⟨s, hs, tail, ht, he⟩ := hrs
    cases he
    rw [(referenceModel i classes roles).path_cons_iff]
    simp only [rolePath, translateRole_iff h hs, ih ht]

private def choosePairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ choosePairs xs

private theorem pairs_iff {α : Type} {r : α → α → Prop} (xs : List α) :
    (∀ p ∈ choosePairs xs, r p.1 p.2) ↔ xs.Pairwise r := by
  induction xs with
  | nil => simp [choosePairs]
  | cons x xs ih =>
    simp only [choosePairs, List.mem_append, List.pairwise_cons]
    constructor
    · intro h
      exact ⟨fun y hy => h (x, y) (Or.inl (List.mem_map_of_mem hy)),
        ih.mp (fun p hp => h p (Or.inr hp))⟩
    · rintro ⟨h, ht⟩ p (hp | hp)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
        exact h y hy
      · exact ih.mpr ht p hp

private inductive Clause where
  | gci (a b : Concept)
  | inclusion (a : Inclusion)
  | role (a : RoleAssertion)
  | abox (a : ABoxAssertion)

private def Clause.holds (m : ABoxModel) : Clause → Prop
  | .gci a b => ∀ x, m.toModel.holds x a → m.toModel.holds x b
  | .inclusion a => ModelsInclusion m.toModel a
  | .role a => m.toModel.holdsAssertion a
  | .abox a => m.holdsABox a

private def Clause.add (a : Clause) (kb : KnowledgeBase) : KnowledgeBase :=
  match a with
  | .gci c e => {kb with tboxRBox := {kb.tboxRBox with tbox := (c, e) :: kb.tboxRBox.tbox}}
  | .inclusion r => {kb with tboxRBox := {kb.tboxRBox with hierarchy := r :: kb.tboxRBox.hierarchy}}
  | .role r => {kb with tboxRBox := {kb.tboxRBox with assertions := r :: kb.tboxRBox.assertions}}
  | .abox a => {kb with abox := a :: kb.abox}

private theorem Clause.add_iff (m : ABoxModel) (a : Clause) (kb : KnowledgeBase) :
    m.Models (a.add kb) ↔ a.holds m ∧ m.Models kb := by
  cases a <;> simp [Clause.add, Clause.holds, ModelsInclusion, ABoxModel.Models, Model.Models,
    and_assoc, and_left_comm, and_comm]

private theorem foldClauses_iff (m : ABoxModel) (cs : List Clause) :
    m.Models (cs.foldr Clause.add {}) ↔ ∀ c ∈ cs, c.holds m := by
  induction cs with
  | nil => simp [ABoxModel.Models, Model.Models]
  | cons c cs ih => simp [Clause.add_iff, ih]

private def translateAxiom : Axiom → Option (List Clause)
  | .subClassOf a b =>
    (translateConcept a).bind fun c => (translateConcept b).map fun e => [.gci c e]
  | .subObjectProperty r s =>
    (translateRole r).bind fun r' => (translateRole s).map fun s' =>
      [.inclusion (Inclusion.toNamedHead r' [] s')]
  | .subObjectPropertyChain (r :: rs) s =>
    (translateRole r).bind fun r' => (rs.mapM translateRole).bind fun rs' =>
      (translateRole s).map fun s' => [.inclusion (Inclusion.toNamedHead r' rs' s')]
  | .inverseObjectProperties r s =>
    (translateRole r).bind fun r' => (translateRole s).map fun s' =>
      [.inclusion (Inclusion.toNamedHead r' [] (Role.flip s')),
       .inclusion (Inclusion.toNamedHead (Role.flip s') [] r')]
  | .objectPropertyDomain r c =>
    (translateRole r).bind fun r' => (translateConcept c).map fun c' => [.gci (.some r' .top) c']
  | .objectPropertyRange r c =>
    (translateRole r).bind fun r' => (translateConcept c).map fun c' =>
      [.gci (.some (Role.flip r') .top) c']
  | .transitiveObjectProperty r => (translateRole r).map fun r' => [.role (.transitive r')]
  | .symmetricObjectProperty r => (translateRole r).map fun r' => [.role (.symmetric r')]
  | .irreflexiveObjectProperty r => (translateRole r).map fun r' => [.role (.irreflexive r')]
  | .reflexiveObjectProperty r => (translateRole r).map fun r' => [.gci .top (.self r')]
  | .asymmetricObjectProperty r => (translateRole r).map fun r' => [.role (.disjoint r' (Role.flip r'))]
  | .classAssertion c a => (translateConcept c).map fun c' => [.abox (.concept c' (individualKey a))]
  | .objectAssertion r a b => (translateRole r).map fun r' =>
    [.abox (.role r' (individualKey a) (individualKey b))]
  | .negativeObjectAssertion r a b => (translateRole r).map fun r' =>
    [.abox (.negRole r' (individualKey a) (individualKey b))]
  | .sameIndividuals as => some ((choosePairs as).map fun (a, b) => .abox (.same (individualKey a) (individualKey b)))
  | .differentIndividuals as =>
    some ((choosePairs as).map fun (a, b) => .abox (.different (individualKey a) (individualKey b)))
  | _ => none

private theorem singletonPath (m : Model) (r : Role) (x y : m.Object) :
    m.path [r] x y ↔ m.edge r x y := by
  simp [m.path_cons_iff, m.path_nil_iff]

private theorem pairwise_eq_iff {α β : Type} (f : α → β) (xs : List α) :
    xs.Pairwise (fun a b => f a = f b) ↔ ∀ a ∈ xs, ∀ b ∈ xs, f a = f b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons, ih]
    constructor
    · rintro ⟨hx, ht⟩ a ha b hb
      rcases List.mem_cons.mp ha with hax | ha
      · subst a
        rcases List.mem_cons.mp hb with hbx | hb
        · subst b
          rfl
        · exact hx _ hb
      · rcases List.mem_cons.mp hb with hbx | hb
        · subst b
          exact (hx _ ha).symm
        · exact ht _ ha _ hb
    · intro h
      exact ⟨fun b hb => h x (by simp) b (List.mem_cons_of_mem _ hb),
        fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩

private theorem translateAxiom_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) (a : Axiom) {cs : List Clause}
    (ha : translateAxiom a = some cs) :
    axiomHolds i a ↔ ∀ c ∈ cs, c.holds (referenceABox i classes roles names) := by
  cases a with
  | subClassOf a b =>
    simp only [translateAxiom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨c, hc, e, he, rfl⟩ := ha
    simp only [List.mem_singleton, forall_eq, Clause.holds, axiomHolds, translateConcept_iff h _ hc,
      translateConcept_iff h _ he]
  | subObjectProperty r s | inverseObjectProperties r s =>
    simp only [translateAxiom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨r', hr, s', hs, rfl⟩ := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Clause.holds,
      toNamedHead_iff, singletonPath, flipEdge, axiomHolds, translateRole_iff h hr, translateRole_iff h hs]
    all_goals exact ⟨fun h => ⟨fun x y => (h x y).mp, fun x y => (h x y).mpr⟩,
      fun ⟨h₁, h₂⟩ x y => ⟨h₁ x y, h₂ x y⟩⟩
  | subObjectPropertyChain rs s =>
    cases rs with
    | nil => contradiction
    | cons r rs =>
      simp only [translateAxiom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
      obtain ⟨r', hr, rs', hrs, s', hs, rfl⟩ := ha
      simp only [List.mem_singleton, forall_eq, Clause.holds, toNamedHead_iff, axiomHolds,
        translatePath_iff h _ (show (r :: rs).mapM translateRole = some (r' :: rs') by
          simp [List.mapM_cons, hr, hrs]), translateRole_iff h hs]
  | objectPropertyDomain r c | objectPropertyRange r c =>
    simp only [translateAxiom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨r', hr, c', hc, rfl⟩ := ha
    simp only [List.mem_singleton, forall_eq, Clause.holds, axiomHolds,
      translateRole_iff h hr, translateConcept_iff h _ hc, Model.holds, flipEdge, and_true]
    all_goals
      constructor
      · intro hi x
        rintro ⟨y, hy⟩
        first | exact hi x y hy | exact hi y x hy
      · intro hi x y hxy
        first | exact hi x ⟨y, hxy⟩ | exact hi y ⟨x, hxy⟩
  | transitiveObjectProperty r | symmetricObjectProperty r | irreflexiveObjectProperty r
  | reflexiveObjectProperty r | asymmetricObjectProperty r =>
    simp only [translateAxiom, Option.map_eq_some_iff] at ha
    obtain ⟨r', hr, rfl⟩ := ha
    simp [Clause.holds, axiomHolds, translateRole_iff h hr, Model.holdsAssertion, Model.holds, flipEdge]
  | classAssertion c a =>
    simp only [translateAxiom, Option.map_eq_some_iff] at ha
    obtain ⟨c', hc, rfl⟩ := ha
    simp only [List.mem_singleton, forall_eq, Clause.holds, axiomHolds, ABoxModel.holdsABox,
      translateConcept_iff h _ hc, h.individuals]
  | objectAssertion r a b | negativeObjectAssertion r a b =>
    simp only [translateAxiom, Option.map_eq_some_iff] at ha
    obtain ⟨r', hr, rfl⟩ := ha
    simp only [List.mem_singleton, forall_eq, Clause.holds, axiomHolds, ABoxModel.holdsABox,
      translateRole_iff h hr, h.individuals]
  | sameIndividuals as | differentIndividuals as =>
    cases ha
    simp only [axiomHolds, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Clause.holds, ABoxModel.holdsABox, h.individuals]
    first
    | exact ((pairs_iff (r := fun a b => names (individualKey a) = names (individualKey b)) as).trans
        (pairwise_eq_iff _ _)).symm
    | exact (pairs_iff (r := fun a b => names (individualKey a) ≠ names (individualKey b)) as).symm
  | _ => contradiction

/-- Compile supported object axioms into a reference knowledge base. Unsupported
axioms cause translation failure. The solver applies the separate polarity check. -/
def translateOntology (o : Ontology) : Option KnowledgeBase :=
  (o.mapM translateAxiom).map fun css => css.flatten.foldr Clause.add {}

private theorem translateLists_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) (o : Ontology) {css : List (List Clause)}
    (ho : o.mapM translateAxiom = some css) :
    satisfies i o ↔ ∀ c ∈ css.flatten, c.holds (referenceABox i classes roles names) := by
  induction o generalizing css with
  | nil =>
    cases ho
    simp [satisfies]
  | cons a o ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨cs, ha, tail, ht, he⟩ := ho
    cases he
    simp only [satisfies, List.mem_cons, forall_eq_or_imp, List.flatten_cons, List.mem_append]
    change (axiomHolds i a ∧ satisfies i o) ↔ _
    rw [translateAxiom_iff h a ha, ih ht]
    constructor
    · rintro ⟨h₁, h₂⟩ c (hc | hc)
      · exact h₁ c hc
      · exact h₂ c hc
    · intro hc
      exact ⟨fun c hm => hc c (Or.inl hm), fun c hm => hc c (Or.inr hm)⟩

private theorem translateModels_iff {i : Interpretation d} {classes roles names}
    (h : Agreement i classes roles names) {o : Ontology} {kb : KnowledgeBase}
    (ho : translateOntology o = some kb) :
    satisfies i o ↔ (referenceABox i classes roles names).Models kb := by
  obtain ⟨css, hcss, rfl⟩ := Option.map_eq_some_iff.mp ho
  exact (translateLists_iff h o hcss).trans (foldClauses_iff _ _).symm

theorem translateOntology_sat_iff {o : Ontology} {kb : KnowledgeBase}
    (h : translateOntology o = some kb) (d : DatatypeMap) :
    Satisfiable d o ↔ kb.Sat := by
  constructor
  · rintro ⟨i, assign, hi⟩
    exact ⟨reduct (i.withAnonymous assign), (translateModels_iff (reductAgreement _) h).mp hi⟩
  · rintro ⟨m, hm⟩
    refine ⟨expand m d, satisfies_models ((translateModels_iff (expandAgreement m d) h).mpr ?_)⟩
    exact hm

private def decideKB? (kb : KnowledgeBase) : Option Bool :=
  if h : kb.isUniversal = true then some (kb.decideUniversal h) else none

private theorem decideKB_iff {kb : KnowledgeBase} {b : Bool}
    (h : decideKB? kb = some b) : b = true ↔ kb.Sat := by
  unfold decideKB? at h
  split at h
  · rename_i hu
    cases h
    exact KnowledgeBase.decideUniversal_iff hu
  · contradiction

/-- Admission preserves the typed structural and simple-role checks. Rank
regularity is unnecessary for finite grounding. -/
def decideUniversalOntology? (o : Ontology) : Option Bool :=
  (Normalize.normalizeWithDefs o).bind fun (defs, p) =>
    if o.all (WellFormed.checkAxiom defs) && p.checkSimple then
      (translateOntology o).bind decideKB?
    else none

theorem decideUniversalOntology_iff {o : Ontology} {b : Bool}
    (h : decideUniversalOntology? o = some b) : b = true ↔ Satisfiable datatypeMap o := by
  simp only [decideUniversalOntology?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, _⟩, _, h⟩ := h
  split at h
  · obtain ⟨kb, hkb, h⟩ := Option.bind_eq_some_iff.mp h
    exact (decideKB_iff h).trans (translateOntology_sat_iff hkb _).symm
  · contradiction

#print axioms readIndividualKey_roundtrip
#print axioms translateOntology_sat_iff
#print axioms decideUniversalOntology_iff


/-! Subclass verdicts via the fresh-witness reduction and the existing
universal consistency solver. -/

open Sabrina.ALC (InclusionVerdict)

private theorem subclassHolds_iff {i : Interpretation d} {classes roles names}
    (agreement : Agreement i classes roles names) {a b : ClassExpr} {c e : Concept}
    (ha : translateConcept a = some c) (hb : translateConcept b = some e) :
    axiomHolds i (.subClassOf a b) ↔
      ∀ x, (referenceModel i classes roles).holds x c → (referenceModel i classes roles).holds x e :=
  forall_congr' fun x => imp_congr (translateConcept_iff agreement a ha x) (translateConcept_iff agreement b hb x)

private theorem subclassHolds_withAnonymous_iff (i : Interpretation d)
    (assign : String → String → i.Object) {a b : ClassExpr} {c e : Concept}
    (ha : translateConcept a = some c) (hb : translateConcept b = some e) :
    axiomHolds (i.withAnonymous assign) (.subClassOf a b) ↔ axiomHolds i (.subClassOf a b) :=
  (subclassHolds_iff (reductAgreement (i.withAnonymous assign)) ha hb).trans
    (subclassHolds_iff (reductAgreement i) ha hb).symm

private theorem translateSubclass_entails_iff {o : Ontology} {kb : KnowledgeBase}
    {a b : ClassExpr} {c e : Concept}
    (ho : translateOntology o = some kb) (ha : translateConcept a = some c) (hb : translateConcept b = some e)
    (d : DatatypeMap) :
    Entails d o [.subClassOf a b] ↔
      ∀ m : ABoxModel, m.Models kb → ∀ x, m.toModel.holds x c → m.toModel.holds x e := by
  constructor
  · intro h m hm
    let i := expand m d
    have hmodels := satisfies_models ((translateModels_iff (expandAgreement m d) ho).mpr hm)
    obtain ⟨assign, hass⟩ := h i hmodels
    have hi := (subclassHolds_withAnonymous_iff i assign ha hb).mp (hass _ (List.mem_singleton_self _))
    exact (subclassHolds_iff (expandAgreement m d) ha hb).mp hi
  · rintro h i ⟨assign, hass⟩
    let j := i.withAnonymous assign
    have hm : (reduct j).Models kb := (translateModels_iff (reductAgreement j) ho).mp hass
    refine ⟨assign, ?_⟩
    intro ax hax
    rw [List.mem_singleton.mp hax]
    exact (subclassHolds_iff (reductAgreement j) ha hb).mpr (h (reduct j) hm)

private theorem translatedCounterexample_sat_iff {o : Ontology} {kb : KnowledgeBase}
    {a b : ClassExpr} {c e : Concept}
    (ho : translateOntology o = some kb) (ha : translateConcept a = some c) (hb : translateConcept b = some e)
    (d : DatatypeMap) :
    (kb.withCounterexample c e).Sat ↔ ¬ Entails d o [.subClassOf a b] := by
  rw [KnowledgeBase.counterexample_sat_iff, translateSubclass_entails_iff ho ha hb]
  constructor
  · rintro ⟨m, hm, x, hcx, hex⟩ h
    exact hex (h m hm x hcx)
  · intro hn
    apply Classical.byContradiction
    intro hnone
    apply hn
    intro m hm x hcx
    exact Classical.byContradiction fun hex => hnone ⟨m, hm, x, hcx, hex⟩

private def addSubclass (kb : KnowledgeBase) (c e : Concept) : KnowledgeBase :=
  Clause.add (.gci c e) kb

private theorem translateOntology_addSubclass {o : Ontology} {kb : KnowledgeBase}
    {a b : ClassExpr} {c e : Concept}
    (ho : translateOntology o = some kb) (ha : translateConcept a = some c) (hb : translateConcept b = some e) :
    translateOntology (.subClassOf a b :: o) = some (addSubclass kb c e) := by
  obtain ⟨css, hcss, rfl⟩ := Option.map_eq_some_iff.mp ho
  simp [translateOntology, translateAxiom, ha, hb, List.mapM_cons, hcss, addSubclass]

private def prepareSubclass? (o : Ontology) (a b : ClassExpr) :
    Option (KnowledgeBase × Concept × Concept) :=
  let withQuery := .subClassOf a b :: o
  (Normalize.normalizeWithDefs withQuery).bind fun (defs, p) =>
    if withQuery.all (WellFormed.checkAxiom defs) && p.checkSimple then
      (translateOntology o).bind fun kb =>
        (translateConcept a).bind fun c => (translateConcept b).map fun e => (kb, c, e)
    else none

private theorem prepareSubclass_spec {o : Ontology} {a b : ClassExpr} {kb : KnowledgeBase} {c e : Concept}
    (h : prepareSubclass? o a b = some (kb, c, e)) :
    translateOntology o = some kb ∧ translateConcept a = some c ∧ translateConcept b = some e := by
  simp only [prepareSubclass?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, _⟩, _, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨kb', hkb, c', hc, e', he, htriple⟩ := h
    cases htriple
    exact ⟨hkb, hc, he⟩
  · contradiction

/-- Answer the binary entailment question by checking the counterexample
extension. A satisfiable extension yields `some false`. -/
def decideUniversalEntails? (o : Ontology) (a b : ClassExpr) : Option Bool :=
  (prepareSubclass? o a b).bind fun (kb, c, e) =>
    (decideKB? (kb.withCounterexample c e)).map (! ·)

theorem decideUniversalEntails_iff {o : Ontology} {a b : ClassExpr} {result : Bool}
    (h : decideUniversalEntails? o a b = some result) :
    result = true ↔ Entails datatypeMap o [.subClassOf a b] := by
  simp only [decideUniversalEntails?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨kb, c, e⟩, hp, sat, hsat, hresult⟩ := h
  obtain ⟨hkb, hc, he⟩ := prepareSubclass_spec hp
  have hneg : (!sat) = true ↔ ¬ sat = true := by cases sat <;> decide
  rw [← hresult, hneg, (decideKB_iff hsat).trans (translatedCounterexample_sat_iff hkb hc he _)]
  exact Classical.not_not

/-- Entailment and refutation can use base satisfiability and one refutation.
Independence requires both extensions to have models. -/
private def groundingVerdict (base : Bool) (counter inclusionCase : Unit → Option Bool) :
    Option InclusionVerdict :=
  if base then
    let result := counter ()
    if result = some false then some .entailed
    else
      match inclusionCase () with
      | some false => some .refuted
      | some true => if result = some true then some .independent else none
      | none => none
  else some .inconsistent

private theorem groundingVerdict_sound {o : Ontology} {q : Axiom} {v : InclusionVerdict}
    {base : Bool} {counter inclusionCase : Unit → Option Bool}
    (hbase : base = true ↔ Satisfiable datatypeMap o)
    (hcounter : ∀ {b}, counter () = some b → (b = true ↔ ¬ Entails datatypeMap o [q]))
    (hinclude : ∀ {b}, inclusionCase () = some b → (b = true ↔ Satisfiable datatypeMap (q :: o)))
    (hv : groundingVerdict base counter inclusionCase = some v) :
    Normalize.queryVerdictClaim o q v := by
  cases base with
  | false =>
    cases hv
    exact fun h => Bool.noConfusion (hbase.mpr h)
  | true =>
    by_cases hc : counter () = some false
    · have he : v = .entailed := by simpa [groundingVerdict, hc] using hv.symm
      subst v
      exact ⟨hbase.mp rfl, Classical.byContradiction fun hn => Bool.noConfusion ((hcounter hc).mpr hn)⟩
    · cases hi : inclusionCase () with
      | none => simp [groundingVerdict, hc, hi] at hv
      | some b =>
        cases b with
        | false =>
          have he : v = .refuted := by simpa [groundingVerdict, hc, hi] using hv.symm
          subst v
          exact ⟨hbase.mp rfl, fun hs => Bool.noConfusion ((hinclude hi).mpr hs)⟩
        | true =>
          by_cases hw : counter () = some true
          · have he : v = .independent := by simpa [groundingVerdict, hc, hi, hw] using hv.symm
            subst v
            exact ⟨(hcounter hw).mp rfl, (hinclude hi).mp rfl⟩
          · simp [groundingVerdict, hc, hi, hw] at hv

/-- Classify a subclass query when the consistency checks establish a verdict. -/
private def decideSubclassUsing? (solve : KnowledgeBase → Option Bool) (o : Ontology) (a b : ClassExpr) : Option InclusionVerdict :=
  (prepareSubclass? o a b).bind fun (kb, c, e) =>
    (solve kb).bind fun sat =>
      groundingVerdict sat (fun () => solve (kb.withCounterexample c e))
        (fun () => solve (addSubclass kb c e))

private theorem decideSubclassUsing_sound {solve : KnowledgeBase → Option Bool}
    (correct : ∀ {kb b}, solve kb = some b → (b = true ↔ kb.Sat)) {o : Ontology} {a b : ClassExpr} {v : InclusionVerdict}
    (h : decideSubclassUsing? solve o a b = some v) :
    Normalize.queryVerdictClaim o (.subClassOf a b) v := by
  simp only [decideSubclassUsing?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨kb, c, e⟩, hp, sat, hsat, hv⟩ := h
  obtain ⟨hkb, hc, he⟩ := prepareSubclass_spec hp
  exact groundingVerdict_sound
    ((correct hsat).trans (translateOntology_sat_iff hkb _).symm)
    (fun h => (correct h).trans (translatedCounterexample_sat_iff hkb hc he _))
    (fun h => (correct h).trans
      (translateOntology_sat_iff (translateOntology_addSubclass hkb hc he) _).symm)
    hv

def decideUniversalSubclass? := decideSubclassUsing? decideKB?

theorem decideUniversalSubclass_sound {o : Ontology} {a b : ClassExpr} {v : InclusionVerdict}
    (h : decideUniversalSubclass? o a b = some v) :
    Normalize.queryVerdictClaim o (.subClassOf a b) v :=
  decideSubclassUsing_sound decideKB_iff h

private def decideWithBounds? (kb : KnowledgeBase) : Option Bool :=
  decideKB? kb <|> ObjectRoleBounds.decideObjectHierarchy? kb.toOWL

private theorem decideWithBounds_iff {kb b} (h : decideWithBounds? kb = some b) :
    b = true ↔ kb.Sat := by
  cases hg : decideKB? kb with
  | some v =>
    have he : v = b := by simpa [decideWithBounds?, hg] using h
    exact he ▸ decideKB_iff hg
  | none =>
    have hv : ObjectRoleBounds.decideObjectHierarchy? kb.toOWL = some b := by
      simpa [decideWithBounds?, hg] using h
    exact (ObjectRoleBounds.decideObjectHierarchy_iff hv).trans (kb_satisfiable_toOWL_iff ..)

def decideObjectSubclass? := decideSubclassUsing? decideWithBounds?

theorem decideObjectSubclass_sound {o : Ontology} {a b : ClassExpr} {v : InclusionVerdict}
    (h : decideObjectSubclass? o a b = some v) :
    Normalize.queryVerdictClaim o (.subClassOf a b) v :=
  decideSubclassUsing_sound decideWithBounds_iff h

#print axioms decideObjectSubclass_sound
#print axioms translatedCounterexample_sat_iff
#print axioms decideUniversalEntails_iff
#print axioms decideUniversalSubclass_sound

end Sabrina.OWL2.OWLUniversal
