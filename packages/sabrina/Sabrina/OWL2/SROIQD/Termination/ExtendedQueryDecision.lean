import Sabrina.OWL2.SROIQD.Termination.ExactQueryDecision

/-! Extended exact four-way query entailment (`ENTAILED`, `REFUTED`,
    `SENTENCE_INDEPENDENT`, `INCONSISTENT_ONTOLOGY`) covering the full OWL 2 DL
    axiom language:
    - All class axioms (`SubClassOf`, n-ary `EquivalentClasses`, n-ary `DisjointClasses`,
      `DisjointUnion`)
    - All object property axioms (`SubObjectPropertyOf`, `SubObjectPropertyChain`,
      n-ary `EquivalentObjectProperties`, n-ary `DisjointObjectProperties`,
      `InverseObjectProperties`, `ObjectPropertyDomain`, `ObjectPropertyRange`,
      `Functional`, `InverseFunctional`, `Reflexive`, `Irreflexive`, `Symmetric`,
      `Asymmetric`, `Transitive`)
    - Data property domain, range, and functionality (`DataPropertyDomain`,
      `DataPropertyRange`, `FunctionalDataProperty`)
    - All ABox assertions (`ClassAssertion`, `(Negative)ObjectPropertyAssertion`,
      `(Negative)DataPropertyAssertion`, n-ary `SameIndividual`, n-ary `DifferentIndividuals`)
    - Existential anonymous-individual queries (`ClassAssertion(C, _:x)`,
      `ObjectPropertyAssertion(r, _:x, b)`, `ObjectPropertyAssertion(r, a, _:y)`,
      `ObjectPropertyAssertion(r, _:x, _:y)`, `DataPropertyAssertion(dp, _:x, l)`).

    All soundness and completeness theorems are kernel-verified over arbitrary
    `DatatypeMap` (and instantiated for `realDatatypeMap` and `datatypeMap`). -/

namespace Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.WellFormed
open Sabrina.ALC (InclusionVerdict)
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.XMLLiteral
open Sabrina.OWL2.SROIQD.Termination.ExactQuery

/-! ### 1. Fresh Anonymous Document Allocator & Assignment Agreement -/

def indAnonDocs : Individual → List String
  | .named _ => []
  | .anonymous d _ => [d]

def classAnonDocs : ClassExpr → List String
  | .named _ => []
  | .complement c => classAnonDocs c
  | .intersection a b | .union a b => classAnonDocs a ++ classAnonDocs b
  | .oneOf inds => inds.flatMap indAnonDocs
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c =>
    classAnonDocs c
  | .objectValue _ a => indAnonDocs a
  | .objectSelf _ => []
  | .dataSome _ _ | .dataAll _ _ | .dataValue _ _
  | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => []

def axiomAnonDocs : Axiom → List String
  | .subClassOf a b => classAnonDocs a ++ classAnonDocs b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs => cs.flatMap classAnonDocs
  | .objectPropertyDomain _ c | .objectPropertyRange _ c | .dataPropertyDomain _ c => classAnonDocs c
  | .hasKey c _ _ => classAnonDocs c
  | .sameIndividuals inds | .differentIndividuals inds => inds.flatMap indAnonDocs
  | .classAssertion c a => classAnonDocs c ++ indAnonDocs a
  | .objectAssertion _ a b | .negativeObjectAssertion _ a b => indAnonDocs a ++ indAnonDocs b
  | .dataAssertion _ a _ | .negativeDataAssertion _ a _ => indAnonDocs a
  | _ => []

def ontAnonDocs (o : Ontology) : List String :=
  o.flatMap axiomAnonDocs

private def maxStrLen : List String → Nat
  | [] => 0
  | s :: rest => max s.length (maxStrLen rest)

private theorem le_maxStrLen {s : String} {xs : List String} (h : s ∈ xs) :
    s.length ≤ maxStrLen xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- A document identifier guaranteed not to appear in any anonymous individual of `o`. -/
def freshAnonDoc (o : Ontology) : String :=
  String.ofList (List.replicate (maxStrLen (ontAnonDocs o) + 1) 'q')

theorem freshAnonDoc_not_mem (o : Ontology) : freshAnonDoc o ∉ ontAnonDocs o := by
  intro hmem
  have hle := le_maxStrLen hmem
  have hlen : (freshAnonDoc o).length = maxStrLen (ontAnonDocs o) + 1 := by
    simp [freshAnonDoc]
  omega

private theorem dataHolds_withAnonymous_eq {dm : DatatypeMap} (i : Interpretation dm)
    (a1 a2 : String → String → i.Object) (y : i.Data) (d : DataRange) :
    dataHolds (i.withAnonymous a1) y d ↔ dataHolds (i.withAnonymous a2) y d := by
  induction d with
  | datatype _ | oneOf _ | restriction _ _ => exact Iff.rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ia ib => exact and_congr ia ib
  | union _ _ ia ib => exact or_congr ia ib

private theorem ind_withAnonymous_agree {dm : DatatypeMap} (i : Interpretation dm)
    {a1 a2 : String → String → i.Object} {ind : Individual}
    (hag : ∀ d ∈ indAnonDocs ind, ∀ loc, a1 d loc = a2 d loc) :
    (i.withAnonymous a1).individuals ind = (i.withAnonymous a2).individuals ind := by
  cases ind with
  | named _ => rfl
  | anonymous d loc =>
    exact hag d (List.mem_cons_self ..) loc

private theorem classHolds_withAnonymous_agree {dm : DatatypeMap} (i : Interpretation dm)
    {a1 a2 : String → String → i.Object} (x : i.Object) {c : ClassExpr}
    (hag : ∀ d ∈ classAnonDocs c, ∀ loc, a1 d loc = a2 d loc) :
    classHolds (i.withAnonymous a1) x c ↔ classHolds (i.withAnonymous a2) x c := by
  induction c generalizing x with
  | named _ | objectSelf _ | dataValue _ _ => exact Iff.rfl
  | complement c ih => exact not_congr (ih x hag)
  | intersection a b iha ihb =>
    exact and_congr
      (iha x (fun d hd => hag d (List.mem_append_left _ hd)))
      (ihb x (fun d hd => hag d (List.mem_append_right _ hd)))
  | union a b iha ihb =>
    exact or_congr
      (iha x (fun d hd => hag d (List.mem_append_left _ hd)))
      (ihb x (fun d hd => hag d (List.mem_append_right _ hd)))
  | oneOf inds =>
    simp only [classHolds]
    constructor
    · rintro ⟨ind, hind, heq⟩
      exact ⟨ind, hind, by rw [← ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨ind, hind, hd⟩))]; exact heq⟩
    · rintro ⟨ind, hind, heq⟩
      exact ⟨ind, hind, by rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨ind, hind, hd⟩))]; exact heq⟩
  | objectSome r c ih =>
    exact exists_congr fun y => and_congr Iff.rfl (ih y hag)
  | objectAll r c ih =>
    exact forall_congr' fun y => imp_congr Iff.rfl (ih y hag)
  | objectValue r a =>
    simp only [classHolds]
    rw [ind_withAnonymous_agree i hag]
    cases r <;> exact Iff.rfl
  | objectMin n r c ih =>
    simp only [classHolds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y hag))))
  | objectMax n r c ih =>
    simp only [classHolds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y hag)))))
  | objectExact n r c ih =>
    simp only [classHolds, Exactly, AtLeast]
    exact and_congr
      (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y hag)))))
      (not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (ih y hag))))))
  | dataSome dp d =>
    exact exists_congr fun y => and_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)
  | dataAll dp d =>
    exact forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)
  | dataMin n dp d =>
    simp only [classHolds, AtLeast]
    exact exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d))))
  | dataMax n dp d =>
    simp only [classHolds, AtLeast]
    exact not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)))))
  | dataExact n dp d =>
    simp only [classHolds, Exactly, AtLeast]
    exact and_congr
      (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)))))
      (not_congr (exists_congr fun xs => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => imp_congr Iff.rfl (and_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d))))))

private theorem pairwise_iff {α : Type} {P Q : α → α → Prop} :
    ∀ {xs : List α}, (∀ a ∈ xs, ∀ b ∈ xs, P a b ↔ Q a b) → (xs.Pairwise P ↔ xs.Pairwise Q)
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.pairwise_cons]
    refine and_congr ?_ (pairwise_iff (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))
    exact ⟨fun hx y hy => (h x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)).mp (hx y hy),
           fun hx y hy => (h x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)).mpr (hx y hy)⟩

private theorem axiomHolds_withAnonymous_agree {dm : DatatypeMap} (i : Interpretation dm)
    {a1 a2 : String → String → i.Object} {ax : Axiom}
    (hag : ∀ d ∈ axiomAnonDocs ax, ∀ loc, a1 d loc = a2 d loc) :
    axiomHolds (i.withAnonymous a1) ax ↔ axiomHolds (i.withAnonymous a2) ax := by
  cases ax with
  | subClassOf a b =>
    exact forall_congr' fun x => imp_congr
      (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_append_left _ hd)))
      (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_append_right _ hd)))
  | equivalentClasses cs =>
    simp only [axiomHolds]
    constructor
    · intro h a ha b hb x
      exact (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩))).symm.trans
        ((h a ha b hb x).trans (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))))
    · intro h a ha b hb x
      exact (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩))).trans
        ((h a ha b hb x).trans (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))).symm)
  | disjointClasses cs =>
    exact pairwise_iff fun a ha b hb => forall_congr' fun x => not_congr (and_congr
      (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩)))
      (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))))
  | disjointUnion h cs =>
    refine and_congr (forall_congr' fun x => iff_congr Iff.rfl ?_) ?_
    · constructor
      · rintro ⟨c, hc, hx⟩
        exact ⟨c, hc, (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨c, hc, hd⟩))).mp hx⟩
      · rintro ⟨c, hc, hx⟩
        exact ⟨c, hc, (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨c, hc, hd⟩))).mpr hx⟩
    · exact pairwise_iff fun a ha b hb => forall_congr' fun x => not_congr (and_congr
        (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩)))
        (classHolds_withAnonymous_agree i x (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))))
  | objectPropertyDomain r c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr (by cases r <;> exact Iff.rfl) (classHolds_withAnonymous_agree i x hag)
  | objectPropertyRange r c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr (by cases r <;> exact Iff.rfl) (classHolds_withAnonymous_agree i y hag)
  | dataPropertyDomain dp c =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (classHolds_withAnonymous_agree i x hag)
  | dataPropertyRange dp d =>
    exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)
  | datatypeDefinition dt d =>
    exact forall_congr' fun y => iff_congr Iff.rfl (dataHolds_withAnonymous_eq i a1 a2 y d)
  | hasKey c os ds =>
    have hobj : ∀ r x z, objectHolds (i.withAnonymous a1) r x z ↔ objectHolds (i.withAnonymous a2) r x z := by
      intro r x z; cases r <;> exact Iff.rfl
    simp only [axiomHolds, Interpretation.withAnonymous]
    refine forall_congr' fun x => forall_congr' fun y =>
      imp_congr (classHolds_withAnonymous_agree i x hag)
        (imp_congr (classHolds_withAnonymous_agree i y hag)
          (imp_congr Iff.rfl (imp_congr Iff.rfl
            (imp_congr (forall_congr' fun r => imp_congr Iff.rfl (exists_congr fun z =>
              and_congr Iff.rfl (and_congr (hobj r x z) (hobj r y z)))) Iff.rfl))))
  | sameIndividuals inds =>
    simp only [axiomHolds]
    constructor
    · intro h a ha b hb
      rw [← ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩)),
          ← ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))]
      exact h a ha b hb
    · intro h a ha b hb
      rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩)),
          ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))]
      exact h a ha b hb
  | differentIndividuals inds =>
    exact pairwise_iff fun a ha b hb => by
      rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨a, ha, hd⟩)),
          ind_withAnonymous_agree i (fun d hd => hag d (List.mem_flatMap.mpr ⟨b, hb, hd⟩))]
      exact Iff.rfl
  | classAssertion c a =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_append_right _ hd))]
    exact classHolds_withAnonymous_agree i _ (fun d hd => hag d (List.mem_append_left _ hd))
  | objectAssertion r a b =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_append_left _ hd)),
        ind_withAnonymous_agree i (fun d hd => hag d (List.mem_append_right _ hd))]
    cases r <;> exact Iff.rfl
  | negativeObjectAssertion r a b =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_agree i (fun d hd => hag d (List.mem_append_left _ hd)),
        ind_withAnonymous_agree i (fun d hd => hag d (List.mem_append_right _ hd))]
    cases r <;> exact Iff.rfl
  | dataAssertion dp a l =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_agree i hag]
    exact Iff.rfl
  | negativeDataAssertion dp a l =>
    simp only [axiomHolds]
    rw [ind_withAnonymous_agree i hag]
    exact Iff.rfl
  | subObjectProperty r s | inverseObjectProperties r s => cases r <;> cases s <;> exact Iff.rfl
  | subObjectPropertyChain rs s =>
    have hpath : ∀ (rs : List ObjectProperty) (x y : i.Object),
        rolePath (i.withAnonymous a1) rs x y ↔ rolePath (i.withAnonymous a2) rs x y := by
      intro rs
      induction rs with
      | nil => intro x y; exact Iff.rfl
      | cons r rs ih =>
        intro x y
        constructor
        · rintro ⟨z, hz1, hz2⟩
          exact ⟨z, (by cases r <;> exact hz1), (ih z y).mp hz2⟩
        · rintro ⟨z, hz1, hz2⟩
          exact ⟨z, (by cases r <;> exact hz1), (ih z y).mpr hz2⟩
    exact forall_congr' fun x : i.Object => forall_congr' fun y : i.Object =>
      imp_congr (hpath rs x y) (by cases s <;> exact Iff.rfl)
  | equivalentObjectProperties rs =>
    exact forall_congr' fun r => imp_congr Iff.rfl (forall_congr' fun s => imp_congr Iff.rfl
      (forall_congr' fun x => forall_congr' fun y => iff_congr (by cases r <;> exact Iff.rfl) (by cases s <;> exact Iff.rfl)))
  | disjointObjectProperties rs =>
    exact pairwise_iff fun r _ s _ => forall_congr' fun x => forall_congr' fun y =>
      not_congr (and_congr (by cases r <;> exact Iff.rfl) (by cases s <;> exact Iff.rfl))
  | functionalObjectProperty r | inverseFunctionalObjectProperty r
  | reflexiveObjectProperty r | irreflexiveObjectProperty r
  | symmetricObjectProperty r | asymmetricObjectProperty r | transitiveObjectProperty r =>
    cases r <;> exact Iff.rfl
  | subDataProperty _ _ | equivalentDataProperties _ | disjointDataProperties _ | functionalDataProperty _ =>
    exact Iff.rfl

/-- Master separation lemma: if every axiom in `branch` uses only fresh anonymous
    document `d` (`d ∉ ontAnonDocs o`), then `i` models `branch ++ o` iff `i` models `o`
    AND there exists a local witness assignment for `d` satisfying `branch`. -/
theorem models_fresh_branch_iff {dm : DatatypeMap} (i : Interpretation dm)
    (o branch : Ontology) (d : String)
    (hfresh : d ∉ ontAnonDocs o)
    (hbranch : ∀ ax ∈ branch, ∀ d' ∈ axiomAnonDocs ax, d' = d) :
    models i (branch ++ o) ↔
      models i o ∧ ∃ f : String → i.Object, ∀ ax ∈ branch,
        axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax := by
  constructor
  · rintro ⟨assign, hsat⟩
    refine ⟨⟨assign, fun ax hax => hsat ax (List.mem_append_right _ hax)⟩,
      fun loc => assign d loc, fun ax hax => ?_⟩
    have h1 := hsat ax (List.mem_append_left _ hax)
    exact (axiomHolds_withAnonymous_agree i (fun d' hd' loc => by
      have heq := hbranch ax hax d' hd'; subst heq; rfl)).mp h1
  · rintro ⟨⟨assign, hsat⟩, f, hf⟩
    let assign' : String → String → i.Object := fun d' loc => if d' = d then f loc else assign d' loc
    refine ⟨assign', fun ax hax => ?_⟩
    rcases List.mem_append.mp hax with hb | ho
    · exact (axiomHolds_withAnonymous_agree i (fun d' hd' loc => by
        have heq := hbranch ax hb d' hd'; subst heq; simp [assign'])).mp (hf ax hb)
    · exact (axiomHolds_withAnonymous_agree i (fun d' hd' loc => by
        have hne : d' ≠ d := fun heq => hfresh (heq ▸ List.mem_flatMap.mpr ⟨ax, ho, hd'⟩)
        simp [assign', hne])).mpr (hsat ax ho)

/-! ### 2. Pairwise & Chain Helper Combinators -/

def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

theorem mem_unorderedPairs_iff {α : Type} {xs : List α} {p : α × α} :
    p ∈ unorderedPairs xs → p.1 ∈ xs ∧ p.2 ∈ xs := by
  induction xs with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    simp only [unorderedPairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h'
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hy⟩
    · obtain ⟨h1, h2⟩ := ih h'
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem pairwise_iff_unorderedPairs {α : Type} (P : α → α → Prop) (xs : List α) :
    xs.Pairwise P ↔ ∀ p ∈ unorderedPairs xs, P p.1 p.2 := by
  induction xs with
  | nil => simp [unorderedPairs]
  | cons x xs ih =>
    simp only [List.pairwise_cons, unorderedPairs, List.mem_append, List.mem_map, ih]
    constructor
    · rintro ⟨hx, hxs⟩ p (⟨y, hy, rfl⟩ | hp)
      · exact hx y hy
      · exact hxs p hp
    · intro h
      refine ⟨fun y hy => h (x, y) (Or.inl ⟨y, hy, rfl⟩), fun p hp => h p (Or.inr hp)⟩

def orderedPairs {α : Type} (xs : List α) : List (α × α) :=
  xs.flatMap fun a => xs.map fun b => (a, b)

theorem mem_orderedPairs_iff {α : Type} {xs : List α} {a b : α} :
    (a, b) ∈ orderedPairs xs ↔ a ∈ xs ∧ b ∈ xs := by
  simp [orderedPairs]

private def natTag (n : Nat) : String :=
  String.ofList (List.replicate (n + 1) 'n')

private theorem natTag_length (n : Nat) : (natTag n).length = n + 1 := by
  simp [natTag]

private theorem natTag_injective {i j : Nat} (h : natTag i = natTag j) : i = j := by
  have hl := congrArg String.length h
  rw [natTag_length, natTag_length] at hl
  omega

private def chainAssertions (d : String) : Nat → List ObjectProperty → List Axiom
  | _, [] => []
  | k, r :: rs =>
    .objectAssertion r (.anonymous d (natTag k)) (.anonymous d (natTag (k + 1))) ::
      chainAssertions d (k + 1) rs

private theorem chainAssertions_docs (d : String) (k : Nat) (rs : List ObjectProperty) :
    ∀ ax ∈ chainAssertions d k rs, ∀ d' ∈ axiomAnonDocs ax, d' = d := by
  induction rs generalizing k with
  | nil => intro _ h; cases h
  | cons r rs ih =>
    intro ax hax d' hd'
    rcases List.mem_cons.mp hax with rfl | h'
    · simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'
      exact hd'.elim id id
    · exact ih (k + 1) ax h' d' hd'

private theorem chainAssertions_holds_iff {dm : DatatypeMap} (i : Interpretation dm)
    (d : String) (k : Nat) (rs : List ObjectProperty) (f : String → i.Object) :
    (∀ ax ∈ chainAssertions d k rs, axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax) ↔
      (∀ idx : Nat, (h : idx < rs.length) →
        objectHolds i rs[idx] (f (natTag (k + idx))) (f (natTag (k + idx + 1)))) := by
  induction rs generalizing k with
  | nil => simp [chainAssertions]
  | cons r rs ih =>
    simp only [chainAssertions, List.mem_cons, forall_eq_or_imp, ih (k + 1)]
    have hr : axiomHolds (i.withAnonymous (fun _ loc => f loc))
        (.objectAssertion r (.anonymous d (natTag k)) (.anonymous d (natTag (k + 1)))) ↔
        objectHolds i r (f (natTag k)) (f (natTag (k + 1))) := by
      cases r <;> exact Iff.rfl
    rw [hr]
    constructor
    · rintro ⟨h0, hrest⟩ idx hidx
      cases idx with
      | zero => simpa using h0
      | succ m =>
        have := hrest m (by simpa using hidx)
        simpa [Nat.add_assoc, Nat.add_comm 1 m] using this
    · intro hall
      refine ⟨?_, fun m hm => ?_⟩
      · have h0 := hall 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        exact h0
      · have h' := hall (m + 1) (by simpa using hm)
        simp only [List.getElem_cons_succ] at h'
        have heq1 : k + (m + 1) = k + 1 + m := by omega
        simpa [heq1] using h'

private theorem exists_chain_witness {dm : DatatypeMap} (i : Interpretation dm)
    (d : String) (k : Nat) (rs : List ObjectProperty) (x y : i.Object) :
    rolePath i rs x y ↔
      ∃ f : String → i.Object,
        f (natTag k) = x ∧ f (natTag (k + rs.length)) = y ∧
        ∀ ax ∈ chainAssertions d k rs, axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax := by
  induction rs generalizing k x with
  | nil =>
    simp only [rolePath, chainAssertions, List.length_nil, Nat.add_zero, List.not_mem_nil,
      false_implies, implies_true, and_true]
    constructor
    · rintro rfl; exact ⟨fun _ => x, rfl, rfl⟩
    · rintro ⟨f, h1, h2⟩; exact h1.symm.trans h2
  | cons r rs ih =>
    simp only [rolePath, chainAssertions, List.length_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨z, hxz, hpath⟩
      obtain ⟨f, hfz, hfy, hrest⟩ := (ih (k + 1) z).mp hpath
      let f' : String → i.Object := fun tag => if tag = natTag k then x else f tag
      refine ⟨f', by simp [f'], ?_, ?_, ?_⟩
      · have hne : natTag (k + (rs.length + 1)) ≠ natTag k := fun h => by
          have := natTag_injective h; omega
        simp only [f', hne, ↓reduceIte]
        have heq : k + (rs.length + 1) = k + 1 + rs.length := by omega
        rw [heq]; exact hfy
      · have hne : natTag (k + 1) ≠ natTag k := fun h => by
          have := natTag_injective h; omega
        have hf0 : f' (natTag k) = x := by simp [f']
        have hf1 : f' (natTag (k + 1)) = z := by simp [f', hne, hfz]
        cases r <;> simpa [axiomHolds, objectHolds, Interpretation.withAnonymous, hf0, hf1] using hxz
      · intro ax hax
        have hholds := (chainAssertions_holds_iff i d (k + 1) rs f).mp hrest
        apply (chainAssertions_holds_iff i d (k + 1) rs f').mpr
        · intro idx hidx
          have hne1 : natTag (k + 1 + idx) ≠ natTag k := fun h => by
            have := natTag_injective h; omega
          have hne2 : natTag (k + 1 + idx + 1) ≠ natTag k := fun h => by
            have := natTag_injective h; omega
          simpa [f', hne1, hne2] using hholds idx hidx
        · exact hax
    · rintro ⟨f, hfx, hfy, h0, hrest⟩
      have heq : k + 1 + rs.length = k + (rs.length + 1) := by omega
      refine ⟨f (natTag (k + 1)), ?_, (ih (k + 1) (f (natTag (k + 1)))).mpr ⟨f, rfl, heq ▸ hfy, hrest⟩⟩
      subst hfx
      cases r <;> exact h0

/-! ### 3. Full-Language Exact Query Negation Branches -/

/-- Construct a finite list of OWL 2 DL counterexample branches for `qAx` against `o`:
    `o ⊭ qAx` iff at least one `branch ∈ branches` makes `branch ++ o` satisfiable. -/
def negateQueryBranches (o : Ontology) (qAx : Axiom) : Option (List Ontology) :=
  let d := freshAnonDoc o
  let u0 := Individual.anonymous d (natTag 0)
  let u1 := Individual.anonymous d (natTag 1)
  let u2 := Individual.anonymous d (natTag 2)
  match qAx with
  -- Class axioms (any arity, anonymous-free expressions)
  | .subClassOf a b =>
    if hasNoAnonIndsClassExpr a && hasNoAnonIndsClassExpr b then
      some [[existsWitnessAxiom (.intersection a (.complement b))]]
    else none
  | .equivalentClasses cs =>
    if cs.all hasNoAnonIndsClassExpr then
      some ((orderedPairs cs).map fun (a, b) =>
        [existsWitnessAxiom (.intersection a (.complement b))])
    else none
  | .disjointClasses cs =>
    if cs.all hasNoAnonIndsClassExpr then
      some ((unorderedPairs cs).map fun (a, b) =>
        [existsWitnessAxiom (.intersection a b)])
    else none
  | .disjointUnion h cs =>
    if cs.all hasNoAnonIndsClassExpr then
      let u := ClassExpr.unite cs
      some ([existsWitnessAxiom (.intersection (.named h) (.complement u))] ::
            [existsWitnessAxiom (.intersection u (.complement (.named h)))] ::
            (unorderedPairs cs).map fun (a, b) => [existsWitnessAxiom (.intersection a b)])
    else none
  -- Object property axioms (all 13 constructors!)
  | .subObjectProperty r s =>
    some [[.objectAssertion r u0 u1, .negativeObjectAssertion s u0 u1]]
  | .subObjectPropertyChain rs s =>
    let uk := Individual.anonymous d (natTag rs.length)
    some [chainAssertions d 0 rs ++ [.negativeObjectAssertion s u0 uk]]
  | .equivalentObjectProperties rs =>
    some ((orderedPairs rs).map fun (r, s) =>
      [.objectAssertion r u0 u1, .negativeObjectAssertion s u0 u1])
  | .disjointObjectProperties rs =>
    some ((unorderedPairs rs).map fun (r, s) =>
      [.objectAssertion r u0 u1, .objectAssertion s u0 u1])
  | .inverseObjectProperties r s =>
    some [[.objectAssertion r u0 u1, .negativeObjectAssertion s u1 u0],
          [.objectAssertion s u1 u0, .negativeObjectAssertion r u0 u1]]
  | .objectPropertyDomain r c =>
    if hasNoAnonIndsClassExpr c then
      some [[existsWitnessAxiom (.intersection (.objectSome r (.named thing)) (.complement c))]]
    else none
  | .objectPropertyRange r c =>
    if hasNoAnonIndsClassExpr c then
      some [[existsWitnessAxiom (.objectSome r (.complement c))]]
    else none
  | .functionalObjectProperty r =>
    some [[existsWitnessAxiom (.objectMin 2 r (.named thing))]]
  | .inverseFunctionalObjectProperty r =>
    some [[existsWitnessAxiom (.objectMin 2 r.converse (.named thing))]]
  | .reflexiveObjectProperty r =>
    some [[existsWitnessAxiom (.complement (.objectSelf r))]]
  | .irreflexiveObjectProperty r =>
    some [[existsWitnessAxiom (.objectSelf r)]]
  | .symmetricObjectProperty r =>
    some [[.objectAssertion r u0 u1, .negativeObjectAssertion r u1 u0]]
  | .asymmetricObjectProperty r =>
    some [[.objectAssertion r u0 u1, .objectAssertion r u1 u0]]
  | .transitiveObjectProperty r =>
    some [[.objectAssertion r u0 u1, .objectAssertion r u1 u2, .negativeObjectAssertion r u0 u2]]
  -- Data property domain, range, functionality
  | .dataPropertyDomain dp c =>
    if hasNoAnonIndsClassExpr c then
      some [[existsWitnessAxiom (.intersection (.dataSome dp (.datatype literalDatatype)) (.complement c))]]
    else none
  | .dataPropertyRange dp dr =>
    some [[existsWitnessAxiom (.dataSome dp (.complement dr))]]
  | .functionalDataProperty dp =>
    some [[existsWitnessAxiom (.dataMin 2 dp (.datatype literalDatatype))]]
  -- Ground & existential anonymous-individual ABox assertions
  | .classAssertion c (.named a) =>
    if hasNoAnonIndsClassExpr c then
      some [[.classAssertion (.complement c) (.named a)]]
    else none
  | .classAssertion c (.anonymous _ _) =>
    if hasNoAnonIndsClassExpr c then
      some [[.subClassOf c (.named nothing)]]
    else none
  | .objectAssertion r (.named a) (.named b) =>
    some [[.negativeObjectAssertion r (.named a) (.named b)]]
  | .objectAssertion r (.anonymous _ _) (.named b) =>
    some [[.classAssertion (.objectAll r.converse (.named nothing)) (.named b)]]
  | .objectAssertion r (.named a) (.anonymous _ _) =>
    some [[.classAssertion (.objectAll r (.named nothing)) (.named a)]]
  | .objectAssertion r (.anonymous d1 l1) (.anonymous d2 l2) =>
    if d1 == d2 && l1 == l2 then
      some [[.subClassOf (.objectSelf r) (.named nothing)]]
    else
      some [[.subClassOf (.objectSome r (.named thing)) (.named nothing)]]
  | .negativeObjectAssertion r (.named a) (.named b) =>
    some [[.objectAssertion r (.named a) (.named b)]]
  | .dataAssertion dp (.named a) l =>
    some [[.negativeDataAssertion dp (.named a) l]]
  | .dataAssertion dp (.anonymous _ _) l =>
    some [[.subClassOf (.dataValue dp l) (.named nothing)]]
  | .negativeDataAssertion dp (.named a) l =>
    some [[.dataAssertion dp (.named a) l]]
  | .sameIndividuals inds =>
    if inds.all isNamedIndividual then
      some ((unorderedPairs inds).map fun (a, b) => [.differentIndividuals [a, b]])
    else none
  | .differentIndividuals inds =>
    if inds.all isNamedIndividual then
      some ((unorderedPairs inds).map fun (a, b) => [.sameIndividuals [a, b]])
    else none
  | _ => none

private theorem classAnonDocs_empty_of_noAnon {c : ClassExpr} (h : hasNoAnonIndsClassExpr c = true) :
    classAnonDocs c = [] := by
  induction c with
  | named _ | objectSelf _ | dataSome _ _ | dataAll _ _ | dataValue _ _
  | dataMin _ _ _ | dataMax _ _ _ | dataExact _ _ _ => rfl
  | complement _ ih => exact ih h
  | intersection a b iha ihb | union a b iha ihb =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    simp [classAnonDocs, iha ha, ihb hb]
  | oneOf inds =>
    simp only [classAnonDocs, List.flatMap_eq_nil_iff]
    intro ind hind
    have := List.all_eq_true.mp h ind hind
    cases ind with
    | named _ => rfl
    | anonymous _ _ => cases this
  | objectSome _ _ ih | objectAll _ _ ih | objectMin _ _ _ ih | objectMax _ _ _ ih | objectExact _ _ _ ih =>
    exact ih h
  | objectValue _ a =>
    cases a with
    | named _ => rfl
    | anonymous _ _ => cases h

private theorem models_singleton_noAnon {dm : DatatypeMap} (i : Interpretation dm) {ax : Axiom}
    (h : axiomAnonDocs ax = []) :
    models i [ax] ↔ axiomHolds i ax := by
  constructor
  · rintro ⟨assign, hsat⟩
    have h1 := hsat ax (List.mem_cons_self ..)
    exact (axiomHolds_withAnonymous_agree (a2 := fun _ _ => i.individuals (.named "")) i
      (fun d hd => by rw [h] at hd; cases hd)).mp h1 |> fun h2 =>
      (axiomHolds_withAnonymous_agree (a1 := fun _ _ => i.individuals (.named "")) (a2 := fun d l => i.individuals (.anonymous d l)) i
        (fun d hd => by rw [h] at hd; cases hd)).mp h2 |> fun h3 => by
      have : i.withAnonymous (fun d l => i.individuals (.anonymous d l)) = i := by
        cases i; simp only [Interpretation.withAnonymous]; congr; funext x; cases x <;> rfl
      simpa [this] using h3
  · intro hax
    obtain ⟨x₀⟩ := i.objectNonempty
    refine ⟨fun _ _ => x₀, fun a ha => ?_⟩
    simp only [List.mem_singleton] at ha; subst ha
    have hself : i.withAnonymous (fun d l => i.individuals (.anonymous d l)) = i := by
      cases i; simp only [Interpretation.withAnonymous]; congr; funext x; cases x <;> rfl
    have hax' : axiomHolds (i.withAnonymous (fun d l => i.individuals (.anonymous d l))) a := by
      simpa [hself] using hax
    exact (axiomHolds_withAnonymous_agree i (fun d hd => by rw [h] at hd; cases hd)).mpr hax'

private theorem models_single_noAnon_append {dm : DatatypeMap} (i : Interpretation dm)
    (o : Ontology) {negAx : Axiom} (h : axiomAnonDocs negAx = []) :
    models i ([negAx] ++ o) ↔ models i o ∧ axiomHolds i negAx := by
  have h1 := models_fresh_branch_iff i o [negAx] (freshAnonDoc o) (freshAnonDoc_not_mem o)
    (fun ax hax d' hd' => by
      simp only [List.mem_singleton] at hax; subst hax; rw [h] at hd'; cases hd')
  rw [h1]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨f, hf⟩
    have hax := hf negAx (List.mem_cons_self ..)
    exact (models_singleton_noAnon i h).mp ⟨fun _ loc => f loc, fun a ha => by
      simp only [List.mem_singleton] at ha; subst ha; exact hax⟩
  · intro hax
    obtain ⟨x₀⟩ := i.objectNonempty
    refine ⟨fun _ => x₀, fun a ha => ?_⟩
    simp only [List.mem_singleton] at ha; subst ha
    have hself : i.withAnonymous (fun d l => i.individuals (.anonymous d l)) = i := by
      cases i; simp only [Interpretation.withAnonymous]; congr; funext x; cases x <;> rfl
    have hax' : axiomHolds (i.withAnonymous (fun d l => i.individuals (.anonymous d l))) a := by
      simpa [hself] using hax
    exact (axiomHolds_withAnonymous_agree i (fun d hd => by rw [h] at hd; cases hd)).mpr hax'

private theorem existsWitnessAxiom_holds {dm : DatatypeMap} (i : Interpretation dm) (e : ClassExpr) :
    axiomHolds i (existsWitnessAxiom e) ↔ ∃ x, classHolds i x e := by
  simp only [existsWitnessAxiom, axiomHolds, classHolds, objectHolds, i.thingExt, i.topObjectExt,
    true_and, true_implies]
  exact ⟨fun h => i.objectNonempty.elim h, fun h _ => h⟩

/-- Helper turning a pointwise model equivalence into `counterexample_branches_sat_iff`. -/
private theorem branches_sat_iff_of_models {dm : DatatypeMap} (o : Ontology) (qAx : Axiom)
    (branches : List Ontology)
    (hmod : ∀ i : Interpretation dm,
      (∃ b ∈ branches, models i (b ++ o)) ↔ models i o ∧ ¬ models i [qAx]) :
    (∃ b ∈ branches, Satisfiable dm (b ++ o)) ↔ ¬ Entails dm o [qAx] := by
  classical
  constructor
  · rintro ⟨b, hb, i, hbi⟩ hent
    obtain ⟨hmo, hnq⟩ := (hmod i).mp ⟨b, hb, hbi⟩
    exact hnq (hent i hmo)
  · intro hnotEnt
    apply Classical.byContradiction
    intro hno
    apply hnotEnt
    intro i hmo
    exact Classical.byContradiction fun hnq => by
      obtain ⟨b, hb, hbi⟩ := (hmod i).mpr ⟨hmo, hnq⟩
      exact hno ⟨b, hb, i, hbi⟩

private theorem u01_fresh_iff {dm : DatatypeMap} (i : Interpretation dm) (o : Ontology)
    (P : i.Object → i.Object → Prop) (branch : Ontology)
    (hdocs : ∀ ax ∈ branch, ∀ d' ∈ axiomAnonDocs ax, d' = freshAnonDoc o)
    (hspec : ∀ f : String → i.Object,
      (∀ ax ∈ branch, axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax) ↔
        P (f (natTag 0)) (f (natTag 1))) :
    models i (branch ++ o) ↔ models i o ∧ ∃ x y, P x y := by
  rw [models_fresh_branch_iff i o branch (freshAnonDoc o) (freshAnonDoc_not_mem o) hdocs]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f (natTag 0), f (natTag 1), (hspec f).mp hf⟩
  · rintro ⟨x, y, hxy⟩
    refine ⟨fun tag => if tag = natTag 0 then x else y, (hspec _).mpr ?_⟩
    have hne : natTag 1 ≠ natTag 0 := fun h => by have := natTag_injective h; omega
    simpa [hne] using hxy

private theorem u012_fresh_iff {dm : DatatypeMap} (i : Interpretation dm) (o : Ontology)
    (P : i.Object → i.Object → i.Object → Prop) (branch : Ontology)
    (hdocs : ∀ ax ∈ branch, ∀ d' ∈ axiomAnonDocs ax, d' = freshAnonDoc o)
    (hspec : ∀ f : String → i.Object,
      (∀ ax ∈ branch, axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax) ↔
        P (f (natTag 0)) (f (natTag 1)) (f (natTag 2))) :
    models i (branch ++ o) ↔ models i o ∧ ∃ x y z, P x y z := by
  rw [models_fresh_branch_iff i o branch (freshAnonDoc o) (freshAnonDoc_not_mem o) hdocs]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f (natTag 0), f (natTag 1), f (natTag 2), (hspec f).mp hf⟩
  · rintro ⟨x, y, z, hxyz⟩
    refine ⟨fun tag => if tag = natTag 0 then x else if tag = natTag 1 then y else z, (hspec _).mpr ?_⟩
    have h10 : natTag 1 ≠ natTag 0 := fun h => by have := natTag_injective h; omega
    have h20 : natTag 2 ≠ natTag 0 := fun h => by have := natTag_injective h; omega
    have h21 : natTag 2 ≠ natTag 1 := fun h => by have := natTag_injective h; omega
    simpa [h10, h20, h21] using hxyz

/-- Kernel-checked exact semantic characterization for all 29 supported OWL 2 DL
    query axiom forms (including property axioms, n-ary axioms, and anonymous-individual
    existential queries): `o` does NOT entail `qAx` iff at least one counterexample
    branch in `negateQueryBranches o qAx` is satisfiable with `o`. -/
theorem counterexample_branches_sat_iff {dm : DatatypeMap} (o : Ontology)
    {qAx : Axiom} {branches : List Ontology}
    (h : negateQueryBranches o qAx = some branches) :
    (∃ b ∈ branches, Satisfiable dm (b ++ o)) ↔ ¬ Entails dm o [qAx] := by
  classical
  apply branches_sat_iff_of_models
  intro i
  cases qAx with
  | subClassOf a b =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hno
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hno
    cases h
    have hqa : axiomAnonDocs (.subClassOf a b) = [] := by
      simp [axiomAnonDocs, classAnonDocs_empty_of_noAnon ha, classAnonDocs_empty_of_noAnon hb]
    have hna : axiomAnonDocs (existsWitnessAxiom (.intersection a (.complement b))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs,
        classAnonDocs_empty_of_noAnon ha, classAnonDocs_empty_of_noAnon hb]
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, hxa, hnb⟩ hall; exact hnb (hall x hxa)
    · intro hnot; apply Classical.byContradiction; intro hnoEx; apply hnot
      intro x hxa; exact Classical.byContradiction fun hnb => hnoEx ⟨x, hxa, hnb⟩
  | equivalentClasses cs =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hall
    cases h
    have hno : ∀ c ∈ cs, classAnonDocs c = [] := fun c hc =>
      classAnonDocs_empty_of_noAnon (List.all_eq_true.mp hall c hc)
    have hqa : axiomAnonDocs (.equivalentClasses cs) = [] := by
      simp [axiomAnonDocs, List.flatMap_eq_nil_iff]; exact hno
    rw [models_singleton_noAnon i hqa]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hb
      obtain ⟨ha, hb'⟩ := mem_orderedPairs_iff.mp hab
      have hna : axiomAnonDocs (existsWitnessAxiom (.intersection a (.complement b))) = [] := by
        simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno a ha, hno b hb']
      obtain ⟨hmo, hex⟩ := (models_single_noAnon_append i o hna).mp hmod
      rw [existsWitnessAxiom_holds] at hex
      refine ⟨hmo, fun heq => ?_⟩
      obtain ⟨x, hxa, hnb⟩ := hex
      exact hnb ((heq a ha b hb' x).mp hxa)
    · rintro ⟨hmo, hneq⟩
      apply Classical.byContradiction; intro hnoB
      apply hneq; intro a ha b hb' x
      have hdir (u v : ClassExpr) (hu : u ∈ cs) (hv : v ∈ cs) : classHolds i x u → classHolds i x v := by
        intro hxu
        apply Classical.byContradiction; intro hnv
        have hna : axiomAnonDocs (existsWitnessAxiom (.intersection u (.complement v))) = [] := by
          simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno u hu, hno v hv]
        exact hnoB ⟨[existsWitnessAxiom (.intersection u (.complement v))],
          List.mem_map.mpr ⟨(u, v), mem_orderedPairs_iff.mpr ⟨hu, hv⟩, rfl⟩,
          (models_single_noAnon_append i o hna).mpr ⟨hmo, (existsWitnessAxiom_holds i _).mpr ⟨x, hxu, hnv⟩⟩⟩
      exact ⟨hdir a b ha hb', hdir b a hb' ha⟩
  | disjointClasses cs =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hall
    cases h
    have hno : ∀ c ∈ cs, classAnonDocs c = [] := fun c hc =>
      classAnonDocs_empty_of_noAnon (List.all_eq_true.mp hall c hc)
    have hqa : axiomAnonDocs (.disjointClasses cs) = [] := by
      simp [axiomAnonDocs, List.flatMap_eq_nil_iff]; exact hno
    rw [models_singleton_noAnon i hqa, axiomHolds, pairwise_iff_unorderedPairs]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hb
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (existsWitnessAxiom (.intersection a b)) = [] := by
        simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno a ha, hno b hb']
      obtain ⟨hmo, hex⟩ := (models_single_noAnon_append i o hna).mp hmod
      rw [existsWitnessAxiom_holds] at hex
      refine ⟨hmo, fun hdisj => ?_⟩
      obtain ⟨x, hxa, hxb⟩ := hex
      exact hdisj (a, b) hab x ⟨hxa, hxb⟩
    · rintro ⟨hmo, hndisj⟩
      apply Classical.byContradiction; intro hnoB
      apply hndisj; intro ⟨a, b⟩ hab x ⟨hxa, hxb⟩
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (existsWitnessAxiom (.intersection a b)) = [] := by
        simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno a ha, hno b hb']
      exact hnoB ⟨[existsWitnessAxiom (.intersection a b)],
        List.mem_map.mpr ⟨(a, b), hab, rfl⟩,
        (models_single_noAnon_append i o hna).mpr ⟨hmo, (existsWitnessAxiom_holds i _).mpr ⟨x, hxa, hxb⟩⟩⟩
  | disjointUnion head cs =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hall
    cases h
    have hno : ∀ c ∈ cs, classAnonDocs c = [] := fun c hc =>
      classAnonDocs_empty_of_noAnon (List.all_eq_true.mp hall c hc)
    have hnoU : classAnonDocs (ClassExpr.unite cs) = [] := by
      clear hno
      induction cs with
      | nil => rfl
      | cons c rest ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        change classAnonDocs c ++ classAnonDocs (ClassExpr.unite rest) = []
        rw [classAnonDocs_empty_of_noAnon hall.1, ih hall.2]
        rfl
    have hqa : axiomAnonDocs (.disjointUnion head cs) = [] := by
      simp [axiomAnonDocs, List.flatMap_eq_nil_iff]; exact hno
    rw [models_singleton_noAnon i hqa, axiomHolds, pairwise_iff_unorderedPairs]
    have hna1 : axiomAnonDocs (existsWitnessAxiom (.intersection (.named head) (.complement (ClassExpr.unite cs)))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hnoU]
    have hna2 : axiomAnonDocs (existsWitnessAxiom (.intersection (ClassExpr.unite cs) (.complement (.named head)))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hnoU]
    constructor
    · rintro ⟨b, hb, hmod⟩
      simp only [List.mem_cons, List.mem_map] at hb
      rcases hb with rfl | rfl | ⟨⟨a, c⟩, hac, rfl⟩
      · obtain ⟨hmo, hex⟩ := (models_single_noAnon_append i o hna1).mp hmod
        rw [existsWitnessAxiom_holds] at hex
        obtain ⟨x, hxh, hnu⟩ := hex
        exact ⟨hmo, fun ⟨hcov, _⟩ => hnu ((classHolds_unite i x cs).mpr ((hcov x).mp hxh))⟩
      · obtain ⟨hmo, hex⟩ := (models_single_noAnon_append i o hna2).mp hmod
        rw [existsWitnessAxiom_holds] at hex
        obtain ⟨x, hxu, hnh⟩ := hex
        exact ⟨hmo, fun ⟨hcov, _⟩ => hnh ((hcov x).mpr ((classHolds_unite i x cs).mp hxu))⟩
      · obtain ⟨ha, hc'⟩ := mem_unorderedPairs_iff hac
        have hna3 : axiomAnonDocs (existsWitnessAxiom (.intersection a c)) = [] := by
          simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno a ha, hno c hc']
        obtain ⟨hmo, hex⟩ := (models_single_noAnon_append i o hna3).mp hmod
        rw [existsWitnessAxiom_holds] at hex
        obtain ⟨x, hxa, hxc⟩ := hex
        exact ⟨hmo, fun ⟨_, hdisj⟩ => hdisj (a, c) hac x ⟨hxa, hxc⟩⟩
    · rintro ⟨hmo, hndu⟩
      apply Classical.byContradiction; intro hnoB
      apply hndu
      refine ⟨fun x => ⟨fun hxh => Classical.byContradiction fun hnu => ?_,
        fun hxu => Classical.byContradiction fun hnh => ?_⟩, fun ⟨a, c⟩ hac x ⟨hxa, hxc⟩ => ?_⟩
      · exact hnoB ⟨_, List.mem_cons_self .., (models_single_noAnon_append i o hna1).mpr
          ⟨hmo, (existsWitnessAxiom_holds i _).mpr ⟨x, hxh, fun hu => hnu ((classHolds_unite i x cs).mp hu)⟩⟩⟩
      · exact hnoB ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (models_single_noAnon_append i o hna2).mpr
          ⟨hmo, (existsWitnessAxiom_holds i _).mpr ⟨x, (classHolds_unite i x cs).mpr hxu, hnh⟩⟩⟩
      · obtain ⟨ha, hc'⟩ := mem_unorderedPairs_iff hac
        have hna3 : axiomAnonDocs (existsWitnessAxiom (.intersection a c)) = [] := by
          simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, hno a ha, hno c hc']
        exact hnoB ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, c), hac, rfl⟩)),
          (models_single_noAnon_append i o hna3).mpr ⟨hmo, (existsWitnessAxiom_holds i _).mpr ⟨x, hxa, hxc⟩⟩⟩
  | subObjectProperty r s =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.subObjectProperty r s) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_singleton, exists_eq_left]
    rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ ¬ objectHolds i s x y)]
    · refine and_congr Iff.rfl ?_
      simp only [axiomHolds]
      constructor
      · rintro ⟨x, y, hr, hns⟩ hall; exact hns (hall x y hr)
      · intro hnot; apply Classical.byContradiction; intro hnoEx; apply hnot
        intro x y hr; exact Classical.byContradiction fun hns => hnoEx ⟨x, y, hr, hns⟩
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> cases s <;> exact Iff.rfl
  | subObjectPropertyChain rs s =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.subObjectPropertyChain rs s) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_singleton, exists_eq_left]
    have hdocs : ∀ ax ∈ chainAssertions (freshAnonDoc o) 0 rs ++
        [.negativeObjectAssertion s (.anonymous (freshAnonDoc o) (natTag 0)) (.anonymous (freshAnonDoc o) (natTag rs.length))],
        ∀ d' ∈ axiomAnonDocs ax, d' = freshAnonDoc o := by
      intro ax hax d' hd'
      rcases List.mem_append.mp hax with h1 | h2
      · exact chainAssertions_docs _ 0 rs ax h1 d' hd'
      · simp only [List.mem_singleton] at h2; subst h2
        simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'
        exact hd'.elim id id
    rw [models_fresh_branch_iff i o _ (freshAnonDoc o) (freshAnonDoc_not_mem o) hdocs]
    refine and_congr Iff.rfl ?_
    simp only [axiomHolds]
    constructor
    · rintro ⟨f, hf⟩ hall
      have hch : ∀ ax ∈ chainAssertions (freshAnonDoc o) 0 rs,
          axiomHolds (i.withAnonymous (fun _ loc => f loc)) ax :=
        fun ax hax => hf ax (List.mem_append_left _ hax)
      have hneg := hf _ (List.mem_append_right _ (List.mem_cons_self ..))
      have hpath : rolePath i rs (f (natTag 0)) (f (natTag rs.length)) :=
        (exists_chain_witness i (freshAnonDoc o) 0 rs (f (natTag 0)) (f (natTag rs.length))).mpr
          ⟨f, rfl, by simp, hch⟩
      have hs := hall _ _ hpath
      cases s <;> exact hneg hs
    · intro hnot
      apply Classical.byContradiction; intro hnoF; apply hnot
      intro x y hpath
      apply Classical.byContradiction; intro hns
      obtain ⟨f, hfx, hfy, hch⟩ := (exists_chain_witness i (freshAnonDoc o) 0 rs x y).mp hpath
      refine hnoF ⟨f, fun ax hax => ?_⟩
      rcases List.mem_append.mp hax with hc | hn
      · exact hch ax hc
      · simp only [List.mem_singleton] at hn; subst hn
        simp only [Nat.zero_add] at hfy
        cases s <;> simpa [axiomHolds, objectHolds, Interpretation.withAnonymous, hfx, hfy] using hns
  | equivalentObjectProperties rs =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.equivalentObjectProperties rs) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨r, s⟩, hrs, rfl⟩ := hb
      obtain ⟨hr, hs⟩ := mem_orderedPairs_iff.mp hrs
      rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ ¬ objectHolds i s x y)] at hmod
      · obtain ⟨hmo, x, y, hrx, hns⟩ := hmod
        exact ⟨hmo, fun heq => hns ((heq r hr s hs x y).mp hrx)⟩
      · intro ax hax d' hd'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
        rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
      · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        cases r <;> cases s <;> exact Iff.rfl
    · rintro ⟨hmo, hneq⟩
      apply Classical.byContradiction; intro hnoB
      apply hneq; intro r hr s hs x y
      have hdir (u v : ObjectProperty) (hu : u ∈ rs) (hv : v ∈ rs) : objectHolds i u x y → objectHolds i v x y := by
        intro hux
        apply Classical.byContradiction; intro hnv
        refine hnoB ⟨[.objectAssertion u (.anonymous (freshAnonDoc o) (natTag 0)) (.anonymous (freshAnonDoc o) (natTag 1)),
          .negativeObjectAssertion v (.anonymous (freshAnonDoc o) (natTag 0)) (.anonymous (freshAnonDoc o) (natTag 1))],
          List.mem_map.mpr ⟨(u, v), mem_orderedPairs_iff.mpr ⟨hu, hv⟩, rfl⟩, ?_⟩
        rw [u01_fresh_iff i o (fun x y => objectHolds i u x y ∧ ¬ objectHolds i v x y)]
        · exact ⟨hmo, x, y, hux, hnv⟩
        · intro ax hax d' hd'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
          rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
        · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          cases u <;> cases v <;> exact Iff.rfl
      exact ⟨hdir r s hr hs, hdir s r hs hr⟩
  | disjointObjectProperties rs =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.disjointObjectProperties rs) = [] := rfl
    rw [models_singleton_noAnon i hqa, axiomHolds, pairwise_iff_unorderedPairs]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨r, s⟩, hrs, rfl⟩ := hb
      rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ objectHolds i s x y)] at hmod
      · obtain ⟨hmo, x, y, hrx, hsx⟩ := hmod
        exact ⟨hmo, fun hdisj => hdisj (r, s) hrs x y ⟨hrx, hsx⟩⟩
      · intro ax hax d' hd'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
        rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
      · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        cases r <;> cases s <;> exact Iff.rfl
    · rintro ⟨hmo, hndisj⟩
      apply Classical.byContradiction; intro hnoB
      apply hndisj; intro ⟨r, s⟩ hrs x y ⟨hrx, hsx⟩
      refine hnoB ⟨[.objectAssertion r (.anonymous (freshAnonDoc o) (natTag 0)) (.anonymous (freshAnonDoc o) (natTag 1)),
        .objectAssertion s (.anonymous (freshAnonDoc o) (natTag 0)) (.anonymous (freshAnonDoc o) (natTag 1))],
        List.mem_map.mpr ⟨(r, s), hrs, rfl⟩, ?_⟩
      rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ objectHolds i s x y)]
      · exact ⟨hmo, x, y, hrx, hsx⟩
      · intro ax hax d' hd'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
        rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
      · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        cases r <;> cases s <;> exact Iff.rfl
  | inverseObjectProperties r s =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.inverseObjectProperties r s) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ ¬ objectHolds i s y x),
        u01_fresh_iff i o (fun x y => objectHolds i s y x ∧ ¬ objectHolds i r x y)]
    · simp only [axiomHolds]
      constructor
      · rintro (⟨hmo, x, y, hr, hns⟩ | ⟨hmo, x, y, hs, hnr⟩)
        · exact ⟨hmo, fun hinv => hns ((hinv x y).mp hr)⟩
        · exact ⟨hmo, fun hinv => hnr ((hinv x y).mpr hs)⟩
      · rintro ⟨hmo, hninv⟩
        apply Classical.byContradiction; intro hno
        apply hninv; intro x y
        exact ⟨fun hr => Classical.byContradiction fun hns => hno (Or.inl ⟨hmo, x, y, hr, hns⟩),
               fun hs => Classical.byContradiction fun hnr => hno (Or.inr ⟨hmo, x, y, hs, hnr⟩)⟩
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> cases s <;> exact Iff.rfl
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> cases s <;> exact Iff.rfl
  | objectPropertyDomain r c =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hc; cases h
    have hqa : axiomAnonDocs (.objectPropertyDomain r c) = [] := classAnonDocs_empty_of_noAnon hc
    have hna : axiomAnonDocs (existsWitnessAxiom (.intersection (.objectSome r (.named thing)) (.complement c))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, classAnonDocs_empty_of_noAnon hc]
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, i.thingExt, and_true]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, ⟨y, hxy⟩, hnc⟩ hall; exact hnc (hall x y hxy)
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y hxy; exact Classical.byContradiction fun hnc => hno ⟨x, ⟨y, hxy⟩, hnc⟩
  | objectPropertyRange r c =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hc; cases h
    have hqa : axiomAnonDocs (.objectPropertyRange r c) = [] := classAnonDocs_empty_of_noAnon hc
    have hna : axiomAnonDocs (existsWitnessAxiom (.objectSome r (.complement c))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, classAnonDocs_empty_of_noAnon hc]
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, y, hxy, hnc⟩ hall; exact hnc (hall x y hxy)
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y hxy; exact Classical.byContradiction fun hnc => hno ⟨x, y, hxy, hnc⟩
  | functionalObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.functionalObjectProperty r) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.objectMin 2 r (.named thing))) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, i.thingExt, and_true]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, h2⟩ hfunc
      exact ((atMostOne_iff (fun y => objectHolds i r x y)).mpr (hfunc x)) h2
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y z hxy hxz
      exact (atMostOne_iff (fun w => objectHolds i r x w)).mp (fun h2 => hno ⟨x, h2⟩) y z hxy hxz
  | inverseFunctionalObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.inverseFunctionalObjectProperty r) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.objectMin 2 r.converse (.named thing))) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, i.thingExt, and_true,
      objectHolds_converse]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, h2⟩ hfunc
      exact ((atMostOne_iff (fun y => objectHolds i r y x)).mpr (hfunc x)) h2
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y z hyx hzx
      exact (atMostOne_iff (fun w => objectHolds i r w x)).mp (fun h2 => hno ⟨x, h2⟩) y z hyx hzx
  | reflexiveObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.reflexiveObjectProperty r) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.complement (.objectSelf r))) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds]
    refine and_congr Iff.rfl ?_
    exact ⟨fun ⟨x, hnr⟩ hall => hnr (hall x),
      fun hnot => Classical.byContradiction fun hno => hnot fun x => Classical.byContradiction fun hnr => hno ⟨x, hnr⟩⟩
  | irreflexiveObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.irreflexiveObjectProperty r) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.objectSelf r)) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds]
    refine and_congr Iff.rfl ?_
    exact ⟨fun ⟨x, hr⟩ hall => hall x hr,
      fun hnot => Classical.byContradiction fun hno => hnot fun x hr => hno ⟨x, hr⟩⟩
  | symmetricObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.symmetricObjectProperty r) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_singleton, exists_eq_left]
    rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ ¬ objectHolds i r y x)]
    · refine and_congr Iff.rfl ?_
      simp only [axiomHolds]
      exact ⟨fun ⟨x, y, h1, h2⟩ hall => h2 (hall x y h1),
        fun hnot => Classical.byContradiction fun hno => hnot fun x y h1 =>
          Classical.byContradiction fun h2 => hno ⟨x, y, h1, h2⟩⟩
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> exact Iff.rfl
  | asymmetricObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.asymmetricObjectProperty r) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_singleton, exists_eq_left]
    rw [u01_fresh_iff i o (fun x y => objectHolds i r x y ∧ objectHolds i r y x)]
    · refine and_congr Iff.rfl ?_
      simp only [axiomHolds]
      exact ⟨fun ⟨x, y, h1, h2⟩ hall => hall x y h1 h2,
        fun hnot => Classical.byContradiction fun hno => hnot fun x y h1 h2 => hno ⟨x, y, h1, h2⟩⟩
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> exact Iff.rfl
  | transitiveObjectProperty r =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.transitiveObjectProperty r) = [] := rfl
    rw [models_singleton_noAnon i hqa]
    simp only [List.mem_singleton, exists_eq_left]
    rw [u012_fresh_iff i o (fun x y z => objectHolds i r x y ∧ objectHolds i r y z ∧ ¬ objectHolds i r x z)]
    · refine and_congr Iff.rfl ?_
      simp only [axiomHolds]
      exact ⟨fun ⟨x, y, z, h1, h2, h3⟩ hall => h3 (hall x y z h1 h2),
        fun hnot => Classical.byContradiction fun hno => hnot fun x y z h1 h2 =>
          Classical.byContradiction fun h3 => hno ⟨x, y, z, h1, h2, h3⟩⟩
    · intro ax hax d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl | rfl <;> (simp only [axiomAnonDocs, indAnonDocs, List.mem_append, List.mem_singleton] at hd'; exact hd'.elim id id)
    · intro f; simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      cases r <;> exact Iff.rfl
  | dataPropertyDomain dp c =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hc; cases h
    have hqa : axiomAnonDocs (.dataPropertyDomain dp c) = [] := classAnonDocs_empty_of_noAnon hc
    have hna : axiomAnonDocs (existsWitnessAxiom (.intersection (.dataSome dp (.datatype literalDatatype)) (.complement c))) = [] := by
      simp [existsWitnessAxiom, axiomAnonDocs, classAnonDocs, classAnonDocs_empty_of_noAnon hc]
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, dataHolds, i.literalDatatypeExt, and_true]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, ⟨y, hxy⟩, hnc⟩ hall; exact hnc (hall x y hxy)
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y hxy; exact Classical.byContradiction fun hnc => hno ⟨x, ⟨y, hxy⟩, hnc⟩
  | dataPropertyRange dp dr =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.dataPropertyRange dp dr) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.dataSome dp (.complement dr))) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, dataHolds]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, y, hxy, hnd⟩ hall; exact hnd (hall x y hxy)
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y hxy; exact Classical.byContradiction fun hnd => hno ⟨x, y, hxy, hnd⟩
  | functionalDataProperty dp =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.functionalDataProperty dp) = [] := rfl
    have hna : axiomAnonDocs (existsWitnessAxiom (.dataMin 2 dp (.datatype literalDatatype))) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa]
    rw [existsWitnessAxiom_holds]
    simp only [axiomHolds, classHolds, dataHolds, i.literalDatatypeExt, and_true]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, h2⟩ hfunc
      exact ((atMostOne_iff (fun y => i.dataProperties dp x y)).mpr (hfunc x)) h2
    · intro hnot; apply Classical.byContradiction; intro hno; apply hnot
      intro x y z hxy hxz
      exact (atMostOne_iff (fun w => i.dataProperties dp x w)).mp (fun h2 => hno ⟨x, h2⟩) y z hxy hxz
  | classAssertion c ind =>
    cases ind with
    | named a =>
      simp only [negateQueryBranches] at h
      split at h; rotate_left; · cases h
      rename_i hc; cases h
      have hqa : axiomAnonDocs (.classAssertion c (.named a)) = [] := by
        simp [axiomAnonDocs, indAnonDocs, classAnonDocs_empty_of_noAnon hc]
      have hna : axiomAnonDocs (.classAssertion (.complement c) (.named a)) = [] := by
        simp [axiomAnonDocs, indAnonDocs, classAnonDocs, classAnonDocs_empty_of_noAnon hc]
      simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
        models_singleton_noAnon i hqa, axiomHolds, classHolds]
    | anonymous doc loc =>
      simp only [negateQueryBranches] at h
      split at h; rotate_left; · cases h
      rename_i hc; cases h
      have hna : axiomAnonDocs (.subClassOf c (.named nothing)) = [] := by
        simp [axiomAnonDocs, classAnonDocs, classAnonDocs_empty_of_noAnon hc]
      have hmodQ : models i [.classAssertion c (.anonymous doc loc)] ↔ ∃ x, classHolds i x c := by
        constructor
        · rintro ⟨assign, hsat⟩
          have h1 : classHolds (i.withAnonymous assign) (assign doc loc) c := hsat _ (List.mem_cons_self ..)
          exact ⟨assign doc loc, (classHolds_withAnonymous_of_noAnon i assign (assign doc loc) hc).mp h1⟩
        · rintro ⟨x, hx⟩
          refine ⟨fun _ _ => x, fun a ha => ?_⟩
          simp only [List.mem_singleton] at ha; subst ha
          exact (classHolds_withAnonymous_of_noAnon i (fun _ _ => x) x hc).mpr hx
      simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
        axiomHolds, classHolds, i.nothingExt]
      refine and_congr Iff.rfl ?_
      exact ⟨fun hall ⟨x, hx⟩ => hall x hx, fun hnex x hx => hnex ⟨x, hx⟩⟩
  | objectAssertion r ind1 ind2 =>
    cases ind1 with
    | named a =>
      cases ind2 with
      | named b =>
        simp only [negateQueryBranches] at h; cases h
        have hqa : axiomAnonDocs (.objectAssertion r (.named a) (.named b)) = [] := rfl
        have hna : axiomAnonDocs (.negativeObjectAssertion r (.named a) (.named b)) = [] := rfl
        simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
          models_singleton_noAnon i hqa, axiomHolds]
      | anonymous doc loc =>
        simp only [negateQueryBranches] at h; cases h
        have hna : axiomAnonDocs (.classAssertion (.objectAll r (.named nothing)) (.named a)) = [] := rfl
        have hmodQ : models i [.objectAssertion r (.named a) (.anonymous doc loc)] ↔
            ∃ y, objectHolds i r (i.individuals (.named a)) y := by
          constructor
          · rintro ⟨assign, hsat⟩
            have h1 := hsat _ (List.mem_cons_self ..)
            refine ⟨assign doc loc, ?_⟩
            cases r <;> exact h1
          · rintro ⟨y, hy⟩
            refine ⟨fun _ _ => y, fun ax hax => ?_⟩
            simp only [List.mem_singleton] at hax; subst hax
            cases r <;> exact hy
        simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
          axiomHolds, classHolds, i.nothingExt]
        refine and_congr Iff.rfl ?_
        exact ⟨fun hall ⟨y, hy⟩ => hall y hy, fun hnex y hy => hnex ⟨y, hy⟩⟩
    | anonymous d1 l1 =>
      cases ind2 with
      | named b =>
        simp only [negateQueryBranches] at h; cases h
        have hna : axiomAnonDocs (.classAssertion (.objectAll r.converse (.named nothing)) (.named b)) = [] := rfl
        have hmodQ : models i [.objectAssertion r (.anonymous d1 l1) (.named b)] ↔
            ∃ x, objectHolds i r x (i.individuals (.named b)) := by
          constructor
          · rintro ⟨assign, hsat⟩
            have h1 := hsat _ (List.mem_cons_self ..)
            refine ⟨assign d1 l1, ?_⟩
            cases r <;> exact h1
          · rintro ⟨x, hx⟩
            refine ⟨fun _ _ => x, fun ax hax => ?_⟩
            simp only [List.mem_singleton] at hax; subst hax
            cases r <;> exact hx
        simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
          axiomHolds, classHolds, i.nothingExt, objectHolds_converse]
        refine and_congr Iff.rfl ?_
        exact ⟨fun hall ⟨x, hx⟩ => hall x hx, fun hnex x hx => hnex ⟨x, hx⟩⟩
      | anonymous d2 l2 =>
        simp only [negateQueryBranches] at h
        split at h
        · rename_i hsame
          obtain ⟨hd, hl⟩ := Bool.and_eq_true_iff.mp hsame
          have hd' : d1 = d2 := beq_iff_eq.mp hd
          have hl' : l1 = l2 := beq_iff_eq.mp hl
          subst hd'; subst hl'; cases h
          have hna : axiomAnonDocs (.subClassOf (.objectSelf r) (.named nothing)) = [] := rfl
          have hmodQ : models i [.objectAssertion r (.anonymous d1 l1) (.anonymous d1 l1)] ↔
              ∃ x, objectHolds i r x x := by
            constructor
            · rintro ⟨assign, hsat⟩
              have h1 := hsat _ (List.mem_cons_self ..)
              refine ⟨assign d1 l1, ?_⟩
              cases r <;> exact h1
            · rintro ⟨x, hx⟩
              refine ⟨fun _ _ => x, fun ax hax => ?_⟩
              simp only [List.mem_singleton] at hax; subst hax
              cases r <;> exact hx
          simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
            axiomHolds, classHolds, i.nothingExt]
          refine and_congr Iff.rfl ?_
          exact ⟨fun hall ⟨x, hx⟩ => hall x hx, fun hnex x hx => hnex ⟨x, hx⟩⟩
        · rename_i hdiff
          cases h
          have hna : axiomAnonDocs (.subClassOf (.objectSome r (.named thing)) (.named nothing)) = [] := rfl
          have hmodQ : models i [.objectAssertion r (.anonymous d1 l1) (.anonymous d2 l2)] ↔
              ∃ x y, objectHolds i r x y := by
            constructor
            · rintro ⟨assign, hsat⟩
              have h1 := hsat _ (List.mem_cons_self ..)
              refine ⟨assign d1 l1, assign d2 l2, ?_⟩
              cases r <;> exact h1
            · rintro ⟨x, y, hxy⟩
              refine ⟨fun d l => if d = d1 ∧ l = l1 then x else y, fun ax hax => ?_⟩
              simp only [List.mem_singleton] at hax; subst hax
              have hne : ¬ (d2 = d1 ∧ l2 = l1) := fun ⟨hd, hl⟩ => hdiff (by simp [hd, hl])
              cases r <;> simpa [axiomHolds, objectHolds, Interpretation.withAnonymous, hne] using hxy
          simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
            axiomHolds, classHolds, i.thingExt, i.nothingExt, and_true]
          refine and_congr Iff.rfl ?_
          exact ⟨fun hall ⟨x, y, hxy⟩ => hall x ⟨y, hxy⟩, fun hnex x ⟨y, hxy⟩ => hnex ⟨x, y, hxy⟩⟩
  | negativeObjectAssertion r ind1 ind2 =>
    cases ind1 with | anonymous _ _ => simp [negateQueryBranches] at h | named a =>
    cases ind2 with | anonymous _ _ => simp [negateQueryBranches] at h | named b =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.negativeObjectAssertion r (.named a) (.named b)) = [] := rfl
    have hna : axiomAnonDocs (.objectAssertion r (.named a) (.named b)) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa, axiomHolds, Classical.not_not]
  | dataAssertion dp ind l =>
    cases ind with
    | named a =>
      simp only [negateQueryBranches] at h; cases h
      have hqa : axiomAnonDocs (.dataAssertion dp (.named a) l) = [] := rfl
      have hna : axiomAnonDocs (.negativeDataAssertion dp (.named a) l) = [] := rfl
      simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
        models_singleton_noAnon i hqa, axiomHolds]
    | anonymous doc loc =>
      simp only [negateQueryBranches] at h; cases h
      have hna : axiomAnonDocs (.subClassOf (.dataValue dp l) (.named nothing)) = [] := rfl
      have hmodQ : models i [.dataAssertion dp (.anonymous doc loc) l] ↔
          ∃ x, i.dataProperties dp x (i.literalValue l) := by
        constructor
        · rintro ⟨assign, hsat⟩
          exact ⟨assign doc loc, hsat _ (List.mem_cons_self ..)⟩
        · rintro ⟨x, hx⟩
          refine ⟨fun _ _ => x, fun ax hax => ?_⟩
          simp only [List.mem_singleton] at hax; subst hax; exact hx
      simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna, hmodQ,
        axiomHolds, classHolds, i.nothingExt]
      refine and_congr Iff.rfl ?_
      exact ⟨fun hall ⟨x, hx⟩ => hall x hx, fun hnex x hx => hnex ⟨x, hx⟩⟩
  | negativeDataAssertion dp ind l =>
    cases ind with | anonymous _ _ => simp [negateQueryBranches] at h | named a =>
    simp only [negateQueryBranches] at h; cases h
    have hqa : axiomAnonDocs (.negativeDataAssertion dp (.named a) l) = [] := rfl
    have hna : axiomAnonDocs (.dataAssertion dp (.named a) l) = [] := rfl
    simp only [List.mem_singleton, exists_eq_left, models_single_noAnon_append i o hna,
      models_singleton_noAnon i hqa, axiomHolds, Classical.not_not]
  | sameIndividuals inds =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hall; cases h
    have hno : ∀ a ∈ inds, indAnonDocs a = [] := fun a ha => by
      have := List.all_eq_true.mp hall a ha
      cases a with | named _ => rfl | anonymous _ _ => cases this
    have hqa : axiomAnonDocs (.sameIndividuals inds) = [] := by
      simp [axiomAnonDocs, List.flatMap_eq_nil_iff]; exact hno
    rw [models_singleton_noAnon i hqa, axiomHolds]
    have hpairEq : (∀ a ∈ inds, ∀ b ∈ inds, i.individuals a = i.individuals b) ↔
        ∀ p ∈ unorderedPairs inds, i.individuals p.1 = i.individuals p.2 := by
      rw [← pairwise_iff_unorderedPairs (fun a b => i.individuals a = i.individuals b)]
      clear hall hno hqa
      constructor
      · intro heq
        induction inds with
        | nil => exact .nil
        | cons x xs ih =>
          exact List.pairwise_cons.mpr ⟨fun y hy => heq x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy),
            ih (fun a ha b hb => heq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
      · intro hpw
        induction inds with
        | nil => intro _ ha; cases ha
        | cons x xs ih =>
          obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hpw
          intro a ha b hb
          rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
          · rfl
          · exact hx b hb'
          · exact (hx a ha').symm
          · exact ih hxs a ha' b hb'
    rw [hpairEq]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hb
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (.differentIndividuals [a, b]) = [] := by
        simp [axiomAnonDocs, hno a ha, hno b hb']
      obtain ⟨hmo, hdiff⟩ := (models_single_noAnon_append i o hna).mp hmod
      simp only [axiomHolds, List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil, and_true] at hdiff
      exact ⟨hmo, fun hsame => hdiff.1 (hsame (a, b) hab)⟩
    · rintro ⟨hmo, hnsame⟩
      apply Classical.byContradiction; intro hnoB
      apply hnsame; intro ⟨a, b⟩ hab
      apply Classical.byContradiction; intro hne
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (.differentIndividuals [a, b]) = [] := by
        simp [axiomAnonDocs, hno a ha, hno b hb']
      refine hnoB ⟨[.differentIndividuals [a, b]], List.mem_map.mpr ⟨(a, b), hab, rfl⟩,
        (models_single_noAnon_append i o hna).mpr ⟨hmo, ?_⟩⟩
      simp [axiomHolds, hne]
  | differentIndividuals inds =>
    simp only [negateQueryBranches] at h
    split at h; rotate_left; · cases h
    rename_i hall; cases h
    have hno : ∀ a ∈ inds, indAnonDocs a = [] := fun a ha => by
      have := List.all_eq_true.mp hall a ha
      cases a with | named _ => rfl | anonymous _ _ => cases this
    have hqa : axiomAnonDocs (.differentIndividuals inds) = [] := by
      simp [axiomAnonDocs, List.flatMap_eq_nil_iff]; exact hno
    rw [models_singleton_noAnon i hqa, axiomHolds, pairwise_iff_unorderedPairs]
    constructor
    · rintro ⟨_, hb, hmod⟩
      simp only [List.mem_map] at hb
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hb
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (.sameIndividuals [a, b]) = [] := by
        simp [axiomAnonDocs, hno a ha, hno b hb']
      obtain ⟨hmo, hsame⟩ := (models_single_noAnon_append i o hna).mp hmod
      have heq : i.individuals a = i.individuals b :=
        hsame a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      exact ⟨hmo, fun hdiff => hdiff (a, b) hab heq⟩
    · rintro ⟨hmo, hndiff⟩
      apply Classical.byContradiction; intro hnoB
      apply hndiff; intro ⟨a, b⟩ hab heq
      obtain ⟨ha, hb'⟩ := mem_unorderedPairs_iff hab
      have hna : axiomAnonDocs (.sameIndividuals [a, b]) = [] := by
        simp [axiomAnonDocs, hno a ha, hno b hb']
      refine hnoB ⟨[.sameIndividuals [a, b]], List.mem_map.mpr ⟨(a, b), hab, rfl⟩,
        (models_single_noAnon_append i o hna).mpr ⟨hmo, ?_⟩⟩
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact heq
      · exact heq.symm
      · rfl
  | subDataProperty _ _ | equivalentDataProperties _ | disjointDataProperties _
  | datatypeDefinition _ _ | hasKey _ _ _ =>
    simp [negateQueryBranches] at h

/-! ### 4. Generic Branching Four-Way Query Classifier -/

private def anyBranchSat (solve : Ontology → Option Bool) (o : Ontology) :
    List Ontology → Option Bool
  | [] => some false
  | b :: bs =>
    match solve (b ++ o) with
    | some true => some true
    | some false => anyBranchSat solve o bs
    | none =>
      match anyBranchSat solve o bs with
      | some true => some true
      | _ => none

private theorem anyBranchSat_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    (o : Ontology) (bs : List Ontology) {res : Bool}
    (h : anyBranchSat solve o bs = some res) :
    res = true ↔ ∃ b ∈ bs, Satisfiable dm (b ++ o) := by
  induction bs generalizing res with
  | nil =>
    simp only [anyBranchSat, Option.some.injEq] at h; subst h
    simp
  | cons b bs ih =>
    simp only [anyBranchSat] at h
    cases hb : solve (b ++ o) with
    | some v =>
      rw [hb] at h
      cases v with
      | true =>
        simp only [Option.some.injEq] at h; subst h
        exact ⟨fun _ => ⟨b, List.mem_cons_self .., (hsolve hb).mp rfl⟩, fun _ => rfl⟩
      | false =>
        have hunsat : ¬ Satisfiable dm (b ++ o) := fun hs => Bool.noConfusion ((hsolve hb).mpr hs)
        rw [ih h]
        simp only [List.mem_cons]
        exact ⟨fun ⟨b', hb', hs⟩ => ⟨b', Or.inr hb', hs⟩,
          fun ⟨b', hb', hs⟩ => hb'.elim (fun e => absurd (e ▸ hs) hunsat) (fun h' => ⟨b', h', hs⟩)⟩
    | none =>
      rw [hb] at h
      cases hrest : anyBranchSat solve o bs with
      | none => rw [hrest] at h; cases h
      | some v =>
        rw [hrest] at h
        cases v with
        | false => cases h
        | true =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨b', hb', hs⟩ := (ih hrest).mp rfl
          exact ⟨fun _ => ⟨b', List.mem_cons_of_mem _ hb', hs⟩, fun _ => rfl⟩

/-- Four-way query classifier over all 29 supported OWL 2 DL query axiom forms. -/
def classifyExtendedQueryWith (solve : Ontology → Option Bool) (o : Ontology) (qAx : Axiom) :
    Option InclusionVerdict :=
  (negateQueryBranches o qAx).bind fun branches =>
    (solve o).bind fun base =>
      if !base then some .inconsistent
      else
        match anyBranchSat solve o branches with
        | some false => some .entailed
        | some true =>
          match solve (qAx :: o) with
          | some false => some .refuted
          | some true => some .independent
          | none => none
        | none =>
          match solve (qAx :: o) with
          | some false => some .refuted
          | _ => none

theorem classifyExtendedQueryWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : classifyExtendedQueryWith solve o qAx = some v) :
    queryVerdictClaimWith dm o qAx v := by
  simp only [classifyExtendedQueryWith, Option.bind_eq_some_iff] at h
  obtain ⟨branches, hneg, base, hbase, hrest⟩ := h
  cases base with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest
    subst hrest
    exact fun hsat => Bool.noConfusion ((hsolve hbase).mpr hsat)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrest
    have hBaseSat : Satisfiable dm o := (hsolve hbase).mp rfl
    cases hcnt : anyBranchSat solve o branches with
    | some bc =>
      cases bc with
      | false =>
        simp only [hcnt, Option.some.injEq] at hrest
        subst hrest
        refine ⟨hBaseSat, Classical.byContradiction fun hnotEnt => ?_⟩
        have hex := (counterexample_branches_sat_iff o hneg).mpr hnotEnt
        exact Bool.noConfusion ((anyBranchSat_iff hsolve o branches hcnt).mpr hex)
      | true =>
        simp only [hcnt] at hrest
        have hNotEnt : ¬ Entails dm o [qAx] :=
          (counterexample_branches_sat_iff o hneg).mp ((anyBranchSat_iff hsolve o branches hcnt).mp rfl)
        cases hinc : solve (qAx :: o) with
        | none => simp [hinc] at hrest
        | some bi =>
          cases bi with
          | false =>
            simp only [hinc, Option.some.injEq] at hrest
            subst hrest
            exact ⟨hBaseSat, fun hsat => Bool.noConfusion ((hsolve hinc).mpr hsat)⟩
          | true =>
            simp only [hinc, Option.some.injEq] at hrest
            subst hrest
            exact ⟨hNotEnt, (hsolve hinc).mp rfl⟩
    | none =>
      simp only [hcnt] at hrest
      cases hinc : solve (qAx :: o) with
      | none => simp [hinc] at hrest
      | some bi =>
        cases bi with
        | false =>
          simp only [hinc, Option.some.injEq] at hrest
          subst hrest
          exact ⟨hBaseSat, fun hsat => Bool.noConfusion ((hsolve hinc).mpr hsat)⟩
        | true => simp [hinc] at hrest

/-- Decide any of the 29 supported OWL 2 DL query axiom forms over `realDatatypeMap`. -/
def decideRealExtendedQuery? (o : Ontology) (qAx : Axiom) : Option InclusionVerdict :=
  classifyExtendedQueryWith decideRealOntology? o qAx

theorem decideRealExtendedQuery_sound {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideRealExtendedQuery? o qAx = some v) :
    queryVerdictClaimWith realDatatypeMap o qAx v :=
  classifyExtendedQueryWith_sound decideRealOntology_iff h

/-- Decide any of the 29 supported OWL 2 DL query axiom forms over standard `datatypeMap`. -/
def decideWiderExtendedQuery? (o : Ontology) (qAx : Axiom) : Option InclusionVerdict :=
  classifyExtendedQueryWith decideWithWiderDataRanges? o qAx

theorem decideWiderExtendedQuery_sound {o : Ontology} {qAx : Axiom} {v : InclusionVerdict}
    (h : decideWiderExtendedQuery? o qAx = some v) :
    Normalize.queryVerdictClaim o qAx v :=
  (queryVerdictClaimWith_std_iff o qAx v).mp
    (classifyExtendedQueryWith_sound decideWithWiderDataRanges_iff h)

#print axioms counterexample_branches_sat_iff
#print axioms classifyExtendedQueryWith_sound
#print axioms decideRealExtendedQuery_sound
#print axioms decideWiderExtendedQuery_sound

end Sabrina.OWL2.SROIQD.Termination.ExtendedQuery
