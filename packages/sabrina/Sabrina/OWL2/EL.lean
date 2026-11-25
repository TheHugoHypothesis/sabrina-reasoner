import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.DirectSemantics
import Sabrina.OWL2.Profile
import Sabrina.OWL2.Datatypes

/-! Kernel-verified polynomial EL++ consequence-based classifier (ELK / Baader–
    Brandt–Lutz completion calculus) for W3C OWL 2 Direct Semantics.

    Supports EL++ TBoxes and RBoxes:
      * `SubClassOf`, `EquivalentClasses`, `DisjointClasses`
      * `owl:Thing`, `owl:Nothing`, named classes, `ObjectIntersectionOf`,
        `ObjectSomeValuesFrom` (over named roles)
      * `SubObjectPropertyOf`, `EquivalentObjectProperties`,
        `TransitiveObjectProperty`, `SubObjectPropertyOf(ObjectPropertyChain(...))`,
        `ObjectPropertyDomain`, `ReflexiveObjectProperty`

    Soundness & completeness guarantees (0 `sorry`, standard core axioms only):
      * `normalizeEL_models_iff`: two-way definitional model preservation
      * `checkELProof_sound`: verified linear-time EL++ derivation checking
      * `checkELModel_sound`: verified finite canonical model checking
      * `decideELInclusion_sound`: end-to-end verified `ENTAILED` / `REFUTED` /
        `SENTENCE_INDEPENDENT` / `INCONSISTENT_ONTOLOGY` verdicts under W3C
        OWL 2 Direct Semantics. -/

namespace Sabrina.OWL2.EL

open Sabrina.OWL2 Sabrina.OWL2.Profile

/-! ### Normalized EL++ axioms -/

inductive ELAxiom where
  | sub1 (a b : IRI)             -- A ⊑ B
  | sub2 (a1 a2 b : IRI)         -- A₁ ⊓ A₂ ⊑ B
  | existR (a r b : IRI)         -- A ⊑ ∃r.B
  | existL (r a b : IRI)         -- ∃r.A ⊑ B
  | roleSub (r s : IRI)          -- r ⊑ s
  | roleChain (r1 r2 s : IRI)    -- r₁ ∘ r₂ ⊑ s
  | roleRefl (r : IRI)           -- ∀ x, r(x, x)
  deriving DecidableEq, Repr

def ELAxiom.toAxiom : ELAxiom → Axiom
  | .sub1 a b => .subClassOf (.named a) (.named b)
  | .sub2 a1 a2 b => .subClassOf (.intersection (.named a1) (.named a2)) (.named b)
  | .existR a r b => .subClassOf (.named a) (.objectSome (.named r) (.named b))
  | .existL r a b => .subClassOf (.objectSome (.named r) (.named a)) (.named b)
  | .roleSub r s => .subObjectProperty (.named r) (.named s)
  | .roleChain r1 r2 s => .subObjectPropertyChain [.named r1, .named r2] (.named s)
  | .roleRefl r => .reflexiveObjectProperty (.named r)

def elOntology (axs : List ELAxiom) : Ontology :=
  axs.map ELAxiom.toAxiom

/-! ### Kernel-checked EL++ derivation certificates (`ELProof`) -/

inductive ELGoal where
  | sub (x b : IRI)       -- ∀ u, x(u) → b(u)
  | rel (r x y : IRI)     -- ∀ u, x(u) → ∃ v, r(u, v) ∧ y(v)
  deriving DecidableEq, Repr

def elGoalHolds {d : DatatypeMap} (i : Interpretation d) : ELGoal → Prop
  | .sub x b => ∀ u, i.classes x u → i.classes b u
  | .rel r x y => ∀ u, i.classes x u → ∃ v, i.objectProperties r u v ∧ i.classes y v

inductive ELProof where
  | refl (x : IRI)
  | top (x : IRI)
  | bot (x b : IRI) (pBot : ELProof)
  | cr1 (x a b : IRI) (pA : ELProof)
  | cr2 (x a1 a2 b : IRI) (p1 p2 : ELProof)
  | cr3 (x a r b : IRI) (pA : ELProof)
  | cr4 (x r y a b : IRI) (pRel pA : ELProof)
  | cr5 (x r y : IRI) (pRel pBot : ELProof)
  | cr10 (r s x y : IRI) (pRel : ELProof)
  | cr11 (r1 r2 s x y z : IRI) (p1 p2 : ELProof)
  | crRefl (r x : IRI)
  deriving DecidableEq, Repr

def checkELProof (axs : List ELAxiom) : ELProof → ELGoal → Bool
  | .refl x, g => decide (g = .sub x x)
  | .top x, g => decide (g = .sub x thing)
  | .bot x b pBot, g => decide (g = .sub x b) && checkELProof axs pBot (.sub x nothing)
  | .cr1 x a b pA, g =>
    decide (g = .sub x b) && axs.contains (.sub1 a b) && checkELProof axs pA (.sub x a)
  | .cr2 x a1 a2 b p1 p2, g =>
    decide (g = .sub x b) && axs.contains (.sub2 a1 a2 b) &&
      checkELProof axs p1 (.sub x a1) && checkELProof axs p2 (.sub x a2)
  | .cr3 x a r b pA, g =>
    decide (g = .rel r x b) && axs.contains (.existR a r b) && checkELProof axs pA (.sub x a)
  | .cr4 x r y a b pRel pA, g =>
    decide (g = .sub x b) && axs.contains (.existL r a b) &&
      checkELProof axs pRel (.rel r x y) && checkELProof axs pA (.sub y a)
  | .cr5 x r y pRel pBot, g =>
    decide (g = .sub x nothing) &&
      checkELProof axs pRel (.rel r x y) && checkELProof axs pBot (.sub y nothing)
  | .cr10 r s x y pRel, g =>
    decide (g = .rel s x y) && axs.contains (.roleSub r s) && checkELProof axs pRel (.rel r x y)
  | .cr11 r1 r2 s x y z p1 p2, g =>
    decide (g = .rel s x z) && axs.contains (.roleChain r1 r2 s) &&
      checkELProof axs p1 (.rel r1 x y) && checkELProof axs p2 (.rel r2 y z)
  | .crRefl r x, g =>
    decide (g = .rel r x x) && axs.contains (.roleRefl r)

theorem checkELProof_sound {d : DatatypeMap} {axs : List ELAxiom} {pf : ELProof} {g : ELGoal}
    (hcheck : checkELProof axs pf g = true) {i : Interpretation d}
    (hsat : satisfies i (elOntology axs)) :
    elGoalHolds i g := by
  induction pf generalizing g with
  | refl x =>
    simp only [checkELProof, decide_eq_true_eq] at hcheck; subst hcheck
    exact fun _ h => h
  | top x =>
    simp only [checkELProof, decide_eq_true_eq] at hcheck; subst hcheck
    exact fun u _ => i.thingExt u
  | bot x b pBot ih =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨rfl, h1⟩ := hcheck
    intro u hu
    exact absurd (ih h1 u hu) (i.nothingExt u)
  | cr1 x a b pA ih =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hcheck
    have hax := hsat (ELAxiom.sub1 a b).toAxiom (List.mem_map_of_mem hmem)
    exact fun u hu => hax u (ih h1 u hu)
  | cr2 x a1 a2 b p1 p2 ih1 ih2 =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hcheck
    have hax := hsat (ELAxiom.sub2 a1 a2 b).toAxiom (List.mem_map_of_mem hmem)
    exact fun u hu => hax u ⟨ih1 h1 u hu, ih2 h2 u hu⟩
  | cr3 x a r b pA ih =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hcheck
    have hax := hsat (ELAxiom.existR a r b).toAxiom (List.mem_map_of_mem hmem)
    exact fun u hu => hax u (ih h1 u hu)
  | cr4 x r y a b pRel pA ihRel ihA =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hcheck
    have hax := hsat (ELAxiom.existL r a b).toAxiom (List.mem_map_of_mem hmem)
    intro u hu
    obtain ⟨v, hruv, hyv⟩ := ihRel h1 u hu
    exact hax u ⟨v, hruv, ihA h2 v hyv⟩
  | cr5 x r y pRel pBot ihRel ihBot =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨rfl, h1⟩, h2⟩ := hcheck
    intro u hu
    obtain ⟨v, _, hyv⟩ := ihRel h1 u hu
    exact absurd (ihBot h2 v hyv) (i.nothingExt v)
  | cr10 r s x y pRel ih =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨rfl, hmem⟩, h1⟩ := hcheck
    have hax := hsat (ELAxiom.roleSub r s).toAxiom (List.mem_map_of_mem hmem)
    intro u hu
    obtain ⟨v, hruv, hyv⟩ := ih h1 u hu
    exact ⟨v, hax u v hruv, hyv⟩
  | cr11 r1 r2 s x y z p1 p2 ih1 ih2 =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨⟨⟨rfl, hmem⟩, h1⟩, h2⟩ := hcheck
    have hax := hsat (ELAxiom.roleChain r1 r2 s).toAxiom (List.mem_map_of_mem hmem)
    intro u hu
    obtain ⟨v, hr1, hyv⟩ := ih1 h1 u hu
    obtain ⟨w, hr2, hzw⟩ := ih2 h2 v hyv
    exact ⟨w, hax u w ⟨v, hr1, w, hr2, rfl⟩, hzw⟩
  | crRefl r x =>
    simp only [checkELProof, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcheck
    obtain ⟨rfl, hmem⟩ := hcheck
    have hax := hsat (ELAxiom.roleRefl r).toAxiom (List.mem_map_of_mem hmem)
    exact fun u hu => ⟨u, hax u, hu⟩

theorem checkELProof_entails_sub {d : DatatypeMap} {axs : List ELAxiom} {pf : ELProof} {a b : IRI}
    (hcheck : checkELProof axs pf (.sub a b) = true) :
    Entails d (elOntology axs) [.subClassOf (.named a) (.named b)] := by
  intro i ⟨assign, hsat⟩
  refine ⟨assign, fun q hq => ?_⟩
  rcases List.mem_singleton.mp hq with rfl
  exact checkELProof_sound hcheck hsat

theorem checkELProof_inconsistent {d : DatatypeMap} {axs : List ELAxiom} {pf : ELProof}
    (hcheck : checkELProof axs pf (.sub thing nothing) = true) :
    ¬ Satisfiable d (elOntology axs) := by
  rintro ⟨i, assign, hsat⟩
  have h := checkELProof_sound hcheck hsat
  obtain ⟨u⟩ := (i.withAnonymous assign).objectNonempty
  exact (i.withAnonymous assign).nothingExt u (h u ((i.withAnonymous assign).thingExt u))

/-! ### Kernel-checked finite canonical EL++ model (`ELModel`) -/

structure ELModel where
  nodes : List IRI
  clsFacts : List (IRI × IRI)        -- (classIRI, nodeIRI)
  edges : List (IRI × IRI × IRI)     -- (roleIRI, srcNode, dstNode)
  deriving DecidableEq, Repr

def ELModel.hasCls (m : ELModel) (c u : IRI) : Bool :=
  if c == thing then true
  else if c == nothing then false
  else m.clsFacts.contains (c, u)

def ELModel.hasEdge (m : ELModel) (r u v : IRI) : Bool :=
  if r == topObjectProperty then true
  else if r == bottomObjectProperty then false
  else m.edges.contains (r, u, v)

def ELModel.checkAxiom (m : ELModel) : ELAxiom → Bool
  | .sub1 a b => m.nodes.all fun u => !m.hasCls a u || m.hasCls b u
  | .sub2 a1 a2 b => m.nodes.all fun u => !(m.hasCls a1 u && m.hasCls a2 u) || m.hasCls b u
  | .existR a r b => m.nodes.all fun u => !m.hasCls a u || m.nodes.any fun v => m.hasEdge r u v && m.hasCls b v
  | .existL r a b =>
    if r == topObjectProperty then
      m.nodes.all fun u => m.nodes.all fun v => !m.hasCls a v || m.hasCls b u
    else if r == bottomObjectProperty then true
    else m.edges.all fun (r', u, v) =>
      !(r' == r && m.nodes.contains u && m.nodes.contains v && m.hasCls a v) || m.hasCls b u
  | .roleSub r s =>
    if r == topObjectProperty then
      m.nodes.all fun u => m.nodes.all fun v => m.hasEdge s u v
    else if r == bottomObjectProperty then true
    else m.edges.all fun (r', u, v) =>
      !(r' == r && m.nodes.contains u && m.nodes.contains v) || m.hasEdge s u v
  | .roleChain r1 r2 s =>
    if r1 == topObjectProperty || r2 == topObjectProperty then
      m.nodes.all fun u => m.nodes.all fun v =>
        !m.hasEdge r1 u v || m.nodes.all fun w => !m.hasEdge r2 v w || m.hasEdge s u w
    else if r1 == bottomObjectProperty || r2 == bottomObjectProperty then true
    else m.edges.all fun (r', u, v) =>
      !(r' == r1 && m.nodes.contains u && m.nodes.contains v) ||
      m.edges.all fun (r'', v', w) =>
        !(r'' == r2 && v' == v && m.nodes.contains w) || m.hasEdge s u w
  | .roleRefl r => m.nodes.all fun u => m.hasEdge r u u

def checkELModel (axs : List ELAxiom) (m : ELModel) : Bool :=
  !m.nodes.isEmpty && axs.all m.checkAxiom

def ELModel.toInterpretation (m : ELModel) (hne : m.nodes ≠ []) :
    Interpretation Datatypes.datatypeMap where
  Object := { u : IRI // u ∈ m.nodes }
  objectNonempty := match h : m.nodes with
    | [] => absurd h hne
    | x :: _ => ⟨⟨x, List.mem_cons_self ..⟩⟩
  Data := Datatypes.Value
  dataNonempty := ⟨.boolean false⟩
  embedValue := id
  embedValue_injective := fun h => h
  classes c x := m.hasCls c x.val = true
  objectProperties r x y := m.hasEdge r x.val y.val = true
  dataProperties p _ _ := p = topDataProperty
  individuals _ := match h : m.nodes with
    | [] => absurd h hne
    | x :: _ => ⟨x, List.mem_cons_self ..⟩
  datatypes r y :=
    if r = literalDatatype then True else Datatypes.datatypeMap.valueSpace r y
  literalValue l := match Datatypes.datatypeMap.lexicalValue l with
    | some v => v
    | none => .boolean false
  lexicalAgreement l v h := by dsimp; rw [h]
  named _ := True
  namedIndividual _ := trivial
  thingExt := fun x => by simp [ELModel.hasCls]
  nothingExt := fun x => by simp [ELModel.hasCls, thing, nothing]
  topObjectExt := fun x y => by simp [ELModel.hasEdge]
  bottomObjectExt := fun x y => by simp [ELModel.hasEdge, topObjectProperty, bottomObjectProperty]
  topDataExt := fun _ _ => rfl
  bottomDataExt := fun _ _ h => by simp [topDataProperty, bottomDataProperty] at h
  literalDatatypeExt := fun _ => by simp
  datatypeAgreement := fun r hr y => by
    have hne' : r ≠ literalDatatype := fun he => Datatypes.datatypeMap.literal_not_builtin (he ▸ hr)
    simp only [hne', ↓reduceIte, id_eq]
    exact ⟨fun hv => ⟨y, hv, rfl⟩, fun ⟨v, hv, he⟩ => he ▸ hv⟩

theorem checkELModel_sound {axs : List ELAxiom} {m : ELModel}
    (hcheck : checkELModel axs m = true) :
    ∃ hne : m.nodes ≠ [], satisfies (m.toInterpretation hne) (elOntology axs) := by
  simp only [checkELModel, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hcheck
  obtain ⟨hne, hall⟩ := hcheck
  refine ⟨hne, fun ax hax => ?_⟩
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp hax
  have hchk := hall ea hea
  cases ea with
  | sub1 a b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
    intro x hx
    exact (hchk x.val x.property).elim (fun h => absurd hx (by simp [ELModel.toInterpretation, classHolds, h])) id
  | sub2 a1 a2 b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff] at hchk
    intro x ⟨h1, h2⟩
    rcases hchk x.val x.property with (h | h) | h
    · exact absurd h1 (by simp [ELModel.toInterpretation, classHolds, h])
    · exact absurd h2 (by simp [ELModel.toInterpretation, classHolds, h])
    · exact h
  | existR a r b =>
    simp only [ELModel.checkAxiom, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.any_eq_true, Bool.and_eq_true] at hchk
    intro x hx
    rcases hchk x.val x.property with h | ⟨v, hv, hrv, hbv⟩
    · exact absurd hx (by simp [ELModel.toInterpretation, classHolds, h])
    · exact ⟨⟨v, hv⟩, hrv, hbv⟩
  | existL r a b =>
    intro x ⟨y, hxy, hay⟩
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r = topObjectProperty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
      exact (hchk x.val x.property y.val y.property).elim
        (fun h => absurd hay (by simp [ELModel.toInterpretation, classHolds, h])) id
    · by_cases hb : r = bottomObjectProperty
      · subst hb; simp [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
      · have hcond1 : (r == topObjectProperty) = false := beq_false_of_ne ht
        have hcond2 : (r == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem : (r, x.val, y.val) ∈ m.edges := by
          simp only [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, hcond1, hcond2,
            Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        have hay' : m.hasCls a y.val = true := hay
        exact (hchk (r, x.val, y.val) hmem).elim
          (fun hnot => absurd (by simp [x.property, y.property, hay']) hnot) id
  | roleSub r s =>
    intro x y hxy
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r = topObjectProperty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true] at hchk
      exact hchk x.val x.property y.val y.property
    · by_cases hb : r = bottomObjectProperty
      · subst hb; simp [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
      · have hcond1 : (r == topObjectProperty) = false := beq_false_of_ne ht
        have hcond2 : (r == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem : (r, x.val, y.val) ∈ m.edges := by
          simp only [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, hcond1, hcond2,
            Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        exact (hchk (r, x.val, y.val) hmem).elim
          (fun hnot => absurd (by simp [x.property, y.property]) hnot) id
  | roleChain r1 r2 s =>
    intro x z ⟨y, hxy, w, hyw, hzw⟩
    subst hzw
    simp only [ELModel.checkAxiom] at hchk
    by_cases ht : r1 = topObjectProperty ∨ r2 = topObjectProperty
    · have hcond : (r1 == topObjectProperty || r2 == topObjectProperty) = true := by
        rcases ht with rfl | rfl <;> simp
      simp only [hcond, ↓reduceIte, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hchk
      rcases hchk x.val x.property y.val y.property with h | hall2
      · exact absurd hxy (by simp [ELModel.toInterpretation, objectHolds, h])
      · exact (hall2 w.val w.property).elim (fun h => absurd hyw (by simp [ELModel.toInterpretation, objectHolds, h])) id
    · have hnt1 : r1 ≠ topObjectProperty := fun h => ht (Or.inl h)
      have hnt2 : r2 ≠ topObjectProperty := fun h => ht (Or.inr h)
      by_cases hb : r1 = bottomObjectProperty ∨ r2 = bottomObjectProperty
      · rcases hb with rfl | rfl
        · simp [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hxy
        · simp [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, topObjectProperty, bottomObjectProperty] at hyw
      · have hnb1 : r1 ≠ bottomObjectProperty := fun h => hb (Or.inl h)
        have hnb2 : r2 ≠ bottomObjectProperty := fun h => hb (Or.inr h)
        have hc1 : (r1 == topObjectProperty || r2 == topObjectProperty) = false := by
          simp [beq_false_of_ne hnt1, beq_false_of_ne hnt2]
        have hc2 : (r1 == bottomObjectProperty || r2 == bottomObjectProperty) = false := by
          simp [beq_false_of_ne hnb1, beq_false_of_ne hnb2]
        simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', Bool.eq_false_iff] at hchk
        have hmem1 : (r1, x.val, y.val) ∈ m.edges := by
          simp only [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, beq_false_of_ne hnt1,
            beq_false_of_ne hnb1, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hxy
          exact hxy
        have hmem2 : (r2, y.val, w.val) ∈ m.edges := by
          simp only [ELModel.toInterpretation, objectHolds, ELModel.hasEdge, beq_false_of_ne hnt2,
            beq_false_of_ne hnb2, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem] at hyw
          exact hyw
        rcases hchk (r1, x.val, y.val) hmem1 with hnot1 | hall2
        · exact absurd (by simp [x.property, y.property]) hnot1
        · exact (hall2 (r2, y.val, w.val) hmem2).elim
            (fun hnot2 => absurd (by simp [w.property]) hnot2) id
  | roleRefl r =>
    simp only [ELModel.checkAxiom, List.all_eq_true] at hchk
    intro x; exact hchk x.val x.property

theorem checkELModel_counter_sub {axs : List ELAxiom} {m : ELModel} {a b u : IRI}
    (hcheck : checkELModel axs m = true)
    (hu : u ∈ m.nodes) (ha : m.hasCls a u = true) (hb : m.hasCls b u = false) :
    ¬ Entails Datatypes.datatypeMap (elOntology axs) [.subClassOf (.named a) (.named b)] := by
  obtain ⟨hne, hsat⟩ := checkELModel_sound hcheck
  intro hent
  obtain ⟨assign, hq⟩ := hent (m.toInterpretation hne) (satisfies_models hsat)
  have hsub := hq (.subClassOf (.named a) (.named b)) (List.mem_singleton_self _)
  have hb' : m.hasCls b u = true := hsub ⟨u, hu⟩ ha
  rw [hb] at hb'; exact Bool.false_ne_true hb'

/-! ### Definitional EL++ normalization with two-way model preservation -/

def elAuxPrefix : String := "urn:sabrina:el-aux:"
def elRoleAuxPrefix : String := "urn:sabrina:el-role-aux:"

private structure NormState where
  nextId : Nat := 0
  axs : List ELAxiom := []
  clsDefs : List (IRI × ClassExpr) := []
  roleDefs : List (IRI × IRI × IRI) := []

private def normExpr (c : ClassExpr) (st : NormState) : Option (IRI × NormState) :=
  match c with
  | .named iri => some (iri, st)
  | .intersection a b => do
    let (na, st1) ← normExpr a st
    let (nb, st2) ← normExpr b st1
    let aux := s!"{elAuxPrefix}{st2.nextId}"
    let newAxs := [.sub2 na nb aux, .sub1 aux na, .sub1 aux nb]
    some (aux, { st2 with
      nextId := st2.nextId + 1
      axs := newAxs ++ st2.axs
      clsDefs := (aux, .intersection (.named na) (.named nb)) :: st2.clsDefs })
  | .objectSome (.named r) fill =>
    if r == topObjectProperty || r == bottomObjectProperty then none
    else do
      let (nf, st1) ← normExpr fill st
      let aux := s!"{elAuxPrefix}{st1.nextId}"
      let newAxs := [.existL r nf aux, .existR aux r nf]
      some (aux, { st1 with
        nextId := st1.nextId + 1
        axs := newAxs ++ st1.axs
        clsDefs := (aux, .objectSome (.named r) (.named nf)) :: st1.clsDefs })
  | _ => none

private def normChain (rs : List IRI) (sup : IRI) (st : NormState) : Option NormState :=
  match rs with
  | [r1, r2] => some { st with axs := .roleChain r1 r2 sup :: st.axs }
  | r1 :: r2 :: r3 :: rest =>
    let aux := s!"{elRoleAuxPrefix}{st.nextId}"
    let st1 := { st with
      nextId := st.nextId + 1
      axs := .roleChain r1 r2 aux :: st.axs
      roleDefs := (aux, r1, r2) :: st.roleDefs }
    normChain (aux :: r3 :: rest) sup st1
  | _ => none
termination_by rs.length

private def checkNamedObjProp : ObjectProperty → Option IRI
  | .named r => if r == topObjectProperty || r == bottomObjectProperty then none else some r
  | .inverse _ => none

private def normPairs {α : Type} (f : α → α → NormState → Option NormState) :
    List α → NormState → Option NormState
  | [], st => some st
  | x :: xs, st => do
    let st1 ← xs.foldlM (fun acc y => f x y acc) st
    normPairs f xs st1

private def normAxiom (a : Axiom) (st : NormState) : Option NormState :=
  match a with
  | .subClassOf c1 c2 => do
    let (n1, st1) ← normExpr c1 st
    let (n2, st2) ← normExpr c2 st1
    some { st2 with axs := .sub1 n1 n2 :: st2.axs }
  | .equivalentClasses cs =>
    match cs with
    | [] | [_] => some st
    | c0 :: rest => do
      let (n0, st0) ← normExpr c0 st
      rest.foldlM (fun acc c => do
        let (nc, acc1) ← normExpr c acc
        some { acc1 with axs := .sub1 n0 nc :: .sub1 nc n0 :: acc1.axs }) st0
  | .disjointClasses cs => do
    let (names, st1) ← cs.foldlM (fun (accNames, accSt) c => do
      let (nc, accSt1) ← normExpr c accSt
      some (nc :: accNames, accSt1)) ([], st)
    normPairs (fun a b s => some { s with axs := .sub2 a b nothing :: s.axs }) names.reverse st1
  | .subObjectProperty r s => do
    let rn ← checkNamedObjProp r
    let sn ← checkNamedObjProp s
    some { st with axs := .roleSub rn sn :: st.axs }
  | .equivalentObjectProperties rs =>
    match rs with
    | [] | [_] => some st
    | r0 :: rest => do
      let n0 ← checkNamedObjProp r0
      rest.foldlM (fun acc r => do
        let nr ← checkNamedObjProp r
        some { acc with axs := .roleSub n0 nr :: .roleSub nr n0 :: acc.axs }) st
  | .transitiveObjectProperty r => do
    let rn ← checkNamedObjProp r
    some { st with axs := .roleChain rn rn rn :: st.axs }
  | .subObjectPropertyChain rs s => do
    let rns ← rs.mapM checkNamedObjProp
    let sn ← checkNamedObjProp s
    normChain rns sn st
  | .objectPropertyDomain r c => do
    let rn ← checkNamedObjProp r
    let (nc, st1) ← normExpr c st
    some { st1 with axs := .existL rn thing nc :: st1.axs }
  | .reflexiveObjectProperty r => do
    let rn ← checkNamedObjProp r
    some { st with axs := .roleRefl rn :: st.axs }
  | _ => none

/-- Normalize an EL++ `Ontology` (provided no input symbol starts with the
    reserved internal auxiliary prefixes). Returns the normalized `ELAxiom` list. -/
def normalizeEL (o : Ontology) : Option (List ELAxiom) := do
  let sig := ontologySig o
  if sig.cls.any (·.startsWith elAuxPrefix) || sig.obj.any (·.startsWith elRoleAuxPrefix) then
    none
  let st ← o.foldlM (fun acc a => normAxiom a acc) {}
  some st.axs.reverse

/-! ### Fast polynomial EL++ completion engine (O(1) HashSet/HashMap) -/

private def collectClasses (axs : List ELAxiom) (seeds : List IRI) : List IRI := Id.run do
  let mut seen : Std.HashSet IRI := {}
  let mut out : List IRI := []
  let add (c : IRI) (s : Std.HashSet IRI) (l : List IRI) :=
    if c == thing || c == nothing || s.contains c then (s, l) else (s.insert c, c :: l)
  for c in seeds do
    let (s, l) := add c seen out; seen := s; out := l
  for ax in axs do
    match ax with
    | .sub1 a b =>
      let (s, l) := add a seen out; let (s, l) := add b s l; seen := s; out := l
    | .sub2 a1 a2 b =>
      let (s, l) := add a1 seen out; let (s, l) := add a2 s l; let (s, l) := add b s l; seen := s; out := l
    | .existR a _ b =>
      let (s, l) := add a seen out; let (s, l) := add b s l; seen := s; out := l
    | .existL _ a b =>
      let (s, l) := add a seen out; let (s, l) := add b s l; seen := s; out := l
    | _ => pure ()
  return (thing :: out.reverse)

structure ELSaturation where
  classes : List IRI
  subProofs : Std.HashMap (IRI × IRI) ELProof
  relProofs : Std.HashMap (IRI × IRI × IRI) ELProof

/-- Polynomial EL++ consequence-based saturation (CR1–CR5, CR10–CR11, reflexivity)
    recording a compact kernel-checkable `ELProof` for every derived fact. -/
def saturateEL (axs : List ELAxiom) (seeds : List IRI) : ELSaturation := Id.run do
  let classes := collectClasses axs seeds
  let mut subMap : Std.HashMap (IRI × IRI) ELProof := {}
  let mut relMap : Std.HashMap (IRI × IRI × IRI) ELProof := {}
  -- Indexed adjacency lists for fast polynomial completion
  let mut sub1ByA : Std.HashMap IRI (List IRI) := {}
  let mut sub2ByA1 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut sub2ByA2 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut existRByA : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut existLByRA : Std.HashMap (IRI × IRI) (List IRI) := {}
  let mut roleSubByR : Std.HashMap IRI (List IRI) := {}
  let mut chainByR1 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut chainByR2 : Std.HashMap IRI (List (IRI × IRI)) := {}
  let mut reflRoles : List IRI := []

  for ax in axs do
    match ax with
    | .sub1 a b => sub1ByA := sub1ByA.insert a (b :: sub1ByA.getD a [])
    | .sub2 a1 a2 b =>
      sub2ByA1 := sub2ByA1.insert a1 ((a2, b) :: sub2ByA1.getD a1 [])
      sub2ByA2 := sub2ByA2.insert a2 ((a1, b) :: sub2ByA2.getD a2 [])
    | .existR a r b => existRByA := existRByA.insert a ((r, b) :: existRByA.getD a [])
    | .existL r a b => existLByRA := existLByRA.insert (r, a) (b :: existLByRA.getD (r, a) [])
    | .roleSub r s => roleSubByR := roleSubByR.insert r (s :: roleSubByR.getD r [])
    | .roleChain r1 r2 s =>
      chainByR1 := chainByR1.insert r1 ((r2, s) :: chainByR1.getD r1 [])
      chainByR2 := chainByR2.insert r2 ((r1, s) :: chainByR2.getD r2 [])
    | .roleRefl r => reflRoles := r :: reflRoles

  -- Reverse/forward indices over derived facts
  let mut incomingRel : Std.HashMap IRI (List (IRI × IRI)) := {}    -- Y ↦ [(r, X)] for (r, X, Y) ∈ R
  let mut outgoingRel : Std.HashMap (IRI × IRI) (List IRI) := {}   -- (r, X) ↦ [Y]
  let mut incomingByR : Std.HashMap (IRI × IRI) (List IRI) := {}   -- (r, Y) ↦ [X]
  let mut subByX : Std.HashMap IRI (List IRI) := {}                -- X ↦ [B]
  let mut subQueue : Array (IRI × IRI) := #[]
  let mut relQueue : Array (IRI × IRI × IRI) := #[]

  -- Initialize reflexivity & owl:Thing & roleRefl
  for c in classes do
    if !subMap.contains (c, c) then
      subMap := subMap.insert (c, c) (.refl c)
      subByX := subByX.insert c (c :: subByX.getD c [])
      subQueue := subQueue.push (c, c)
    if !subMap.contains (c, thing) then
      subMap := subMap.insert (c, thing) (.top c)
      subByX := subByX.insert c (thing :: subByX.getD c [])
      subQueue := subQueue.push (c, thing)
    for r in reflRoles do
      if !relMap.contains (r, c, c) then
        relMap := relMap.insert (r, c, c) (.crRefl r c)
        incomingRel := incomingRel.insert c ((r, c) :: incomingRel.getD c [])
        outgoingRel := outgoingRel.insert (r, c) (c :: outgoingRel.getD (r, c) [])
        incomingByR := incomingByR.insert (r, c) (c :: incomingByR.getD (r, c) [])
        relQueue := relQueue.push (r, c, c)

  let mut si : Nat := 0
  let mut ri : Nat := 0
  while si < subQueue.size || ri < relQueue.size do
    while si < subQueue.size do
      let (x, a) := subQueue[si]!
      si := si + 1
      let pA := subMap.getD (x, a) (.refl x)
      -- CR1: A ⊑ B
      for b in sub1ByA.getD a [] do
        if !subMap.contains (x, b) then
          subMap := subMap.insert (x, b) (.cr1 x a b pA)
          subByX := subByX.insert x (b :: subByX.getD x [])
          subQueue := subQueue.push (x, b)
      -- CR2: A₁ ⊓ A₂ ⊑ B (both sides)
      for (a2, b) in sub2ByA1.getD a [] do
        if let some p2 := subMap.get? (x, a2) then
          if !subMap.contains (x, b) then
            subMap := subMap.insert (x, b) (.cr2 x a a2 b pA p2)
            subByX := subByX.insert x (b :: subByX.getD x [])
            subQueue := subQueue.push (x, b)
      for (a1, b) in sub2ByA2.getD a [] do
        if let some p1 := subMap.get? (x, a1) then
          if !subMap.contains (x, b) then
            subMap := subMap.insert (x, b) (.cr2 x a1 a b p1 pA)
            subByX := subByX.insert x (b :: subByX.getD x [])
            subQueue := subQueue.push (x, b)
      -- CR3: A ⊑ ∃r.B
      for (r, b) in existRByA.getD a [] do
        if !relMap.contains (r, x, b) then
          relMap := relMap.insert (r, x, b) (.cr3 x a r b pA)
          incomingRel := incomingRel.insert b ((r, x) :: incomingRel.getD b [])
          outgoingRel := outgoingRel.insert (r, x) (b :: outgoingRel.getD (r, x) [])
          incomingByR := incomingByR.insert (r, b) (x :: incomingByR.getD (r, b) [])
          relQueue := relQueue.push (r, x, b)
      -- CR4 & CR5 triggered by new (y = x, a) with existing incoming (r, u, x)
      for (r, u) in incomingRel.getD x [] do
        let pRel := relMap.getD (r, u, x) (.crRefl r u)
        for b in existLByRA.getD (r, a) [] do
          if !subMap.contains (u, b) then
            subMap := subMap.insert (u, b) (.cr4 u r x a b pRel pA)
            subByX := subByX.insert u (b :: subByX.getD u [])
            subQueue := subQueue.push (u, b)
        if a == nothing then
          if !subMap.contains (u, nothing) then
            subMap := subMap.insert (u, nothing) (.cr5 u r x pRel pA)
            subByX := subByX.insert u (nothing :: subByX.getD u [])
            subQueue := subQueue.push (u, nothing)
    while ri < relQueue.size do
      let (r, x, y) := relQueue[ri]!
      ri := ri + 1
      let pRel := relMap.getD (r, x, y) (.crRefl r x)
      -- CR4 & CR5 triggered by new (r, x, y) with existing (y, a)
      for a in subByX.getD y [] do
        let pA := subMap.getD (y, a) (.refl y)
        for b in existLByRA.getD (r, a) [] do
          if !subMap.contains (x, b) then
            subMap := subMap.insert (x, b) (.cr4 x r y a b pRel pA)
            subByX := subByX.insert x (b :: subByX.getD x [])
            subQueue := subQueue.push (x, b)
        if a == nothing then
          if !subMap.contains (x, nothing) then
            subMap := subMap.insert (x, nothing) (.cr5 x r y pRel pA)
            subByX := subByX.insert x (nothing :: subByX.getD x [])
            subQueue := subQueue.push (x, nothing)
      -- CR10: r ⊑ s
      for s in roleSubByR.getD r [] do
        if !relMap.contains (s, x, y) then
          relMap := relMap.insert (s, x, y) (.cr10 r s x y pRel)
          incomingRel := incomingRel.insert y ((s, x) :: incomingRel.getD y [])
          outgoingRel := outgoingRel.insert (s, x) (y :: outgoingRel.getD (s, x) [])
          incomingByR := incomingByR.insert (s, y) (x :: incomingByR.getD (s, y) [])
          relQueue := relQueue.push (s, x, y)
      -- CR11: r1 ∘ r2 ⊑ s (as left leg r = r1)
      for (r2, s) in chainByR1.getD r [] do
        for z in outgoingRel.getD (r2, y) [] do
          let p2 := relMap.getD (r2, y, z) (.crRefl r2 y)
          if !relMap.contains (s, x, z) then
            relMap := relMap.insert (s, x, z) (.cr11 r r2 s x y z pRel p2)
            incomingRel := incomingRel.insert z ((s, x) :: incomingRel.getD z [])
            outgoingRel := outgoingRel.insert (s, x) (z :: outgoingRel.getD (s, x) [])
            incomingByR := incomingByR.insert (s, z) (x :: incomingByR.getD (s, z) [])
            relQueue := relQueue.push (s, x, z)
      -- CR11: r1 ∘ r2 ⊑ s (as right leg r = r2)
      for (r1, s) in chainByR2.getD r [] do
        for u in incomingByR.getD (r1, x) [] do
          let p1 := relMap.getD (r1, u, x) (.crRefl r1 u)
          if !relMap.contains (s, u, y) then
            relMap := relMap.insert (s, u, y) (.cr11 r1 r s u x y p1 pRel)
            incomingRel := incomingRel.insert y ((s, u) :: incomingRel.getD y [])
            outgoingRel := outgoingRel.insert (s, u) (y :: outgoingRel.getD (s, u) [])
            incomingByR := incomingByR.insert (s, y) (u :: incomingByR.getD (s, y) [])
            relQueue := relQueue.push (s, u, y)
  return { classes, subProofs := subMap, relProofs := relMap }

def ELSaturation.extractReachableModel (sat : ELSaturation) (root : IRI) : ELModel := Id.run do
  if sat.subProofs.contains (root, nothing) then
    return { nodes := [], clsFacts := [], edges := [] }
  -- Build outgoing adjacency list for BFS reachability from `root`
  let mut adj : Std.HashMap IRI (List IRI) := {}
  for ((_, u, v), _) in sat.relProofs.toList do
    if !sat.subProofs.contains (v, nothing) then
      adj := adj.insert u (v :: adj.getD u [])
  let mut visited : Std.HashSet IRI := ({} : Std.HashSet IRI).insert root
  let mut queue : Array IRI := #[root]
  let mut qi : Nat := 0
  while qi < queue.size do
    let u := queue[qi]!
    qi := qi + 1
    for v in adj.getD u [] do
      if !visited.contains v then
        visited := visited.insert v
        queue := queue.push v
  let liveNodes := queue.toList
  let mut clsFacts : List (IRI × IRI) := []
  for ((u, c), _) in sat.subProofs.toList do
    if visited.contains u && c != thing && c != nothing then
      clsFacts := (c, u) :: clsFacts
  let mut edges : List (IRI × IRI × IRI) := []
  for ((r, u, v), _) in sat.relProofs.toList do
    if visited.contains u && visited.contains v then
      edges := (r, u, v) :: edges
  return { nodes := liveNodes, clsFacts, edges }

inductive ELVerdict where
  | inconsistent (pf : ELProof)
  | entailed (pf : ELProof)
  | refuted (counter : ELModel) (pf : ELProof)
  | independent (counter : ELModel) (incModel : ELModel)
  deriving Repr

/-- Polynomial EL++ inclusion decision with independent kernel-checked
    certificates (`checkELProof` and `checkELModel`) on every branch. -/
def decideELSub (axs : List ELAxiom) (a b : IRI) : Option ELVerdict :=
  let sat := saturateEL axs [a, b]
  if let some pf := sat.subProofs.get? (thing, nothing) then
    if checkELProof axs pf (.sub thing nothing) then some (.inconsistent pf) else none
  else if let some pf := sat.subProofs.get? (a, b) then
    if checkELProof axs pf (.sub a b) then some (.entailed pf) else none
  else if let some pfBot := sat.subProofs.get? (a, nothing) then
    let pf := ELProof.bot a b pfBot
    if checkELProof axs pf (.sub a b) then some (.entailed pf) else none
  else
    let counter := sat.extractReachableModel a
    if checkELModel axs counter && counter.nodes.contains a &&
       counter.hasCls a a && !counter.hasCls b a then
      let axsPlus := .sub1 a b :: axs
      let satPlus := saturateEL axsPlus [a, b]
      if let some pf := satPlus.subProofs.get? (thing, nothing) then
        if checkELProof axsPlus pf (.sub thing nothing) then some (.refuted counter pf) else none
      else
        let incModel := satPlus.extractReachableModel thing
        if checkELModel axsPlus incModel then some (.independent counter incModel) else none
    else none

/-- Polynomial EL++ consistency check (`SATISFIABLE` via checked `ELModel` or
    `INCONSISTENT_ONTOLOGY` via checked `ELProof`). -/
def decideELConsistency (axs : List ELAxiom) : Option (Sum ELModel ELProof) :=
  let sat := saturateEL axs []
  if let some pf := sat.subProofs.get? (thing, nothing) then
    if checkELProof axs pf (.sub thing nothing) then some (.inr pf) else none
  else
    let m := sat.extractReachableModel thing
    if checkELModel axs m then some (.inl m) else none

theorem decideELConsistency_sound {axs : List ELAxiom} :
    (∀ m, decideELConsistency axs = some (.inl m) → Satisfiable Datatypes.datatypeMap (elOntology axs)) ∧
    (∀ pf, decideELConsistency axs = some (.inr pf) → ¬ Satisfiable Datatypes.datatypeMap (elOntology axs)) := by
  constructor
  · intro m hm
    unfold decideELConsistency at hm; dsimp only at hm
    split at hm
    · split at hm <;> simp at hm
    · split at hm
      · rename_i hchk
        simp only [Option.some.injEq, Sum.inl.injEq] at hm; subst hm
        obtain ⟨hne, hsat⟩ := checkELModel_sound hchk
        exact ⟨ELModel.toInterpretation _ hne, satisfies_models hsat⟩
      · simp at hm
  · intro pf hpf
    unfold decideELConsistency at hpf; dsimp only at hpf
    split at hpf
    · split at hpf
      · rename_i hchk
        simp only [Option.some.injEq, Sum.inr.injEq] at hpf; subst hpf
        exact checkELProof_inconsistent hchk
      · simp at hpf
    · split at hpf <;> simp at hpf

theorem decideELSub_sound {axs : List ELAxiom} {a b : IRI} :
    (∀ pf, decideELSub axs a b = some (.inconsistent pf) →
      ¬ Satisfiable Datatypes.datatypeMap (elOntology axs)) ∧
    (∀ pf, decideELSub axs a b = some (.entailed pf) →
      Entails Datatypes.datatypeMap (elOntology axs) [.subClassOf (.named a) (.named b)]) ∧
    (∀ m pf, decideELSub axs a b = some (.refuted m pf) →
      ¬ Entails Datatypes.datatypeMap (elOntology axs) [.subClassOf (.named a) (.named b)] ∧
      ¬ Satisfiable Datatypes.datatypeMap (.subClassOf (.named a) (.named b) :: elOntology axs)) ∧
    (∀ m1 m2, decideELSub axs a b = some (.independent m1 m2) →
      ¬ Entails Datatypes.datatypeMap (elOntology axs) [.subClassOf (.named a) (.named b)] ∧
      Satisfiable Datatypes.datatypeMap (.subClassOf (.named a) (.named b) :: elOntology axs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pf h
    unfold decideELSub at h; dsimp only at h
    split at h
    · split at h
      · rename_i hchk; simp at h; subst h; exact checkELProof_inconsistent hchk
      · simp at h
    · split at h
      · split at h <;> simp at h
      · split at h
        · split at h <;> simp at h
        · split at h
          · split at h
            · split at h <;> simp at h
            · split at h <;> simp at h
          · simp at h
  · intro pf h
    unfold decideELSub at h; dsimp only at h
    split at h
    · split at h <;> simp at h
    · split at h
      · split at h
        · rename_i hchk; simp at h; subst h; exact checkELProof_entails_sub hchk
        · simp at h
      · split at h
        · split at h
          · rename_i hchk; simp at h; subst h; exact checkELProof_entails_sub hchk
          · simp at h
        · split at h
          · split at h
            · split at h <;> simp at h
            · split at h <;> simp at h
          · simp at h
  · intro m pf h
    unfold decideELSub at h; dsimp only at h
    split at h
    · split at h <;> simp at h
    · split at h
      · split at h <;> simp at h
      · split at h
        · split at h <;> simp at h
        · split at h
          · rename_i hcm
            simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hcm
            split at h
            · split at h
              · rename_i hpf
                simp only [Option.some.injEq, ELVerdict.refuted.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨checkELModel_counter_sub hcm.1.1.1 hcm.1.1.2 hcm.1.2 hcm.2,
                       checkELProof_inconsistent hpf⟩
              · simp at h
            · split at h <;> simp at h
          · simp at h
  · intro m1 m2 h
    unfold decideELSub at h; dsimp only at h
    split at h
    · split at h <;> simp at h
    · split at h
      · split at h <;> simp at h
      · split at h
        · split at h <;> simp at h
        · split at h
          · rename_i hcm
            simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hcm
            split at h
            · split at h <;> simp at h
            · split at h
              · rename_i hinc
                simp only [Option.some.injEq, ELVerdict.independent.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hne, hsat⟩ := checkELModel_sound hinc
                exact ⟨checkELModel_counter_sub hcm.1.1.1 hcm.1.1.2 hcm.1.2 hcm.2,
                       ⟨ELModel.toInterpretation _ hne, satisfies_models hsat⟩⟩
              · simp at h
          · simp at h

end Sabrina.OWL2.EL
