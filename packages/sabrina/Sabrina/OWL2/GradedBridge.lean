import Sabrina.OWL2.DirectSemantics
import Sabrina.Graded.Search

/-! Embed the original typed graded fragment into OWL 2. The fragment treats
names as uninterpreted symbols, including strings that spell reserved OWL
IRIs. Its symbols are embedded under a fresh namespace and the logical top
and bottom constructors use their standard OWL denotations. -/

namespace Sabrina.OWL2.GradedBridge

open Sabrina.ALC (OrientedRole RoleTheory)
open Sabrina.RoleChains (Chain)

private def symbolNamespace : String := "urn:sabrina:graded:"

def symbol (s : String) : IRI := symbolNamespace ++ s

private def readSymbol (s : IRI) : String :=
  String.ofList (s.toList.drop symbolNamespace.toList.length)

private theorem readSymbol_symbol (s : String) : readSymbol (symbol s) = s := by
  simp [readSymbol,symbol]

private theorem symbol_head (s : String) : (symbol s).toList.head? = some 'u' := by
  simp [symbol,symbolNamespace]

private theorem symbol_ne_builtin (s : String) :
    symbol s ≠ thing ∧ symbol s ≠ nothing ∧
    symbol s ≠ topObjectProperty ∧ symbol s ≠ bottomObjectProperty := by
  have he (iri : IRI) (h : iri.toList.head? = some 'h') : symbol s ≠ iri := by
    intro eq
    have bad := congrArg (fun r : IRI => r.toList.head?) eq
    rw [symbol_head,h] at bad
    cases bad
  exact ⟨he thing rfl,he nothing rfl,he topObjectProperty rfl,he bottomObjectProperty rfl⟩

def role (r : OrientedRole) : ObjectProperty :=
  if r.2 then .inverse (symbol r.1) else .named (symbol r.1)

def concept : Sabrina.Graded.Concept → ClassExpr
  | .top => .named thing
  | .bottom => .named nothing
  | .lit s true => .named (symbol s)
  | .lit s false => .complement (.named (symbol s))
  | .nom a true => .oneOf [.named (symbol a)]
  | .nom a false => .complement (.oneOf [.named (symbol a)])
  | .self r true => .objectSelf (.named (symbol r))
  | .self r false => .complement (.objectSelf (.named (symbol r)))
  | .conj a b => .intersection (concept a) (concept b)
  | .disj a b => .union (concept a) (concept b)
  | .some r c => .objectSome (.named (symbol r)) (concept c)
  | .all r c => .objectAll (.named (symbol r)) (concept c)
  | .min n r c => .objectMin n (.named (symbol r)) (concept c)
  | .max n r c => .objectMax n (.named (symbol r)) (concept c)

def inclusion (q : Sabrina.Graded.Inclusion) : Axiom :=
  .subClassOf (concept q.sub) (concept q.sup)

def roleInclusion (rs : OrientedRole × OrientedRole) : Axiom :=
  .subObjectProperty (role rs.1) (role rs.2)

def chain (c : Chain) : Axiom :=
  .subObjectPropertyChain (c.body.map role) (.named (symbol c.head))

def roleCharsAxioms (chars : Sabrina.Graded.RoleChars) : Ontology :=
  chars.reflexive.map (fun r => .reflexiveObjectProperty (.named (symbol r))) ++
  chars.irreflexive.map (fun r => .irreflexiveObjectProperty (.named (symbol r))) ++
  chars.asymmetric.map (fun r => .asymmetricObjectProperty (.named (symbol r))) ++
  chars.disjoint.map (fun p => .disjointObjectProperties [role p.1, role p.2])

def ontology (rules : RoleTheory) (chains : List Chain) (tbox : Sabrina.Graded.TBox)
    (chars : Sabrina.Graded.RoleChars := {}) : Ontology :=
  rules.map roleInclusion ++ chains.map chain ++ roleCharsAxioms chars ++ tbox.map inclusion

def reduct {d : DatatypeMap} (i : Interpretation d) : Sabrina.ALC.Interpretation where
  Domain := i.Object
  nonempty := i.objectNonempty
  atom s x := i.classes (symbol s) x
  role r x y := i.objectProperties (symbol r) x y

def reductNom {d : DatatypeMap} (i : Interpretation d) : String → i.Object :=
  fun a => i.individuals (.named (symbol a))

theorem role_iff {d : DatatypeMap} (i : Interpretation d) (r : OrientedRole) (x y : i.Object) :
    objectHolds i (role r) x y ↔ Sabrina.ALC.holdsRole (reduct i) r x y := by
  rcases r with ⟨r,_ | _⟩ <;> rfl

theorem concept_iff {d : DatatypeMap} (i : Interpretation d) (c : Sabrina.Graded.Concept)
    (x : i.Object) :
    classHolds i x (concept c) ↔ Sabrina.Graded.holds (reduct i) (reductNom i) x c := by
  induction c generalizing x with
  | top => exact ⟨fun _ => trivial,fun _ => i.thingExt x⟩
  | bottom => exact ⟨i.nothingExt x,False.elim⟩
  | lit n bit => cases bit <;> rfl
  | nom a bit => cases bit <;> simp [concept,classHolds,Sabrina.Graded.holds,reductNom,eq_comm] <;> exact Iff.rfl
  | self r bit => cases bit <;> simp [concept,classHolds,objectHolds,Sabrina.Graded.holds,reduct]
  | conj a b ha hb => simp only [concept,classHolds,Sabrina.Graded.holds,ha,hb]
  | disj a b ha hb => simp only [concept,classHolds,Sabrina.Graded.holds,ha,hb]
  | some r c ih =>
    simp only [concept,classHolds,Sabrina.Graded.holds,ih,objectHolds,reduct]
  | all r c ih =>
    simp only [concept,classHolds,Sabrina.Graded.holds,ih,objectHolds,reduct]
  | min n r c ih =>
    simp only [concept,classHolds,Sabrina.Graded.holds,AtLeast,Sabrina.Graded.AtLeast,
      ih,objectHolds,reduct] <;> rfl
  | max n r c ih =>
    simp only [concept,classHolds,Sabrina.Graded.holds,AtLeast,Sabrina.Graded.AtLeast,
      ih,objectHolds,reduct] <;> rfl

private theorem rolePath_iff {d : DatatypeMap} (i : Interpretation d) (rs : List OrientedRole)
    (x y : i.Object) :
    rolePath i (rs.map role) x y ↔
      Sabrina.RoleChains.TransitivePaths.WordPath (reduct i) rs x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r tail ih =>
    simp only [List.map_cons,rolePath,role_iff,Sabrina.RoleChains.TransitivePaths.WordPath,ih] <;> rfl

theorem inclusion_iff {d : DatatypeMap} (i : Interpretation d) (q : Sabrina.Graded.Inclusion) :
    axiomHolds i (inclusion q) ↔
      ∀ x, Sabrina.Graded.holds (reduct i) (reductNom i) x q.sub →
        Sabrina.Graded.holds (reduct i) (reductNom i) x q.sup := by
  simp only [inclusion,axiomHolds,concept_iff] <;> rfl

private theorem roleInclusion_iff {d : DatatypeMap} (i : Interpretation d)
    (rs : OrientedRole × OrientedRole) :
    axiomHolds i (roleInclusion rs) ↔ ∀ x y,
      Sabrina.ALC.holdsRole (reduct i) rs.1 x y → Sabrina.ALC.holdsRole (reduct i) rs.2 x y := by
  simp only [roleInclusion,axiomHolds,role_iff] <;> rfl

private theorem chain_iff {d : DatatypeMap} (i : Interpretation d) (c : Chain) :
    axiomHolds i (chain c) ↔ ∀ x y,
      Sabrina.RoleChains.TransitivePaths.WordPath (reduct i) c.body x y → (reduct i).role c.head x y := by
  simp only [chain,axiomHolds,rolePath_iff] <;> rfl

private theorem satisfy_map {d : DatatypeMap} (i : Interpretation d) {α : Type}
    (xs : List α) (f : α → Axiom) :
    satisfies i (xs.map f) ↔ ∀ a ∈ xs, axiomHolds i (f a) := by
  constructor
  · intro h a ha
    exact h _ (List.mem_map_of_mem ha)
  · intro h a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact h x hx

private theorem satisfy_append {d : DatatypeMap} (i : Interpretation d) (a b : Ontology) :
    satisfies i (a ++ b) ↔ satisfies i a ∧ satisfies i b := by
  constructor
  · intro h
    exact ⟨fun ax ha => h ax (List.mem_append_left _ ha),
      fun ax hb => h ax (List.mem_append_right _ hb)⟩
  · intro ⟨ha,hb⟩ ax h
    exact (List.mem_append.mp h).elim (ha ax) (hb ax)

private theorem roleCharsAxioms_iff {d : DatatypeMap} (i : Interpretation d)
    (chars : Sabrina.Graded.RoleChars) :
    satisfies i (roleCharsAxioms chars) ↔ Sabrina.Graded.modelsRoleChars (reduct i) chars := by
  simp only [roleCharsAxioms,satisfy_append,satisfy_map,Sabrina.Graded.modelsRoleChars,and_assoc]
  have hdisj : (∀ a ∈ chars.disjoint, axiomHolds i (.disjointObjectProperties [role a.1, role a.2])) ↔
      ∀ p ∈ chars.disjoint, ∀ x y, ¬ (Sabrina.ALC.holdsRole (reduct i) p.1 x y ∧
        Sabrina.ALC.holdsRole (reduct i) p.2 x y) := by
    constructor
    · intro h p hp x y
      have hp' := h p hp
      simp only [axiomHolds,List.pairwise_cons,List.mem_singleton,forall_eq,List.Pairwise.nil,
        and_true,role_iff] at hp'
      exact hp'.1 x y
    · intro h p hp
      simp only [axiomHolds,List.pairwise_cons,List.mem_singleton,forall_eq,List.Pairwise.nil,
        and_true,role_iff]
      exact ⟨h p hp, by simp⟩
  rw [hdisj]
  simp only [axiomHolds,objectHolds,reduct]

theorem satisfies_iff {d : DatatypeMap} (i : Interpretation d) (rules : RoleTheory)
    (chains : List Chain) (tbox : Sabrina.Graded.TBox) (chars : Sabrina.Graded.RoleChars := {}) :
    satisfies i (ontology rules chains tbox chars) ↔
      Sabrina.ALC.modelsRoles (reduct i) rules ∧
      Sabrina.RoleChains.modelsChains (reduct i) chains ∧
      Sabrina.Graded.modelsRoleChars (reduct i) chars ∧
      Sabrina.Graded.models (reduct i) (reductNom i) tbox := by
  simp only [ontology,satisfy_append,satisfy_map,roleInclusion_iff,chain_iff,roleCharsAxioms_iff,
    inclusion_iff,Sabrina.ALC.modelsRoles,Sabrina.RoleChains.modelsChains,Sabrina.Graded.models,and_assoc]
  constructor
  · rintro ⟨hr,hc,hrc,ht⟩
    exact ⟨fun r s h => hr (r,s) h,hc,hrc,ht⟩
  · rintro ⟨hr,hc,hrc,ht⟩
    exact ⟨fun e h => hr e.1 e.2 h,hc,hrc,ht⟩

theorem models_iff {d : DatatypeMap} (i : Interpretation d) (rules : RoleTheory)
    (chains : List Chain) (tbox : Sabrina.Graded.TBox) (chars : Sabrina.Graded.RoleChars := {}) :
    models i (ontology rules chains tbox chars) ↔
      Sabrina.ALC.modelsRoles (reduct i) rules ∧
      Sabrina.RoleChains.modelsChains (reduct i) chains ∧
      Sabrina.Graded.modelsRoleChars (reduct i) chars ∧
      Sabrina.Graded.models (reduct i) (reductNom i) tbox := by
  constructor
  · rintro ⟨assign,h⟩
    exact (satisfies_iff (i.withAnonymous assign) rules chains tbox chars).mp h
  · intro h
    exact satisfies_models ((satisfies_iff i rules chains tbox chars).mpr h)

/-- Every graded object model extends to an interpretation over any fixed
    datatype map. An extra data value keeps the data domain nonempty. -/
noncomputable def extend (d : DatatypeMap) (i : Sabrina.ALC.Interpretation)
    (nom : String → i.Domain := fun _ => Classical.choice i.nonempty) : Interpretation d where
  Object := i.Domain
  objectNonempty := i.nonempty
  Data := Option d.Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes r x := if r = thing then True else if r = nothing then False else i.atom (readSymbol r) x
  objectProperties r x y :=
    if r = topObjectProperty then True else if r = bottomObjectProperty then False
    else i.role (readSymbol r) x y
  dataProperties r _ _ := r = topDataProperty
  individuals
    | .named a => nom (readSymbol a)
    | .anonymous _ _ => Classical.choice i.nonempty
  datatypes t y := t = literalDatatype ∨ ∃ v, d.valueSpace t v ∧ some v = y
  literalValue := d.lexicalValue
  lexicalAgreement := fun _ _ h => h
  named _ := True
  namedIndividual _ := trivial
  thingExt := by simp
  nothingExt := by
    have h : nothing ≠ thing := by decide
    simp [h]
  topObjectExt := by simp
  bottomObjectExt := by
    have h : bottomObjectProperty ≠ topObjectProperty := by decide
    simp [h]
  topDataExt := by simp
  bottomDataExt := by
    intro _ _
    decide
  literalDatatypeExt := by simp
  datatypeAgreement := by
    intro t ht y
    have hn : t ≠ literalDatatype := fun e => d.literal_not_builtin (e ▸ ht)
    simp [hn]

theorem reduct_extend (d : DatatypeMap) (i : Sabrina.ALC.Interpretation)
    (nom : String → i.Domain := fun _ => Classical.choice i.nonempty) :
    reduct (extend d i nom) = i := by
  cases i with
  | mk domain nonempty atom relation =>
    have ha (s : String) (x : domain) :
        (reduct (extend d ⟨domain,nonempty,atom,relation⟩ nom)).atom s x = atom s x := by
      have hn := symbol_ne_builtin s
      simp [reduct,extend,hn.1,hn.2.1,readSymbol_symbol]
    have hr (s : String) (x y : domain) :
        (reduct (extend d ⟨domain,nonempty,atom,relation⟩ nom)).role s x y = relation s x y := by
      have hn := symbol_ne_builtin s
      simp [reduct,extend,hn.2.2.1,hn.2.2.2,readSymbol_symbol]
    have hea := funext fun s => funext (ha s)
    have her := funext fun s => funext fun x => funext (hr s x)
    apply (Sabrina.ALC.Interpretation.mk.injEq ..).mpr
    exact ⟨rfl,heq_of_eq hea,heq_of_eq her⟩

theorem reductNom_extend (d : DatatypeMap) (i : Sabrina.ALC.Interpretation)
    (nom : String → i.Domain) :
    reductNom (extend d i nom) = nom := by
  funext a
  simp [reductNom,extend,readSymbol_symbol]

private theorem holds_ext {i₁ i₂ : Sabrina.ALC.Interpretation} (h : i₁ = i₂)
    {nom₁ : String → i₁.Domain} {nom₂ : String → i₂.Domain} (hnom : HEq nom₁ nom₂)
    {x₁ : i₁.Domain} {x₂ : i₂.Domain} (hx : HEq x₁ x₂) (c : Sabrina.Graded.Concept) :
    Sabrina.Graded.holds i₁ nom₁ x₁ c ↔ Sabrina.Graded.holds i₂ nom₂ x₂ c := by
  subst h; subst hnom; subst hx; rfl

private theorem models_ext {i₁ i₂ : Sabrina.ALC.Interpretation} (h : i₁ = i₂)
    {nom₁ : String → i₁.Domain} {nom₂ : String → i₂.Domain} (hnom : HEq nom₁ nom₂)
    (tbox : Sabrina.Graded.TBox) :
    Sabrina.Graded.models i₁ nom₁ tbox ↔ Sabrina.Graded.models i₂ nom₂ tbox := by
  subst h; subst hnom; rfl

theorem conceptSat_iff (d : DatatypeMap) (rules : RoleTheory) (chains : List Chain)
    (tbox : Sabrina.Graded.TBox) (root : Sabrina.Graded.Concept)
    (chars : Sabrina.Graded.RoleChars := {}) :
    Sabrina.Graded.ConceptSat rules chains tbox root chars ↔
      ∃ i : Interpretation d, models i (ontology rules chains tbox chars) ∧
        ∃ x, classHolds i x (concept root) := by
  constructor
  · rintro ⟨i,nom,hr,hc,hrc,ht,x,hx⟩
    have hre := reduct_extend d i nom
    have hrn : HEq (reductNom (extend d i nom)) nom := heq_of_eq (reductNom_extend d i nom)
    have hw : Sabrina.Graded.holds (reduct (extend d i nom)) (reductNom (extend d i nom)) x root :=
      (holds_ext hre hrn HEq.rfl root).mpr hx
    refine ⟨extend d i nom,(models_iff _ _ _ _ _).mpr ?_,x,(concept_iff _ _ _).mpr hw⟩
    exact ⟨by simpa only [reduct_extend] using hr,
      by simpa only [reduct_extend] using hc,
      by simpa only [reduct_extend] using hrc,
      (models_ext hre hrn tbox).mpr ht⟩
  · rintro ⟨i,hm,x,hx⟩
    obtain ⟨hr,hc,hrc,ht⟩ := (models_iff i _ _ _ _).mp hm
    exact ⟨reduct i,reductNom i,hr,hc,hrc,ht,x,(concept_iff i _ _).mp hx⟩

theorem satisfiable_iff (d : DatatypeMap) (rules : RoleTheory) (chains : List Chain)
    (tbox : Sabrina.Graded.TBox) (chars : Sabrina.Graded.RoleChars := {}) :
    Satisfiable d (ontology rules chains tbox chars) ↔
      Sabrina.Graded.ConceptSat rules chains tbox .top chars := by
  rw [conceptSat_iff d rules chains tbox .top chars]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨x⟩ := i.objectNonempty
    exact ⟨i,hi,x,i.thingExt x⟩
  · rintro ⟨i,hi,_⟩
    exact ⟨i,hi⟩

theorem query_models_iff {d : DatatypeMap} (i : Interpretation d) (q : Sabrina.Graded.Inclusion) :
    models i [inclusion q] ↔ axiomHolds i (inclusion q) := by
  constructor
  · rintro ⟨assign,h⟩
    exact (inclusion_iff i q).mpr ((inclusion_iff (i.withAnonymous assign) q).mp (h _ (by simp)))
  · intro h
    apply satisfies_models
    intro a ha
    rw [List.mem_singleton.mp ha]
    exact h

theorem entails_iff_no_countermodel (d : DatatypeMap) (rules : RoleTheory)
    (chains : List Chain) (tbox : Sabrina.Graded.TBox) (q : Sabrina.Graded.Inclusion)
    (chars : Sabrina.Graded.RoleChars := {}) :
    Entails d (ontology rules chains tbox chars) [inclusion q] ↔
      ¬ (Sabrina.Graded.counterProblem rules chains tbox q chars).Sat := by
  change Entails d (ontology rules chains tbox chars) [inclusion q] ↔
    ¬ Sabrina.Graded.ConceptSat rules chains tbox (.conj q.sub q.sup.dual) chars
  rw [conceptSat_iff d rules chains tbox _ chars]
  constructor
  · rintro h ⟨i,hi,x,hx⟩
    obtain ⟨hsub,hn⟩ := (concept_iff i _ x).mp hx
    have hs := (inclusion_iff i q).mp ((query_models_iff i q).mp (h i hi))
    exact (Sabrina.Graded.holds_dual (reduct i) (reductNom i) x q.sup).mp hn (hs x hsub)
  · intro h i hi
    apply (query_models_iff i q).mpr
    apply (inclusion_iff i q).mpr
    intro x hx
    apply Classical.byContradiction
    intro hn
    exact h ⟨i,hi,x,(concept_iff i _ x).mpr
      ⟨hx,(Sabrina.Graded.holds_dual (reduct i) (reductNom i) x q.sup).mpr hn⟩⟩

def verdictClaim (d : DatatypeMap) (rules : RoleTheory) (chains : List Chain)
    (tbox : Sabrina.Graded.TBox) (q : Sabrina.Graded.Inclusion)
    (chars : Sabrina.Graded.RoleChars := {}) : Sabrina.ALC.InclusionVerdict → Prop
  | .entailed => Satisfiable d (ontology rules chains tbox chars) ∧
      Entails d (ontology rules chains tbox chars) [inclusion q]
  | .refuted => Satisfiable d (ontology rules chains tbox chars) ∧
      ¬ Satisfiable d (ontology rules chains (q :: tbox) chars)
  | .independent => ¬ Entails d (ontology rules chains tbox chars) [inclusion q] ∧
      Satisfiable d (ontology rules chains (q :: tbox) chars)
  | .inconsistent => ¬ Satisfiable d (ontology rules chains tbox chars)

/-- The executable graded checker's successful verdicts hold in the shared
    OWL 2 model theory on the embedded axioms and query. -/
theorem certificate_sound (d : DatatypeMap) {rules chains tbox q maxNodes evidence chars}
    (h : Sabrina.Graded.checkInclusion rules chains tbox q maxNodes evidence chars = true) :
    verdictClaim d rules chains tbox q chars evidence.verdict := by
  have hc := (Sabrina.Graded.checkInclusion_sound h).2
  have he := entails_iff_no_countermodel d rules chains tbox q chars
  have hs := satisfiable_iff d rules chains tbox chars
  have hq : Satisfiable d (ontology rules chains (q :: tbox) chars) ↔
      (Sabrina.Graded.inclusionProblem rules chains tbox q chars).Sat :=
    satisfiable_iff d rules chains (q :: tbox) chars
  cases hv : evidence.verdict <;> rw [hv] at hc
  · exact ⟨hs.mpr hc.2,he.mpr hc.1⟩
  · exact ⟨hs.mpr hc.2,fun hp => hc.1 (hq.mp hp)⟩
  · exact ⟨fun ht => he.mp ht hc.1,hq.mpr hc.2⟩
  · exact fun hp => hc (hs.mp hp)

end Sabrina.OWL2.GradedBridge
