import Std.Data.HashSet
import Std.Data.HashMap
import Sabrina.OWL2.Profile

/-! Hash-indexed O(|O| + |M|) syntactic ⊥-locality module extraction
    (Milestone E.1), targeting sub-second extraction on 350,000+-axiom clinical
    ontologies such as SNOMED CT.

    Maintains a `Std.HashSet`-backed signature (`FastSig`) and an inverted
    symbol-to-axiom-index map (`LocalityIndex`), runs an indexed worklist
    fixpoint, and certifies both locality and minimality in linear time with
    O(1) hash lookups.

    Kernel-checked theorems (strictly `[propext, Classical.choice, Quot.sound]`):
    * `isBotLocalAxiom_antitone` — syntactic ⊥-locality is anti-monotone in σ
    * `extractBotModule_least` — `extractBotModule` is the unique least ⊥-local module
    * `isBotLocalAxiomFast_eq` — exact agreement between `FastSig` and `Sig` locality
    * `extractBotModuleFast_mem_iff` — exact set equality with `extractBotModule`
    * `extractBotModuleFast_sat_iff` — satisfiability preservation
    * `extractBotModuleFast_entails_iff` — entailment conservativity. -/

namespace Sabrina.OWL2.FastLocality

open Sabrina.OWL2
open Sabrina.OWL2.Profile

/-! ### 1. Anti-Monotonicity & Least-Fixed-Point Minimality of `extractBotModule` -/

private theorem isBotObjProp_antitone {σ₁ σ₂ : Sig} (hsub : σ₁.Subset σ₂) {r : ObjectProperty}
    (h : isBotObjProp σ₂ r = true) : isBotObjProp σ₁ r = true := by
  simp only [isBotObjProp, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h ⊢
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h2, ?_⟩
    cases h1 : σ₁.hasObj (objPropIRI r)
    · rfl
    · exact absurd (hsub.2.1 _ h1) (by simp [h3])

private theorem isBotDataProp_antitone {σ₁ σ₂ : Sig} (hsub : σ₁.Subset σ₂) {p : IRI}
    (h : isBotDataProp σ₂ p = true) : isBotDataProp σ₁ p = true := by
  simp only [isBotDataProp, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h ⊢
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h2, ?_⟩
    cases h1 : σ₁.hasData p
    · rfl
    · exact absurd (hsub.2.2 _ h1) (by simp [h3])

theorem isBotTopExpr_antitone {σ₁ σ₂ : Sig} (hsub : σ₁.Subset σ₂) (c : ClassExpr) :
    (isBotExpr σ₂ c = true → isBotExpr σ₁ c = true) ∧
    (isTopExpr σ₂ c = true → isTopExpr σ₁ c = true) := by
  induction c with
  | named cn =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h ⊢
      rcases h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h2, ?_⟩
        cases hc : σ₁.hasCls cn
        · rfl
        · exact absurd (hsub.1 _ hc) (by simp [h3])
    · intro h; exact h
  | complement a ih =>
    exact ⟨ih.2, ih.1⟩
  | intersection a b iha ihb =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.or_eq_true] at h ⊢
      exact h.elim (Or.inl ∘ iha.1) (Or.inr ∘ ihb.1)
    · intro h
      simp only [isTopExpr, Bool.and_eq_true] at h ⊢
      exact ⟨iha.2 h.1, ihb.2 h.2⟩
  | union a b iha ihb =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.and_eq_true] at h ⊢
      exact ⟨iha.1 h.1, ihb.1 h.2⟩
    · intro h
      simp only [isTopExpr, Bool.or_eq_true] at h ⊢
      exact h.elim (Or.inl ∘ iha.2) (Or.inr ∘ ihb.2)
  | oneOf _ => exact ⟨id, id⟩
  | objectSome r a ih =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.or_eq_true] at h ⊢
      exact h.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ ih.1)
    · intro h; exact h
  | objectAll r a ih =>
    constructor
    · intro h; exact h
    · intro h
      simp only [isTopExpr, Bool.or_eq_true] at h ⊢
      exact h.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ ih.2)
  | objectValue r _ => exact ⟨isBotObjProp_antitone hsub, id⟩
  | objectSelf r => exact ⟨isBotObjProp_antitone hsub, id⟩
  | objectMin n r a ih =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨h.1, h.2.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ ih.1)⟩
    · intro h; exact h
  | objectMax n r a ih =>
    constructor
    · intro h; exact h
    · intro h
      simp only [isTopExpr, Bool.or_eq_true] at h ⊢
      exact h.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ ih.1)
  | objectExact n r a ih =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨h.1, h.2.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ ih.1)⟩
    · intro h; exact h
  | dataSome p _ => exact ⟨isBotDataProp_antitone hsub, id⟩
  | dataAll p _ => exact ⟨id, isBotDataProp_antitone hsub⟩
  | dataValue p _ => exact ⟨isBotDataProp_antitone hsub, id⟩
  | dataMin n p _ =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, isBotDataProp_antitone hsub h.2⟩
    · intro h; exact h
  | dataMax n p _ => exact ⟨id, isBotDataProp_antitone hsub⟩
  | dataExact n p _ =>
    constructor
    · intro h
      simp only [isBotExpr, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, isBotDataProp_antitone hsub h.2⟩
    · intro h; exact h

private theorem atMostOne_antitone {α : Type} {p q : α → Bool} {xs : List α}
    (hpq : ∀ x, p x = true → q x = true) (h : atMostOne q xs = true) :
    atMostOne p xs = true := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    simp only [atMostOne] at h ⊢
    cases hqx : q x
    · simp only [hqx, Bool.false_eq_true, ↓reduceIte] at h
      have hpx : p x = false := by
        cases hp : p x
        · rfl
        · exact absurd (hpq x hp) (by simp [hqx])
      simp only [hpx, Bool.false_eq_true, ↓reduceIte]
      exact ih h
    · simp only [hqx, ↓reduceIte, List.all_eq_true, Bool.not_eq_true'] at h
      have htail : ∀ y ∈ tail, p y = false := fun y hy => by
        cases hp : p y
        · rfl
        · exact absurd (hpq y hp) (by simp [h y hy])
      cases hpx : p x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        clear h hqx hpx ih
        induction tail with
        | nil => rfl
        | cons z rest ihr =>
          simp only [atMostOne, htail z (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
          exact ihr (fun y hy => htail y (List.mem_cons_of_mem _ hy))
      · simp only [↓reduceIte, List.all_eq_true, Bool.not_eq_true']
        exact htail

/-- Syntactic ⊥-locality is anti-monotone with respect to signature inclusion:
    shrinking `σ` can only preserve ⊥-locality. -/
theorem isBotLocalAxiom_antitone {σ₁ σ₂ : Sig} (hsub : σ₁.Subset σ₂) {a : Axiom}
    (h : isBotLocalAxiom σ₂ a = true) : isBotLocalAxiom σ₁ a = true := by
  cases a with
  | subClassOf c1 c2 =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h ⊢
    exact h.elim (Or.inl ∘ (isBotTopExpr_antitone hsub c1).1) (Or.inr ∘ (isBotTopExpr_antitone hsub c2).2)
  | equivalentClasses cs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true] at h ⊢
    exact h.elim (fun hb => Or.inl fun c hc => (isBotTopExpr_antitone hsub c).1 (hb c hc))
      (fun ht => Or.inr fun c hc => (isBotTopExpr_antitone hsub c).2 (ht c hc))
  | disjointClasses cs =>
    refine atMostOne_antitone (fun c hc => ?_) h
    simp only [Bool.not_eq_true'] at hc ⊢
    cases hb : isBotExpr σ₂ c
    · rfl
    · exact absurd ((isBotTopExpr_antitone hsub c).1 hb) (by simp [hc])
  | disjointUnion hd cs =>
    simp only [isBotLocalAxiom, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨(isBotTopExpr_antitone hsub (.named hd)).1 h.1, fun c hc => (isBotTopExpr_antitone hsub c).1 (h.2 c hc)⟩
  | subObjectProperty r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h ⊢
    exact h.elim (Or.inl ∘ isBotObjProp_antitone hsub) Or.inr
  | subObjectPropertyChain rs s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
    exact h.elim (fun ⟨hne, r, hr, hbot⟩ => Or.inl ⟨hne, r, hr, isBotObjProp_antitone hsub hbot⟩) Or.inr
  | equivalentObjectProperties rs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true] at h ⊢
    exact h.elim (fun hb => Or.inl fun r hr => isBotObjProp_antitone hsub (hb r hr)) Or.inr
  | disjointObjectProperties rs =>
    refine atMostOne_antitone (fun r hr => ?_) h
    simp only [Bool.not_eq_true'] at hr ⊢
    cases hb : isBotObjProp σ₂ r
    · rfl
    · exact absurd (isBotObjProp_antitone hsub hb) (by simp [hr])
  | inverseObjectProperties r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.elim (fun ⟨h1, h2⟩ => Or.inl ⟨isBotObjProp_antitone hsub h1, isBotObjProp_antitone hsub h2⟩) Or.inr
  | objectPropertyDomain r c | objectPropertyRange r c =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h ⊢
    exact h.elim (Or.inl ∘ isBotObjProp_antitone hsub) (Or.inr ∘ (isBotTopExpr_antitone hsub c).2)
  | functionalObjectProperty r | inverseFunctionalObjectProperty r
  | irreflexiveObjectProperty r | symmetricObjectProperty r
  | asymmetricObjectProperty r | transitiveObjectProperty r =>
    exact isBotObjProp_antitone hsub h
  | reflexiveObjectProperty _ => exact h
  | subDataProperty r s =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h ⊢
    exact h.elim (Or.inl ∘ isBotDataProp_antitone hsub) Or.inr
  | equivalentDataProperties rs =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.all_eq_true] at h ⊢
    exact h.elim (fun hb => Or.inl fun p hp => isBotDataProp_antitone hsub (hb p hp)) Or.inr
  | disjointDataProperties rs =>
    refine atMostOne_antitone (fun p hp => ?_) h
    simp only [Bool.not_eq_true'] at hp ⊢
    cases hb : isBotDataProp σ₂ p
    · rfl
    · exact absurd (isBotDataProp_antitone hsub hb) (by simp [hp])
  | dataPropertyDomain r c =>
    simp only [isBotLocalAxiom, Bool.or_eq_true] at h ⊢
    exact h.elim (Or.inl ∘ isBotDataProp_antitone hsub) (Or.inr ∘ (isBotTopExpr_antitone hsub c).2)
  | dataPropertyRange r _ | functionalDataProperty r =>
    exact isBotDataProp_antitone hsub h
  | datatypeDefinition _ _ | sameIndividuals _ | differentIndividuals _ => exact h
  | hasKey c rs ds =>
    simp only [isBotLocalAxiom, Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with (hc | ⟨r, hr, hrb⟩) | ⟨p, hp, hpb⟩
    · exact Or.inl (Or.inl ((isBotTopExpr_antitone hsub c).1 hc))
    · exact Or.inl (Or.inr ⟨r, hr, isBotObjProp_antitone hsub hrb⟩)
    · exact Or.inr ⟨p, hp, isBotDataProp_antitone hsub hpb⟩
  | classAssertion c _ => exact (isBotTopExpr_antitone hsub c).2 h
  | objectAssertion _ _ _ | dataAssertion _ _ _ => exact h
  | negativeObjectAssertion r _ _ => exact isBotObjProp_antitone hsub h
  | negativeDataAssertion p _ _ => exact isBotDataProp_antitone hsub h

/-- Any `(M, σ)` that is closed under syntactic ⊥-locality and covers `seed`
    is a sound ⊥-local module (conservativity over arbitrary `DatatypeMap`). -/
structure ValidBotModule (o : Ontology) (seed : Sig) (M : Ontology) (σ : Sig) : Prop where
  subset : ∀ a ∈ M, a ∈ o
  seedSub : seed.Subset σ
  modSig : ∀ a ∈ M, (axiomSig a).Subset σ
  localRest : ∀ a ∈ o, a ∉ M → isBotLocalAxiom σ a = true

theorem ValidBotModule.models_ext {d : DatatypeMap} {o : Ontology} {seed : Sig} {M : Ontology} {σ : Sig}
    (hv : ValidBotModule o seed M σ) {i : Interpretation d} (hmod : models i M) :
    models (restrictToSig i σ) o := by
  obtain ⟨assign, hsat⟩ := hmod
  refine ⟨assign, fun a ha => ?_⟩
  rw [restrictToSig_withAnonymous]
  by_cases hin : a ∈ M
  · exact (restrictToSig_axiomHolds (i.withAnonymous assign) (hv.modSig a hin)).mpr (hsat a hin)
  · exact isBotLocalAxiom_sound (i.withAnonymous assign) σ (hv.localRest a ha hin)

theorem ValidBotModule.sat_iff {d : DatatypeMap} {o : Ontology} {seed : Sig} {M : Ontology} {σ : Sig}
    (hv : ValidBotModule o seed M σ) :
    Satisfiable d o ↔ Satisfiable d M := by
  constructor
  · rintro ⟨i, assign, hsat⟩
    exact ⟨i, assign, fun a ha => hsat a (hv.subset a ha)⟩
  · rintro ⟨i, hmod⟩
    exact ⟨restrictToSig i σ, hv.models_ext hmod⟩

theorem ValidBotModule.entails_iff {d : DatatypeMap} {o Q : Ontology} {seed : Sig} {M : Ontology} {σ : Sig}
    (hv : ValidBotModule o seed M σ) (hQ : ∀ q ∈ Q, (axiomSig q).Subset seed) :
    Entails d o Q ↔ Entails d M Q := by
  constructor
  · intro hent i hmod
    have hfull := hv.models_ext hmod
    obtain ⟨assign, hq⟩ := hent (restrictToSig i σ) hfull
    let assign' : String → String → i.Object := assign
    refine ⟨assign', fun q hqm => ?_⟩
    have hqsub := Sig.Subset.trans (hQ q hqm) hv.seedSub
    exact (restrictToSig_axiomHolds (i.withAnonymous assign') hqsub).mp (hq q hqm)
  · intro hent i ⟨assign, hsat⟩
    exact hent i ⟨assign, fun a ha => hsat a (hv.subset a ha)⟩

/-- `extractBotModule o seed` is a valid ⊥-local module. -/
theorem extractBotModule_valid (o : Ontology) (seed : Sig) :
    ValidBotModule o seed (extractBotModule o seed).1 (extractBotModule o seed).2 :=
  ⟨extractBotModule_subset o seed, extractBotModule_seed_subset o seed,
   extractBotModule_mod_sig o seed, extractBotModule_local o seed⟩

private theorem mem_foldl_addUnique_iff (xs ys : List IRI) (x : IRI) :
    x ∈ ys.foldl addUnique xs ↔ x ∈ xs ∨ x ∈ ys := by
  induction ys generalizing xs with
  | nil => simp
  | cons y tl ih =>
    simp only [List.foldl_cons, ih, mem_addUnique, List.mem_cons]
    exact ⟨fun h => h.elim (fun h1 => h1.elim (fun e => Or.inr (Or.inl e)) Or.inl) (fun h2 => Or.inr (Or.inr h2)),
           fun h => h.elim (fun h1 => Or.inl (Or.inr h1)) (fun h2 => h2.elim (fun e => Or.inl (Or.inl e)) Or.inr)⟩

private theorem sig_subset_union_of {a b c : Sig} (ha : a.Subset c) (hb : b.Subset c) :
    (a.union b).Subset c := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Sig.hasCls, Sig.union, List.contains_iff_mem, mem_foldl_addUnique_iff] at hx
    exact hx.elim (fun h1 => ha.1 x (List.contains_iff_mem.mpr h1))
      (fun h2 => hb.1 x (List.contains_iff_mem.mpr h2))
  · intro x hx
    simp only [Sig.hasObj, Sig.union, List.contains_iff_mem, mem_foldl_addUnique_iff] at hx
    exact hx.elim (fun h1 => ha.2.1 x (List.contains_iff_mem.mpr h1))
      (fun h2 => hb.2.1 x (List.contains_iff_mem.mpr h2))
  · intro x hx
    simp only [Sig.hasData, Sig.union, List.contains_iff_mem, mem_foldl_addUnique_iff] at hx
    exact hx.elim (fun h1 => ha.2.2 x (List.contains_iff_mem.mpr h1))
      (fun h2 => hb.2.2 x (List.contains_iff_mem.mpr h2))

/-! ### 2. HashSet-Backed `FastSig` and Exact Agreement with `Sig` -/

structure FastSig where
  cls : Std.HashSet IRI := {}
  obj : Std.HashSet IRI := {}
  data : Std.HashSet IRI := {}

namespace FastSig

def empty : FastSig := {}

def hasCls (fs : FastSig) (c : IRI) : Bool := fs.cls.contains c
def hasObj (fs : FastSig) (r : IRI) : Bool := fs.obj.contains r
def hasData (fs : FastSig) (p : IRI) : Bool := fs.data.contains p

def addCls (fs : FastSig) (c : IRI) : FastSig :=
  if c == thing || c == nothing then fs else { fs with cls := fs.cls.insert c }

def addObj (fs : FastSig) (r : IRI) : FastSig :=
  if r == topObjectProperty || r == bottomObjectProperty then fs else { fs with obj := fs.obj.insert r }

def addData (fs : FastSig) (p : IRI) : FastSig :=
  if p == topDataProperty || p == bottomDataProperty then fs else { fs with data := fs.data.insert p }

def ofSig (σ : Sig) : FastSig :=
  let c := σ.cls.foldl (fun s x => s.insert x) {}
  let o := σ.obj.foldl (fun s x => s.insert x) {}
  let d := σ.data.foldl (fun s x => s.insert x) {}
  ⟨c, o, d⟩

def toSig (fs : FastSig) : Sig :=
  ⟨fs.cls.toList, fs.obj.toList, fs.data.toList⟩

def insertSig (fs : FastSig) (σ : Sig) : FastSig :=
  let c := σ.cls.foldl (fun s x => s.insert x) fs.cls
  let o := σ.obj.foldl (fun s x => s.insert x) fs.obj
  let d := σ.data.foldl (fun s x => s.insert x) fs.data
  ⟨c, o, d⟩

def coversSig (fs : FastSig) (σ : Sig) : Bool :=
  σ.cls.all (fs.hasCls ·) && σ.obj.all (fs.hasObj ·) && σ.data.all (fs.hasData ·)

private theorem hashSet_contains_eq_toList (m : Std.HashSet IRI) (x : IRI) :
    m.contains x = m.toList.contains x := by
  apply Bool.eq_iff_iff.mpr
  rw [Std.HashSet.contains_iff_mem, List.contains_iff_mem, Std.HashSet.mem_toList]

theorem hasCls_eq (fs : FastSig) (c : IRI) : fs.hasCls c = fs.toSig.hasCls c :=
  hashSet_contains_eq_toList fs.cls c

theorem hasObj_eq (fs : FastSig) (r : IRI) : fs.hasObj r = fs.toSig.hasObj r :=
  hashSet_contains_eq_toList fs.obj r

theorem hasData_eq (fs : FastSig) (p : IRI) : fs.hasData p = fs.toSig.hasData p :=
  hashSet_contains_eq_toList fs.data p

theorem coversSig_iff (fs : FastSig) (σ : Sig) :
    fs.coversSig σ = true ↔ σ.Subset fs.toSig := by
  simp only [coversSig, Bool.and_eq_true, List.all_eq_true, hasCls_eq, hasObj_eq, hasData_eq,
    Sig.Subset, Sig.hasCls, Sig.hasObj, Sig.hasData, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨hc, ho⟩, hd⟩
    exact ⟨fun x hx => hc x hx, fun x hx => ho x hx, fun x hx => hd x hx⟩
  · rintro ⟨hc, ho, hd⟩
    exact ⟨⟨fun x hx => hc x hx, fun x hx => ho x hx⟩, fun x hx => hd x hx⟩

private theorem mem_foldl_insert (xs : List IRI) (m : Std.HashSet IRI) (x : IRI) :
    x ∈ xs.foldl (fun s y => s.insert y) m ↔ x ∈ m ∨ x ∈ xs := by
  induction xs generalizing m with
  | nil => simp
  | cons y tl ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
    exact ⟨fun h => h.elim (fun h1 => h1.elim (fun e => Or.inr (Or.inl e.symm)) Or.inl) (fun h2 => Or.inr (Or.inr h2)),
           fun h => h.elim (fun h1 => Or.inl (Or.inr h1)) (fun h2 => h2.elim (fun e => Or.inl (Or.inl e.symm)) Or.inr)⟩

theorem insertSig_subset_of {fs : FastSig} {σ tgt : Sig}
    (h1 : fs.toSig.Subset tgt) (h2 : σ.Subset tgt) :
    (fs.insertSig σ).toSig.Subset tgt := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [toSig, insertSig, Sig.hasCls, List.contains_iff_mem, Std.HashSet.mem_toList,
      mem_foldl_insert] at hx
    exact hx.elim
      (fun hm => h1.1 x (by simp [toSig, Sig.hasCls, Std.HashSet.mem_toList, hm]))
      (fun hl => h2.1 x (List.contains_iff_mem.mpr hl))
  · intro x hx
    simp only [toSig, insertSig, Sig.hasObj, List.contains_iff_mem, Std.HashSet.mem_toList,
      mem_foldl_insert] at hx
    exact hx.elim
      (fun hm => h1.2.1 x (by simp [toSig, Sig.hasObj, Std.HashSet.mem_toList, hm]))
      (fun hl => h2.2.1 x (List.contains_iff_mem.mpr hl))
  · intro x hx
    simp only [toSig, insertSig, Sig.hasData, List.contains_iff_mem, Std.HashSet.mem_toList,
      mem_foldl_insert] at hx
    exact hx.elim
      (fun hm => h1.2.2 x (by simp [toSig, Sig.hasData, Std.HashSet.mem_toList, hm]))
      (fun hl => h2.2.2 x (List.contains_iff_mem.mpr hl))

theorem ofSig_subset (σ : Sig) : (ofSig σ).toSig.Subset σ := by
  have hempty : FastSig.empty.toSig.Subset σ := by
    refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;>
      simp [FastSig.empty, toSig, Sig.hasCls, Sig.hasObj, Sig.hasData] at hx
  exact insertSig_subset_of hempty (Sig.Subset.refl σ)

end FastSig

/-! ### 3. O(1)-Per-Symbol Syntactic ⊥-Locality Check on `FastSig` -/

def isBotObjPropFast (fs : FastSig) (r : ObjectProperty) : Bool :=
  let iri := objPropIRI r
  iri == bottomObjectProperty || (iri != topObjectProperty && !fs.hasObj iri)

def isBotDataPropFast (fs : FastSig) (p : IRI) : Bool :=
  p == bottomDataProperty || (p != topDataProperty && !fs.hasData p)

mutual
  def isBotExprFast (fs : FastSig) : ClassExpr → Bool
    | .named c => c == nothing || (c != thing && !fs.hasCls c)
    | .complement c => isTopExprFast fs c
    | .intersection a b => isBotExprFast fs a || isBotExprFast fs b
    | .union a b => isBotExprFast fs a && isBotExprFast fs b
    | .oneOf inds => inds.isEmpty
    | .objectSome r c => isBotObjPropFast fs r || isBotExprFast fs c
    | .objectAll _ _ => false
    | .objectValue r _ => isBotObjPropFast fs r
    | .objectSelf r => isBotObjPropFast fs r
    | .objectMin n r c => decide (n > 0) && (isBotObjPropFast fs r || isBotExprFast fs c)
    | .objectMax _ _ _ => false
    | .objectExact n r c => decide (n > 0) && (isBotObjPropFast fs r || isBotExprFast fs c)
    | .dataSome p _ => isBotDataPropFast fs p
    | .dataAll _ _ => false
    | .dataValue p _ => isBotDataPropFast fs p
    | .dataMin n p _ => decide (n > 0) && isBotDataPropFast fs p
    | .dataMax _ _ _ => false
    | .dataExact n p _ => decide (n > 0) && isBotDataPropFast fs p

  def isTopExprFast (fs : FastSig) : ClassExpr → Bool
    | .named c => c == thing
    | .complement c => isBotExprFast fs c
    | .intersection a b => isTopExprFast fs a && isTopExprFast fs b
    | .union a b => isTopExprFast fs a || isTopExprFast fs b
    | .oneOf _ => false
    | .objectSome _ _ => false
    | .objectAll r c => isBotObjPropFast fs r || isTopExprFast fs c
    | .objectValue _ _ => false
    | .objectSelf _ => false
    | .objectMin n _ _ => n == 0
    | .objectMax _ r c => isBotObjPropFast fs r || isBotExprFast fs c
    | .objectExact _ _ _ => false
    | .dataSome _ _ => false
    | .dataAll p _ => isBotDataPropFast fs p
    | .dataValue _ _ => false
    | .dataMin n _ _ => n == 0
    | .dataMax _ p _ => isBotDataPropFast fs p
    | .dataExact _ _ _ => false
end

def isBotLocalAxiomFast (fs : FastSig) : Axiom → Bool
  | .subClassOf a b => isBotExprFast fs a || isTopExprFast fs b
  | .equivalentClasses cs => cs.all (isBotExprFast fs) || cs.all (isTopExprFast fs)
  | .disjointClasses cs => atMostOne (fun c => !isBotExprFast fs c) cs
  | .disjointUnion h cs => isBotExprFast fs (.named h) && cs.all (isBotExprFast fs)
  | .subObjectProperty r s => isBotObjPropFast fs r || isTopObjProp s
  | .subObjectPropertyChain rs s => (!rs.isEmpty && rs.any (isBotObjPropFast fs)) || isTopObjProp s
  | .equivalentObjectProperties rs => rs.all (isBotObjPropFast fs) || rs.all isTopObjProp
  | .disjointObjectProperties rs => atMostOne (fun r => !isBotObjPropFast fs r) rs
  | .inverseObjectProperties r s => (isBotObjPropFast fs r && isBotObjPropFast fs s) || (isTopObjProp r && isTopObjProp s)
  | .objectPropertyDomain r c => isBotObjPropFast fs r || isTopExprFast fs c
  | .objectPropertyRange r c => isBotObjPropFast fs r || isTopExprFast fs c
  | .functionalObjectProperty r => isBotObjPropFast fs r
  | .inverseFunctionalObjectProperty r => isBotObjPropFast fs r
  | .reflexiveObjectProperty r => isTopObjProp r
  | .irreflexiveObjectProperty r => isBotObjPropFast fs r
  | .symmetricObjectProperty r => isBotObjPropFast fs r
  | .asymmetricObjectProperty r => isBotObjPropFast fs r
  | .transitiveObjectProperty r => isBotObjPropFast fs r
  | .subDataProperty r s => isBotDataPropFast fs r || s == topDataProperty
  | .equivalentDataProperties rs => rs.all (isBotDataPropFast fs) || rs.all (fun p => p == topDataProperty)
  | .disjointDataProperties rs => atMostOne (fun p => !isBotDataPropFast fs p) rs
  | .dataPropertyDomain r c => isBotDataPropFast fs r || isTopExprFast fs c
  | .dataPropertyRange r _ => isBotDataPropFast fs r
  | .functionalDataProperty r => isBotDataPropFast fs r
  | .datatypeDefinition _ _ => false
  | .hasKey c rs ds => isBotExprFast fs c || rs.any (isBotObjPropFast fs) || ds.any (isBotDataPropFast fs)
  | .sameIndividuals _ => false
  | .differentIndividuals _ => false
  | .classAssertion c _ => isTopExprFast fs c
  | .objectAssertion r _ _ => isTopObjProp r
  | .negativeObjectAssertion r _ _ => isBotObjPropFast fs r
  | .dataAssertion p _ _ => p == topDataProperty
  | .negativeDataAssertion p _ _ => isBotDataPropFast fs p

private theorem isBotObjPropFast_eq (fs : FastSig) (r : ObjectProperty) :
    isBotObjPropFast fs r = isBotObjProp fs.toSig r := by
  simp [isBotObjPropFast, isBotObjProp, FastSig.hasObj_eq]

private theorem isBotDataPropFast_eq (fs : FastSig) (p : IRI) :
    isBotDataPropFast fs p = isBotDataProp fs.toSig p := by
  simp [isBotDataPropFast, isBotDataProp, FastSig.hasData_eq]

private theorem isBotTopExprFast_eq (fs : FastSig) (c : ClassExpr) :
    isBotExprFast fs c = isBotExpr fs.toSig c ∧ isTopExprFast fs c = isTopExpr fs.toSig c := by
  induction c with
  | named cn =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, FastSig.hasCls_eq]
  | complement a ih =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, ih.1, ih.2]
  | intersection a b iha ihb | union a b iha ihb =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, iha.1, iha.2, ihb.1, ihb.2]
  | oneOf _ => exact ⟨rfl, rfl⟩
  | objectSome r a ih | objectAll r a ih | objectMin _ r a ih | objectMax _ r a ih | objectExact _ r a ih =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, isBotObjPropFast_eq, ih.1, ih.2]
  | objectValue r _ | objectSelf r =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, isBotObjPropFast_eq]
  | dataSome p _ | dataAll p _ | dataValue p _ | dataMin _ p _ | dataMax _ p _ | dataExact _ p _ =>
    simp [isBotExprFast, isBotExpr, isTopExprFast, isTopExpr, isBotDataPropFast_eq]

private theorem list_all_congr {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) (xs : List α) :
    xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [h x, ih]

private theorem atMostOne_congr {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) (xs : List α) :
    atMostOne p xs = atMostOne q xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    have hall : tl.all (fun y => !p y) = tl.all (fun y => !q y) :=
      list_all_congr (fun y => congrArg (!·) (h y)) tl
    cases hp : p x <;> simp [atMostOne, ← h x, hp, hall, ih]

private theorem list_any_congr {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) (xs : List α) :
    xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [h x, ih]

/-- Exact extensional equality between hash-backed `isBotLocalAxiomFast` and
    specification `isBotLocalAxiom`. -/
theorem isBotLocalAxiomFast_eq (fs : FastSig) (a : Axiom) :
    isBotLocalAxiomFast fs a = isBotLocalAxiom fs.toSig a := by
  cases a with
  | subClassOf c1 c2 =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, (isBotTopExprFast_eq fs c1).1, (isBotTopExprFast_eq fs c2).2]
  | equivalentClasses cs =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom,
      list_all_congr (fun c => (isBotTopExprFast_eq fs c).1),
      list_all_congr (fun c => (isBotTopExprFast_eq fs c).2)]
  | disjointClasses cs =>
    exact atMostOne_congr (fun c => by rw [(isBotTopExprFast_eq fs c).1]) cs
  | disjointUnion hd cs =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom, (isBotTopExprFast_eq fs (.named hd)).1,
      list_all_congr (fun c => (isBotTopExprFast_eq fs c).1)]
  | subObjectProperty r s =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotObjPropFast_eq]
  | subObjectPropertyChain rs s =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom, list_any_congr (isBotObjPropFast_eq fs)]
  | equivalentObjectProperties rs =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom, list_all_congr (isBotObjPropFast_eq fs)]
  | disjointObjectProperties rs =>
    exact atMostOne_congr (fun r => by rw [isBotObjPropFast_eq]) rs
  | inverseObjectProperties r s =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotObjPropFast_eq]
  | objectPropertyDomain r c | objectPropertyRange r c =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotObjPropFast_eq, (isBotTopExprFast_eq fs c).2]
  | functionalObjectProperty r | inverseFunctionalObjectProperty r
  | reflexiveObjectProperty r | irreflexiveObjectProperty r
  | symmetricObjectProperty r | asymmetricObjectProperty r | transitiveObjectProperty r =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotObjPropFast_eq]
  | subDataProperty r s =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotDataPropFast_eq]
  | equivalentDataProperties rs =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom, list_all_congr (isBotDataPropFast_eq fs)]
  | disjointDataProperties rs =>
    exact atMostOne_congr (fun p => by rw [isBotDataPropFast_eq]) rs
  | dataPropertyDomain r c =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotDataPropFast_eq, (isBotTopExprFast_eq fs c).2]
  | dataPropertyRange r _ | functionalDataProperty r =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotDataPropFast_eq]
  | datatypeDefinition _ _ | sameIndividuals _ | differentIndividuals _ => rfl
  | hasKey c rs ds =>
    simp only [isBotLocalAxiomFast, isBotLocalAxiom, (isBotTopExprFast_eq fs c).1,
      list_any_congr (isBotObjPropFast_eq fs), list_any_congr (isBotDataPropFast_eq fs)]
  | classAssertion c _ =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, (isBotTopExprFast_eq fs c).2]
  | objectAssertion _ _ _ | dataAssertion _ _ _ => rfl
  | negativeObjectAssertion r _ _ =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotObjPropFast_eq]
  | negativeDataAssertion p _ _ =>
    simp [isBotLocalAxiomFast, isBotLocalAxiom, isBotDataPropFast_eq]

/-! ### 4. Inverted Symbol-to-Axiom Index & O(|O| + |M|) Worklist Extractor -/

/-- Pre-built inverted index over an ontology for O(|M|) repeated module extractions. -/
structure LocalityIndex where
  axioms : Array Axiom
  clsIdx : Std.HashMap IRI (Array Nat)
  objIdx : Std.HashMap IRI (Array Nat)
  dataIdx : Std.HashMap IRI (Array Nat)
  alwaysNonLocal : Array Nat

private def pushMap (m : Std.HashMap IRI (Array Nat)) (k : IRI) (v : Nat) :
    Std.HashMap IRI (Array Nat) :=
  m.alter k fun
    | some arr => some (arr.push v)
    | none => some #[v]

/-- Build an inverted signature index for `o` in a single O(|O|) linear pass. -/
def LocalityIndex.build (o : Ontology) : LocalityIndex := Id.run do
  let axioms := o.toArray
  let mut clsIdx : Std.HashMap IRI (Array Nat) := {}
  let mut objIdx : Std.HashMap IRI (Array Nat) := {}
  let mut dataIdx : Std.HashMap IRI (Array Nat) := {}
  let mut alwaysNonLocal : Array Nat := #[]
  for h : i in [:axioms.size] do
    let ax := axioms[i]
    if !isBotLocalAxiomFast FastSig.empty ax then
      alwaysNonLocal := alwaysNonLocal.push i
    let sig := axiomSig ax
    for c in sig.cls do
      clsIdx := pushMap clsIdx c i
    for r in sig.obj do
      objIdx := pushMap objIdx r i
    for p in sig.data do
      dataIdx := pushMap dataIdx p i
  return { axioms, clsIdx, objIdx, dataIdx, alwaysNonLocal }

/-- Extend an existing `LocalityIndex` with additional axioms appended to the end
    of the ontology in O(|extra|) time (used by persistent sessions with cached TBoxes). -/
def LocalityIndex.extend (idx : LocalityIndex) (extra : Ontology) : LocalityIndex := Id.run do
  let mut axioms := idx.axioms
  let mut clsIdx := idx.clsIdx
  let mut objIdx := idx.objIdx
  let mut dataIdx := idx.dataIdx
  let mut alwaysNonLocal := idx.alwaysNonLocal
  for ax in extra do
    let i := axioms.size
    axioms := axioms.push ax
    if !isBotLocalAxiomFast FastSig.empty ax then
      alwaysNonLocal := alwaysNonLocal.push i
    let sig := axiomSig ax
    for c in sig.cls do
      clsIdx := pushMap clsIdx c i
    for r in sig.obj do
      objIdx := pushMap objIdx r i
    for p in sig.data do
      dataIdx := pushMap dataIdx p i
  return { axioms, clsIdx, objIdx, dataIdx, alwaysNonLocal }

/-- Indexed worklist extraction returning `(pickedOrder, inModuleMask, finalFastSig)`. -/
def LocalityIndex.runWorklist (idx : LocalityIndex) (seed : Sig) :
    Array Nat × Array Bool × FastSig := Id.run do
  let n := idx.axioms.size
  let mut sig := FastSig.ofSig seed
  let mut inMod : Array Bool := Array.replicate n false
  let mut queued : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  let mut picked : Array Nat := #[]
  -- Seed queue with always-non-local axioms + axioms mentioning seed symbols
  for i in idx.alwaysNonLocal do
    if i < n && !queued[i]! then
      queued := queued.set! i true
      queue := queue.push i
  for c in seed.cls do
    if let some hits := idx.clsIdx.get? c then
      for i in hits do
        if i < n && !queued[i]! then
          queued := queued.set! i true
          queue := queue.push i
  for r in seed.obj do
    if let some hits := idx.objIdx.get? r then
      for i in hits do
        if i < n && !queued[i]! then
          queued := queued.set! i true
          queue := queue.push i
  for p in seed.data do
    if let some hits := idx.dataIdx.get? p then
      for i in hits do
        if i < n && !queued[i]! then
          queued := queued.set! i true
          queue := queue.push i
  -- Worklist fixpoint loop
  let mut head : Nat := 0
  while head < queue.size do
    let i := queue[head]!
    head := head + 1
    queued := queued.set! i false
    if inMod.getD i false then continue
    if hi : i < idx.axioms.size then
      let ax := idx.axioms[i]
      if !isBotLocalAxiomFast sig ax then
        inMod := inMod.set! i true
        picked := picked.push i
        let asig := axiomSig ax
        for c in asig.cls do
          if !sig.hasCls c then
            sig := { sig with cls := sig.cls.insert c }
            if let some hits := idx.clsIdx.get? c then
              for j in hits do
                if !inMod.getD j false && !queued.getD j false then
                  queued := queued.set! j true
                  queue := queue.push j
        for r in asig.obj do
          if !sig.hasObj r then
            sig := { sig with obj := sig.obj.insert r }
            if let some hits := idx.objIdx.get? r then
              for j in hits do
                if !inMod.getD j false && !queued.getD j false then
                  queued := queued.set! j true
                  queue := queue.push j
        for p in asig.data do
          if !sig.hasData p then
            sig := { sig with data := sig.data.insert p }
            if let some hits := idx.dataIdx.get? p then
              for j in hits do
                if !inMod.getD j false && !queued.getD j false then
                  queued := queued.set! j true
                  queue := queue.push j
  return (picked, inMod, sig)

/-! ### 5. Linear-Time O(|O|) Certificate Verifier & Exact Equivalence Proofs -/

/-- O(|O|) linear verifier checking every axiom `o[i]` against `(mark[i], fs)` in O(1) per symbol. -/
private def verifyMaskAux (mark : Array Bool) (fs : FastSig) :
    Nat → List Axiom → List Axiom → Option (List Axiom)
  | _, [], acc => some acc.reverse
  | i, a :: rest, acc =>
    if mark.getD i false then
      if fs.coversSig (axiomSig a) then
        verifyMaskAux mark fs (i + 1) rest (a :: acc)
      else none
    else
      if isBotLocalAxiomFast fs a then
        verifyMaskAux mark fs (i + 1) rest acc
      else none

private theorem verifyMaskAux_sound (mark : Array Bool) (fs : FastSig) :
    ∀ (i : Nat) (xs acc mod : List Axiom),
      verifyMaskAux mark fs i xs acc = some mod →
      (∀ a ∈ mod, a ∈ acc ∨ (∃ (k : Nat) (hk : k < xs.length), xs[k] = a ∧ mark.getD (i + k) false = true ∧ (axiomSig a).Subset fs.toSig)) ∧
      (∀ a ∈ acc, a ∈ mod) ∧
      (∀ a ∈ xs, a ∈ mod ∨ isBotLocalAxiom fs.toSig a = true) := by
  intro i xs
  induction xs generalizing i with
  | nil =>
    intro acc mod h
    simp only [verifyMaskAux, Option.some.injEq] at h
    subst h
    refine ⟨fun a ha => Or.inl (List.mem_reverse.mp ha),
      fun a ha => List.mem_reverse.mpr ha, fun _ ha => by cases ha⟩
  | cons a rest ih =>
    intro acc mod h
    simp only [verifyMaskAux] at h
    cases hmk : mark.getD i false
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i hloc
        rw [isBotLocalAxiomFast_eq] at hloc
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) acc mod h
        refine ⟨fun x hx => ?_, h2, fun x hx => ?_⟩
        · rcases h1 x hx with ha' | ⟨k, hk, heq, hmk', hxs⟩
          · exact Or.inl ha'
          · refine Or.inr ⟨k + 1, by simp; omega, by simpa using heq, ?_, hxs⟩
            have : i + (k + 1) = i + 1 + k := by omega
            simpa [this] using hmk'
        · rcases List.mem_cons.mp hx with rfl | hr
          · exact Or.inr hloc
          · exact h3 x hr
      · cases h
    · simp only [hmk, ↓reduceIte] at h
      split at h
      · rename_i hcov
        have hsub := (FastSig.coversSig_iff fs (axiomSig a)).mp hcov
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) (a :: acc) mod h
        refine ⟨fun x hx => ?_, fun x hx => h2 x (List.mem_cons_of_mem _ hx), fun x hx => ?_⟩
        · rcases h1 x hx with ha' | ⟨k, hk, heq, hmk', hxs⟩
          · rcases List.mem_cons.mp ha' with rfl | hacc
            · exact Or.inr ⟨0, by simp, rfl, by simpa using hmk, hsub⟩
            · exact Or.inl hacc
          · refine Or.inr ⟨k + 1, by simp; omega, by simpa using heq, ?_, hxs⟩
            have : i + (k + 1) = i + 1 + k := by omega
            simpa [this] using hmk'
        · rcases List.mem_cons.mp hx with rfl | hr
          · exact Or.inl (h2 x (List.mem_cons_self ..))
          · exact h3 x hr
      · cases h

/-- O(|M|) minimality replay: checks that every index in `order` is genuinely
    non-local under the signature accumulated from `seed`, building the certified
    boolean mask `mark'`. -/
private def verifyMinimalBuild (axioms : Array Axiom) :
    FastSig → List Nat → Array Bool → Option (Array Bool)
  | _, [], mark => some mark
  | fs, i :: rest, mark =>
    if h : i < axioms.size then
      let a := axioms[i]
      if !isBotLocalAxiomFast fs a then
        verifyMinimalBuild axioms (fs.insertSig (axiomSig a)) rest (mark.setIfInBounds i true)
      else none
    else none

private theorem array_getD_setIfInBounds {α : Type} (arr : Array α) (i j : Nat) (v d : α) :
    (arr.setIfInBounds i v).getD j d = if j = i ∧ i < arr.size then v else arr.getD j d := by
  by_cases hi : i < arr.size
  · simp only [Array.setIfInBounds, hi, ↓reduceDIte, Array.getD, Array.size_set, and_true]
    by_cases hj : j < arr.size
    · simp only [hj, ↓reduceDIte]
      by_cases heq : j = i
      · subst heq; simp
      · simp only [heq, ↓reduceIte]
        exact Array.getElem_set_ne hi hj (Ne.symm heq)
    · have hne : j ≠ i := fun h => hj (h ▸ hi)
      simp [hj, hne]
  · simp only [Array.setIfInBounds, hi, ↓reduceDIte, and_false, ↓reduceIte]

private theorem verifyMinimalBuild_sound {o M : Ontology} {seed σ : Sig}
    (hv : ValidBotModule o seed M σ) :
    ∀ (order : List Nat) (fs : FastSig) (mark mark' : Array Bool),
      fs.toSig.Subset σ →
      mark.size = o.toArray.size →
      (∀ j (hj : j < o.toArray.size), mark.getD j false = true → o.toArray[j] ∈ M) →
      verifyMinimalBuild o.toArray fs order mark = some mark' →
      ∀ j (hj : j < o.toArray.size), mark'.getD j false = true → o.toArray[j] ∈ M := by
  intro order
  induction order with
  | nil =>
    intro fs mark mark' _ _ hmk h
    simp only [verifyMinimalBuild, Option.some.injEq] at h
    subst h; exact hmk
  | cons i rest ih =>
    intro fs mark mark' hsub hsz hmk h
    simp only [verifyMinimalBuild] at h
    split at h; rotate_left; · cases h
    rename_i hi
    split at h; rotate_left; · cases h
    rename_i hnonloc
    simp only [Bool.not_eq_true', isBotLocalAxiomFast_eq] at hnonloc
    have hi_o : o.toArray[i] ∈ o := by
      have hi' : i < o.length := by simpa using hi
      simp [List.getElem_mem hi']
    have hi_M : o.toArray[i] ∈ M := by
      by_cases hin : o.toArray[i] ∈ M
      · exact hin
      · have hloc := isBotLocalAxiom_antitone hsub (hv.localRest _ hi_o hin)
        rw [hnonloc] at hloc; cases hloc
    have hsub' : (fs.insertSig (axiomSig o.toArray[i])).toSig.Subset σ :=
      FastSig.insertSig_subset_of hsub (hv.modSig _ hi_M)
    have hsz' : (mark.setIfInBounds i true).size = o.toArray.size := by
      simp [Array.size_setIfInBounds, hsz]
    have hmk' : ∀ j (hj : j < o.toArray.size),
        (mark.setIfInBounds i true).getD j false = true → o.toArray[j] ∈ M := by
      intro j hj hget
      rw [array_getD_setIfInBounds] at hget
      by_cases hji : j = i ∧ i < mark.size
      · obtain ⟨rfl, _⟩ := hji; exact hi_M
      · simp only [hji, ↓reduceIte] at hget
        exact hmk j hj hget
    exact ih _ _ mark' hsub' hsz' hmk' h

/-- Certified O(|O| + |M|) hash-indexed ⊥-locality module extractor using a pre-built
    (or untrusted cached) inverted index `idx`. Runs the hash-indexed worklist,
    certifies minimality (O(|M|)) and locality (O(|O|)) with O(1) hash lookups,
    and falls back to `extractBotModule` only if certification fails. -/
def extractBotModuleWithIndex (idx : LocalityIndex) (o : Ontology) (seed : Sig) : Ontology × Sig :=
  let (picked, _, fs) := idx.runWorklist seed
  if fs.coversSig seed then
    let axioms := o.toArray
    match verifyMinimalBuild axioms (FastSig.ofSig seed) picked.toList (Array.replicate axioms.size false) with
    | some mark =>
      match verifyMaskAux mark fs 0 o [] with
      | some mod => (mod, fs.toSig)
      | none => extractBotModule o seed
    | none => extractBotModule o seed
  else
    extractBotModule o seed

/-- Certified O(|O| + |M|) hash-indexed ⊥-locality module extractor.
    Builds an inverted signature index in a single O(|O|) pass and runs
    `extractBotModuleWithIndex`. -/
def extractBotModuleFast (o : Ontology) (seed : Sig) : Ontology × Sig :=
  extractBotModuleWithIndex (LocalityIndex.build o) o seed

/-- `extractBotModuleWithIndex` always produces a kernel-certified `ValidBotModule`,
    regardless of how `idx` was constructed. -/
theorem extractBotModuleWithIndex_valid (idx : LocalityIndex) (o : Ontology) (seed : Sig) :
    ValidBotModule o seed (extractBotModuleWithIndex idx o seed).1 (extractBotModuleWithIndex idx o seed).2 := by
  unfold extractBotModuleWithIndex
  dsimp only
  split
  · rename_i hseed
    split
    · rename_i mark _
      split
      · rename_i mod hmask
        obtain ⟨h1, _, h3⟩ := verifyMaskAux_sound mark _ 0 o [] mod hmask
        refine ⟨fun a ha => ?_, (FastSig.coversSig_iff _ seed).mp hseed,
          fun a ha => ?_, fun a ha hnot => (h3 a ha).elim (fun hin => absurd hin hnot) id⟩
        · rcases h1 a ha with h | ⟨k, hk, rfl, _, _⟩
          · cases h
          · exact List.getElem_mem hk
        · rcases h1 a ha with h | ⟨_, _, _, _, hsub⟩
          · cases h
          · exact hsub
      · exact extractBotModule_valid o seed
    · exact extractBotModule_valid o seed
  · exact extractBotModule_valid o seed

/-- `extractBotModuleFast` always produces a kernel-certified `ValidBotModule`. -/
theorem extractBotModuleFast_valid (o : Ontology) (seed : Sig) :
    ValidBotModule o seed (extractBotModuleFast o seed).1 (extractBotModuleFast o seed).2 :=
  extractBotModuleWithIndex_valid (LocalityIndex.build o) o seed

/-- Kernel-checked satisfiability preservation for `extractBotModuleWithIndex`. -/
theorem extractBotModuleWithIndex_sat_iff {d : DatatypeMap} (idx : LocalityIndex) (o : Ontology) (seed : Sig) :
    Satisfiable d o ↔ Satisfiable d (extractBotModuleWithIndex idx o seed).1 :=
  (extractBotModuleWithIndex_valid idx o seed).sat_iff

/-- Kernel-checked entailment conservativity for `extractBotModuleWithIndex`. -/
theorem extractBotModuleWithIndex_entails_iff {d : DatatypeMap} (idx : LocalityIndex) (o Q : Ontology) (seed : Sig)
    (hQ : ∀ q ∈ Q, (axiomSig q).Subset seed) :
    Entails d o Q ↔ Entails d (extractBotModuleWithIndex idx o seed).1 Q :=
  (extractBotModuleWithIndex_valid idx o seed).entails_iff hQ

/-- Kernel-checked satisfiability preservation for `extractBotModuleFast`. -/
theorem extractBotModuleFast_sat_iff {d : DatatypeMap} (o : Ontology) (seed : Sig) :
    Satisfiable d o ↔ Satisfiable d (extractBotModuleFast o seed).1 :=
  (extractBotModuleFast_valid o seed).sat_iff

/-- Kernel-checked entailment conservativity for `extractBotModuleFast`:
    for any query ontology `Q` covered by `seed`, `o ⊨ Q` iff the fast hash-indexed
    ⊥-local module entails `Q`. -/
theorem extractBotModuleFast_entails_iff {d : DatatypeMap} (o Q : Ontology) (seed : Sig)
    (hQ : ∀ q ∈ Q, (axiomSig q).Subset seed) :
    Entails d o Q ↔ Entails d (extractBotModuleFast o seed).1 Q :=
  (extractBotModuleFast_valid o seed).entails_iff hQ

/-! ### 6. Minimality & Exact Set-Equality with `extractBotModule` -/

private theorem extractStep_least {o M : Ontology} {seed σ : Sig}
    (hv : ValidBotModule o seed M σ) (rem : Ontology) (s : Sig)
    (hrem : ∀ a ∈ rem, a ∈ o) (hs : s.Subset σ) :
    (∀ a ∈ (extractStep rem s).1, a ∈ M) ∧ (extractStep rem s).2.2.Subset σ := by
  have go : ∀ (xs ad kp : Ontology) (st : Sig),
      (∀ a ∈ xs, a ∈ o) → (∀ a ∈ ad, a ∈ M) → st.Subset σ →
      let res := xs.foldl (fun (ad, kp, st) a =>
        if isBotLocalAxiom st a then (ad, a :: kp, st)
        else (a :: ad, kp, st.union (axiomSig a))) (ad, kp, st)
      (∀ a ∈ res.1, a ∈ M) ∧ res.2.2.Subset σ := by
    intro xs
    induction xs with
    | nil => intro ad kp st _ had hst; exact ⟨had, hst⟩
    | cons a tl ih =>
      intro ad kp st hxs had hst
      simp only [List.foldl_cons]
      by_cases hloc : isBotLocalAxiom st a = true
      · simp only [hloc, ↓reduceIte]
        exact ih ad (a :: kp) st (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) had hst
      · simp only [hloc, Bool.false_eq_true, ↓reduceIte]
        have haM : a ∈ M := by
          by_cases hin : a ∈ M
          · exact hin
          · exact absurd (isBotLocalAxiom_antitone hst (hv.localRest a (hxs a (List.mem_cons_self ..)) hin)) hloc
        exact ih (a :: ad) kp (st.union (axiomSig a))
          (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
          (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ haM) (had x))
          (sig_subset_union_of hst (hv.modSig a haM))
  exact go rem [] [] s hrem (fun _ h => by cases h) hs

private theorem extractLoop_least {o M : Ontology} {seed σ : Sig}
    (hv : ValidBotModule o seed M σ) (picked rem : Ontology) (s : Sig)
    (hpick : ∀ a ∈ picked, a ∈ M) (hrem : ∀ a ∈ rem, a ∈ o) (hs : s.Subset σ) :
    (∀ a ∈ (extractLoop picked rem s).1, a ∈ M) ∧ (extractLoop picked rem s).2.Subset σ := by
  unfold extractLoop
  dsimp only
  split
  · exact ⟨fun a ha => hpick a (List.mem_reverse.mp ha), hs⟩
  · rename_i hne
    have hprops := extractStep_props rem s
    have hlt : (extractStep rem s).2.1.length < rem.length := by
      have hlen := hprops.1
      cases h1 : (extractStep rem s).1 with
      | nil => simp [h1] at hne
      | cons _ _ => rw [h1] at hlen; simp at hlen; omega
    obtain ⟨hadM, hs'⟩ := extractStep_least hv rem s hrem hs
    exact extractLoop_least hv ((extractStep rem s).1 ++ picked) (extractStep rem s).2.1 (extractStep rem s).2.2
      (fun a ha => (List.mem_append.mp ha).elim (hadM a) (hpick a))
      (fun a ha => hrem a (hprops.2.2.2.1 a ha)) hs'
termination_by rem.length

/-- Least-fixed-point minimality of `extractBotModule`: any valid ⊥-local module `(M, σ)`
    for `(o, seed)` must contain every axiom extracted by `extractBotModule o seed`. -/
theorem extractBotModule_least {o : Ontology} {seed : Sig} {M : Ontology} {σ : Sig}
    (hv : ValidBotModule o seed M σ) :
    (∀ a ∈ (extractBotModule o seed).1, a ∈ M) ∧
    (extractBotModule o seed).2.Subset σ :=
  extractLoop_least hv [] o seed (fun _ h => by cases h) (fun _ h => h) hv.seedSub

/-- Kernel-checked exact module equality: `extractBotModuleWithIndex idx o seed`
    extracts the exact same set of axioms as `extractBotModule o seed`. -/
theorem extractBotModuleWithIndex_mem_iff (idx : LocalityIndex) (o : Ontology) (seed : Sig) (a : Axiom) :
    a ∈ (extractBotModuleWithIndex idx o seed).1 ↔ a ∈ (extractBotModule o seed).1 := by
  constructor
  · intro ha
    unfold extractBotModuleWithIndex at ha
    dsimp only at ha
    split at ha
    · split at ha
      · rename_i mark hmin
        split at ha
        · rename_i mod hmask
          obtain ⟨h1, _, _⟩ := verifyMaskAux_sound mark _ 0 o [] mod hmask
          rcases h1 a ha with h | ⟨k, hk, rfl, hmk, _⟩
          · cases h
          · have hspec := extractBotModule_valid o seed
            have h0 : ∀ j (hj : j < o.toArray.size),
                (Array.replicate o.toArray.size false).getD j false = true →
                o.toArray[j] ∈ (extractBotModule o seed).1 := by
              intro j _ hget
              simp [Array.getD] at hget
            have hmarkM := verifyMinimalBuild_sound hspec _ (FastSig.ofSig seed)
              (Array.replicate o.toArray.size false) mark
              (Sig.Subset.trans (FastSig.ofSig_subset seed) hspec.seedSub)
              (by simp) h0 hmin
            have hk_arr : k < o.toArray.size := by simpa using hk
            have hget : mark.getD k false = true := by simpa using hmk
            have hmem := hmarkM k hk_arr hget
            simpa using hmem
        · exact ha
      · exact ha
    · exact ha
  · intro ha
    exact (extractBotModule_least (extractBotModuleWithIndex_valid idx o seed)).1 a ha

/-- Kernel-checked exact module equality: `extractBotModuleFast o seed` extracts
    the exact same set of axioms as the quadratic specification `extractBotModule o seed`. -/
theorem extractBotModuleFast_mem_iff (o : Ontology) (seed : Sig) (a : Axiom) :
    a ∈ (extractBotModuleFast o seed).1 ↔ a ∈ (extractBotModule o seed).1 :=
  extractBotModuleWithIndex_mem_iff (LocalityIndex.build o) o seed a

/-- Fast O(|O| + |M|) drop-in replacement for `Profile.profileQuery` backed by
    `extractBotModuleWithIndex`. -/
def profileQueryWithIndex (idx : LocalityIndex) (o : Ontology) (q : Option Axiom) : QueryProfile :=
  let fullFp := profileOntology o
  let (mod, modFp) := match q with
    | none => (o, fullFp)
    | some qa =>
      let m := (extractBotModuleWithIndex idx o (axiomSig qa)).1
      (m, (profileOntology m).merge (profileAxiom qa))
  { fullAxiomCount := o.length
    moduleAxiomCount := mod.length
    fullFeatures := fullFp
    moduleFeatures := modFp
    fullFragment := fullFp.leastFragment
    moduleFragment := modFp.leastFragment
    extractedModule := mod }

/-- Fast O(|O| + |M|) drop-in replacement for `Profile.profileQuery` backed by
    `extractBotModuleFast` (exact module equality proved by `extractBotModuleFast_mem_iff`). -/
def profileQueryFast (o : Ontology) (q : Option Axiom) : QueryProfile :=
  let fullFp := profileOntology o
  let (mod, modFp) := match q with
    | none => (o, fullFp)
    | some qa =>
      let m := (extractBotModuleFast o (axiomSig qa)).1
      (m, (profileOntology m).merge (profileAxiom qa))
  { fullAxiomCount := o.length
    moduleAxiomCount := mod.length
    fullFeatures := fullFp
    moduleFeatures := modFp
    fullFragment := fullFp.leastFragment
    moduleFragment := modFp.leastFragment
    extractedModule := mod }

end Sabrina.OWL2.FastLocality
