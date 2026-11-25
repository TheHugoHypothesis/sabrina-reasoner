import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQABoxSemantics

/-!
A finite model decision procedure for reference SRIQ knowledge bases whose
concept clauses are universal after accounting for polarity. Role inclusions
and role assertions are checked directly and may use arbitrary finite chains.
-/

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

/-- At positive polarity, universals are preserved on a restricted domain.
At negative polarity, the complement of an existential is preserved. -/
def Concept.isUniversal (positive : Bool) : Concept → Bool
  | .atom _ | .top | .bottom | .self _ => true
  | .neg c => c.isUniversal !positive
  | .conj c d | .disj c d => c.isUniversal positive && d.isUniversal positive
  | .some _ c => !positive && c.isUniversal false
  | .all _ c => positive && c.isUniversal true
  | .min .. | .max .. => false

def ABoxAssertion.isUniversal : ABoxAssertion → Bool
  | .concept c _ => c.isUniversal true
  | _ => true

def KnowledgeBase.isUniversal (kb : KnowledgeBase) : Bool :=
  kb.tboxRBox.tbox.all (fun (a, b) => a.isUniversal false && b.isUniversal true) &&
  kb.abox.all ABoxAssertion.isUniversal

private def Model.pullback (m : Model) {α : Type} [Nonempty α] (f : α → m.Object) : Model where
  Object := α
  nonempty := inferInstance
  classes := fun c x => m.classes c (f x)
  relations := fun r x y => m.relations r (f x) (f y)

private theorem pullback_edge (m : Model) {α : Type} [Nonempty α]
    (f : α → m.Object) (r : Role) (x y : α) :
    (m.pullback f).edge r x y ↔ m.edge r (f x) (f y) := by
  cases r <;> rfl

private theorem pullback_path (m : Model) {α : Type} [Nonempty α]
    (f : α → m.Object) (rs : List Role) (x y : α) (h : (m.pullback f).path rs x y) :
    m.path rs (f x) (f y) := by
  induction rs generalizing x y with
  | nil =>
    obtain rfl := ((m.pullback f).path_nil_iff x y).mp h
    exact .nil _
  | cons r rs ih =>
    obtain ⟨z, he, hp⟩ := ((m.pullback f).path_cons_iff r rs x y).mp h
    exact .cons ((pullback_edge m f r x z).mp he) (ih z y hp)

private def atPolarity (positive : Bool) (p : Prop) : Prop :=
  if positive then p else ¬ p

private theorem pullback_holds (m : Model) {α : Type} [Nonempty α] (f : α → m.Object)
    (c : Concept) (positive : Bool) (h : c.isUniversal positive = true) (x : α) :
    atPolarity positive (m.holds (f x) c) → atPolarity positive ((m.pullback f).holds x c) := by
  induction c generalizing positive x with
  | atom | top | bottom => exact id
  | self r =>
    cases r <;> exact id
  | neg c ih =>
    cases positive
    · simpa [Concept.isUniversal, atPolarity, Model.holds] using ih true (by simpa [Concept.isUniversal] using h) x
    · exact ih false h x
  | conj c d ihc ihd =>
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp h
    cases positive
    · change (¬(m.holds (f x) c ∧ m.holds (f x) d)) → ¬_
      intro hn hp
      by_cases hmc : m.holds (f x) c
      · exact ihd false hd x (fun hmd => hn ⟨hmc, hmd⟩) hp.2
      · exact ihc false hc x hmc hp.1
    · exact fun ⟨ha, hb⟩ => ⟨ihc true hc x ha, ihd true hd x hb⟩
  | disj c d ihc ihd =>
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp h
    cases positive
    · intro hn hp
      exact hp.elim (ihc false hc x (hn ∘ Or.inl)) (ihd false hd x (hn ∘ Or.inr))
    · exact fun h => h.elim (Or.inl ∘ ihc true hc x) (Or.inr ∘ ihd true hd x)
  | some r c ih =>
    cases positive
    · have hc : c.isUniversal false = true := by simpa [Concept.isUniversal] using h
      intro hn
      rintro ⟨y, he, hy⟩
      exact ih false hc y (fun h => hn ⟨f y, (pullback_edge ..).mp he, h⟩) hy
    · contradiction
  | all r c ih =>
    cases positive
    · contradiction
    · have hc : c.isUniversal true = true := by simpa [Concept.isUniversal] using h
      exact fun hp y he => ih true hc y (hp (f y) ((pullback_edge ..).mp he))
  | min | max => contradiction

private theorem pullback_assertion (m : Model) {α : Type} [Nonempty α] (f : α → m.Object)
    (a : RoleAssertion) (h : m.holdsAssertion a) : (m.pullback f).holdsAssertion a := by
  cases a with
  | localReflexive r =>
    change ∀ x : α, (∃ y : α, (m.pullback f).edge r x y) → (m.pullback f).edge r x x
    rintro x ⟨y, hy⟩
    exact (pullback_edge m f r x x).mpr (h (f x) ⟨f y, (pullback_edge m f r x y).mp hy⟩)
  | irreflexive r =>
    change ∀ x : α, ¬ (m.pullback f).edge r x x
    exact fun x hx => h (f x) ((pullback_edge m f r x x).mp hx)
  | symmetric r =>
    change ∀ x y : α, (m.pullback f).edge r x y → (m.pullback f).edge r y x
    exact fun x y hxy => (pullback_edge m f r y x).mpr (h (f x) (f y) ((pullback_edge m f r x y).mp hxy))
  | transitive r =>
    change ∀ x y z : α, (m.pullback f).edge r x y → (m.pullback f).edge r y z → (m.pullback f).edge r x z
    exact fun x y z hxy hyz => (pullback_edge m f r x z).mpr
      (h (f x) (f y) (f z) ((pullback_edge m f r x y).mp hxy) ((pullback_edge m f r y z).mp hyz))
  | disjoint r s =>
    change ∀ x y : α, ¬ ((m.pullback f).edge r x y ∧ (m.pullback f).edge s x y)
    exact fun x y ⟨hr, hs⟩ =>
      h (f x) (f y) ⟨(pullback_edge m f r x y).mp hr, (pullback_edge m f s x y).mp hs⟩

private def ABoxAssertion.individualNames : ABoxAssertion → List String
  | .concept _ a => [a]
  | .role _ a b | .negRole _ a b | .same a b | .different a b => [a, b]

private def individualNames (kb : KnowledgeBase) : List String :=
  (kb.abox.flatMap ABoxAssertion.individualNames).eraseDups

private theorem names_mem {kb : KnowledgeBase} {a : ABoxAssertion} (ha : a ∈ kb.abox)
    {n : String} (hn : n ∈ a.individualNames) : n ∈ individualNames kb := by
  simp [individualNames, List.mem_flatMap]
  exact ⟨a, ha, hn⟩

private def longestName : List String → Nat
  | [] => 0
  | a :: as => max a.length (longestName as)

private theorem length_le_longestName {a : String} {names : List String} (h : a ∈ names) :
    a.length ≤ longestName names := by
  induction names with
  | nil => contradiction
  | cons b bs ih =>
    rcases List.mem_cons.mp h with he | hb
    · subst b
      exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hb) (Nat.le_max_right ..)

private def freshWitness (kb : KnowledgeBase) : String :=
  String.ofList (List.replicate (longestName (individualNames kb) + 1) 'x')

private theorem freshWitness_not_mem (kb : KnowledgeBase) :
    freshWitness kb ∉ individualNames kb := by
  intro h
  have hlen := length_le_longestName h
  simp [freshWitness] at hlen
  omega

/-- Add a fresh constant whose denotation witnesses failure of the inclusion.
The fresh constant may denote an object already named in the knowledge base. -/
def KnowledgeBase.withCounterexample (kb : KnowledgeBase) (a b : Concept) : KnowledgeBase :=
  { kb with abox := .concept (.conj a (.neg b)) (freshWitness kb) :: kb.abox }

private theorem holdsABox_congr (m : ABoxModel) (names : String → m.toModel.Object)
    (a : ABoxAssertion) (ha : ∀ n ∈ a.individualNames, names n = m.individuals n) :
    (ABoxModel.mk m.toModel names).holdsABox a ↔ m.holdsABox a := by
  cases a <;> simp_all [ABoxAssertion.individualNames, ABoxModel.holdsABox]

theorem KnowledgeBase.counterexample_sat_iff (kb : KnowledgeBase) (a b : Concept) :
    (kb.withCounterexample a b).Sat ↔
      ∃ m : ABoxModel, m.Models kb ∧
        ∃ x, m.toModel.holds x a ∧ ¬ m.toModel.holds x b := by
  constructor
  · rintro ⟨m, ht, ha⟩
    exact ⟨m, ⟨ht, fun a ha' => ha a (List.mem_cons_of_mem _ ha')⟩,
      m.individuals (freshWitness kb), ha _ (List.mem_cons_self ..)⟩
  · rintro ⟨m, hm, x, hx⟩
    let names := fun n => if n = freshWitness kb then x else m.individuals n
    refine ⟨⟨m.toModel, names⟩, hm.1, ?_⟩
    intro assertion ha
    rcases List.mem_cons.mp ha with he | ha
    · subst assertion
      simpa [ABoxModel.holdsABox, Model.holds, names] using hx
    · apply (holdsABox_congr m names assertion ?_).mpr (hm.2 _ ha)
      intro n hn
      have hne : n ≠ freshWitness kb := fun he => freshWitness_not_mem kb (he ▸ names_mem ha hn)
      simp [names, hne]

private theorem pullback_models (kb : KnowledgeBase) (m : ABoxModel) {α : Type} [Nonempty α]
    (f : α → m.toModel.Object) (names : String → α)
    (hname : ∀ a ∈ individualNames kb, f (names a) = m.individuals a)
    (heq : ∀ a ∈ individualNames kb, ∀ b ∈ individualNames kb,
      m.individuals a = m.individuals b → names a = names b)
    (hu : kb.isUniversal = true) (hm : m.Models kb) :
    (ABoxModel.mk (m.toModel.pullback f) names).Models kb := by
  obtain ⟨ht, ha⟩ := Bool.and_eq_true_iff.mp hu
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg x hx
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ht g hg)
    apply pullback_holds _ f g.2 true hr x
    apply hm.1.1 g hg (f x)
    by_cases hh : m.toModel.holds (f x) g.1
    · exact hh
    · exact False.elim (pullback_holds _ f g.1 false hl x hh hx)
  · intro a ha x y hxy
    exact (pullback_edge m.toModel f (.named a.head) x y).mpr
      (hm.1.2.1 a ha (f x) (f y) (pullback_path m.toModel f a.body x y hxy))
  · exact fun a ha => pullback_assertion _ f a (hm.1.2.2 a ha)
  · intro a hmem
    have hsource := hm.2 a hmem
    have halign : ∀ n ∈ a.individualNames, f (names n) = m.individuals n :=
      fun n hn => hname n (names_mem hmem hn)
    cases a with
    | concept c n =>
      have hc := List.all_eq_true.mp ha _ hmem
      apply pullback_holds _ f c true hc (names n)
      simpa [halign n (by simp [ABoxAssertion.individualNames]), ABoxModel.holdsABox, atPolarity] using hsource
    | role r a b =>
      change (m.toModel.pullback f).edge r (names a) (names b)
      apply (pullback_edge m.toModel f r (names a) (names b)).mpr
      rw [halign a (by simp [ABoxAssertion.individualNames]), halign b (by simp [ABoxAssertion.individualNames])]
      exact hsource
    | negRole r a b =>
      intro h
      apply hsource
      have h' := (pullback_edge m.toModel f r (names a) (names b)).mp h
      rwa [halign a (by simp [ABoxAssertion.individualNames]), halign b (by simp [ABoxAssertion.individualNames])] at h'
    | same a b =>
      exact heq a (names_mem hmem (by simp [ABoxAssertion.individualNames]))
        b (names_mem hmem (by simp [ABoxAssertion.individualNames])) hsource
    | different a b =>
      intro h
      apply hsource
      have h' := congrArg f h
      rwa [halign a (by simp [ABoxAssertion.individualNames]), halign b (by simp [ABoxAssertion.individualNames])] at h'

/-- Enumerate maps on the keys used by the continuation. Values outside the
keys use the default. Keeping enumeration under the continuation permits
short-circuiting at the first satisfying assignment. -/
private def searchMaps {α β : Type} [DecidableEq α] (values : List β) (default : β) :
    List α → ((α → β) → Bool) → Bool
  | [], accept => accept (fun _ => default)
  | k :: ks, accept =>
    values.any fun v => searchMaps values default ks fun f =>
      accept (fun a => if a = k then v else f a)

private theorem searchMaps_sound {α β : Type} [DecidableEq α] (values : List β) (default : β)
    (keys : List α) (accept : (α → β) → Bool)
    (h : searchMaps values default keys accept = true) : ∃ f, accept f = true := by
  induction keys generalizing accept with
  | nil => exact ⟨_, h⟩
  | cons k ks ih =>
    obtain ⟨v, _, hv⟩ := List.any_eq_true.mp h
    obtain ⟨f, hf⟩ := ih _ hv
    exact ⟨_, hf⟩

private theorem searchMaps_complete {α β : Type} [DecidableEq α] (values : List β) (default : β)
    (keys : List α) (accept : (α → β) → Bool) (wanted : α → β)
    (hvalues : ∀ a ∈ keys, wanted a ∈ values)
    (haccept : ∀ f, (∀ a ∈ keys, f a = wanted a) → accept f = true) :
    searchMaps values default keys accept = true := by
  induction keys generalizing accept with
  | nil => exact haccept _ (by simp)
  | cons k ks ih =>
    apply List.any_eq_true.mpr
    refine ⟨wanted k, hvalues k (by simp), ih _ (fun a ha => hvalues a (List.mem_cons_of_mem _ ha)) ?_⟩
    intro f hf
    apply haccept
    intro a ha
    by_cases h : a = k
    · simp [h]
    · exact (ite_eq_right h).trans (hf a ((List.mem_cons.mp ha).resolve_left h))

private inductive Test (α : Type) where
  | const (b : Bool)
  | var (v : α)
  | neg (t : Test α)
  | conj (t u : Test α)
  | disj (t u : Test α)

private def Test.eval {α : Type} (f : α → Bool) : Test α → Bool
  | .const b => b
  | .var v => f v
  | .neg t => !(t.eval f)
  | .conj t u => t.eval f && u.eval f
  | .disj t u => t.eval f || u.eval f

private def Test.denote {α : Type} (f : α → Prop) : Test α → Prop
  | .const b => b = true
  | .var v => f v
  | .neg t => ¬ t.denote f
  | .conj t u => t.denote f ∧ u.denote f
  | .disj t u => t.denote f ∨ u.denote f

private def Test.variables {α : Type} : Test α → List α
  | .const _ => []
  | .var v => [v]
  | .neg t => t.variables
  | .conj t u | .disj t u => t.variables ++ u.variables

private theorem Test.eval_congr {α : Type} (t : Test α) {f g : α → Bool}
    (h : ∀ v ∈ t.variables, f v = g v) : t.eval f = t.eval g := by
  induction t with
  | const => rfl
  | var v => exact h v (by simp [Test.variables])
  | neg t ih => simp only [Test.eval, ih h]
  | conj t u iht ihu | disj t u iht ihu =>
    have ht := iht (fun v hv => h v (List.mem_append_left _ hv))
    have hu := ihu (fun v hv => h v (List.mem_append_right _ hv))
    simp only [Test.eval, ht, hu]

private theorem Test.eval_iff {α : Type} (t : Test α) {f : α → Bool} {p : α → Prop}
    (h : ∀ v, f v = true ↔ p v) : t.eval f = true ↔ t.denote p := by
  induction t <;> simp_all [Test.eval, Test.denote]
  rename_i t ih
  rw [← Bool.not_eq_true, ih]

private def Test.solve {α : Type} [DecidableEq α] (t : Test α) : Bool :=
  searchMaps [false, true] false t.variables.eraseDups (t.eval ·)

private theorem Test.solve_iff {α : Type} [DecidableEq α] (t : Test α) :
    t.solve = true ↔ ∃ f, t.eval f = true := by
  constructor
  · exact searchMaps_sound _ _ _ _
  · rintro ⟨f, hf⟩
    apply searchMaps_complete _ _ _ _ f
    · intro a _
      cases f a <;> simp
    · intro g h
      rw [Test.eval_congr t (fun v hv => h v (List.mem_eraseDups.mpr hv))]
      exact hf

private def Test.all {α β : Type} (xs : List β) (f : β → Test α) : Test α :=
  xs.foldr (fun x rest => .conj (f x) rest) (.const true)

private def Test.any {α β : Type} (xs : List β) (f : β → Test α) : Test α :=
  xs.foldr (fun x rest => .disj (f x) rest) (.const false)

private def Test.implies {α : Type} (a b : Test α) : Test α := .disj (.neg a) b

private theorem Test.denote_all {α β : Type} (xs : List β) (f : β → Test α) (p : α → Prop) :
    (Test.all xs f).denote p ↔ ∀ x ∈ xs, (f x).denote p := by
  induction xs <;> simp_all [Test.all, Test.denote]

private theorem Test.denote_any {α β : Type} (xs : List β) (f : β → Test α) (p : α → Prop) :
    (Test.any xs f).denote p ↔ ∃ x ∈ xs, (f x).denote p := by
  induction xs <;> simp_all [Test.any, Test.denote]

private theorem Test.denote_implies {α : Type} (a b : Test α) (p : α → Prop) :
    (a.implies b).denote p ↔ (a.denote p → b.denote p) := by
  simp only [Test.implies, Test.denote]
  constructor
  · exact fun h ha => h.resolve_left (fun hn => hn ha)
  · intro h
    by_cases ha : a.denote p
    · exact Or.inr (h ha)
    · exact Or.inl ha

private def Test.every {α : Type} (n : Nat) (f : Fin n → Test α) : Test α :=
  Test.all (List.finRange n) f

private def Test.existsAt {α : Type} (n : Nat) (f : Fin n → Test α) : Test α :=
  Test.any (List.finRange n) f

private theorem Test.denote_every {α : Type} (n : Nat) (f : Fin n → Test α) (p : α → Prop) :
    (Test.every n f).denote p ↔ ∀ x, (f x).denote p := by
  rw [Test.every, Test.denote_all]
  exact ⟨fun h x => h x (List.mem_finRange x), fun h x _ => h x⟩

private theorem Test.denote_existsAt {α : Type} (n : Nat) (f : Fin n → Test α) (p : α → Prop) :
    (Test.existsAt n f).denote p ↔ ∃ x, (f x).denote p := by
  rw [Test.existsAt, Test.denote_any]
  exact ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, List.mem_finRange x, h⟩⟩

private inductive Fact (n : Nat) where
  | member (c : String) (x : Fin n)
  | related (r : String) (x y : Fin n)
  deriving DecidableEq

private def readFact {n : Nat} (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop) :
    Fact n → Prop
  | .member c x => classes c x
  | .related r x y => rel r x y

private def edgeTest {n : Nat} (r : Role) (x y : Fin n) : Test (Fact n) :=
  match r with
  | .named r => .var (.related r x y)
  | .inverse r => .var (.related r y x)

private def pathTest {n : Nat} : List Role → Fin n → Fin n → Test (Fact n)
  | [], x, y => .const (decide (x = y))
  | r :: rs, x, y => Test.existsAt n fun z => .conj (edgeTest r x z) (pathTest rs z y)

private def conceptTest {n : Nat} (x : Fin n) : Concept → Test (Fact n)
  | .atom c => .var (.member c x)
  | .top => .const true
  | .bottom => .const false
  | .neg c => .neg (conceptTest x c)
  | .conj c d => .conj (conceptTest x c) (conceptTest x d)
  | .disj c d => .disj (conceptTest x c) (conceptTest x d)
  | .some r c => Test.existsAt n fun y => .conj (edgeTest r x y) (conceptTest y c)
  | .all r c => Test.every n fun y => (edgeTest r x y).implies (conceptTest y c)
  | .self r => edgeTest r x x
  | .min .. | .max .. => .const false

private def roleAssertionTest (n : Nat) : RoleAssertion → Test (Fact n)
  | .localReflexive r => Test.every n fun x => Test.every n fun y =>
      (edgeTest r x y).implies (edgeTest r x x)
  | .irreflexive r => Test.every n fun x => .neg (edgeTest r x x)
  | .symmetric r => Test.every n fun x => Test.every n fun y =>
      (edgeTest r x y).implies (edgeTest r y x)
  | .transitive r => Test.every n fun x => Test.every n fun y => Test.every n fun z =>
      (edgeTest r x y).implies ((edgeTest r y z).implies (edgeTest r x z))
  | .disjoint r s => Test.every n fun x => Test.every n fun y =>
      .neg (.conj (edgeTest r x y) (edgeTest s x y))

private def aboxTest {n : Nat} (names : String → Fin n) : ABoxAssertion → Test (Fact n)
  | .concept c a => conceptTest (names a) c
  | .role r a b => edgeTest r (names a) (names b)
  | .negRole r a b => .neg (edgeTest r (names a) (names b))
  | .same a b => .const (decide (names a = names b))
  | .different a b => .const (decide (names a ≠ names b))

private def compileKB {n : Nat} (kb : KnowledgeBase) (names : String → Fin n) : Test (Fact n) :=
  .conj
    (Test.all kb.tboxRBox.tbox fun (a, b) => Test.every n fun x =>
      (conceptTest x a).implies (conceptTest x b))
    (.conj
      (Test.all kb.tboxRBox.hierarchy fun a => Test.every n fun x => Test.every n fun y =>
        (pathTest a.body x y).implies (edgeTest (.named a.head) x y))
      (.conj (Test.all kb.tboxRBox.assertions (roleAssertionTest n))
        (Test.all kb.abox (aboxTest names))))

private abbrev finiteModel {n : Nat} [Nonempty (Fin n)] (classes : String → Fin n → Prop)
    (rel : String → Fin n → Fin n → Prop) : Model :=
  ⟨Fin n, inferInstance, classes, rel⟩

private theorem edgeTest_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (r : Role) (x y : Fin n) :
    (edgeTest r x y).denote (readFact classes rel) ↔ (finiteModel classes rel).edge r x y := by
  cases r <;> rfl

private theorem pathTest_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (rs : List Role) (x y : Fin n) :
    (pathTest rs x y).denote (readFact classes rel) ↔ (finiteModel classes rel).path rs x y := by
  induction rs generalizing x y with
  | nil =>
    simpa [pathTest, Test.denote] using ((finiteModel classes rel).path_nil_iff x y).symm
  | cons r rs ih =>
    simp only [pathTest, Test.denote_existsAt, Test.denote, edgeTest_correct, ih]
    exact ((finiteModel classes rel).path_cons_iff r rs x y).symm

private theorem conceptTest_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (c : Concept) (positive : Bool) (h : c.isUniversal positive = true) (x : Fin n) :
    (conceptTest x c).denote (readFact classes rel) ↔ (finiteModel classes rel).holds x c := by
  induction c generalizing positive x with
  | atom => rfl
  | top | bottom => simp [conceptTest, Test.denote, Model.holds]
  | neg c ih => simp [conceptTest, Test.denote, Model.holds, ih (!positive) h]
  | conj c d ihc ihd | disj c d ihc ihd =>
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp h
    simp [conceptTest, Test.denote, Model.holds, ihc positive hc, ihd positive hd]
  | some r c ih =>
    have hc := (Bool.and_eq_true_iff.mp h).2
    simp [conceptTest, Test.denote_existsAt, Test.denote, edgeTest_correct, Model.holds, ih false hc]
  | all r c ih =>
    have hc := (Bool.and_eq_true_iff.mp h).2
    simp [conceptTest, Test.denote_every, Test.denote_implies, edgeTest_correct, Model.holds, ih true hc]
  | self r => exact edgeTest_correct classes rel r x x
  | min | max => contradiction

private theorem roleAssertionTest_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (a : RoleAssertion) :
    (roleAssertionTest n a).denote (readFact classes rel) ↔ (finiteModel classes rel).holdsAssertion a := by
  cases a with
  | localReflexive r =>
    simp only [roleAssertionTest, Test.denote_every, Test.denote_implies, edgeTest_correct, Model.holdsAssertion]
    exact ⟨fun h x ⟨y, hy⟩ => h x y hy, fun h x y hy => h x ⟨y, hy⟩⟩
  | _ => simp [roleAssertionTest, Test.denote_every, Test.denote_implies, Test.denote, edgeTest_correct,
      Model.holdsAssertion]

private theorem aboxTest_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (names : String → Fin n) (a : ABoxAssertion) (h : a.isUniversal = true) :
    (aboxTest names a).denote (readFact classes rel) ↔
      (ABoxModel.mk (finiteModel classes rel) names).holdsABox a := by
  cases a with
  | concept c a => exact conceptTest_correct classes rel c true h (names a)
  | _ => simp [aboxTest, Test.denote, edgeTest_correct, ABoxModel.holdsABox]

private theorem compileKB_correct {n : Nat} [Nonempty (Fin n)]
    (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop)
    (kb : KnowledgeBase) (names : String → Fin n) (hu : kb.isUniversal = true) :
    (compileKB kb names).denote (readFact classes rel) ↔
      (ABoxModel.mk (finiteModel classes rel) names).Models kb := by
  obtain ⟨ht, ha⟩ := Bool.and_eq_true_iff.mp hu
  have htbox : (∀ g ∈ kb.tboxRBox.tbox, ∀ x,
      ((conceptTest x g.1).denote (readFact classes rel) → (conceptTest x g.2).denote (readFact classes rel))) ↔
      (∀ g ∈ kb.tboxRBox.tbox, ∀ x, (finiteModel classes rel).holds x g.1 →
        (finiteModel classes rel).holds x g.2) := by
    apply forall_congr'
    intro g
    apply forall_congr'
    intro hg
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ht g hg)
    simp only [conceptTest_correct classes rel g.1 false hl, conceptTest_correct classes rel g.2 true hr]
  have habox : (∀ a ∈ kb.abox, (aboxTest names a).denote (readFact classes rel)) ↔
      (∀ a ∈ kb.abox, (ABoxModel.mk (finiteModel classes rel) names).holdsABox a) := by
    apply forall_congr'
    intro a
    apply forall_congr'
    exact fun hm => aboxTest_correct classes rel names a (List.all_eq_true.mp ha a hm)
  simp only [compileKB, Test.denote, Test.denote_all, Test.denote_every, Test.denote_implies,
    pathTest_correct, edgeTest_correct, roleAssertionTest_correct, ABoxModel.Models, Model.Models, ← and_assoc]
  rw [htbox, habox]

private theorem Test.solve_iff_model {n : Nat} [Nonempty (Fin n)]
    (kb : KnowledgeBase) (names : String → Fin n) (hu : kb.isUniversal = true) :
    (compileKB kb names).solve = true ↔
      ∃ (classes : String → Fin n → Prop) (rel : String → Fin n → Fin n → Prop),
        (ABoxModel.mk (finiteModel classes rel) names).Models kb := by
  rw [Test.solve_iff]
  constructor
  · rintro ⟨f, hf⟩
    let classes := fun c x => f (.member c x) = true
    let rel := fun r x y => f (.related r x y) = true
    have hf' : ∀ v, f v = true ↔ readFact classes rel v := by intro v; cases v <;> rfl
    exact ⟨classes, rel, (compileKB_correct classes rel kb names hu).mp
      ((Test.eval_iff _ hf').mp hf)⟩
  · rintro ⟨classes, rel, h⟩
    classical
    refine ⟨fun v => decide (readFact classes rel v), ?_⟩
    apply (Test.eval_iff _ (p := readFact classes rel) (fun v => by simp)).mpr
    exact (compileKB_correct classes rel kb names hu).mpr h

private theorem finite_representatives (kb : KnowledgeBase) (m : ABoxModel) :
    ∃ (f : Fin ((individualNames kb).length + 1) → m.toModel.Object)
      (names : String → Fin ((individualNames kb).length + 1)),
      (∀ a ∈ individualNames kb, f (names a) = m.individuals a) ∧
      (∀ a b, m.individuals a = m.individuals b → names a = names b) := by
  classical
  let xs := Classical.choice m.toModel.nonempty :: (individualNames kb).map m.individuals
  have hlen : xs.length = (individualNames kb).length + 1 := by simp [xs]
  let f := fun i : Fin ((individualNames kb).length + 1) => xs.get (i.cast hlen.symm)
  let pick := fun x : m.toModel.Object =>
    if hx : ∃ i, f i = x then Classical.choose hx else 0
  refine ⟨f, pick ∘ m.individuals, ?_, fun a b h => congrArg pick h⟩
  intro a ha
  have hmem : m.individuals a ∈ xs := List.mem_cons_of_mem _ (List.mem_map_of_mem ha)
  obtain ⟨i, hi⟩ := List.get_of_mem hmem
  have hex : ∃ i, f i = m.individuals a := ⟨i.cast hlen, hi⟩
  change f (pick (m.individuals a)) = m.individuals a
  dsimp only [pick]
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

/-- Decide the universal fragment by grounding over one position per name plus
a default position. Assignments of names may co-denote and all named assertions
are checked in the resulting interpretation. -/
def KnowledgeBase.decideUniversal (kb : KnowledgeBase) (_ : kb.isUniversal = true) : Bool :=
  let n := (individualNames kb).length + 1
  searchMaps (List.finRange n) 0 (individualNames kb) fun names => (compileKB kb names).solve

theorem KnowledgeBase.decideUniversal_iff {kb : KnowledgeBase} (hu : kb.isUniversal = true) :
    kb.decideUniversal hu = true ↔ kb.Sat := by
  constructor
  · intro h
    obtain ⟨names, hnames⟩ := searchMaps_sound _ _ _ _ h
    obtain ⟨classes, rel, hm⟩ := (Test.solve_iff_model kb names hu).mp hnames
    exact ⟨ABoxModel.mk (finiteModel classes rel) names, hm⟩
  · rintro ⟨m, hm⟩
    obtain ⟨f, names, halign, heq⟩ := finite_representatives kb m
    apply searchMaps_complete _ _ _ _ names (fun _ _ => List.mem_finRange _)
    intro found hfound
    have hmodel := pullback_models kb m f found
      (fun a ha => (congrArg f (hfound a ha)).trans (halign a ha))
      (fun a ha b hb h => (hfound a ha).trans ((heq a b h).trans (hfound b hb).symm)) hu hm
    exact (Test.solve_iff_model kb found hu).mpr ⟨_, _, hmodel⟩

#print axioms KnowledgeBase.counterexample_sat_iff
#print axioms KnowledgeBase.decideUniversal_iff

end Sabrina.OWL2.SROIQD.TextbookSRIQ
