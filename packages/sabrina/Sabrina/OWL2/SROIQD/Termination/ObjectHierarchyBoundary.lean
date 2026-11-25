import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQABox
import Sabrina.OWL2.SROIQD.Termination.OWLHierarchy

/-! A reduction from intersection emptiness for two start symbols of a binary
context-free grammar in Chomsky normal form. The role box passes both
the reference oriented-role test and the written OWL hierarchy condition. -/
namespace Sabrina.OWL2.RoleHierarchy.GrammarBoundary

open SROIQD.TextbookSRIQ
open Sabrina.ALC (OrientedRole)

inductive Production where
  | terminal (head : String) (bit : Bool)
  | binary (head left right : String)
  deriving DecidableEq, Repr

inductive Generates (g : List Production) : String → List Bool → Prop where
  | terminal {a bit} : .terminal a bit ∈ g → Generates g a [bit]
  | binary {a b c u v} : .binary a b c ∈ g → Generates g b u → Generates g c v →
      Generates g a (u ++ v)

def DisjointStarts (g : List Production) (a b : String) : Prop :=
  ∀ w, Generates g a w → ¬ Generates g b w

private def tag (k : Char) (s : String) : String := String.ofList (k :: s.toList)
private def letter (bit : Bool) : String := if bit then "1" else "0"

/-- For a binary production, the first chain reads the two edges backwards.
The first unary inclusion turns its result forwards. The second chain uses
the compulsory loop to copy the result backwards, and the final unary
inclusion transfers it to the grammar role. Distinct tag pairs separate the
strict chain comparisons from the directed unary inclusions. -/
private def clauses : Production → List Inclusion
  | .terminal a bit => [⟨.inverse (letter bit), [], tag 'n' a⟩]
  | .binary a b c =>
    [⟨.inverse (tag 'n' c), [.inverse (tag 'n' b)], tag 'h' a⟩,
     ⟨.inverse (tag 'h' a), [], tag 'm' a⟩,
     ⟨.inverse (tag 'm' a), [.inverse "i"], tag 'l' a⟩,
     ⟨.inverse (tag 'l' a), [], tag 'n' a⟩]

private def serial (bit : Bool) : Concept × Concept :=
  (.top, .some (.inverse (letter bit)) .top)

def grammarKB (g : List Production) (a b : String) : KnowledgeBase where
  tboxRBox := { hierarchy := g.flatMap clauses
                tbox := [serial false, serial true, (.top, .self (.named "i"))] }
  abox := [.concept (.all (.named (tag 'n' a)) (.atom "mark")) "root",
           .concept (.all (.named (tag 'n' b)) (.neg (.atom "mark"))) "root"]

private theorem single (m : Model) (r : Role) (h : String) :
    (∀ x y, m.path (Inclusion.mk r [] h).body x y → m.relations h x y) ↔
      ∀ x y, m.edge r x y → m.relations h x y := by
  simp [Inclusion.body, Model.path_cons_iff, Model.path_nil_iff]

private theorem double (m : Model) (r s : Role) (h : String) :
    (∀ x y, m.path (Inclusion.mk r [s] h).body x y → m.relations h x y) ↔
      ∀ x z y, m.edge r x z → m.edge s z y → m.relations h x y := by
  simp only [Inclusion.body, Model.path_cons_iff, Model.path_nil_iff]
  constructor
  · intro f x z y hr hs
    exact f x y ⟨z, hr, y, hs, rfl⟩
  · rintro f x y ⟨z, hr, _, hs, rfl⟩
    exact f x z _ hr hs

private def walk (m : Model) : List Bool → m.Object → m.Object → Prop
  | [], x, y => x = y
  | t :: w, x, y => ∃ z, m.relations (letter t) z x ∧ walk m w z y

private theorem walk_append (m : Model) (u v : List Bool) (x y : m.Object) :
    walk m (u ++ v) x y ↔ ∃ z, walk m u x z ∧ walk m v z y := by
  induction u generalizing x with
  | nil => simp [walk]
  | cons t u ih =>
    simp only [List.cons_append, walk, ih]
    constructor
    · rintro ⟨k, hk, z, huz, hv⟩
      exact ⟨z, ⟨k, hk, huz⟩, hv⟩
    · rintro ⟨z, ⟨k, hk, huz⟩, hv⟩
      exact ⟨k, hk, z, huz, hv⟩

private theorem sat_disjoint {g a b} (hs : (grammarKB g a b).Sat) : DisjointStarts g a b := by
  obtain ⟨m, ⟨ht, hh, _⟩, hab⟩ := hs
  have edge (q) (hq : q ∈ g) (s) (hs : s ∈ clauses q) :=
    hh s (List.mem_flatMap.mpr ⟨q, hq, hs⟩)
  have loop (x : m.toModel.Object) : m.toModel.relations "i" x x :=
    ht (.top, .self (.named "i")) (by simp [grammarKB]) x trivial
  have serialEdge (t) (x : m.toModel.Object) : ∃ y, m.toModel.relations (letter t) y x := by
    have h := ht (serial t) (by cases t <;> simp [grammarKB]) x trivial
    exact ⟨h.choose, h.choose_spec.1⟩
  have path (w) (x : m.toModel.Object) : ∃ y, walk m.toModel w x y := by
    induction w generalizing x with
    | nil => exact ⟨x, rfl⟩
    | cons t w ih =>
      obtain ⟨z, hz⟩ := serialEdge t x
      obtain ⟨y, hy⟩ := ih z
      exact ⟨y, z, hz, hy⟩
  have deriv {s w} (h : Generates g s w) (x y) (hp : walk m.toModel w x y) :
      m.toModel.relations (tag 'n' s) x y := by
    induction h generalizing x y with
    | @terminal a bit hq =>
      obtain ⟨k, hk, rfl⟩ := hp
      exact (single m.toModel (.inverse (letter bit)) (tag 'n' a)).mp (edge _ hq _ (by simp [clauses])) _ _ hk
    | @binary a b c u v hq _ _ ihu ihv =>
      obtain ⟨z, hu, hv⟩ := (walk_append _ _ _ _ _).mp hp
      have rev := (double m.toModel (.inverse (tag 'n' c)) (.inverse (tag 'n' b)) (tag 'h' a)).mp
        (edge _ hq _ (by simp [clauses])) y z x (ihv _ _ hv) (ihu _ _ hu)
      have mid := (single m.toModel (.inverse (tag 'h' a)) (tag 'm' a)).mp
        (edge _ hq _ (by simp [clauses])) x y rev
      have low := (double m.toModel (.inverse (tag 'm' a)) (.inverse "i") (tag 'l' a)).mp
        (edge _ hq _ (by simp [clauses])) y x x mid (loop x)
      exact (single m.toModel (.inverse (tag 'l' a)) (tag 'n' a)).mp (edge _ hq _ (by simp [clauses])) x y low
  intro w ha hb
  obtain ⟨y, hy⟩ := path w (m.individuals "root")
  have yes := hab (.concept (.all (.named (tag 'n' a)) (.atom "mark")) "root") (by simp [grammarKB])
  have no := hab (.concept (.all (.named (tag 'n' b)) (.neg (.atom "mark"))) "root") (by simp [grammarKB])
  exact no y (deriv hb _ _ hy) (yes y (deriv ha _ _ hy))

private def lang (g : List Production) (s : String) (x y : List Bool) : Prop :=
  ∃ w, Generates g s w ∧ y = x ++ w

private def wordRelation (g : List Production) (r : String) (x y : List Bool) : Prop :=
  match r.toList with
  | ['0'] => x = y ++ [false]
  | ['1'] => x = y ++ [true]
  | ['i'] => x = y
  | 'n' :: s | 'm' :: s => lang g (String.ofList s) x y
  | 'l' :: s | 'h' :: s => lang g (String.ofList s) y x
  | _ => False

private def wordModel (g : List Production) (start : String) : ABoxModel :=
  ⟨⟨List Bool, ⟨[]⟩, fun _ w => Generates g start w, wordRelation g⟩, fun _ => []⟩

private theorem disjoint_sat {g a b} (hd : DisjointStarts g a b) : (grammarKB g a b).Sat := by
  let m := wordModel g a
  have terminal (t : Bool) (x y : List Bool) :
      m.toModel.edge (.inverse (letter t)) x y ↔ y = x ++ [t] := by cases t <;> rfl
  refine ⟨m, ⟨?_, ?_, by simp [grammarKB]⟩, ?_⟩
  · intro c hc
    simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact fun (x : List Bool) _ => ⟨x ++ [false], (terminal ..).mpr rfl, trivial⟩
    · exact fun (x : List Bool) _ => ⟨x ++ [true], (terminal ..).mpr rfl, trivial⟩
    · exact fun _ _ => rfl
  · intro c hc
    obtain ⟨q, hq, hc⟩ := List.mem_flatMap.mp hc
    cases q with
    | terminal s t =>
      obtain rfl := List.mem_singleton.mp hc
      apply (single ..).mpr
      intro x y he
      simpa [m, wordModel, Model.edge, wordRelation, tag] using
        (show lang g s x y from ⟨[t], .terminal hq, (terminal ..).mp he⟩)
    | binary s l r =>
      simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · apply (double ..).mpr
        intro y z x hr hl
        simp [m, wordModel, Model.edge, wordRelation, tag] at hr hl ⊢
        obtain ⟨v, hv, rfl⟩ := hr
        obtain ⟨u, hu, rfl⟩ := hl
        exact ⟨u ++ v, .binary hq hu hv, (List.append_assoc ..)⟩
      · apply (single ..).mpr
        simp [m, wordModel, Model.edge, wordRelation, tag]
      · apply (double ..).mpr
        simp [m, wordModel, Model.edge, wordRelation, tag]
      · apply (single ..).mpr
        simp [m, wordModel, Model.edge, wordRelation, tag]
  · intro c hc
    simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · intro y he
      obtain ⟨w, hw, e⟩ : lang g a [] y := by simpa [m, wordModel, Model.edge, wordRelation, tag] using he
      exact (List.nil_append w ▸ e) ▸ hw
    · intro y he hy
      obtain ⟨w, hw, e⟩ : lang g b [] y := by simpa [m, wordModel, Model.edge, wordRelation, tag] using he
      exact hd y hy ((List.nil_append w ▸ e) ▸ hw)

theorem grammarOntology_sat_iff (d : DatatypeMap) (g : List Production) (a b : String) :
    Satisfiable d (grammarKB g a b).toOWL ↔ DisjointStarts g a b :=
  (kb_satisfiable_toOWL_iff ..).trans ⟨sat_disjoint, disjoint_sat⟩

private def orientedLess : Role → Role → Prop
  | .inverse _, .named _ => True
  | _, _ => False

private theorem allowedClauses (q : Production) (s : Inclusion) (hs : s ∈ clauses q) :
    s.regularFor orientedLess ∧ s.head ≠ "i" := by
  cases q <;> simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at hs
  case' terminal => subst s
  case' binary => rcases hs with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · right; right; left
      simp [Inclusion.body, orientedLess]
    · intro h
      have := congrArg (fun t : String => t.toList.head?) h
      simp [tag] at this

theorem grammarKB_wellFormed (g : List Production) (a b : String) :
    (grammarKB g a b).WellFormed := by
  let kb := grammarKB g a b
  have member {s} (h : s ∈ kb.tboxRBox.expandedHierarchy) : s.regularFor orientedLess ∧ s.head ≠ "i" := by
    change s ∈ g.flatMap clauses ++ [] at h
    obtain ⟨q, _, hs⟩ := List.mem_flatMap.mp (List.append_nil _ ▸ h)
    exact allowedClauses q s hs
  have hi : Simple kb.tboxRBox.expandedHierarchy (.named "i") :=
    .named _ (fun _ hs he => ((member hs).2 he).elim) (fun _ hs he => ((member hs).2 he).elim)
  refine ⟨⟨⟨orientedLess, ?_, ?_, fun _ hs => (member hs).1⟩, by simp [grammarKB], ?_⟩, ?_⟩
  · intro r; cases r <;> simp [orientedLess]
  · intro r s t; cases s <;> cases r <;> cases t <;> simp [orientedLess]
  · intro c hc
    simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨trivial, trivial⟩
    · exact ⟨trivial, trivial⟩
    · exact ⟨trivial, hi⟩
  · intro c hc
    simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial

private def roleTag (r : OrientedRole) : Option Char :=
  (r.1.toList.drop (encodeName "").toList.length).head?

private theorem roleTag_encode (s : String) (o : Bool) :
    roleTag (encodeName s, o) = s.toList.head? := by
  simp [roleTag, encodeName, GradedBridge.symbol]

private def Less (x y : Option Char) : Prop :=
  (x = some 'n' ∧ y = some 'h') ∨ ((x = some 'm' ∨ x = some 'i') ∧ y = some 'l')

private def Unary (x y : Option Char) : Prop :=
  (x = some 'h' ∧ y = some 'm') ∨ (x = some 'l' ∧ y = some 'n') ∨
  ((x = some '0' ∨ x = some '1') ∧ y = some 'n')

private theorem projections (g : List Production) (a b : String) :
    unaryEdges (grammarKB g a b).toOWL = g.flatMap (fun q => unaryEdges ((clauses q).map Inclusion.toOWL)) ∧
    propertyChains (grammarKB g a b).toOWL = g.flatMap (fun q => propertyChains ((clauses q).map Inclusion.toOWL)) := by
  have splitOnt : (grammarKB g a b).toOWL =
      (grammarKB [] a b).tboxRBox.toOWL ++ g.flatMap (fun q => (clauses q).map Inclusion.toOWL) ++
      (grammarKB [] a b).abox.map ABoxAssertion.toOWL := by
    simp [grammarKB, KnowledgeBase.toOWL, TBoxRBox.toOWL, List.map_flatMap]
  rw [splitOnt]
  rw [show (grammarKB [] a b).tboxRBox.toOWL = [Axiom.subClassOf (.named thing) (Concept.some (.inverse (letter false)) .top).toOWL,
      .subClassOf (.named thing) (Concept.some (.inverse (letter true)) .top).toOWL,
      .subClassOf (.named thing) (Concept.self (.named "i")).toOWL] by rfl]
  simp [unaryEdges, propertyChains, List.flatMap_assoc, List.filterMap_flatMap, Function.comp_def, grammarKB, ABoxAssertion.toOWL]

private theorem unary_clause (q : Production) (e : OrientedRole × OrientedRole)
    (he : e ∈ unaryEdges ((clauses q).map Inclusion.toOWL)) : Unary (roleTag e.1) (roleTag e.2) := by
  cases q with
  | terminal a t =>
    cases t <;> obtain rfl := List.mem_singleton.mp he <;>
      simp [Unary, Role.toOWL, Normalize.toOriented, roleTag_encode, tag, letter]
  | binary a b c =>
    change e ∈ [((encodeName (tag 'h' a), true), (encodeName (tag 'm' a), false)),
                 ((encodeName (tag 'l' a), true), (encodeName (tag 'n' a), false))] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [roleTag_encode, tag, Unary]

private theorem strict_clause (q : Production) (c : PropertyChain)
    (hc : c ∈ propertyChains ((clauses q).map Inclusion.toOWL)) :
    2 ≤ c.body.length ∧ ∀ r ∈ c.body, Less (roleTag r) (roleTag c.head) := by
  cases q with
  | terminal => contradiction
  | binary a b d =>
    change c ∈ [⟨[(encodeName (tag 'n' d), true), (encodeName (tag 'n' b), true)], (encodeName (tag 'h' a), false)⟩,
                ⟨[(encodeName (tag 'm' a), true), (encodeName "i", true)], (encodeName (tag 'l' a), false)⟩] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [roleTag_encode, tag, Less]

private theorem reachTag {g a b} {r s : OrientedRole}
    (h : Sabrina.RoleChains.SimpleRoles.Reachable (unaryEdges (grammarKB g a b).toOWL) r s) :
    roleTag r = roleTag s ∨ Unary (roleTag r) (roleTag s) := by
  have step {r s : OrientedRole} (he : (r,s) ∈ unaryEdges (grammarKB g a b).toOWL) : Unary (roleTag r) (roleTag s) := by
    rw [(projections g a b).1] at he
    obtain ⟨q, _, h⟩ := List.mem_flatMap.mp he
    exact unary_clause q _ h
  induction h with
  | refl => exact .inl rfl
  | step h =>
    apply Or.inr
    rcases List.mem_append.mp h with h | h
    · exact step h
    · obtain ⟨⟨x,y⟩, hxy, eq⟩ := List.mem_map.mp h
      cases eq
      exact step (r := x) (s := y) hxy
  | trans _ _ ih hj =>
    rcases ih with hi | hi
    · rwa [hi]
    rcases hj with hj | hj
    · exact .inr (hj ▸ hi)
    · unfold Unary at hi hj
      grind

theorem grammarOntology_writtenRegular (g : List Production) (a b : String) :
    WrittenOntologyRegular (grammarKB g a b).toOWL := by
  refine ⟨fun r s => Less (roleTag r) (roleTag s), ?_, ?_, fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro r; unfold Less; grind
  · intro r s t; unfold Less; grind
  · intro r s hlt hr
    have h := reachTag hr
    unfold Less at hlt
    unfold Unary at h
    grind
  · intro c hc
    rw [(projections g a b).2] at hc
    obtain ⟨q, _, h⟩ := List.mem_flatMap.mp hc
    obtain ⟨hl, hlower⟩ := strict_clause q c h
    exact ⟨hl, .inr ⟨_, .plain _, hlower⟩⟩

/-- Dropping the two class assertions preserves the syntactic hierarchy
of the consistent base used for the subclass reduction. -/
theorem grammarTBox_writtenRegular (g : List Production) (a b : String) :
    WrittenOntologyRegular (grammarKB g a b).tboxRBox.toOWL := by
  have h := grammarOntology_writtenRegular g a b
  simpa [WrittenOntologyRegular, KnowledgeBase.toOWL, unaryEdges, propertyChains,
    grammarKB, ABoxAssertion.toOWL] using h

/-- The only self restriction in the OWL translation uses an ordinary role
unreachable from every composite role in the actual typed hierarchy. -/
theorem grammarOntology_self_simple (g : List Production) (a b : String) :
    Sabrina.RoleChains.SimpleRoles.Simple (unaryEdges (grammarKB g a b).toOWL)
      ((propertyChains (grammarKB g a b).toOWL).map PropertyChain.orient) (encodeName "i", false) := by
  intro s hr hc
  have eq := reachTag hr
  have htag : roleTag s = some 'i' := by
    rcases eq with eq | eq
    · exact eq
    · change Unary (roleTag s) (some 'i') at eq
      simp [Unary] at eq
  rcases hc with hb | ⟨c, hmem, _, hn⟩
  · simp only [Sabrina.RoleChains.SimpleRoles.builtinRoles, List.mem_cons, List.not_mem_nil, or_false] at hb
    have hname : roleTag (s.1, false) = some 'i' := htag
    rcases hb with h | h <;> rw [h] at hname <;> exact (by decide : ¬ _) hname
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    rw [(projections g a b).2] at hc
    obtain ⟨q, _, hm⟩ := List.mem_flatMap.mp hc
    have hlen := (strict_clause q c hm).1
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil c.body (show c.body ≠ [] by intro he; simp [he] at hlen)
    have ht := (strict_clause q c hm).2 r hr
    have he : roleTag c.head = roleTag s := congrArg
      (fun str : String => roleTag (str,false)) hn
    rw [he, htag] at ht
    simp [Less] at ht

/-- Removing the two assertions at the root leaves a satisfiable ontology for
every grammar. A one-object interpretation with all role edges suffices. -/
theorem grammarTBox_sat (d : DatatypeMap) (g : List Production) (a b : String) :
    Satisfiable d (grammarKB g a b).tboxRBox.toOWL := by
  apply (satisfiable_toOWL_iff ..).mpr
  let m : Model := ⟨Unit, inferInstance, fun _ _ => True, fun _ _ _ => True⟩
  refine ⟨m, ⟨?_, fun _ _ _ _ _ => trivial, by simp [grammarKB]⟩⟩
  intro c hc
  simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact fun _ _ => ⟨(), trivial, trivial⟩
  · exact fun _ _ => ⟨(), trivial, trivial⟩
  · exact fun _ _ => trivial

def grammarSubclass (a b : String) : Axiom :=
  .subClassOf (Concept.all (.named (tag 'n' a)) (.atom "mark")).toOWL
    (Concept.neg (.all (.named (tag 'n' b)) (.neg (.atom "mark")))).toOWL

/-- Subclass entailment already detects a common word over the consistent
TBox and RBox alone. No conclusion follows by explosion in this reduction. -/
theorem grammarSubclass_entails_iff (d : DatatypeMap) (g : List Production) (a b : String) :
    Entails d (grammarKB g a b).tboxRBox.toOWL [grammarSubclass a b] ↔
      ∃ w, Generates g a w ∧ Generates g b w := by
  classical
  have overlap : (∃ w, Generates g a w ∧ Generates g b w) ↔ ¬ DisjointStarts g a b := by
    simp [DisjointStarts]
  rw [overlap]
  constructor
  · intro ent hd
    obtain ⟨i, assign, h⟩ := (grammarOntology_sat_iff d g a b).mpr hd
    obtain ⟨other, hq⟩ := ent i ⟨assign, fun ax hm => h ax (List.mem_append_left _ hm)⟩
    have pos := h _ (List.mem_append_right _ (List.mem_cons_self ..))
    have neg := h _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact hq (grammarSubclass a b) (List.mem_singleton_self _) (i.individuals (encodeInd "root")) pos neg
  · intro h i ⟨assign, hi⟩
    refine ⟨assign, ?_⟩
    intro ax hm
    obtain rfl := List.mem_singleton.mp hm
    intro x hp hn
    let j := i.withAnonymous assign
    let m : ABoxModel := ⟨Model.fromOWL j, fun _ => x⟩
    apply h
    apply sat_disjoint
    refine ⟨m, (models_fromOWL_iff j _).mp hi, ?_⟩
    intro c hc
    simp only [grammarKB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (holds_fromOWL_iff j (.all (.named (tag 'n' a)) (.atom "mark")) x).mp hp
    · exact (holds_fromOWL_iff j (.all (.named (tag 'n' b)) (.neg (.atom "mark"))) x).mp hn

/-- Composing an executable total verdict on this domain with the translation
would decide the disjointness of the two grammar languages. -/
theorem decide_disjoint_of_object_decider (f : Ontology → Bool)
    (correct : ∀ g a b, WrittenOntologyRegular (grammarKB g a b).toOWL →
      (grammarKB g a b).WellFormed →
      Sabrina.RoleChains.SimpleRoles.Simple (unaryEdges (grammarKB g a b).toOWL)
        ((propertyChains (grammarKB g a b).toOWL).map PropertyChain.orient) (encodeName "i", false) →
      (f (grammarKB g a b).toOWL = true ↔ Satisfiable Datatypes.datatypeMap (grammarKB g a b).toOWL))
    (g : List Production) (a b : String) :
    f (grammarKB g a b).toOWL = true ↔ DisjointStarts g a b :=
  (correct g a b (grammarOntology_writtenRegular ..) (grammarKB_wellFormed ..) (grammarOntology_self_simple g a b)).trans
    (grammarOntology_sat_iff ..)

/-- Separate starts and production lists. Nonterminal names can overlap. -/
structure Grammar where
  start : String
  rules : List Production
  deriving DecidableEq, Repr

private def listFor (left right : Grammar) (side : Bool) : List Production :=
  if side then right.rules else left.rules

private def scopeName (side : Bool) := tag (if side then 'R' else 'L')

private def rename (side : Bool) : Production → Production
  | .terminal a t => .terminal (scopeName side a) t
  | .binary a b c => .binary (scopeName side a) (scopeName side b) (scopeName side c)

private def merge (l r : Grammar) : List Production :=
  (l.rules.map (rename false)) ++ (r.rules.map (rename true))

private theorem scope_eq {i j : Bool} {a b : String} :
    scopeName i a = scopeName j b ↔ i = j ∧ a = b := by
  constructor
  · intro he
    have hh := congrArg String.toList he
    cases i <;> cases j <;> simp [scopeName, tag] at hh ⊢ <;> simpa using congrArg String.ofList hh
  · rintro ⟨rfl, rfl⟩; rfl

private theorem merge_mem {l r : Grammar} {q : Production} :
    q ∈ merge l r ↔ ∃ s p, p ∈ listFor l r s ∧ rename s p = q := by
  simp only [merge, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨p, hp, eq⟩ | ⟨p, hp, eq⟩)
    · exact ⟨false, p, hp, eq⟩
    · exact ⟨true, p, hp, eq⟩
  · rintro ⟨(_ | _), p, hp, eq⟩
    · exact .inl ⟨p, hp, eq⟩
    · exact .inr ⟨p, hp, eq⟩

private theorem merge_generates {l r : Grammar} {s : Bool} {a w} :
    Generates (merge l r) (scopeName s a) w ↔ Generates (listFor l r s) a w := by
  constructor
  · intro h
    generalize he : scopeName s a = name at h
    induction h generalizing s a with
    | terminal hp =>
      obtain ⟨j, p, hm, eq⟩ := merge_mem.mp hp
      cases p with
      | terminal head t =>
        cases eq
        obtain ⟨rfl, rfl⟩ := scope_eq.mp he
        exact .terminal hm
      | binary => contradiction
    | binary hp hl hr ihl ihr =>
      obtain ⟨j, p, hm, eq⟩ := merge_mem.mp hp
      cases p with
      | terminal => contradiction
      | binary head lhs rhs =>
        cases eq
        obtain ⟨rfl, rfl⟩ := scope_eq.mp he
        exact .binary hm (ihl rfl) (ihr rfl)
  · intro h
    induction h with
    | terminal hp => exact .terminal (merge_mem.mpr ⟨s, _, hp, rfl⟩)
    | binary hp _ _ ihl ihr => exact .binary (merge_mem.mpr ⟨s, _, hp, rfl⟩) ihl ihr

def encodePair (l r : Grammar) : KnowledgeBase :=
  grammarKB (merge l r) (scopeName false l.start) (scopeName true r.start)

theorem encodePair_sat_iff (d : DatatypeMap) (l r : Grammar) :
    Satisfiable d (encodePair l r).toOWL ↔
      ∀ w, Generates l.rules l.start w → ¬ Generates r.rules r.start w := by
  simp only [encodePair, grammarOntology_sat_iff, DisjointStarts, merge_generates, listFor, Bool.false_eq_true,
    ite_false, ite_true]

theorem encodePair_entails_iff (d : DatatypeMap) (l r : Grammar) :
    Entails d (encodePair l r).tboxRBox.toOWL
      [grammarSubclass (scopeName false l.start) (scopeName true r.start)] ↔
      ∃ w, Generates l.rules l.start w ∧ Generates r.rules r.start w := by
  simp only [encodePair, grammarSubclass_entails_iff, merge_generates, listFor, Bool.false_eq_true,
    ite_false, ite_true]

#print axioms encodePair_sat_iff
#print axioms encodePair_entails_iff
#print axioms grammarTBox_writtenRegular
#print axioms grammarTBox_sat
#print axioms grammarSubclass_entails_iff
#print axioms grammarOntology_sat_iff
#print axioms grammarKB_wellFormed
#print axioms grammarOntology_self_simple
#print axioms grammarOntology_writtenRegular
#print axioms decide_disjoint_of_object_decider

end Sabrina.OWL2.RoleHierarchy.GrammarBoundary
