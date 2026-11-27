import Sabrina.OWL2.SROIQD.Model

/-! Tableau branch state, nominal/anonymous/ABox initialization, node allocation,
    and equality merging with soundness proofs for unified SROIQ(D). -/

namespace Sabrina.OWL2.SROIQD

open Sabrina.ALC (OrientedRole)
open Sabrina.OWL2.Datatypes (Value datatypeMap decodeLiteral)

structure Branch where
  labels : List (Nat × Concept)
  edges : List (IRI × Nat × Nat) := []
  negEdges : List (IRI × Nat × Nat) := []
  unequal : List (Nat × Nat) := []
  expanded : List (Nat × Concept) := []
  noms : List (IRI × Nat) := []
  anons : List ((String × String) × Nat) := []
  dataEdges : List (IRI × Nat × Value) := []
  negDataEdges : List (IRI × Nat × Value) := []
  dataConstraints : List (Nat × IRI × DataRange) := []
  deriving Repr

structure Branch.Realizes (s : Branch) (i : Interpretation datatypeMap)
    (env : Nat → i.Object) : Prop where
  labels : ∀ x c, (x, c) ∈ s.labels → holds i (env x) c
  edges : ∀ r x y, (r, x, y) ∈ s.edges → i.objectProperties r (env x) (env y)
  negEdges : ∀ r x y, (r, x, y) ∈ s.negEdges → ¬ i.objectProperties r (env x) (env y)
  unequal : ∀ x y, (x, y) ∈ s.unequal → env x ≠ env y
  noms : ∀ a x, (a, x) ∈ s.noms → env x = i.individuals (.named a)
  anons : ∀ k x, (k, x) ∈ s.anons → env x = i.individuals (.anonymous k.1 k.2)
  dataEdges : ∀ dp x v, (dp, x, v) ∈ s.dataEdges → i.dataProperties dp (env x) (i.embedValue v)
  negDataEdges : ∀ dp x v, (dp, x, v) ∈ s.negDataEdges → ¬ i.dataProperties dp (env x) (i.embedValue v)
  dataConstraints : ∀ x dp d, (x, dp, d) ∈ s.dataConstraints →
    ∀ y, i.dataProperties dp (env x) y → dataHolds i y d

def Branch.Sat (p : Problem) (s : Branch) : Prop :=
  ∃ i : Interpretation datatypeMap, p.Models i ∧ ∃ env, s.Realizes i env

private theorem zipIdx_index_eq {α : Type} (xs : List α) (start : Nat) {a : α} {k : Nat}
    (h : (a, k) ∈ xs.zipIdx start) :
    ∃ j : Nat, j < xs.length ∧ k = start + j ∧ xs[j]? = some a := by
  induction xs generalizing start with
  | nil => simp at h
  | cons hd tail ih =>
    simp only [List.zipIdx, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h'
    · exact ⟨0, Nat.zero_lt_succ _, by omega, rfl⟩
    · obtain ⟨j, hj, rfl, hget⟩ := ih (start + 1) h'
      exact ⟨j + 1, Nat.succ_lt_succ hj, by omega, hget⟩

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α]
    {xs : List (α × β)} {a : α} {b : β} (h : xs.lookup a = some b) : (a, b) ∈ xs := by
  induction xs with
  | nil => simp [List.lookup] at h
  | cons hd tail ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.lookup] at h
    cases hbeq : (a == k) with
    | true =>
      simp only [hbeq, Option.some.injEq] at h
      have hk := beq_iff_eq.mp hbeq
      subst hk h
      exact List.mem_cons_self ..
    | false =>
      simp only [hbeq] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem mapM_mem_iff {α β : Type} {xs : List α} {f : α → Option β} {ys : List β}
    (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    simp [List.mapM_nil, pure] at h; subst h; simp at hy
  | cons a tail ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hf : f a with
    | none => simp [hf] at h
    | some b =>
      simp only [hf] at h
      cases hrest : tail.mapM f with
      | none => simp [hrest] at h
      | some bs =>
        simp only [hrest, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨a, List.mem_cons_self .., hf⟩
        · obtain ⟨x, hx, hfx⟩ := ih hrest hy'
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private def lookupInd (ns : List (IRI × Nat)) (as : List ((String × String) × Nat)) :
    Individual → Option Nat
  | .named a => ns.lookup a
  | .anonymous doc lid => as.lookup (doc, lid)

/-- Initialize root node `0` for `p.root`, dedicated nominal roots `1..k` for
    named individuals, dedicated anonymous roots `k+1..k+m` for anonymous
    individuals, and all ABox assertions. -/
def initial (p : Problem) : Option Branch :=
  let ns := p.nominals.zipIdx 1
  let as := p.anons.zipIdx (1 + p.nominals.length)
  let lu := lookupInd ns as
  (p.classAssertions.mapM fun ac => (lu ac.1).map (·, ac.2)).bind fun caLabels =>
  (p.sameInds.mapM fun ab => (lu ab.1).map (·, Concept.nom ab.2 true)).bind fun sameLabels =>
  (p.objAssertions.mapM fun rab => (lu rab.2.1).bind fun ka => (lu rab.2.2).map fun kb => (rab.1, ka, kb)).bind fun objEdges =>
  (p.negObjAssertions.mapM fun rab => (lu rab.2.1).bind fun ka => (lu rab.2.2).map fun kb => (rab.1, ka, kb)).bind fun negObjEdges =>
  (p.diffInds.mapM fun ab => (lu ab.1).bind fun ka => (lu ab.2).map fun kb => (ka, kb)).bind fun diffPairs =>
  (p.dataAssertions.mapM fun ral => (lu ral.2.1).bind fun ka => (decodeLiteral ral.2.2).map fun v => (ral.1, ka, v)).bind fun dEdges =>
  (p.negDataAssertions.mapM fun ral => (lu ral.2.1).bind fun ka => (decodeLiteral ral.2.2).map fun v => (ral.1, ka, v)).map fun negDEdges =>
  { labels := (0, p.root) ::
      ns.map (fun (a, k) => (k, .nom (.named a) true)) ++
      as.map (fun (a, k) => (k, .nom (.anonymous a.1 a.2) true)) ++
      caLabels ++ sameLabels
    edges := objEdges
    negEdges := negObjEdges
    unequal := diffPairs
    expanded := []
    noms := ns
    anons := as
    dataEdges := dEdges
    negDataEdges := negDEdges
    dataConstraints := [] }

theorem initial_sat {p : Problem} {s : Branch} (hi : initial p = some s) (hp : p.Sat) :
    s.Sat p := by
  obtain ⟨i, hm, x0, hx0⟩ := hp
  let ns := p.nominals
  let ans := p.anons
  let env : Nat → i.Object
    | 0 => x0
    | k + 1 =>
      if k < ns.length then
        match ns[k]? with | some a => i.individuals (.named a) | none => x0
      else
        match ans[k - ns.length]? with | some a => i.individuals (.anonymous a.1 a.2) | none => x0
  have hnom : ∀ a k, (a, k) ∈ ns.zipIdx 1 → env k = i.individuals (.named a) := fun a k hk => by
    obtain ⟨j, hj, rfl, hget⟩ := zipIdx_index_eq ns 1 hk
    have h1 : 1 + j = j + 1 := Nat.add_comm 1 j
    rw [h1]
    simp only [env, hj, ↓reduceIte, hget]
  have hanon : ∀ a k, (a, k) ∈ ans.zipIdx (1 + ns.length) → env k = i.individuals (.anonymous a.1 a.2) := fun a k hk => by
    obtain ⟨j, _, rfl, hget⟩ := zipIdx_index_eq ans (1 + ns.length) hk
    have h1 : 1 + ns.length + j = (ns.length + j) + 1 := by omega
    have h2 : ¬ (ns.length + j < ns.length) := by omega
    have h3 : ns.length + j - ns.length = j := by omega
    rw [h1]
    simp only [env, h2, ↓reduceIte, h3, hget]
  have hlookup : ∀ ind k, lookupInd (ns.zipIdx 1) (ans.zipIdx (1 + ns.length)) ind = some k →
      env k = i.individuals ind := fun ind k hk => by
    cases ind with
    | named a => exact hnom a k (mem_of_lookup_eq_some hk)
    | anonymous doc lid => exact hanon (doc, lid) k (mem_of_lookup_eq_some hk)
  unfold initial at hi
  obtain ⟨caLabels, hca, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨sameLabels, hsame, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨objEdges, hoa, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨negObjEdges, hnoa, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨diffPairs, hdiff, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨dEdges, hda, hi⟩ := Option.bind_eq_some_iff.mp hi
  obtain ⟨negDEdges, hnda, rfl⟩ := Option.map_eq_some_iff.mp hi
  refine ⟨i, hm, env, ⟨?_, ?_, ?_, ?_, hnom, hanon, ?_, ?_, by simp⟩⟩
  · -- labels
    intro n c hmem
    simp only [List.mem_append, List.mem_cons] at hmem
    rcases hmem with (((hroot | hns) | has) | hcm) | hsm
    · cases hroot; exact hx0
    · obtain ⟨⟨a, k⟩, hk, heq⟩ := List.mem_map.mp hns
      cases heq
      exact hnom a k hk
    · obtain ⟨⟨a, k⟩, hk, heq⟩ := List.mem_map.mp has
      cases heq
      exact hanon a k hk
    · obtain ⟨⟨a, c'⟩, hac, hfa⟩ := mapM_mem_iff hca hcm
      obtain ⟨k, hl, heq⟩ := Option.map_eq_some_iff.mp hfa
      cases heq
      rw [hlookup _ _ hl]
      exact hm.classAssertions (a, c') hac
    · obtain ⟨⟨a, b⟩, hab, hfa⟩ := mapM_mem_iff hsame hsm
      obtain ⟨k, hl, heq⟩ := Option.map_eq_some_iff.mp hfa
      cases heq
      rw [hlookup _ _ hl]
      exact hm.sameInds (a, b) hab
  · -- edges
    intro r x y hmem
    obtain ⟨⟨r', a, b⟩, hrab, hfa⟩ := mapM_mem_iff hoa hmem
    obtain ⟨ka, hla, hfa⟩ := Option.bind_eq_some_iff.mp hfa
    obtain ⟨kb, hlb, heq⟩ := Option.map_eq_some_iff.mp hfa
    cases heq
    rw [hlookup _ _ hla, hlookup _ _ hlb]
    exact hm.objAssertions (r', a, b) hrab
  · -- negEdges
    intro r x y hmem
    obtain ⟨⟨r', a, b⟩, hrab, hfa⟩ := mapM_mem_iff hnoa hmem
    obtain ⟨ka, hla, hfa⟩ := Option.bind_eq_some_iff.mp hfa
    obtain ⟨kb, hlb, heq⟩ := Option.map_eq_some_iff.mp hfa
    cases heq
    rw [hlookup _ _ hla, hlookup _ _ hlb]
    exact hm.negObjAssertions (r', a, b) hrab
  · -- unequal
    intro x y hmem
    obtain ⟨⟨a, b⟩, hab, hfa⟩ := mapM_mem_iff hdiff hmem
    obtain ⟨ka, hla, hfa⟩ := Option.bind_eq_some_iff.mp hfa
    obtain ⟨kb, hlb, heq⟩ := Option.map_eq_some_iff.mp hfa
    cases heq
    rw [hlookup _ _ hla, hlookup _ _ hlb]
    exact hm.diffInds (a, b) hab
  · -- dataEdges
    intro dp x v hmem
    obtain ⟨⟨dp', a, l⟩, hral, hfa⟩ := mapM_mem_iff hda hmem
    obtain ⟨ka, hla, hfa⟩ := Option.bind_eq_some_iff.mp hfa
    obtain ⟨v', hdl, heq⟩ := Option.map_eq_some_iff.mp hfa
    cases heq
    rw [hlookup _ _ hla, ← i.lexicalAgreement l _ hdl]
    exact hm.dataAssertions (dp', a, l) hral
  · -- negDataEdges
    intro dp x v hmem
    obtain ⟨⟨dp', a, l⟩, hral, hfa⟩ := mapM_mem_iff hnda hmem
    obtain ⟨ka, hla, hfa⟩ := Option.bind_eq_some_iff.mp hfa
    obtain ⟨v', hdl, heq⟩ := Option.map_eq_some_iff.mp hfa
    cases heq
    rw [hlookup _ _ hla, ← i.lexicalAgreement l _ hdl]
    exact hm.negDataAssertions (dp', a, l) hral

def Branch.support (s : Branch) : List Nat :=
  s.labels.map Prod.fst ++
  s.edges.flatMap (fun (_, x, y) => [x, y]) ++
  s.negEdges.flatMap (fun (_, x, y) => [x, y]) ++
  s.unequal.flatMap (fun (x, y) => [x, y]) ++
  s.noms.map Prod.snd ++
  s.anons.map Prod.snd ++
  s.dataEdges.map (fun (_, x, _) => x) ++
  s.negDataEdges.map (fun (_, x, _) => x) ++
  s.dataConstraints.map (fun (x, _, _) => x)

private theorem le_maximum (xs : List Nat) {x : Nat} (h : x ∈ xs) :
    x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons a tail ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

private def Branch.fresh (s : Branch) : Nat := s.support.foldr max 0 + 1

private theorem Branch.lt_fresh (s : Branch) {x : Nat} (h : x ∈ s.support) :
    x < s.fresh := Nat.lt_succ_of_le (le_maximum _ h)

def Branch.nodes (s : Branch) : List Nat :=
  (List.range s.fresh).filter s.support.contains

theorem Branch.nodes_nodup (s : Branch) : s.nodes.Nodup :=
  List.filter_sublist.nodup (List.nodup_range ..)

theorem Branch.mem_nodes {s : Branch} {x : Nat} : x ∈ s.nodes ↔ x ∈ s.support := by
  simp only [Branch.nodes, List.mem_filter, List.mem_range, List.contains_iff_mem]
  exact ⟨And.right, fun h => ⟨s.lt_fresh h, h⟩⟩

theorem Branch.label_support {s : Branch} {x : Nat} {c : Concept}
    (h : (x, c) ∈ s.labels) : x ∈ s.support := by
  simp only [Branch.support, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem h))))))))

private theorem Branch.realizes_congr {s : Branch} {i : Interpretation datatypeMap}
    {env env' : Nat → i.Object} (h : s.Realizes i env)
    (agree : ∀ n ∈ s.support, env' n = env n) : s.Realizes i env' := by
  have hsup : ∀ {n}, n ∈ s.support → env' n = env n := fun hn => agree _ hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x c he
    rw [hsup (Branch.label_support he)]; exact h.labels x c he
  · intro r x y he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(r, x, y), he, by simp⟩))))))))
    have hy : y ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(r, x, y), he, by simp⟩))))))))
    rw [hsup hx, hsup hy]; exact h.edges r x y he
  · intro r x y he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(r, x, y), he, by simp⟩)))))))
    have hy : y ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(r, x, y), he, by simp⟩)))))))
    rw [hsup hx, hsup hy]; exact h.negEdges r x y he
  · intro x y he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(x, y), he, by simp⟩))))))
    have hy : y ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨(x, y), he, by simp⟩))))))
    rw [hsup hx, hsup hy]; exact h.unequal x y he
  · intro a x he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem he)))))
    rw [hsup hx]; exact h.noms a x he
  · intro k x he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem he))))
    rw [hsup hx]; exact h.anons k x he
  · intro dp x v he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem he)))
    rw [hsup hx]; exact h.dataEdges dp x v he
  · intro dp x v he
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem he))
    rw [hsup hx]; exact h.negDataEdges dp x v he
  · intro x dp d he y hy
    have hx : x ∈ s.support := by
      simp only [Branch.support, List.mem_append]
      exact Or.inr (List.mem_map_of_mem he)
    rw [hsup hx] at hy
    exact h.dataConstraints x dp d he y hy

def Branch.known (s : Branch) (x : Nat) (c : Concept) : Bool :=
  match c with
  | .top => true
  | _ => s.labels.contains (x, c)

def Branch.add (s : Branch) (x : Nat) (c : Concept) : Branch :=
  if s.known x c then s else { s with labels := (x, c) :: s.labels }

theorem Branch.add_realizes {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {x : Nat} {c : Concept} (h : s.Realizes i env) (hc : holds i (env x) c) :
    (s.add x c).Realizes i env := by
  unfold Branch.add
  split
  · exact h
  · refine ⟨?_, h.edges, h.negEdges, h.unequal, h.noms, h.anons, h.dataEdges, h.negDataEdges, h.dataConstraints⟩
    intro n d hn
    rcases List.mem_cons.mp hn with heq | hn
    · cases heq; exact hc
    · exact h.labels n d hn

theorem Branch.known_sound {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {x : Nat} {c : Concept} (h : s.Realizes i env) (hk : s.known x c = true) :
    holds i (env x) c := by
  cases c with
  | top => trivial
  | _ => exact h.labels x _ (List.contains_iff_mem.mp hk)

def Branch.edge (s : Branch) (r : OrientedRole) (x y : Nat) : Bool :=
  if r.2 then s.edges.contains (r.1, y, x) else s.edges.contains (r.1, x, y)

def Branch.addEdge (s : Branch) (r : IRI) (x y : Nat) : Branch :=
  if s.edges.contains (r, x, y) then s else { s with edges := (r, x, y) :: s.edges }

theorem Branch.addEdge_realizes {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {r : IRI} {x y : Nat} (h : s.Realizes i env)
    (he : i.objectProperties r (env x) (env y)) : (s.addEdge r x y).Realizes i env := by
  unfold Branch.addEdge
  split
  · exact h
  · refine ⟨h.labels, ?_, h.negEdges, h.unequal, h.noms, h.anons, h.dataEdges, h.negDataEdges, h.dataConstraints⟩
    intro t a b hm
    rcases List.mem_cons.mp hm with hEq | hm
    · cases hEq; exact he
    · exact h.edges t a b hm

theorem Branch.edge_sound {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {r : OrientedRole} {x y : Nat} (h : s.Realizes i env) (he : s.edge r x y = true) :
    holdsOriented i r (env x) (env y) := by
  rcases r with ⟨r, _ | _⟩
  · exact h.edges r x y (List.contains_iff_mem.mp he)
  · exact h.edges r y x (List.contains_iff_mem.mp he)

def Branch.addOriented (s : Branch) (r : OrientedRole) (x y : Nat) : Branch :=
  if r.2 then s.addEdge r.1 y x else s.addEdge r.1 x y

theorem Branch.addOriented_realizes {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {r : OrientedRole} {x y : Nat} (h : s.Realizes i env)
    (he : holdsOriented i r (env x) (env y)) : (s.addOriented r x y).Realizes i env := by
  rcases r with ⟨r, _ | _⟩ <;> exact Branch.addEdge_realizes h he

def Branch.addDataEdge (s : Branch) (dp : IRI) (x : Nat) (v : Value) : Branch :=
  if s.dataEdges.contains (dp, x, v) then s
  else { s with dataEdges := (dp, x, v) :: s.dataEdges }

theorem Branch.addDataEdge_realizes {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {dp : IRI} {x : Nat} {v : Value} (h : s.Realizes i env)
    (he : i.dataProperties dp (env x) (i.embedValue v)) :
    (s.addDataEdge dp x v).Realizes i env := by
  unfold Branch.addDataEdge
  split
  · exact h
  · refine ⟨h.labels, h.edges, h.negEdges, h.unequal, h.noms, h.anons, ?_, h.negDataEdges, h.dataConstraints⟩
    intro r a w hm
    rcases List.mem_cons.mp hm with hEq | hm
    · cases hEq; exact he
    · exact h.dataEdges r a w hm

def Branch.addNegDataEdge (s : Branch) (dp : IRI) (x : Nat) (v : Value) : Branch :=
  if s.negDataEdges.contains (dp, x, v) then s
  else { s with negDataEdges := (dp, x, v) :: s.negDataEdges }

theorem Branch.addNegDataEdge_realizes {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {dp : IRI} {x : Nat} {v : Value} (h : s.Realizes i env)
    (he : ¬ i.dataProperties dp (env x) (i.embedValue v)) :
    (s.addNegDataEdge dp x v).Realizes i env := by
  unfold Branch.addNegDataEdge
  split
  · exact h
  · refine ⟨h.labels, h.edges, h.negEdges, h.unequal, h.noms, h.anons, h.dataEdges, ?_, h.dataConstraints⟩
    intro r a w hm
    rcases List.mem_cons.mp hm with hEq | hm
    · cases hEq; exact he
    · exact h.negDataEdges r a w hm

def Branch.addDataConstraint (s : Branch) (x : Nat) (dp : IRI) (d : DataRange) : Branch :=
  if s.dataConstraints.contains (x, dp, d) then s
  else { s with dataConstraints := (x, dp, d) :: s.dataConstraints }

theorem Branch.addDataConstraint_realizes {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} {x : Nat} {dp : IRI} {d : DataRange} (h : s.Realizes i env)
    (he : ∀ y, i.dataProperties dp (env x) y → dataHolds i y d) :
    (s.addDataConstraint x dp d).Realizes i env := by
  unfold Branch.addDataConstraint
  split
  · exact h
  · refine ⟨h.labels, h.edges, h.negEdges, h.unequal, h.noms, h.anons, h.dataEdges, h.negDataEdges, ?_⟩
    intro a r t hm
    rcases List.mem_cons.mp hm with hEq | hm
    · cases hEq; exact he
    · exact h.dataConstraints a r t hm

def Branch.targets (s : Branch) (x : Nat) : List OrientedRole → List Nat
  | [] => [x]
  | r :: rs => (s.edges.filterMap fun (name, a, b) =>
      let source := if r.2 then b else a
      let target := if r.2 then a else b
      if name == r.1 && source == x then some target else none).flatMap
      fun y => s.targets y rs

theorem Branch.targets_sound {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {x y : Nat} {rs : List OrientedRole} (h : s.Realizes i env) (ht : y ∈ s.targets x rs) :
    objPath i rs (env x) (env y) := by
  induction rs generalizing x with
  | nil =>
    have he := List.mem_singleton.mp ht
    subst he; rfl
  | cons r tail ih =>
    rcases r with ⟨r, _ | _⟩ <;>
      simp only [Branch.targets, List.mem_flatMap, List.mem_filterMap, Bool.false_eq_true,
        ↓reduceIte] at ht
    all_goals
      obtain ⟨z, ⟨⟨name, a, b⟩, he, hm⟩, hrest⟩ := ht
      split at hm
      · rename_i hmatch
        obtain ⟨hname, hsource⟩ := Bool.and_eq_true_iff.mp hmatch
        have hname := beq_iff_eq.mp hname
        have hsource := beq_iff_eq.mp hsource
        have htarget := Option.some.inj hm
        refine ⟨env z, ?_, ih hrest⟩
        dsimp only at hname hsource htarget
        subst name x z
        exact h.edges _ _ _ he
      · contradiction

private def retarget (keep drop n : Nat) : Nat := if n = drop then keep else n

private theorem env_retarget {α : Type} {env : Nat → α} {keep drop : Nat}
    (he : env keep = env drop) (n : Nat) : env (retarget keep drop n) = env n := by
  unfold retarget
  split
  · rename_i h; subst h; exact he
  · rfl

private def eraseBranchDupsFast {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] [Hashable β] [LawfulHashable β]
    (key : α → β) (xs : List α) : List α :=
  go xs {} []
where
  go : List α → Std.HashMap β (List α) → List α → List α
    | [], _, kept => kept.reverse
    | a :: rest, seen, kept =>
      let bucket := seen.getD (key a) []
      if bucket.contains a then go rest seen kept
      else go rest (seen.insert (key a) (a :: bucket)) (a :: kept)

private def eraseBranchDups {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] [Hashable β] [LawfulHashable β]
    (_key : α → β) (xs : List α) : List α := xs.eraseDups

/-- Bucket the equality checks while preserving the first occurrence and list order. -/
@[csimp] private theorem eraseBranchDups_eq : @eraseBranchDups = @eraseBranchDupsFast := by
  funext α β _ _ _ _ _ _ key xs
  have sameLoop (todo : List α) (seen : Std.HashMap β (List α)) (kept : List α)
      (h : ∀ a, a ∈ seen.getD (key a) [] ↔ a ∈ kept) :
      eraseBranchDupsFast.go key todo seen kept = List.eraseDupsBy.loop (· == ·) todo kept := by
    induction todo generalizing seen kept with
    | nil => rfl
    | cons a rest ih =>
      have hc : (seen.getD (key a) []).contains a = kept.any (a == ·) := by
        apply Bool.eq_iff_iff.mpr
        simpa [List.contains_iff_mem, List.any_eq_true, beq_iff_eq] using h a
      simp only [eraseBranchDupsFast.go, List.eraseDupsBy.loop, hc]
      cases kept.any (a == ·)
      · apply ih
        intro b
        simp only [Std.HashMap.getD_insert, beq_iff_eq]
        by_cases hk : key a = key b
        · simp [hk, h b]
        · have hab : b ≠ a := fun e => hk (congrArg key e.symm)
          simp [hk, hab, h b]
      · exact ih _ _ h
  exact (sameLoop xs {} [] (by simp)).symm

/-- Merge `drop` into `keep`, preserving all object labels, object edges,
    negative object edges, inequalities, nominal/anonymous bindings, data edges,
    negative data edges, and data constraints. -/
def Branch.merge (s : Branch) (keep drop : Nat) : Branch :=
  let move := retarget keep drop
  { labels := eraseBranchDups Prod.fst (s.labels.map fun (x, c) => (move x, c))
    edges := eraseBranchDups id (s.edges.map fun (r, x, y) => (r, move x, move y))
    negEdges := eraseBranchDups id (s.negEdges.map fun (r, x, y) => (r, move x, move y))
    unequal := eraseBranchDups id (s.unequal.map fun (x, y) => (move x, move y))
    expanded := eraseBranchDups Prod.fst (s.expanded.map fun (x, c) => (move x, c))
    noms := eraseBranchDups id (s.noms.map fun (a, x) => (a, move x))
    anons := eraseBranchDups id (s.anons.map fun (k, x) => (k, move x))
    dataEdges := eraseBranchDups (fun (dp, x, _) => (dp, x)) (s.dataEdges.map fun (dp, x, v) => (dp, move x, v))
    negDataEdges := eraseBranchDups (fun (dp, x, _) => (dp, x)) (s.negDataEdges.map fun (dp, x, v) => (dp, move x, v))
    dataConstraints := eraseBranchDups (fun (x, dp, _) => (x, dp)) (s.dataConstraints.map fun (x, dp, d) => (move x, dp, d)) }

theorem Branch.merge_realizes {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {keep drop : Nat} (h : s.Realizes i env) (he : env keep = env drop) :
    (s.merge keep drop).Realizes i env := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x c hm
    obtain ⟨⟨a, d⟩, ha, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he]; exact h.labels _ _ ha
  · intro r x y hm
    obtain ⟨⟨t, a, b⟩, ha, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he, env_retarget he]; exact h.edges _ _ _ ha
  · intro r x y hm
    obtain ⟨⟨t, a, b⟩, ha, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he, env_retarget he]; exact h.negEdges _ _ _ ha
  · intro x y hm
    obtain ⟨⟨a, b⟩, ha, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he, env_retarget he]; exact h.unequal _ _ ha
  · intro a x hm
    obtain ⟨⟨b, y⟩, hb, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he]; exact h.noms _ _ hb
  · intro k x hm
    obtain ⟨⟨b, y⟩, hb, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he]; exact h.anons _ _ hb
  · intro dp x v hm
    obtain ⟨⟨r, y, w⟩, hb, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he]; exact h.dataEdges _ _ _ hb
  · intro dp x v hm
    obtain ⟨⟨r, y, w⟩, hb, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he]; exact h.negDataEdges _ _ _ hb
  · intro x dp d hm y hy
    obtain ⟨⟨a, r, t⟩, hb, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp hm)
    cases heq
    rw [env_retarget he] at hy
    exact h.dataConstraints _ _ _ hb y hy

def distinctPairs (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap fun a => xs.filterMap fun b => if a == b then none else some (a, b)

theorem mem_distinctPairs {xs : List Nat} {a b : Nat} :
    (a, b) ∈ distinctPairs xs ↔ a ∈ xs ∧ b ∈ xs ∧ a ≠ b := by
  simp only [distinctPairs, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, y, hy, hm⟩
    split at hm
    · contradiction
    · rename_i hne
      cases hm
      exact ⟨hx, hy, by simpa using hne⟩
  · rintro ⟨ha, hb, hne⟩
    refine ⟨a, ha, b, hb, ?_⟩
    simp [hne]

def Branch.allocate (s : Branch) (x : Nat) (r : OrientedRole) (body mark : Concept) (count : Nat)
    (distinct : Bool) : Branch :=
  let start := s.fresh
  let freshNodes := (List.range count).map (start + ·)
  { s with
    labels := freshNodes.map (·, body) ++ s.labels
    edges := freshNodes.map (fun y => if r.2 then (r.1, y, x) else (r.1, x, y)) ++ s.edges
    unequal := (if distinct then distinctPairs freshNodes else []) ++ s.unequal
    expanded := (x, mark) :: s.expanded }

private def assignFresh {α : Type} (base : Nat → α) (start : Nat) (values : List α)
    (n : Nat) : α :=
  if h : start ≤ n ∧ n - start < values.length then values[n - start]'h.2 else base n

private theorem assignFresh_old {α : Type} {base : Nat → α} {start : Nat} {values : List α}
    {n : Nat} (h : n < start) : assignFresh base start values n = base n := by
  have hn : ¬ (start ≤ n ∧ n - start < values.length) := fun ha => Nat.not_le_of_lt h ha.1
  simp [assignFresh, hn]

private theorem assignFresh_new {α : Type} {base : Nat → α} {start : Nat} {values : List α}
    {k : Nat} (h : k < values.length) :
    assignFresh base start values (start + k) = values[k] := by
  have ha : start ≤ start + k ∧ start + k - start < values.length :=
    ⟨Nat.le_add_right .., by simpa using h⟩
  simp [assignFresh, ha, h]

theorem Branch.allocate_sound {s : Branch} {i : Interpretation datatypeMap} {env : Nat → i.Object}
    {x : Nat} {r : OrientedRole} {body mark : Concept} (h : s.Realizes i env) (count : Nat)
    (distinct : Bool) (values : List i.Object) (hlen : values.length = count)
    (hnd : distinct = true → values.Nodup)
    (hq : ∀ y ∈ values, holdsOriented i r (env x) y ∧ holds i y body)
    (hx : x ∈ s.support) :
    ∃ env', (s.allocate x r body mark count distinct).Realizes i env' := by
  let start := s.fresh
  let env' := assignFresh env start values
  have hkeep (n : Nat) (hn : n ∈ s.support) : env' n = env n :=
    assignFresh_old (s.lt_fresh hn)
  have hold := Branch.realizes_congr h hkeep
  refine ⟨env', ⟨?_, ?_, hold.negEdges, ?_, hold.noms, hold.anons, hold.dataEdges, hold.negDataEdges, hold.dataConstraints⟩⟩
  · intro n c hn
    rcases List.mem_append.mp hn with hnew | hprev
    · obtain ⟨y, hy, heq⟩ := List.mem_map.mp hnew
      cases heq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      have hk' : k < values.length := hlen.symm ▸ List.mem_range.mp hk
      dsimp only [env', start]
      rw [assignFresh_new hk']
      exact (hq _ (List.getElem_mem hk')).2
    · exact hold.labels n c hprev
  · intro t a b hn
    rcases List.mem_append.mp hn with hnew | hprev
    · obtain ⟨y, hy, heq⟩ := List.mem_map.mp hnew
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      have hk' : k < values.length := hlen.symm ▸ List.mem_range.mp hk
      rcases r with ⟨rn, _ | _⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hkeep x hx]
        dsimp only [env', start]
        rw [assignFresh_new hk']
        exact (hq _ (List.getElem_mem hk')).1
      · simp only [↓reduceIte, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hkeep x hx]
        dsimp only [env', start]
        rw [assignFresh_new hk']
        exact (hq _ (List.getElem_mem hk')).1
    · exact hold.edges t a b hprev
  · intro a b hn
    rcases List.mem_append.mp hn with hnew | hprev
    · cases distinct with
      | false => cases hnew
      | true =>
        obtain ⟨ha, hb, hne⟩ := mem_distinctPairs.mp hnew
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
        have hk' : k < values.length := hlen.symm ▸ List.mem_range.mp hk
        have hm' : m < values.length := hlen.symm ▸ List.mem_range.mp hm
        dsimp only [env', start]
        rw [assignFresh_new hk', assignFresh_new hm']
        intro heq
        have hkm : k = m := by
          have hinj : ∀ (l : List i.Object), l.Nodup →
              ∀ {i1 i2 : Nat} (h1 : i1 < l.length) (h2 : i2 < l.length), l[i1] = l[i2] → i1 = i2 := by
            intro l
            induction l with
            | nil => intro _ _ _ h1; exact (Nat.not_lt_zero _ h1).elim
            | cons x tail ih =>
              intro hn i1 i2 h1 h2 he
              rw [List.nodup_cons] at hn
              cases i1 with
              | zero =>
                cases i2 with
                | zero => rfl
                | succ j =>
                  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
                  exact (hn.1 (he ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ h2))).elim
              | succ j1 =>
                cases i2 with
                | zero =>
                  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
                  exact (hn.1 (he.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ h1))).elim
                | succ j2 =>
                  simp only [List.getElem_cons_succ] at he
                  exact congrArg Nat.succ (ih hn.2 (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) he)
          exact hinj values (hnd rfl) hk' hm' heq
        exact hne (congrArg (start + ·) hkm)
    · exact hold.unequal a b hprev

def Branch.allocateManySome (s : Branch) (items : List (Nat × OrientedRole × Concept)) : Branch :=
  let start := s.fresh
  let indexed := items.zipIdx start
  let newLabels := indexed.map fun ((_, _, body), y) => (y, body)
  let newEdges := indexed.map fun ((x, r, _), y) => if r.2 then (r.1, y, x) else (r.1, x, y)
  let newExpanded := items.map fun (x, r, body) => (x, .some r body)
  { s with
    labels := newLabels ++ s.labels
    edges := newEdges ++ s.edges
    expanded := newExpanded ++ s.expanded }

private theorem exists_some_witnesses {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} (h : s.Realizes i env)
    (items : List (Nat × OrientedRole × Concept))
    (hsub : ∀ item ∈ items, (item.1, .some item.2.1 item.2.2) ∈ s.labels) :
    ∃ values : List i.Object, values.length = items.length ∧
      ∀ (k : Nat) (hk : k < items.length) (hkv : k < values.length),
        holdsOriented i items[k].2.1 (env items[k].1) values[k] ∧ holds i values[k] items[k].2.2 := by
  induction items with
  | nil => exact ⟨[], rfl, fun _ hk _ => absurd hk (Nat.not_lt_zero _)⟩
  | cons hd tl ih =>
    obtain ⟨v, hv⟩ := h.labels hd.1 (.some hd.2.1 hd.2.2) (hsub hd (List.mem_cons_self ..))
    obtain ⟨vs, hlen, hrest⟩ := ih (fun it hm => hsub it (List.mem_cons_of_mem _ hm))
    refine ⟨v :: vs, by simp [hlen], fun k hk hkv => ?_⟩
    cases k with
    | zero => exact hv
    | succ k' => exact hrest k' (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hkv)

theorem Branch.allocateManySome_sound {s : Branch} {i : Interpretation datatypeMap}
    {env : Nat → i.Object} (h : s.Realizes i env)
    (items : List (Nat × OrientedRole × Concept))
    (hsub : ∀ item ∈ items, (item.1, .some item.2.1 item.2.2) ∈ s.labels) :
    ∃ env', (s.allocateManySome items).Realizes i env' := by
  obtain ⟨values, hlen, hvals⟩ := exists_some_witnesses h items hsub
  let start := s.fresh
  let env' := assignFresh env start values
  have hkeep (n : Nat) (hn : n ∈ s.support) : env' n = env n :=
    assignFresh_old (s.lt_fresh hn)
  have hold := Branch.realizes_congr h hkeep
  refine ⟨env', ⟨?_, ?_, hold.negEdges, hold.unequal, hold.noms, hold.anons,
    hold.dataEdges, hold.negDataEdges, hold.dataConstraints⟩⟩
  · intro n c hn
    rcases List.mem_append.mp hn with hnew | hprev
    · obtain ⟨⟨⟨x, r, body⟩, y⟩, hmem, heq⟩ := List.mem_map.mp hnew
      cases heq
      obtain ⟨k, hk, rfl, hget⟩ := zipIdx_index_eq items start hmem
      have hget' : items[k] = (x, r, c) := Option.some.inj (by simpa [hk] using hget)
      have hkv : k < values.length := hlen.symm ▸ hk
      dsimp only [env', start]
      rw [assignFresh_new hkv]
      have hw := (hvals k hk hkv).2
      rw [hget'] at hw
      exact hw
    · exact hold.labels n c hprev
  · intro t a b hn
    rcases List.mem_append.mp hn with hnew | hprev
    · obtain ⟨⟨⟨x, r, body⟩, y⟩, hmem, heq⟩ := List.mem_map.mp hnew
      obtain ⟨k, hk, rfl, hget⟩ := zipIdx_index_eq items start hmem
      have hget' : items[k] = (x, r, body) := Option.some.inj (by simpa [hk] using hget)
      have hkv : k < values.length := hlen.symm ▸ hk
      have hx : x ∈ s.support := by
        have hmemIt : (x, r, body) ∈ items := hget' ▸ List.getElem_mem hk
        exact Branch.label_support (hsub _ hmemIt)
      have hw := (hvals k hk hkv).1
      rw [hget'] at hw
      rcases r with ⟨rn, _ | _⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hkeep x hx]
        dsimp only [env', start]
        rw [assignFresh_new hkv]
        exact hw
      · simp only [↓reduceIte, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hkeep x hx]
        dsimp only [env', start]
        rw [assignFresh_new hkv]
        exact hw
    · exact hold.edges t a b hprev

theorem exists_equal_witnesses {α : Type} {env : Nat → α} {p : α → Prop} {n : Nat}
    {nodes : List Nat} (hlen : nodes.length = n + 1) (hnd : nodes.Nodup)
    (hp : ∀ x ∈ nodes, p (env x)) (hmax : ¬ AtLeast (n + 1) p) :
    ∃ a ∈ nodes, ∃ b ∈ nodes, a ≠ b ∧ env a = env b := by
  classical
  have hdup : ¬ (nodes.map env).Nodup := by
    intro hmap
    apply hmax
    refine ⟨nodes.map env, by simpa using hlen, hmap, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hp x hx
  have aux : ∀ xs : List Nat, xs.Nodup → ¬ (xs.map env).Nodup →
      ∃ a ∈ xs, ∃ b ∈ xs, a ≠ b ∧ env a = env b := by
    intro xs
    induction xs with
    | nil => intro _ h; exact (h List.nodup_nil).elim
    | cons x tail ih =>
      intro hn hnm
      rw [List.nodup_cons] at hn
      rw [List.map_cons, List.nodup_cons] at hnm
      by_cases hmem : env x ∈ tail.map env
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp hmem
        exact ⟨x, List.mem_cons_self .., y, List.mem_cons_of_mem _ hy,
          fun heq => hn.1 (heq ▸ hy), he.symm⟩
      · have htn : ¬ (tail.map env).Nodup := fun ht => hnm ⟨hmem, ht⟩
        obtain ⟨a, ha, b, hb, hne, he⟩ := ih hn.2 htn
        exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hne, he⟩
  exact aux nodes hnd hdup

end Sabrina.OWL2.SROIQD
