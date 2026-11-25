import Sabrina.Graded.Model

namespace Sabrina.Graded

open ALC RoleChains

structure Branch where
  labels : List (Nat × Concept)
  edges : List (String × Nat × Nat) := []
  unequal : List (Nat × Nat) := []
  expanded : List (Nat × Concept) := []
  noms : List (String × Nat) := []
  deriving Repr

/-- Initialize the root node `0` for `p.root` and a dedicated nominal root node
    `k + 1` for each nominal occurring in `p`. -/
def initial (p : Problem) : Branch :=
  let ns := p.nominals.zipIdx 1
  ⟨(0, p.root) :: ns.map (fun (a, k) => (k, .nom a true)), [], [], [], ns⟩

def Branch.Realizes (s : Branch) (i : Interpretation) (nom : String → i.Domain)
    (env : Nat → i.Domain) : Prop :=
  (∀ x c, (x,c) ∈ s.labels → Graded.holds i nom (env x) c) ∧
  (∀ r x y, (r,x,y) ∈ s.edges → i.role r (env x) (env y)) ∧
  (∀ x y, (x,y) ∈ s.unequal → env x ≠ env y) ∧
  ∀ a x, (a,x) ∈ s.noms → env x = nom a

def Branch.Sat (p : Problem) (s : Branch) : Prop :=
  ∃ (i : Interpretation) (nom : String → i.Domain),
    modelsRoles i p.rules ∧ modelsChains i p.chains ∧ modelsRoleChars i p.chars ∧
    Graded.models i nom p.tbox ∧ ∃ env, s.Realizes i nom env

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

theorem initial_sat {p : Problem} (h : p.Sat) : (initial p).Sat p := by
  obtain ⟨i, nom, hr, hc, hrc, ht, x, hx⟩ := h
  let ns := p.nominals
  let env : Nat → i.Domain
    | 0 => x
    | k + 1 => match ns[k]? with | some a => nom a | none => x
  refine ⟨i, nom, hr, hc, hrc, ht, env, ?_, by simp [initial], by simp [initial], ?_⟩
  · intro n c hn
    simp only [initial, List.mem_cons] at hn
    rcases hn with heq | hmem
    · cases heq; exact hx
    · obtain ⟨⟨a, k⟩, hk, heq⟩ := List.mem_map.mp hmem
      cases heq
      obtain ⟨j, _, rfl, hget⟩ := zipIdx_index_eq ns 1 hk
      simp [env, Nat.add_comm, hget, Graded.holds]
  · intro a k hk
    obtain ⟨j, _, rfl, hget⟩ := zipIdx_index_eq ns 1 hk
    simp [env, Nat.add_comm, hget]

def Branch.support (s : Branch) : List Nat :=
  ((s.labels.map Prod.fst ++ s.edges.flatMap (fun (_,x,y) => [x,y])) ++
    s.unequal.flatMap (fun (x,y) => [x,y])) ++ s.noms.map Prod.snd

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
  exact ⟨And.right,fun h => ⟨s.lt_fresh h,h⟩⟩

theorem Branch.label_support {s : Branch} {x : Nat} {c : Concept}
    (h : (x,c) ∈ s.labels) : x ∈ s.support :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h)))

private theorem Branch.realizes_congr {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env env' : Nat → i.Domain} (h : s.Realizes i nom env)
    (agree : ∀ n ∈ s.support, env' n = env n) : s.Realizes i nom env' := by
  have label {x c} (he : (x,c) ∈ s.labels) : x ∈ s.support :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem he)))
  have edge {r x y} (he : (r,x,y) ∈ s.edges) (n : Nat) (hn : n ∈ [x,y]) : n ∈ s.support :=
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(r,x,y),he,hn⟩)))
  have distinct {x y} (he : (x,y) ∈ s.unequal) (n : Nat) (hn : n ∈ [x,y]) : n ∈ s.support :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(x,y),he,hn⟩))
  have nomSup {a x} (he : (a,x) ∈ s.noms) : x ∈ s.support :=
    List.mem_append_right _ (List.mem_map_of_mem he)
  refine ⟨?_,?_,?_,?_⟩
  · intro x c he
    rw [agree x (label he)]
    exact h.1 x c he
  · intro r x y he
    rw [agree x (edge he x (by simp)), agree y (edge he y (by simp))]
    exact h.2.1 r x y he
  · intro x y he
    rw [agree x (distinct he x (by simp)), agree y (distinct he y (by simp))]
    exact h.2.2.1 x y he
  · intro a x he
    rw [agree x (nomSup he)]
    exact h.2.2.2 a x he

def Branch.add (s : Branch) (x : Nat) (c : Concept) : Branch :=
  {s with labels := (x,c) :: s.labels}

theorem Branch.add_realizes {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {x : Nat} {c : Concept}
    (hc : Graded.holds i nom (env x) c) : (s.add x c).Realizes i nom env := by
  refine ⟨?_,h.2⟩
  intro n c' hn
  rcases List.mem_cons.mp hn with he | hn
  · cases he
    exact hc
  · exact h.1 n c' hn

def Branch.known (s : Branch) (x : Nat) (c : Concept) : Bool :=
  c == .top || s.labels.contains (x,c)

theorem Branch.known_sound {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {x : Nat} {c : Concept}
    (hc : s.known x c = true) : Graded.holds i nom (env x) c := by
  rcases Bool.or_eq_true_iff.mp hc with he | hc
  · rw [beq_iff_eq.mp he]
    trivial
  · exact h.1 x c (List.contains_iff_mem.mp hc)

def Branch.addEdge (s : Branch) (r : String) (x y : Nat) : Branch :=
  {s with edges := (r,x,y) :: s.edges}

theorem Branch.addEdge_realizes {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {r : String} {x y : Nat}
    (he : i.role r (env x) (env y)) : (s.addEdge r x y).Realizes i nom env := by
  refine ⟨h.1,?_,h.2.2⟩
  intro t u v ht
  rcases List.mem_cons.mp ht with hh | ht
  · cases hh
    exact he
  · exact h.2.1 t u v ht

def Branch.addOriented (s : Branch) (r : OrientedRole) (x y : Nat) : Branch :=
  if r.2 then s.addEdge r.1 y x else s.addEdge r.1 x y

def Branch.edge (s : Branch) (r : OrientedRole) (x y : Nat) : Bool :=
  if r.2 then s.edges.contains (r.1,y,x) else s.edges.contains (r.1,x,y)

theorem Branch.edge_sound {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {r : OrientedRole} {x y : Nat}
    (he : s.edge r x y = true) : holdsRole i r (env x) (env y) := by
  rcases r with ⟨r,_ | _⟩
  · exact h.2.1 r x y (List.contains_iff_mem.mp he)
  · exact h.2.1 r y x (List.contains_iff_mem.mp he)

theorem Branch.addOriented_realizes {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {r : OrientedRole} {x y : Nat}
    (he : holdsRole i r (env x) (env y)) : (s.addOriented r x y).Realizes i nom env := by
  rcases r with ⟨r,_ | _⟩ <;> exact Branch.addEdge_realizes h he

def Branch.targets (s : Branch) (x : Nat) : List OrientedRole → List Nat
  | [] => [x]
  | h :: tail => (s.nodes.filter fun y => s.edge h x y).flatMap fun y =>
      s.targets y tail

theorem Branch.targets_sound {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {x y : Nat} {word : List OrientedRole}
    (he : y ∈ s.targets x word) : RoleChains.TransitivePaths.WordPath i word (env x) (env y) := by
  induction word generalizing x with
  | nil =>
    have eq : y = x := List.mem_singleton.mp he
    subst y
    rfl
  | cons a tail ih =>
    obtain ⟨z,hz,ht⟩ := List.mem_flatMap.mp he
    exact ⟨env z,Branch.edge_sound h (List.mem_filter.mp hz).2,ih ht⟩

/-- Enumerate both orientations of every pair of distinct node identifiers. -/
def distinctPairs (nodes : List Nat) : List (Nat × Nat) :=
  nodes.flatMap fun x => (nodes.filter (· != x)).map fun y => (x,y)

theorem mem_distinctPairs {nodes : List Nat} {x y : Nat} :
    (x,y) ∈ distinctPairs nodes ↔ x ∈ nodes ∧ y ∈ nodes ∧ x ≠ y := by
  simp only [distinctPairs,List.mem_flatMap,List.mem_map,List.mem_filter,bne_iff_ne,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,⟨hb,hn⟩,rfl,rfl⟩
    exact ⟨ha,hb,Ne.symm hn⟩
  · rintro ⟨hx,hy,hn⟩
    exact ⟨x,hx,y,⟨hy,Ne.symm hn⟩,rfl,rfl⟩

private def retarget (x y n : Nat) : Nat := if n = y then x else n

def Branch.merge (s : Branch) (x y : Nat) : Branch :=
  let f := retarget x y
  ⟨s.labels.map (fun (a,c) => (f a,c)),
   s.edges.map (fun (r,a,b) => (r,f a,f b)),
   s.unequal.map (fun (a,b) => (f a,f b)),
   s.expanded.map (fun (a,c) => (f a,c)),
   s.noms.map (fun (a,n) => (a,f n))⟩

theorem Branch.merge_realizes {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {x y : Nat} (he : env x = env y) :
    (s.merge x y).Realizes i nom env := by
  have same (n : Nat) : env (retarget x y n) = env n := by
    by_cases hn : n = y <;> simp [retarget, hn, he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n c hn
    obtain ⟨⟨a,d⟩,ha,eq⟩ := List.mem_map.mp hn
    cases eq
    simpa only [same] using h.1 a _ ha
  · intro r n m hn
    obtain ⟨⟨u,a,b⟩,ha,eq⟩ := List.mem_map.mp hn
    cases eq
    simpa only [same] using h.2.1 _ a b ha
  · intro n m hn
    obtain ⟨⟨a,b⟩,ha,eq⟩ := List.mem_map.mp hn
    cases eq
    simpa only [same] using h.2.2.1 a b ha
  · intro a n hn
    obtain ⟨⟨b,m⟩,hb,eq⟩ := List.mem_map.mp hn
    cases eq
    simpa only [same] using h.2.2.2 _ m hb

/-- A merged branch has precisely the realizations of the old branch with
    the selected names identified, preserving class labels, role edges,
    inequalities, and nominal bindings. -/
theorem Branch.merge_realizable_iff (s : Branch) (i : Interpretation) (nom : String → i.Domain)
    (x y : Nat) :
    (∃ env, (s.merge x y).Realizes i nom env) ↔
      ∃ env, s.Realizes i nom env ∧ env x = env y := by
  constructor
  · rintro ⟨env,h⟩
    refine ⟨fun n => env (retarget x y n),⟨?_,?_,?_,?_⟩,?_⟩
    · intro a c ha
      exact h.1 _ _ (List.mem_map_of_mem ha)
    · intro r a b hab
      exact h.2.1 _ _ _ (List.mem_map_of_mem hab)
    · intro a b hab
      exact h.2.2.1 _ _ (List.mem_map_of_mem hab)
    · intro a n han
      exact h.2.2.2 _ _ (List.mem_map_of_mem han)
    · by_cases he : x = y <;> simp [retarget, he]
  · rintro ⟨env,h,he⟩
    exact ⟨env,Branch.merge_realizes h he⟩

theorem nodup_map_of_injOn {α β : Type} {f : α → β} {xs : List α}
    (h : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tail ih =>
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨?_,ih h.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy))⟩
    intro ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp ha
    exact h.1 ((hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) he) ▸ hb)

theorem exists_equal_witnesses {α : Type} {env : Nat → α} {q : α → Prop}
    {n : Nat} {xs : List Nat} (hlen : xs.length = n) (hn : xs.Nodup)
    (hq : ∀ x ∈ xs, q (env x)) (hmax : ¬ AtLeast n q) :
    ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y ∧ env x = env y := by
  classical
  apply Classical.byContradiction
  intro h
  have hinj : ∀ x ∈ xs, ∀ y ∈ xs, env x = env y → x = y := by
    intro x hx y hy he
    exact Classical.byContradiction fun hn => h ⟨x,hx,y,hy,hn,he⟩
  apply hmax
  refine ⟨xs.map env,by simpa, nodup_map_of_injOn hn hinj,?_⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  exact hq x hx

def Branch.allocate (s : Branch) (p : Nat) (r : String) (c mark : Concept) (n : Nat)
    (distinct : Bool) : Branch :=
  let ns := (List.range n).map (s.fresh + ·)
  ⟨(ns.map fun x => (x,c)) ++ s.labels,
   (ns.map fun x => (r,p,x)) ++ s.edges,
   (if distinct then distinctPairs ns else []) ++ s.unequal,
   (p,mark) :: s.expanded,
   s.noms⟩

theorem Branch.allocate_sound {s : Branch} {i : Interpretation} {nom : String → i.Domain}
    {env : Nat → i.Domain} (h : s.Realizes i nom env) {p : Nat} {r : String}
    {c mark : Concept} (n : Nat) (separate : Bool)
    (values : List i.Domain) (hlen : values.length = n)
    (hn : separate = true → values.Nodup)
    (hq : ∀ x ∈ values, i.role r (env p) x ∧ Graded.holds i nom x c)
    (hp : p ∈ s.support) : ∃ env', (s.allocate p r c mark n separate).Realizes i nom env' := by
  let env' := fun x => if x < s.fresh then env x else (values[x - s.fresh]?).getD (env x)
  have agree (x : Nat) (hx : x ∈ s.support) : env' x = env x := by
    simp [env', s.lt_fresh hx]
  have point {j : Nat} (hj : j < n) : env' (s.fresh + j) = values[j]'(by omega) := by
    have he : ¬ s.fresh + j < s.fresh := by omega
    simp [env',he,List.getElem?_eq_getElem (by omega : j < values.length)]
  have known {j : Nat} (hj : j < n) :
      i.role r (env' p) (env' (s.fresh + j)) ∧ Graded.holds i nom (env' (s.fresh + j)) c := by
    rw [point hj, agree p hp]
    exact hq _ (List.getElem_mem ..)
  refine ⟨env',?_,?_,?_,?_⟩
  · intro x d he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨k,hk,eq⟩ := List.mem_map.mp he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
      cases eq
      exact (known (List.mem_range.mp hj)).2
    · exact (Branch.realizes_congr h agree).1 x d he
  · intro t x y he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨k,hk,eq⟩ := List.mem_map.mp he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
      cases eq
      exact (known (List.mem_range.mp hj)).1
    · exact (Branch.realizes_congr h agree).2.1 t x y he
  · intro x y he
    rcases List.mem_append.mp he with he | he
    · cases hs : separate
      · simp [hs] at he
      · rw [ite_eq_left hs] at he
        obtain ⟨hx,hy,hne⟩ := mem_distinctPairs.mp he
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hy
        have hj' := List.mem_range.mp hj
        have hk' := List.mem_range.mp hk
        rw [point hj',point hk']
        intro eq
        have same := (hn hs).eq_of_getElem_eq (by omega) (by omega) eq
        exact hne (by omega)
    · exact (Branch.realizes_congr h agree).2.2.1 x y he
  · exact (Branch.realizes_congr h agree).2.2.2

end Sabrina.Graded
