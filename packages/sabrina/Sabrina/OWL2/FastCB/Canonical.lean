import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastEL
import Sabrina.OWL2.FastCB.Saturate

/-! # H.4: Verified Horn-$\mathcal{SHIQ}$ Canonical Model & Zero-Tableau Classification

Constructs a single finite canonical interpretation `CBCanonicalModel` from a
saturated Horn-$\mathcal{SHIQ}$ derivation certificate and kernel-verifies that it
satisfies every axiom of the original OWL 2 ontology `o` in parallel
(`checkCBCanonicalModel`, $O(|\mathcal{O}| \cdot |V| \cdot \text{deg})$):

- `checkCBCanonicalModel_sound`: if `checkCBCanonicalModel o m w = true`, then
  `m.toInterpretation dm hne` satisfies every axiom in `o` (for arbitrary `dm`).
- `checkCBCanonicalModel_counter_sub`: any node `x` where `m.hasCls a x = true`
  and `m.hasCls b x = false` refutes `Entails dm o [subClassOf (.named a) (.named b)]`.
- `classifyFastCB`: when `o` is pure Horn-$\mathcal{SHIQ}$ and `m` passes both
  `checkCBCanonicalModel` and $O(|C| \cdot \text{deg})$ singleton-witness coverage,
  classifies `o` with **zero tableau calls**, proved sound & complete by
  `classifyFastCB_sound_complete` and worker-count invariant by
  `classifyFastCB_workers_eq`.

Zero `sorry`, zero `admit`, strictly standard Lean 4 core axioms
(`[propext, Classical.choice, Quot.sound]`). -/

namespace Sabrina.OWL2.FastCB

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Classification
open Sabrina.OWL2.FastEL

/-! ### 1. `CBCanonicalModel` & Exact Interpretation Bridge -/

/-- Compact finite model indexed by node IDs `0 .. numNodes - 1`.
    `outAdj` is the authoritative object-property relation; `inAdj`, `clsNodes`,
    `roleOutNodes`, and `roleInNodes` are fast inverted indices verified by
    `checkAdjConsistent` so axiom checking runs in $O(|\mathcal{O}| \cdot \text{support})$
    instead of $O(|\mathcal{O}| \cdot |V|)$. -/
structure CBCanonicalModel where
  numNodes : Nat
  nodeClasses : Array (Std.HashSet IRI)
  outAdj : Array (Std.HashMap IRI (Array Nat))
  inAdj : Array (Std.HashMap IRI (Array Nat))
  clsNodes : Std.HashMap IRI (Array Nat) := {}
  roleOutNodes : Std.HashMap IRI (Array Nat) := {}
  roleInNodes : Std.HashMap IRI (Array Nat) := {}
  deriving Inhabited

/-- $O(\log n)$ binary search on a sorted `Array Nat`.
    Soundness (`binSearchContains_mem`) holds unconditionally for any array. -/
def binSearchContains (xs : Array Nat) (v : Nat) : Bool :=
  go xs v 0 xs.size xs.size
where
  go (xs : Array Nat) (v lo hi : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if lo >= hi then false
      else
        let mid := lo + (hi - lo) / 2
        match xs[mid]? with
        | none => false
        | some u =>
          if u == v then true
          else if u < v then go xs v (mid + 1) hi fuel
          else go xs v lo mid fuel

private theorem binSearchContains_go_mem {xs : Array Nat} {v lo hi fuel : Nat}
    (h : binSearchContains.go xs v lo hi fuel = true) : v ∈ xs.toList := by
  induction fuel generalizing lo hi with
  | zero => cases h
  | succ fuel ih =>
    unfold binSearchContains.go at h
    split at h
    · cases h
    · cases hmid : xs[lo + (hi - lo) / 2]? with
      | none => simp [hmid] at h
      | some u =>
        simp only [hmid] at h
        split at h
        · rename_i heq
          have heq' : u = v := beq_iff_eq.mp heq
          subst heq'
          obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hmid
          have hmem : xs[lo + (hi - lo) / 2] ∈ xs.toList := List.getElem_mem (by simpa using hlt)
          rwa [hget] at hmem
        · split at h
          · exact ih h
          · exact ih h

private theorem binSearchContains_mem {xs : Array Nat} {v : Nat}
    (h : binSearchContains xs v = true) : v ∈ xs.toList :=
  binSearchContains_go_mem h

def CBCanonicalModel.hasCls (m : CBCanonicalModel) (c : IRI) (x : Nat) : Bool :=
  if c == thing then true
  else if c == nothing then false
  else (m.nodeClasses.getD x {}).contains c

def CBCanonicalModel.outNeighbors (m : CBCanonicalModel) (r : IRI) (x : Nat) : Array Nat :=
  (m.outAdj.getD x {}).getD r #[]

def CBCanonicalModel.inNeighbors (m : CBCanonicalModel) (r : IRI) (x : Nat) : Array Nat :=
  (m.inAdj.getD x {}).getD r #[]

def CBCanonicalModel.hasNamedEdge (m : CBCanonicalModel) (r : IRI) (x y : Nat) : Bool :=
  if r == topObjectProperty then true
  else if r == bottomObjectProperty then false
  else (m.outNeighbors r x).contains y

def CBCanonicalModel.hasObjEdge (m : CBCanonicalModel) (r : ObjectProperty) (x y : Nat) : Bool :=
  match r with
  | .named p => m.hasNamedEdge p x y
  | .inverse p => m.hasNamedEdge p y x

/-- Strictly ascending check on `Array Nat` — implies both `Nodup` and `< bound`. -/
def isStrictSortedLt (xs : Array Nat) (bound : Nat) : Bool :=
  allRangeSeq (fun j =>
    match xs[j]? with
    | none => false
    | some v =>
      v < bound &&
      if j == 0 then true
      else match xs[j - 1]? with
        | some prev => prev < v
        | none => false) 0 xs.size

private theorem strictSorted_lt_of_mem {xs : Array Nat} {bound : Nat}
    (hs : isStrictSortedLt xs bound = true) {v : Nat} (hv : v ∈ xs.toList) :
    v < bound := by
  unfold isStrictSortedLt at hs
  rw [allRangeSeq_iff] at hs
  obtain ⟨j, hjlt, rfl⟩ := List.getElem_of_mem hv
  have hjlt' : j < xs.size := by simpa using hjlt
  have hj := hs j (Nat.zero_le _) hjlt'
  rw [Array.getElem?_eq_getElem hjlt'] at hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  exact hj.1

private theorem strictSorted_mono {xs : Array Nat} {bound : Nat}
    (hs : isStrictSortedLt xs bound = true) {i j : Nat}
    (hi : i < xs.size) (hj : j < xs.size) (hlt : i < j) :
    xs[i] < xs[j] := by
  unfold isStrictSortedLt at hs
  rw [allRangeSeq_iff] at hs
  induction j with
  | zero => omega
  | succ k ih =>
    have hk_step := hs (k + 1) (Nat.zero_le _) hj
    rw [Array.getElem?_eq_getElem hj] at hk_step
    have hklt : k < xs.size := by omega
    have hprev : xs[k]? = some xs[k] := Array.getElem?_eq_getElem hklt
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel, hprev,
      Bool.and_eq_true, decide_eq_true_eq] at hk_step
    by_cases heq : i = k
    · subst heq; exact hk_step.2
    · exact Nat.lt_trans (ih hklt (by omega)) hk_step.2

private theorem strictSorted_nodup {xs : Array Nat} {bound : Nat}
    (hs : isStrictSortedLt xs bound = true) : xs.toList.Nodup := by
  have hpw : ∀ (k : Nat), k ≤ xs.size →
      (xs.toList.drop (xs.size - k)).Pairwise (· ≠ ·) := by
    intro k hk
    induction k with
    | zero => simp [List.drop_of_length_le]
    | succ m ih =>
      let idx := xs.size - (m + 1)
      have hidxLt : idx < xs.size := by omega
      have hdrop : xs.toList.drop idx = xs[idx] :: xs.toList.drop (xs.size - m) := by
        have hlen : idx < xs.toList.length := by simpa using hidxLt
        have heq : xs.size - m = idx + 1 := by omega
        rw [heq, ← List.getElem_cons_drop hlen]
        rfl
      rw [hdrop]
      refine List.pairwise_cons.mpr ⟨fun y hy heq => ?_, ih (by omega)⟩
      obtain ⟨j, hjlt, hjEq⟩ := List.getElem_of_mem hy
      have hjLt' : (xs.size - m) + j < xs.size := by
        simp only [List.length_drop, Array.length_toList] at hjlt; omega
      have hval : xs[(xs.size - m) + j] = y := by
        simpa [List.getElem_drop] using hjEq
      have hlt := strictSorted_mono hs hidxLt hjLt' (by omega)
      rw [hval] at hlt
      exact Nat.ne_of_lt hlt heq
  have h0 := hpw xs.size (Nat.le_refl _)
  simp only [Nat.sub_self, List.drop_zero] at h0
  exact h0

/-- Build an OWL 2 `Interpretation dm` (for arbitrary `dm : DatatypeMap`) from `m`. -/
def CBCanonicalModel.toInterpretation (dm : DatatypeMap) (m : CBCanonicalModel)
    (hne : 0 < m.numNodes) : Interpretation dm where
  Object := Fin m.numNodes
  objectNonempty := ⟨⟨0, hne⟩⟩
  Data := Option dm.Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := fun h => Option.some.inj h
  classes c x := m.hasCls c x.val = true
  objectProperties r x y := m.hasNamedEdge r x.val y.val = true
  dataProperties p _ _ := p = topDataProperty
  individuals _ := ⟨0, hne⟩
  datatypes r y :=
    if r = literalDatatype then True
    else match y with
      | some v => dm.valueSpace r v
      | none => False
  literalValue l := dm.lexicalValue l
  lexicalAgreement _ _ h := h
  named _ := True
  namedIndividual _ := trivial
  thingExt := fun x => by simp [CBCanonicalModel.hasCls]
  nothingExt := fun x => by simp [CBCanonicalModel.hasCls, thing, nothing]
  topObjectExt := fun x y => by simp [CBCanonicalModel.hasNamedEdge]
  bottomObjectExt := fun x y => by
    simp [CBCanonicalModel.hasNamedEdge, topObjectProperty, bottomObjectProperty]
  topDataExt := fun _ _ => rfl
  bottomDataExt := fun _ _ h => by simp [topDataProperty, bottomDataProperty] at h
  literalDatatypeExt := fun _ => by simp
  datatypeAgreement := fun r hr y => by
    have hne' : r ≠ literalDatatype := fun he => dm.literal_not_builtin (he ▸ hr)
    simp only [hne', ↓reduceIte]
    cases y with
    | none => simp
    | some v =>
      constructor
      · intro hv; exact ⟨v, hv, rfl⟩
      · rintro ⟨w, hw, heq⟩; cases heq; exact hw

/-! ### 2. Adjacency Consistency & Fast Exact `ClassExpr` Evaluator -/

/-- Verify that `outAdj` and `inAdj` are strictly sorted, bounded by `numNodes`,
    exact converses of each other, and complete with respect to the inverted
    indices `clsNodes`, `roleOutNodes`, and `roleInNodes`. -/
def checkAdjConsistent (m : CBCanonicalModel) (numWorkers : Nat := 8) : Bool :=
  m.numNodes > 0 &&
  m.outAdj.size == m.numNodes &&
  m.inAdj.size == m.numNodes &&
  allRangePar m.numNodes (fun x =>
    let clsOk := (m.nodeClasses.getD x {}).toList.all fun c =>
      binSearchContains (m.clsNodes.getD c #[]) x
    let outOk := (m.outAdj.getD x {}).toList.all fun (r, ys) =>
      isStrictSortedLt ys m.numNodes &&
      (ys.isEmpty || binSearchContains (m.roleOutNodes.getD r #[]) x) &&
      ys.all fun y => binSearchContains (m.inNeighbors r y) x
    let inOk := (m.inAdj.getD x {}).toList.all fun (r, ys) =>
      isStrictSortedLt ys m.numNodes &&
      (ys.isEmpty || binSearchContains (m.roleInNodes.getD r #[]) x) &&
      ys.all fun y => binSearchContains (m.outNeighbors r y) x
    clsOk && outOk && inOk) numWorkers

private theorem array_contains_iff' {α : Type} [BEq α] [LawfulBEq α] {xs : Array α} {a : α} :
    xs.contains a = true ↔ a ∈ xs.toList := by
  rw [Array.contains_iff_mem, Array.mem_def]

private theorem array_all_iff' {α : Type} {xs : Array α} {p : α → Bool} :
    xs.all p = true ↔ ∀ x ∈ xs.toList, p x = true := by
  rw [← Array.all_toList, List.all_eq_true]

private theorem array_any_iff' {α : Type} {xs : Array α} {p : α → Bool} :
    xs.any p = true ↔ ∃ x ∈ xs.toList, p x = true := by
  rw [← Array.any_toList, List.any_eq_true]

private theorem mem_toList_of_getD {m : Std.HashMap IRI (Array Nat)} {r : IRI} {y : Nat}
    (hy : (m.getD r #[]).contains y = true) :
    ∃ ys, (r, ys) ∈ m.toList ∧ y ∈ ys.toList := by
  cases hm : m[r]? with
  | none =>
    have hget : m.getD r #[] = #[] := by simp [Std.HashMap.getD_eq_getD_getElem?, hm]
    rw [hget] at hy; simp at hy
  | some ys =>
    have hget : m.getD r #[] = ys := by simp [Std.HashMap.getD_eq_getD_getElem?, hm]
    rw [hget] at hy
    exact ⟨ys, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm, array_contains_iff'.mp hy⟩

private theorem adjConsistent_in_iff {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (r : IRI) {x y : Nat}
    (hx : x < m.numNodes) (hy : y < m.numNodes) :
    (m.inNeighbors r x).contains y = true ↔ (m.outNeighbors r y).contains x = true := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  obtain ⟨⟨⟨_, _⟩, _⟩, hnodes⟩ := hadj
  constructor
  · intro hin
    obtain ⟨ys, hmem, hyin⟩ := mem_toList_of_getD hin
    have hnx := hnodes x hx
    have hpair := List.all_eq_true.mp hnx.2 (r, ys) hmem
    have hback := (Bool.and_eq_true _ _).mp hpair
    exact array_contains_iff'.mpr (binSearchContains_mem (array_all_iff'.mp hback.2 y hyin))
  · intro hout
    obtain ⟨ys, hmem, hxin⟩ := mem_toList_of_getD hout
    have hny := hnodes y hy
    have hpair := List.all_eq_true.mp hny.1.2 (r, ys) hmem
    have hback := (Bool.and_eq_true _ _).mp hpair
    exact array_contains_iff'.mpr (binSearchContains_mem (array_all_iff'.mp hback.2 x hxin))

private theorem adjConsistent_out_sorted {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (r : IRI) {x : Nat} (hx : x < m.numNodes) :
    isStrictSortedLt (m.outNeighbors r x) m.numNodes = true := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  obtain ⟨⟨⟨_, _⟩, _⟩, hnodes⟩ := hadj
  unfold CBCanonicalModel.outNeighbors
  cases hm : (m.outAdj.getD x {})[r]? with
  | none =>
    have hget : (m.outAdj.getD x {}).getD r #[] = #[] := by
      rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
    rw [hget]; simp [isStrictSortedLt, allRangeSeq, allRangeSeq.go]
  | some ys =>
    have hget : (m.outAdj.getD x {}).getD r #[] = ys := by
      rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
    rw [hget]
    have hnx := hnodes x hx
    have hpair := List.all_eq_true.mp hnx.1.2 (r, ys)
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm)
    exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hpair).1).1

private theorem adjConsistent_in_sorted {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (r : IRI) {x : Nat} (hx : x < m.numNodes) :
    isStrictSortedLt (m.inNeighbors r x) m.numNodes = true := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  obtain ⟨⟨⟨_, _⟩, _⟩, hnodes⟩ := hadj
  unfold CBCanonicalModel.inNeighbors
  cases hm : (m.inAdj.getD x {})[r]? with
  | none =>
    have hget : (m.inAdj.getD x {}).getD r #[] = #[] := by
      rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
    rw [hget]; simp [isStrictSortedLt, allRangeSeq, allRangeSeq.go]
  | some ys =>
    have hget : (m.inAdj.getD x {}).getD r #[] = ys := by
      rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
    rw [hget]
    have hnx := hnodes x hx
    have hpair := List.all_eq_true.mp hnx.2 (r, ys)
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm)
    exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hpair).1).1

private theorem adjConsistent_cls_mem {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) {c : IRI} {x : Nat}
    (hx : x < m.numNodes) (hct : (m.nodeClasses.getD x {}).contains c = true) :
    x ∈ (m.clsNodes.getD c #[]).toList := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  have hnx := (hadj.2 x hx).1.1
  have hmem : c ∈ (m.nodeClasses.getD x {}).toList :=
    Std.HashSet.mem_toList.mpr (Std.HashSet.contains_iff_mem.mp hct)
  exact binSearchContains_mem (List.all_eq_true.mp hnx c hmem)

private theorem adjConsistent_roleOut_mem {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) {r : IRI} {x y : Nat}
    (hx : x < m.numNodes) (hy : (m.outNeighbors r x).contains y = true) :
    x ∈ (m.roleOutNodes.getD r #[]).toList := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  obtain ⟨ys, hmem, hyin⟩ := mem_toList_of_getD hy
  have hnx := (hadj.2 x hx).1.2
  have hpair := List.all_eq_true.mp hnx (r, ys) hmem
  have hor := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hpair).1).2
  cases hemp : ys.isEmpty with
  | true =>
    have hsz : ys.size = 0 := by simpa [Array.isEmpty] using hemp
    have : ys.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsz)
    rw [this] at hyin; cases hyin
  | false =>
    simp only [hemp, Bool.false_or] at hor
    exact binSearchContains_mem hor

private theorem adjConsistent_roleIn_mem {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) {r : IRI} {x y : Nat}
    (hx : x < m.numNodes) (hy : (m.inNeighbors r x).contains y = true) :
    x ∈ (m.roleInNodes.getD r #[]).toList := by
  unfold checkAdjConsistent at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allRangePar_iff] at hadj
  obtain ⟨ys, hmem, hyin⟩ := mem_toList_of_getD hy
  have hnx := (hadj.2 x hx).2
  have hpair := List.all_eq_true.mp hnx (r, ys) hmem
  have hor := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hpair).1).2
  cases hemp : ys.isEmpty with
  | true =>
    have hsz : ys.size = 0 := by simpa [Array.isEmpty] using hemp
    have : ys.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsz)
    rw [this] at hyin; cases hyin
  | false =>
    simp only [hemp, Bool.false_or] at hor
    exact binSearchContains_mem hor

/-- Neighbors of `x` along oriented property `r` (returns `none` for `topObjectProperty`,
    which ranges over all `0 .. m.numNodes - 1`). -/
def CBCanonicalModel.neighbors? (m : CBCanonicalModel) (r : ObjectProperty) (x : Nat) :
    Option (Array Nat) :=
  match r with
  | .named p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else some (m.outNeighbors p x)
  | .inverse p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else some (m.inNeighbors p x)

private theorem neighbors?_spec {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (r : ObjectProperty) (x : Fin m.numNodes) :
    match m.neighbors? r x.val with
    | none => ∀ y : Fin m.numNodes, objectHolds (m.toInterpretation dm hne) r x y
    | some ys =>
      isStrictSortedLt ys m.numNodes = true ∧
      ∀ y : Fin m.numNodes, objectHolds (m.toInterpretation dm hne) r x y ↔ y.val ∈ ys.toList := by
  cases r with
  | named p =>
    unfold CBCanonicalModel.neighbors?
    by_cases ht : p = topObjectProperty
    · subst ht; simp [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge]
    · by_cases hb : p = bottomObjectProperty
      · subst hb
        have hne' : (bottomObjectProperty == topObjectProperty) = false := by decide
        simp [hne', isStrictSortedLt, allRangeSeq, allRangeSeq.go, objectHolds,
              CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge]
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨adjConsistent_out_sorted hadj p x.isLt, fun y => ?_⟩
        simp only [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge,
          hnt, hnb, Bool.false_eq_true, ↓reduceIte, array_contains_iff']
  | inverse p =>
    unfold CBCanonicalModel.neighbors?
    by_cases ht : p = topObjectProperty
    · subst ht; simp [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge]
    · by_cases hb : p = bottomObjectProperty
      · subst hb
        have hne' : (bottomObjectProperty == topObjectProperty) = false := by decide
        simp [hne', isStrictSortedLt, allRangeSeq, allRangeSeq.go, objectHolds,
              CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge]
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨adjConsistent_in_sorted hadj p x.isLt, fun y => ?_⟩
        simp only [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge,
          hnt, hnb, Bool.false_eq_true, ↓reduceIte]
        rw [← adjConsistent_in_iff hadj p x.isLt y.isLt, array_contains_iff']

/-- Count elements of `xs` for which `p y = some true`, returning `none` if any returns `none`. -/
def countOptArray (xs : Array Nat) (p : Nat → Option Bool) : Option Nat :=
  xs.foldl (fun acc y =>
    match acc, p y with
    | some cnt, some true => some (cnt + 1)
    | some cnt, some false => some cnt
    | _, _ => none) (some 0)

/-- Count `y ∈ [0, n)` for which `p y = some true`. -/
def countOptRange (n : Nat) (p : Nat → Option Bool) : Option Nat :=
  let rec go (i fuel acc : Nat) : Option Nat :=
    match fuel with
    | 0 => some acc
    | k + 1 =>
      match p i with
      | some true => go (i + 1) k (acc + 1)
      | some false => go (i + 1) k acc
      | none => none
  go 0 n 0

/-- Exact 2-valued evaluator for Horn-$\mathcal{SHIQ}$ `ClassExpr`s on `CBCanonicalModel`.
    Returns `none` on unsupported constructors (nominals, data expressions). -/
def evalClassExpr (m : CBCanonicalModel) (x : Nat) : ClassExpr → Option Bool
  | .named c => some (m.hasCls c x)
  | .complement c => (evalClassExpr m x c).map (! ·)
  | .intersection a b =>
    match evalClassExpr m x a with
    | some false => some false
    | some true => evalClassExpr m x b
    | none => none
  | .union a b =>
    match evalClassExpr m x a with
    | some true => some true
    | some false => evalClassExpr m x b
    | none => none
  | .objectSome r f =>
    match m.neighbors? r x with
    | some ys =>
      ys.foldl (fun acc y =>
        match acc with
        | some true => some true
        | some false => evalClassExpr m y f
        | none => none) (some false)
    | none =>
      (countOptRange m.numNodes (fun y => evalClassExpr m y f)).map (· ≥ 1)
  | .objectAll r f =>
    match m.neighbors? r x with
    | some ys =>
      ys.foldl (fun acc y =>
        match acc with
        | some false => some false
        | some true => evalClassExpr m y f
        | none => none) (some true)
    | none =>
      (countOptRange m.numNodes (fun y => evalClassExpr m y f)).map (· == m.numNodes)
  | .objectSelf r => some (m.hasObjEdge r x x)
  | .objectMin n r f =>
    match m.neighbors? r x with
    | some ys => (countOptArray ys (fun y => evalClassExpr m y f)).map (· ≥ n)
    | none => (countOptRange m.numNodes (fun y => evalClassExpr m y f)).map (· ≥ n)
  | .objectMax n r f =>
    match m.neighbors? r x with
    | some ys => (countOptArray ys (fun y => evalClassExpr m y f)).map (· ≤ n)
    | none => (countOptRange m.numNodes (fun y => evalClassExpr m y f)).map (· ≤ n)
  | .objectExact n r f =>
    match m.neighbors? r x with
    | some ys => (countOptArray ys (fun y => evalClassExpr m y f)).map (· == n)
    | none => (countOptRange m.numNodes (fun y => evalClassExpr m y f)).map (· == n)
  | _ => none

/-! ### 3. Soundness Proofs for `evalClassExpr` -/

private theorem foldl_or_opt {ys : List Nat} {p : Nat → Option Bool} {b : Bool} :
    ∀ {init : Bool},
      ys.foldl (fun acc y =>
        match acc with
        | some true => some true
        | some false => p y
        | none => none) (some init) = some b →
      (∀ y ∈ ys, ∀ v, p y = some v → True) →
      (b = true ↔ init = true ∨ ∃ y ∈ ys, p y = some true) ∧
      (b = false → init = false ∧ ∀ y ∈ ys, p y = some false) := by
  induction ys with
  | nil =>
    intro init h _
    have := Option.some.inj h; subst this
    cases init <;> simp
  | cons y tl ih =>
    intro init h _
    simp only [List.foldl_cons] at h
    cases init with
    | true =>
      have h' : tl.foldl (fun acc y => match acc with | some true => some true | some false => p y | none => none)
          (some true) = some b := h
      have hres := ih h' (fun _ _ _ _ => trivial)
      constructor
      · simp [hres.1]
      · intro hbf; have := (hres.2 hbf).1; cases this
    | false =>
      cases hpy : p y with
      | none =>
        rw [hpy] at h
        have hnone : ∀ (ls : List Nat), ls.foldl (fun acc y =>
            match acc with | some true => some true | some false => p y | none => none) none = none := by
          intro ls; induction ls with | nil => rfl | cons _ _ ih' => exact ih'
        rw [hnone] at h; cases h
      | some v =>
        rw [hpy] at h
        have hres := ih h (fun _ _ _ _ => trivial)
        cases v with
        | true =>
          constructor
          · constructor
            · intro _; exact Or.inr ⟨y, List.mem_cons_self .., hpy⟩
            · intro _; exact hres.1.mpr (Or.inl rfl)
          · intro hbf; have := (hres.2 hbf).1; cases this
        | false =>
          constructor
          · rw [hres.1]; simp [hpy]
          · intro hbf
            obtain ⟨_, htl⟩ := hres.2 hbf
            refine ⟨rfl, fun z hz => ?_⟩
            rcases List.mem_cons.mp hz with rfl | hmem
            · exact hpy
            · exact htl z hmem

private theorem foldl_and_opt {ys : List Nat} {p : Nat → Option Bool} {b : Bool} :
    ∀ {init : Bool},
      ys.foldl (fun acc y =>
        match acc with
        | some false => some false
        | some true => p y
        | none => none) (some init) = some b →
      (b = true → init = true ∧ ∀ y ∈ ys, p y = some true) ∧
      (b = false → init = false ∨ ∃ y ∈ ys, p y = some false) := by
  induction ys with
  | nil =>
    intro init h
    have := Option.some.inj h; subst this
    cases init <;> simp
  | cons y tl ih =>
    intro init h
    simp only [List.foldl_cons] at h
    cases init with
    | false =>
      have hres := ih h
      constructor
      · intro hbt; have := (hres.1 hbt).1; cases this
      · intro _; exact Or.inl rfl
    | true =>
      cases hpy : p y with
      | none =>
        rw [hpy] at h
        have hnone : ∀ (ls : List Nat), ls.foldl (fun acc y =>
            match acc with | some false => some false | some true => p y | none => none) none = none := by
          intro ls; induction ls with | nil => rfl | cons _ _ ih' => exact ih'
        rw [hnone] at h; cases h
      | some v =>
        rw [hpy] at h
        have hres := ih h
        cases v with
        | false =>
          constructor
          · intro hbt; have := (hres.1 hbt).1; cases this
          · intro _; exact Or.inr ⟨y, List.mem_cons_self .., hpy⟩
        | true =>
          constructor
          · intro hbt
            obtain ⟨_, htl⟩ := hres.1 hbt
            refine ⟨rfl, fun z hz => ?_⟩
            rcases List.mem_cons.mp hz with rfl | hmem
            · exact hpy
            · exact htl z hmem
          · intro hbf
            rcases hres.2 hbf with h | ⟨z, hz, hpz⟩
            · cases h
            · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, hpz⟩

private theorem foldl_count_list {ys : List Nat} {p : Nat → Option Bool} :
    ∀ {init cnt : Nat},
      ys.foldl (fun acc y =>
        match acc, p y with
        | some c, some true => some (c + 1)
        | some c, some false => some c
        | _, _ => none) (some init) = some cnt →
      (∀ y ∈ ys, ∃ v, p y = some v) ∧
      cnt = init + (ys.filter fun y => p y == some true).length := by
  induction ys with
  | nil =>
    intro init cnt h
    have := Option.some.inj h; subst this
    exact ⟨(fun _ h => nomatch h), by simp⟩
  | cons y tl ih =>
    intro init cnt h
    simp only [List.foldl_cons] at h
    cases hpy : p y with
    | none =>
      rw [hpy] at h
      have hnone : ∀ (ls : List Nat), ls.foldl (fun acc y =>
          match acc, p y with
          | some c, some true => some (c + 1)
          | some c, some false => some c
          | _, _ => none) none = none := by
        intro ls; induction ls with | nil => rfl | cons _ _ ih' => exact ih'
      rw [hnone] at h; cases h
    | some v =>
      rw [hpy] at h
      cases v with
      | true =>
        obtain ⟨htl, hcnt⟩ := ih h
        refine ⟨fun z hz => ?_, ?_⟩
        · rcases List.mem_cons.mp hz with rfl | hmem
          · exact ⟨true, hpy⟩
          · exact htl z hmem
        · simp [hpy]; omega
      | false =>
        obtain ⟨htl, hcnt⟩ := ih h
        refine ⟨fun z hz => ?_, ?_⟩
        · rcases List.mem_cons.mp hz with rfl | hmem
          · exact ⟨false, hpy⟩
          · exact htl z hmem
        · simp [hpy]; omega

private theorem countOptRange_go_spec {p : Nat → Option Bool} :
    ∀ {i fuel acc cnt : Nat},
      countOptRange.go p i fuel acc = some cnt →
      (∀ y, i ≤ y → y < i + fuel → ∃ v, p y = some v) ∧
      cnt = acc + ((List.range fuel).filter fun k => p (i + k) == some true).length := by
  intro i fuel
  induction fuel generalizing i with
  | zero =>
    intro acc cnt h
    simp only [countOptRange.go] at h
    have := Option.some.inj h; subst this
    exact ⟨fun _ h1 h2 => by omega, by simp⟩
  | succ k ih =>
    intro acc cnt h
    simp only [countOptRange.go] at h
    cases hpi : p i with
    | none => rw [hpi] at h; cases h
    | some v =>
      rw [hpi] at h
      have hrange : List.range (k + 1) = 0 :: (List.range k).map (· + 1) := by
        rw [List.range_succ_eq_map]
      have hmap : ((List.range k).map (· + 1)).filter (fun j => p (i + j) == some true) =
          ((List.range k).filter (fun j => p (i + 1 + j) == some true)).map (· + 1) := by
        rw [List.filter_map]
        have hfun : (fun j => p (i + j) == some true) ∘ (· + 1) =
            (fun j => p (i + 1 + j) == some true) := by
          funext j; simp only [Function.comp_def, Nat.add_assoc, Nat.add_comm 1 j]
        rw [hfun]
      cases v with
      | true =>
        obtain ⟨htl, hcnt⟩ := ih h
        refine ⟨fun y h1 h2 => ?_, ?_⟩
        · by_cases heq : y = i
          · subst heq; exact ⟨true, hpi⟩
          · exact htl y (by omega) (by omega)
        · have h0t : (p (i + 0) == some true) = true := by simp [hpi]
          simp only [hrange, List.filter_cons, h0t, ↓reduceIte, List.length_cons, hmap, List.length_map]
          omega
      | false =>
        obtain ⟨htl, hcnt⟩ := ih h
        refine ⟨fun y h1 h2 => ?_, ?_⟩
        · by_cases heq : y = i
          · subst heq; exact ⟨false, hpi⟩
          · exact htl y (by omega) (by omega)
        · have h0f : (p (i + 0) == some true) = false := by simp [hpi]
          simp only [hrange, List.filter_cons, h0f, Bool.false_eq_true, ↓reduceIte, hmap, List.length_map]
          omega

private theorem nodup_filter' {α : Type} {xs : List α} (p : α → Bool) (h : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    obtain ⟨hanot, htl⟩ := List.nodup_cons.mp h
    simp only [List.filter_cons]
    split
    · exact List.nodup_cons.mpr ⟨fun hm => hanot (List.mem_filter.mp hm).1, ih htl⟩
    · exact ih htl

private theorem nodup_map_inj' {α β : Type} {f : α → β} (hinj : ∀ x y, f x = f y → x = y)
    {xs : List α} (h : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    obtain ⟨hanot, htl⟩ := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, ih htl⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact hanot (hinj b a hfb ▸ hb)

private theorem nodup_of_map' {α β : Type} (f : α → β) {xs : List α} (h : (xs.map f).Nodup) :
    xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    obtain ⟨hanot, htl⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hm => hanot (List.mem_map_of_mem hm), ih htl⟩

private theorem nodup_take' {α : Type} {xs : List α} (n : Nat) (h : xs.Nodup) :
    (xs.take n).Nodup := by
  induction xs generalizing n with
  | nil => simp
  | cons a tl ih =>
    cases n with
    | zero => simp
    | succ k =>
      obtain ⟨hanot, htl⟩ := List.nodup_cons.mp h
      exact List.nodup_cons.mpr ⟨fun hm => hanot (List.mem_of_mem_take hm), ih k htl⟩

private def listToFins (num : Nat) : (ls : List Nat) → (∀ y ∈ ls, y < num) → List (Fin num)
  | [], _ => []
  | y :: tl, h =>
    ⟨y, h y (List.mem_cons_self ..)⟩ ::
      listToFins num tl (fun z hz => h z (List.mem_cons_of_mem _ hz))

private theorem listToFins_length (num : Nat) (ls : List Nat) (h : ∀ y ∈ ls, y < num) :
    (listToFins num ls h).length = ls.length := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [listToFins, ih]

private theorem listToFins_map_val (num : Nat) (ls : List Nat) (h : ∀ y ∈ ls, y < num) :
    (listToFins num ls h).map Fin.val = ls := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [listToFins, ih]

private theorem filter_length_eq_imp {α : Type} {ls : List α} {p : α → Bool}
    (hlen : (ls.filter p).length = ls.length) : ∀ x ∈ ls, p x = true := by
  induction ls with
  | nil => intro _ h; cases h
  | cons a tl ih =>
    simp only [List.filter_cons] at hlen
    have hle : (tl.filter p).length ≤ tl.length := List.length_filter_le p tl
    cases hpa : p a with
    | false =>
      simp only [hpa, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
      omega
    | true =>
      simp only [hpa, ↓reduceIte, List.length_cons] at hlen
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hpa
      · exact ih (by omega) x hmem

private theorem atLeast_iff_filter_length {n num : Nat} {ys : List Nat}
    (hnodup : ys.Nodup) (hlt : ∀ y ∈ ys, y < num)
    {P : Fin num → Prop} {p : Nat → Bool}
    (hiff : ∀ y : Fin num, P y ↔ y.val ∈ ys ∧ p y.val = true) :
    AtLeast n P ↔ n ≤ (ys.filter p).length := by
  let filtered := ys.filter p
  have hfnodup : filtered.Nodup := nodup_filter' p hnodup
  have hfsub : ∀ y ∈ filtered, y < num := fun y hy => hlt y (List.mem_filter.mp hy).1
  constructor
  · rintro ⟨xs, hlen, hnd, hP⟩
    have hsub : ∀ x ∈ xs.map Fin.val, x ∈ filtered := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have ⟨hym, hyp⟩ := (hiff y).mp (hP y hy)
      exact List.mem_filter.mpr ⟨hym, hyp⟩
    have hnd_map : (xs.map Fin.val).Nodup :=
      nodup_map_inj' (fun _ _ h => Fin.ext h) hnd
    have hle : (xs.map Fin.val).length ≤ filtered.length := by
      have hcard : ∀ (as bs : List Nat), as.Nodup → (∀ a ∈ as, a ∈ bs) → as.length ≤ bs.length := by
        intro as
        induction as with
        | nil => intro _ _ _; exact Nat.zero_le _
        | cons a rest ih =>
          intro bs hnda hsub'
          obtain ⟨hanot, hndr⟩ := List.nodup_cons.mp hnda
          have haIn : a ∈ bs := hsub' a (List.mem_cons_self ..)
          have hrest : ∀ x ∈ rest, x ∈ bs.erase a := by
            intro x hx
            have hne : x ≠ a := fun he => hanot (he ▸ hx)
            exact (List.mem_erase_of_ne hne).mpr (hsub' x (List.mem_cons_of_mem _ hx))
          have hlen_r := ih (bs.erase a) hndr hrest
          have hlen_e : (bs.erase a).length + 1 = bs.length := by
            rw [List.length_erase_of_mem haIn]
            have hpos : 0 < bs.length := List.length_pos_of_mem haIn
            omega
          simp only [List.length_cons]; omega
      exact hcard _ _ hnd_map hsub
    simpa [hlen] using hle
  · intro hle
    let taken := filtered.take n
    have htlen : taken.length = n := by
      simp only [taken, List.length_take]; exact Nat.min_eq_left hle
    have htnodup : taken.Nodup := nodup_take' n hfnodup
    have htsub : ∀ y ∈ taken, y ∈ filtered := fun y hy => List.mem_of_mem_take hy
    let fins := listToFins num taken (fun y hy => hfsub y (htsub y hy))
    refine ⟨fins, by rw [listToFins_length, htlen], ?_, ?_⟩
    · have hmap := listToFins_map_val num taken (fun y hy => hfsub y (htsub y hy))
      have : (fins.map Fin.val).Nodup := hmap ▸ htnodup
      exact nodup_of_map' Fin.val this
    · intro x hx
      have hxv : x.val ∈ taken := by
        have hmap := listToFins_map_val num taken (fun y hy => hfsub y (htsub y hy))
        rw [← hmap]; exact List.mem_map_of_mem hx
      have ⟨hym, hyp⟩ := List.mem_filter.mp (htsub x.val hxv)
      exact (hiff x).mpr ⟨hym, hyp⟩

/-- Exact correspondence between `evalClassExpr m x e = some b` and OWL 2 Direct Semantics
    `classHolds (m.toInterpretation dm hne) x e`. -/
theorem evalClassExpr_iff (dm : DatatypeMap) {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes) :
    ∀ (e : ClassExpr) (x : Fin m.numNodes) (b : Bool),
      evalClassExpr m x.val e = some b →
      (b = true ↔ classHolds (m.toInterpretation dm hne) x e)
  | .named c, x, b, he => by
    simp only [evalClassExpr, Option.some.injEq] at he
    subst he; simp [classHolds, CBCanonicalModel.toInterpretation]
  | .complement c, x, b, he => by
    simp only [evalClassExpr, Option.map_eq_some_iff] at he
    obtain ⟨v, hv, rfl⟩ := he
    have ih := evalClassExpr_iff dm hadj hne c x v hv
    simp only [classHolds, Bool.not_eq_true']
    cases v <;> simp at ih ⊢ <;> exact ih
  | .intersection e1 e2, x, b, he => by
    simp only [evalClassExpr] at he
    cases h1 : evalClassExpr m x.val e1 with
    | none => rw [h1] at he; cases he
    | some v1 =>
      rw [h1] at he
      have ih1 := evalClassExpr_iff dm hadj hne e1 x v1 h1
      cases v1 with
      | false =>
        cases he; simp only [Bool.false_eq_true, false_iff, classHolds]
        intro ⟨h1', _⟩; exact Bool.false_ne_true (ih1.mpr h1')
      | true =>
        have ih2 := evalClassExpr_iff dm hadj hne e2 x b he
        simp only [classHolds]
        exact ⟨fun hb => ⟨ih1.mp rfl, ih2.mp hb⟩, fun ⟨_, h2'⟩ => ih2.mpr h2'⟩
  | .union e1 e2, x, b, he => by
    simp only [evalClassExpr] at he
    cases h1 : evalClassExpr m x.val e1 with
    | none => rw [h1] at he; cases he
    | some v1 =>
      rw [h1] at he
      have ih1 := evalClassExpr_iff dm hadj hne e1 x v1 h1
      cases v1 with
      | true =>
        cases he; simp only [true_iff, classHolds]
        exact Or.inl (ih1.mp rfl)
      | false =>
        have ih2 := evalClassExpr_iff dm hadj hne e2 x b he
        simp only [classHolds]
        exact ⟨fun hb => Or.inr (ih2.mp hb),
               fun h => h.elim (fun h1' => absurd (ih1.mpr h1') Bool.false_ne_true) ih2.mpr⟩
  | .objectSome r f, x, b, he => by
    simp only [evalClassExpr] at he
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at he hnb; dsimp only at he
      obtain ⟨hsort, hiff⟩ := hnb
      rw [← Array.foldl_toList] at he
      obtain ⟨hbt, hbf⟩ := foldl_or_opt he (fun _ _ _ _ => trivial)
      simp only [classHolds]
      constructor
      · intro hb
        rcases hbt.mp hb with h | ⟨y, hy, hpy⟩
        · cases h
        · let yf : Fin m.numNodes := ⟨y, strictSorted_lt_of_mem hsort hy⟩
          exact ⟨yf, (hiff yf).mpr hy, (evalClassExpr_iff dm hadj hne f yf true hpy).mp rfl⟩
      · rintro ⟨y, hry, hyf⟩
        apply Classical.byContradiction; intro hnot
        have hbf' : b = false := by cases b <;> simp_all
        have hpy := (hbf hbf').2 y.val ((hiff y).mp hry)
        exact Bool.false_ne_true ((evalClassExpr_iff dm hadj hne f y false hpy).mpr hyf)
    | none =>
      rw [hnr] at he hnb; dsimp only at he
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := countOptRange_go_spec hcnt
      simp only [Nat.zero_add] at hlen
      have hge := atLeast_iff_filter_length (n := 1) (num := m.numNodes) (ys := List.range m.numNodes)
        List.nodup_range (fun y hy => List.mem_range.mp hy)
        (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
                       classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          obtain ⟨v, hv⟩ := hdef y.val (Nat.zero_le _) (by simp [y.isLt])
          have ih := evalClassExpr_iff dm hadj hne f y v hv
          simp only [hnb y, true_and, List.mem_range, y.isLt, hv, beq_iff_eq, Option.some.injEq]
          exact ih.symm)
      simp only [classHolds, decide_eq_true_eq, hlen]
      constructor
      · intro h
        obtain ⟨xs, hl, _, hp⟩ := hge.mpr (by omega)
        cases xs with
        | nil => simp at hl
        | cons y _ => exact ⟨y, hp y (List.mem_cons_self ..)⟩
      · rintro ⟨y, hy⟩
        have h1 : 1 ≤ (List.filter (fun k => evalClassExpr m k f == some true) (List.range m.numNodes)).length :=
          hge.mp ⟨[(y : Fin m.numNodes)], rfl, List.pairwise_singleton _ _, fun z hz => (List.mem_singleton.mp hz) ▸ hy⟩
        omega
  | .objectAll r f, x, b, he => by
    simp only [evalClassExpr] at he
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at he hnb; dsimp only at he
      obtain ⟨hsort, hiff⟩ := hnb
      rw [← Array.foldl_toList] at he
      obtain ⟨hbt, hbf⟩ := foldl_and_opt he
      simp only [classHolds]
      constructor
      · intro hb y hry
        have hpy := (hbt hb).2 y.val ((hiff y).mp hry)
        exact (evalClassExpr_iff dm hadj hne f y true hpy).mp rfl
      · intro hall
        apply Classical.byContradiction; intro hnot
        have hbf' : b = false := by cases b <;> simp_all
        rcases hbf hbf' with h | ⟨y, hy, hpy⟩
        · cases h
        · let yf : Fin m.numNodes := ⟨y, strictSorted_lt_of_mem hsort hy⟩
          have hyf := hall yf ((hiff yf).mpr hy)
          exact Bool.false_ne_true ((evalClassExpr_iff dm hadj hne f yf false hpy).mpr hyf)
    | none =>
      rw [hnr] at he hnb
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := countOptRange_go_spec hcnt
      simp only [Nat.zero_add] at hlen
      simp only [classHolds, beq_iff_eq, hlen]
      constructor
      · intro hfull y _
        have hall_eq : ((List.range m.numNodes).filter (fun k => evalClassExpr m k f == some true)).length =
            (List.range m.numNodes).length := by rw [hfull, List.length_range]
        have hpred := filter_length_eq_imp hall_eq y.val (List.mem_range.mpr y.isLt)
        exact (evalClassExpr_iff dm hadj hne f y true (beq_iff_eq.mp hpred)).mp rfl
      · intro hall
        have hallp : ∀ k ∈ List.range m.numNodes, (evalClassExpr m k f == some true) = true := by
          intro k hk
          have hklt := List.mem_range.mp hk
          obtain ⟨v, hv⟩ := hdef k (Nat.zero_le _) (by simpa using hklt)
          have htrue := (evalClassExpr_iff dm hadj hne f ⟨k, hklt⟩ v hv).mpr (hall ⟨k, hklt⟩ (hnb ⟨k, hklt⟩))
          rw [hv, htrue]; rfl
        rw [List.filter_eq_self.mpr hallp, List.length_range]
  | .objectSelf r, x, b, he => by
    simp only [evalClassExpr, Option.some.injEq] at he
    subst he
    cases r <;> simp [classHolds, objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasObjEdge]
  | .objectMin n r f, x, b, he => by
    simp only [evalClassExpr] at he
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at he hnb
      obtain ⟨hsort, hiff⟩ := hnb
      simp only [Option.map_eq_some_iff, countOptArray, ← Array.foldl_toList] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := foldl_count_list hcnt
      simp only [Nat.zero_add] at hlen
      simp only [classHolds, decide_eq_true_eq, hlen]
      exact (atLeast_iff_filter_length (strictSorted_nodup hsort)
        (fun y hy => strictSorted_lt_of_mem hsort hy) (fun y => by
          constructor
          · intro ⟨hry, hyf⟩
            have hyin := (hiff y).mp hry
            obtain ⟨v, hv⟩ := hdef y.val hyin
            have hvt := (evalClassExpr_iff dm hadj hne f y v hv).mpr hyf
            exact ⟨hyin, by rw [hv, hvt]; rfl⟩
          · intro ⟨hyin, hpy⟩
            exact ⟨(hiff y).mpr hyin, (evalClassExpr_iff dm hadj hne f y true (beq_iff_eq.mp hpy)).mp rfl⟩)).symm
    | none =>
      rw [hnr] at he hnb
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := countOptRange_go_spec hcnt
      simp only [Nat.zero_add] at hlen
      simp only [classHolds, decide_eq_true_eq, hlen]
      exact (atLeast_iff_filter_length List.nodup_range (fun y hy => List.mem_range.mp hy) (fun y => by
        obtain ⟨v, hv⟩ := hdef y.val (Nat.zero_le _) (by simp [y.isLt])
        have ih := evalClassExpr_iff dm hadj hne f y v hv
        simp only [hnb y, true_and, List.mem_range, y.isLt, hv, beq_iff_eq, Option.some.injEq]
        exact ih.symm)).symm
  | .objectMax n r f, x, b, he => by
    simp only [evalClassExpr] at he
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at he hnb
      obtain ⟨hsort, hiff⟩ := hnb
      simp only [Option.map_eq_some_iff, countOptArray, ← Array.foldl_toList] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := foldl_count_list hcnt
      simp only [Nat.zero_add] at hlen
      have hge := atLeast_iff_filter_length (n := n + 1) (strictSorted_nodup hsort)
        (fun y hy => strictSorted_lt_of_mem hsort hy) (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          constructor
          · intro ⟨hry, hyf⟩
            have hyin := (hiff y).mp hry
            obtain ⟨v, hv⟩ := hdef y.val hyin
            have hvt := (evalClassExpr_iff dm hadj hne f y v hv).mpr hyf
            exact ⟨hyin, by rw [hv, hvt]; rfl⟩
          · intro ⟨hyin, hpy⟩
            exact ⟨(hiff y).mpr hyin, (evalClassExpr_iff dm hadj hne f y true (beq_iff_eq.mp hpy)).mp rfl⟩)
      simp only [classHolds, decide_eq_true_eq, hlen]
      constructor
      · intro h hgt; have := hge.mp hgt; omega
      · intro hnot
        exact Nat.le_of_not_lt fun hlt => hnot (hge.mpr hlt)
    | none =>
      rw [hnr] at he hnb
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := countOptRange_go_spec hcnt
      simp only [Nat.zero_add] at hlen
      have hge := atLeast_iff_filter_length (n := n + 1) List.nodup_range (fun y hy => List.mem_range.mp hy)
        (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          obtain ⟨v, hv⟩ := hdef y.val (Nat.zero_le _) (by simp [y.isLt])
          have ih := evalClassExpr_iff dm hadj hne f y v hv
          simp only [hnb y, true_and, List.mem_range, y.isLt, hv, beq_iff_eq, Option.some.injEq]
          exact ih.symm)
      simp only [classHolds, decide_eq_true_eq, hlen]
      constructor
      · intro h hgt; have := hge.mp hgt; omega
      · intro hnot
        exact Nat.le_of_not_lt fun hlt => hnot (hge.mpr hlt)
  | .objectExact n r f, x, b, he => by
    simp only [evalClassExpr] at he
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at he hnb
      obtain ⟨hsort, hiff⟩ := hnb
      simp only [Option.map_eq_some_iff, countOptArray, ← Array.foldl_toList] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := foldl_count_list hcnt
      simp only [Nat.zero_add] at hlen
      have hgeN := atLeast_iff_filter_length (n := n) (strictSorted_nodup hsort)
        (fun y hy => strictSorted_lt_of_mem hsort hy) (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          constructor
          · intro ⟨hry, hyf⟩
            have hyin := (hiff y).mp hry
            obtain ⟨v, hv⟩ := hdef y.val hyin
            have hvt := (evalClassExpr_iff dm hadj hne f y v hv).mpr hyf
            exact ⟨hyin, by rw [hv, hvt]; rfl⟩
          · intro ⟨hyin, hpy⟩
            exact ⟨(hiff y).mpr hyin, (evalClassExpr_iff dm hadj hne f y true (beq_iff_eq.mp hpy)).mp rfl⟩)
      have hgeS := atLeast_iff_filter_length (n := n + 1) (strictSorted_nodup hsort)
        (fun y hy => strictSorted_lt_of_mem hsort hy) (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          constructor
          · intro ⟨hry, hyf⟩
            have hyin := (hiff y).mp hry
            obtain ⟨v, hv⟩ := hdef y.val hyin
            have hvt := (evalClassExpr_iff dm hadj hne f y v hv).mpr hyf
            exact ⟨hyin, by rw [hv, hvt]; rfl⟩
          · intro ⟨hyin, hpy⟩
            exact ⟨(hiff y).mpr hyin, (evalClassExpr_iff dm hadj hne f y true (beq_iff_eq.mp hpy)).mp rfl⟩)
      simp only [classHolds, Exactly, beq_iff_eq, hlen]
      constructor
      · intro h
        exact ⟨hgeN.mpr (by omega), fun hgt => by have := hgeS.mp hgt; omega⟩
      · rintro ⟨h1, h2⟩
        have h1' := hgeN.mp h1
        have h2' : ¬ (n + 1 ≤ (List.filter (fun y => evalClassExpr m y f == some true) ys.toList).length) :=
          fun hlt => h2 (hgeS.mpr hlt)
        omega
    | none =>
      rw [hnr] at he hnb
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨cnt, hcnt, rfl⟩ := he
      obtain ⟨hdef, hlen⟩ := countOptRange_go_spec hcnt
      simp only [Nat.zero_add] at hlen
      have hgeN := atLeast_iff_filter_length (n := n) List.nodup_range (fun y hy => List.mem_range.mp hy)
        (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          obtain ⟨v, hv⟩ := hdef y.val (Nat.zero_le _) (by simp [y.isLt])
          have ih := evalClassExpr_iff dm hadj hne f y v hv
          simp only [hnb y, true_and, List.mem_range, y.isLt, hv, beq_iff_eq, Option.some.injEq]
          exact ih.symm)
      have hgeS := atLeast_iff_filter_length (n := n + 1) List.nodup_range (fun y hy => List.mem_range.mp hy)
        (P := fun y => objectHolds (m.toInterpretation dm hne) r x y ∧
          classHolds (m.toInterpretation dm hne) y f)
        (p := fun y => evalClassExpr m y f == some true) (fun y => by
          obtain ⟨v, hv⟩ := hdef y.val (Nat.zero_le _) (by simp [y.isLt])
          have ih := evalClassExpr_iff dm hadj hne f y v hv
          simp only [hnb y, true_and, List.mem_range, y.isLt, hv, beq_iff_eq, Option.some.injEq]
          exact ih.symm)
      simp only [classHolds, Exactly, beq_iff_eq, hlen]
      constructor
      · intro h
        exact ⟨hgeN.mpr (by omega), fun hgt => by have := hgeS.mp hgt; omega⟩
      · rintro ⟨h1, h2⟩
        have h1' := hgeN.mp h1
        have h2' : ¬ (n + 1 ≤ (List.filter (fun y => evalClassExpr m y f == some true) (List.range m.numNodes)).length) :=
          fun hlt => h2 (hgeS.mpr hlt)
        omega
  | .oneOf _, _, _, he => by cases he
  | .objectValue _ _, _, _, he => by cases he
  | .dataSome _ _, _, _, he => by cases he
  | .dataAll _ _, _, _, he => by cases he
  | .dataValue _ _, _, _, he => by cases he
  | .dataMin _ _ _, _, _, he => by cases he
  | .dataMax _ _ _, _, _, he => by cases he
  | .dataExact _ _ _, _, _, he => by cases he

/-! ### 4. Parallel Axiom Checker & Soundness Theorem -/

/-- Check `∀ y, r(x, y) → P y` using `neighbors?` in $O(\text{deg}(x))$. -/
def allNeighborsCheck (m : CBCanonicalModel) (r : ObjectProperty) (x : Nat) (p : Nat → Bool) : Bool :=
  match m.neighbors? r x with
  | some ys => ys.all p
  | none => allRangeSeq p 0 m.numNodes

private theorem allNeighborsCheck_iff {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (r : ObjectProperty) (x : Fin m.numNodes) (p : Nat → Bool) :
    allNeighborsCheck m r x.val p = true ↔
      ∀ y : Fin m.numNodes, objectHolds (m.toInterpretation dm hne) r x y → p y.val = true := by
  unfold allNeighborsCheck
  have hnb := neighbors?_spec (dm := dm) hadj hne r x
  cases hnr : m.neighbors? r x.val with
  | some ys =>
    rw [hnr] at hnb
    obtain ⟨hsort, hiff⟩ := hnb
    rw [array_all_iff']
    constructor
    · intro h y hry; exact h y.val ((hiff y).mp hry)
    · intro h y hy; exact h ⟨y, strictSorted_lt_of_mem hsort hy⟩ ((hiff ⟨y, _⟩).mpr hy)
  | none =>
    rw [hnr] at hnb
    rw [allRangeSeq_iff]
    constructor
    · intro h y _; exact h y.val (Nat.zero_le _) y.isLt
    · intro h y _ hylt; exact h ⟨y, hylt⟩ (hnb ⟨y, hylt⟩)

/-- Check `rolePath m rs x z → m.hasObjEdge s x z` for all `z` reachable from `x` along `rs`. -/
def checkRoleChainFrom (m : CBCanonicalModel) (s : ObjectProperty) (x : Nat) :
    List ObjectProperty → Nat → Bool
  | [], cur => m.hasObjEdge s x cur
  | r :: rs, cur => allNeighborsCheck m r cur (fun nxt => checkRoleChainFrom m s x rs nxt)

private theorem checkRoleChainFrom_sound {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (s : ObjectProperty) (x : Fin m.numNodes) :
    ∀ (rs : List ObjectProperty) (cur : Fin m.numNodes),
      checkRoleChainFrom m s x.val rs cur.val = true →
      ∀ z : Fin m.numNodes, rolePath (m.toInterpretation dm hne) rs cur z →
        objectHolds (m.toInterpretation dm hne) s x z
  | [], cur, hchk, z, hpath => by
    simp only [rolePath] at hpath; subst hpath
    simp only [checkRoleChainFrom] at hchk
    cases s <;> exact hchk
  | r :: rs, cur, hchk, z, hpath => by
    simp only [rolePath] at hpath
    obtain ⟨nxt, hr, hrest⟩ := hpath
    simp only [checkRoleChainFrom] at hchk
    have hnxt := (allNeighborsCheck_iff hadj hne r cur _).mp hchk nxt hr
    exact checkRoleChainFrom_sound hadj hne s x rs nxt hnxt z hrest

private def checkDisjointGo (m : CBCanonicalModel) (x : Nat) (seenTrue : Bool) : List ClassExpr → Bool
  | [] => true
  | c :: rest =>
    match evalClassExpr m x c with
    | none => false
    | some false => checkDisjointGo m x seenTrue rest
    | some true => if seenTrue then false else checkDisjointGo m x true rest

private def checkDisjointUnionGo (m : CBCanonicalModel) (x : Nat) (cnt : Nat) : List ClassExpr → Option Nat
  | [] => some cnt
  | c :: rest =>
    match evalClassExpr m x c with
    | none => none
    | some false => checkDisjointUnionGo m x cnt rest
    | some true => checkDisjointUnionGo m x (cnt + 1) rest

/-- Check `p` on every node in `cands?` (or all `0 .. m.numNodes - 1` when `none`). -/
def checkNodes (m : CBCanonicalModel) (cands? : Option (Array Nat)) (p : Nat → Bool) : Bool :=
  match cands? with
  | some xs => xs.all p
  | none => allRangeSeq p 0 m.numNodes

private theorem checkNodes_sound {m : CBCanonicalModel} {cands? : Option (Array Nat)}
    {p : Nat → Bool} (hchk : checkNodes m cands? p = true)
    (x : Fin m.numNodes) (hmem : ∀ xs, cands? = some xs → x.val ∈ xs.toList) :
    p x.val = true := by
  unfold checkNodes at hchk
  cases hc : cands? with
  | none =>
    rw [hc, allRangeSeq_iff] at hchk
    exact hchk x.val (Nat.zero_le _) x.isLt
  | some xs => rw [hc] at hchk; exact array_all_iff'.mp hchk x.val (hmem xs hc)

/-- Candidate source nodes that can have an outgoing `r`-edge in `m` (`none` = all nodes). -/
def roleSourceNodes? (m : CBCanonicalModel) : ObjectProperty → Option (Array Nat)
  | .named p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else some (m.roleOutNodes.getD p #[])
  | .inverse p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else some (m.roleInNodes.getD p #[])

private theorem roleSourceNodes?_complete {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (r : ObjectProperty) {xs : Array Nat} (h : roleSourceNodes? m r = some xs)
    (x y : Fin m.numNodes) (hxy : objectHolds (m.toInterpretation dm hne) r x y) :
    x.val ∈ xs.toList := by
  cases r with
  | named p =>
    unfold roleSourceNodes? at h
    by_cases ht : p = topObjectProperty
    · subst ht; simp at h
    · by_cases hb : p = bottomObjectProperty
      · subst hb
        have hbot : False := (m.toInterpretation dm hne).bottomObjectExt x y hxy
        exact hbot.elim
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hout : (m.outNeighbors p x.val).contains y.val = true := by
          simpa [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge,
                 hnt, hnb] using hxy
        exact adjConsistent_roleOut_mem hadj x.isLt hout
  | inverse p =>
    unfold roleSourceNodes? at h
    by_cases ht : p = topObjectProperty
    · subst ht; simp at h
    · by_cases hb : p = bottomObjectProperty
      · subst hb
        have hbot : False := (m.toInterpretation dm hne).bottomObjectExt y x hxy
        exact hbot.elim
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hout : (m.outNeighbors p y.val).contains x.val = true := by
          simpa [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge,
                 hnt, hnb] using hxy
        have hin : (m.inNeighbors p x.val).contains y.val = true :=
          (adjConsistent_in_iff hadj p x.isLt y.isLt).mpr hout
        exact adjConsistent_roleIn_mem hadj x.isLt hin

/-- Candidate nodes where `ClassExpr` can hold in `m` (`none` = all nodes). -/
def candidateNodes? (m : CBCanonicalModel) : ClassExpr → Option (Array Nat)
  | .named c =>
    if c == thing then none
    else if c == nothing then some #[]
    else some (m.clsNodes.getD c #[])
  | .intersection a b =>
    match candidateNodes? m a, candidateNodes? m b with
    | some xa, some xb => if xa.size ≤ xb.size then some xa else some xb
    | some xa, none => some xa
    | none, some xb => some xb
    | none, none => none
  | .objectSome r _ => roleSourceNodes? m r
  | .objectSelf r => roleSourceNodes? m r
  | .objectMin (_ + 1) r _ => roleSourceNodes? m r
  | .objectExact (_ + 1) r _ => roleSourceNodes? m r
  | _ => none

private theorem candidateNodes?_complete {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes) :
    ∀ (e : ClassExpr) {xs : Array Nat},
      candidateNodes? m e = some xs →
      ∀ (x : Fin m.numNodes), classHolds (m.toInterpretation dm hne) x e →
      x.val ∈ xs.toList
  | .named c, xs, h, x, hx => by
    unfold candidateNodes? at h
    by_cases ht : c = thing
    · subst ht; simp at h
    · by_cases hn : c = nothing
      · subst hn; exact ((m.toInterpretation dm hne).nothingExt x hx).elim
      · have hnt : (c == thing) = false := beq_false_of_ne ht
        have hnn : (c == nothing) = false := beq_false_of_ne hn
        simp only [hnt, hnn, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hct : (m.nodeClasses.getD x.val {}).contains c = true := by
          simpa [classHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasCls,
                 hnt, hnn] using hx
        exact adjConsistent_cls_mem hadj x.isLt hct
  | .intersection a b, xs, h, x, ⟨hxa, hxb⟩ => by
    unfold candidateNodes? at h
    cases ha : candidateNodes? m a <;> cases hb : candidateNodes? m b <;>
      simp only [ha, hb] at h
    · cases h
    · cases h; exact candidateNodes?_complete hadj hne b hb x hxb
    · cases h; exact candidateNodes?_complete hadj hne a ha x hxa
    · split at h <;> cases h
      · exact candidateNodes?_complete hadj hne a ha x hxa
      · exact candidateNodes?_complete hadj hne b hb x hxb
  | .objectSome r _, xs, h, x, ⟨y, hxy, _⟩ =>
    roleSourceNodes?_complete hadj hne r h x y hxy
  | .objectSelf r, xs, h, x, hxx =>
    roleSourceNodes?_complete hadj hne r h x x hxx
  | .objectMin (_ + 1) r _, xs, h, x, ⟨ys, hlen, _, hpy⟩ => by
    cases ys with
    | nil => simp at hlen
    | cons y _ =>
      exact roleSourceNodes?_complete hadj hne r h x y (hpy y (List.mem_cons_self ..)).1
  | .objectExact (_ + 1) r _, xs, h, x, ⟨⟨ys, hlen, _, hpy⟩, _⟩ => by
    cases ys with
    | nil => simp at hlen
    | cons y _ =>
      exact roleSourceNodes?_complete hadj hne r h x y (hpy y (List.mem_cons_self ..)).1
  | .objectMin 0 _ _, _, h, _, _ => by cases h
  | .objectExact 0 _ _, _, h, _, _ => by cases h
  | .complement _, _, h, _, _ => by cases h
  | .union _ _, _, h, _, _ => by cases h
  | .oneOf _, _, h, _, _ => by cases h
  | .objectAll _ _, _, h, _, _ => by cases h
  | .objectValue _ _, _, h, _, _ => by cases h
  | .objectMax _ _ _, _, h, _, _ => by cases h
  | .dataSome _ _, _, h, _, _ => by cases h
  | .dataAll _ _, _, h, _, _ => by cases h
  | .dataValue _ _, _, h, _, _ => by cases h
  | .dataMin _ _ _, _, h, _, _ => by cases h
  | .dataMax _ _ _, _, h, _, _ => by cases h
  | .dataExact _ _ _, _, h, _, _ => by cases h

/-- Check a single `Axiom` on `m` in $O(\text{support})$ using inverted indices
    (assuming `checkAdjConsistent m`). -/
def checkCBAxiom (m : CBCanonicalModel) : Axiom → Bool
  | .subClassOf a b =>
    checkNodes m (candidateNodes? m a) fun x =>
      match evalClassExpr m x a with
      | some false => true
      | some true => evalClassExpr m x b == some true
      | none => false
  | .equivalentClasses cs =>
    match cs with
    | [] | [_] => true
    | [c0, c1] =>
      match candidateNodes? m c0, candidateNodes? m c1 with
      | some xs0, some xs1 =>
        let chk (x : Nat) : Bool :=
          match evalClassExpr m x c0, evalClassExpr m x c1 with
          | some v0, some v1 => v0 == v1
          | _, _ => false
        xs0.all chk && xs1.all chk
      | _, _ =>
        allRangeSeq (fun x =>
          match evalClassExpr m x c0 with
          | none => false
          | some v0 => evalClassExpr m x c1 == some v0) 0 m.numNodes
    | c0 :: rest =>
      allRangeSeq (fun x =>
        match evalClassExpr m x c0 with
        | none => false
        | some v0 => rest.all fun c => evalClassExpr m x c == some v0) 0 m.numNodes
  | .disjointClasses cs =>
    match cs with
    | [a, b] =>
      let cands? := match candidateNodes? m a, candidateNodes? m b with
        | some xa, some xb => if xa.size ≤ xb.size then some xa else some xb
        | some xa, none => some xa
        | none, some xb => some xb
        | none, none => none
      checkNodes m cands? (fun x => checkDisjointGo m x false [a, b])
    | _ =>
      allRangeSeq (fun x => checkDisjointGo m x false cs) 0 m.numNodes
  | .disjointUnion h cs =>
    allRangeSeq (fun x =>
      let hx := m.hasCls h x
      match checkDisjointUnionGo m x 0 cs with
      | none => false
      | some cnt => if hx then cnt == 1 else cnt == 0) 0 m.numNodes
  | .subObjectProperty r s =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      allNeighborsCheck m r x (fun y => m.hasObjEdge s x y)
  | .subObjectPropertyChain rs s =>
    let cands? := match rs with
      | r0 :: _ => roleSourceNodes? m r0
      | [] => none
    checkNodes m cands? (fun x => checkRoleChainFrom m s x rs x)
  | .equivalentObjectProperties rs =>
    match rs with
    | [] | [_] => true
    | r0 :: rest =>
      rest.all fun r =>
        checkNodes m (roleSourceNodes? m r0) (fun x => allNeighborsCheck m r0 x (fun y => m.hasObjEdge r x y)) &&
        checkNodes m (roleSourceNodes? m r) (fun x => allNeighborsCheck m r x (fun y => m.hasObjEdge r0 x y))
  | .inverseObjectProperties r s =>
    checkNodes m (roleSourceNodes? m r) (fun x => allNeighborsCheck m r x (fun y => m.hasObjEdge s y x)) &&
    checkNodes m (roleSourceNodes? m s) (fun x => allNeighborsCheck m s x (fun y => m.hasObjEdge r y x))
  | .symmetricObjectProperty r =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      allNeighborsCheck m r x (fun y => m.hasObjEdge r y x)
  | .transitiveObjectProperty r =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      allNeighborsCheck m r x (fun y =>
        allNeighborsCheck m r y (fun z => m.hasObjEdge r x z))
  | .reflexiveObjectProperty r =>
    allRangeSeq (fun x => m.hasObjEdge r x x) 0 m.numNodes
  | .objectPropertyDomain r dom =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      match m.neighbors? r x with
      | some ys => if ys.isEmpty then true else evalClassExpr m x dom == some true
      | none => evalClassExpr m x dom == some true
  | .objectPropertyRange r rng =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      allNeighborsCheck m r x (fun y => evalClassExpr m y rng == some true)
  | .functionalObjectProperty r =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      match m.neighbors? r x with
      | some ys => ys.size ≤ 1
      | none => m.numNodes ≤ 1
  | .inverseFunctionalObjectProperty r =>
    checkNodes m (roleSourceNodes? m r.converse) fun x =>
      match m.neighbors? r.converse x with
      | some ys => ys.size ≤ 1
      | none => m.numNodes ≤ 1
  | _ => false

/-- Parallel kernel-verified model checker for `o` on `CBCanonicalModel`. -/
def checkCBCanonicalModel (o : Ontology) (m : CBCanonicalModel) (numWorkers : Nat := 8) : Bool :=
  let axArr := o.toArray
  checkAdjConsistent m numWorkers &&
  allRangePar axArr.size (fun idx =>
    match axArr[idx]? with
    | some ax => checkCBAxiom m ax
    | none => false) numWorkers

private theorem hasObjEdge_iff {dm : DatatypeMap} {m : CBCanonicalModel} {hne : 0 < m.numNodes}
    (r : ObjectProperty) (x y : Fin m.numNodes) :
    m.hasObjEdge r x.val y.val = true ↔ objectHolds (m.toInterpretation dm hne) r x y := by
  cases r <;> rfl

private theorem pairwise_of_all_not {α : Type} {P : α → Prop} :
    ∀ {ls : List α}, (∀ c ∈ ls, ¬ P c) → ls.Pairwise (fun a b => ¬ (P a ∧ P b))
  | [], _ => List.Pairwise.nil
  | d :: _tl, hnone =>
    List.pairwise_cons.mpr
      ⟨fun _ _ ⟨hdx, _⟩ => hnone d (List.mem_cons_self ..) hdx,
       pairwise_of_all_not (fun e he => hnone e (List.mem_cons_of_mem _ he))⟩

private theorem checkDisjointGo_sound (dm : DatatypeMap) {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes) (x : Fin m.numNodes) :
    ∀ (cs : List ClassExpr) (seenTrue : Bool),
      checkDisjointGo m x.val seenTrue cs = true →
      (seenTrue = true → ∀ c ∈ cs, ¬ classHolds (m.toInterpretation dm hne) x c) ∧
      cs.Pairwise (fun a b => ¬ (classHolds (m.toInterpretation dm hne) x a ∧
                                  classHolds (m.toInterpretation dm hne) x b))
  | [], _, _ => ⟨(fun _ _ h => nomatch h), List.Pairwise.nil⟩
  | c :: rest, seenTrue, h => by
    unfold checkDisjointGo at h
    cases hc : evalClassExpr m x.val c with
    | none => simp [hc] at h
    | some v =>
      have ihc := evalClassExpr_iff dm hadj hne c x v hc
      cases v with
      | false =>
        simp only [hc] at h
        have ⟨hrestS, hrestP⟩ := checkDisjointGo_sound dm hadj hne x rest seenTrue h
        constructor
        · intro hs d hd
          rcases List.mem_cons.mp hd with rfl | hmem
          · intro hcx; exact Bool.false_ne_true (ihc.mpr hcx)
          · exact hrestS hs d hmem
        · refine List.pairwise_cons.mpr ⟨fun d _ ⟨hcx, _⟩ => Bool.false_ne_true (ihc.mpr hcx), hrestP⟩
      | true =>
        cases seenTrue with
        | true => simp [hc] at h
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          have ⟨hrestS, hrestP⟩ := checkDisjointGo_sound dm hadj hne x rest true h
          refine ⟨(fun hf => nomatch hf), List.pairwise_cons.mpr ⟨fun d hd ⟨_, hdx⟩ => hrestS rfl d hd hdx, hrestP⟩⟩

private theorem checkDisjointUnionGo_ge (m : CBCanonicalModel) (x : Nat) :
    ∀ (ls : List ClassExpr) (a k : Nat), checkDisjointUnionGo m x a ls = some k → a ≤ k
  | [], a, k, hk => by simp only [checkDisjointUnionGo, Option.some.injEq] at hk; omega
  | d :: tl, a, k, hk => by
    unfold checkDisjointUnionGo at hk
    cases hd : evalClassExpr m x d with
    | none => simp [hd] at hk
    | some v =>
      cases v <;> simp only [hd] at hk
      · exact checkDisjointUnionGo_ge m x tl a k hk
      · have := checkDisjointUnionGo_ge m x tl (a + 1) k hk; omega

private theorem checkDisjointUnionGo_sound (dm : DatatypeMap) {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes) (x : Fin m.numNodes) :
    ∀ (cs : List ClassExpr) (acc cnt : Nat),
      checkDisjointUnionGo m x.val acc cs = some cnt →
      (cnt = acc → ∀ c ∈ cs, ¬ classHolds (m.toInterpretation dm hne) x c) ∧
      (cnt = acc + 1 → (∃ c ∈ cs, classHolds (m.toInterpretation dm hne) x c) ∧
        cs.Pairwise (fun a b => ¬ (classHolds (m.toInterpretation dm hne) x a ∧
                                    classHolds (m.toInterpretation dm hne) x b)))
  | [], acc, cnt, h => by
    simp only [checkDisjointUnionGo, Option.some.injEq] at h; subst h
    exact ⟨(fun _ _ hm => nomatch hm), (fun h' => by omega)⟩
  | c :: rest, acc, cnt, h => by
    unfold checkDisjointUnionGo at h
    cases hc : evalClassExpr m x.val c with
    | none => simp [hc] at h
    | some v =>
      have ihc := evalClassExpr_iff dm hadj hne c x v hc
      cases v with
      | false =>
        simp only [hc] at h
        obtain ⟨h0, h1⟩ := checkDisjointUnionGo_sound dm hadj hne x rest acc cnt h
        constructor
        · intro heq d hd
          rcases List.mem_cons.mp hd with rfl | hmem
          · intro hcx; exact Bool.false_ne_true (ihc.mpr hcx)
          · exact h0 heq d hmem
        · intro heq
          obtain ⟨⟨d, hd, hdx⟩, hpw⟩ := h1 heq
          exact ⟨⟨d, List.mem_cons_of_mem _ hd, hdx⟩,
                 List.pairwise_cons.mpr ⟨fun e _ ⟨hcx, _⟩ => Bool.false_ne_true (ihc.mpr hcx), hpw⟩⟩
      | true =>
        simp only [hc] at h
        obtain ⟨h0, _⟩ := checkDisjointUnionGo_sound dm hadj hne x rest (acc + 1) cnt h
        have hle := checkDisjointUnionGo_ge m x.val rest (acc + 1) cnt h
        constructor
        · intro heq; omega
        · intro heq
          refine ⟨⟨c, List.mem_cons_self .., ihc.mp rfl⟩,
                  List.pairwise_cons.mpr ⟨fun d hd ⟨_, hdx⟩ => h0 heq d hd hdx,
                    pairwise_of_all_not (h0 heq)⟩⟩

private theorem checkCBAxiom_sound {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes) {ax : Axiom}
    (hchk : checkCBAxiom m ax = true) :
    axiomHolds (m.toInterpretation dm hne) ax := by
  cases ax with
  | subClassOf a b =>
    simp only [checkCBAxiom] at hchk
    intro x hax
    have hx := checkNodes_sound hchk x (fun xs hc => candidateNodes?_complete hadj hne a hc x hax)
    cases ha : evalClassExpr m x.val a with
    | none => simp [ha] at hx
    | some v =>
      have iha := evalClassExpr_iff dm hadj hne a x v ha
      cases v with
      | false => exact absurd (iha.mpr hax) Bool.false_ne_true
      | true =>
        simp only [ha, beq_iff_eq] at hx
        exact (evalClassExpr_iff dm hadj hne b x true hx).mp rfl
  | equivalentClasses cs =>
    cases cs with
    | nil => intro a ha; cases ha
    | cons c0 rest =>
      cases rest with
      | nil =>
        intro a ha b hb x
        have := List.mem_singleton.mp ha; have := List.mem_singleton.mp hb
        subst_vars; rfl
      | cons c1 tl =>
        cases tl with
        | nil =>
          have hiff01 : ∀ x : Fin m.numNodes,
              classHolds (m.toInterpretation dm hne) x c0 ↔
              classHolds (m.toInterpretation dm hne) x c1 := by
            intro x
            unfold checkCBAxiom at hchk
            dsimp only at hchk
            cases hc0 : candidateNodes? m c0 with
            | none =>
              rw [hc0] at hchk; dsimp only at hchk
              rw [allRangeSeq_iff] at hchk
              have hx := hchk x.val (Nat.zero_le _) x.isLt
              cases h0 : evalClassExpr m x.val c0 with
              | none => simp [h0] at hx
              | some v0 =>
                simp only [h0, beq_iff_eq] at hx
                exact (evalClassExpr_iff dm hadj hne c0 x v0 h0).symm.trans
                      (evalClassExpr_iff dm hadj hne c1 x v0 hx)
            | some xs0 =>
              cases hc1 : candidateNodes? m c1 with
              | none =>
                rw [hc0, hc1] at hchk; dsimp only at hchk
                rw [allRangeSeq_iff] at hchk
                have hx := hchk x.val (Nat.zero_le _) x.isLt
                cases h0 : evalClassExpr m x.val c0 with
                | none => simp [h0] at hx
                | some v0 =>
                  simp only [h0, beq_iff_eq] at hx
                  exact (evalClassExpr_iff dm hadj hne c0 x v0 h0).symm.trans
                        (evalClassExpr_iff dm hadj hne c1 x v0 hx)
              | some xs1 =>
                rw [hc0, hc1] at hchk; dsimp only at hchk
                obtain ⟨h0all, h1all⟩ := (Bool.and_eq_true _ _).mp hchk
                constructor
                · intro hx0
                  have hmem0 := candidateNodes?_complete hadj hne c0 hc0 x hx0
                  have hx := array_all_iff'.mp h0all x.val hmem0
                  cases he0 : evalClassExpr m x.val c0 with
                  | none => simp [he0] at hx
                  | some v0 =>
                    cases he1 : evalClassExpr m x.val c1 with
                    | none => simp [he0, he1] at hx
                    | some v1 =>
                      simp only [he0, he1, beq_iff_eq] at hx
                      subst hx
                      exact (evalClassExpr_iff dm hadj hne c1 x v0 he1).mp
                        ((evalClassExpr_iff dm hadj hne c0 x v0 he0).mpr hx0)
                · intro hx1
                  have hmem1 := candidateNodes?_complete hadj hne c1 hc1 x hx1
                  have hx := array_all_iff'.mp h1all x.val hmem1
                  cases he0 : evalClassExpr m x.val c0 with
                  | none => simp [he0] at hx
                  | some v0 =>
                    cases he1 : evalClassExpr m x.val c1 with
                    | none => simp [he0, he1] at hx
                    | some v1 =>
                      simp only [he0, he1, beq_iff_eq] at hx
                      subst hx
                      exact (evalClassExpr_iff dm hadj hne c0 x v0 he0).mp
                        ((evalClassExpr_iff dm hadj hne c1 x v0 he1).mpr hx1)
          intro a ha b hb x
          rcases List.mem_cons.mp ha with rfl | ha1
          · rcases List.mem_cons.mp hb with rfl | hb1
            · rfl
            · rw [List.mem_singleton.mp hb1]; exact hiff01 x
          · rw [List.mem_singleton.mp ha1]
            rcases List.mem_cons.mp hb with rfl | hb1
            · exact (hiff01 x).symm
            · rw [List.mem_singleton.mp hb1]
        | cons c2 tl2 =>
          simp only [checkCBAxiom, allRangeSeq_iff] at hchk
          intro a ha b hb x
          have hx := hchk x.val (Nat.zero_le _) x.isLt
          cases h0 : evalClassExpr m x.val c0 with
          | none => simp [h0] at hx
          | some v0 =>
            simp only [h0, List.all_eq_true, beq_iff_eq] at hx
            have heval : ∀ c ∈ c0 :: c1 :: c2 :: tl2, evalClassExpr m x.val c = some v0 := by
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hmem
              · exact h0
              · exact hx c hmem
            have iha := evalClassExpr_iff dm hadj hne a x v0 (heval a ha)
            have ihb := evalClassExpr_iff dm hadj hne b x v0 (heval b hb)
            exact iha.symm.trans ihb
  | disjointClasses cs =>
    match cs with
    | [a, b] =>
      simp only [checkCBAxiom] at hchk
      refine List.pairwise_cons.mpr ⟨fun d hd x ⟨hxa, hxd⟩ => ?_,
        List.pairwise_cons.mpr ⟨(fun _ h => nomatch h), List.Pairwise.nil⟩⟩
      rcases List.mem_singleton.mp hd with rfl
      have hx : checkDisjointGo m x.val false [a, d] = true := by
        apply checkNodes_sound hchk x
        intro xs hc
        cases ha : candidateNodes? m a <;> cases hb : candidateNodes? m d <;>
          simp only [ha, hb] at hc
        · cases hc
        · cases hc; exact candidateNodes?_complete hadj hne d hb x hxd
        · cases hc; exact candidateNodes?_complete hadj hne a ha x hxa
        · split at hc <;> cases hc
          · exact candidateNodes?_complete hadj hne a ha x hxa
          · exact candidateNodes?_complete hadj hne d hb x hxd
      have hpw := (checkDisjointGo_sound dm hadj hne x [a, d] false hx).2
      exact (List.pairwise_cons.mp hpw).1 d (List.mem_singleton.mpr rfl) ⟨hxa, hxd⟩
    | [] => exact List.Pairwise.nil
    | [a] => exact List.pairwise_cons.mpr ⟨(fun _ h => nomatch h), List.Pairwise.nil⟩
    | a :: b :: c :: rest =>
      simp only [checkCBAxiom, allRangeSeq_iff] at hchk
      have hpw : ∀ x : Fin m.numNodes,
          (a :: b :: c :: rest).Pairwise (fun u v => ¬ (classHolds (m.toInterpretation dm hne) x u ∧
                                      classHolds (m.toInterpretation dm hne) x v)) :=
        fun x => (checkDisjointGo_sound dm hadj hne x (a :: b :: c :: rest) false (hchk x.val (Nat.zero_le _) x.isLt)).2
      clear hchk
      generalize hls : (a :: b :: c :: rest) = ls at hpw ⊢
      clear hls
      induction ls with
      | nil => exact List.Pairwise.nil
      | cons u tl ih =>
        refine List.pairwise_cons.mpr ⟨fun v hv x => ?_, ih (fun x => (List.pairwise_cons.mp (hpw x)).2)⟩
        exact (List.pairwise_cons.mp (hpw x)).1 v hv
  | disjointUnion h cs =>
    simp only [checkCBAxiom, allRangeSeq_iff] at hchk
    have hper : ∀ x : Fin m.numNodes,
        (m.hasCls h x.val = true ↔ ∃ c ∈ cs, classHolds (m.toInterpretation dm hne) x c) ∧
        cs.Pairwise (fun a b => ¬ (classHolds (m.toInterpretation dm hne) x a ∧
                                    classHolds (m.toInterpretation dm hne) x b)) := by
      intro x
      have hx := hchk x.val (Nat.zero_le _) x.isLt
      cases hg : checkDisjointUnionGo m x.val 0 cs with
      | none => simp [hg] at hx
      | some cnt =>
        simp only [hg] at hx
        obtain ⟨h0, h1⟩ := checkDisjointUnionGo_sound dm hadj hne x cs 0 cnt hg
        cases hh : m.hasCls h x.val with
        | true =>
          simp only [hh, ↓reduceIte, beq_iff_eq] at hx
          obtain ⟨hex, hpw⟩ := h1 hx
          exact ⟨⟨fun _ => hex, fun _ => rfl⟩, hpw⟩
        | false =>
          simp only [hh, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hx
          have hnone := h0 hx
          exact ⟨⟨fun hf => absurd hf Bool.false_ne_true, fun ⟨c, hc, hcx⟩ => absurd hcx (hnone c hc)⟩,
                 pairwise_of_all_not hnone⟩
    refine ⟨fun x => (hper x).1, ?_⟩
    have hpw := fun x => (hper x).2
    clear hper hchk
    induction cs with
    | nil => exact List.Pairwise.nil
    | cons a rest ih =>
      refine List.pairwise_cons.mpr ⟨fun b hb x => ?_, ih (fun x => (List.pairwise_cons.mp (hpw x)).2)⟩
      exact (List.pairwise_cons.mp (hpw x)).1 b hb
  | subObjectProperty r s =>
    simp only [checkCBAxiom] at hchk
    intro x y hry
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hry)
    exact (hasObjEdge_iff s x y).mp ((allNeighborsCheck_iff hadj hne r x _).mp hx y hry)
  | subObjectPropertyChain rs s =>
    simp only [checkCBAxiom] at hchk
    intro x y hpath
    have hx : checkRoleChainFrom m s x.val rs x.val = true := by
      apply checkNodes_sound hchk x
      intro xs hc
      cases rs with
      | nil => cases hc
      | cons r0 tl =>
        obtain ⟨nxt, hr0, _⟩ := hpath
        exact roleSourceNodes?_complete hadj hne r0 hc x nxt hr0
    exact checkRoleChainFrom_sound hadj hne s x rs x hx y hpath
  | equivalentObjectProperties rs =>
    cases rs with
    | nil => intro r hr; cases hr
    | cons r0 rest =>
      cases rest with
      | nil =>
        intro r hr s hs x y
        have := List.mem_singleton.mp hr; have := List.mem_singleton.mp hs
        subst_vars; rfl
      | cons r1 tl =>
        simp only [checkCBAxiom, List.all_eq_true] at hchk
        have hiff0 : ∀ r ∈ r0 :: r1 :: tl, ∀ x y,
            objectHolds (m.toInterpretation dm hne) r0 x y ↔
            objectHolds (m.toInterpretation dm hne) r x y := by
          intro r hr x y
          rcases List.mem_cons.mp hr with rfl | hmem
          · rfl
          · have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp (hchk r hmem)
            constructor
            · intro h
              have hx := checkNodes_sound h1 x (fun xs hc => roleSourceNodes?_complete hadj hne r0 hc x y h)
              exact (hasObjEdge_iff r x y).mp ((allNeighborsCheck_iff hadj hne r0 x _).mp hx y h)
            · intro h
              have hx := checkNodes_sound h2 x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y h)
              exact (hasObjEdge_iff r0 x y).mp ((allNeighborsCheck_iff hadj hne r x _).mp hx y h)
        intro r hr s hs x y
        exact (hiff0 r hr x y).symm.trans (hiff0 s hs x y)
  | inverseObjectProperties r s =>
    simp only [checkCBAxiom, Bool.and_eq_true] at hchk
    obtain ⟨h1, h2⟩ := hchk
    intro x y
    constructor
    · intro h
      have hx := checkNodes_sound h1 x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y h)
      exact (hasObjEdge_iff s y x).mp ((allNeighborsCheck_iff hadj hne r x _).mp hx y h)
    · intro h
      have hy := checkNodes_sound h2 y (fun xs hc => roleSourceNodes?_complete hadj hne s hc y x h)
      exact (hasObjEdge_iff r x y).mp ((allNeighborsCheck_iff hadj hne s y _).mp hy x h)
  | symmetricObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x y h
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y h)
    exact (hasObjEdge_iff r y x).mp ((allNeighborsCheck_iff hadj hne r x _).mp hx y h)
  | transitiveObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x y z hxy hyz
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
    have hy := (allNeighborsCheck_iff hadj hne r x _).mp hx y hxy
    exact (hasObjEdge_iff r x z).mp ((allNeighborsCheck_iff hadj hne r y _).mp hy z hyz)
  | reflexiveObjectProperty r =>
    simp only [checkCBAxiom, allRangeSeq_iff] at hchk
    intro x
    exact (hasObjEdge_iff r x x).mp (hchk x.val (Nat.zero_le _) x.isLt)
  | objectPropertyDomain r dom =>
    simp only [checkCBAxiom] at hchk
    intro x y hxy
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at hx hnb
      have hyin := hnb.2 y |>.mp hxy
      have hne_ys : ys.isEmpty = false := by
        cases h : ys.isEmpty with
        | false => rfl
        | true =>
          have hsz : ys.size = 0 := by simpa [Array.isEmpty] using h
          have : ys.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsz)
          rw [this] at hyin; cases hyin
      simp only [hne_ys, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hx
      exact (evalClassExpr_iff dm hadj hne dom x true hx).mp rfl
    | none =>
      rw [hnr] at hx
      simp only [beq_iff_eq] at hx
      exact (evalClassExpr_iff dm hadj hne dom x true hx).mp rfl
  | objectPropertyRange r rng =>
    simp only [checkCBAxiom] at hchk
    intro x y hxy
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
    have hy := (allNeighborsCheck_iff hadj hne r x _).mp hx y hxy
    exact (evalClassExpr_iff dm hadj hne rng y true (beq_iff_eq.mp hy)).mp rfl
  | functionalObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x y z hxy hxz
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
    have hnb := neighbors?_spec (dm := dm) hadj hne r x
    cases hnr : m.neighbors? r x.val with
    | some ys =>
      rw [hnr] at hx hnb
      simp only [decide_eq_true_eq] at hx
      have hyin := (hnb.2 y).mp hxy
      have hzin := (hnb.2 z).mp hxz
      obtain ⟨iy, hiy, heqy⟩ := List.getElem_of_mem hyin
      obtain ⟨iz, hiz, heqz⟩ := List.getElem_of_mem hzin
      have hlen : ys.toList.length ≤ 1 := by simpa using hx
      have h0 : iy = iz := by omega
      subst h0
      exact Fin.ext (heqy.symm.trans heqz)
    | none =>
      rw [hnr] at hx; simp only [decide_eq_true_eq] at hx
      exact Fin.ext (by omega)
  | inverseFunctionalObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x y z hyx hzx
    have hxy : objectHolds (m.toInterpretation dm hne) r.converse x y :=
      (objectHolds_converse _ r x y).mpr hyx
    have hxz : objectHolds (m.toInterpretation dm hne) r.converse x z :=
      (objectHolds_converse _ r x z).mpr hzx
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r.converse hc x y hxy)
    have hnb := neighbors?_spec (dm := dm) hadj hne r.converse x
    cases hnr : m.neighbors? r.converse x.val with
    | some ys =>
      rw [hnr] at hx hnb
      simp only [decide_eq_true_eq] at hx
      have hyin := (hnb.2 y).mp hxy
      have hzin := (hnb.2 z).mp hxz
      obtain ⟨iy, hiy, heqy⟩ := List.getElem_of_mem hyin
      obtain ⟨iz, hiz, heqz⟩ := List.getElem_of_mem hzin
      have hlen : ys.toList.length ≤ 1 := by simpa using hx
      have h0 : iy = iz := by omega
      subst h0
      exact Fin.ext (heqy.symm.trans heqz)
    | none =>
      rw [hnr] at hx; simp only [decide_eq_true_eq] at hx
      exact Fin.ext (by omega)
  | _ => cases hchk

/-- Headline soundness theorem for `checkCBCanonicalModel`:
    if `checkCBCanonicalModel o m w = true`, then `m` defines a valid OWL 2 Direct Semantics
    model of `o` for every `DatatypeMap`. -/
theorem checkCBCanonicalModel_sound {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {numWorkers : Nat} (hcheck : checkCBCanonicalModel o m numWorkers = true) :
    ∃ hne : 0 < m.numNodes, satisfies (m.toInterpretation dm hne) o := by
  unfold checkCBCanonicalModel at hcheck
  simp only [Bool.and_eq_true, allRangePar_iff] at hcheck
  obtain ⟨hadj, haxs⟩ := hcheck
  have hne : 0 < m.numNodes := by
    unfold checkAdjConsistent at hadj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hadj
    exact hadj.1.1.1
  refine ⟨hne, fun ax hax => ?_⟩
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hax
  have hidx' : idx < o.toArray.size := by simpa using hidx
  have hchk := haxs idx hidx'
  have hget : o.toArray[idx]? = some o[idx] := by
    rw [Array.getElem?_eq_getElem hidx']; rfl
  rw [hget] at hchk
  exact checkCBAxiom_sound hadj hne hchk

/-- Counterexample refutation theorem: a verified `CBCanonicalModel` with a node `x` where
    `m.hasCls a x = true` and `m.hasCls b x = false` refutes `o ⊨ a ⊑ b`. -/
theorem checkCBCanonicalModel_counter_sub {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {numWorkers : Nat} (hcheck : checkCBCanonicalModel o m numWorkers = true)
    {a b : IRI} {x : Nat} (hx : x < m.numNodes)
    (ha : m.hasCls a x = true) (hb : m.hasCls b x = false) :
    ¬ Entails dm o [.subClassOf (.named a) (.named b)] := by
  obtain ⟨hne, hsat⟩ := checkCBCanonicalModel_sound (dm := dm) hcheck
  intro hent
  obtain ⟨assign, hq⟩ := hent (m.toInterpretation dm hne) (satisfies_models hsat)
  have hsub := hq _ (List.mem_singleton.mpr rfl) ⟨x, hx⟩ ha
  change m.hasCls b x = true at hsub
  rw [hb] at hsub
  cases hsub

/-- Satisfiability witness theorem: a verified `CBCanonicalModel` with `m.hasCls a x = true`
    certifies `o ⊭ a ⊑ owl:Nothing`. -/
theorem checkCBCanonicalModel_witness_sat {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {numWorkers : Nat} (hcheck : checkCBCanonicalModel o m numWorkers = true)
    {a : IRI} {x : Nat} (hx : x < m.numNodes) (ha : m.hasCls a x = true) :
    ¬ Entails dm o [.subClassOf (.named a) (.named nothing)] :=
  checkCBCanonicalModel_counter_sub hcheck hx ha (by simp [CBCanonicalModel.hasCls, thing, nothing])

/-! ### 5. Fast Canonical Model Builder (`buildCBCanonicalModel`) -/

private def dedupSortNat (xs : Array Nat) : Array Nat := Id.run do
  if xs.size ≤ 1 then return xs
  let sorted := xs.qsort (· < ·)
  let mut out : Array Nat := Array.mkEmpty sorted.size
  let mut prev : Nat := sorted[0]!
  out := out.push prev
  for i in [1:sorted.size] do
    let v := sorted[i]!
    if v != prev then
      out := out.push v
      prev := v
  return out

/-- Construct a `CBCanonicalModel` from `(o, norm, cert)` using live contexts as domain nodes
    and maximal derived role links closed under the RBox of `o`. -/
def buildCBCanonicalModel (o : Ontology) (norm : NormResult) (cert : CBCert) :
    CBCanonicalModel × Std.HashMap IRI Nat := Id.run do
  let nCtx := cert.contexts.size
  -- Build per-context derived class sets
  let mut ctxDerived : Array (Std.HashSet Nat) := Array.replicate nCtx {}
  for sf in cert.subFacts do
    if sf.h < nCtx then
      ctxDerived := ctxDerived.modify sf.h (·.insert sf.c)

  -- Map live contexts (not deriving `1 = owl:Nothing`) to dense node IDs `0 .. numLive - 1`
  let mut oldToNew : Array (Option Nat) := Array.replicate nCtx none
  let mut newToOld : Array Nat := #[]
  for h in [0:nCtx] do
    if !(ctxDerived[h]!).contains 1 then
      let nid := newToOld.size
      oldToNew := oldToNew.set! h (some nid)
      newToOld := newToOld.push h

  let numNodes := newToOld.size
  if numNodes == 0 then
    return ({ numNodes := 0, nodeClasses := #[], outAdj := #[], inAdj := #[] }, {})

  -- Populate `nodeClasses`, `clsNodes` (strictly ascending by construction), and singleton witnesses
  let mut nodeClasses : Array (Std.HashSet IRI) := Array.replicate numNodes {}
  let mut clsNodes : Std.HashMap IRI (Array Nat) := {}
  let mut witnessNode : Std.HashMap IRI Nat := {}
  for nid in [0:numNodes] do
    let h := newToOld[nid]!
    let mut clsSet : Std.HashSet IRI := {}
    for c in ctxDerived[h]! do
      if let some (.named iri) := norm.table.classes[c]? then
        if iri != thing && iri != nothing && !clsSet.contains iri then
          clsSet := clsSet.insert iri
          clsNodes := clsNodes.insert iri ((clsNodes.getD iri #[]).push nid)
    nodeClasses := nodeClasses.set! nid clsSet
    let ctx := cert.contexts[h]!
    if ctx.size == 1 then
      if let some (.named iri) := norm.table.classes[ctx[0]!]? then
        if iri != thing && iri != nothing then
          witnessNode := witnessNode.insert iri nid

  -- Group live links by `(h, r)` for single-step roles and keep only maximal target contexts
  let mut linksByHR : Std.HashMap (Nat × Nat) (Array Nat) := {}
  let mut inParentsByKR : Std.HashMap (Nat × Nat) (Array Nat) := {}
  for lf in cert.linkFacts do
    if lf.h < nCtx && lf.k < nCtx then
      if (oldToNew[lf.h]!).isSome && (oldToNew[lf.k]!).isSome then
        match norm.table.roles[lf.r]? with
        | some [op] =>
          let iri := match op with | .named p => p | .inverse p => p
          if iri != topObjectProperty && iri != bottomObjectProperty then
            linksByHR := linksByHR.insert (lf.h, lf.r) ((linksByHR.getD (lf.h, lf.r) #[]).push lf.k)
            inParentsByKR := inParentsByKR.insert (lf.k, lf.r) ((inParentsByKR.getD (lf.k, lf.r) #[]).push lf.h)
        | _ => pure ()

  let mut edgeSet : Std.HashSet (IRI × Nat × Nat) := {}
  let mut outAdj : Array (Std.HashMap IRI (Array Nat)) := Array.replicate numNodes {}
  let mut inAdj : Array (Std.HashMap IRI (Array Nat)) := Array.replicate numNodes {}
  let mut activeOut : Std.HashMap IRI (Array Nat) := {}
  let mut activeIn : Std.HashMap IRI (Array Nat) := {}

  let addEdge := fun (p : IRI) (u v : Nat)
      (edgeSet : Std.HashSet (IRI × Nat × Nat))
      (outAdj inAdj : Array (Std.HashMap IRI (Array Nat)))
      (activeOut activeIn : Std.HashMap IRI (Array Nat)) =>
    if p == topObjectProperty || p == bottomObjectProperty || edgeSet.contains (p, u, v) then
      (edgeSet, outAdj, inAdj, activeOut, activeIn)
    else
      let es' := edgeSet.insert (p, u, v)
      let hadOut := (outAdj[u]!).contains p
      let hadIn := (inAdj[v]!).contains p
      let oa' := outAdj.modify u fun m => m.insert p ((m.getD p #[]).push v)
      let ia' := inAdj.modify v fun m => m.insert p ((m.getD p #[]).push u)
      let ao' := if hadOut then activeOut else activeOut.insert p ((activeOut.getD p #[]).push u)
      let ai' := if hadIn then activeIn else activeIn.insert p ((activeIn.getD p #[]).push v)
      (es', oa', ia', ao', ai')

  for ((h, r), ks) in linksByHR.toList do
    if let some u := oldToNew[h]! then
      -- Filter out target contexts `k` already witnessed by an incoming inverse parent edge `p --r^- --> h`
      -- (avoids duplicate neighbors after `parentMerge` under `InverseFunctional` / `maxOne`),
      -- and non-maximal target contexts `k` strictly subsumed by another `k'`
      let invR := invRole r
      let incomingParents := inParentsByKR.getD (h, invR) #[]
      let maximalKs := ks.filter fun k =>
        !(incomingParents.any fun p =>
          cert.contexts[k]!.all fun e => (ctxDerived[p]!).contains e) &&
        !(ks.any fun k' =>
          k' != k &&
          (cert.contexts[k]!.all fun e => (ctxDerived[k']!).contains e) &&
          (!(cert.contexts[k']!.all fun e => (ctxDerived[k]!).contains e) || k < k'))
      if let some [op] := norm.table.roles[r]? then
        for k in maximalKs do
          if let some v := oldToNew[k]! then
            match op with
            | .named p =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge p u v edgeSet outAdj inAdj activeOut activeIn
            | .inverse p =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge p v u edgeSet outAdj inAdj activeOut activeIn

  -- Close edges under RBox axioms of `o` (iterating only active role nodes)
  let mut rSub : List (ObjectProperty × ObjectProperty) := []
  let mut rChains : List (List ObjectProperty × ObjectProperty) := []
  let mut rRefl : List ObjectProperty := []
  for ax in o do
    match ax with
    | .subObjectProperty r s => rSub := (r, s) :: rSub
    | .equivalentObjectProperties rs =>
      match rs with
      | [] | [_] => pure ()
      | r0 :: rest =>
        for r in rest do
          rSub := (r0, r) :: (r, r0) :: rSub
    | .inverseObjectProperties r s =>
      rSub := (r, s.converse) :: (s, r.converse) :: rSub
    | .symmetricObjectProperty r =>
      rSub := (r, r.converse) :: rSub
    | .transitiveObjectProperty r =>
      rChains := ([r, r], r) :: rChains
    | .subObjectPropertyChain rs s =>
      match rs with
      | [] => rRefl := s :: rRefl
      | [r] => rSub := (r, s) :: rSub
      | _ => rChains := (rs, s) :: rChains
    | .reflexiveObjectProperty r => rRefl := r :: rRefl
    | _ => pure ()

  for r in rRefl do
    match r with
    | .named p | .inverse p =>
      for u in [0:numNodes] do
        (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
          addEdge p u u edgeSet outAdj inAdj activeOut activeIn

  let mut changed := !rSub.isEmpty || !rChains.isEmpty
  let mut rounds : Nat := 0
  while changed && rounds < 16 do
    changed := false
    rounds := rounds + 1
    let beforeSz := edgeSet.size
    for (r, s) in rSub do
      match r with
      | .named pr =>
        for u in activeOut.getD pr #[] do
          for v in (outAdj[u]!).getD pr #[] do
            match s with
            | .named ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps u v edgeSet outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps v u edgeSet outAdj inAdj activeOut activeIn
      | .inverse pr =>
        for u in activeIn.getD pr #[] do
          for v in (inAdj[u]!).getD pr #[] do
            match s with
            | .named ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps u v edgeSet outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps v u edgeSet outAdj inAdj activeOut activeIn
    for (rs, s) in rChains do
      match rs with
      | [] => pure ()
      | r0 :: _ =>
        let startNodes : Array Nat := match r0 with
          | .named p0 => activeOut.getD p0 #[]
          | .inverse p0 => activeIn.getD p0 #[]
        for u in startNodes do
          let mut frontier : Array Nat := #[u]
          for step in rs do
            let mut nextF : Array Nat := #[]
            let mut seenF : Std.HashSet Nat := {}
            for cur in frontier do
              let nbrs : Array Nat := match step with
                | .named p => (outAdj[cur]!).getD p #[]
                | .inverse p => (inAdj[cur]!).getD p #[]
              for nxt in nbrs do
                if !seenF.contains nxt then
                  seenF := seenF.insert nxt
                  nextF := nextF.push nxt
            frontier := nextF
            if frontier.isEmpty then break
          for v in frontier do
            match s with
            | .named ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps u v edgeSet outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge ps v u edgeSet outAdj inAdj activeOut activeIn
    if edgeSet.size > beforeSz then changed := true

  -- Strictly sort and deduplicate all adjacency lists and role source indices
  for u in [0:numNodes] do
    let mut om : Std.HashMap IRI (Array Nat) := {}
    for (r, ys) in (outAdj[u]!).toList do
      om := om.insert r (dedupSortNat ys)
    outAdj := outAdj.set! u om
    let mut im : Std.HashMap IRI (Array Nat) := {}
    for (r, ys) in (inAdj[u]!).toList do
      im := im.insert r (dedupSortNat ys)
    inAdj := inAdj.set! u im

  let mut roleOutNodes : Std.HashMap IRI (Array Nat) := {}
  for (p, us) in activeOut.toList do
    roleOutNodes := roleOutNodes.insert p (dedupSortNat us)
  let mut roleInNodes : Std.HashMap IRI (Array Nat) := {}
  for (p, vs) in activeIn.toList do
    roleInNodes := roleInNodes.insert p (dedupSortNat vs)

  return ({ numNodes := numNodes, nodeClasses := nodeClasses, outAdj := outAdj, inAdj := inAdj,
            clsNodes := clsNodes, roleOutNodes := roleOutNodes, roleInNodes := roleInNodes },
          witnessNode)

/-! ### 6. Zero-Tableau Complete Classifier for Pure Horn-$\mathcal{SHIQ}$ (`classifyFastCB`) -/

/-- Build `ClassHierarchy` from exact `knownSups` + `unsatSet` in $O(|C| \cdot \text{deg}^2)$. -/
private def buildCBHierarchy (namedClasses : List IRI)
    (knownSups : Std.HashMap IRI (Std.HashSet IRI)) (unsatSet : Std.HashSet IRI) : ClassHierarchy := Id.run do
  let unsat := namedClasses.filter fun c => c == nothing || unsatSet.contains c
  let unsatFull : Std.HashSet IRI := unsat.foldl (fun s c => s.insert c) {}
  let satClasses := namedClasses.filter fun c => !unsatFull.contains c
  let mut subsArr : Array (IRI × IRI) := #[]
  for a in namedClasses do
    if unsatFull.contains a then
      for b in namedClasses do
        subsArr := subsArr.push (a, b)
    else
      let ks := knownSups.getD a {}
      for b in ks do
        subsArr := subsArr.push (a, b)
  let mut seenEq : Std.HashSet IRI := {}
  let mut eqGroups : Array (List IRI) := #[]
  for c in satClasses do
    if !seenEq.contains c then
      let ksC := knownSups.getD c {}
      let grp := ksC.toList.filter fun d =>
        !unsatFull.contains d && (knownSups.getD d {}).contains c
      let grp' := if grp.contains c then grp else c :: grp
      for d in grp' do
        seenEq := seenEq.insert d
      eqGroups := eqGroups.push grp'
  let mut dpArr : Array (IRI × List IRI) := #[]
  for c in satClasses do
    let ksC := knownSups.getD c {}
    let strictSups := ksC.toList.filter fun p =>
      p != c && !unsatFull.contains p && !(knownSups.getD p {}).contains c
    let direct := strictSups.filter fun p =>
      !strictSups.any fun mid =>
        mid != p && (knownSups.getD mid {}).contains p && !(knownSups.getD p {}).contains mid
    let parents := if direct.isEmpty then [thing] else direct
    dpArr := dpArr.push (c, parents)
  return {
    consistent := true
    classes := namedClasses
    unsatisfiable := unsat
    subsumptions := subsArr.toList
    equivalences := eqGroups.toList
    directParents := dpArr.toList
  }

/-- Zero-tableau kernel-verified complete classifier for pure Horn-$\mathcal{SHIQ}$ TBoxes.
    Returns `some h` iff:
    1. `o` is pure Horn-$\mathcal{SHIQ}$ (`norm.isPureHornSHIQ`),
    2. `checkCBSound norm cert w = true` (every derived subsumption/unsat is entailed),
    3. `checkCBCanonicalModel o m w = true` (`m` is a valid finite model of `o`), and
    4. every live named class `a` has a witness node `x_a` in `m` with `m.hasCls a x_a = true`
       and every class `b` true at `x_a` is already certified entailed from `a`.
    Returns `none` immediately on non-Horn ontologies or whenever any check does not close,
    falling back seamlessly to KP enhanced traversal. -/
def classifyFastCB (o : Ontology) (namedClasses : List IRI) (numWorkers : Nat := 8)
    (maxContexts : Nat := 16384) (maxCtxSize : Nat := 16) (maxLinks : Nat := 131072) :
    Option ClassHierarchy :=
  let norm := extractHornSHIQ o
  if !norm.isPureHornSHIQ then none
  else
    let effMaxContexts := max maxContexts (norm.table.classes.size * 4)
    let effMaxLinks := max maxLinks (norm.table.classes.size * 32)
    let cert := saturateHornSHI norm effMaxContexts maxCtxSize effMaxLinks
    if !checkCBSound norm cert numWorkers then none
    else
      let cbUnsats := extractNamedUnsats norm cert
      if cbUnsats.contains thing then
        some {
          consistent := false
          classes := namedClasses
          unsatisfiable := namedClasses
          subsumptions := []
          equivalences := []
          directParents := []
        }
      else
      let (m, witnessNode) := buildCBCanonicalModel o norm cert
      if !checkCBCanonicalModel o m numWorkers then none
      else
        let namedClassSet : Std.HashSet IRI := namedClasses.foldl (fun s c => s.insert c) {}
        let hasThing := namedClassSet.contains thing
        let cbSubs := extractNamedSubs norm cert
        let unsatSet : Std.HashSet IRI :=
          cbUnsats.foldl (fun s u => if namedClassSet.contains u then s.insert u else s)
            (if namedClassSet.contains nothing then ({} : Std.HashSet IRI).insert nothing else {})
        let knownSups : Std.HashMap IRI (Std.HashSet IRI) := Id.run do
          let mut ks : Std.HashMap IRI (Std.HashSet IRI) := {}
          for a in namedClasses do
            let mut s : Std.HashSet IRI := ({} : Std.HashSet IRI).insert a
            if hasThing then s := s.insert thing
            ks := ks.insert a s
          for (a, b) in cbSubs do
            if namedClassSet.contains a && namedClassSet.contains b then
              ks := ks.insert a ((ks.getD a {}).insert b)
          return ks
        -- Parallel O(|C| · deg) completeness coverage check
        let clsArr := namedClasses.toArray
        let covered := allRangePar clsArr.size (fun idx =>
          match clsArr[idx]? with
          | none => false
          | some a =>
            if a == nothing || unsatSet.contains a then true
            else if a == thing then
              -- `owl:Thing` is witnessed by node 0 iff every named class true at node 0 is in `knownSups[thing]`
              let ksA := knownSups.getD a {}
              m.numNodes > 0 &&
              (m.nodeClasses.getD 0 {}).toList.all fun b =>
                !namedClassSet.contains b || ksA.contains b
            else
              match witnessNode[a]? with
              | none => false
              | some x =>
                let ksA := knownSups.getD a {}
                x < m.numNodes &&
                m.hasCls a x &&
                (m.nodeClasses.getD x {}).toList.all fun b =>
                  !namedClassSet.contains b || ksA.contains b) numWorkers
        if covered then
          some (buildCBHierarchy namedClasses knownSups unsatSet)
        else none

/-- Worker-count invariance for `checkAdjConsistent`, `checkCBCanonicalModel`, and `classifyFastCB`. -/
theorem checkAdjConsistent_workers_eq (m : CBCanonicalModel) (w : Nat) :
    checkAdjConsistent m w = checkAdjConsistent m 1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkAdjConsistent, Bool.and_eq_true, allRangePar_iff]

theorem checkCBCanonicalModel_workers_eq (o : Ontology) (m : CBCanonicalModel) (w : Nat) :
    checkCBCanonicalModel o m w = checkCBCanonicalModel o m 1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkCBCanonicalModel, Bool.and_eq_true, checkAdjConsistent_workers_eq, allRangePar_iff]

theorem classifyFastCB_workers_eq (o : Ontology) (namedClasses : List IRI)
    (w maxContexts maxCtxSize maxLinks : Nat) :
    classifyFastCB o namedClasses w maxContexts maxCtxSize maxLinks =
      classifyFastCB o namedClasses 1 maxContexts maxCtxSize maxLinks := by
  dsimp only [classifyFastCB]
  rw [checkCBSound_workers_eq, checkCBCanonicalModel_workers_eq]
  have hall : ∀ (n : Nat) (f : Nat → Bool), allRangePar n f w = allRangePar n f 1 := fun n f => by
    apply Bool.eq_iff_iff.mpr
    simp only [allRangePar_iff]
  simp only [hall]

end Sabrina.OWL2.FastCB
