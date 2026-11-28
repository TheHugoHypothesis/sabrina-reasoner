import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.Classification
import Sabrina.OWL2.FastEL
import Sabrina.OWL2.FastLocality
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

/-- Predecessor nodes of `ys` along `r` (nodes `x` with `r(x, y)` for some `y ∈ ys`),
    aborting and returning `none` if the total size would exceed `limit`. -/
def rolePredecessors? (m : CBCanonicalModel) (r : ObjectProperty) (ys : Array Nat) (limit : Nat) :
    Option (Array Nat) :=
  match r with
  | .named p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else
      ys.foldl (fun acc? y =>
        match acc? with
        | none => none
        | some acc =>
          let xs := m.inNeighbors p y
          if acc.size + xs.size > limit then none
          else some (acc ++ xs)) (some #[])
  | .inverse p =>
    if p == topObjectProperty then none
    else if p == bottomObjectProperty then some #[]
    else
      ys.foldl (fun acc? y =>
        match acc? with
        | none => none
        | some acc =>
          let xs := m.outNeighbors p y
          if acc.size + xs.size > limit then none
          else some (acc ++ xs)) (some #[])

private theorem foldl_append_limit_mem {ys : List Nat} {f : Nat → Array Nat} {limit : Nat}
    {acc0 res : Array Nat}
    (h : ys.foldl (fun acc? y =>
      match acc? with
      | none => none
      | some acc =>
        let xs := f y
        if acc.size + xs.size > limit then none
        else some (acc ++ xs)) (some acc0) = some res) :
    (∀ z ∈ acc0.toList, z ∈ res.toList) ∧
    (∀ y ∈ ys, ∀ z ∈ (f y).toList, z ∈ res.toList) := by
  induction ys generalizing acc0 with
  | nil =>
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun _ hz => hz, fun _ hy => nomatch hy⟩
  | cons y tl ih =>
    simp only [List.foldl_cons] at h
    split at h
    · have hnone : tl.foldl (fun acc? y =>
        match acc? with
        | none => none
        | some acc =>
          let xs := f y
          if acc.size + xs.size > limit then none
          else some (acc ++ xs)) none = none := by
        clear h ih
        induction tl with
        | nil => rfl
        | cons _ _ ih' => exact ih'
      rw [hnone] at h; cases h
    · obtain ⟨hacc, htl⟩ := ih h
      refine ⟨fun z hz => hacc z (by simpa using Or.inl hz), fun y' hy' z hz => ?_⟩
      rcases List.mem_cons.mp hy' with rfl | hmem
      · exact hacc z (by simpa using Or.inr hz)
      · exact htl y' hmem z hz

private theorem rolePredecessors?_complete {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (r : ObjectProperty) {ys res : Array Nat} {limit : Nat}
    (h : rolePredecessors? m r ys limit = some res)
    (x y : Fin m.numNodes) (hxy : objectHolds (m.toInterpretation dm hne) r x y)
    (hy : y.val ∈ ys.toList) :
    x.val ∈ res.toList := by
  cases r with
  | named p =>
    unfold rolePredecessors? at h
    by_cases ht : p = topObjectProperty
    · subst ht; simp at h
    · by_cases hb : p = bottomObjectProperty
      · subst hb; exact ((m.toInterpretation dm hne).bottomObjectExt x y hxy).elim
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte, ← Array.foldl_toList] at h
        have ⟨_, hmem⟩ := foldl_append_limit_mem h
        have hout : (m.outNeighbors p x.val).contains y.val = true := by
          simpa [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge, hnt, hnb] using hxy
        have hin := (adjConsistent_in_iff hadj p y.isLt x.isLt).mpr hout
        exact hmem y.val hy x.val (by simpa [Array.contains_iff_mem] using hin)
  | inverse p =>
    unfold rolePredecessors? at h
    by_cases ht : p = topObjectProperty
    · subst ht; simp at h
    · by_cases hb : p = bottomObjectProperty
      · subst hb; exact ((m.toInterpretation dm hne).bottomObjectExt y x hxy).elim
      · have hnt : (p == topObjectProperty) = false := beq_false_of_ne ht
        have hnb : (p == bottomObjectProperty) = false := beq_false_of_ne hb
        simp only [hnt, hnb, Bool.false_eq_true, ↓reduceIte, ← Array.foldl_toList] at h
        have ⟨_, hmem⟩ := foldl_append_limit_mem h
        have hout : (m.outNeighbors p y.val).contains x.val = true := by
          simpa [objectHolds, CBCanonicalModel.toInterpretation, CBCanonicalModel.hasNamedEdge, hnt, hnb] using hxy
        exact hmem y.val hy x.val (by simpa [Array.contains_iff_mem] using hout)

/-- Candidate nodes where `ClassExpr` can hold in `m` (`none` = all nodes).
    Intersects/unions support sets and projects existential fillers backward along
    `inAdj`/`outAdj` so nested expressions like `∃has_part.(PATO_1 ⊓ ∃inheres_in.UBERON_2)`
    evaluate in $O(\text{filler-support})$ instead of scanning every `has_part` source. -/
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
  | .union a b =>
    match candidateNodes? m a, candidateNodes? m b with
    | some xa, some xb => some (xa ++ xb)
    | _, _ => none
  | .objectSome r f | .objectMin (_ + 1) r f | .objectExact (_ + 1) r f =>
    match roleSourceNodes? m r with
    | none => none
    | some srcs =>
      match candidateNodes? m f with
      | some ys =>
        if ys.size ≤ srcs.size then
          match rolePredecessors? m r ys srcs.size with
          | some preds => some preds
          | none => some srcs
        else some srcs
      | none => some srcs
  | .objectSelf r => roleSourceNodes? m r
  | _ => none

private theorem candidateNodes?_exist_complete {dm : DatatypeMap} {m : CBCanonicalModel} {w : Nat}
    (hadj : checkAdjConsistent m w = true) (hne : 0 < m.numNodes)
    (r : ObjectProperty) (f : ClassExpr) {xs : Array Nat}
    (ihf : ∀ {ys : Array Nat}, candidateNodes? m f = some ys →
      ∀ (y : Fin m.numNodes), classHolds (m.toInterpretation dm hne) y f → y.val ∈ ys.toList)
    (h : (match roleSourceNodes? m r with
      | none => none
      | some srcs =>
        match candidateNodes? m f with
        | some ys =>
          if ys.size ≤ srcs.size then
            match rolePredecessors? m r ys srcs.size with
            | some preds => some preds
            | none => some srcs
          else some srcs
        | none => some srcs) = some xs)
    (x y : Fin m.numNodes) (hxy : objectHolds (m.toInterpretation dm hne) r x y)
    (hyf : classHolds (m.toInterpretation dm hne) y f) :
    x.val ∈ xs.toList := by
  cases hsrc : roleSourceNodes? m r with
  | none => simp [hsrc] at h
  | some srcs =>
    simp only [hsrc] at h
    cases hf : candidateNodes? m f with
    | none =>
      simp only [hf, Option.some.injEq] at h
      subst h
      exact roleSourceNodes?_complete hadj hne r hsrc x y hxy
    | some ys =>
      simp only [hf] at h
      split at h
      · cases hpred : rolePredecessors? m r ys srcs.size with
        | none =>
          simp only [hpred, Option.some.injEq] at h
          subst h
          exact roleSourceNodes?_complete hadj hne r hsrc x y hxy
        | some preds =>
          simp only [hpred, Option.some.injEq] at h
          subst h
          exact rolePredecessors?_complete hadj hne r hpred x y hxy (ihf hf y hyf)
      · simp only [Option.some.injEq] at h
        subst h
        exact roleSourceNodes?_complete hadj hne r hsrc x y hxy

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
  | .union a b, xs, h, x, hx => by
    unfold candidateNodes? at h
    cases ha : candidateNodes? m a <;> cases hb : candidateNodes? m b <;>
      simp only [ha, hb] at h
    · cases h
    · cases h
    · cases h
    · cases h
      rcases hx with hxa | hxb
      · exact by simpa using Or.inl (candidateNodes?_complete hadj hne a ha x hxa)
      · exact by simpa using Or.inr (candidateNodes?_complete hadj hne b hb x hxb)
  | .objectSome r f, xs, h, x, ⟨y, hxy, hyf⟩ =>
    candidateNodes?_exist_complete hadj hne r f (candidateNodes?_complete hadj hne f) h x y hxy hyf
  | .objectSelf r, xs, h, x, hxx =>
    roleSourceNodes?_complete hadj hne r h x x hxx
  | .objectMin (_ + 1) r f, xs, h, x, ⟨ys, hlen, _, hpy⟩ => by
    cases ys with
    | nil => simp at hlen
    | cons y _ =>
      have ⟨hxy, hyf⟩ := hpy y (List.mem_cons_self ..)
      exact candidateNodes?_exist_complete hadj hne r f (candidateNodes?_complete hadj hne f) h x y hxy hyf
  | .objectExact (_ + 1) r f, xs, h, x, ⟨⟨ys, hlen, _, hpy⟩, _⟩ => by
    cases ys with
    | nil => simp at hlen
    | cons y _ =>
      have ⟨hxy, hyf⟩ := hpy y (List.mem_cons_self ..)
      exact candidateNodes?_exist_complete hadj hne r f (candidateNodes?_complete hadj hne f) h x y hxy hyf
  | .objectMin 0 _ _, _, h, _, _ => by cases h
  | .objectExact 0 _ _, _, h, _, _ => by cases h
  | .complement _, _, h, _, _ => by cases h
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

/-- Helper for pairwise `DisjointObjectProperties` checking in `checkCBAxiom`. -/
def checkDisjointObjProps (m : CBCanonicalModel) : List ObjectProperty → Bool
  | [] => true
  | r :: rest =>
    rest.all (fun s =>
      checkNodes m (roleSourceNodes? m r) fun x =>
        allNeighborsCheck m r x (fun y => !m.hasObjEdge s x y)) &&
    checkDisjointObjProps m rest

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
  | .irreflexiveObjectProperty r =>
    checkNodes m (roleSourceNodes? m r) fun x => !m.hasObjEdge r x x
  | .asymmetricObjectProperty r =>
    checkNodes m (roleSourceNodes? m r) fun x =>
      allNeighborsCheck m r x (fun y => !m.hasObjEdge r y x)
  | .disjointObjectProperties rs => checkDisjointObjProps m rs
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
  | irreflexiveObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x hxx
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x x hxx)
    have htrue := (hasObjEdge_iff r x x).mpr hxx
    rw [htrue] at hx; cases hx
  | asymmetricObjectProperty r =>
    simp only [checkCBAxiom] at hchk
    intro x y hxy hyx
    have hx := checkNodes_sound hchk x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
    have hy := (allNeighborsCheck_iff hadj hne r x _).mp hx y hxy
    have htrue := (hasObjEdge_iff r y x).mpr hyx
    rw [htrue] at hy; cases hy
  | disjointObjectProperties rs =>
    simp only [checkCBAxiom] at hchk
    induction rs with
    | nil => exact List.Pairwise.nil
    | cons r rest ih =>
      simp only [checkDisjointObjProps, Bool.and_eq_true, List.all_eq_true] at hchk
      refine List.pairwise_cons.mpr ⟨fun s hs x y ⟨hxy, hsxy⟩ => ?_, ih hchk.2⟩
      have hrs := hchk.1 s hs
      have hx := checkNodes_sound hrs x (fun xs hc => roleSourceNodes?_complete hadj hne r hc x y hxy)
      have hy := (allNeighborsCheck_iff hadj hne r x _).mp hx y hxy
      have htrue := (hasObjEdge_iff s x y).mpr hsxy
      rw [htrue] at hy; cases hy
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

  -- Identify roles constrained by `Functional` / `InverseFunctional` / `objectMax` / `objectExact`
  -- so the O(|ks|^2) `maximalKs` filter only runs where cardinality requires merging witnesses.
  let mut cardRoles : Std.HashSet IRI := {}
  let rec collectCardExpr (e : ClassExpr) (acc : Std.HashSet IRI) : Std.HashSet IRI :=
    match e with
    | .objectMax _ r c | .objectExact _ r c =>
      collectCardExpr c (acc.insert (Profile.objPropIRI r))
    | .complement c | .objectSome _ c | .objectAll _ c | .objectMin _ _ c =>
      collectCardExpr c acc
    | .intersection a b | .union a b => collectCardExpr b (collectCardExpr a acc)
    | _ => acc
  for ax in o do
    match ax with
    | .functionalObjectProperty r | .inverseFunctionalObjectProperty r =>
      cardRoles := cardRoles.insert (Profile.objPropIRI r)
    | .subClassOf a b => cardRoles := collectCardExpr b (collectCardExpr a cardRoles)
    | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
      for c in cs do cardRoles := collectCardExpr c cardRoles
    | _ => pure ()

  for ((h, r), ks) in linksByHR.toList do
    if let some u := oldToNew[h]! then
      if let some [op] := norm.table.roles[r]? then
        let opIri := Profile.objPropIRI op
        let chosenKs :=
          if cardRoles.contains opIri && ks.size ≤ 64 then
            let invR := invRole r
            let incomingParents := inParentsByKR.getD (h, invR) #[]
            ks.filter fun k =>
              !(incomingParents.any fun p =>
                cert.contexts[k]!.all fun e => (ctxDerived[p]!).contains e) &&
              !(ks.any fun k' =>
                k' != k &&
                (cert.contexts[k]!.all fun e => (ctxDerived[k']!).contains e) &&
                (!(cert.contexts[k']!.all fun e => (ctxDerived[k]!).contains e) || k < k'))
          else ks
        for k in chosenKs do
          if let some v := oldToNew[k]! then
            match op with
            | .named p =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge p u v edgeSet outAdj inAdj activeOut activeIn
            | .inverse p =>
              (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
                addEdge p v u edgeSet outAdj inAdj activeOut activeIn

  -- Add self-loops for `SubClassOf(C, ObjectHasSelf r)` / `EquivalentClasses([C, ObjectHasSelf r])`
  for ax in o do
    let selfPairs : List (IRI × ObjectProperty) := match ax with
      | .subClassOf (.named c) (.objectSelf r) => [(c, r)]
      | .equivalentClasses [.named c, .objectSelf r]
      | .equivalentClasses [.objectSelf r, .named c] => [(c, r)]
      | _ => []
    for (c, r) in selfPairs do
      let p := Profile.objPropIRI r
      for u in clsNodes.getD c #[] do
        (edgeSet, outAdj, inAdj, activeOut, activeIn) :=
          addEdge p u u edgeSet outAdj inAdj activeOut activeIn

  -- Close edges under RBox axioms of `o` (iterating only active role nodes, with per-role cap
  -- so dense symmetric/chain cliques never blow up the untrusted canonical model builder)
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

  let maxEdgesPerRole : Nat := 250000
  let maxTotalEdges : Nat := 1500000
  let mut roleEdgeCnt : Std.HashMap IRI Nat := {}
  let mut cappedRoles : Std.HashSet IRI := {}
  for (p, _, _) in edgeSet do
    roleEdgeCnt := roleEdgeCnt.insert p (roleEdgeCnt.getD p 0 + 1)

  let addEdgeCapped := fun (p : IRI) (u v : Nat)
      (edgeSet : Std.HashSet (IRI × Nat × Nat))
      (roleEdgeCnt : Std.HashMap IRI Nat)
      (cappedRoles : Std.HashSet IRI)
      (outAdj inAdj : Array (Std.HashMap IRI (Array Nat)))
      (activeOut activeIn : Std.HashMap IRI (Array Nat)) =>
    if edgeSet.size >= maxTotalEdges || cappedRoles.contains p ||
        p == topObjectProperty || p == bottomObjectProperty || edgeSet.contains (p, u, v) then
      (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn)
    else
      let cnt := roleEdgeCnt.getD p 0 + 1
      if cnt > maxEdgesPerRole then
        (edgeSet, roleEdgeCnt, cappedRoles.insert p, outAdj, inAdj, activeOut, activeIn)
      else
        let (es', oa', ia', ao', ai') := addEdge p u v edgeSet outAdj inAdj activeOut activeIn
        (es', roleEdgeCnt.insert p cnt, cappedRoles, oa', ia', ao', ai')

  let mut changed := !rSub.isEmpty || !rChains.isEmpty
  let mut rounds : Nat := 0
  while changed && rounds < 16 && edgeSet.size < maxTotalEdges do
    changed := false
    rounds := rounds + 1
    let beforeSz := edgeSet.size
    for (r, s) in rSub do
      let sp := Profile.objPropIRI s
      if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then continue
      match r with
      | .named pr =>
        for u in activeOut.getD pr #[] do
          if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
          for v in (outAdj[u]!).getD pr #[] do
            match s with
            | .named ps =>
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
      | .inverse pr =>
        for u in activeIn.getD pr #[] do
          if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
          for v in (inAdj[u]!).getD pr #[] do
            match s with
            | .named ps =>
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
    for (rs, s) in rChains do
      let sp := Profile.objPropIRI s
      if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then continue
      match rs with
      | [] => pure ()
      | r0 :: _ =>
        let startNodes : Array Nat := match r0 with
          | .named p0 => activeOut.getD p0 #[]
          | .inverse p0 => activeIn.getD p0 #[]
        for u in startNodes do
          if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
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
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
            | .inverse ps =>
              (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                addEdgeCapped ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
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

/-! ### 7. Nearly-Horn Partial-Model ⊥-Locality Refutation (`checkCBPartialModel`) -/

/-- Parallel kernel-verified partial-model checker for `o` on `CBCanonicalModel`
    restricted to signature `fs`:
    every axiom of `o` must either be syntactically ⊥-local w.r.t. `fs` (hence holds
    vacuously on `restrictToSig m fs.toSig`) or have its entire signature inside `fs`
    and hold on `m` (`checkCBAxiom m ax = true`). -/
def checkCBPartialModel (o : Ontology) (m : CBCanonicalModel) (fs : FastLocality.FastSig)
    (numWorkers : Nat := 8) : Bool :=
  let axArr := o.toArray
  checkAdjConsistent m numWorkers &&
  allRangePar axArr.size (fun idx =>
    match axArr[idx]? with
    | some ax =>
      FastLocality.isBotLocalAxiomFast fs ax ||
      (fs.coversSig (Profile.axiomSig ax) && checkCBAxiom m ax)
    | none => false) numWorkers

/-- Headline soundness theorem for `checkCBPartialModel`:
    if `checkCBPartialModel o m fs w = true`, then restricting `m` to `fs.toSig`
    defines a valid OWL 2 Direct Semantics model of the ENTIRE ontology `o`
    for arbitrary `DatatypeMap`. -/
theorem checkCBPartialModel_sound {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBPartialModel o m fs numWorkers = true) :
    ∃ hne : 0 < m.numNodes,
      satisfies (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) o := by
  unfold checkCBPartialModel at hcheck
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
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hchk
  rcases hchk with hloc | ⟨hcov, haxm⟩
  · rw [FastLocality.isBotLocalAxiomFast_eq] at hloc
    exact Profile.isBotLocalAxiom_sound (m.toInterpretation dm hne) fs.toSig hloc
  · have hsub := (FastLocality.FastSig.coversSig_iff fs (Profile.axiomSig o[idx])).mp hcov
    exact (Profile.restrictToSig_axiomHolds (m.toInterpretation dm hne) hsub).mpr
      (checkCBAxiom_sound hadj hne haxm)

/-- Counterexample refutation theorem for partial CB models:
    any witness node `x < m.numNodes` where `a` holds in `restrictToSig m fs.toSig`
    and `b` does not hold (either `b = nothing`, `b ∉ fs`, or `m.hasCls b x = false`)
    soundly refutes `o ⊨ a ⊑ b`. -/
theorem checkCBPartialModel_counter_sub {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBPartialModel o m fs numWorkers = true)
    {a b : IRI} {x : Nat} (hx : x < m.numNodes)
    (haSig : a = thing ∨ (a ≠ nothing ∧ fs.hasCls a = true))
    (ha : m.hasCls a x = true)
    (hb : b ≠ thing ∧ (b = nothing ∨ fs.hasCls b = false ∨ m.hasCls b x = false)) :
    ¬ Entails dm o [.subClassOf (.named a) (.named b)] := by
  obtain ⟨hne, hsat⟩ := checkCBPartialModel_sound (dm := dm) hcheck
  intro hent
  obtain ⟨assign, hq⟩ := hent (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig)
    (satisfies_models hsat)
  have haHolds : classHolds ((Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).withAnonymous assign)
      ⟨x, hx⟩ (.named a) := by
    simp only [classHolds, Interpretation.withAnonymous, Profile.restrictToSig]
    rcases haSig with rfl | ⟨han, has⟩
    · simp
    · by_cases hat : a = thing
      · simp [hat]
      · rw [FastLocality.FastSig.hasCls_eq] at has
        simp [hat, han, has]
        exact ha
  have hbHolds := hq _ (List.mem_singleton.mpr rfl) ⟨x, hx⟩ haHolds
  simp only [classHolds, Interpretation.withAnonymous, Profile.restrictToSig] at hbHolds
  obtain ⟨hbt, hbRest⟩ := hb
  simp only [hbt, ↓reduceIte] at hbRest hbHolds
  rcases hbRest with rfl | hbf | hbm
  · simp at hbHolds
  · rw [FastLocality.FastSig.hasCls_eq] at hbf
    by_cases hbn : b = nothing
    · simp [hbn] at hbHolds
    · simp [hbn, hbf] at hbHolds
  · by_cases hbn : b = nothing
    · simp [hbn] at hbHolds
    · simp only [hbn, ↓reduceIte] at hbHolds
      split at hbHolds
      · change m.hasCls b x = true at hbHolds
        rw [hbm] at hbHolds
        cases hbHolds
      · exact hbHolds

/-- Satisfiability witness theorem for partial CB models:
    any class `a` in `fs` (or `owl:Thing`) holding at `x < m.numNodes` in `m`
    is proved satisfiable in `o` (`o ⊭ a ⊑ owl:Nothing`). -/
theorem checkCBPartialModel_witness_sat {dm : DatatypeMap} {o : Ontology} {m : CBCanonicalModel}
    {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBPartialModel o m fs numWorkers = true)
    {a : IRI} {x : Nat} (hx : x < m.numNodes)
    (haSig : a = thing ∨ (a ≠ nothing ∧ fs.hasCls a = true))
    (ha : m.hasCls a x = true) :
    ¬ Entails dm o [.subClassOf (.named a) (.named nothing)] :=
  checkCBPartialModel_counter_sub hcheck hx haSig ha ⟨by simp [thing, nothing], Or.inl rfl⟩

theorem checkCBPartialModel_workers_eq (o : Ontology) (m : CBCanonicalModel)
    (fs : FastLocality.FastSig) (w : Nat) :
    checkCBPartialModel o m fs w = checkCBPartialModel o m fs 1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkCBPartialModel, Bool.and_eq_true, checkAdjConsistent_workers_eq, allRangePar_iff]

private def mapListChunks {α β : Type} (chunk : Nat) (f : α → β) :
    Nat → List α → List (Task (List β))
  | 0, xs => [Task.pure (xs.map f)]
  | _ + 1, [] => []
  | workers + 1, x :: xs =>
    let (front, rest) := (x :: xs).splitAt chunk
    Task.spawn (fun () => front.map f) :: mapListChunks chunk f workers rest

private theorem mapListChunks_get {α β : Type} (chunk : Nat) (f : α → β)
    (workers : Nat) (xs : List α) :
    (mapListChunks chunk f workers xs).flatMap Task.get = xs.map f := by
  induction workers generalizing xs with
  | zero => simp [mapListChunks]
  | succ workers ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [mapListChunks, List.splitAt_eq, List.flatMap_cons, Task.spawn, ih]
      rw [← List.map_append, List.take_append_drop]

private def mapListPar {α β : Type} (workers : Nat) (f : α → β) (xs : List α) : List β :=
  if workers ≤ 1 || xs.length ≤ 1 then xs.map f
  else
    let count := min workers xs.length
    let chunk := (xs.length + count - 1) / count
    (mapListChunks chunk f count xs).flatMap Task.get

private theorem mapListPar_eq {α β : Type} (workers : Nat) (f : α → β) (xs : List α) :
    mapListPar workers f xs = xs.map f := by
  unfold mapListPar
  split
  · rfl
  · exact mapListChunks_get ..

private inductive SigSym where
  | cls (iri : IRI)
  | obj (iri : IRI)
  | data (iri : IRI)
  deriving BEq, Hashable

private def symDeg (idx : FastLocality.LocalityIndex) : SigSym → Nat
  | .cls c => (idx.clsIdx.getD c #[]).size
  | .obj r => (idx.objIdx.getD r #[]).size
  | .data p => (idx.dataIdx.getD p #[]).size

private def pickCheaper (a b : Option (Nat × List SigSym)) : Option (Nat × List SigSym) :=
  match a, b with
  | some (ca, sa), some (cb, sb) => if ca ≤ cb then some (ca, sa) else some (cb, sb)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

private def combinePlans (a b : Option (Nat × List SigSym)) : Option (Nat × List SigSym) :=
  match a, b with
  | some (ca, sa), some (cb, sb) => some (ca + cb, sa ++ sb)
  | _, _ => none

private def planBotObj (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig)
    (r : ObjectProperty) : Option (Nat × List SigSym) :=
  let iri := Profile.objPropIRI r
  if iri == bottomObjectProperty then some (0, [])
  else if iri == topObjectProperty then none
  else if !fs.hasObj iri then some (0, [])
  else some (symDeg idx (.obj iri) + 1, [.obj iri])

private def planBotData (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig)
    (p : IRI) : Option (Nat × List SigSym) :=
  if p == bottomDataProperty then some (0, [])
  else if p == topDataProperty then none
  else if !fs.hasData p then some (0, [])
  else some (symDeg idx (.data p) + 1, [.data p])

mutual
  private def planBotExpr (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
      ClassExpr → Option (Nat × List SigSym)
    | .named c =>
      if c == nothing then some (0, [])
      else if c == thing then none
      else if !fs.hasCls c then some (0, [])
      else some (symDeg idx (.cls c) + 1, [.cls c])
    | .complement c => planTopExpr idx fs c
    | .intersection a b => pickCheaper (planBotExpr idx fs a) (planBotExpr idx fs b)
    | .union a b => combinePlans (planBotExpr idx fs a) (planBotExpr idx fs b)
    | .oneOf inds => if inds.isEmpty then some (0, []) else none
    | .objectSome r c => pickCheaper (planBotObj idx fs r) (planBotExpr idx fs c)
    | .objectAll _ _ => none
    | .objectValue r _ => planBotObj idx fs r
    | .objectSelf r => planBotObj idx fs r
    | .objectMin n r c =>
      if n > 0 then pickCheaper (planBotObj idx fs r) (planBotExpr idx fs c) else none
    | .objectMax _ _ _ => none
    | .objectExact n r c =>
      if n > 0 then pickCheaper (planBotObj idx fs r) (planBotExpr idx fs c) else none
    | .dataSome p _ | .dataValue p _ => planBotData idx fs p
    | .dataAll _ _ => none
    | .dataMin n p _ | .dataExact n p _ => if n > 0 then planBotData idx fs p else none
    | .dataMax _ _ _ => none

  private def planTopExpr (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
      ClassExpr → Option (Nat × List SigSym)
    | .named c => if c == thing then some (0, []) else none
    | .complement c => planBotExpr idx fs c
    | .intersection a b => combinePlans (planTopExpr idx fs a) (planTopExpr idx fs b)
    | .union a b => pickCheaper (planTopExpr idx fs a) (planTopExpr idx fs b)
    | .oneOf _ | .objectSome _ _ | .objectValue _ _ | .objectSelf _ | .objectExact _ _ _
    | .dataSome _ _ | .dataValue _ _ | .dataExact _ _ _ => none
    | .objectAll r c => pickCheaper (planBotObj idx fs r) (planTopExpr idx fs c)
    | .objectMin n _ _ => if n == 0 then some (0, []) else none
    | .objectMax _ r c => pickCheaper (planBotObj idx fs r) (planBotExpr idx fs c)
    | .dataAll p _ | .dataMax _ p _ => planBotData idx fs p
    | .dataMin n _ _ => if n == 0 then some (0, []) else none
end

private def planAtMostOne (plans : List (Option (Nat × List SigSym))) : Option (Nat × List SigSym) := Id.run do
  let mut noneCount : Nat := 0
  let mut maxCost : Nat := 0
  let mut maxIdx : Nat := 0
  let mut idxPos : Nat := 0
  let arr := plans.toArray
  for p in arr do
    match p with
    | none => noneCount := noneCount + 1
    | some (c, _) =>
      if c ≥ maxCost then
        maxCost := c
        maxIdx := idxPos
    idxPos := idxPos + 1
  if noneCount ≥ 2 then return none
  let mut totalCost : Nat := 0
  let mut syms : List SigSym := []
  for i in [0:arr.size] do
    let skip := if noneCount == 1 then arr[i]!.isNone else i == maxIdx
    if !skip then
      match arr[i]! with
      | none => return none
      | some (c, s) =>
        totalCost := totalCost + c
        syms := s ++ syms
  return some (totalCost, syms)

private def planBotLocalAxiom (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
    Axiom → Option (Nat × List SigSym)
  | .subClassOf a b => pickCheaper (planBotExpr idx fs a) (planTopExpr idx fs b)
  | .equivalentClasses cs =>
    let allBot := cs.foldl (fun acc c => combinePlans acc (planBotExpr idx fs c)) (some (0, []))
    let allTop := cs.foldl (fun acc c => combinePlans acc (planTopExpr idx fs c)) (some (0, []))
    pickCheaper allBot allTop
  | .disjointClasses cs => planAtMostOne (cs.map (planBotExpr idx fs))
  | .disjointUnion h cs =>
    cs.foldl (fun acc c => combinePlans acc (planBotExpr idx fs c)) (planBotExpr idx fs (.named h))
  | .subObjectProperty r s =>
    if Profile.isTopObjProp s then some (0, []) else planBotObj idx fs r
  | .subObjectPropertyChain rs s =>
    if Profile.isTopObjProp s then some (0, [])
    else rs.foldl (fun acc r => pickCheaper acc (planBotObj idx fs r)) none
  | .equivalentObjectProperties rs =>
    if rs.all Profile.isTopObjProp then some (0, [])
    else rs.foldl (fun acc r => combinePlans acc (planBotObj idx fs r)) (some (0, []))
  | .disjointObjectProperties rs => planAtMostOne (rs.map (planBotObj idx fs))
  | .inverseObjectProperties r s =>
    if Profile.isTopObjProp r && Profile.isTopObjProp s then some (0, [])
    else combinePlans (planBotObj idx fs r) (planBotObj idx fs s)
  | .objectPropertyDomain r c | .objectPropertyRange r c =>
    pickCheaper (planBotObj idx fs r) (planTopExpr idx fs c)
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .irreflexiveObjectProperty r | .symmetricObjectProperty r
  | .asymmetricObjectProperty r | .transitiveObjectProperty r =>
    planBotObj idx fs r
  | .reflexiveObjectProperty r =>
    if Profile.isTopObjProp r then some (0, []) else none
  | .subDataProperty r s =>
    if s == topDataProperty then some (0, []) else planBotData idx fs r
  | .equivalentDataProperties rs =>
    if rs.all (· == topDataProperty) then some (0, [])
    else rs.foldl (fun acc p => combinePlans acc (planBotData idx fs p)) (some (0, []))
  | .disjointDataProperties rs => planAtMostOne (rs.map (planBotData idx fs))
  | .dataPropertyDomain r c =>
    pickCheaper (planBotData idx fs r) (planTopExpr idx fs c)
  | .dataPropertyRange r _ | .functionalDataProperty r => planBotData idx fs r
  | .hasKey c rs ds =>
    let p0 := planBotExpr idx fs c
    let p1 := rs.foldl (fun acc r => pickCheaper acc (planBotObj idx fs r)) p0
    ds.foldl (fun acc p => pickCheaper acc (planBotData idx fs p)) p1
  | .classAssertion c _ => planTopExpr idx fs c
  | .objectAssertion r _ _ => if Profile.isTopObjProp r then some (0, []) else none
  | .negativeObjectAssertion r _ _ => planBotObj idx fs r
  | .dataAssertion p _ _ => if p == topDataProperty then some (0, []) else none
  | .negativeDataAssertion p _ _ => planBotData idx fs p
  | .datatypeDefinition _ _ | .sameIndividuals _ | .differentIndividuals _ => none

/-- Compute a maximal clean sub-signature `fs` of `idx` in $O(|O|)$ time such that
    every axiom failing `axOk` (and every axiom losing a symbol from `fs`) becomes
    syntactically ⊥-local w.r.t. `fs`. Untrusted heuristic — independently verified
    by `checkCBPartialModel`. -/
def buildCBPartialSig (idx : FastLocality.LocalityIndex) (axOk : Array Bool) :
    Option FastLocality.FastSig := Id.run do
  let n := idx.axioms.size
  if axOk.size != n then return none
  let mut clsSet : Std.HashSet IRI := {}
  for (c, _) in idx.clsIdx do
    clsSet := clsSet.insert c
  let mut objSet : Std.HashSet IRI := {}
  for (r, _) in idx.objIdx do
    objSet := objSet.insert r
  let mut dataSet : Std.HashSet IRI := {}
  for (p, _) in idx.dataIdx do
    dataSet := dataSet.insert p
  let mut fs : FastLocality.FastSig := ⟨clsSet, objSet, dataSet⟩
  let mut dropped : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for i in [0:n] do
    if !axOk[i]! then
      dropped := dropped.set! i true
      queue := queue.push i
  let mut head : Nat := 0
  while head < queue.size do
    let i := queue[head]!
    head := head + 1
    let some ax := idx.axioms[i]? | continue
    if FastLocality.isBotLocalAxiomFast fs ax then continue
    match planBotLocalAxiom idx fs ax with
    | none => return none
    | some (_, syms) =>
      for sym in syms do
        let mut hits : Array Nat := #[]
        match sym with
        | .cls c =>
          if fs.hasCls c then
            fs := { fs with cls := fs.cls.erase c }
            hits := idx.clsIdx.getD c #[]
        | .obj r =>
          if fs.hasObj r then
            fs := { fs with obj := fs.obj.erase r }
            hits := idx.objIdx.getD r #[]
        | .data p =>
          if fs.hasData p then
            fs := { fs with data := fs.data.erase p }
            hits := idx.dataIdx.getD p #[]
        for j in hits do
          if j < n && !dropped[j]! then
            dropped := dropped.set! j true
            if let some axj := idx.axioms[j]? then
              if !FastLocality.isBotLocalAxiomFast fs axj then
                queue := queue.push j
      if !FastLocality.isBotLocalAxiomFast fs ax then
        return none
  if fs.cls.isEmpty then return none
  return some fs

private def hasUnsupportedAlwaysNonLocal (idx : FastLocality.LocalityIndex) : Bool :=
  idx.alwaysNonLocal.any fun i =>
    match idx.axioms[i]? with
    | some (.classAssertion ..) | some (.objectAssertion ..) | some (.dataAssertion ..)
    | some (.sameIndividuals ..) | some (.differentIndividuals ..)
    | some (.datatypeDefinition ..) => true
    | _ => false

/-! ### 8. Disjoint-Union TBox+ABox Partial-Model Verification (`checkCBDisjointPartialModel`)

Extends `checkCBPartialModel` to arbitrary consistent ontologies containing ABox assertions,
`ObjectOneOf`/`ObjectHasValue` nominals, `HasKey`, and datatype axioms (as long as the ontology
does not mention `owl:topObjectProperty` or `owl:topDataProperty`): given any model `I_base ⊨ o`
(certified by consistency of `o`), the disjoint union `I_base ⊕ restrictToSig(m, fs)` with all
named/anonymous individuals placed in `I_base` satisfies EVERY axiom of `o`. -/

def objPropNotTop (r : ObjectProperty) : Bool :=
  Profile.objPropIRI r != topObjectProperty

def exprNoTopProp : ClassExpr → Bool
  | .named _ | .oneOf _ => true
  | .complement c => exprNoTopProp c
  | .intersection a b | .union a b => exprNoTopProp a && exprNoTopProp b
  | .objectSome r c | .objectAll r c | .objectMin _ r c | .objectMax _ r c | .objectExact _ r c =>
    objPropNotTop r && exprNoTopProp c
  | .objectValue r _ | .objectSelf r => objPropNotTop r
  | .dataSome p _ | .dataAll p _ | .dataValue p _ | .dataMin _ p _ | .dataMax _ p _ | .dataExact _ p _ =>
    p != topDataProperty

def axiomNoTopProp : Axiom → Bool
  | .subClassOf a b => exprNoTopProp a && exprNoTopProp b
  | .equivalentClasses cs | .disjointClasses cs => cs.all exprNoTopProp
  | .disjointUnion _ cs => cs.all exprNoTopProp
  | .subObjectProperty r s => objPropNotTop r && objPropNotTop s
  | .subObjectPropertyChain rs s => rs.all objPropNotTop && objPropNotTop s
  | .equivalentObjectProperties rs | .disjointObjectProperties rs => rs.all objPropNotTop
  | .inverseObjectProperties r s => objPropNotTop r && objPropNotTop s
  | .objectPropertyDomain r c | .objectPropertyRange r c => objPropNotTop r && exprNoTopProp c
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .reflexiveObjectProperty r | .irreflexiveObjectProperty r
  | .symmetricObjectProperty r | .asymmetricObjectProperty r
  | .transitiveObjectProperty r => objPropNotTop r
  | .subDataProperty r s => r != topDataProperty && s != topDataProperty
  | .equivalentDataProperties rs | .disjointDataProperties rs => rs.all (· != topDataProperty)
  | .dataPropertyDomain p c => p != topDataProperty && exprNoTopProp c
  | .dataPropertyRange p _ | .functionalDataProperty p => p != topDataProperty
  | .datatypeDefinition _ _ => true
  | .hasKey c rs ds => exprNoTopProp c && rs.all objPropNotTop && ds.all (· != topDataProperty)
  | .sameIndividuals _ | .differentIndividuals _ => true
  | .classAssertion c _ => exprNoTopProp c
  | .objectAssertion r _ _ | .negativeObjectAssertion r _ _ => objPropNotTop r
  | .dataAssertion p _ _ | .negativeDataAssertion p _ _ => p != topDataProperty

def exprNoIndivData : ClassExpr → Bool
  | .named _ => true
  | .complement c => exprNoIndivData c
  | .intersection a b | .union a b => exprNoIndivData a && exprNoIndivData b
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c | .objectMax _ _ c | .objectExact _ _ c =>
    exprNoIndivData c
  | .objectSelf _ => true
  | .oneOf _ | .objectValue _ _ | .dataSome _ _ | .dataAll _ _ | .dataValue _ _
  | .dataMin _ _ _ | .dataMax _ _ _ | .dataExact _ _ _ => false

def axiomNoIndivData : Axiom → Bool
  | .subClassOf a b => exprNoIndivData a && exprNoIndivData b
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs => cs.all exprNoIndivData
  | .objectPropertyDomain _ c | .objectPropertyRange _ c => exprNoIndivData c
  | .subObjectProperty .. | .subObjectPropertyChain .. | .equivalentObjectProperties ..
  | .disjointObjectProperties .. | .inverseObjectProperties ..
  | .functionalObjectProperty .. | .inverseFunctionalObjectProperty ..
  | .reflexiveObjectProperty .. | .irreflexiveObjectProperty ..
  | .symmetricObjectProperty .. | .asymmetricObjectProperty ..
  | .transitiveObjectProperty .. => true
  | _ => false

mutual
  def isZeroOnRightFast (fs : FastLocality.FastSig) : ClassExpr → Bool
    | .named c => c == nothing || (c != thing && !fs.hasCls c)
    | .complement c => isTopOnRightFast fs c
    | .intersection a b => isZeroOnRightFast fs a || isZeroOnRightFast fs b
    | .union a b => isZeroOnRightFast fs a && isZeroOnRightFast fs b
    | .oneOf _ => true
    | .objectSome r c => FastLocality.isBotObjPropFast fs r || isZeroOnRightFast fs c
    | .objectAll _ _ => false
    | .objectValue r _ => objPropNotTop r
    | .objectSelf r => FastLocality.isBotObjPropFast fs r
    | .objectMin n r c => decide (n > 0) && (FastLocality.isBotObjPropFast fs r || isZeroOnRightFast fs c)
    | .objectMax _ _ _ => false
    | .objectExact n r c => decide (n > 0) && (FastLocality.isBotObjPropFast fs r || isZeroOnRightFast fs c)
    | .dataSome p _ => p != topDataProperty
    | .dataAll _ _ => false
    | .dataValue p _ => p != topDataProperty
    | .dataMin n p _ => decide (n > 0) && (p != topDataProperty)
    | .dataMax _ _ _ => false
    | .dataExact n p _ => decide (n > 0) && (p != topDataProperty)

  def isTopOnRightFast (fs : FastLocality.FastSig) : ClassExpr → Bool
    | .named c => c == thing
    | .complement c => isZeroOnRightFast fs c
    | .intersection a b => isTopOnRightFast fs a && isTopOnRightFast fs b
    | .union a b => isTopOnRightFast fs a || isTopOnRightFast fs b
    | .oneOf _ | .objectSome _ _ | .objectValue _ _ | .objectSelf _ | .objectExact _ _ _
    | .dataSome _ _ | .dataValue _ _ | .dataExact _ _ _ => false
    | .objectAll r c => FastLocality.isBotObjPropFast fs r || isTopOnRightFast fs c
    | .objectMin n _ _ => n == 0
    | .objectMax _ r c => FastLocality.isBotObjPropFast fs r || isZeroOnRightFast fs c
    | .dataAll p _ => p != topDataProperty
    | .dataMin n _ _ => n == 0
    | .dataMax _ p _ => p != topDataProperty
end

def isRightLocalAxiomFast (fs : FastLocality.FastSig) : Axiom → Bool
  | .subClassOf a b => isZeroOnRightFast fs a || isTopOnRightFast fs b
  | .equivalentClasses cs => cs.all (isZeroOnRightFast fs) || cs.all (isTopOnRightFast fs)
  | .disjointClasses cs => Profile.atMostOne (fun c => !isZeroOnRightFast fs c) cs
  | .disjointUnion h cs => isZeroOnRightFast fs (.named h) && cs.all (isZeroOnRightFast fs)
  | .subObjectProperty r _ => FastLocality.isBotObjPropFast fs r
  | .subObjectPropertyChain rs _ => !rs.isEmpty && rs.any (FastLocality.isBotObjPropFast fs)
  | .equivalentObjectProperties rs => rs.all (FastLocality.isBotObjPropFast fs)
  | .disjointObjectProperties rs => Profile.atMostOne (fun r => !FastLocality.isBotObjPropFast fs r) rs
  | .inverseObjectProperties r s => FastLocality.isBotObjPropFast fs r && FastLocality.isBotObjPropFast fs s
  | .objectPropertyDomain r c | .objectPropertyRange r c =>
    FastLocality.isBotObjPropFast fs r || isTopOnRightFast fs c
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .irreflexiveObjectProperty r | .symmetricObjectProperty r
  | .asymmetricObjectProperty r | .transitiveObjectProperty r => FastLocality.isBotObjPropFast fs r
  | .reflexiveObjectProperty _ => false
  | .subDataProperty _ _ | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataPropertyDomain _ _ | .dataPropertyRange _ _ | .functionalDataProperty _
  | .datatypeDefinition _ _ | .hasKey _ _ _ | .sameIndividuals _ | .differentIndividuals _
  | .classAssertion _ _ | .objectAssertion _ _ _ | .negativeObjectAssertion _ _ _
  | .dataAssertion _ _ _ | .negativeDataAssertion _ _ _ => true

/-- Parallel kernel-verified disjoint-union TBox+ABox partial-model checker:
    every axiom of `o` must avoid `owl:topObjectProperty`/`owl:topDataProperty`, and
    must either hold trivially on the right component (`isRightLocalAxiomFast fs ax`),
    or be an individual/data-free TBox/RBox axiom covered by `fs` and verified on `m`. -/
def checkCBDisjointPartialModel (o : Ontology) (m : CBCanonicalModel) (fs : FastLocality.FastSig)
    (numWorkers : Nat := 8) : Bool :=
  let axArr := o.toArray
  checkAdjConsistent m numWorkers &&
  allRangePar axArr.size (fun idx =>
    match axArr[idx]? with
    | some ax =>
      axiomNoTopProp ax &&
      (isRightLocalAxiomFast fs ax ||
       (axiomNoIndivData ax && fs.coversSig (Profile.axiomSig ax) && checkCBAxiom m ax))
    | none => false) numWorkers

/-- Disjoint union `base ⊕ restrictToSig(m, fs)` placing all named/anonymous individuals
    in the `Sum.inl` (`base`) component and zero cross-component edges for non-top roles. -/
def disjointUnionInterp {dm : DatatypeMap} (base : Interpretation dm) (m : CBCanonicalModel)
    (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) : Interpretation dm where
  Object := Sum base.Object (Fin m.numNodes)
  objectNonempty := ⟨Sum.inr ⟨0, hne⟩⟩
  Data := base.Data
  dataNonempty := base.dataNonempty
  embedValue := base.embedValue
  embedValue_injective := base.embedValue_injective
  classes c
    | Sum.inl x => base.classes c x
    | Sum.inr y => (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).classes c y
  objectProperties r
    | Sum.inl x, Sum.inl y => base.objectProperties r x y
    | Sum.inr x, Sum.inr y =>
      (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).objectProperties r x y
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => r = topObjectProperty
  dataProperties p
    | Sum.inl x, d => base.dataProperties p x d
    | Sum.inr _, _ => p = topDataProperty
  individuals a := Sum.inl (base.individuals a)
  datatypes := base.datatypes
  literalValue := base.literalValue
  lexicalAgreement := base.lexicalAgreement
  named
    | Sum.inl x => base.named x
    | Sum.inr _ => False
  namedIndividual a := base.namedIndividual a
  thingExt := by
    intro z; cases z with
    | inl x => exact base.thingExt x
    | inr y => exact (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).thingExt y
  nothingExt := by
    intro z; cases z with
    | inl x => exact base.nothingExt x
    | inr y => exact (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).nothingExt y
  topObjectExt := by
    intro z1 z2; cases z1 with
    | inl x => cases z2 with
      | inl y => exact base.topObjectExt x y
      | inr _ => rfl
    | inr x => cases z2 with
      | inl _ => rfl
      | inr y => exact (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).topObjectExt x y
  bottomObjectExt := by
    intro z1 z2; cases z1 with
    | inl x => cases z2 with
      | inl y => exact base.bottomObjectExt x y
      | inr _ => simp [topObjectProperty, bottomObjectProperty]
    | inr x => cases z2 with
      | inl _ => simp [topObjectProperty, bottomObjectProperty]
      | inr y => exact (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig).bottomObjectExt x y
  topDataExt := by
    intro z d; cases z with
    | inl x => exact base.topDataExt x d
    | inr _ => rfl
  bottomDataExt := by
    intro z d; cases z with
    | inl x => exact base.bottomDataExt x d
    | inr _ => simp [topDataProperty, bottomDataProperty]
  literalDatatypeExt := base.literalDatatypeExt
  datatypeAgreement := base.datatypeAgreement

private theorem disjointUnion_dataHolds {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    (d : base.Data) (dr : DataRange) :
    dataHolds (disjointUnionInterp base m hne fs) d dr ↔ dataHolds base d dr := by
  induction dr with
  | datatype _ | oneOf _ | restriction _ _ => rfl
  | complement _ ih => exact not_congr ih
  | intersection _ _ ha hb => exact and_congr ha hb
  | union _ _ ha hb => exact or_congr ha hb

private theorem disjointUnion_obj_inl {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    {r : ObjectProperty} (hr : objPropNotTop r = true) (x : base.Object) :
    ∀ (z : Sum base.Object (Fin m.numNodes)),
      objectHolds (disjointUnionInterp base m hne fs) r (Sum.inl x) z ↔
        ∃ y, z = Sum.inl y ∧ objectHolds base r x y := by
  have hnt : Profile.objPropIRI r ≠ topObjectProperty := by
    simpa [objPropNotTop, bne_iff_ne] using hr
  intro z
  cases r with
  | named p | inverse p =>
    simp only [Profile.objPropIRI] at hnt
    cases z with
    | inl y => exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨_, he, h⟩ => Sum.inl.inj he ▸ h⟩
    | inr y => simp [objectHolds, disjointUnionInterp, hnt]

private theorem disjointUnion_obj_inr {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    {r : ObjectProperty} (hr : objPropNotTop r = true) (x : Fin m.numNodes) :
    ∀ (z : Sum base.Object (Fin m.numNodes)),
      objectHolds (disjointUnionInterp base m hne fs) r (Sum.inr x) z ↔
        ∃ y, z = Sum.inr y ∧
          objectHolds (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) r x y := by
  have hnt : Profile.objPropIRI r ≠ topObjectProperty := by
    simpa [objPropNotTop, bne_iff_ne] using hr
  intro z
  cases r with
  | named p | inverse p =>
    simp only [Profile.objPropIRI] at hnt
    cases z with
    | inl y => simp [objectHolds, disjointUnionInterp, hnt]
    | inr y => exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨_, he, h⟩ => Sum.inr.inj he ▸ h⟩

private theorem atLeast_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b)
    {n : Nat} {P : β → Prop} {Q : α → Prop}
    (h1 : ∀ z, P z → ∃ y, z = f y ∧ Q y) (h2 : ∀ y, Q y → P (f y)) :
    AtLeast n P ↔ AtLeast n Q := by
  constructor
  · rintro ⟨zs, hlen, hnd, hp⟩
    have hex : ∀ z ∈ zs, ∃ y, z = f y ∧ Q y := fun z hz => h1 z (hp z hz)
    let g : {z // z ∈ zs} → α := fun z => Classical.choose (hex z.1 z.2)
    have hg : ∀ z : {z // z ∈ zs}, z.1 = f (g z) ∧ Q (g z) := fun z => Classical.choose_spec (hex z.1 z.2)
    let ys := zs.attach.map g
    refine ⟨ys, by simp [ys, hlen], ?_, ?_⟩
    · have hmap : ys.map f = zs := by
        simp only [ys, List.map_map]
        have hfg : f ∘ g = Subtype.val := by
          funext x; exact (hg x).1.symm
        rw [hfg]; simp
      have : (ys.map f).Nodup := hmap ▸ hnd
      exact nodup_of_map' f this
    · intro y hy
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
      exact (hg z).2
  · rintro ⟨ys, hlen, hnd, hq⟩
    refine ⟨ys.map f, by simp [hlen], nodup_map_inj' hf hnd, ?_⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact h2 y (hq y hy)

private theorem atLeast_congr' {α : Type} {n : Nat} {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) :
    AtLeast n P ↔ AtLeast n Q :=
  ⟨fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun x hx => (h x).mp (hp x hx)⟩,
   fun ⟨xs, hl, hn, hp⟩ => ⟨xs, hl, hn, fun x hx => (h x).mpr (hp x hx)⟩⟩

private theorem disjointUnion_classHolds_inl {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (c : ClassExpr), exprNoTopProp c = true →
      ∀ (x : base.Object),
        classHolds (disjointUnionInterp base m hne fs) (Sum.inl x) c ↔ classHolds base x c
  | .named _, _, _ => Iff.rfl
  | .complement c, h, x => not_congr (disjointUnion_classHolds_inl base m hne fs c h x)
  | .intersection a b, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    exact and_congr (disjointUnion_classHolds_inl base m hne fs a h.1 x)
                    (disjointUnion_classHolds_inl base m hne fs b h.2 x)
  | .union a b, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    exact or_congr (disjointUnion_classHolds_inl base m hne fs a h.1 x)
                   (disjointUnion_classHolds_inl base m hne fs b h.2 x)
  | .oneOf inds, _, x => by
    simp only [classHolds, disjointUnionInterp]
    exact exists_congr fun a => and_congr_right fun _ => ⟨Sum.inl.inj, congrArg Sum.inl⟩
  | .objectSome r c, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    simp only [classHolds]
    constructor
    · rintro ⟨z, hz, hc⟩
      obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inl base m hne fs h.1 x z).mp hz
      exact ⟨y, hry, (disjointUnion_classHolds_inl base m hne fs c h.2 y).mp hc⟩
    · rintro ⟨y, hry, hc⟩
      exact ⟨Sum.inl y, (disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl y)).mpr ⟨y, rfl, hry⟩,
        (disjointUnion_classHolds_inl base m hne fs c h.2 y).mpr hc⟩
  | .objectAll r c, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    simp only [classHolds]
    constructor
    · intro hall y hry
      exact (disjointUnion_classHolds_inl base m hne fs c h.2 y).mp
        (hall (Sum.inl y) ((disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl y)).mpr ⟨y, rfl, hry⟩))
    · intro hall z hz
      obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inl base m hne fs h.1 x z).mp hz
      exact (disjointUnion_classHolds_inl base m hne fs c h.2 y).mpr (hall y hry)
  | .objectValue r a, h, x => by
    simp only [exprNoTopProp] at h
    change objectHolds (disjointUnionInterp base m hne fs) r (Sum.inl x) (Sum.inl (base.individuals a)) ↔
      objectHolds base r x (base.individuals a)
    rw [disjointUnion_obj_inl base m hne fs h x (Sum.inl (base.individuals a))]
    exact ⟨fun ⟨y, hy, hry⟩ => Sum.inl.inj hy ▸ hry, fun h' => ⟨base.individuals a, rfl, h'⟩⟩
  | .objectSelf r, h, x => by
    simp only [exprNoTopProp] at h
    simp only [classHolds, disjointUnion_obj_inl base m hne fs h x]
    exact ⟨fun ⟨y, hy, hry⟩ => Sum.inl.inj hy ▸ hry, fun h' => ⟨x, rfl, h'⟩⟩
  | .objectMin n r c, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    exact atLeast_of_inj (fun _ _ e => Sum.inl.inj e)
      (fun z ⟨hz, hc⟩ => by
        obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inl base m hne fs h.1 x z).mp hz
        exact ⟨y, rfl, hry, (disjointUnion_classHolds_inl base m hne fs c h.2 y).mp hc⟩)
      (fun y ⟨hry, hc⟩ =>
        ⟨(disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl y)).mpr ⟨y, rfl, hry⟩,
         (disjointUnion_classHolds_inl base m hne fs c h.2 y).mpr hc⟩)
  | .objectMax n r c, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    exact not_congr (atLeast_of_inj (fun _ _ e => Sum.inl.inj e)
      (fun z ⟨hz, hc⟩ => by
        obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inl base m hne fs h.1 x z).mp hz
        exact ⟨y, rfl, hry, (disjointUnion_classHolds_inl base m hne fs c h.2 y).mp hc⟩)
      (fun y ⟨hry, hc⟩ =>
        ⟨(disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl y)).mpr ⟨y, rfl, hry⟩,
         (disjointUnion_classHolds_inl base m hne fs c h.2 y).mpr hc⟩))
  | .objectExact n r c, h, x => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have h1 : ∀ k, AtLeast k (fun z => objectHolds (disjointUnionInterp base m hne fs) r (Sum.inl x) z ∧
        classHolds (disjointUnionInterp base m hne fs) z c) ↔
        AtLeast k (fun y => objectHolds base r x y ∧ classHolds base y c) :=
      fun k => atLeast_of_inj (n := k) (fun _ _ e => Sum.inl.inj e)
        (fun z ⟨hz, hc⟩ => by
          obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inl base m hne fs h.1 x z).mp hz
          exact ⟨y, rfl, hry, (disjointUnion_classHolds_inl base m hne fs c h.2 y).mp hc⟩)
        (fun y ⟨hry, hc⟩ =>
          ⟨(disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl y)).mpr ⟨y, rfl, hry⟩,
           (disjointUnion_classHolds_inl base m hne fs c h.2 y).mpr hc⟩)
    exact and_congr (h1 n) (not_congr (h1 (n + 1)))
  | .dataSome p dr, _, x =>
    exists_congr fun d => and_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr
  | .dataAll p dr, _, x =>
    forall_congr' fun d => imp_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr
  | .dataValue _ _, _, _ => Iff.rfl
  | .dataMin _ p dr, _, x =>
    atLeast_congr' fun d => and_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr
  | .dataMax _ p dr, _, x =>
    not_congr (atLeast_congr' fun d => and_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr)
  | .dataExact _ p dr, _, x =>
    and_congr
      (atLeast_congr' fun d => and_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr)
      (not_congr (atLeast_congr' fun d => and_congr_right fun _ => disjointUnion_dataHolds base m hne fs d dr))

private theorem disjointUnion_classHolds_inr {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (c : ClassExpr), exprNoTopProp c = true → exprNoIndivData c = true →
      ∀ (x : Fin m.numNodes),
        classHolds (disjointUnionInterp base m hne fs) (Sum.inr x) c ↔
          classHolds (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) x c
  | .named _, _, _, _ => Iff.rfl
  | .complement c, ht, hi, x => not_congr (disjointUnion_classHolds_inr base m hne fs c ht hi x)
  | .intersection a b, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    exact and_congr (disjointUnion_classHolds_inr base m hne fs a ht.1 hi.1 x)
                    (disjointUnion_classHolds_inr base m hne fs b ht.2 hi.2 x)
  | .union a b, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    exact or_congr (disjointUnion_classHolds_inr base m hne fs a ht.1 hi.1 x)
                   (disjointUnion_classHolds_inr base m hne fs b ht.2 hi.2 x)
  | .objectSome r c, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    simp only [classHolds]
    constructor
    · rintro ⟨z, hz, hc⟩
      obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs ht.1 x z).mp hz
      exact ⟨y, hry, (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mp hc⟩
    · rintro ⟨y, hry, hc⟩
      exact ⟨Sum.inr y, (disjointUnion_obj_inr base m hne fs ht.1 x (Sum.inr y)).mpr ⟨y, rfl, hry⟩,
        (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mpr hc⟩
  | .objectAll r c, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    simp only [classHolds]
    constructor
    · intro hall y hry
      exact (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mp
        (hall (Sum.inr y) ((disjointUnion_obj_inr base m hne fs ht.1 x (Sum.inr y)).mpr ⟨y, rfl, hry⟩))
    · intro hall z hz
      obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs ht.1 x z).mp hz
      exact (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mpr (hall y hry)
  | .objectSelf r, ht, _, x => by
    simp only [exprNoTopProp] at ht
    simp only [classHolds, disjointUnion_obj_inr base m hne fs ht x]
    exact ⟨fun ⟨y, hy, hry⟩ => Sum.inr.inj hy ▸ hry, fun h' => ⟨x, rfl, h'⟩⟩
  | .objectMin n r c, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    exact atLeast_of_inj (fun _ _ e => Sum.inr.inj e)
      (fun z ⟨hz, hc⟩ => by
        obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs ht.1 x z).mp hz
        exact ⟨y, rfl, hry, (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mp hc⟩)
      (fun y ⟨hry, hc⟩ =>
        ⟨(disjointUnion_obj_inr base m hne fs ht.1 x (Sum.inr y)).mpr ⟨y, rfl, hry⟩,
         (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mpr hc⟩)
  | .objectMax n r c, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    exact not_congr (atLeast_of_inj (fun _ _ e => Sum.inr.inj e)
      (fun z ⟨hz, hc⟩ => by
        obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs ht.1 x z).mp hz
        exact ⟨y, rfl, hry, (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mp hc⟩)
      (fun y ⟨hry, hc⟩ =>
        ⟨(disjointUnion_obj_inr base m hne fs ht.1 x (Sum.inr y)).mpr ⟨y, rfl, hry⟩,
         (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mpr hc⟩))
  | .objectExact n r c, ht, hi, x => by
    simp only [exprNoTopProp, exprNoIndivData, Bool.and_eq_true] at ht hi
    have h1 : ∀ k, AtLeast k (fun z => objectHolds (disjointUnionInterp base m hne fs) r (Sum.inr x) z ∧
        classHolds (disjointUnionInterp base m hne fs) z c) ↔
        AtLeast k (fun y =>
          objectHolds (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) r x y ∧
          classHolds (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) y c) :=
      fun k => atLeast_of_inj (n := k) (fun _ _ e => Sum.inr.inj e)
        (fun z ⟨hz, hc⟩ => by
          obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs ht.1 x z).mp hz
          exact ⟨y, rfl, hry, (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mp hc⟩)
        (fun y ⟨hry, hc⟩ =>
          ⟨(disjointUnion_obj_inr base m hne fs ht.1 x (Sum.inr y)).mpr ⟨y, rfl, hry⟩,
           (disjointUnion_classHolds_inr base m hne fs c ht.2 hi y).mpr hc⟩)
    exact and_congr (h1 n) (not_congr (h1 (n + 1)))
  | .oneOf _, _, hi, _ | .objectValue _ _, _, hi, _ | .dataSome _ _, _, hi, _
  | .dataAll _ _, _, hi, _ | .dataValue _ _, _, hi, _ | .dataMin _ _ _, _, hi, _
  | .dataMax _ _ _, _, hi, _ | .dataExact _ _ _, _, hi, _ => by cases hi

private theorem disjointUnion_botObj_inr {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    {r : ObjectProperty} (hb : FastLocality.isBotObjPropFast fs r = true)
    (x : Fin m.numNodes) (z : Sum base.Object (Fin m.numNodes)) :
    ¬ objectHolds (disjointUnionInterp base m hne fs) r (Sum.inr x) z := by
  have hb' : Profile.objPropIRI r = bottomObjectProperty ∨
      (Profile.objPropIRI r ≠ topObjectProperty ∧ fs.toSig.hasObj (Profile.objPropIRI r) = false) := by
    simp only [FastLocality.isBotObjPropFast, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, Bool.not_eq_true', FastLocality.FastSig.hasObj_eq] at hb
    exact hb
  have hnt : objPropNotTop r = true := by
    simp only [objPropNotTop, bne_iff_ne]
    rcases hb' with hbot | ⟨hnt', _⟩
    · rw [hbot]; decide
    · exact hnt'
  intro hxy
  obtain ⟨y, rfl, hry⟩ := (disjointUnion_obj_inr base m hne fs hnt x z).mp hxy
  cases r with
  | named p | inverse p =>
    simp only [Profile.objPropIRI] at hb'
    simp only [objectHolds, Profile.restrictToSig] at hry
    rcases hb' with rfl | ⟨hnt', hnf⟩
    · simp [topObjectProperty, bottomObjectProperty] at hry
    · by_cases hbot : p = bottomObjectProperty
      · simp [hbot, topObjectProperty, bottomObjectProperty] at hry
      · simp [hnt', hbot, hnf] at hry

private theorem isZeroTopOnRight_sound {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (c : ClassExpr), exprNoTopProp c = true →
      (∀ y : Fin m.numNodes, isZeroOnRightFast fs c = true →
        ¬ classHolds (disjointUnionInterp base m hne fs) (Sum.inr y) c) ∧
      (∀ y : Fin m.numNodes, isTopOnRightFast fs c = true →
        classHolds (disjointUnionInterp base m hne fs) (Sum.inr y) c)
  | .named cn, _ => by
    constructor
    · intro y hz hc
      simp only [isZeroOnRightFast, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        bne_iff_ne, Bool.not_eq_true'] at hz
      simp only [classHolds, disjointUnionInterp, Profile.restrictToSig] at hc
      rcases hz with rfl | ⟨hnt, hnf⟩
      · simp [thing, nothing] at hc
      · rw [FastLocality.FastSig.hasCls_eq] at hnf
        by_cases hcn : cn = nothing
        · simp [hcn, thing, nothing] at hc
        · simp [hnt, hcn, hnf] at hc
    · intro y ht
      simp only [isTopOnRightFast, beq_iff_eq] at ht
      subst ht; simp [classHolds, disjointUnionInterp, Profile.restrictToSig]
  | .complement c, h => by
    have ih := isZeroTopOnRight_sound base m hne fs c h
    exact ⟨fun y hz hc => hc (ih.2 y hz), fun y ht => ih.1 y ht⟩
  | .intersection a b, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have iha := isZeroTopOnRight_sound base m hne fs a h.1
    have ihb := isZeroTopOnRight_sound base m hne fs b h.2
    refine ⟨fun y hz ⟨ha, hb⟩ => ?_, fun y ht => ?_⟩
    · simp only [isZeroOnRightFast, Bool.or_eq_true] at hz
      exact hz.elim (fun h1 => iha.1 y h1 ha) (fun h2 => ihb.1 y h2 hb)
    · simp only [isTopOnRightFast, Bool.and_eq_true] at ht
      exact ⟨iha.2 y ht.1, ihb.2 y ht.2⟩
  | .union a b, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have iha := isZeroTopOnRight_sound base m hne fs a h.1
    have ihb := isZeroTopOnRight_sound base m hne fs b h.2
    refine ⟨fun y hz hdisj => ?_, fun y ht => ?_⟩
    · simp only [isZeroOnRightFast, Bool.and_eq_true] at hz
      exact hdisj.elim (iha.1 y hz.1) (ihb.1 y hz.2)
    · simp only [isTopOnRightFast, Bool.or_eq_true] at ht
      exact ht.elim (Or.inl ∘ iha.2 y) (Or.inr ∘ ihb.2 y)
  | .oneOf inds, _ =>
    ⟨fun y _ ⟨a, _, heq⟩ => by simp [disjointUnionInterp] at heq, fun _ ht => by cases ht⟩
  | .objectSome r c, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have ih := isZeroTopOnRight_sound base m hne fs c h.2
    refine ⟨fun y hz ⟨z, hrz, hcz⟩ => ?_, fun _ ht => by cases ht⟩
    simp only [isZeroOnRightFast, Bool.or_eq_true] at hz
    rcases hz with hrb | hcb
    · exact disjointUnion_botObj_inr base m hne fs hrb y z hrz
    · obtain ⟨w, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs h.1 y z).mp hrz
      exact ih.1 w hcb hcz
  | .objectAll r c, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have ih := isZeroTopOnRight_sound base m hne fs c h.2
    refine ⟨fun _ hz => (by cases hz), fun y ht z hrz => ?_⟩
    simp only [isTopOnRightFast, Bool.or_eq_true] at ht
    rcases ht with hrb | hct
    · exact absurd hrz (disjointUnion_botObj_inr base m hne fs hrb y z)
    · obtain ⟨w, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs h.1 y z).mp hrz
      exact ih.2 w hct
  | .objectValue r a, h => by
    refine ⟨fun y _ hrv => ?_, fun _ ht => by cases ht⟩
    obtain ⟨w, heq, _⟩ := (disjointUnion_obj_inr base m hne fs h y (Sum.inl (base.individuals a))).mp hrv
    cases heq
  | .objectSelf r, h =>
    ⟨fun y hz hrr => disjointUnion_botObj_inr base m hne fs hz y (Sum.inr y) hrr, fun _ ht => by cases ht⟩
  | .objectMin n r c, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have ih := isZeroTopOnRight_sound base m hne fs c h.2
    refine ⟨fun y hz ⟨zs, hlen, _, hp⟩ => ?_, fun y ht => ?_⟩
    · simp only [isZeroOnRightFast, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hz
      cases zs with
      | nil => simp at hlen; omega
      | cons z _ =>
        have ⟨hrz, hcz⟩ := hp z (List.mem_cons_self ..)
        rcases hz.2 with hrb | hcb
        · exact disjointUnion_botObj_inr base m hne fs hrb y z hrz
        · obtain ⟨w, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs h.1 y z).mp hrz
          exact ih.1 w hcb hcz
    · simp only [isTopOnRightFast, beq_iff_eq] at ht; subst ht
      exact ⟨[], rfl, List.Pairwise.nil, fun _ hm => nomatch hm⟩
  | .objectMax n r c, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have ih := isZeroTopOnRight_sound base m hne fs c h.2
    refine ⟨fun _ hz => (by cases hz), fun y ht ⟨zs, hlen, _, hp⟩ => ?_⟩
    simp only [isTopOnRightFast, Bool.or_eq_true] at ht
    cases zs with
    | nil => simp at hlen
    | cons z _ =>
      have ⟨hrz, hcz⟩ := hp z (List.mem_cons_self ..)
      rcases ht with hrb | hcb
      · exact disjointUnion_botObj_inr base m hne fs hrb y z hrz
      · obtain ⟨w, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs h.1 y z).mp hrz
        exact ih.1 w hcb hcz
  | .objectExact n r c, h => by
    simp only [exprNoTopProp, Bool.and_eq_true] at h
    have ih := isZeroTopOnRight_sound base m hne fs c h.2
    refine ⟨fun y hz ⟨⟨zs, hlen, _, hp⟩, _⟩ => ?_, fun _ ht => by cases ht⟩
    simp only [isZeroOnRightFast, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hz
    cases zs with
    | nil => simp at hlen; omega
    | cons z _ =>
      have ⟨hrz, hcz⟩ := hp z (List.mem_cons_self ..)
      rcases hz.2 with hrb | hcb
      · exact disjointUnion_botObj_inr base m hne fs hrb y z hrz
      · obtain ⟨w, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs h.1 y z).mp hrz
        exact ih.1 w hcb hcz
  | .dataSome p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    exact ⟨fun y _ ⟨_, hd, _⟩ => hnt hd, fun _ ht => by cases ht⟩
  | .dataAll p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    exact ⟨fun _ hz => (by cases hz), fun y _ _ hd => absurd hd hnt⟩
  | .dataValue p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    exact ⟨fun y _ hd => hnt hd, fun _ ht => by cases ht⟩
  | .dataMin n p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    refine ⟨fun y hz ⟨ds, hlen, _, hp⟩ => ?_, fun y ht => ?_⟩
    · simp only [isZeroOnRightFast, Bool.and_eq_true, decide_eq_true_eq] at hz
      cases ds with
      | nil => simp at hlen; omega
      | cons d _ => exact hnt (hp d (List.mem_cons_self ..)).1
    · simp only [isTopOnRightFast, beq_iff_eq] at ht; subst ht
      exact ⟨[], rfl, List.Pairwise.nil, fun _ hm => nomatch hm⟩
  | .dataMax _ p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    refine ⟨fun _ hz => (by cases hz), fun y _ ⟨ds, hlen, _, hp⟩ => ?_⟩
    cases ds with
    | nil => simp at hlen
    | cons d _ => exact hnt (hp d (List.mem_cons_self ..)).1
  | .dataExact n p _, h => by
    have hnt : p ≠ topDataProperty := by simpa [exprNoTopProp, bne_iff_ne] using h
    refine ⟨fun y hz ⟨⟨ds, hlen, _, hp⟩, _⟩ => ?_, fun _ ht => by cases ht⟩
    simp only [isZeroOnRightFast, Bool.and_eq_true, decide_eq_true_eq] at hz
    cases ds with
    | nil => simp at hlen; omega
    | cons d _ => exact hnt (hp d (List.mem_cons_self ..)).1

private theorem disjointUnion_rolePath_inl {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (rs : List ObjectProperty), rs.all objPropNotTop = true →
      ∀ (x : base.Object) (z : Sum base.Object (Fin m.numNodes)),
        rolePath (disjointUnionInterp base m hne fs) rs (Sum.inl x) z ↔
          ∃ y, z = Sum.inl y ∧ rolePath base rs x y
  | [], _, x, z => by
    cases z with
    | inl y => exact ⟨fun h => ⟨y, rfl, Sum.inl.inj h⟩, fun ⟨_, he, h⟩ => Sum.inl.inj he ▸ congrArg Sum.inl h⟩
    | inr y => simp [rolePath]
  | r :: rs, h, x, z => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    constructor
    · rintro ⟨mid, hr, hrest⟩
      obtain ⟨m0, rfl, hrm⟩ := (disjointUnion_obj_inl base m hne fs h.1 x mid).mp hr
      obtain ⟨y, rfl, hy⟩ := (disjointUnion_rolePath_inl base m hne fs rs h.2 m0 z).mp hrest
      exact ⟨y, rfl, m0, hrm, hy⟩
    · rintro ⟨y, rfl, m0, hrm, hy⟩
      exact ⟨Sum.inl m0, (disjointUnion_obj_inl base m hne fs h.1 x (Sum.inl m0)).mpr ⟨m0, rfl, hrm⟩,
        (disjointUnion_rolePath_inl base m hne fs rs h.2 m0 (Sum.inl y)).mpr ⟨y, rfl, hy⟩⟩

private theorem disjointUnion_rolePath_inr {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (rs : List ObjectProperty), rs.all objPropNotTop = true →
      ∀ (x : Fin m.numNodes) (z : Sum base.Object (Fin m.numNodes)),
        rolePath (disjointUnionInterp base m hne fs) rs (Sum.inr x) z ↔
          ∃ y, z = Sum.inr y ∧
            rolePath (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) rs x y
  | [], _, x, z => by
    cases z with
    | inl y => simp [rolePath]
    | inr y => exact ⟨fun h => ⟨y, rfl, Sum.inr.inj h⟩, fun ⟨_, he, h⟩ => Sum.inr.inj he ▸ congrArg Sum.inr h⟩
  | r :: rs, h, x, z => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    constructor
    · rintro ⟨mid, hr, hrest⟩
      obtain ⟨m0, rfl, hrm⟩ := (disjointUnion_obj_inr base m hne fs h.1 x mid).mp hr
      obtain ⟨y, rfl, hy⟩ := (disjointUnion_rolePath_inr base m hne fs rs h.2 m0 z).mp hrest
      exact ⟨y, rfl, m0, hrm, hy⟩
    · rintro ⟨y, rfl, m0, hrm, hy⟩
      exact ⟨Sum.inr m0, (disjointUnion_obj_inr base m hne fs h.1 x (Sum.inr m0)).mpr ⟨m0, rfl, hrm⟩,
        (disjointUnion_rolePath_inr base m hne fs rs h.2 m0 (Sum.inr y)).mpr ⟨y, rfl, hy⟩⟩

private theorem disjointUnion_rolePath_bot_inr {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig) :
    ∀ (rs : List ObjectProperty), rs.all objPropNotTop = true →
      rs.any (FastLocality.isBotObjPropFast fs) = true →
      ∀ (x : Fin m.numNodes) (z : Sum base.Object (Fin m.numNodes)),
        ¬ rolePath (disjointUnionInterp base m hne fs) rs (Sum.inr x) z
  | [], _, hany, _, _ => by simp at hany
  | r :: rs, hnt, hany, x, z => by
    simp only [List.all_cons, Bool.and_eq_true] at hnt
    simp only [List.any_cons, Bool.or_eq_true] at hany
    rintro ⟨mid, hrm, hrest⟩
    rcases hany with hrb | hrestb
    · exact disjointUnion_botObj_inr base m hne fs hrb x mid hrm
    · obtain ⟨m0, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x mid).mp hrm
      exact disjointUnion_rolePath_bot_inr base m hne fs rs hnt.2 hrestb m0 z hrest

private theorem disjointUnion_pairwise_atMostOne {α : Type} {P : α → Prop} {f : α → Bool}
    (hf : ∀ x, f x = true → ¬ P x) :
    ∀ {xs : List α}, Profile.atMostOne (fun x => !f x) xs = true →
      xs.Pairwise (fun a b => ¬ (P a ∧ P b))
  | [], _ => List.Pairwise.nil
  | x :: tl, h => by
    simp only [Profile.atMostOne] at h
    cases hfx : f x with
    | true =>
      simp only [hfx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact List.pairwise_cons.mpr ⟨fun _ _ ⟨hx, _⟩ => hf x hfx hx,
        disjointUnion_pairwise_atMostOne hf h⟩
    | false =>
      simp only [hfx, Bool.not_false, ↓reduceIte, List.all_eq_true, Bool.not_not] at h
      refine List.pairwise_cons.mpr ⟨fun y hy ⟨_, hyP⟩ => hf y (h y hy) hyP, ?_⟩
      exact pairwise_of_all_not (fun y hy => hf y (h y hy))

private theorem disjointUnion_axiom_rightLocal {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    {ax : Axiom} (hnt : axiomNoTopProp ax = true) (hloc : isRightLocalAxiomFast fs ax = true)
    (hbase : axiomHolds base ax) :
    axiomHolds (disjointUnionInterp base m hne fs) ax := by
  let U := disjointUnionInterp base m hne fs
  cases ax with
  | subClassOf a b =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.or_eq_true] at hloc
    intro z hz
    cases z with
    | inl x =>
      exact (disjointUnion_classHolds_inl base m hne fs b hnt.2 x).mpr
        (hbase x ((disjointUnion_classHolds_inl base m hne fs a hnt.1 x).mp hz))
    | inr y =>
      rcases hloc with hza | htb
      · exact absurd hz ((isZeroTopOnRight_sound base m hne fs a hnt.1).1 y hza)
      · exact (isZeroTopOnRight_sound base m hne fs b hnt.2).2 y htb
  | equivalentClasses cs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.or_eq_true, List.all_eq_true] at hloc
    intro a ha b hb z
    cases z with
    | inl x =>
      exact (disjointUnion_classHolds_inl base m hne fs a (hnt a ha) x).trans
        ((hbase a ha b hb x).trans (disjointUnion_classHolds_inl base m hne fs b (hnt b hb) x).symm)
    | inr y =>
      rcases hloc with hzero | htop
      · exact ⟨fun h => absurd h ((isZeroTopOnRight_sound base m hne fs a (hnt a ha)).1 y (hzero a ha)),
               fun h => absurd h ((isZeroTopOnRight_sound base m hne fs b (hnt b hb)).1 y (hzero b hb))⟩
      · exact ⟨fun _ => (isZeroTopOnRight_sound base m hne fs b (hnt b hb)).2 y (htop b hb),
               fun _ => (isZeroTopOnRight_sound base m hne fs a (hnt a ha)).2 y (htop a ha)⟩
  | disjointClasses cs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    have hpwR : ∀ y : Fin m.numNodes,
        cs.Pairwise (fun a b => ¬ (classHolds U (Sum.inr y) a ∧ classHolds U (Sum.inr y) b)) := by
      intro y
      have : ∀ (ls : List ClassExpr), (∀ c ∈ ls, exprNoTopProp c = true) →
          Profile.atMostOne (fun c => !isZeroOnRightFast fs c) ls = true →
          ls.Pairwise (fun a b => ¬ (classHolds U (Sum.inr y) a ∧ classHolds U (Sum.inr y) b)) := by
        intro ls hls hat
        induction ls with
        | nil => exact List.Pairwise.nil
        | cons c tl ih =>
          simp only [Profile.atMostOne] at hat
          cases hc : isZeroOnRightFast fs c with
          | true =>
            simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hat
            exact List.pairwise_cons.mpr
              ⟨fun _ _ ⟨hcy, _⟩ => (isZeroTopOnRight_sound base m hne fs c (hls c (List.mem_cons_self ..))).1 y hc hcy,
               ih (fun d hd => hls d (List.mem_cons_of_mem _ hd)) hat⟩
          | false =>
            simp only [hc, Bool.not_false, ↓reduceIte, List.all_eq_true, Bool.not_not] at hat
            have hnone : ∀ d ∈ tl, ¬ classHolds U (Sum.inr y) d := fun d hd =>
              (isZeroTopOnRight_sound base m hne fs d (hls d (List.mem_cons_of_mem _ hd))).1 y (hat d hd)
            exact List.pairwise_cons.mpr ⟨fun d hd ⟨_, hdy⟩ => hnone d hd hdy, pairwise_of_all_not hnone⟩
      exact this cs hnt hloc
    clear hloc
    revert hbase hnt hpwR
    induction cs with
    | nil => intro _ _ _; exact List.Pairwise.nil
    | cons a tl ih =>
      intro hbase hnt hpwR
      refine List.pairwise_cons.mpr ⟨fun b hb z ⟨hza, hzb⟩ => ?_,
        ih (List.pairwise_cons.mp hbase).2 (fun c hc => hnt c (List.mem_cons_of_mem _ hc))
           (fun y => (List.pairwise_cons.mp (hpwR y)).2)⟩
      cases z with
      | inl x =>
        exact (List.pairwise_cons.mp hbase).1 b hb x
          ⟨(disjointUnion_classHolds_inl base m hne fs a (hnt a (List.mem_cons_self ..)) x).mp hza,
           (disjointUnion_classHolds_inl base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) x).mp hzb⟩
      | inr y =>
        exact (List.pairwise_cons.mp (hpwR y)).1 b hb ⟨hza, hzb⟩
  | disjointUnion h cs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.and_eq_true, List.all_eq_true] at hloc
    refine ⟨fun z => ?_, ?_⟩
    · cases z with
      | inl x =>
        have h1 := hbase.1 x
        exact h1.trans (exists_congr fun c => and_congr_right fun hc =>
          (disjointUnion_classHolds_inl base m hne fs c (hnt c hc) x).symm)
      | inr y =>
        constructor
        · intro hh
          exact absurd hh ((isZeroTopOnRight_sound base m hne fs (.named h) rfl).1 y hloc.1)
        · rintro ⟨c, hc, hcy⟩
          exact absurd hcy ((isZeroTopOnRight_sound base m hne fs c (hnt c hc)).1 y (hloc.2 c hc))
    · have hpwBase := hbase.2
      have hlocCs := hloc.2
      clear hbase hloc
      revert hnt hpwBase hlocCs
      induction cs with
      | nil => intro _ _ _; exact List.Pairwise.nil
      | cons a tl ih =>
        intro hnt hpwBase hlocCs
        refine List.pairwise_cons.mpr ⟨fun b hb z ⟨hza, hzb⟩ => ?_,
          ih (fun c hc => hnt c (List.mem_cons_of_mem _ hc))
             (List.pairwise_cons.mp hpwBase).2 (fun c hc => hlocCs c (List.mem_cons_of_mem _ hc))⟩
        cases z with
        | inl x =>
          exact (List.pairwise_cons.mp hpwBase).1 b hb x
            ⟨(disjointUnion_classHolds_inl base m hne fs a (hnt a (List.mem_cons_self ..)) x).mp hza,
             (disjointUnion_classHolds_inl base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) x).mp hzb⟩
        | inr y =>
          exact (isZeroTopOnRight_sound base m hne fs a (hnt a (List.mem_cons_self ..))).1 y
            (hlocCs a (List.mem_cons_self ..)) hza
  | subObjectProperty r s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_obj_inl base m hne fs hnt.2 x (Sum.inl y)).mpr ⟨y, rfl, hbase x y hxy⟩
    | inr x => exact absurd hr (disjointUnion_botObj_inr base m hne fs hloc x z2)
  | subObjectPropertyChain rs s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.and_eq_true] at hloc
    intro z1 z2 hpath
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_rolePath_inl base m hne fs rs hnt.1 x z2).mp hpath
      exact (disjointUnion_obj_inl base m hne fs hnt.2 x (Sum.inl y)).mpr ⟨y, rfl, hbase x y hxy⟩
    | inr x => exact absurd hpath (disjointUnion_rolePath_bot_inr base m hne fs rs hnt.1 hloc.2 x z2)
  | equivalentObjectProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    simp only [isRightLocalAxiomFast, List.all_eq_true] at hloc
    intro r hr s hs z1 z2
    cases z1 with
    | inl x =>
      rw [disjointUnion_obj_inl base m hne fs (hnt r hr) x z2,
          disjointUnion_obj_inl base m hne fs (hnt s hs) x z2]
      exact exists_congr fun y => and_congr_right fun _ => hbase r hr s hs x y
    | inr x =>
      exact ⟨fun h => absurd h (disjointUnion_botObj_inr base m hne fs (hloc r hr) x z2),
             fun h => absurd h (disjointUnion_botObj_inr base m hne fs (hloc s hs) x z2)⟩
  | disjointObjectProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    have hpwR : ∀ (x : Fin m.numNodes) (z : Sum base.Object (Fin m.numNodes)),
        rs.Pairwise (fun r s => ¬ (objectHolds U r (Sum.inr x) z ∧ objectHolds U s (Sum.inr x) z)) :=
      fun x z => disjointUnion_pairwise_atMostOne
        (fun r hrb => disjointUnion_botObj_inr base m hne fs hrb x z) hloc
    clear hloc
    revert hbase hnt hpwR
    induction rs with
    | nil => intro _ _ _; exact List.Pairwise.nil
    | cons r tl ih =>
      intro hbase hnt hpwR
      refine List.pairwise_cons.mpr ⟨fun s hs z1 z2 ⟨hr, hs'⟩ => ?_,
        ih (List.pairwise_cons.mp hbase).2 (fun q hq => hnt q (List.mem_cons_of_mem _ hq))
           (fun x z => (List.pairwise_cons.mp (hpwR x z)).2)⟩
      cases z1 with
      | inl x =>
        obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs (hnt r (List.mem_cons_self ..)) x z2).mp hr
        obtain ⟨y2, heq, hxy2⟩ := (disjointUnion_obj_inl base m hne fs (hnt s (List.mem_cons_of_mem _ hs)) x (Sum.inl y)).mp hs'
        cases Sum.inl.inj heq
        exact (List.pairwise_cons.mp hbase).1 s hs x y ⟨hxy, hxy2⟩
      | inr x =>
        exact (List.pairwise_cons.mp (hpwR x z2)).1 s hs ⟨hr, hs'⟩
  | inverseObjectProperties r s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.and_eq_true] at hloc
    intro z1 z2
    cases z1 with
    | inl x =>
      cases z2 with
      | inl y =>
        rw [disjointUnion_obj_inl base m hne fs hnt.1 x (Sum.inl y),
            disjointUnion_obj_inl base m hne fs hnt.2 y (Sum.inl x)]
        simp only [Sum.inl.injEq, exists_eq_left']
        exact hbase x y
      | inr y =>
        exact ⟨fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x (Sum.inr y)).mp h; cases heq),
               fun h => absurd h (disjointUnion_botObj_inr base m hne fs hloc.2 y (Sum.inl x))⟩
    | inr x =>
      cases z2 with
      | inl y =>
        exact ⟨fun h => absurd h (disjointUnion_botObj_inr base m hne fs hloc.1 x (Sum.inl y)),
               fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inl base m hne fs hnt.2 y (Sum.inr x)).mp h; cases heq)⟩
      | inr y =>
        exact ⟨fun h => absurd h (disjointUnion_botObj_inr base m hne fs hloc.1 x (Sum.inr y)),
               fun h => absurd h (disjointUnion_botObj_inr base m hne fs hloc.2 y (Sum.inr x))⟩
  | objectPropertyDomain r c =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.or_eq_true] at hloc
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inl base m hne fs c hnt.2 x).mpr (hbase x y hxy)
    | inr x =>
      rcases hloc with hrb | hct
      · exact absurd hr (disjointUnion_botObj_inr base m hne fs hrb x z2)
      · exact (isZeroTopOnRight_sound base m hne fs c hnt.2).2 x hct
  | objectPropertyRange r c =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    simp only [isRightLocalAxiomFast, Bool.or_eq_true] at hloc
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inl base m hne fs c hnt.2 y).mpr (hbase x y hxy)
    | inr x =>
      rcases hloc with hrb | hct
      · exact absurd hr (disjointUnion_botObj_inr base m hne fs hrb x z2)
      · obtain ⟨y, rfl, _⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x z2).mp hr
        exact (isZeroTopOnRight_sound base m hne fs c hnt.2).2 y hct
  | functionalObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 z3 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y2, rfl, hxy2⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨y3, rfl, hxy3⟩ := (disjointUnion_obj_inl base m hne fs hnt x z3).mp h2
      exact congrArg Sum.inl (hbase x y2 y3 hxy2 hxy3)
    | inr x => exact absurd h1 (disjointUnion_botObj_inr base m hne fs hloc x z2)
  | inverseFunctionalObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 z3 h1 h2
    cases z2 with
    | inl x2 =>
      obtain ⟨y1, rfl, h1'⟩ := (disjointUnion_obj_inl base m hne fs hnt x2 z1).mp h1
      cases z3 with
      | inl x3 =>
        obtain ⟨y1', heq, h2'⟩ := (disjointUnion_obj_inl base m hne fs hnt x3 (Sum.inl y1)).mp h2
        cases Sum.inl.inj heq
        exact congrArg Sum.inl (hbase y1 x2 x3 h1' h2')
      | inr x3 => exact absurd h2 (disjointUnion_botObj_inr base m hne fs hloc x3 (Sum.inl y1))
    | inr x2 => exact absurd h1 (disjointUnion_botObj_inr base m hne fs hloc x2 z1)
  | reflexiveObjectProperty _ => cases hloc
  | irreflexiveObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z hz
    cases z with
    | inl x =>
      obtain ⟨y, heq, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x (Sum.inl x)).mp hz
      cases Sum.inl.inj heq
      exact hbase x hxy
    | inr x => exact disjointUnion_botObj_inr base m hne fs hloc x (Sum.inr x) hz
  | symmetricObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 hz
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp hz
      exact (disjointUnion_obj_inl base m hne fs hnt y (Sum.inl x)).mpr ⟨x, rfl, hbase x y hxy⟩
    | inr x => exact absurd hz (disjointUnion_botObj_inr base m hne fs hloc x z2)
  | asymmetricObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨x', heq, hyx⟩ := (disjointUnion_obj_inl base m hne fs hnt y (Sum.inl x)).mp h2
      cases Sum.inl.inj heq
      exact hbase x y hxy hyx
    | inr x => exact disjointUnion_botObj_inr base m hne fs hloc x z2 h1
  | transitiveObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    simp only [isRightLocalAxiomFast] at hloc
    intro z1 z2 z3 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨w, rfl, hyw⟩ := (disjointUnion_obj_inl base m hne fs hnt y z3).mp h2
      exact (disjointUnion_obj_inl base m hne fs hnt x (Sum.inl w)).mpr ⟨w, rfl, hbase x y w hxy hyw⟩
    | inr x => exact absurd h1 (disjointUnion_botObj_inr base m hne fs hloc x z2)
  | subDataProperty r s =>
    simp only [axiomNoTopProp, Bool.and_eq_true, bne_iff_ne] at hnt
    intro z d hd
    cases z with
    | inl x => exact hbase x d hd
    | inr _ => exact absurd hd hnt.1
  | equivalentDataProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true, bne_iff_ne] at hnt
    intro r hr s hs z d
    cases z with
    | inl x => exact hbase r hr s hs x d
    | inr _ => exact ⟨fun h => absurd h (hnt r hr), fun h => absurd h (hnt s hs)⟩
  | disjointDataProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true, bne_iff_ne] at hnt
    clear hloc
    revert hbase hnt
    induction rs with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons p tl ih =>
      intro hbase hnt
      refine List.pairwise_cons.mpr ⟨fun q hq z d ⟨hp, hq'⟩ => ?_,
        ih (List.pairwise_cons.mp hbase).2 (fun r hr => hnt r (List.mem_cons_of_mem _ hr))⟩
      cases z with
      | inl x => exact (List.pairwise_cons.mp hbase).1 q hq x d ⟨hp, hq'⟩
      | inr _ => exact hnt p (List.mem_cons_self ..) hp
  | dataPropertyDomain p c =>
    simp only [axiomNoTopProp, Bool.and_eq_true, bne_iff_ne] at hnt
    intro z d hd
    cases z with
    | inl x => exact (disjointUnion_classHolds_inl base m hne fs c hnt.2 x).mpr (hbase x d hd)
    | inr _ => exact absurd hd hnt.1
  | dataPropertyRange p dr =>
    simp only [axiomNoTopProp, bne_iff_ne] at hnt
    intro z d hd
    cases z with
    | inl x => exact (disjointUnion_dataHolds base m hne fs d dr).mpr (hbase x d hd)
    | inr _ => exact absurd hd hnt
  | functionalDataProperty p =>
    simp only [axiomNoTopProp, bne_iff_ne] at hnt
    intro z d1 d2 h1 h2
    cases z with
    | inl x => exact hbase x d1 d2 h1 h2
    | inr _ => exact absurd h1 hnt
  | datatypeDefinition d dr =>
    intro v
    exact (hbase v).trans (disjointUnion_dataHolds base m hne fs v dr).symm
  | hasKey c rs ds =>
    simp only [axiomNoTopProp, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hnt
    intro z1 z2 hc1 hc2 hn1 hn2 hrs hds
    cases z1 with
    | inr _ => exact hn1.elim
    | inl x1 =>
      cases z2 with
      | inr _ => exact hn2.elim
      | inl x2 =>
        apply congrArg Sum.inl
        refine hbase x1 x2
          ((disjointUnion_classHolds_inl base m hne fs c hnt.1.1 x1).mp hc1)
          ((disjointUnion_classHolds_inl base m hne fs c hnt.1.1 x2).mp hc2)
          hn1 hn2 (fun r hr => ?_) (fun p hp => hds p hp)
        obtain ⟨z, hnz, hz1, hz2⟩ := hrs r hr
        obtain ⟨w, rfl, h1'⟩ := (disjointUnion_obj_inl base m hne fs (hnt.1.2 r hr) x1 z).mp hz1
        obtain ⟨w2, heq, h2'⟩ := (disjointUnion_obj_inl base m hne fs (hnt.1.2 r hr) x2 (Sum.inl w)).mp hz2
        cases Sum.inl.inj heq
        exact ⟨w, hnz, h1', h2'⟩
  | sameIndividuals inds =>
    intro a ha b hb
    exact congrArg Sum.inl (hbase a ha b hb)
  | differentIndividuals inds =>
    clear hloc hnt
    revert hbase
    induction inds with
    | nil => intro _; exact List.Pairwise.nil
    | cons a tl ih =>
      intro hbase
      refine List.pairwise_cons.mpr ⟨fun b hb heq => (List.pairwise_cons.mp hbase).1 b hb (Sum.inl.inj heq),
        ih (List.pairwise_cons.mp hbase).2⟩
  | classAssertion c a =>
    exact (disjointUnion_classHolds_inl base m hne fs c hnt (base.individuals a)).mpr hbase
  | objectAssertion r a b =>
    exact (disjointUnion_obj_inl base m hne fs hnt (base.individuals a) (Sum.inl (base.individuals b))).mpr
      ⟨base.individuals b, rfl, hbase⟩
  | negativeObjectAssertion r a b =>
    intro hr
    obtain ⟨y, heq, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt (base.individuals a) (Sum.inl (base.individuals b))).mp hr
    exact hbase (Sum.inl.inj heq ▸ hxy)
  | dataAssertion p a l => exact hbase
  | negativeDataAssertion p a l => exact hbase

private theorem disjointUnion_axiom_checked {dm : DatatypeMap} (base : Interpretation dm)
    (m : CBCanonicalModel) (hne : 0 < m.numNodes) (fs : FastLocality.FastSig)
    {ax : Axiom} (hnt : axiomNoTopProp ax = true) (hi : axiomNoIndivData ax = true)
    (hbase : axiomHolds base ax)
    (hright : axiomHolds (Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig) ax) :
    axiomHolds (disjointUnionInterp base m hne fs) ax := by
  let U := disjointUnionInterp base m hne fs
  let R := Profile.restrictToSig (m.toInterpretation dm hne) fs.toSig
  cases ax with
  | subClassOf a b =>
    simp only [axiomNoTopProp, axiomNoIndivData, Bool.and_eq_true] at hnt hi
    intro z hz
    cases z with
    | inl x =>
      exact (disjointUnion_classHolds_inl base m hne fs b hnt.2 x).mpr
        (hbase x ((disjointUnion_classHolds_inl base m hne fs a hnt.1 x).mp hz))
    | inr y =>
      exact (disjointUnion_classHolds_inr base m hne fs b hnt.2 hi.2 y).mpr
        (hright y ((disjointUnion_classHolds_inr base m hne fs a hnt.1 hi.1 y).mp hz))
  | equivalentClasses cs =>
    simp only [axiomNoTopProp, axiomNoIndivData, List.all_eq_true] at hnt hi
    intro a ha b hb z
    cases z with
    | inl x =>
      exact (disjointUnion_classHolds_inl base m hne fs a (hnt a ha) x).trans
        ((hbase a ha b hb x).trans (disjointUnion_classHolds_inl base m hne fs b (hnt b hb) x).symm)
    | inr y =>
      exact (disjointUnion_classHolds_inr base m hne fs a (hnt a ha) (hi a ha) y).trans
        ((hright a ha b hb y).trans (disjointUnion_classHolds_inr base m hne fs b (hnt b hb) (hi b hb) y).symm)
  | disjointClasses cs =>
    simp only [axiomNoTopProp, axiomNoIndivData, List.all_eq_true] at hnt hi
    revert hbase hright hnt hi
    induction cs with
    | nil => intro _ _ _ _; exact List.Pairwise.nil
    | cons a tl ih =>
      intro hbase hright hnt hi
      refine List.pairwise_cons.mpr ⟨fun b hb z ⟨hza, hzb⟩ => ?_,
        ih (List.pairwise_cons.mp hbase).2 (List.pairwise_cons.mp hright).2
           (fun c hc => hnt c (List.mem_cons_of_mem _ hc)) (fun c hc => hi c (List.mem_cons_of_mem _ hc))⟩
      cases z with
      | inl x =>
        exact (List.pairwise_cons.mp hbase).1 b hb x
          ⟨(disjointUnion_classHolds_inl base m hne fs a (hnt a (List.mem_cons_self ..)) x).mp hza,
           (disjointUnion_classHolds_inl base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) x).mp hzb⟩
      | inr y =>
        exact (List.pairwise_cons.mp hright).1 b hb y
          ⟨(disjointUnion_classHolds_inr base m hne fs a (hnt a (List.mem_cons_self ..)) (hi a (List.mem_cons_self ..)) y).mp hza,
           (disjointUnion_classHolds_inr base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) (hi b (List.mem_cons_of_mem _ hb)) y).mp hzb⟩
  | disjointUnion h cs =>
    simp only [axiomNoTopProp, axiomNoIndivData, List.all_eq_true] at hnt hi
    refine ⟨fun z => ?_, ?_⟩
    · cases z with
      | inl x =>
        exact (hbase.1 x).trans (exists_congr fun c => and_congr_right fun hc =>
          (disjointUnion_classHolds_inl base m hne fs c (hnt c hc) x).symm)
      | inr y =>
        exact (hright.1 y).trans (exists_congr fun c => and_congr_right fun hc =>
          (disjointUnion_classHolds_inr base m hne fs c (hnt c hc) (hi c hc) y).symm)
    · have hpwB := hbase.2; have hpwR := hright.2
      clear hbase hright
      revert hnt hi hpwB hpwR
      induction cs with
      | nil => intro _ _ _ _; exact List.Pairwise.nil
      | cons a tl ih =>
        intro hnt hi hpwB hpwR
        refine List.pairwise_cons.mpr ⟨fun b hb z ⟨hza, hzb⟩ => ?_,
          ih (fun c hc => hnt c (List.mem_cons_of_mem _ hc)) (fun c hc => hi c (List.mem_cons_of_mem _ hc))
             (List.pairwise_cons.mp hpwB).2 (List.pairwise_cons.mp hpwR).2⟩
        cases z with
        | inl x =>
          exact (List.pairwise_cons.mp hpwB).1 b hb x
            ⟨(disjointUnion_classHolds_inl base m hne fs a (hnt a (List.mem_cons_self ..)) x).mp hza,
             (disjointUnion_classHolds_inl base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) x).mp hzb⟩
        | inr y =>
          exact (List.pairwise_cons.mp hpwR).1 b hb y
            ⟨(disjointUnion_classHolds_inr base m hne fs a (hnt a (List.mem_cons_self ..)) (hi a (List.mem_cons_self ..)) y).mp hza,
             (disjointUnion_classHolds_inr base m hne fs b (hnt b (List.mem_cons_of_mem _ hb)) (hi b (List.mem_cons_of_mem _ hb)) y).mp hzb⟩
  | subObjectProperty r s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_obj_inl base m hne fs hnt.2 x (Sum.inl y)).mpr ⟨y, rfl, hbase x y hxy⟩
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_obj_inr base m hne fs hnt.2 x (Sum.inr y)).mpr ⟨y, rfl, hright x y hxy⟩
  | subObjectPropertyChain rs s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    intro z1 z2 hpath
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_rolePath_inl base m hne fs rs hnt.1 x z2).mp hpath
      exact (disjointUnion_obj_inl base m hne fs hnt.2 x (Sum.inl y)).mpr ⟨y, rfl, hbase x y hxy⟩
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_rolePath_inr base m hne fs rs hnt.1 x z2).mp hpath
      exact (disjointUnion_obj_inr base m hne fs hnt.2 x (Sum.inr y)).mpr ⟨y, rfl, hright x y hxy⟩
  | equivalentObjectProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    intro r hr s hs z1 z2
    cases z1 with
    | inl x =>
      rw [disjointUnion_obj_inl base m hne fs (hnt r hr) x z2,
          disjointUnion_obj_inl base m hne fs (hnt s hs) x z2]
      exact exists_congr fun y => and_congr_right fun _ => hbase r hr s hs x y
    | inr x =>
      rw [disjointUnion_obj_inr base m hne fs (hnt r hr) x z2,
          disjointUnion_obj_inr base m hne fs (hnt s hs) x z2]
      exact exists_congr fun y => and_congr_right fun _ => hright r hr s hs x y
  | disjointObjectProperties rs =>
    simp only [axiomNoTopProp, List.all_eq_true] at hnt
    clear hi
    revert hbase hright hnt
    induction rs with
    | nil => intro _ _ _; exact List.Pairwise.nil
    | cons r tl ih =>
      intro hbase hright hnt
      refine List.pairwise_cons.mpr ⟨fun s hs z1 z2 ⟨hr, hs'⟩ => ?_,
        ih (List.pairwise_cons.mp hbase).2 (List.pairwise_cons.mp hright).2
           (fun q hq => hnt q (List.mem_cons_of_mem _ hq))⟩
      cases z1 with
      | inl x =>
        obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs (hnt r (List.mem_cons_self ..)) x z2).mp hr
        obtain ⟨y2, heq, hxy2⟩ := (disjointUnion_obj_inl base m hne fs (hnt s (List.mem_cons_of_mem _ hs)) x (Sum.inl y)).mp hs'
        cases Sum.inl.inj heq
        exact (List.pairwise_cons.mp hbase).1 s hs x y ⟨hxy, hxy2⟩
      | inr x =>
        obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs (hnt r (List.mem_cons_self ..)) x z2).mp hr
        obtain ⟨y2, heq, hxy2⟩ := (disjointUnion_obj_inr base m hne fs (hnt s (List.mem_cons_of_mem _ hs)) x (Sum.inr y)).mp hs'
        cases Sum.inr.inj heq
        exact (List.pairwise_cons.mp hright).1 s hs x y ⟨hxy, hxy2⟩
  | inverseObjectProperties r s =>
    simp only [axiomNoTopProp, Bool.and_eq_true] at hnt
    intro z1 z2
    cases z1 with
    | inl x =>
      cases z2 with
      | inl y =>
        rw [disjointUnion_obj_inl base m hne fs hnt.1 x (Sum.inl y),
            disjointUnion_obj_inl base m hne fs hnt.2 y (Sum.inl x)]
        simp only [Sum.inl.injEq, exists_eq_left']
        exact hbase x y
      | inr y =>
        exact ⟨fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x (Sum.inr y)).mp h; cases heq),
               fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inr base m hne fs hnt.2 y (Sum.inl x)).mp h; cases heq)⟩
    | inr x =>
      cases z2 with
      | inl y =>
        exact ⟨fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x (Sum.inl y)).mp h; cases heq),
               fun h => (by obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inl base m hne fs hnt.2 y (Sum.inr x)).mp h; cases heq)⟩
      | inr y =>
        rw [disjointUnion_obj_inr base m hne fs hnt.1 x (Sum.inr y),
            disjointUnion_obj_inr base m hne fs hnt.2 y (Sum.inr x)]
        exact ⟨fun ⟨_, he, h⟩ => ⟨x, rfl, (hright x y).mp (Sum.inr.inj he ▸ h)⟩,
               fun ⟨_, he, h⟩ => ⟨y, rfl, (hright x y).mpr (Sum.inr.inj he ▸ h)⟩⟩
  | objectPropertyDomain r c =>
    simp only [axiomNoTopProp, axiomNoIndivData, Bool.and_eq_true] at hnt hi
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inl base m hne fs c hnt.2 x).mpr (hbase x y hxy)
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inr base m hne fs c hnt.2 hi x).mpr (hright x y hxy)
  | objectPropertyRange r c =>
    simp only [axiomNoTopProp, axiomNoIndivData, Bool.and_eq_true] at hnt hi
    intro z1 z2 hr
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inl base m hne fs c hnt.2 y).mpr (hbase x y hxy)
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt.1 x z2).mp hr
      exact (disjointUnion_classHolds_inr base m hne fs c hnt.2 hi y).mpr (hright x y hxy)
  | functionalObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z1 z2 z3 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y2, rfl, hxy2⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨y3, rfl, hxy3⟩ := (disjointUnion_obj_inl base m hne fs hnt x z3).mp h2
      exact congrArg Sum.inl (hbase x y2 y3 hxy2 hxy3)
    | inr x =>
      obtain ⟨y2, rfl, hxy2⟩ := (disjointUnion_obj_inr base m hne fs hnt x z2).mp h1
      obtain ⟨y3, rfl, hxy3⟩ := (disjointUnion_obj_inr base m hne fs hnt x z3).mp h2
      exact congrArg Sum.inr (hright x y2 y3 hxy2 hxy3)
  | inverseFunctionalObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z1 z2 z3 h1 h2
    cases z2 with
    | inl x2 =>
      obtain ⟨y1, rfl, h1'⟩ := (disjointUnion_obj_inl base m hne fs hnt x2 z1).mp h1
      cases z3 with
      | inl x3 =>
        obtain ⟨y1', heq, h2'⟩ := (disjointUnion_obj_inl base m hne fs hnt x3 (Sum.inl y1)).mp h2
        cases Sum.inl.inj heq
        exact congrArg Sum.inl (hbase y1 x2 x3 h1' h2')
      | inr x3 =>
        obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inr base m hne fs hnt x3 (Sum.inl y1)).mp h2
        cases heq
    | inr x2 =>
      obtain ⟨y1, rfl, h1'⟩ := (disjointUnion_obj_inr base m hne fs hnt x2 z1).mp h1
      cases z3 with
      | inl x3 =>
        obtain ⟨_, heq, _⟩ := (disjointUnion_obj_inl base m hne fs hnt x3 (Sum.inr y1)).mp h2
        cases heq
      | inr x3 =>
        obtain ⟨y1', heq, h2'⟩ := (disjointUnion_obj_inr base m hne fs hnt x3 (Sum.inr y1)).mp h2
        cases Sum.inr.inj heq
        exact congrArg Sum.inr (hright y1 x2 x3 h1' h2')
  | reflexiveObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z
    cases z with
    | inl x => exact (disjointUnion_obj_inl base m hne fs hnt x (Sum.inl x)).mpr ⟨x, rfl, hbase x⟩
    | inr x => exact (disjointUnion_obj_inr base m hne fs hnt x (Sum.inr x)).mpr ⟨x, rfl, hright x⟩
  | irreflexiveObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z hz
    cases z with
    | inl x =>
      obtain ⟨y, heq, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x (Sum.inl x)).mp hz
      cases Sum.inl.inj heq; exact hbase x hxy
    | inr x =>
      obtain ⟨y, heq, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt x (Sum.inr x)).mp hz
      cases Sum.inr.inj heq; exact hright x hxy
  | symmetricObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z1 z2 hz
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp hz
      exact (disjointUnion_obj_inl base m hne fs hnt y (Sum.inl x)).mpr ⟨x, rfl, hbase x y hxy⟩
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt x z2).mp hz
      exact (disjointUnion_obj_inr base m hne fs hnt y (Sum.inr x)).mpr ⟨x, rfl, hright x y hxy⟩
  | asymmetricObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z1 z2 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨x', heq, hyx⟩ := (disjointUnion_obj_inl base m hne fs hnt y (Sum.inl x)).mp h2
      cases Sum.inl.inj heq; exact hbase x y hxy hyx
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt x z2).mp h1
      obtain ⟨x', heq, hyx⟩ := (disjointUnion_obj_inr base m hne fs hnt y (Sum.inr x)).mp h2
      cases Sum.inr.inj heq; exact hright x y hxy hyx
  | transitiveObjectProperty r =>
    simp only [axiomNoTopProp] at hnt
    intro z1 z2 z3 h1 h2
    cases z1 with
    | inl x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inl base m hne fs hnt x z2).mp h1
      obtain ⟨w, rfl, hyw⟩ := (disjointUnion_obj_inl base m hne fs hnt y z3).mp h2
      exact (disjointUnion_obj_inl base m hne fs hnt x (Sum.inl w)).mpr ⟨w, rfl, hbase x y w hxy hyw⟩
    | inr x =>
      obtain ⟨y, rfl, hxy⟩ := (disjointUnion_obj_inr base m hne fs hnt x z2).mp h1
      obtain ⟨w, rfl, hyw⟩ := (disjointUnion_obj_inr base m hne fs hnt y z3).mp h2
      exact (disjointUnion_obj_inr base m hne fs hnt x (Sum.inr w)).mpr ⟨w, rfl, hright x y w hxy hyw⟩
  | _ => cases hi

/-- Headline soundness theorem for `checkCBDisjointPartialModel`:
    given ANY base model `base ⊨ o` (certified by consistency `Satisfiable dm o`),
    the disjoint union `base ⊕ restrictToSig(m, fs)` satisfies EVERY axiom of `o`
    (including ABox assertions, nominals, `HasKey`, and datatype axioms). -/
theorem checkCBDisjointPartialModel_sound {dm : DatatypeMap} {o : Ontology}
    {m : CBCanonicalModel} {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBDisjointPartialModel o m fs numWorkers = true)
    (base : Interpretation dm) (hbase : satisfies base o) :
    ∃ hne : 0 < m.numNodes, satisfies (disjointUnionInterp base m hne fs) o := by
  unfold checkCBDisjointPartialModel at hcheck
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
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hchk
  obtain ⟨hnt, hrest⟩ := hchk
  rcases hrest with hloc | ⟨⟨hi, hcov⟩, haxm⟩
  · exact disjointUnion_axiom_rightLocal base m hne fs hnt hloc (hbase o[idx] hax)
  · have hsub := (FastLocality.FastSig.coversSig_iff fs (Profile.axiomSig o[idx])).mp hcov
    have hr := (Profile.restrictToSig_axiomHolds (m.toInterpretation dm hne) hsub).mpr
      (checkCBAxiom_sound hadj hne haxm)
    exact disjointUnion_axiom_checked base m hne fs hnt hi (hbase o[idx] hax) hr

/-- Counterexample refutation theorem for disjoint-union TBox+ABox CB partial models:
    for any consistent ontology `o` passing `checkCBDisjointPartialModel o m fs w`,
    a witness node `x < m.numNodes` separating `a` (in `fs`) from `b` soundly refutes
    `o ⊨ a ⊑ b`. -/
theorem checkCBDisjointPartialModel_counter_sub {dm : DatatypeMap} {o : Ontology}
    {m : CBCanonicalModel} {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBDisjointPartialModel o m fs numWorkers = true)
    (hsat : Satisfiable dm o)
    {a b : IRI} {x : Nat} (hx : x < m.numNodes)
    (haSig : a = thing ∨ (a ≠ nothing ∧ fs.hasCls a = true))
    (ha : m.hasCls a x = true)
    (hb : b ≠ thing ∧ (b = nothing ∨ fs.hasCls b = false ∨ m.hasCls b x = false)) :
    ¬ Entails dm o [.subClassOf (.named a) (.named b)] := by
  obtain ⟨i0, assign0, hsat0⟩ := hsat
  obtain ⟨hne, hsatU⟩ := checkCBDisjointPartialModel_sound hcheck (i0.withAnonymous assign0) hsat0
  intro hent
  obtain ⟨assign, hq⟩ := hent (disjointUnionInterp (i0.withAnonymous assign0) m hne fs)
    (satisfies_models hsatU)
  have haHolds : classHolds ((disjointUnionInterp (i0.withAnonymous assign0) m hne fs).withAnonymous assign)
      (Sum.inr ⟨x, hx⟩) (.named a) := by
    simp only [classHolds, Interpretation.withAnonymous, disjointUnionInterp, Profile.restrictToSig]
    rcases haSig with rfl | ⟨han, has⟩
    · simp
    · by_cases hat : a = thing
      · simp [hat]
      · rw [FastLocality.FastSig.hasCls_eq] at has
        simp [hat, han, has]
        exact ha
  have hbHolds := hq _ (List.mem_singleton.mpr rfl) (Sum.inr ⟨x, hx⟩) haHolds
  simp only [classHolds, Interpretation.withAnonymous, disjointUnionInterp, Profile.restrictToSig] at hbHolds
  obtain ⟨hbt, hbRest⟩ := hb
  simp only [hbt, ↓reduceIte] at hbRest hbHolds
  rcases hbRest with rfl | hbf | hbm
  · simp at hbHolds
  · rw [FastLocality.FastSig.hasCls_eq] at hbf
    by_cases hbn : b = nothing
    · simp [hbn] at hbHolds
    · simp [hbn, hbf] at hbHolds
  · by_cases hbn : b = nothing
    · simp [hbn] at hbHolds
    · simp only [hbn, ↓reduceIte] at hbHolds
      split at hbHolds
      · change m.hasCls b x = true at hbHolds
        rw [hbm] at hbHolds
        cases hbHolds
      · exact hbHolds

/-- Satisfiability witness theorem for disjoint-union TBox+ABox CB partial models. -/
theorem checkCBDisjointPartialModel_witness_sat {dm : DatatypeMap} {o : Ontology}
    {m : CBCanonicalModel} {fs : FastLocality.FastSig} {numWorkers : Nat}
    (hcheck : checkCBDisjointPartialModel o m fs numWorkers = true)
    (hsat : Satisfiable dm o)
    {a : IRI} {x : Nat} (hx : x < m.numNodes)
    (haSig : a = thing ∨ (a ≠ nothing ∧ fs.hasCls a = true))
    (ha : m.hasCls a x = true) :
    ¬ Entails dm o [.subClassOf (.named a) (.named nothing)] :=
  checkCBDisjointPartialModel_counter_sub hcheck hsat hx haSig ha ⟨by simp [thing, nothing], Or.inl rfl⟩

theorem checkCBDisjointPartialModel_workers_eq (o : Ontology) (m : CBCanonicalModel)
    (fs : FastLocality.FastSig) (w : Nat) :
    checkCBDisjointPartialModel o m fs w = checkCBDisjointPartialModel o m fs 1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkCBDisjointPartialModel, Bool.and_eq_true, checkAdjConsistent_workers_eq, allRangePar_iff]

mutual
  private def planRightZeroExpr (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
      ClassExpr → Option (Nat × List SigSym)
    | .named c =>
      if c == nothing then some (0, [])
      else if c == thing then none
      else if !fs.hasCls c then some (0, [])
      else some (symDeg idx (.cls c) + 1, [.cls c])
    | .complement c => planRightTopExpr idx fs c
    | .intersection a b => pickCheaper (planRightZeroExpr idx fs a) (planRightZeroExpr idx fs b)
    | .union a b => combinePlans (planRightZeroExpr idx fs a) (planRightZeroExpr idx fs b)
    | .oneOf _ => some (0, [])
    | .objectSome r c => pickCheaper (planBotObj idx fs r) (planRightZeroExpr idx fs c)
    | .objectAll _ _ => none
    | .objectValue r _ => if objPropNotTop r then some (0, []) else none
    | .objectSelf r => planBotObj idx fs r
    | .objectMin n r c =>
      if n > 0 then pickCheaper (planBotObj idx fs r) (planRightZeroExpr idx fs c) else none
    | .objectMax _ _ _ => none
    | .objectExact n r c =>
      if n > 0 then pickCheaper (planBotObj idx fs r) (planRightZeroExpr idx fs c) else none
    | .dataSome p _ | .dataValue p _ => if p != topDataProperty then some (0, []) else none
    | .dataAll _ _ => none
    | .dataMin n p _ | .dataExact n p _ =>
      if n > 0 && p != topDataProperty then some (0, []) else none
    | .dataMax _ _ _ => none

  private def planRightTopExpr (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
      ClassExpr → Option (Nat × List SigSym)
    | .named c => if c == thing then some (0, []) else none
    | .complement c => planRightZeroExpr idx fs c
    | .intersection a b => combinePlans (planRightTopExpr idx fs a) (planRightTopExpr idx fs b)
    | .union a b => pickCheaper (planRightTopExpr idx fs a) (planRightTopExpr idx fs b)
    | .oneOf _ | .objectSome _ _ | .objectValue _ _ | .objectSelf _ | .objectExact _ _ _
    | .dataSome _ _ | .dataValue _ _ | .dataExact _ _ _ => none
    | .objectAll r c => pickCheaper (planBotObj idx fs r) (planRightTopExpr idx fs c)
    | .objectMin n _ _ => if n == 0 then some (0, []) else none
    | .objectMax _ r c => pickCheaper (planBotObj idx fs r) (planRightZeroExpr idx fs c)
    | .dataAll p _ | .dataMax _ p _ => if p != topDataProperty then some (0, []) else none
    | .dataMin n _ _ => if n == 0 then some (0, []) else none
end

private def planRightLocalAxiom (idx : FastLocality.LocalityIndex) (fs : FastLocality.FastSig) :
    Axiom → Option (Nat × List SigSym)
  | .subClassOf a b => pickCheaper (planRightZeroExpr idx fs a) (planRightTopExpr idx fs b)
  | .equivalentClasses cs =>
    let allZero := cs.foldl (fun acc c => combinePlans acc (planRightZeroExpr idx fs c)) (some (0, []))
    let allTop := cs.foldl (fun acc c => combinePlans acc (planRightTopExpr idx fs c)) (some (0, []))
    pickCheaper allZero allTop
  | .disjointClasses cs => planAtMostOne (cs.map (planRightZeroExpr idx fs))
  | .disjointUnion h cs =>
    cs.foldl (fun acc c => combinePlans acc (planRightZeroExpr idx fs c)) (planRightZeroExpr idx fs (.named h))
  | .subObjectProperty r _ => planBotObj idx fs r
  | .subObjectPropertyChain rs _ => rs.foldl (fun acc r => pickCheaper acc (planBotObj idx fs r)) none
  | .equivalentObjectProperties rs =>
    rs.foldl (fun acc r => combinePlans acc (planBotObj idx fs r)) (some (0, []))
  | .disjointObjectProperties rs => planAtMostOne (rs.map (planBotObj idx fs))
  | .inverseObjectProperties r s => combinePlans (planBotObj idx fs r) (planBotObj idx fs s)
  | .objectPropertyDomain r c | .objectPropertyRange r c =>
    pickCheaper (planBotObj idx fs r) (planRightTopExpr idx fs c)
  | .functionalObjectProperty r | .inverseFunctionalObjectProperty r
  | .irreflexiveObjectProperty r | .symmetricObjectProperty r
  | .asymmetricObjectProperty r | .transitiveObjectProperty r => planBotObj idx fs r
  | .reflexiveObjectProperty _ => none
  | .subDataProperty _ _ | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataPropertyDomain _ _ | .dataPropertyRange _ _ | .functionalDataProperty _
  | .datatypeDefinition _ _ | .hasKey _ _ _ | .sameIndividuals _ | .differentIndividuals _
  | .classAssertion _ _ | .objectAssertion _ _ _ | .negativeObjectAssertion _ _ _
  | .dataAssertion _ _ _ | .negativeDataAssertion _ _ _ => some (0, [])

/-- Compute a maximal clean sub-signature `fs` for `checkCBDisjointPartialModel` in $O(|O|)$ time:
    ABox assertions, `HasKey`, datatype axioms, and `ObjectOneOf`/`ObjectHasValue` on the right
    component incur zero symbol drops! Independently verified by `checkCBDisjointPartialModel`. -/
def buildCBDisjointPartialSig (idx : FastLocality.LocalityIndex) (axOk : Array Bool) :
    Option FastLocality.FastSig := Id.run do
  let n := idx.axioms.size
  if axOk.size != n then return none
  let mut clsSet : Std.HashSet IRI := {}
  for (c, _) in idx.clsIdx do
    clsSet := clsSet.insert c
  let mut objSet : Std.HashSet IRI := {}
  for (r, _) in idx.objIdx do
    objSet := objSet.insert r
  let mut dataSet : Std.HashSet IRI := {}
  for (p, _) in idx.dataIdx do
    dataSet := dataSet.insert p
  let mut fs : FastLocality.FastSig := ⟨clsSet, objSet, dataSet⟩
  let mut dropped : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for i in [0:n] do
    if !axOk[i]! then
      dropped := dropped.set! i true
      if let some ax := idx.axioms[i]? then
        if !isRightLocalAxiomFast fs ax then
          queue := queue.push i
  let mut head : Nat := 0
  while head < queue.size do
    let i := queue[head]!
    head := head + 1
    let some ax := idx.axioms[i]? | continue
    if isRightLocalAxiomFast fs ax then continue
    match planRightLocalAxiom idx fs ax with
    | none => return none
    | some (_, syms) =>
      for sym in syms do
        let mut hits : Array Nat := #[]
        match sym with
        | .cls c =>
          if fs.hasCls c then
            fs := { fs with cls := fs.cls.erase c }
            hits := idx.clsIdx.getD c #[]
        | .obj r =>
          if fs.hasObj r then
            fs := { fs with obj := fs.obj.erase r }
            hits := idx.objIdx.getD r #[]
        | .data p =>
          if fs.hasData p then
            fs := { fs with data := fs.data.erase p }
            hits := idx.dataIdx.getD p #[]
        for j in hits do
          if j < n && !dropped[j]! then
            dropped := dropped.set! j true
            if let some axj := idx.axioms[j]? then
              if !isRightLocalAxiomFast fs axj then
                queue := queue.push j
      if !isRightLocalAxiomFast fs ax then
        return none
  if fs.cls.isEmpty then return none
  return some fs

private def runPar2 {α β : Type} (workers : Nat) (f : Unit → α) (g : Unit → β) : α × β :=
  if workers ≤ 1 then (f (), g ())
  else
    let t := Task.spawn g
    let a := f ()
    (a, t.get)

private theorem runPar2_eq {α β : Type} (workers : Nat) (f : Unit → α) (g : Unit → β) :
    runPar2 workers f g = (f (), g ()) := by
  unfold runPar2
  split <;> rfl

private def exprHasPosUnion : ClassExpr → Bool
  | .union a b => a != .named nothing && b != .named nothing
  | .intersection a b => exprHasPosUnion a || exprHasPosUnion b
  | .objectSome _ c | .objectAll _ c | .objectMin _ _ c => exprHasPosUnion c
  | _ => false

private def axiomHasPosUnion : Axiom → Bool
  | .subClassOf _ b => exprHasPosUnion b
  | .equivalentClasses cs => cs.any exprHasPosUnion
  | _ => false

private def strengthenPos (pickFirst : Bool) : ClassExpr → ClassExpr
  | .intersection a b => .intersection (strengthenPos pickFirst a) (strengthenPos pickFirst b)
  | .union a b =>
    if a == .named nothing then strengthenPos pickFirst b
    else if b == .named nothing then strengthenPos pickFirst a
    else if pickFirst then strengthenPos pickFirst a else strengthenPos pickFirst b
  | .objectSome r c => .objectSome r (strengthenPos pickFirst c)
  | .objectAll r c => .objectAll r (strengthenPos pickFirst c)
  | .objectMin n r c => .objectMin n r (strengthenPos pickFirst c)
  | c => c

private def strengthenOnt (pickFirst : Bool) (o : Ontology) : Ontology :=
  o.flatMap fun
    | .subClassOf a b => [.subClassOf a (strengthenPos pickFirst b)]
    | .equivalentClasses [c0, c1] =>
      [.subClassOf c0 (strengthenPos pickFirst c1), .subClassOf c1 (strengthenPos pickFirst c0)]
    | ax => [ax]

private def flattenUnionExpr : ClassExpr → List ClassExpr
  | .union a b => flattenUnionExpr a ++ flattenUnionExpr b
  | .named c => if c == nothing then [] else [.named c]
  | e => [e]

private def flattenConjExpr : ClassExpr → List ClassExpr
  | .intersection a b => flattenConjExpr a ++ flattenConjExpr b
  | .named c => if c == thing then [] else [.named c]
  | e => [e]

/-- Untrusted post-pass repair on a `CBCanonicalModel` for nearly-Horn ontologies with
    multi-way positive unions (`owl:unionOf`), qualified cardinality restrictions
    (`ObjectMinCardinality n` / `ObjectExactCardinality n`), and complex `EquivalentClasses`
    definitions. All resulting models are independently kernel-verified by `checkCBCanonicalModel`,
    `checkCBDisjointPartialModel`, or `checkCBPartialModel`. -/
private def repairCBCanonicalModel (o : Ontology)
    (subs : List (IRI × IRI)) (m0 : CBCanonicalModel) (wmap : Std.HashMap IRI Nat)
    (preferAlt : Bool := false) : CBCanonicalModel × Std.HashMap IRI Nat := Id.run do
  if m0.numNodes == 0 then return (m0, wmap)
  let mut supMap : Std.HashMap IRI (Array IRI) := {}
  for (a, b) in subs do
    supMap := supMap.insert a ((supMap.getD a #[]).push b)

  let mut disjMap : Std.HashMap IRI (Std.HashSet IRI) := {}
  for ax in o do
    match ax with
    | .disjointClasses cs =>
      let names := cs.filterMap fun | .named c => some c | _ => none
      for a in names do
        for b in names do
          if a != b then
            disjMap := disjMap.insert a ((disjMap.getD a {}).insert b)
    | .subClassOf (.intersection (.named a) (.named b)) (.named c) =>
      if c == nothing then
        disjMap := disjMap.insert a ((disjMap.getD a {}).insert b)
        disjMap := disjMap.insert b ((disjMap.getD b {}).insert a)
    | _ => pure ()

  let mut disjObls : Array (IRI × List IRI) := #[]
  let mut cardObls : Array (IRI × Nat × ObjectProperty × IRI × Bool) := #[]
  let mut eqDefs : Array (IRI × ClassExpr) := #[]
  let mut selfPairs : Array (IRI × IRI) := #[]
  let mut rSub : List (ObjectProperty × ObjectProperty) := []
  let mut rChains : List (List ObjectProperty × ObjectProperty) := []

  for ax in o do
    match ax with
    | .subClassOf (.named a) (.objectSelf r) =>
      selfPairs := selfPairs.push (a, Profile.objPropIRI r)
    | .subClassOf (.named a) rhs =>
      let ds := flattenUnionExpr rhs
      if ds.length ≥ 2 then
        let names := ds.filterMap fun | .named d => some d | _ => none
        if !names.isEmpty then disjObls := disjObls.push (a, names)
      for part in flattenConjExpr rhs do
        match part with
        | .objectMin n r (.named c) => if n ≥ 2 then cardObls := cardObls.push (a, n, r, c, false)
        | .objectExact n r (.named c) => if n ≥ 1 then cardObls := cardObls.push (a, n, r, c, true)
        | _ => pure ()
    | .equivalentClasses [.named a, .objectSelf r] | .equivalentClasses [.objectSelf r, .named a] =>
      selfPairs := selfPairs.push (a, Profile.objPropIRI r)
    | .equivalentClasses [.named a, rhs] | .equivalentClasses [rhs, .named a] =>
      eqDefs := eqDefs.push (a, rhs)
      let ds := flattenUnionExpr rhs
      if ds.length ≥ 2 then
        let names := ds.filterMap fun | .named d => some d | _ => none
        if !names.isEmpty then disjObls := disjObls.push (a, names)
      for part in flattenConjExpr rhs do
        match part with
        | .objectMin n r (.named c) => if n ≥ 2 then cardObls := cardObls.push (a, n, r, c, false)
        | .objectExact n r (.named c) => if n ≥ 1 then cardObls := cardObls.push (a, n, r, c, true)
        | _ => pure ()
    | .subObjectProperty r s => rSub := (r, s) :: rSub
    | .equivalentObjectProperties rs =>
      match rs with
      | [] | [_] => pure ()
      | r0 :: rest => for r in rest do rSub := (r0, r) :: (r, r0) :: rSub
    | .inverseObjectProperties r s => rSub := (r, s.converse) :: (s, r.converse) :: rSub
    | .symmetricObjectProperty r => rSub := (r, r.converse) :: rSub
    | .transitiveObjectProperty r => rChains := ([r, r], r) :: rChains
    | .subObjectPropertyChain rs s =>
      match rs with
      | [] => pure ()
      | [r] => rSub := (r, s) :: rSub
      | _ => rChains := (rs, s) :: rChains
    | _ => pure ()

  if disjObls.isEmpty && cardObls.isEmpty && eqDefs.isEmpty then return (m0, wmap)

  -- Specific fillers first so subclass `exact n` obligations populate before superclass `exact n`
  cardObls := cardObls.qsort fun a b =>
    (supMap.getD a.2.2.2.1 #[]).size > (supMap.getD b.2.2.2.1 #[]).size

  let mut nodeClasses := m0.nodeClasses
  let mut outAdj := m0.outAdj
  let mut inAdj := m0.inAdj
  let mut edgeSet : Std.HashSet (IRI × Nat × Nat) := {}
  let mut roleEdgeCnt : Std.HashMap IRI Nat := {}
  let mut cappedRoles : Std.HashSet IRI := {}
  let mut activeOut : Std.HashMap IRI (Array Nat) := {}
  let mut activeIn : Std.HashMap IRI (Array Nat) := {}
  for u in [0:m0.numNodes] do
    for (p, ys) in (outAdj[u]!).toList do
      if !ys.isEmpty then activeOut := activeOut.insert p ((activeOut.getD p #[]).push u)
      for v in ys do
        edgeSet := edgeSet.insert (p, u, v)
        roleEdgeCnt := roleEdgeCnt.insert p (roleEdgeCnt.getD p 0 + 1)
    for (p, xs) in (inAdj[u]!).toList do
      if !xs.isEmpty then activeIn := activeIn.insert p ((activeIn.getD p #[]).push u)

  let maxEdgesPerRole : Nat := 250000
  let maxTotalEdges : Nat := 1500000
  let addEdge := fun (p : IRI) (u v : Nat)
      (edgeSet : Std.HashSet (IRI × Nat × Nat))
      (roleEdgeCnt : Std.HashMap IRI Nat) (cappedRoles : Std.HashSet IRI)
      (outAdj inAdj : Array (Std.HashMap IRI (Array Nat)))
      (activeOut activeIn : Std.HashMap IRI (Array Nat)) =>
    if edgeSet.size >= maxTotalEdges || cappedRoles.contains p ||
        p == topObjectProperty || p == bottomObjectProperty || edgeSet.contains (p, u, v) then
      (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn)
    else
      let cnt := roleEdgeCnt.getD p 0 + 1
      if cnt > maxEdgesPerRole then
        (edgeSet, roleEdgeCnt, cappedRoles.insert p, outAdj, inAdj, activeOut, activeIn)
      else
        let es1 := edgeSet.insert (p, u, v)
        let hadOut := (outAdj[u]!).contains p
        let hadIn := (inAdj[v]!).contains p
        let oa1 := outAdj.modify u fun m => m.insert p ((m.getD p #[]).push v)
        let ia1 := inAdj.modify v fun m => m.insert p ((m.getD p #[]).push u)
        let ao1 := if hadOut then activeOut else activeOut.insert p ((activeOut.getD p #[]).push u)
        let ai1 := if hadIn then activeIn else activeIn.insert p ((activeIn.getD p #[]).push v)
        (es1, roleEdgeCnt.insert p cnt, cappedRoles, oa1, ia1, ao1, ai1)

  let removeEdge := fun (p : IRI) (u v : Nat)
      (edgeSet : Std.HashSet (IRI × Nat × Nat))
      (outAdj inAdj : Array (Std.HashMap IRI (Array Nat))) =>
    if !edgeSet.contains (p, u, v) then (edgeSet, outAdj, inAdj)
    else
      let es1 := edgeSet.erase (p, u, v)
      let oa1 := outAdj.modify u fun m => m.insert p ((m.getD p #[]).filter (· != v))
      let ia1 := inAdj.modify v fun m => m.insert p ((m.getD p #[]).filter (· != u))
      (es1, oa1, ia1)

  let mut subRolesOf : Std.HashMap IRI (Std.HashSet IRI) := {}
  for (r, s) in rSub do
    let pr := Profile.objPropIRI r; let ps := Profile.objPropIRI s
    subRolesOf := subRolesOf.insert ps ((subRolesOf.getD ps {}).insert pr)

  let closeRBox := fun
      (edgeSet : Std.HashSet (IRI × Nat × Nat))
      (roleEdgeCnt : Std.HashMap IRI Nat) (cappedRoles : Std.HashSet IRI)
      (outAdj inAdj : Array (Std.HashMap IRI (Array Nat)))
      (activeOut activeIn : Std.HashMap IRI (Array Nat)) => Id.run do
    let mut edgeSet := edgeSet; let mut roleEdgeCnt := roleEdgeCnt; let mut cappedRoles := cappedRoles
    let mut outAdj := outAdj; let mut inAdj := inAdj
    let mut activeOut := activeOut; let mut activeIn := activeIn
    for _round in [0:6] do
      if edgeSet.size >= maxTotalEdges then break
      let beforeSz := edgeSet.size
      for (r, s) in rSub do
        let sp := Profile.objPropIRI s
        if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then continue
        match r with
        | .named pr =>
          for u in activeOut.getD pr #[] do
            if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
            for v in (outAdj[u]!).getD pr #[] do
              match s with
              | .named ps =>
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
              | .inverse ps =>
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
        | .inverse pr =>
          for u in activeIn.getD pr #[] do
            if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
            for v in (inAdj[u]!).getD pr #[] do
              match s with
              | .named ps =>
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
              | .inverse ps =>
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
      for (rs, s) in rChains do
        let sp := Profile.objPropIRI s
        if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then continue
        match rs with
        | [] => pure ()
        | r0 :: _ =>
          let startNodes : Array Nat := match r0 with
            | .named p0 => activeOut.getD p0 #[]
            | .inverse p0 => activeIn.getD p0 #[]
          for u in startNodes do
            if cappedRoles.contains sp || edgeSet.size >= maxTotalEdges then break
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
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps u v edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
              | .inverse ps =>
                (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                  addEdge ps v u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
      if edgeSet.size == beforeSz then break
    return (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn)

  let buildSortedModel (nc : Array (Std.HashSet IRI))
      (oa ia : Array (Std.HashMap IRI (Array Nat))) : CBCanonicalModel := Id.run do
    let numNodes := nc.size
    let mut clsNodes : Std.HashMap IRI (Array Nat) := {}
    let mut roleOutNodes : Std.HashMap IRI (Array Nat) := {}
    let mut roleInNodes : Std.HashMap IRI (Array Nat) := {}
    let mut oaS := oa
    let mut iaS := ia
    for u in [0:numNodes] do
      for c in nc[u]! do
        clsNodes := clsNodes.insert c ((clsNodes.getD c #[]).push u)
      let mut om : Std.HashMap IRI (Array Nat) := {}
      for (r, ys) in (oaS[u]!).toList do
        let ds := dedupSortNat ys
        if !ds.isEmpty then
          om := om.insert r ds
          roleOutNodes := roleOutNodes.insert r ((roleOutNodes.getD r #[]).push u)
      oaS := oaS.set! u om
      let mut im : Std.HashMap IRI (Array Nat) := {}
      for (r, ys) in (iaS[u]!).toList do
        let ds := dedupSortNat ys
        if !ds.isEmpty then
          im := im.insert r ds
          roleInNodes := roleInNodes.insert r ((roleInNodes.getD r #[]).push u)
      iaS := iaS.set! u im
    return { numNodes := numNodes, nodeClasses := nc, outAdj := oaS, inAdj := iaS,
             clsNodes := clsNodes, roleOutNodes := roleOutNodes, roleInNodes := roleInNodes }

  let setsCompat (s1 s2 : Std.HashSet IRI) : Bool :=
    s1.all fun c => !(disjMap.getD c {}).any fun d => s2.contains d

  let maxNodes := m0.numNodes + 8000
  let mut m := m0
  let mut edgesDirty := false
  for outer in [0:12] do
    let mut anyChanged := false
    let beforeEdgeSz := edgeSet.size
    -- (A) Qualified cardinality witness cloning (< n) & load-balanced compatible merging (exact > n)
    for (a, n, r, c, isExact) in cardObls do
      if let some wC := wmap[c]? then
        let curNum := nodeClasses.size
        for u in [0:curNum] do
          if (nodeClasses[u]!).contains a then
            let nbrs : Array Nat := match r with
              | .named p => dedupSortNat ((outAdj[u]!).getD p #[])
              | .inverse p => dedupSortNat ((inAdj[u]!).getD p #[])
            let hits := nbrs.filter fun y => (nodeClasses[y]!).contains c
            let mut cnt := hits.size
            if cnt < n then
              while cnt < n && nodeClasses.size < maxNodes do
                let fresh := nodeClasses.size
                nodeClasses := nodeClasses.push nodeClasses[wC]!
                outAdj := outAdj.push {}
                inAdj := inAdj.push {}
                for (p, ys) in (m0.outAdj[wC]!).toList do
                  for y in ys do
                    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                      addEdge p fresh y edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                match r with
                | .named p =>
                  (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                    addEdge p u fresh edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                | .inverse p =>
                  (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                    addEdge p fresh u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                cnt := cnt + 1
                anyChanged := true
            else if isExact && cnt > n && outer >= 1 && nodeClasses.size < maxNodes then
              let p := Profile.objPropIRI r
              let mut buckets : Array (Array Nat) := Array.replicate n #[]
              let mut bucketCls : Array (Std.HashSet IRI) := Array.replicate n {}
              let mut okMerge := true
              let hitsSorted := hits.qsort fun x y => (nodeClasses[x]!).size > (nodeClasses[y]!).size
              for y in hitsSorted do
                let yCls := nodeClasses[y]!
                let mut placed := false
                for bi in [0:n] do
                  if buckets[bi]!.isEmpty then
                    buckets := buckets.set! bi #[y]
                    bucketCls := bucketCls.set! bi yCls
                    placed := true
                    break
                if !placed then
                  let mut bestBi? : Option Nat := none
                  let mut bestScore : Nat := 9999999
                  for bi in [0:n] do
                    if setsCompat bucketCls[bi]! yCls then
                      let mut overlap := 0
                      for cc in yCls do
                        if (bucketCls[bi]!).contains cc then overlap := overlap + 1
                      let score := buckets[bi]!.size * 10000 + overlap
                      if score < bestScore then
                        bestScore := score
                        bestBi? := some bi
                  if let some bi := bestBi? then
                    buckets := buckets.modify bi (·.push y)
                    let mut merged := bucketCls[bi]!
                    for cc in yCls do merged := merged.insert cc
                    bucketCls := bucketCls.set! bi merged
                    placed := true
                if !placed then okMerge := false
              if okMerge then
                let mut relRoles : Array IRI := #[p]
                for sr in subRolesOf.getD p {} do relRoles := relRoles.push sr
                for bi in [0:n] do
                  let fresh := nodeClasses.size
                  nodeClasses := nodeClasses.push bucketCls[bi]!
                  outAdj := outAdj.push {}
                  inAdj := inAdj.push {}
                  for y in buckets[bi]! do
                    for (qp, qys) in (outAdj[y]!).toList do
                      for qy in qys do
                        if !(qy == u && relRoles.contains qp) then
                          (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                            addEdge qp fresh qy edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                    for sr in subRolesOf.getD p {} do
                      if edgeSet.contains (sr, y, u) then
                        (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                          addEdge sr fresh u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                      if edgeSet.contains (sr, u, y) then
                        (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                          addEdge sr u fresh edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                  match r with
                  | .named rp =>
                    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                      addEdge rp u fresh edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                  | .inverse rp =>
                    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                      addEdge rp fresh u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
                for y in hits do
                  for rp in relRoles do
                    (edgeSet, outAdj, inAdj) := removeEdge rp u y edgeSet outAdj inAdj
                    (edgeSet, outAdj, inAdj) := removeEdge rp y u edgeSet outAdj inAdj
                anyChanged := true
                edgesDirty := true

    -- (B) Self-loops + RBox closure (only when edges changed)
    for (c, p) in selfPairs do
      for u in [0:nodeClasses.size] do
        if (nodeClasses[u]!).contains c then
          (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
            addEdge p u u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
    if edgesDirty || edgeSet.size != beforeEdgeSz then
      (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
        closeRBox edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
      edgesDirty := false
    m := buildSortedModel nodeClasses outAdj inAdj

    -- (C) Forward EquivalentClasses closure (copying witness outgoing edges for newly inferred classes)
    let mut eqChanged := false
    for (a, rhs) in eqDefs do
      match candidateNodes? m rhs with
      | some cands =>
        for u in cands do
          if !(nodeClasses[u]!).contains a then
            if evalClassExpr m u rhs == some true then
              let mut nc1 := (nodeClasses[u]!).insert a
              for s in supMap.getD a #[] do
                if s != thing && s != nothing then nc1 := nc1.insert s
              nodeClasses := nodeClasses.set! u nc1
              if let some w := wmap[a]? then
                for (p, ys) in (m0.outAdj[w]!).toList do
                  for y in ys do
                    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                      addEdge p u y edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
              eqChanged := true
              anyChanged := true
              edgesDirty := true
      | none => pure ()

    -- (D) Compatible-disjunct repair (preferring minimum out-degree compatible disjunct)
    if !eqChanged then
      for (a, names) in disjObls do
        for u in [0:nodeClasses.size] do
          let nc := nodeClasses[u]!
          if nc.contains a && !(names.any fun d => nc.contains d) then
            let isCompat (d : IRI) : Bool :=
              let sups := (supMap.getD d #[]).push d
              sups.all fun s =>
                let ds := disjMap.getD s {}
                !(ds.any fun x => nc.contains x)
            let outDegOf (d : IRI) : Nat :=
              match wmap[d]? with
              | some w => (m0.outAdj[w]!).size
              | none => 999999
            let mut compatCands : Array (Nat × IRI) := #[]
            for d in names do
              if isCompat d then
                compatCands := compatCands.push (outDegOf d, d)
            let sortedCands := compatCands.qsort fun a b => a.1 < b.1
            let bestD? : Option IRI :=
              if preferAlt && sortedCands.size ≥ 2 then some sortedCands[1]!.2
              else sortedCands[0]?.map Prod.snd
            if let some d := bestD? then
              let mut nc1 := nc.insert d
              for s in supMap.getD d #[] do
                if s != thing && s != nothing then nc1 := nc1.insert s
              nodeClasses := nodeClasses.set! u nc1
              if let some w := wmap[d]? then
                for (p, ys) in (m0.outAdj[w]!).toList do
                  for y in ys do
                    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
                      addEdge p u y edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
              anyChanged := true
              edgesDirty := true

    if !anyChanged && outer > 0 then break

  let beforeFinalSelf := edgeSet.size
  for (c, p) in selfPairs do
    for u in [0:nodeClasses.size] do
      if (nodeClasses[u]!).contains c then
        (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
          addEdge p u u edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
  if edgesDirty || edgeSet.size != beforeFinalSelf then
    (edgeSet, roleEdgeCnt, cappedRoles, outAdj, inAdj, activeOut, activeIn) :=
      closeRBox edgeSet roleEdgeCnt cappedRoles outAdj inAdj activeOut activeIn
  return (buildSortedModel nodeClasses outAdj inAdj, wmap)

/-- Extract a kernel-verified countermodel summary from `m` against the ORIGINAL ontology `o`:
    1. When every axiom holds on `m`, verifies the full model via `checkCBCanonicalModel`.
    2. Otherwise, when `o` avoids `owl:topObjectProperty`/`owl:topDataProperty`, shrinks to the
       maximal clean sub-signature `fs` for the disjoint union `I_base ⊕ restrictToSig(m, fs)`
       (verified by `checkCBDisjointPartialModel`, keeping ABox assertions, `ObjectOneOf`,
       `ObjectHasValue`, `HasKey`, and datatype axioms intact at zero cost!).
    3. Otherwise, falls back to standalone ⊥-locality `checkCBPartialModel`. -/
private def harvestVerifiedCBModel (o : Ontology) (idx : FastLocality.LocalityIndex)
    (namedClasses : List IRI) (namedClassSet : Std.HashSet IRI)
    (m : CBCanonicalModel) (witnessNode : Std.HashMap IRI Nat) (numWorkers : Nat) :
    List (IRI × List IRI) :=
  if m.numNodes == 0 || !checkAdjConsistent m numWorkers then []
  else
    let axOk := (mapListPar numWorkers (checkCBAxiom m) o).toArray
    if axOk.all id then
      -- Every axiom of `o` holds on `m`: verify full model via `checkCBCanonicalModel`
      if checkCBCanonicalModel o m numWorkers then
        Id.run do
          let mut out : Array (IRI × List IRI) := #[]
          for c in namedClasses do
            if c == thing then
              let cand := (m.nodeClasses.getD 0 {}).toList.filter fun b =>
                b != thing && b != nothing && namedClassSet.contains b
              out := out.push (thing, cand)
            else if c != nothing then
              let x? := match witnessNode[c]? with
                | some x => some x
                | none => (m.clsNodes.getD c #[])[0]?
              if let some x := x? then
                if x < m.numNodes && m.hasCls c x then
                  let witnesses := m.clsNodes.getD c #[]
                  let cand := (m.nodeClasses.getD x {}).toList.filter fun b =>
                    b != c && b != thing && b != nothing && namedClassSet.contains b &&
                      witnesses.all (m.hasCls b)
                  out := out.push (c, cand)
          return out.toList
      else []
    else
      let extractForSig (fs : FastLocality.FastSig) : List (IRI × List IRI) := Id.run do
        let mut out : Array (IRI × List IRI) := #[]
        for c in namedClasses do
          if c == thing then
            let cand := (m.nodeClasses.getD 0 {}).toList.filter fun b =>
              b != thing && b != nothing && namedClassSet.contains b && fs.hasCls b
            out := out.push (thing, cand)
          else if c != nothing && fs.hasCls c then
            let x? := match witnessNode[c]? with
              | some x => some x
              | none => (m.clsNodes.getD c #[])[0]?
            if let some x := x? then
              if x < m.numNodes && m.hasCls c x then
                let cand := (m.nodeClasses.getD x {}).toList.filter fun b =>
                  b != thing && b != nothing && namedClassSet.contains b && fs.hasCls b
                out := out.push (c, cand)
        return out.toList
      if o.all axiomNoTopProp then
        match buildCBDisjointPartialSig idx axOk with
        | some fs =>
          if checkCBDisjointPartialModel o m fs numWorkers then extractForSig fs else []
        | none => []
      else
        match buildCBPartialSig idx axOk with
        | some fs =>
          if checkCBPartialModel o m fs numWorkers then extractForSig fs else []
        | none => []

private theorem harvestVerifiedCBModel_workers_eq (o : Ontology) (idx : FastLocality.LocalityIndex)
    (namedClasses : List IRI) (namedClassSet : Std.HashSet IRI)
    (m : CBCanonicalModel) (witnessNode : Std.HashMap IRI Nat) (w : Nat) :
    harvestVerifiedCBModel o idx namedClasses namedClassSet m witnessNode w =
      harvestVerifiedCBModel o idx namedClasses namedClassSet m witnessNode 1 := by
  simp only [harvestVerifiedCBModel, checkAdjConsistent_workers_eq, mapListPar_eq,
    checkCBCanonicalModel_workers_eq, checkCBDisjointPartialModel_workers_eq,
    checkCBPartialModel_workers_eq]

/-- Run Horn-$\mathcal{SHIQ}$ saturation, returning both:
    1. the kernel-verified positive subsumptions & unsatisfiable classes (`FastCBResult`), and
    2. kernel-verified countermodel summaries `List (IRI × List IRI)` verified against the
       ORIGINAL ontology `o` via `checkCBCanonicalModel` / `checkCBDisjointPartialModel` /
       `checkCBPartialModel`.
    On nearly-Horn ontologies with positive disjunctions (`owl:unionOf`), also builds two
    Horn-strengthened countermodels (picking left vs. right disjuncts) in parallel and
    verifies them directly against the original unmodified ontology `o`. -/
def runFastCBWithPartialModel (o : Ontology) (idx : FastLocality.LocalityIndex)
    (namedClasses : List IRI) (namedClassSet : Std.HashSet IRI) (numWorkers : Nat := 8)
    (maxContexts : Nat := 4096) (maxCtxSize : Nat := 10) (maxLinks : Nat := 32768) :
    FastCBResult × List (IRI × List IRI) :=
  let norm := extractHornSHIQ o
  let canPartial := o.all axiomNoTopProp || !hasUnsupportedAlwaysNonLocal idx
  let effMaxContexts := max maxContexts (norm.table.classes.size * 2)
  let effMaxLinks := max maxLinks (norm.table.classes.size * 16)
  let cert := saturateHornSHI norm effMaxContexts maxCtxSize effMaxLinks
  if checkCBSound norm cert numWorkers then
    let res : FastCBResult := {
      subs := extractNamedSubs norm cert
      unsats := extractNamedUnsats norm cert
      isPureHornSHIQ := norm.isPureHornSHIQ
      verified := true
    }
    if res.unsats.contains thing || !canPartial then
      (res, [])
    else
      let (mBase, wBase) := buildCBCanonicalModel o norm cert
      let sBase := harvestVerifiedCBModel o idx namedClasses namedClassSet mBase wBase numWorkers
      let hasPosUnion := !norm.isPureHornSHIQ && o.any axiomHasPosUnion
      let baseCov := (sBase.foldl (fun s (c, _) => s.insert c) ({} : Std.HashSet IRI)).size
      if baseCov * 2 ≥ namedClasses.length then
        if !hasPosUnion then
          (res, sBase)
        else
          -- Raw model already covers most classes: use fast dual Horn-strengthening for unions
          let runStr := fun (pickFirst : Bool) () =>
            let normS := extractHornSHIQ (strengthenOnt pickFirst o)
            let effC := max maxContexts (normS.table.classes.size * 2)
            let effL := max maxLinks (normS.table.classes.size * 16)
            let certS := saturateHornSHI normS effC maxCtxSize effL
            let (mS, wS) := buildCBCanonicalModel o normS certS
            harvestVerifiedCBModel o idx namedClasses namedClassSet mS wS (max 1 (numWorkers / 2))
          let (s1, s2) := runPar2 numWorkers (runStr true) (runStr false)
          (res, sBase ++ s1 ++ s2)
      else
        -- Raw model had low coverage (e.g. multi-way unions or qualified `min`/`exact` ≥ 2):
        -- run dual parallel post-pass repair.
        let (sRep1, sRep2) :=
          if o.length ≤ 80000 then
            runPar2 numWorkers
              (fun () =>
                let (m1, w1) := repairCBCanonicalModel o res.subs mBase wBase false
                harvestVerifiedCBModel o idx namedClasses namedClassSet m1 w1 (max 1 (numWorkers / 2)))
              (fun () =>
                let (m2, w2) := repairCBCanonicalModel o res.subs mBase wBase true
                harvestVerifiedCBModel o idx namedClasses namedClassSet m2 w2 (max 1 (numWorkers / 2)))
          else ([], [])
        let combined := sBase ++ sRep1 ++ sRep2
        let repCov := (combined.foldl (fun s (c, _) => s.insert c) ({} : Std.HashSet IRI)).size
        if repCov * 2 ≥ namedClasses.length || !hasPosUnion then
          (res, combined)
        else
          let runStr := fun (pickFirst : Bool) () =>
            let normS := extractHornSHIQ (strengthenOnt pickFirst o)
            let effC := max maxContexts (normS.table.classes.size * 2)
            let effL := max maxLinks (normS.table.classes.size * 16)
            let certS := saturateHornSHI normS effC maxCtxSize effL
            let (mS, wS) := buildCBCanonicalModel o normS certS
            harvestVerifiedCBModel o idx namedClasses namedClassSet mS wS (max 1 (numWorkers / 2))
          let (s1, s2) := runPar2 numWorkers (runStr true) (runStr false)
          (res, combined ++ s1 ++ s2)
  else
    ({ subs := [], unsats := [], isPureHornSHIQ := false, verified := false }, [])

theorem runFastCBWithPartialModel_workers_eq (o : Ontology) (idx : FastLocality.LocalityIndex)
    (namedClasses : List IRI) (namedClassSet : Std.HashSet IRI)
    (w maxContexts maxCtxSize maxLinks : Nat) :
    runFastCBWithPartialModel o idx namedClasses namedClassSet w maxContexts maxCtxSize maxLinks =
      runFastCBWithPartialModel o idx namedClasses namedClassSet 1 maxContexts maxCtxSize maxLinks := by
  simp only [runFastCBWithPartialModel, runPar2_eq, checkCBSound_workers_eq,
    harvestVerifiedCBModel_workers_eq]

end Sabrina.OWL2.FastCB
