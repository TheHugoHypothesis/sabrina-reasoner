import Sabrina.ALC.RoleTheory

namespace Sabrina.ALC

theorem localCheck_iff {cs : List Concept} {tbox : TBox} {row : Row} :
    localCheck cs tbox row = true ↔
      (∀ c ∈ cs, coherent row c = true) ∧
      (∀ ax ∈ tbox, ax.sub ∈ row → ax.sup ∈ row) := by
  simp only [localCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

def hasRoot (root : Concept) (pool : List Row) : Bool :=
  pool.any (fun row => decide (root ∈ row))

theorem hasRoot_iff {root : Concept} {pool : List Row} :
    hasRoot root pool = true ↔ ∃ row ∈ pool, root ∈ row := by
  simp [hasRoot, List.any_eq_true]

/-- A model certificate gives the rows of a finite domain. The role relations
are computed from the rows and checked closure rather than serialized as edges. -/
def checkModelUnder (rules : RoleTheory) (tbox : TBox) (root : Concept) (pool : List Row) : Bool :=
  let cs := closure tbox root
  pool.all (localCheck cs tbox) && pool.all (fun row => hasWitnesses cs pool row (admitsUnder cs rules)) && hasRoot root pool

private def rowModel (cs : List Concept) (pool : List Row) (rules : RoleTheory)
    (inhabited : Nonempty {row : Row // row ∈ pool}) : Interpretation where
  Domain := {row : Row // row ∈ pool}
  nonempty := inhabited
  atom name row := .atom name ∈ row.val
  role r src dst := admitsUnder cs rules r src.val dst.val = true

/-- The truth lemma for the finite model specified by a checked row pool. -/
private theorem row_truth {rules : RoleTheory} {tbox : TBox} {root : Concept} {pool : List Row}
    (inhabited : Nonempty {row : Row // row ∈ pool})
    (hlocal : ∀ row ∈ pool, localCheck (closure tbox root) tbox row = true)
    (hwitness : ∀ row ∈ pool, hasWitnesses (closure tbox root) pool row (admitsUnder (closure tbox root) rules) = true)
    (x : {row : Row // row ∈ pool}) {c : Concept} (hc : c ∈ closure tbox root) :
    holds (rowModel (closure tbox root) pool rules inhabited) x c ↔ c ∈ x.val := by
  induction c generalizing x with
  | top =>
    have h := (localCheck_iff.mp (hlocal x.val x.property)).1 _ hc
    exact ⟨fun _ => of_decide_eq_true h, fun _ => trivial⟩
  | atom name => rfl
  | neg c ih =>
    have h : (.neg c ∈ x.val) ↔ c ∉ x.val :=
      of_decide_eq_true ((localCheck_iff.mp (hlocal x.val x.property)).1 _ hc)
    simp only [holds, ih x (neg_mem_closure hc), h]
  | conj a b iha ihb =>
    obtain ⟨ha, hb⟩ := conj_mem_closure hc
    have h : (.conj a b ∈ x.val) ↔ a ∈ x.val ∧ b ∈ x.val :=
      of_decide_eq_true ((localCheck_iff.mp (hlocal x.val x.property)).1 _ hc)
    simp only [holds, iha x ha, ihb x hb, h]
  | some r c ih =>
    have hchild := some_mem_closure hc
    constructor
    · rintro ⟨y, he, hy⟩
      exact admitsEdge_iff.mp (allowsRole_admits he) c hc ((ih y hchild).mp hy)
    · intro hx
      obtain ⟨row, hm, hrow, he⟩ := hasWitnesses_iff.mp (hwitness x.val x.property) r c hc hx
      exact ⟨⟨row, hm⟩, he, (ih ⟨row, hm⟩ hchild).mpr hrow⟩

theorem checkModelUnder_finite_sound {rules : RoleTheory} {tbox : TBox} {root : Concept} {pool : List Row}
    (h : checkModelUnder rules tbox root pool = true) : FiniteConceptSatUnder rules tbox root := by
  simp only [checkModelUnder, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hlocal, hwitness⟩, hroot⟩ := h
  obtain ⟨row, hm, hr⟩ := hasRoot_iff.mp hroot
  let inhabited : Nonempty {row : Row // row ∈ pool} := ⟨⟨row, hm⟩⟩
  let i := rowModel (closure tbox root) pool rules inhabited
  refine ⟨i, ?_, ?_, ⟨pool.attach, List.mem_attach pool⟩, ⟨row, hm⟩, ?_⟩
  · intro r s hrs x y h
    have oriented (u : OrientedRole) (a b : i.Domain) :
        holdsRole i u a b ↔ allowsRole (closure tbox root) (roleClosure rules) u a.val b.val = true := by
      rcases u with ⟨u, _ | _⟩
      · rfl
      · change allowsRole _ _ (u,false) b.val a.val = true ↔
          allowsRole _ _ (converse (u,false)) a.val b.val = true
        rw [allowsRole_converse]
    exact (oriented s x y).mpr (allowsRole_step hrs ((oriented r x y).mp h))
  · intro ax hax x hsub
    obtain ⟨ha, hb⟩ := axiom_mem_closure root hax
    apply (row_truth inhabited hlocal hwitness x hb).mpr
    exact (localCheck_iff.mp (hlocal _ x.property)).2 ax hax
      ((row_truth inhabited hlocal hwitness x ha).mp hsub)
  · exact (row_truth inhabited hlocal hwitness ⟨row, hm⟩ (root_mem_closure tbox root)).mpr hr

theorem checkModelUnder_sound {rules : RoleTheory} {tbox : TBox} {root : Concept} {pool : List Row}
    (h : checkModelUnder rules tbox root pool = true) : ConceptSatUnder rules tbox root := by
  obtain ⟨i, hr, hi, _, hx⟩ := checkModelUnder_finite_sound h
  exact ⟨i, hr, hi, hx⟩

/-- The row realized by an element of an arbitrary model, including infinite models. -/
private noncomputable def realized (cs : List Concept) (i : Interpretation) (x : i.Domain) : Row := by
  classical
  exact cs.filter (fun c => decide (holds i x c))

private theorem mem_realized {cs : List Concept} {i : Interpretation} {x : i.Domain} {c : Concept} :
    c ∈ realized cs i x ↔ c ∈ cs ∧ holds i x c := by
  classical
  simp [realized, List.mem_filter]

private theorem realized_coherent {tbox : TBox} {root : Concept} (i : Interpretation)
    (x : i.Domain) {c : Concept} (hc : c ∈ closure tbox root) :
    coherent (realized (closure tbox root) i x) c = true := by
  cases c with
  | top => simp [coherent, mem_realized, hc, holds]
  | atom _ | some _ _ => rfl
  | neg c => simp [coherent, mem_realized, hc, neg_mem_closure hc, holds]
  | conj a b =>
    obtain ⟨ha, hb⟩ := conj_mem_closure hc
    simp [coherent, mem_realized, hc, ha, hb, holds]

private theorem realized_candidate {tbox : TBox} (root : Concept) (i : Interpretation)
    (hi : models i tbox) (x : i.Domain) :
    realized (closure tbox root) i x ∈ candidates tbox root := by
  classical
  apply List.mem_filter.mpr
  refine ⟨filter_mem_rows _ _, localCheck_iff.mpr ⟨?_, ?_⟩⟩
  · intro c hc
    exact realized_coherent i x hc
  · intro ax hax hs
    exact mem_realized.mpr ⟨(axiom_mem_closure root hax).2, hi ax hax x (mem_realized.mp hs).2⟩

private theorem realized_edge {tbox : TBox} {root : Concept} {i : Interpretation}
    {r : String} {x y : i.Domain} (he : i.role r x y) :
    admitsEdge (closure tbox root) r (realized (closure tbox root) i x)
        (realized (closure tbox root) i y) = true := by
  apply admitsEdge_iff.mpr
  intro c hc hcy
  exact mem_realized.mpr ⟨hc, y, he, (mem_realized.mp hcy).2⟩

def prune (cs : List Concept) (pool : List Row)
    (edge : String → Row → Row → Bool := admitsEdge cs) : List Row :=
  pool.filter (fun row => hasWitnesses cs pool row edge)

private theorem realized_survives {rules : RoleTheory} {tbox : TBox} {root : Concept} {i : Interpretation}
    {pool : List Row} (hm : modelsRoles i rules)
    (hpool : ∀ x : i.Domain, realized (closure tbox root) i x ∈ pool)
    (x : i.Domain) : realized (closure tbox root) i x ∈
      prune (closure tbox root) pool (admitsUnder (closure tbox root) rules) := by
  refine List.mem_filter.mpr ⟨hpool x, hasWitnesses_iff.mpr ?_⟩
  intro r c hc hx
  obtain ⟨y, he, hy⟩ := (mem_realized.mp hx).2
  exact ⟨_, hpool y, mem_realized.mpr ⟨some_mem_closure hc, hy⟩,
    allowsRole_of_model hm _ (fun _ _ _ => realized_edge) (r := (r,false)) he⟩

/-- Replay pruning for at most the given number of rounds. Stop early at a fixed point. -/
def pruneRoundsWith (cs : List Concept) (edge : String → Row → Row → Bool) : Nat → List Row → List Row
  | 0, pool => pool
  | n + 1, pool =>
    let next := prune cs pool edge
    if next = pool then pool else pruneRoundsWith cs edge n next

private theorem realized_survives_rounds {rules : RoleTheory} {tbox : TBox} {root : Concept} {i : Interpretation}
    (hm : modelsRoles i rules) (rounds : Nat) (pool : List Row)
    (hpool : ∀ x : i.Domain, realized (closure tbox root) i x ∈ pool) (x : i.Domain) :
    realized (closure tbox root) i x ∈ pruneRoundsWith (closure tbox root) (admitsUnder (closure tbox root) rules) rounds pool := by
  induction rounds generalizing pool with
  | zero => exact hpool x
  | succ n ih =>
    by_cases h : prune (closure tbox root) pool (admitsUnder (closure tbox root) rules) = pool
    · simpa only [pruneRoundsWith, h, ite_true] using hpool x
    · simpa only [pruneRoundsWith, h, ite_false] using ih _ (realized_survives hm hpool)

abbrev pruneRounds (cs : List Concept) : Nat → List Row → List Row :=
  pruneRoundsWith cs (admitsEdge cs)

/-- A refutation certificate is a bound on the number of rounds needed to
eliminate every row that contains the query. Checking it replays the elimination. -/
def checkRefutationUnder (rules : RoleTheory) (tbox : TBox) (root : Concept) (rounds : Nat) : Bool :=
  !hasRoot root (pruneRoundsWith (closure tbox root) (admitsUnder (closure tbox root) rules) rounds (candidates tbox root))

theorem checkRefutationUnder_sound {rules : RoleTheory} {tbox : TBox} {root : Concept} {rounds : Nat}
    (h : checkRefutationUnder rules tbox root rounds = true) : ¬ ConceptSatUnder rules tbox root := by
  rintro ⟨i, hm, hi, x, hx⟩
  have hs := realized_survives_rounds hm rounds (candidates tbox root) (realized_candidate root i hi) x
  have hp := hasRoot_iff.mpr ⟨_, hs, mem_realized.mpr ⟨root_mem_closure tbox root, hx⟩⟩
  simp [checkRefutationUnder, hp] at h

abbrev checkModel := checkModelUnder []
abbrev checkRefutation := checkRefutationUnder []

theorem checkModel_finite_sound {tbox : TBox} {root : Concept} {pool : List Row}
    (h : checkModel tbox root pool = true) : FiniteConceptSat tbox root := by
  obtain ⟨i, _, hi, hc, hx⟩ := checkModelUnder_finite_sound h
  exact ⟨i, hi, hc, hx⟩

theorem checkModel_sound {tbox : TBox} {root : Concept} {pool : List Row}
    (h : checkModel tbox root pool = true) : ConceptSat tbox root := by
  obtain ⟨i, _, hi, hx⟩ := checkModelUnder_sound h
  exact ⟨i, hi, hx⟩

theorem checkRefutation_sound {tbox : TBox} {root : Concept} {rounds : Nat}
    (h : checkRefutation tbox root rounds = true) : ¬ ConceptSat tbox root := by
  rintro ⟨i, hi, hx⟩
  exact checkRefutationUnder_sound h ⟨i, by simp [modelsRoles], hi, hx⟩

end Sabrina.ALC
