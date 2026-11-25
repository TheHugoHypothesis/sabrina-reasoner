import Sabrina.ALC.Certificates

namespace Sabrina.ALC

variable {edge : String → Row → Row → Bool}

private theorem prune_sublist (cs : List Concept) (pool : List Row) :
    (prune cs pool edge).Sublist pool := List.filter_sublist

private theorem pruneRounds_subset (cs : List Concept) (rounds : Nat) (pool : List Row) :
    pruneRoundsWith cs edge rounds pool ⊆ pool := by
  induction rounds generalizing pool with
  | zero => intro row h; exact h
  | succ n ih =>
    by_cases h : prune cs pool edge = pool
    · simp only [pruneRoundsWith, h, ite_true]
      exact fun _ hm => hm
    · simp only [pruneRoundsWith, h, ite_false]
      intro row hm
      exact (prune_sublist cs pool).subset (ih (prune cs pool edge) hm)

/-- Every nonstationary round strictly decreases the number of rows. -/
private theorem pruneRounds_fixed (cs : List Concept) (rounds : Nat) (pool : List Row)
    (hsize : pool.length ≤ rounds) :
    prune cs (pruneRoundsWith cs edge rounds pool) edge = pruneRoundsWith cs edge rounds pool := by
  induction rounds generalizing pool with
  | zero =>
    have hn : pool = [] := List.eq_nil_iff_length_eq_zero.mpr (Nat.eq_zero_of_le_zero hsize)
    simp [hn, pruneRoundsWith, prune]
  | succ n ih =>
    by_cases h : prune cs pool edge = pool
    · simp only [pruneRoundsWith, h, ite_true]
    · have sub := prune_sublist (edge := edge) cs pool
      have hne : (prune cs pool edge).length ≠ pool.length := fun he => h (sub.eq_of_length he)
      have hlt := Nat.lt_of_le_of_ne sub.length_le hne
      simpa only [pruneRoundsWith, h, ite_false] using ih (prune cs pool edge) (by omega)

private def survivors (rules : RoleTheory) (tbox : TBox) (root : Concept) : List Row :=
  let initial := candidates tbox root
  pruneRoundsWith (closure tbox root) (admitsUnder (closure tbox root) rules) initial.length initial

private theorem survivors_local (rules : RoleTheory) (tbox : TBox) (root : Concept) {row : Row}
    (hm : row ∈ survivors rules tbox root) : localCheck (closure tbox root) tbox row = true :=
  (List.mem_filter.mp (pruneRounds_subset _ _ _ hm)).2

private theorem survivors_witnesses (rules : RoleTheory) (tbox : TBox) (root : Concept) {row : Row}
    (hm : row ∈ survivors rules tbox root) : hasWitnesses (closure tbox root) (survivors rules tbox root) row (admitsUnder (closure tbox root) rules) = true := by
  have hfixed : prune (closure tbox root) (survivors rules tbox root) (admitsUnder (closure tbox root) rules) = survivors rules tbox root :=
    pruneRounds_fixed _ _ _ (Nat.le_refl _)
  rw [← hfixed] at hm
  exact (List.mem_filter.mp hm).2

inductive Certificate where
  | model (pool : List Row)
  | refutation (rounds : Nat)
  deriving Repr

def checkCertificateUnder (rules : RoleTheory) (tbox : TBox) (root : Concept) : Certificate → Bool
  | .model pool => checkModelUnder rules tbox root pool
  | .refutation rounds => checkRefutationUnder rules tbox root rounds

abbrev checkCertificate := checkCertificateUnder []

def certificateClaimUnder (rules : RoleTheory) (tbox : TBox) (root : Concept) : Certificate → Prop
  | .model _ => ConceptSatUnder rules tbox root
  | .refutation _ => ¬ ConceptSatUnder rules tbox root

theorem checkCertificateUnder_sound {rules : RoleTheory} {tbox : TBox} {root : Concept}
    {certificate : Certificate} (h : checkCertificateUnder rules tbox root certificate = true) :
    certificateClaimUnder rules tbox root certificate := by
  cases certificate with
  | model _ => exact checkModelUnder_sound h
  | refutation _ => exact checkRefutationUnder_sound h

def certificateClaim (tbox : TBox) (root : Concept) : Certificate → Prop
  | .model _ => ConceptSat tbox root
  | .refutation _ => ¬ ConceptSat tbox root

theorem checkCertificate_sound {tbox : TBox} {root : Concept} {certificate : Certificate}
    (h : checkCertificate tbox root certificate = true) : certificateClaim tbox root certificate := by
  cases certificate with
  | model _ => exact checkModel_sound h
  | refutation _ => exact checkRefutation_sound h

/-- Total search for finite class and role axioms and a root concept. -/
def searchUnder (rules : RoleTheory) (tbox : TBox) (root : Concept) : Certificate :=
  let pool := survivors rules tbox root
  if hasRoot root pool then .model pool else .refutation (candidates tbox root).length

/-- Search returns a certificate accepted by the appropriate checker. -/
theorem searchUnder_checked (rules : RoleTheory) (tbox : TBox) (root : Concept) :
    checkCertificateUnder rules tbox root (searchUnder rules tbox root) = true := by
  by_cases h : hasRoot root (survivors rules tbox root) = true
  · rw [searchUnder, ite_eq_left h]
    simp only [checkCertificateUnder, checkModelUnder, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨fun _ hm => survivors_local rules tbox root hm, fun _ hm => survivors_witnesses rules tbox root hm⟩, h⟩
  · have hf : hasRoot root (survivors rules tbox root) = false := Bool.eq_false_iff.mpr h
    rw [searchUnder, ite_eq_right h]
    change (!hasRoot root (survivors rules tbox root)) = true
    rwa [Bool.not_eq_true']

abbrev search := searchUnder []

theorem search_checked (tbox : TBox) (root : Concept) :
    checkCertificate tbox root (search tbox root) = true := searchUnder_checked [] tbox root

theorem searchUnder_correct (rules : RoleTheory) (tbox : TBox) (root : Concept) :
    certificateClaimUnder rules tbox root (searchUnder rules tbox root) :=
  checkCertificateUnder_sound (searchUnder_checked rules tbox root)

/-- Search is total in Lean and proves the claim associated with its output. -/
theorem search_correct (tbox : TBox) (root : Concept) :
    certificateClaim tbox root (search tbox root) :=
  checkCertificate_sound (search_checked tbox root)

theorem search_model_iff (tbox : TBox) (root : Concept) :
    (∃ pool, search tbox root = .model pool) ↔ ConceptSat tbox root := by
  have hs := search_correct tbox root
  cases h : search tbox root with
  | model pool =>
    rw [h] at hs
    exact ⟨fun _ => hs, fun _ => ⟨pool, rfl⟩⟩
  | refutation rounds =>
    rw [h] at hs
    constructor
    · rintro ⟨_, he⟩
      cases he
    · intro hsat
      exact False.elim (hs hsat)

theorem search_refutation_iff (tbox : TBox) (root : Concept) :
    (∃ rounds, search tbox root = .refutation rounds) ↔ ¬ ConceptSat tbox root := by
  have hs := search_correct tbox root
  cases h : search tbox root with
  | model pool =>
    rw [h] at hs
    constructor
    · rintro ⟨_, he⟩
      cases he
    · intro hunsat
      exact False.elim (hunsat hs)
  | refutation rounds =>
    rw [h] at hs
    exact ⟨fun _ => hs, fun _ => ⟨rounds, rfl⟩⟩

/-- Finite GCIs cannot force an infinite carrier for a satisfiable root. -/
theorem finite_model_property (tbox : TBox) (root : Concept) (hs : ConceptSat tbox root) :
    FiniteConceptSat tbox root := by
  obtain ⟨pool, hp⟩ := (search_model_iff tbox root).mpr hs
  have checked := search_checked tbox root
  rw [hp] at checked
  exact checkModel_finite_sound checked

/-- Check both model certificates needed for independence of `A ⊑ B`. -/
def checkSentenceIndependence (tbox : TBox) (a b : Concept) (counter positive : List Row) : Bool :=
  checkModel tbox (.conj a (.neg b)) counter && checkModel (⟨a, b⟩ :: tbox) .top positive

theorem checkSentenceIndependence_sound {tbox : TBox} {a b : Concept} {counter positive : List Row}
    (h : checkSentenceIndependence tbox a b counter positive = true) :
    ¬ Subsumes tbox a b ∧ ¬ EntailsNegatedInclusion tbox a b := by
  simp only [checkSentenceIndependence, Bool.and_eq_true] at h
  exact ⟨fun hs => (subsumes_iff tbox a b).mp hs (checkModel_sound h.1),
    fun hn => (entailsNegatedInclusion_iff tbox a b).mp hn (checkModel_sound h.2)⟩

/-- Produce both finite models exactly when the inclusion sentence is independent. -/
def searchSentenceIndependence (tbox : TBox) (a b : Concept) : Option (List Row × List Row) :=
  match search tbox (.conj a (.neg b)) with
  | .refutation _ => none
  | .model counter =>
    match search (⟨a, b⟩ :: tbox) .top with
    | .refutation _ => none
    | .model positive => some (counter, positive)

theorem searchSentenceIndependence_checked {tbox : TBox} {a b : Concept} {counter positive : List Row}
    (h : searchSentenceIndependence tbox a b = some (counter, positive)) :
    checkSentenceIndependence tbox a b counter positive = true := by
  unfold searchSentenceIndependence at h
  split at h
  · contradiction
  · rename_i c hc
    split at h
    · contradiction
    · rename_i p hp
      cases h
      have hcounter := search_checked tbox (.conj a (.neg b))
      have hpositive := search_checked (⟨a, b⟩ :: tbox) .top
      rw [hc] at hcounter
      rw [hp] at hpositive
      simp only [checkSentenceIndependence, Bool.and_eq_true]
      exact ⟨hcounter, hpositive⟩

theorem searchSentenceIndependence_iff (tbox : TBox) (a b : Concept) :
    (∃ counter positive, searchSentenceIndependence tbox a b = some (counter, positive)) ↔
    ¬ Subsumes tbox a b ∧ ¬ EntailsNegatedInclusion tbox a b := by
  classical
  constructor
  · rintro ⟨_, _, h⟩
    exact checkSentenceIndependence_sound (searchSentenceIndependence_checked h)
  · intro ⟨hnq, hnnq⟩
    have hcounter : ConceptSat tbox (.conj a (.neg b)) :=
      Classical.not_not.mp (fun h => hnq ((subsumes_iff tbox a b).mpr h))
    have hpositive : ConceptSat (⟨a, b⟩ :: tbox) .top :=
      Classical.not_not.mp (fun h => hnnq ((entailsNegatedInclusion_iff tbox a b).mpr h))
    obtain ⟨counter, hc⟩ := (search_model_iff tbox _).mpr hcounter
    obtain ⟨positive, hp⟩ := (search_model_iff (⟨a, b⟩ :: tbox) .top).mpr hpositive
    exact ⟨counter, positive, by simp only [searchSentenceIndependence, hc, hp]⟩

end Sabrina.ALC
