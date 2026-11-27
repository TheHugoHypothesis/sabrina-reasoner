import Sabrina.OWL2.FastLocality
import Sabrina.OWL2.Classification
import Sabrina.OWL2.Materialize

/-! Kernel-verified minimal justifications (explanations) for OWL 2 DL
    entailment and ontology inconsistency (Horridge–Kalyanpur–Parsia
    expand-and-shrink with QuickXplain binary split + Reiter Hitting-Set Tree).

    Pre-filters the source ontology via `FastLocality.extractBotModuleFast`
    (shrinking 350k-axiom ontologies to small local modules before shrinking),
    uses QuickXplain binary-split shrink (`O(k log |M|)` oracle calls) followed
    by a certified minimality sweep, and optionally enumerates multiple distinct
    minimal justifications via Reiter's Hitting-Set Tree (HST).

    Proves (`zero sorry`, strictly standard Lean 4 core axioms):
    - `findOneUnsatJustificationWith_sound` / `findOneUnsatJustificationReal_sound`
    - `findOneJustificationWith_sound` / `findOneJustificationReal_sound`
    - `findAllUnsatJustificationsWith_sound` / `findAllUnsatJustificationsReal_sound`
    - `findAllJustificationsWith_sound` / `findAllJustificationsReal_sound`

    Every returned justification `J` satisfies:
    1. Subset: `∀ a ∈ J, a ∈ o`
    2. Sufficiency: `¬ Satisfiable dm J` (or `Entails dm J [qAx]`)
    3. Strict Minimality: `∀ a ∈ J, Satisfiable dm (J.filter (· != a))`
       (or `¬ Entails dm (J.filter (· != a)) [qAx]`). -/

namespace Sabrina.OWL2.Justification

open Sabrina.OWL2
open Sabrina.OWL2.Datatypes
open Sabrina.OWL2.Profile
open Sabrina.OWL2.FastLocality
open Sabrina.OWL2.Classification
open Sabrina.OWL2.Materialize
open Sabrina.OWL2.SROIQD.Termination.WiderData
open Sabrina.OWL2.SROIQD.Termination.ExtendedQuery

/-! ### 1. Formal Justification Specifications & Monotonicity Lemmas -/

/-- `J` is a minimal justification for the inconsistency of `o`:
    `J ⊆ o`, `J` is unsatisfiable, and removing any axiom from `J` yields a
    satisfiable ontology. -/
def IsMinimalUnsatJustification (dm : DatatypeMap) (o J : Ontology) : Prop :=
  (∀ a ∈ J, a ∈ o) ∧
  ¬ Satisfiable dm J ∧
  (∀ a ∈ J, Satisfiable dm (J.filter (· != a)))

/-- `J` is a minimal justification for `o ⊨ qAx`:
    `J ⊆ o`, `J ⊨ qAx`, and removing any axiom from `J` breaks entailment. -/
def IsMinimalJustification (dm : DatatypeMap) (o : Ontology) (qAx : Axiom) (J : Ontology) : Prop :=
  (∀ a ∈ J, a ∈ o) ∧
  Entails dm J [qAx] ∧
  (∀ a ∈ J, ¬ Entails dm (J.filter (· != a)) [qAx])

private theorem satisfiable_of_subset {dm : DatatypeMap} {o1 o2 : Ontology}
    (hsub : ∀ a ∈ o1, a ∈ o2) (hsat : Satisfiable dm o2) : Satisfiable dm o1 := by
  obtain ⟨i, assign, hs⟩ := hsat
  exact ⟨i, assign, fun a ha => hs a (hsub a ha)⟩

private theorem unsat_mono {dm : DatatypeMap} {o1 o2 : Ontology}
    (hsub : ∀ a ∈ o1, a ∈ o2) (hu : ¬ Satisfiable dm o1) : ¬ Satisfiable dm o2 :=
  fun hs => hu (satisfiable_of_subset hsub hs)

private theorem entails_mono {dm : DatatypeMap} {o1 o2 q : Ontology}
    (hsub : ∀ a ∈ o1, a ∈ o2) (he : Entails dm o1 q) : Entails dm o2 q := by
  intro i ⟨assign, hs⟩
  exact he i ⟨assign, fun a ha => hs a (hsub a ha)⟩

private def dedupAxioms : Ontology → Ontology
  | [] => []
  | a :: rest =>
    let r := dedupAxioms rest
    if r.contains a then r else a :: r

private theorem dedupAxioms_mem_iff {o : Ontology} {a : Axiom} :
    a ∈ dedupAxioms o ↔ a ∈ o := by
  induction o generalizing a with
  | nil => simp [dedupAxioms]
  | cons x tl ih =>
    simp only [dedupAxioms]
    cases hc : (dedupAxioms tl).contains x
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
    · simp only [↓reduceIte, List.mem_cons, ih]
      have hx : x ∈ tl := ih.mp (List.contains_iff_mem.mp hc)
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun e => e ▸ hx) id⟩

private theorem dedupAxioms_nodup (o : Ontology) : (dedupAxioms o).Nodup := by
  induction o with
  | nil => simp [dedupAxioms]
  | cons x tl ih =>
    simp only [dedupAxioms]
    cases hc : (dedupAxioms tl).contains x
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      exact ⟨(fun h => by rw [List.contains_iff_mem.mpr h] at hc; cases hc), ih⟩
    · simp only [↓reduceIte]; exact ih

private theorem mem_take_or_drop {α : Type} {xs : List α} {n : Nat} {a : α}
    (h : a ∈ xs) : a ∈ xs.take n ∨ a ∈ xs.drop n := by
  have heq : xs.take n ++ xs.drop n = xs := List.take_append_drop n xs
  rw [← heq] at h
  exact List.mem_append.mp h

/-! ### 2. Generic QuickXplain Binary Shrink + Certified Minimality Sweep -/

/-- QuickXplain binary-split shrink (`O(k log |M|)` calls): returns `J ⊆ cand`
    such that `pred (bg ++ J) = true` whenever `pred (bg ++ cand) = true`. -/
private def binaryShrink (pred : Ontology → Option Bool) (bg cand : Ontology) :
    Option Ontology :=
  if cand.length ≤ 1 then
    some cand
  else
    let half := cand.length / 2
    let left := cand.take half
    let right := cand.drop half
    (pred (bg ++ right)).bind fun keepRight =>
      if keepRight then
        binaryShrink pred bg right
      else
        (pred (bg ++ left)).bind fun keepLeft =>
          if keepLeft then
            binaryShrink pred bg left
          else
            (binaryShrink pred (bg ++ right) left).bind fun left' =>
              (binaryShrink pred (bg ++ left') right).map fun right' =>
                left' ++ right'
termination_by cand.length
decreasing_by
  all_goals simp only [List.length_drop, List.length_take]; omega

private theorem binaryShrink_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    (bg cand res : Ontology)
    (hhold : P (bg ++ cand))
    (h : binaryShrink pred bg cand = some res) :
    (∀ a ∈ res, a ∈ cand) ∧ P (bg ++ res) := by
  unfold binaryShrink at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    exact ⟨fun _ ha => ha, hhold⟩
  · rename_i hgt
    obtain ⟨kr, hkr, hrest⟩ := Option.bind_eq_some_iff.mp h
    cases kr with
    | true =>
      simp only [↓reduceIte] at hrest
      have hPr : P (bg ++ cand.drop (cand.length / 2)) := (hpred hkr).mp rfl
      have ⟨hsub, hP⟩ := binaryShrink_sound hmono hpred bg (cand.drop (cand.length / 2)) res hPr hrest
      exact ⟨fun a ha => List.mem_of_mem_drop (hsub a ha), hP⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at hrest
      obtain ⟨kl, hkl, hrest2⟩ := hrest
      cases kl with
      | true =>
        simp only [↓reduceIte] at hrest2
        have hPl : P (bg ++ cand.take (cand.length / 2)) := (hpred hkl).mp rfl
        have ⟨hsub, hP⟩ := binaryShrink_sound hmono hpred bg (cand.take (cand.length / 2)) res hPl hrest2
        exact ⟨fun a ha => List.mem_of_mem_take (hsub a ha), hP⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrest2
        obtain ⟨left', hleft, right', hright, rfl⟩ := hrest2
        have hP1 : P ((bg ++ cand.drop (cand.length / 2)) ++ cand.take (cand.length / 2)) := by
          refine hmono (fun a ha => ?_) hhold
          rcases List.mem_append.mp ha with hb | hc
          · exact List.mem_append_left _ (List.mem_append_left _ hb)
          · rcases mem_take_or_drop (n := cand.length / 2) hc with ht | hd
            · exact List.mem_append_right _ ht
            · exact List.mem_append_left _ (List.mem_append_right _ hd)
        have ⟨hsubL, hPL⟩ := binaryShrink_sound hmono hpred
          (bg ++ cand.drop (cand.length / 2)) (cand.take (cand.length / 2)) left' hP1 hleft
        have hP2 : P ((bg ++ left') ++ cand.drop (cand.length / 2)) := by
          refine hmono (fun a ha => ?_) hPL
          rcases List.mem_append.mp ha with hbr | hl
          · rcases List.mem_append.mp hbr with hb | hd
            · exact List.mem_append_left _ (List.mem_append_left _ hb)
            · exact List.mem_append_right _ hd
          · exact List.mem_append_left _ (List.mem_append_right _ hl)
        have ⟨hsubR, hPR⟩ := binaryShrink_sound hmono hpred
          (bg ++ left') (cand.drop (cand.length / 2)) right' hP2 hright
        refine ⟨fun a ha => ?_, ?_⟩
        · rcases List.mem_append.mp ha with hl | hr
          · exact List.mem_of_mem_take (hsubL a hl)
          · exact List.mem_of_mem_drop (hsubR a hr)
        · refine hmono (fun a ha => ?_) hPR
          rcases List.mem_append.mp ha with hbl | hr
          · rcases List.mem_append.mp hbl with hb | hl
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right _ (List.mem_append_left _ hl)
          · exact List.mem_append_right _ (List.mem_append_right _ hr)
termination_by cand.length
decreasing_by
  all_goals simp only [List.length_drop, List.length_take]; omega

/-- Certified minimality sweep: starting from a duplicate-free candidate `rem`
    and kept set `kept`, keeps only axioms essential to `P`. -/
private def minimizeLinear (pred : Ontology → Option Bool) :
    Ontology → Ontology → Option Ontology
  | kept, [] => some kept.reverse
  | kept, a :: rest =>
    (pred (kept ++ rest)).bind fun stillHolds =>
      if stillHolds then
        minimizeLinear pred kept rest
      else
        minimizeLinear pred (a :: kept) rest

private theorem minimizeLinear_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o)) :
    ∀ (rem kept res : Ontology),
      (kept ++ rem).Nodup →
      P (kept ++ rem) →
      (∀ k ∈ kept, ¬ P ((kept ++ rem).filter (· != k))) →
      minimizeLinear pred kept rem = some res →
      (∀ a ∈ res, a ∈ kept ++ rem) ∧ P res ∧ (∀ a ∈ res, ¬ P (res.filter (· != a))) := by
  intro rem
  induction rem with
  | nil =>
    intro kept res _ hP hmin h
    simp only [minimizeLinear, Option.some.injEq] at h; subst h
    simp only [List.append_nil] at hP hmin ⊢
    refine ⟨fun a ha => List.mem_reverse.mp ha,
      hmono (fun a ha => List.mem_reverse.mpr ha) hP,
      fun a ha hPa => ?_⟩
    have haK : a ∈ kept := List.mem_reverse.mp ha
    exact hmin a haK (hmono (fun x hx => by
      simp only [List.mem_filter, List.mem_reverse] at hx ⊢
      exact hx) hPa)
  | cons a rest ih =>
    intro kept res hnd hP hmin h
    simp only [minimizeLinear, Option.bind_eq_some_iff] at h
    obtain ⟨stillHolds, hcheck, hrec⟩ := h
    have hndDisj : a ∉ kept ∧ a ∉ rest ∧ (kept ++ rest).Nodup := by
      have h1 := List.nodup_append.mp hnd
      have h2 := List.nodup_cons.mp h1.2.1
      refine ⟨fun hk => h1.2.2 a hk a (List.mem_cons_self ..) rfl, h2.1,
        List.nodup_append.mpr ⟨h1.1, h2.2, fun x hx y hy => h1.2.2 x hx y (List.mem_cons_of_mem _ hy)⟩⟩
    cases stillHolds with
    | true =>
      simp only [↓reduceIte] at hrec
      have hP' : P (kept ++ rest) := (hpred hcheck).mp rfl
      have hmin' : ∀ k ∈ kept, ¬ P ((kept ++ rest).filter (· != k)) := fun k hk hPk =>
        hmin k hk (hmono (fun x hx => by
          simp only [List.mem_filter, List.mem_append, List.mem_cons] at hx ⊢
          exact ⟨hx.1.elim Or.inl (fun hr => Or.inr (Or.inr hr)), hx.2⟩) hPk)
      obtain ⟨hsub, hPres, hMres⟩ := ih kept res hndDisj.2.2 hP' hmin' hrec
      refine ⟨fun x hx => ?_, hPres, hMres⟩
      rcases List.mem_append.mp (hsub x hx) with hk | hr
      · exact List.mem_append_left _ hk
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrec
      have hNotP : ¬ P (kept ++ rest) := fun hp => Bool.noConfusion ((hpred hcheck).mpr hp)
      have hnd' : ((a :: kept) ++ rest).Nodup := by
        simp only [List.cons_append, List.nodup_cons]
        exact ⟨fun h => (List.mem_append.mp h).elim hndDisj.1 hndDisj.2.1, hndDisj.2.2⟩
      have hP' : P ((a :: kept) ++ rest) :=
        hmono (fun x hx => by
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          rcases hx with hk | rfl | hr
          · exact Or.inl (Or.inr hk)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hr) hP
      have hmin' : ∀ k ∈ a :: kept, ¬ P (((a :: kept) ++ rest).filter (· != k)) := by
        intro k hk hPk
        rcases List.mem_cons.mp hk with rfl | hk'
        · apply hNotP
          refine hmono (fun x hx => ?_) hPk
          simp only [List.mem_filter, List.mem_append, List.mem_cons, bne_iff_ne] at hx ⊢
          rcases hx with ⟨(rfl | hxk) | hxr, hne⟩
          · exact absurd rfl hne
          · exact Or.inl hxk
          · exact Or.inr hxr
        · apply hmin k hk'
          refine hmono (fun x hx => ?_) hPk
          simp only [List.mem_filter, List.mem_append, List.mem_cons] at hx ⊢
          rcases hx with ⟨(rfl | hxk) | hxr, hne⟩
          · exact ⟨Or.inr (Or.inl rfl), hne⟩
          · exact ⟨Or.inl hxk, hne⟩
          · exact ⟨Or.inr (Or.inr hxr), hne⟩
      obtain ⟨hsub, hPres, hMres⟩ := ih (a :: kept) res hnd' hP' hmin' hrec
      refine ⟨fun x hx => ?_, hPres, hMres⟩
      simp only [List.mem_append, List.mem_cons] at hsub ⊢
      rcases hsub x hx with (rfl | hxk) | hxr
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hxk
      · exact Or.inr (Or.inr hxr)

/-- Compute a single certified minimal subset `J ⊆ cand` satisfying monotone `P`. -/
private def findOneMinimal (pred : Ontology → Option Bool) (cand : Ontology) :
    Option Ontology :=
  let clean := dedupAxioms cand
  (binaryShrink pred [] clean).bind fun shrunk =>
    minimizeLinear pred [] (dedupAxioms shrunk)

private theorem findOneMinimal_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    {cand res : Ontology} (hP : P cand)
    (h : findOneMinimal pred cand = some res) :
    (∀ a ∈ res, a ∈ cand) ∧ P res ∧ (∀ a ∈ res, ¬ P (res.filter (· != a))) := by
  unfold findOneMinimal at h
  obtain ⟨shrunk, hshr, hmin⟩ := Option.bind_eq_some_iff.mp h
  have hPclean : P ([] ++ dedupAxioms cand) :=
    hmono (fun a ha => dedupAxioms_mem_iff.mpr ha) hP
  obtain ⟨hsub1, hP1⟩ := binaryShrink_sound hmono hpred [] (dedupAxioms cand) shrunk hPclean hshr
  have hP2 : P ([] ++ dedupAxioms shrunk) :=
    hmono (fun a ha => dedupAxioms_mem_iff.mpr ha) hP1
  have hnd2 : ([] ++ dedupAxioms shrunk).Nodup := dedupAxioms_nodup shrunk
  obtain ⟨hsub2, hPres, hMres⟩ := minimizeLinear_sound hmono hpred (dedupAxioms shrunk) [] res
    hnd2 hP2 (fun _ hk => by cases hk) hmin
  refine ⟨fun a ha => ?_, hPres, hMres⟩
  have h1 : a ∈ dedupAxioms shrunk := by simpa using hsub2 a ha
  exact dedupAxioms_mem_iff.mp (hsub1 a (dedupAxioms_mem_iff.mp h1))

/-! ### 3. Reiter Hitting-Set Tree (HST) Enumeration of Multiple Justifications -/

private def sameAxiomSet (xs ys : Ontology) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

private def isSupersetHit (h1 h2 : Ontology) : Bool :=
  h1.all (h2.contains ·)

/-- Bounded Reiter Hitting-Set Tree (HST) enumeration: finds up to `maxJusts`
    distinct certified minimal subsets of `base` satisfying `pred`. -/
private def hstLoop (pred : Ontology → Option Bool) (base : Ontology) (maxJusts : Nat) :
    Nat → List Ontology → List Ontology → List Ontology → Option (List Ontology)
  | 0, _, _, found => some found.reverse
  | _ + 1, [], _, found => some found.reverse
  | fuel + 1, hit :: queue, closedHits, found =>
    if found.length ≥ maxJusts then
      some found.reverse
    else if closedHits.any (fun ch => isSupersetHit ch hit) then
      hstLoop pred base maxJusts fuel queue closedHits found
    else
      match found.find? (fun j => !j.any (hit.contains ·)) with
      | some existing =>
        let nextHits := existing.map fun a => a :: hit
        hstLoop pred base maxJusts fuel (queue ++ nextHits) closedHits found
      | none =>
        let sub := base.filter fun a => !hit.contains a
        (pred sub).bind fun holds =>
          if !holds then
            hstLoop pred base maxJusts fuel queue (hit :: closedHits) found
          else
            (findOneMinimal pred sub).bind fun j =>
              let found' := if found.any (sameAxiomSet j) then found else j :: found
              let nextHits := j.map fun a => a :: hit
              hstLoop pred base maxJusts fuel (queue ++ nextHits) closedHits found'

private theorem hstLoop_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    (base : Ontology) (maxJusts : Nat) :
    ∀ (fuel : Nat) (queue closedHits found res : List Ontology),
      (∀ J ∈ found, (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a)))) →
      hstLoop pred base maxJusts fuel queue closedHits found = some res →
      ∀ J ∈ res, (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue closedHits found res hinv h
    simp only [hstLoop, Option.some.injEq] at h; subst h
    exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
  | succ n ih =>
    intro queue closedHits found res hinv h
    cases queue with
    | nil =>
      simp only [hstLoop, Option.some.injEq] at h; subst h
      exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
    | cons hit rest =>
      simp only [hstLoop] at h
      cases hlen : decide (found.length ≥ maxJusts) with
      | true =>
        simp only [decide_eq_true_eq] at hlen
        simp only [hlen, ↓reduceIte, Option.some.injEq] at h; subst h
        exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
      | false =>
        simp only [decide_eq_false_iff_not] at hlen
        simp only [hlen, ↓reduceIte] at h
        cases hcl : closedHits.any (fun ch => isSupersetHit ch hit) with
        | true =>
          simp only [hcl, ↓reduceIte] at h
          exact ih rest closedHits found res hinv h
        | false =>
          simp only [hcl, Bool.false_eq_true, ↓reduceIte] at h
          cases hfind : found.find? (fun j => !j.any (hit.contains ·)) with
          | some existing =>
            rw [hfind] at h
            exact ih (rest ++ existing.map (· :: hit)) closedHits found res hinv h
          | none =>
            rw [hfind] at h
            obtain ⟨holds, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
            cases holds with
            | false =>
              simp only [Bool.not_false, ↓reduceIte] at hrest
              exact ih rest (hit :: closedHits) found res hinv hrest
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at hrest
              obtain ⟨j, hj, hrec⟩ := hrest
              have hPsub : P (base.filter fun a => !hit.contains a) := (hpred hchk).mp rfl
              obtain ⟨hsubJ, hPJ, hminJ⟩ := findOneMinimal_sound hmono hpred hPsub hj
              have hJBase : ∀ a ∈ j, a ∈ base := fun a ha => (List.mem_filter.mp (hsubJ a ha)).1
              have hinv' : ∀ J ∈ (if found.any (sameAxiomSet j) then found else j :: found),
                  (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))) := by
                intro J hJm
                split at hJm
                · exact hinv J hJm
                · rcases List.mem_cons.mp hJm with rfl | hJf
                  · exact ⟨hJBase, hPJ, hminJ⟩
                  · exact hinv J hJf
              exact ih (rest ++ j.map (· :: hit)) closedHits _ res hinv' hrec

/-! ### 3.5 Verified Parallel Frontier Reiter HST (`Task.spawn`) -/

private def spawnChunks {α β : Type} (chunk : Nat) (f : α → β) :
    Nat → List α → List (Task (List β))
  | 0, xs => [Task.pure (xs.map f)]
  | _ + 1, [] => []
  | workers + 1, x :: xs =>
    let (front, rest) := (x :: xs).splitAt chunk
    Task.spawn (fun () => front.map f) :: spawnChunks chunk f workers rest

private theorem spawnChunks_get {α β : Type} (chunk : Nat) (f : α → β)
    (workers : Nat) (xs : List α) :
    (spawnChunks chunk f workers xs).flatMap Task.get = xs.map f := by
  induction workers generalizing xs with
  | zero => simp [spawnChunks]
  | succ workers ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [spawnChunks, List.splitAt_eq, List.flatMap_cons, Task.spawn, ih]
      rw [← List.map_append, List.take_append_drop]

private def mapIndependent {α β : Type} (workers : Nat) (f : α → β) (xs : List α) : List β :=
  if workers ≤ 1 || xs.length ≤ 1 then xs.map f
  else
    let count := min workers xs.length
    let chunk := (xs.length + count - 1) / count
    (spawnChunks chunk f count xs).flatMap Task.get

private theorem mapIndependent_eq {α β : Type} (workers : Nat) (f : α → β) (xs : List α) :
    mapIndependent workers f xs = xs.map f := by
  unfold mapIndependent
  split
  · rfl
  · apply spawnChunks_get

/-- Evaluate a single open HST hitting-set node independently:
    - `none` if the oracle returns `none`
    - `some none` if `base \ hit` does not satisfy `pred` (closed branch)
    - `some (some j)` if a certified minimal justification `j ⊆ base \ hit` is found. -/
private def evalHSTNode (pred : Ontology → Option Bool) (base : Ontology) (hit : Ontology) :
    Option (Option Ontology) :=
  let sub := base.filter fun a => !hit.contains a
  (pred sub).bind fun holds =>
    if !holds then some none
    else (findOneMinimal pred sub).map some

private theorem evalHSTNode_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    {base hit j : Ontology}
    (h : evalHSTNode pred base hit = some (some j)) :
    (∀ a ∈ j, a ∈ base) ∧ P j ∧ (∀ a ∈ j, ¬ P (j.filter (· != a))) := by
  unfold evalHSTNode at h
  dsimp only at h
  obtain ⟨holds, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  cases holds with
  | false => simp at hrest
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨j', hj', hEq⟩ := hrest
    cases hEq
    have hPsub : P (base.filter fun a => !hit.contains a) := (hpred hchk).mp rfl
    obtain ⟨hsubJ, hPJ, hminJ⟩ := findOneMinimal_sound hmono hpred hPsub hj'
    exact ⟨fun a ha => (List.mem_filter.mp (hsubJ a ha)).1, hPJ, hminJ⟩

/-- Pop up to `batchCap` genuinely open hitting sets from the BFS frontier,
    skipping hits subsumed by `closedHits` or already in the batch, and reusing
    already-found justifications without oracle calls. -/
private def popOpenBatch (closedHits found : List Ontology) :
    Nat → Nat → List Ontology → List Ontology → List Ontology × List Ontology
  | 0, _, queue, acc => (acc.reverse, queue)
  | _, 0, queue, acc => (acc.reverse, queue)
  | _ + 1, _ + 1, [], acc => (acc.reverse, [])
  | scanFuel + 1, rem + 1, hit :: rest, acc =>
    if closedHits.any (fun ch => isSupersetHit ch hit) ||
       acc.any (fun prev => isSupersetHit prev hit || sameAxiomSet prev hit) then
      popOpenBatch closedHits found scanFuel (rem + 1) rest acc
    else
      match found.find? (fun j => !j.any (hit.contains ·)) with
      | some existing =>
        let nextHits := existing.map fun a => a :: hit
        popOpenBatch closedHits found scanFuel (rem + 1) (rest ++ nextHits) acc
      | none =>
        popOpenBatch closedHits found scanFuel rem rest (hit :: acc)

/-- Merge evaluated `(hit, result)` pairs from a parallel HST batch into
    `(queue, closedHits, found)`. -/
private def applyHSTBatch (maxJusts : Nat) :
    List (Ontology × Option (Option Ontology)) →
    List Ontology → List Ontology → List Ontology →
    Option (List Ontology × List Ontology × List Ontology)
  | [], queue, closedHits, found => some (queue, closedHits, found)
  | (hit, res?) :: rest, queue, closedHits, found =>
    match res? with
    | none => none
    | some none =>
      applyHSTBatch maxJusts rest queue (hit :: closedHits) found
    | some (some j) =>
      if found.length ≥ maxJusts then
        some (queue, closedHits, found)
      else
        let found' := if found.any (sameAxiomSet j) then found else j :: found
        let nextHits := j.map fun a => a :: hit
        applyHSTBatch maxJusts rest (queue ++ nextHits) closedHits found'

private theorem applyHSTBatch_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    (base : Ontology) (maxJusts : Nat)
    (batch : List Ontology)
    (queue closedHits found queue' closedHits' found' : List Ontology)
    (hinv : ∀ J ∈ found, (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))))
    (h : applyHSTBatch maxJusts (batch.zip (batch.map (evalHSTNode pred base)))
          queue closedHits found = some (queue', closedHits', found')) :
    ∀ J ∈ found', (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))) := by
  induction batch generalizing queue closedHits found with
  | nil =>
    simp only [List.map_nil, List.zip_nil_right, applyHSTBatch, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    exact hinv
  | cons hit tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, applyHSTBatch] at h
    cases heval : evalHSTNode pred base hit with
    | none => rw [heval] at h; cases h
    | some res =>
      rw [heval] at h
      cases res with
      | none =>
        exact ih queue (hit :: closedHits) found hinv h
      | some j =>
        dsimp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          exact hinv
        · have hjSpec := evalHSTNode_sound hmono hpred heval
          have hinv' : ∀ J ∈ (if found.any (sameAxiomSet j) then found else j :: found),
              (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))) := by
            intro J hJm
            split at hJm
            · exact hinv J hJm
            · rcases List.mem_cons.mp hJm with rfl | hJf
              · exact hjSpec
              · exact hinv J hJf
          exact ih (queue ++ j.map (· :: hit)) closedHits _ hinv' h

/-- Batch-parallel Reiter Hitting-Set Tree (HST) enumeration backed by `Task.spawn`.
    Uses a fixed frontier batch width `batchWidth` so output is provably identical across
    all worker counts (`hstLoopPar_workers_eq`). -/
private def hstLoopPar (pred : Ontology → Option Bool) (base : Ontology) (maxJusts : Nat)
    (workers : Nat) (batchWidth : Nat) :
    Nat → List Ontology → List Ontology → List Ontology → Option (List Ontology)
  | 0, _, _, found => some found.reverse
  | _ + 1, [], _, found => some found.reverse
  | fuel + 1, queue, closedHits, found =>
    if found.length ≥ maxJusts then
      some found.reverse
    else
      let scanFuel := queue.length + batchWidth * 8 + 16
      let (batch, remQueue) := popOpenBatch closedHits found scanFuel batchWidth queue []
      if batch.isEmpty then
        if remQueue.isEmpty then some found.reverse
        else hstLoopPar pred base maxJusts workers batchWidth fuel remQueue closedHits found
      else
        let results := mapIndependent workers (evalHSTNode pred base) batch
        (applyHSTBatch maxJusts (batch.zip results) remQueue closedHits found).bind
          fun (q', cl', f') =>
            hstLoopPar pred base maxJusts workers batchWidth fuel q' cl' f'

private theorem hstLoopPar_workers_eq (pred : Ontology → Option Bool) (base : Ontology)
    (maxJusts workers batchWidth : Nat) :
    ∀ (fuel : Nat) (queue closedHits found : List Ontology),
      hstLoopPar pred base maxJusts workers batchWidth fuel queue closedHits found =
      hstLoopPar pred base maxJusts 1 batchWidth fuel queue closedHits found := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro queue closedHits found
    cases queue with
    | nil => rfl
    | cons h q =>
      simp only [hstLoopPar]
      split
      · rfl
      · split
        · split
          · rfl
          · exact ih _ _ _
        · rw [mapIndependent_eq workers, mapIndependent_eq 1]
          cases applyHSTBatch maxJusts _ _ closedHits found with
          | none => rfl
          | some triple =>
            rcases triple with ⟨q', cl', f'⟩
            simp only [Option.bind_some]
            exact ih q' cl' f'

private theorem hstLoopPar_sound {P : Ontology → Prop}
    (hmono : ∀ {o1 o2}, (∀ a ∈ o1, a ∈ o2) → P o1 → P o2)
    {pred : Ontology → Option Bool}
    (hpred : ∀ {o b}, pred o = some b → (b = true ↔ P o))
    (base : Ontology) (maxJusts workers batchWidth : Nat) :
    ∀ (fuel : Nat) (queue closedHits found res : List Ontology),
      (∀ J ∈ found, (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a)))) →
      hstLoopPar pred base maxJusts workers batchWidth fuel queue closedHits found = some res →
      ∀ J ∈ res, (∀ a ∈ J, a ∈ base) ∧ P J ∧ (∀ a ∈ J, ¬ P (J.filter (· != a))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue closedHits found res hinv h
    simp only [hstLoopPar, Option.some.injEq] at h; subst h
    exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
  | succ n ih =>
    intro queue closedHits found res hinv h
    cases queue with
    | nil =>
      simp only [hstLoopPar, Option.some.injEq] at h; subst h
      exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
    | cons hd tl =>
      simp only [hstLoopPar] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            exact fun J hJ => hinv J (List.mem_reverse.mp hJ)
          · exact ih _ closedHits found res hinv h
        · rw [mapIndependent_eq] at h
          obtain ⟨⟨q', cl', f'⟩, hbatch, hrec⟩ := Option.bind_eq_some_iff.mp h
          have hinv' := applyHSTBatch_sound hmono hpred base maxJusts _ _ closedHits found q' cl' f' hinv hbatch
          exact ih q' cl' f' res hinv' hrec

/-! ### 4. Public Certified Justification APIs (Inconsistency & Entailment) -/

structure UnsatExplanation where
  inconsistent : Bool
  justifications : List Ontology
  deriving Repr

structure EntailmentExplanation where
  entailed : Bool
  justifications : List Ontology
  deriving Repr

private def unsatPred (solve : Ontology → Option Bool) (o : Ontology) : Option Bool :=
  (solve o).map (!·)

private theorem unsatPred_iff {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {b : Bool} (h : unsatPred solve o = some b) :
    b = true ↔ ¬ Satisfiable dm o := by
  simp only [unsatPred, Option.map_eq_some_iff] at h
  obtain ⟨sat, hsat, rfl⟩ := h
  cases sat with
  | false =>
    simp only [Bool.not_false, true_iff]
    exact fun hs => Bool.noConfusion ((hsolve hsat).mpr hs)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]
    exact (hsolve hsat).mp rfl

/-- Find one certified minimal justification for inconsistency of `o`.
    Pre-filters `o` with `FastLocality.extractBotModuleFast o Sig.empty`. -/
def findOneUnsatJustificationWith (solve : Ontology → Option Bool) (o : Ontology) :
    Option UnsatExplanation :=
  let mod := (extractBotModuleFast o Sig.empty).1
  (unsatPred solve mod).bind fun isUnsat =>
    if !isUnsat then
      some { inconsistent := false, justifications := [] }
    else
      (findOneMinimal (unsatPred solve) mod).map fun J =>
        { inconsistent := true, justifications := [J] }

theorem findOneUnsatJustificationWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {res : UnsatExplanation}
    (h : findOneUnsatJustificationWith solve o = some res) :
    (res.inconsistent = false → Satisfiable dm o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable dm o ∧
      res.justifications ≠ [] ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification dm o J) := by
  unfold findOneUnsatJustificationWith at h
  dsimp only at h
  obtain ⟨isUnsat, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModSat : Satisfiable dm o ↔ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
    extractBotModuleFast_sat_iff o Sig.empty
  have hModSub : ∀ a ∈ (extractBotModuleFast o Sig.empty).1, a ∈ o :=
    (extractBotModuleFast_valid o Sig.empty).1
  cases isUnsat with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hSatMod : Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      Classical.byContradiction fun hnu => Bool.noConfusion ((unsatPred_iff hsolve hchk).mpr hnu)
    exact ⟨fun _ => hModSat.mpr hSatMod, fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨J, hJ, rfl⟩ := hrest
    have hUnsatMod : ¬ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      (unsatPred_iff hsolve hchk).mp rfl
    obtain ⟨hsubJ, hUJ, hminJ⟩ := findOneMinimal_sound (P := fun x => ¬ Satisfiable dm x)
      (fun hsub => unsat_mono hsub) (unsatPred_iff hsolve) hUnsatMod hJ
    refine ⟨(fun hc => by cases hc), fun _ => ⟨fun hs => hUnsatMod (hModSat.mp hs), by simp, ?_⟩⟩
    intro J' hJm
    rw [List.mem_singleton.mp hJm]
    exact ⟨fun a ha => hModSub a (hsubJ a ha), hUJ,
      fun a ha => Classical.byContradiction (hminJ a ha)⟩

/-- Find up to `maxJusts` distinct certified minimal justifications for inconsistency of `o`. -/
def findAllUnsatJustificationsWith (solve : Ontology → Option Bool) (o : Ontology)
    (maxJusts : Nat := 5) (hstFuel : Nat := 128) : Option UnsatExplanation :=
  let mod := (extractBotModuleFast o Sig.empty).1
  (unsatPred solve mod).bind fun isUnsat =>
    if !isUnsat then
      some { inconsistent := false, justifications := [] }
    else
      (hstLoop (unsatPred solve) (dedupAxioms mod) maxJusts hstFuel [[]] [] []).map fun justs =>
        { inconsistent := true, justifications := justs }

theorem findAllUnsatJustificationsWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {maxJusts hstFuel : Nat} {res : UnsatExplanation}
    (h : findAllUnsatJustificationsWith solve o maxJusts hstFuel = some res) :
    (res.inconsistent = false → Satisfiable dm o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable dm o ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification dm o J) := by
  unfold findAllUnsatJustificationsWith at h
  dsimp only at h
  obtain ⟨isUnsat, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModSat : Satisfiable dm o ↔ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
    extractBotModuleFast_sat_iff o Sig.empty
  have hModSub : ∀ a ∈ (extractBotModuleFast o Sig.empty).1, a ∈ o :=
    (extractBotModuleFast_valid o Sig.empty).1
  cases isUnsat with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hSatMod : Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      Classical.byContradiction fun hnu => Bool.noConfusion ((unsatPred_iff hsolve hchk).mpr hnu)
    exact ⟨fun _ => hModSat.mpr hSatMod, fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨justs, hjusts, rfl⟩ := hrest
    have hUnsatMod : ¬ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      (unsatPred_iff hsolve hchk).mp rfl
    have hall := hstLoop_sound (P := fun x => ¬ Satisfiable dm x)
      (fun hsub => unsat_mono hsub) (unsatPred_iff hsolve)
      (dedupAxioms (extractBotModuleFast o Sig.empty).1) maxJusts hstFuel [[]] [] [] justs
      (fun _ hm => by cases hm) hjusts
    refine ⟨(fun hc => by cases hc), fun _ => ⟨fun hs => hUnsatMod (hModSat.mp hs), fun J hJ => ?_⟩⟩
    obtain ⟨hsubJ, hUJ, hminJ⟩ := hall J hJ
    exact ⟨fun a ha => hModSub a (dedupAxioms_mem_iff.mp (hsubJ a ha)), hUJ,
      fun a ha => Classical.byContradiction (hminJ a ha)⟩

/-- Find one certified minimal justification for `o ⊨ qAx`.
    Pre-filters `o` with `FastLocality.extractBotModuleFast o (axiomSig qAx)`. -/
def findOneJustificationWith (solve : Ontology → Option Bool) (o : Ontology) (qAx : Axiom) :
    Option EntailmentExplanation :=
  let mod := (extractBotModuleFast o (axiomSig qAx)).1
  (decidesAxiomEntails solve mod qAx).bind fun isEnt =>
    if !isEnt then
      some { entailed := false, justifications := [] }
    else
      (findOneMinimal (fun sub => decidesAxiomEntails solve sub qAx) mod).map fun J =>
        { entailed := true, justifications := [J] }

theorem findOneJustificationWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {qAx : Axiom} {res : EntailmentExplanation}
    (h : findOneJustificationWith solve o qAx = some res) :
    (res.entailed = false → ¬ Entails dm o [qAx]) ∧
    (res.entailed = true →
      Entails dm o [qAx] ∧
      res.justifications ≠ [] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification dm o qAx J) := by
  unfold findOneJustificationWith at h
  dsimp only at h
  obtain ⟨isEnt, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModEnt : Entails dm o [qAx] ↔ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
    extractBotModuleFast_entails_iff o [qAx] (axiomSig qAx)
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact Sig.Subset.refl _)
  have hModSub : ∀ a ∈ (extractBotModuleFast o (axiomSig qAx)).1, a ∈ o :=
    (extractBotModuleFast_valid o (axiomSig qAx)).1
  cases isEnt with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hNotMod : ¬ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      fun he => Bool.noConfusion ((decidesAxiomEntails_iff hsolve hchk).mpr he)
    exact ⟨fun _ he => hNotMod (hModEnt.mp he), fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨J, hJ, rfl⟩ := hrest
    have hEntMod : Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      (decidesAxiomEntails_iff hsolve hchk).mp rfl
    obtain ⟨hsubJ, hEJ, hminJ⟩ := findOneMinimal_sound (P := fun x => Entails dm x [qAx])
      (fun hsub => entails_mono hsub) (fun {x b} hx => decidesAxiomEntails_iff hsolve hx) hEntMod hJ
    refine ⟨(fun hc => by cases hc), fun _ => ⟨hModEnt.mpr hEntMod, by simp, ?_⟩⟩
    intro J' hJm
    rw [List.mem_singleton.mp hJm]
    exact ⟨fun a ha => hModSub a (hsubJ a ha), hEJ, hminJ⟩

/-- Find up to `maxJusts` distinct certified minimal justifications for `o ⊨ qAx`. -/
def findAllJustificationsWith (solve : Ontology → Option Bool) (o : Ontology) (qAx : Axiom)
    (maxJusts : Nat := 5) (hstFuel : Nat := 128) : Option EntailmentExplanation :=
  let mod := (extractBotModuleFast o (axiomSig qAx)).1
  (decidesAxiomEntails solve mod qAx).bind fun isEnt =>
    if !isEnt then
      some { entailed := false, justifications := [] }
    else
      (hstLoop (fun sub => decidesAxiomEntails solve sub qAx) (dedupAxioms mod)
        maxJusts hstFuel [[]] [] []).map fun justs =>
        { entailed := true, justifications := justs }

theorem findAllJustificationsWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {qAx : Axiom} {maxJusts hstFuel : Nat} {res : EntailmentExplanation}
    (h : findAllJustificationsWith solve o qAx maxJusts hstFuel = some res) :
    (res.entailed = false → ¬ Entails dm o [qAx]) ∧
    (res.entailed = true →
      Entails dm o [qAx] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification dm o qAx J) := by
  unfold findAllJustificationsWith at h
  dsimp only at h
  obtain ⟨isEnt, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModEnt : Entails dm o [qAx] ↔ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
    extractBotModuleFast_entails_iff o [qAx] (axiomSig qAx)
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact Sig.Subset.refl _)
  have hModSub : ∀ a ∈ (extractBotModuleFast o (axiomSig qAx)).1, a ∈ o :=
    (extractBotModuleFast_valid o (axiomSig qAx)).1
  cases isEnt with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hNotMod : ¬ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      fun he => Bool.noConfusion ((decidesAxiomEntails_iff hsolve hchk).mpr he)
    exact ⟨fun _ he => hNotMod (hModEnt.mp he), fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨justs, hjusts, rfl⟩ := hrest
    have hEntMod : Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      (decidesAxiomEntails_iff hsolve hchk).mp rfl
    have hall := hstLoop_sound (P := fun x => Entails dm x [qAx])
      (fun hsub => entails_mono hsub) (fun {x b} hx => decidesAxiomEntails_iff hsolve hx)
      (dedupAxioms (extractBotModuleFast o (axiomSig qAx)).1) maxJusts hstFuel [[]] [] [] justs
      (fun _ hm => by cases hm) hjusts
    refine ⟨(fun hc => by cases hc), fun _ => ⟨hModEnt.mpr hEntMod, fun J hJ => ?_⟩⟩
    obtain ⟨hsubJ, hEJ, hminJ⟩ := hall J hJ
    exact ⟨fun a ha => hModSub a (dedupAxioms_mem_iff.mp (hsubJ a ha)), hEJ, hminJ⟩

/-! ### 5. Dedekind-Cut `realDatatypeMap` Instantiations & Fast Hybrid Runtime -/

def findOneUnsatJustificationReal (o : Ontology) : Option UnsatExplanation :=
  findOneUnsatJustificationWith decideRealOntology? o

theorem findOneUnsatJustificationReal_sound {o : Ontology} {res : UnsatExplanation}
    (h : findOneUnsatJustificationReal o = some res) :
    (res.inconsistent = false → Satisfiable realDatatypeMap o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable realDatatypeMap o ∧
      res.justifications ≠ [] ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification realDatatypeMap o J) :=
  findOneUnsatJustificationWith_sound decideRealOntology_iff h

def findAllUnsatJustificationsReal (o : Ontology) (maxJusts : Nat := 5) (hstFuel : Nat := 128) :
    Option UnsatExplanation :=
  findAllUnsatJustificationsWith decideRealOntology? o maxJusts hstFuel

theorem findAllUnsatJustificationsReal_sound {o : Ontology} {maxJusts hstFuel : Nat}
    {res : UnsatExplanation} (h : findAllUnsatJustificationsReal o maxJusts hstFuel = some res) :
    (res.inconsistent = false → Satisfiable realDatatypeMap o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable realDatatypeMap o ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification realDatatypeMap o J) :=
  findAllUnsatJustificationsWith_sound decideRealOntology_iff h

def findOneJustificationReal (o : Ontology) (qAx : Axiom) : Option EntailmentExplanation :=
  findOneJustificationWith decideRealOntology? o qAx

theorem findOneJustificationReal_sound {o : Ontology} {qAx : Axiom}
    {res : EntailmentExplanation} (h : findOneJustificationReal o qAx = some res) :
    (res.entailed = false → ¬ Entails realDatatypeMap o [qAx]) ∧
    (res.entailed = true →
      Entails realDatatypeMap o [qAx] ∧
      res.justifications ≠ [] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification realDatatypeMap o qAx J) :=
  findOneJustificationWith_sound decideRealOntology_iff h

def findAllJustificationsReal (o : Ontology) (qAx : Axiom)
    (maxJusts : Nat := 5) (hstFuel : Nat := 128) : Option EntailmentExplanation :=
  findAllJustificationsWith decideRealOntology? o qAx maxJusts hstFuel

theorem findAllJustificationsReal_sound {o : Ontology} {qAx : Axiom}
    {maxJusts hstFuel : Nat} {res : EntailmentExplanation}
    (h : findAllJustificationsReal o qAx maxJusts hstFuel = some res) :
    (res.entailed = false → ¬ Entails realDatatypeMap o [qAx]) ∧
    (res.entailed = true →
      Entails realDatatypeMap o [qAx] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification realDatatypeMap o qAx J) :=
  findAllJustificationsWith_sound decideRealOntology_iff h

/-- Parallel Reiter HST enumeration for inconsistency justifications (`Task.spawn`),
    with kernel-verified soundness and worker-count invariance. -/
def findAllUnsatJustificationsParWith (solve : Ontology → Option Bool) (o : Ontology)
    (maxJusts : Nat := 5) (numWorkers : Nat := 8) (hstFuel : Nat := 128) :
    Option UnsatExplanation :=
  let mod := (extractBotModuleFast o Sig.empty).1
  (unsatPred solve mod).bind fun isUnsat =>
    if !isUnsat then
      some { inconsistent := false, justifications := [] }
    else
      (hstLoopPar (unsatPred solve) (dedupAxioms mod) maxJusts numWorkers 8 hstFuel [[]] [] []).map fun justs =>
        { inconsistent := true, justifications := justs }

theorem findAllUnsatJustificationsParWith_workers_eq (solve : Ontology → Option Bool)
    (o : Ontology) (maxJusts numWorkers hstFuel : Nat) :
    findAllUnsatJustificationsParWith solve o maxJusts numWorkers hstFuel =
    findAllUnsatJustificationsParWith solve o maxJusts 1 hstFuel := by
  unfold findAllUnsatJustificationsParWith
  dsimp only
  cases unsatPred solve (extractBotModuleFast o Sig.empty).1 with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      simp only [Option.bind_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hstLoopPar_workers_eq]

theorem findAllUnsatJustificationsParWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {maxJusts numWorkers hstFuel : Nat} {res : UnsatExplanation}
    (h : findAllUnsatJustificationsParWith solve o maxJusts numWorkers hstFuel = some res) :
    (res.inconsistent = false → Satisfiable dm o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable dm o ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification dm o J) := by
  unfold findAllUnsatJustificationsParWith at h
  dsimp only at h
  obtain ⟨isUnsat, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModSat : Satisfiable dm o ↔ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
    extractBotModuleFast_sat_iff o Sig.empty
  have hModSub : ∀ a ∈ (extractBotModuleFast o Sig.empty).1, a ∈ o :=
    (extractBotModuleFast_valid o Sig.empty).1
  cases isUnsat with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hSatMod : Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      Classical.byContradiction fun hnu => Bool.noConfusion ((unsatPred_iff hsolve hchk).mpr hnu)
    exact ⟨fun _ => hModSat.mpr hSatMod, fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨justs, hjusts, rfl⟩ := hrest
    have hUnsatMod : ¬ Satisfiable dm (extractBotModuleFast o Sig.empty).1 :=
      (unsatPred_iff hsolve hchk).mp rfl
    have hall := hstLoopPar_sound (P := fun x => ¬ Satisfiable dm x)
      (fun hsub => unsat_mono hsub) (unsatPred_iff hsolve)
      (dedupAxioms (extractBotModuleFast o Sig.empty).1) maxJusts numWorkers 8 hstFuel [[]] [] [] justs
      (fun _ hm => by cases hm) hjusts
    refine ⟨(fun hc => by cases hc), fun _ => ⟨fun hs => hUnsatMod (hModSat.mp hs), fun J hJ => ?_⟩⟩
    obtain ⟨hsubJ, hUJ, hminJ⟩ := hall J hJ
    exact ⟨fun a ha => hModSub a (dedupAxioms_mem_iff.mp (hsubJ a ha)), hUJ,
      fun a ha => Classical.byContradiction (hminJ a ha)⟩

/-- Parallel Reiter HST enumeration for entailment justifications (`Task.spawn`),
    with kernel-verified soundness and worker-count invariance. -/
def findAllJustificationsParWith (solve : Ontology → Option Bool) (o : Ontology) (qAx : Axiom)
    (maxJusts : Nat := 5) (numWorkers : Nat := 8) (hstFuel : Nat := 128) :
    Option EntailmentExplanation :=
  let mod := (extractBotModuleFast o (axiomSig qAx)).1
  (decidesAxiomEntails solve mod qAx).bind fun isEnt =>
    if !isEnt then
      some { entailed := false, justifications := [] }
    else
      (hstLoopPar (fun sub => decidesAxiomEntails solve sub qAx) (dedupAxioms mod)
        maxJusts numWorkers 8 hstFuel [[]] [] []).map fun justs =>
        { entailed := true, justifications := justs }

theorem findAllJustificationsParWith_workers_eq (solve : Ontology → Option Bool)
    (o : Ontology) (qAx : Axiom) (maxJusts numWorkers hstFuel : Nat) :
    findAllJustificationsParWith solve o qAx maxJusts numWorkers hstFuel =
    findAllJustificationsParWith solve o qAx maxJusts 1 hstFuel := by
  unfold findAllJustificationsParWith
  dsimp only
  cases decidesAxiomEntails solve (extractBotModuleFast o (axiomSig qAx)).1 qAx with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      simp only [Option.bind_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hstLoopPar_workers_eq]

theorem findAllJustificationsParWith_sound {dm : DatatypeMap} {solve : Ontology → Option Bool}
    (hsolve : ∀ {o b}, solve o = some b → (b = true ↔ Satisfiable dm o))
    {o : Ontology} {qAx : Axiom} {maxJusts numWorkers hstFuel : Nat} {res : EntailmentExplanation}
    (h : findAllJustificationsParWith solve o qAx maxJusts numWorkers hstFuel = some res) :
    (res.entailed = false → ¬ Entails dm o [qAx]) ∧
    (res.entailed = true →
      Entails dm o [qAx] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification dm o qAx J) := by
  unfold findAllJustificationsParWith at h
  dsimp only at h
  obtain ⟨isEnt, hchk, hrest⟩ := Option.bind_eq_some_iff.mp h
  have hModEnt : Entails dm o [qAx] ↔ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
    extractBotModuleFast_entails_iff o [qAx] (axiomSig qAx)
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact Sig.Subset.refl _)
  have hModSub : ∀ a ∈ (extractBotModuleFast o (axiomSig qAx)).1, a ∈ o :=
    (extractBotModuleFast_valid o (axiomSig qAx)).1
  cases isEnt with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hrest; subst hrest
    have hNotMod : ¬ Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      fun he => Bool.noConfusion ((decidesAxiomEntails_iff hsolve hchk).mpr he)
    exact ⟨fun _ he => hNotMod (hModEnt.mp he), fun hc => by cases hc⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hrest
    obtain ⟨justs, hjusts, rfl⟩ := hrest
    have hEntMod : Entails dm (extractBotModuleFast o (axiomSig qAx)).1 [qAx] :=
      (decidesAxiomEntails_iff hsolve hchk).mp rfl
    have hall := hstLoopPar_sound (P := fun x => Entails dm x [qAx])
      (fun hsub => entails_mono hsub) (fun {x b} hx => decidesAxiomEntails_iff hsolve hx)
      (dedupAxioms (extractBotModuleFast o (axiomSig qAx)).1) maxJusts numWorkers 8 hstFuel [[]] [] [] justs
      (fun _ hm => by cases hm) hjusts
    refine ⟨(fun hc => by cases hc), fun _ => ⟨hModEnt.mpr hEntMod, fun J hJ => ?_⟩⟩
    obtain ⟨hsubJ, hEJ, hminJ⟩ := hall J hJ
    exact ⟨fun a ha => hModSub a (dedupAxioms_mem_iff.mp (hsubJ a ha)), hEJ, hminJ⟩

def findAllUnsatJustificationsParReal (o : Ontology) (maxJusts : Nat := 5)
    (numWorkers : Nat := 8) (hstFuel : Nat := 128) : Option UnsatExplanation :=
  findAllUnsatJustificationsParWith decideRealOntology? o maxJusts numWorkers hstFuel

theorem findAllUnsatJustificationsParReal_sound {o : Ontology} {maxJusts numWorkers hstFuel : Nat}
    {res : UnsatExplanation} (h : findAllUnsatJustificationsParReal o maxJusts numWorkers hstFuel = some res) :
    (res.inconsistent = false → Satisfiable realDatatypeMap o) ∧
    (res.inconsistent = true →
      ¬ Satisfiable realDatatypeMap o ∧
      ∀ J ∈ res.justifications, IsMinimalUnsatJustification realDatatypeMap o J) :=
  findAllUnsatJustificationsParWith_sound decideRealOntology_iff h

def findAllJustificationsParReal (o : Ontology) (qAx : Axiom) (maxJusts : Nat := 5)
    (numWorkers : Nat := 8) (hstFuel : Nat := 128) : Option EntailmentExplanation :=
  findAllJustificationsParWith decideRealOntology? o qAx maxJusts numWorkers hstFuel

theorem findAllJustificationsParReal_sound {o : Ontology} {qAx : Axiom}
    {maxJusts numWorkers hstFuel : Nat} {res : EntailmentExplanation}
    (h : findAllJustificationsParReal o qAx maxJusts numWorkers hstFuel = some res) :
    (res.entailed = false → ¬ Entails realDatatypeMap o [qAx]) ∧
    (res.entailed = true →
      Entails realDatatypeMap o [qAx] ∧
      ∀ J ∈ res.justifications, IsMinimalJustification realDatatypeMap o qAx J) :=
  findAllJustificationsParWith_sound decideRealOntology_iff h

/-- Fast hybrid runtime inconsistency explainer (backed by `FastLocality` + parallel HST + `fastConsistencyCheck`). -/
def explainInconsistencyRuntime (o : Ontology) (maxJusts : Nat := 5) (numWorkers : Nat := 8) :
    Option UnsatExplanation :=
  if maxJusts ≤ 1 then
    findOneUnsatJustificationWith fastConsistencyCheck o
  else
    findAllUnsatJustificationsParWith fastConsistencyCheck o maxJusts numWorkers

/-- Fast hybrid runtime entailment explainer (backed by `FastLocality` + parallel HST + `fastConsistencyCheck`). -/
def explainEntailmentRuntime (o : Ontology) (qAx : Axiom) (maxJusts : Nat := 5)
    (numWorkers : Nat := 8) : Option EntailmentExplanation :=
  if maxJusts ≤ 1 then
    findOneJustificationWith fastConsistencyCheck o qAx
  else
    findAllJustificationsParWith fastConsistencyCheck o qAx maxJusts numWorkers

#print axioms findAllUnsatJustificationsParWith_workers_eq
#print axioms findAllJustificationsParWith_workers_eq
#print axioms findAllUnsatJustificationsParReal_sound
#print axioms findAllJustificationsParReal_sound

end Sabrina.OWL2.Justification
