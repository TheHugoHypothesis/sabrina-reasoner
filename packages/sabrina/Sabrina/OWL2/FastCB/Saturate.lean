import Std.Data.HashMap
import Std.Data.HashSet
import Sabrina.OWL2.FastEL
import Sabrina.OWL2.FastCB.Normalize

/-! # H.2: Horn-$\mathcal{SHI}$ Consequence-Based Saturator & Kernel-Verified Checker

Implements a fast integer-interned worklist saturator for Horn-$\mathcal{SHI}$
(conjunctions, existentials, universals, inverse roles, disjointness/bottom,
role hierarchies, reflexivity, and arbitrary-length role chains) paired with a
parallel linear-time kernel-verified derivation checker (`checkCBSound`):

1. **Certificate types (`RoleFact`, `SubFact`, `LinkFact`, `CBCert`)**:
   Every derived role inclusion `r ⊑* s`, context subsumption `⋀ H ⊑ c`, and
   existential context link `⋀ H ⊑ ∃r.(⋀ K)` records a compact rank-stratified
   justification.
2. **Parallel $O(|R| + |S| + |L|)$ verifier (`checkCBSound`)**:
   Uses `FastEL.allRangePar` across worker shards. Proved 100% sound by strong
   induction on derivation rank (`checkCBSound_holds`, `checkCBSound_entails_sub`,
   `checkCBSound_entails_unsat`).
3. **Fast worklist saturator (`saturateHornSHI`)**:
   Inverted trigger indices, batched universal strengthening on `exIntro` and
   `allProp`, incoming-link wakeups for `exElim`/`invAll`/`botLink`, bidirectional
   role-chain link composition, and configurable context caps so lower-bound
   saturation is always fast and bounded even on cyclic non-Horn ontologies.
4. **Verified entry point (`runFastCB`)**:
   Extracts Horn-$\mathcal{SHIQ}$ axioms, saturates, kernel-verifies the
   derivation certificate, and returns certified `(a, b)` named-class subsumptions
   and unsatisfiable named classes (`runFastCB_subs_sound`, `runFastCB_unsats_sound`).

Zero `sorry`, zero `admit`, strictly standard Lean 4 core axioms
(`[propext, Classical.choice, Quot.sound]`). -/

namespace Sabrina.OWL2.FastCB

open Sabrina.OWL2
open Sabrina.OWL2.FastEL

/-! ### 1. Derivation Certificate Types & Semantics -/

/-- Justification for a derived role inclusion `r ⊑* s`. -/
inductive RoleJust where
  | refl
  | ax (axIdx : Nat)
  | trans (f1 f2 : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A certified role inclusion `r ⊑* s` with index-stratified justification. -/
structure RoleFact where
  r : Nat
  s : Nat
  just : RoleJust
  deriving DecidableEq, Repr, Inhabited

/-- Justification for a derived context subsumption `⋀ contexts[h] ⊑ c`. -/
inductive SubJust where
  | inCtx (pos : Nat)
  | top
  | conj (axIdx : Nat) (prems : Array Nat)
  | exElim (axIdx linkIdx rfIdx subKIdx : Nat)
  | invAll (axIdx linkIdx rfIdx subKIdx : Nat)
  | botLink (linkIdx subKBotIdx : Nat)
  | reflAll (reflAxIdx rfIdx allAxIdx subAIdx : Nat)
  | parentMerge (maxAxIdx link1Idx rf1Idx subHBIdx subKAIdx link2Idx rf2Idx subK2BIdx subK2CIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A certified context subsumption `⋀ contexts[h] ⊑ c` with rank-stratified justification. -/
structure SubFact where
  h : Nat
  c : Nat
  rank : Nat
  just : SubJust
  deriving DecidableEq, Repr, Inhabited

/-- Justification for a derived existential context link `⋀ contexts[h] ⊑ ∃r.(⋀ contexts[k])`. -/
inductive LinkJust where
  | exIntro (axIdx subAIdx : Nat) (allPrems : Array (Nat × Nat × Nat))
  | allProp (prevLinkIdx : Nat) (allPrems : Array (Nat × Nat × Nat))
  | chainComp (axIdx link1Idx rf1Idx link2Idx rf2Idx : Nat)
  | reflLink (reflAxIdx rfIdx : Nat)
  | siblingMerge (maxAxIdx subAIdx link1Idx rf1Idx subK1BIdx link2Idx rf2Idx subK2BIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A certified existential context link `⋀ contexts[h] ⊑ ∃r.(⋀ contexts[k])`. -/
structure LinkFact where
  h : Nat
  r : Nat
  k : Nat
  rank : Nat
  just : LinkJust
  deriving DecidableEq, Repr, Inhabited

/-- Complete rank-stratified consequence-based derivation certificate. -/
structure CBCert where
  contexts : Array (Array Nat)
  roleFacts : Array RoleFact
  subFacts : Array SubFact
  linkFacts : Array LinkFact
  deriving Repr, Inhabited

/-- Semantics of a context `ctx : Array Nat` at domain element `x`: conjunction of all members. -/
def ctxHolds {dm : DatatypeMap} (t : CBTable) (i : Interpretation dm)
    (x : i.Object) (ctx : Array Nat) : Prop :=
  ∀ c ∈ ctx.toList, classHolds i x (t.exprOf c)

def RoleFact.holds {dm : DatatypeMap} (t : CBTable) (i : Interpretation dm) (rf : RoleFact) : Prop :=
  ∀ x y, rolePath i (t.roleOf rf.r) x y → rolePath i (t.roleOf rf.s) x y

def SubFact.holds {dm : DatatypeMap} (t : CBTable) (ctxs : Array (Array Nat))
    (i : Interpretation dm) (sf : SubFact) : Prop :=
  ∀ ctx, ctxs[sf.h]? = some ctx →
    ∀ x, ctxHolds t i x ctx → classHolds i x (t.exprOf sf.c)

def LinkFact.holds {dm : DatatypeMap} (t : CBTable) (ctxs : Array (Array Nat))
    (i : Interpretation dm) (lf : LinkFact) : Prop :=
  ∀ ctxH ctxK, ctxs[lf.h]? = some ctxH → ctxs[lf.k]? = some ctxK →
    ∀ x, ctxHolds t i x ctxH →
      ∃ y, rolePath i (t.roleOf lf.r) x y ∧ ctxHolds t i y ctxK

/-! ### 2. Linear-Time Kernel-Verified Certificate Checker -/

/-- Check a single role inclusion fact at index `idx` (transitive premises must have index `< idx`). -/
def checkRoleFact (norm : NormResult) (cert : CBCert) (idx : Nat) : Bool :=
  match cert.roleFacts[idx]? with
  | none => false
  | some rf =>
    match rf.just with
    | .refl => rf.r == rf.s
    | .ax axIdx =>
      match norm.axioms[axIdx]? with
      | some (.roleSub r s) => r == rf.r && s == rf.s
      | _ => false
    | .trans f1 f2 =>
      f1 < idx && f2 < idx &&
      match cert.roleFacts[f1]?, cert.roleFacts[f2]? with
      | some rf1, some rf2 => rf1.r == rf.r && rf1.s == rf2.r && rf2.s == rf.s
      | _, _ => false

/-- Check one batched universal premise `(allAxIdx, subAllAIdx, rfIdx)` for `(h, r, myRank)`:
    returns `some d` where `H ⊑ ∀r.d` is certified at rank `< myRank`. -/
def checkAllPrem (norm : NormResult) (cert : CBCert) (h r myRank : Nat)
    (prem : Nat × Nat × Nat) : Option Nat :=
  let (allAxIdx, subAllAIdx, rfIdx) := prem
  match norm.axioms[allAxIdx]?, cert.subFacts[subAllAIdx]?, cert.roleFacts[rfIdx]? with
  | some (.allR a s d), some sfA, some rf =>
    if sfA.h == h && sfA.c == a && sfA.rank < myRank && rf.r == r && rf.s == s then
      some d
    else none
  | _, _, _ => none

/-- Check that every element of `allPrems` is valid for `(h, r, myRank)`. -/
def checkAllPrems (norm : NormResult) (cert : CBCert) (h r myRank : Nat)
    (allPrems : Array (Nat × Nat × Nat)) : Bool :=
  allRangeSeq (fun j =>
    match allPrems[j]? with
    | some p => (checkAllPrem norm cert h r myRank p).isSome
    | none => false) 0 allPrems.size

/-- Check whether `c` is delivered by some universal premise in `allPrems`. -/
def deliveredByAllPrems (norm : NormResult) (cert : CBCert) (h r myRank : Nat)
    (allPrems : Array (Nat × Nat × Nat)) (c : Nat) : Bool :=
  allPrems.any fun p => checkAllPrem norm cert h r myRank p == some c

/-- Check a single `SubFact` at index `idx` (strictly rank-decreasing premises). -/
def checkSubFact (norm : NormResult) (cert : CBCert) (idx : Nat) : Bool :=
  match cert.subFacts[idx]? with
  | none => false
  | some sf =>
    match sf.just with
    | .inCtx pos =>
      match cert.contexts[sf.h]? with
      | some ctx => ctx[pos]? == some sf.c
      | none => false
    | .top => sf.c == 0
    | .conj axIdx prems =>
      match norm.axioms[axIdx]? with
      | some (.sub lhs rhs) =>
        rhs == sf.c && prems.size == lhs.size &&
        allRangeSeq (fun j =>
          match lhs[j]?, prems[j]? with
          | some a, some pIdx =>
            match cert.subFacts[pIdx]? with
            | some sfP => sfP.h == sf.h && sfP.c == a && sfP.rank < sf.rank
            | none => false
          | _, _ => false) 0 lhs.size
      | _ => false
    | .exElim axIdx linkIdx rfIdx subKIdx =>
      match norm.axioms[axIdx]?, cert.linkFacts[linkIdx]?, cert.roleFacts[rfIdx]?,
            cert.subFacts[subKIdx]? with
      | some (.existL s a b), some lf, some rf, some sfK =>
        b == sf.c && lf.h == sf.h && lf.rank < sf.rank &&
        rf.r == lf.r && rf.s == s &&
        sfK.h == lf.k && sfK.c == a && sfK.rank < sf.rank &&
        (cert.contexts[lf.k]?).isSome
      | _, _, _, _ => false
    | .invAll axIdx linkIdx rfIdx subKIdx =>
      match norm.axioms[axIdx]?, cert.linkFacts[linkIdx]?, cert.roleFacts[rfIdx]?,
            cert.subFacts[subKIdx]? with
      | some (.allR a sInv b), some lf, some rf, some sfK =>
        b == sf.c && lf.h == sf.h && lf.rank < sf.rank &&
        rf.r == lf.r && rf.s == invRole sInv &&
        sfK.h == lf.k && sfK.c == a && sfK.rank < sf.rank &&
        (cert.contexts[lf.k]?).isSome
      | _, _, _, _ => false
    | .botLink linkIdx subKBotIdx =>
      match cert.linkFacts[linkIdx]?, cert.subFacts[subKBotIdx]? with
      | some lf, some sfK =>
        sf.c == 1 && lf.h == sf.h && lf.rank < sf.rank &&
        sfK.h == lf.k && sfK.c == 1 && sfK.rank < sf.rank &&
        (cert.contexts[lf.k]?).isSome
      | _, _ => false
    | .reflAll reflAxIdx rfIdx allAxIdx subAIdx =>
      match norm.axioms[reflAxIdx]?, cert.roleFacts[rfIdx]?,
            norm.axioms[allAxIdx]?, cert.subFacts[subAIdx]? with
      | some (.roleRefl r0), some rf, some (.allR a s b), some sfA =>
        b == sf.c && rf.r == r0 && rf.s == s &&
        sfA.h == sf.h && sfA.c == a && sfA.rank < sf.rank
      | _, _, _, _ => false
    | .parentMerge maxAxIdx link1Idx rf1Idx subHBIdx subKAIdx link2Idx rf2Idx subK2BIdx subK2CIdx =>
      match norm.axioms[maxAxIdx]?, cert.linkFacts[link1Idx]?, cert.roleFacts[rf1Idx]?,
            cert.subFacts[subHBIdx]?, cert.subFacts[subKAIdx]?,
            cert.linkFacts[link2Idx]?, cert.roleFacts[rf2Idx]?,
            cert.subFacts[subK2BIdx]?, cert.subFacts[subK2CIdx]? with
      | some (.maxOne a s b), some l1, some rf1, some sfHB, some sfKA,
        some l2, some rf2, some sfK2B, some sfK2C =>
        l1.h == sf.h && l1.rank < sf.rank &&
        rf1.r == l1.r && rf1.s == invRole s &&
        sfHB.h == sf.h && sfHB.c == b && sfHB.rank < sf.rank &&
        sfKA.h == l1.k && sfKA.c == a && sfKA.rank < sf.rank &&
        l2.h == l1.k && l2.rank < sf.rank &&
        rf2.r == l2.r && rf2.s == s &&
        sfK2B.h == l2.k && sfK2B.c == b && sfK2B.rank < sf.rank &&
        sfK2C.h == l2.k && sfK2C.c == sf.c && sfK2C.rank < sf.rank &&
        (cert.contexts[l1.k]?).isSome && (cert.contexts[l2.k]?).isSome
      | _, _, _, _, _, _, _, _, _ => false

/-- Check a single `LinkFact` at index `idx` (strictly rank-decreasing premises). -/
def checkLinkFact (norm : NormResult) (cert : CBCert) (idx : Nat) : Bool :=
  match cert.linkFacts[idx]? with
  | none => false
  | some lf =>
    match cert.contexts[lf.k]? with
    | none => false
    | some ctxK =>
      match lf.just with
      | .exIntro axIdx subAIdx allPrems =>
        match norm.axioms[axIdx]?, cert.subFacts[subAIdx]? with
        | some (.existR a r b), some sfA =>
          r == lf.r && sfA.h == lf.h && sfA.c == a && sfA.rank < lf.rank &&
          checkAllPrems norm cert lf.h lf.r lf.rank allPrems &&
          ctxK.all fun c => c == b || deliveredByAllPrems norm cert lf.h lf.r lf.rank allPrems c
        | _, _ => false
      | .allProp prevLinkIdx allPrems =>
        match cert.linkFacts[prevLinkIdx]? with
        | some prevLf =>
          match cert.contexts[prevLf.k]? with
          | none => false
          | some ctxK0 =>
            prevLf.h == lf.h && prevLf.r == lf.r && prevLf.rank < lf.rank &&
            checkAllPrems norm cert lf.h lf.r lf.rank allPrems &&
            ctxK.all fun c =>
              ctxK0.contains c || deliveredByAllPrems norm cert lf.h lf.r lf.rank allPrems c
        | none => false
      | .chainComp axIdx link1Idx rf1Idx link2Idx rf2Idx =>
        match norm.axioms[axIdx]?, cert.linkFacts[link1Idx]?, cert.roleFacts[rf1Idx]?,
              cert.linkFacts[link2Idx]?, cert.roleFacts[rf2Idx]? with
        | some (.roleChain s1 s2 s), some l1, some rf1, some l2, some rf2 =>
          s == lf.r && l1.h == lf.h && l1.rank < lf.rank &&
          rf1.r == l1.r && rf1.s == s1 &&
          l2.h == l1.k && l2.k == lf.k && l2.rank < lf.rank &&
          rf2.r == l2.r && rf2.s == s2 &&
          (cert.contexts[l1.k]?).isSome
        | _, _, _, _, _ => false
      | .reflLink reflAxIdx rfIdx =>
        match norm.axioms[reflAxIdx]?, cert.roleFacts[rfIdx]? with
        | some (.roleRefl r0), some rf =>
          lf.k == lf.h && rf.r == r0 && rf.s == lf.r
        | _, _ => false
      | .siblingMerge maxAxIdx subAIdx link1Idx rf1Idx subK1BIdx link2Idx rf2Idx subK2BIdx =>
        match norm.axioms[maxAxIdx]?, cert.subFacts[subAIdx]?,
              cert.linkFacts[link1Idx]?, cert.roleFacts[rf1Idx]?, cert.subFacts[subK1BIdx]?,
              cert.linkFacts[link2Idx]?, cert.roleFacts[rf2Idx]?, cert.subFacts[subK2BIdx]? with
        | some (.maxOne a s b), some sfA, some l1, some rf1, some sfK1B,
          some l2, some rf2, some sfK2B =>
          match cert.contexts[l1.k]?, cert.contexts[l2.k]? with
          | some ctxK1, some ctxK2 =>
            sfA.h == lf.h && sfA.c == a && sfA.rank < lf.rank &&
            l1.h == lf.h && l1.r == lf.r && l1.rank < lf.rank &&
            rf1.r == l1.r && rf1.s == s &&
            sfK1B.h == l1.k && sfK1B.c == b && sfK1B.rank < lf.rank &&
            l2.h == lf.h && l2.rank < lf.rank &&
            rf2.r == l2.r && rf2.s == s &&
            sfK2B.h == l2.k && sfK2B.c == b && sfK2B.rank < lf.rank &&
            ctxK.all fun c => ctxK1.contains c || ctxK2.contains c
          | _, _ => false
        | _, _, _, _, _, _, _, _ => false

/-- Parallel linear-time soundness verifier for a consequence-based derivation certificate. -/
def checkCBSound (norm : NormResult) (cert : CBCert) (numWorkers : Nat := 8) : Bool :=
  allRangePar cert.roleFacts.size (checkRoleFact norm cert) numWorkers &&
  allRangePar cert.subFacts.size (checkSubFact norm cert) numWorkers &&
  allRangePar cert.linkFacts.size (checkLinkFact norm cert) numWorkers

/-! ### 3. Kernel Soundness Proofs for `checkCBSound` -/

private theorem mem_toList_of_getElem? {α : Type} {xs : Array α} {idx : Nat} {v : α}
    (h : xs[idx]? = some v) : v ∈ xs.toList := by
  have hlt : idx < xs.size := by
    apply Classical.byContradiction; intro hge
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at h; cases h
  rw [Array.getElem?_eq_getElem hlt] at h
  cases h
  exact Array.getElem_mem_toList hlt

private theorem array_all_iff {α : Type} {xs : Array α} {p : α → Bool} :
    xs.all p = true ↔ ∀ x ∈ xs.toList, p x = true := by
  rw [← Array.all_toList, List.all_eq_true]

private theorem array_any_iff {α : Type} {xs : Array α} {p : α → Bool} :
    xs.any p = true ↔ ∃ x ∈ xs.toList, p x = true := by
  rw [← Array.any_toList, List.any_eq_true]

private theorem array_contains_iff {α : Type} [BEq α] [LawfulBEq α] {xs : Array α} {a : α} :
    xs.contains a = true ↔ a ∈ xs.toList := by
  rw [Array.contains_iff_mem, Array.mem_def]

private theorem checkRoleFacts_sound {dm : DatatypeMap} {norm : NormResult} {cert : CBCert}
    {i : Interpretation dm}
    (hax : ∀ ax ∈ norm.axioms.toList, ax.holds norm.table i)
    (hall : ∀ idx, idx < cert.roleFacts.size → checkRoleFact norm cert idx = true) :
    ∀ (idx : Nat) (rf : RoleFact), cert.roleFacts[idx]? = some rf → rf.holds norm.table i := by
  intro idx
  induction idx using Nat.strongRecOn with
  | ind idx ih =>
    intro rf hrf
    have hlt : idx < cert.roleFacts.size := by
      apply Classical.byContradiction; intro hge
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hrf; cases hrf
    have hchk := hall idx hlt
    unfold checkRoleFact at hchk
    rw [hrf] at hchk
    cases hj : rf.just with
    | refl =>
      simp only [hj, beq_iff_eq] at hchk
      intro x y hxy; rw [← hchk]; exact hxy
    | ax axIdx =>
      simp only [hj] at hchk
      cases hget : norm.axioms[axIdx]? with
      | none => rw [hget] at hchk; cases hchk
      | some ax =>
        rw [hget] at hchk
        cases ax with
        | roleSub r s =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hchk
          obtain ⟨hr, hs⟩ := hchk
          have hh := hax (.roleSub r s) (mem_toList_of_getElem? hget)
          rw [hr, hs] at hh
          exact hh
        | _ => cases hchk
    | trans f1 f2 =>
      simp only [hj, Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨hf1, hf2⟩, hrest⟩ := hchk
      cases h1 : cert.roleFacts[f1]? with
      | none => rw [h1] at hrest; cases hrest
      | some rf1 =>
        cases h2 : cert.roleFacts[f2]? with
        | none => rw [h1, h2] at hrest; cases hrest
        | some rf2 =>
          rw [h1, h2] at hrest
          simp only [Bool.and_eq_true, beq_iff_eq] at hrest
          obtain ⟨⟨he1, he2⟩, he3⟩ := hrest
          have hh1 := ih f1 hf1 rf1 h1
          have hh2 := ih f2 hf2 rf2 h2
          intro x y hxy
          rw [← he1] at hxy
          rw [← he3]
          exact hh2 x y (he2 ▸ hh1 x y hxy)

private theorem deliveredByAllPrems_sound {dm : DatatypeMap} {norm : NormResult} {cert : CBCert}
    {i : Interpretation dm}
    (hax : ∀ ax ∈ norm.axioms.toList, ax.holds norm.table i)
    (hroles : ∀ (idx : Nat) (rf : RoleFact), cert.roleFacts[idx]? = some rf → rf.holds norm.table i)
    {h r myRank : Nat} {allPrems : Array (Nat × Nat × Nat)} {ctxH : Array Nat}
    (hctxH : cert.contexts[h]? = some ctxH)
    (hsubIH : ∀ (idx : Nat) (sf : SubFact), cert.subFacts[idx]? = some sf → sf.rank < myRank →
      sf.holds norm.table cert.contexts i)
    {x y : i.Object} (hx : ctxHolds norm.table i x ctxH) (hry : rolePath i (norm.table.roleOf r) x y)
    {c : Nat} (hdel : deliveredByAllPrems norm cert h r myRank allPrems c = true) :
    classHolds i y (norm.table.exprOf c) := by
  unfold deliveredByAllPrems at hdel
  obtain ⟨⟨allAxIdx, subAllAIdx, rfIdx⟩, _, hp⟩ := array_any_iff.mp hdel
  rw [beq_iff_eq] at hp
  unfold checkAllPrem at hp
  dsimp only at hp
  cases hgetAx : norm.axioms[allAxIdx]? with
  | none => simp [hgetAx] at hp
  | some ax =>
    cases hgetSf : cert.subFacts[subAllAIdx]? with
    | none => simp [hgetAx, hgetSf] at hp
    | some sfA =>
      cases hgetRf : cert.roleFacts[rfIdx]? with
      | none => simp [hgetAx, hgetSf, hgetRf] at hp
      | some rf =>
        simp only [hgetAx, hgetSf, hgetRf] at hp
        cases ax with
        | allR a s d =>
          dsimp only at hp
          split at hp
          · rename_i hc
            have hdc : d = c := Option.some.inj hp
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨⟨⟨hhA, hcA⟩, hrA⟩, hrr⟩, hrs⟩ := hc
            have haxH := hax (.allR a s d) (mem_toList_of_getElem? hgetAx)
            have hsfH := hsubIH subAllAIdx sfA hgetSf hrA ctxH (hhA.symm ▸ hctxH) x hx
            rw [hcA] at hsfH
            have hrfH := hroles rfIdx rf hgetRf x y (hrr.symm ▸ hry)
            rw [hrs] at hrfH
            rw [← hdc]
            exact haxH x hsfH y hrfH
          · cases hp
        | _ => cases hp

/-- Mutual rank-stratified soundness of all `SubFact`s and `LinkFact`s in a verified `CBCert`. -/
theorem checkCBSound_holds {dm : DatatypeMap} {norm : NormResult} {cert : CBCert}
    {numWorkers : Nat} {i : Interpretation dm}
    (hwf : norm.table.WF)
    (hax : ∀ ax ∈ norm.axioms.toList, ax.holds norm.table i)
    (hcheck : checkCBSound norm cert numWorkers = true) :
    (∀ (idx : Nat) (rf : RoleFact), cert.roleFacts[idx]? = some rf → rf.holds norm.table i) ∧
    (∀ (idx : Nat) (sf : SubFact), cert.subFacts[idx]? = some sf → sf.holds norm.table cert.contexts i) ∧
    (∀ (idx : Nat) (lf : LinkFact), cert.linkFacts[idx]? = some lf → lf.holds norm.table cert.contexts i) := by
  unfold checkCBSound at hcheck
  simp only [Bool.and_eq_true, allRangePar_iff] at hcheck
  obtain ⟨⟨hRoleAll, hSubAll⟩, hLinkAll⟩ := hcheck
  have hroles := checkRoleFacts_sound hax hRoleAll
  have hmut : ∀ (rk : Nat),
      (∀ (idx : Nat) (sf : SubFact), cert.subFacts[idx]? = some sf → sf.rank = rk →
        sf.holds norm.table cert.contexts i) ∧
      (∀ (idx : Nat) (lf : LinkFact), cert.linkFacts[idx]? = some lf → lf.rank = rk →
        lf.holds norm.table cert.contexts i) := by
    intro rk
    induction rk using Nat.strongRecOn with
    | ind rk ih =>
      have hsubLT : ∀ (idx : Nat) (sf : SubFact), cert.subFacts[idx]? = some sf → sf.rank < rk →
          sf.holds norm.table cert.contexts i :=
        fun idx sf hsf hlt => (ih sf.rank hlt).1 idx sf hsf rfl
      have hlinkLT : ∀ (idx : Nat) (lf : LinkFact), cert.linkFacts[idx]? = some lf → lf.rank < rk →
          lf.holds norm.table cert.contexts i :=
        fun idx lf hlf hlt => (ih lf.rank hlt).2 idx lf hlf rfl
      constructor
      · -- SubFact case
        intro idx sf hsf hrk ctxH hctxH x hx
        have hlt : idx < cert.subFacts.size := by
          apply Classical.byContradiction; intro hge
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hsf; cases hsf
        have hchk := hSubAll idx hlt
        unfold checkSubFact at hchk
        rw [hsf] at hchk
        cases hj : sf.just with
        | inCtx pos =>
          simp only [hj, hctxH, beq_iff_eq] at hchk
          exact hx sf.c (mem_toList_of_getElem? hchk)
        | top =>
          simp only [hj, beq_iff_eq] at hchk
          rw [hchk, CBTable.exprOf_zero hwf]
          exact i.thingExt x
        | conj axIdx prems =>
          simp only [hj] at hchk
          cases hgetAx : norm.axioms[axIdx]? with
          | none => rw [hgetAx] at hchk; cases hchk
          | some ax =>
            rw [hgetAx] at hchk
            cases ax with
            | sub lhs rhs =>
              simp only [Bool.and_eq_true, beq_iff_eq, allRangeSeq_iff] at hchk
              obtain ⟨⟨hrhs, hsz⟩, hprems⟩ := hchk
              have haxH := hax (.sub lhs rhs) (mem_toList_of_getElem? hgetAx)
              rw [← hrhs]
              apply haxH x
              intro c hc
              obtain ⟨j, hjlt, rfl⟩ := List.getElem_of_mem hc
              have hjlt' : j < lhs.size := by simpa using hjlt
              have hpj := hprems j (Nat.zero_le _) hjlt'
              have hlj : lhs[j]? = some lhs[j] := Array.getElem?_eq_getElem hjlt'
              have hjltP : j < prems.size := hsz.symm ▸ hjlt'
              have hpIdx : prems[j]? = some prems[j] := Array.getElem?_eq_getElem hjltP
              simp only [hlj, hpIdx] at hpj
              cases hgetP : cert.subFacts[prems[j]]? with
              | none => simp [hgetP] at hpj
              | some sfP =>
                simp only [hgetP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpj
                obtain ⟨⟨hhP, hcP⟩, hrP⟩ := hpj
                have hhold := hsubLT prems[j] sfP hgetP (hrk ▸ hrP) ctxH (hhP.symm ▸ hctxH) x hx
                rw [hcP] at hhold
                exact hhold
            | _ => cases hchk
        | exElim axIdx linkIdx rfIdx subKIdx =>
          simp only [hj] at hchk
          cases hgetAx : norm.axioms[axIdx]? with
          | none => simp [hgetAx] at hchk
          | some ax =>
            cases hgetL : cert.linkFacts[linkIdx]? with
            | none => simp [hgetAx, hgetL] at hchk
            | some lf =>
              cases hgetRf : cert.roleFacts[rfIdx]? with
              | none => simp [hgetAx, hgetL, hgetRf] at hchk
              | some rf =>
                cases hgetSk : cert.subFacts[subKIdx]? with
                | none => simp [hgetAx, hgetL, hgetRf, hgetSk] at hchk
                | some sfK =>
                  simp only [hgetAx, hgetL, hgetRf, hgetSk] at hchk
                  cases ax with
                  | existL s a b =>
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                      Option.isSome_iff_exists] at hchk
                    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb, hhl⟩, hrl⟩, hrr⟩, hrs⟩, hhk⟩, hca⟩, hrkK⟩, ⟨ctxK, hctxK⟩⟩ := hchk
                    have haxH := hax (.existL s a b) (mem_toList_of_getElem? hgetAx)
                    obtain ⟨y, hry, hyK⟩ :=
                      hlinkLT linkIdx lf hgetL (hrk ▸ hrl) ctxH ctxK (hhl.symm ▸ hctxH) hctxK x hx
                    have hsy := hroles rfIdx rf hgetRf x y (hrr.symm ▸ hry)
                    rw [hrs] at hsy
                    have hya := hsubLT subKIdx sfK hgetSk (hrk ▸ hrkK) ctxK (hhk.symm ▸ hctxK) y hyK
                    rw [hca] at hya
                    rw [← hb]
                    exact haxH x y hsy hya
                  | _ => cases hchk
        | invAll axIdx linkIdx rfIdx subKIdx =>
          simp only [hj] at hchk
          cases hgetAx : norm.axioms[axIdx]? with
          | none => simp [hgetAx] at hchk
          | some ax =>
            cases hgetL : cert.linkFacts[linkIdx]? with
            | none => simp [hgetAx, hgetL] at hchk
            | some lf =>
              cases hgetRf : cert.roleFacts[rfIdx]? with
              | none => simp [hgetAx, hgetL, hgetRf] at hchk
              | some rf =>
                cases hgetSk : cert.subFacts[subKIdx]? with
                | none => simp [hgetAx, hgetL, hgetRf, hgetSk] at hchk
                | some sfK =>
                  simp only [hgetAx, hgetL, hgetRf, hgetSk] at hchk
                  cases ax with
                  | allR a sInv b =>
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                      Option.isSome_iff_exists] at hchk
                    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb, hhl⟩, hrl⟩, hrr⟩, hrs⟩, hhk⟩, hca⟩, hrkK⟩, ⟨ctxK, hctxK⟩⟩ := hchk
                    have haxH := hax (.allR a sInv b) (mem_toList_of_getElem? hgetAx)
                    obtain ⟨y, hry, hyK⟩ :=
                      hlinkLT linkIdx lf hgetL (hrk ▸ hrl) ctxH ctxK (hhl.symm ▸ hctxH) hctxK x hx
                    have hinv := hroles rfIdx rf hgetRf x y (hrr.symm ▸ hry)
                    rw [hrs, CBTable.roleOf_invRole hwf i sInv x y] at hinv
                    have hya := hsubLT subKIdx sfK hgetSk (hrk ▸ hrkK) ctxK (hhk.symm ▸ hctxK) y hyK
                    rw [hca] at hya
                    rw [← hb]
                    exact haxH y hya x hinv
                  | _ => cases hchk
        | botLink linkIdx subKBotIdx =>
          simp only [hj] at hchk
          cases hgetL : cert.linkFacts[linkIdx]? with
          | none => simp [hgetL] at hchk
          | some lf =>
            cases hgetSk : cert.subFacts[subKBotIdx]? with
            | none => simp [hgetL, hgetSk] at hchk
            | some sfK =>
              simp only [hgetL, hgetSk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                Option.isSome_iff_exists] at hchk
              obtain ⟨⟨⟨⟨⟨⟨hc1, hhl⟩, hrl⟩, hhk⟩, hk1⟩, hrkK⟩, ⟨ctxK, hctxK⟩⟩ := hchk
              obtain ⟨y, _, hyK⟩ :=
                hlinkLT linkIdx lf hgetL (hrk ▸ hrl) ctxH ctxK (hhl.symm ▸ hctxH) hctxK x hx
              have hyBot := hsubLT subKBotIdx sfK hgetSk (hrk ▸ hrkK) ctxK (hhk.symm ▸ hctxK) y hyK
              rw [hk1, CBTable.exprOf_one hwf] at hyBot
              exact absurd hyBot (i.nothingExt y)
        | reflAll reflAxIdx rfIdx allAxIdx subAIdx =>
          simp only [hj] at hchk
          cases hgetR : norm.axioms[reflAxIdx]? with
          | none => simp [hgetR] at hchk
          | some axR =>
            cases hgetRf : cert.roleFacts[rfIdx]? with
            | none => simp [hgetR, hgetRf] at hchk
            | some rf =>
              cases hgetA : norm.axioms[allAxIdx]? with
              | none => simp [hgetR, hgetRf, hgetA] at hchk
              | some axA =>
                cases hgetSf : cert.subFacts[subAIdx]? with
                | none => simp [hgetR, hgetRf, hgetA, hgetSf] at hchk
                | some sfA =>
                  simp only [hgetR, hgetRf, hgetA, hgetSf] at hchk
                  cases axR with
                  | roleRefl r0 =>
                    cases axA with
                    | allR a s b =>
                      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
                      obtain ⟨⟨⟨⟨⟨hb, hrr⟩, hrs⟩, hha⟩, hca⟩, hrA⟩ := hchk
                      have hrefl := hax (.roleRefl r0) (mem_toList_of_getElem? hgetR) x
                      have hsxx := hroles rfIdx rf hgetRf x x (hrr.symm ▸ hrefl)
                      rw [hrs] at hsxx
                      have hxa := hsubLT subAIdx sfA hgetSf (hrk ▸ hrA) ctxH (hha.symm ▸ hctxH) x hx
                      rw [hca] at hxa
                      have hallA := hax (.allR a s b) (mem_toList_of_getElem? hgetA)
                      rw [← hb]
                      exact hallA x hxa x hsxx
                    | _ => cases hchk
                  | _ => cases hchk
        | parentMerge maxAxIdx link1Idx rf1Idx subHBIdx subKAIdx link2Idx rf2Idx subK2BIdx subK2CIdx =>
          simp only [hj] at hchk
          cases hgetM : norm.axioms[maxAxIdx]? with
          | none => simp [hgetM] at hchk
          | some axM =>
            cases hgetL1 : cert.linkFacts[link1Idx]? with
            | none => simp [hgetM, hgetL1] at hchk
            | some l1 =>
              cases hgetRf1 : cert.roleFacts[rf1Idx]? with
              | none => simp [hgetM, hgetL1, hgetRf1] at hchk
              | some rf1 =>
                cases hgetHB : cert.subFacts[subHBIdx]? with
                | none => simp [hgetM, hgetL1, hgetRf1, hgetHB] at hchk
                | some sfHB =>
                  cases hgetKA : cert.subFacts[subKAIdx]? with
                  | none => simp [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA] at hchk
                  | some sfKA =>
                    cases hgetL2 : cert.linkFacts[link2Idx]? with
                    | none => simp [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA, hgetL2] at hchk
                    | some l2 =>
                      cases hgetRf2 : cert.roleFacts[rf2Idx]? with
                      | none => simp [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA, hgetL2, hgetRf2] at hchk
                      | some rf2 =>
                        cases hgetK2B : cert.subFacts[subK2BIdx]? with
                        | none => simp [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA, hgetL2, hgetRf2, hgetK2B] at hchk
                        | some sfK2B =>
                          cases hgetK2C : cert.subFacts[subK2CIdx]? with
                          | none => simp [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA, hgetL2, hgetRf2, hgetK2B, hgetK2C] at hchk
                          | some sfK2C =>
                            simp only [hgetM, hgetL1, hgetRf1, hgetHB, hgetKA, hgetL2, hgetRf2, hgetK2B, hgetK2C] at hchk
                            cases axM with
                            | maxOne a s b =>
                              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                                Option.isSome_iff_exists, and_assoc] at hchk
                              obtain ⟨hl1h, hl1r, hrf1r, hrf1s, hhbH, hhbC, hhbR,
                                hkaH, hkaC, hkaR, hl2h, hl2r, hrf2r, hrf2s,
                                hk2bH, hk2bC, hk2bR, hk2cH, hk2cC, hk2cR,
                                ⟨ctxK1, hctxK1⟩, ⟨ctxK2, hctxK2⟩⟩ := hchk
                              obtain ⟨y, hr1y, hyK1⟩ :=
                                hlinkLT link1Idx l1 hgetL1 (hrk ▸ hl1r) ctxH ctxK1 (hl1h.symm ▸ hctxH) hctxK1 x hx
                              have hsyx := hroles rf1Idx rf1 hgetRf1 x y (hrf1r.symm ▸ hr1y)
                              rw [hrf1s, CBTable.roleOf_invRole hwf i s x y] at hsyx
                              have hxb := hsubLT subHBIdx sfHB hgetHB (hrk ▸ hhbR) ctxH (hhbH.symm ▸ hctxH) x hx
                              rw [hhbC] at hxb
                              have hya := hsubLT subKAIdx sfKA hgetKA (hrk ▸ hkaR) ctxK1 (hkaH.symm ▸ hctxK1) y hyK1
                              rw [hkaC] at hya
                              obtain ⟨z, hr2z, hzK2⟩ :=
                                hlinkLT link2Idx l2 hgetL2 (hrk ▸ hl2r) ctxK1 ctxK2 (hl2h.symm ▸ hctxK1) hctxK2 y hyK1
                              have hsyz := hroles rf2Idx rf2 hgetRf2 y z (hrf2r.symm ▸ hr2z)
                              rw [hrf2s] at hsyz
                              have hzb := hsubLT subK2BIdx sfK2B hgetK2B (hrk ▸ hk2bR) ctxK2 (hk2bH.symm ▸ hctxK2) z hzK2
                              rw [hk2bC] at hzb
                              have hzc := hsubLT subK2CIdx sfK2C hgetK2C (hrk ▸ hk2cR) ctxK2 (hk2cH.symm ▸ hctxK2) z hzK2
                              rw [hk2cC] at hzc
                              have hmax := hax (.maxOne a s b) (mem_toList_of_getElem? hgetM)
                              have hxz : x = z := hmax y hya x z hsyx hxb hsyz hzb
                              exact hxz ▸ hzc
                            | _ => cases hchk
      · -- LinkFact case
        intro idx lf hlf hrk ctxH ctxK hctxH hctxK x hx
        have hlt : idx < cert.linkFacts.size := by
          apply Classical.byContradiction; intro hge
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hlf; cases hlf
        have hchk := hLinkAll idx hlt
        unfold checkLinkFact at hchk
        simp only [hlf, hctxK] at hchk
        cases hj : lf.just with
        | exIntro axIdx subAIdx allPrems =>
          simp only [hj] at hchk
          cases hgetAx : norm.axioms[axIdx]? with
          | none => simp [hgetAx] at hchk
          | some ax =>
            cases hgetSf : cert.subFacts[subAIdx]? with
            | none => simp [hgetAx, hgetSf] at hchk
            | some sfA =>
              simp only [hgetAx, hgetSf] at hchk
              cases ax with
              | existR a r b =>
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
                obtain ⟨⟨⟨⟨⟨hr, hha⟩, hca⟩, hrA⟩, _⟩, hmemAll⟩ := hchk
                have hxa := hsubLT subAIdx sfA hgetSf (hrk ▸ hrA) ctxH (hha.symm ▸ hctxH) x hx
                rw [hca] at hxa
                have haxH := hax (.existR a r b) (mem_toList_of_getElem? hgetAx)
                obtain ⟨y, hry, hyb⟩ := haxH x hxa
                rw [hr] at hry
                refine ⟨y, hry, fun c hc => ?_⟩
                have hcov := array_all_iff.mp hmemAll c hc
                simp only [Bool.or_eq_true, beq_iff_eq] at hcov
                rcases hcov with rfl | hdel
                · exact hyb
                · exact deliveredByAllPrems_sound hax hroles hctxH
                    (fun i' s' hs' hlt' => hsubLT i' s' hs' (hrk ▸ hlt')) hx hry hdel
              | _ => cases hchk
        | allProp prevLinkIdx allPrems =>
          simp only [hj] at hchk
          cases hgetPrev : cert.linkFacts[prevLinkIdx]? with
          | none => simp [hgetPrev] at hchk
          | some prevLf =>
            simp only [hgetPrev] at hchk
            cases hctx0 : cert.contexts[prevLf.k]? with
            | none => simp [hctx0] at hchk
            | some ctxK0 =>
              simp only [hctx0, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
              obtain ⟨⟨⟨⟨hhl, hrl⟩, hrkP⟩, _⟩, hmemAll⟩ := hchk
              obtain ⟨y, hry, hyK0⟩ :=
                hlinkLT prevLinkIdx prevLf hgetPrev (hrk ▸ hrkP) ctxH ctxK0 (hhl.symm ▸ hctxH) hctx0 x hx
              rw [hrl] at hry
              refine ⟨y, hry, fun c hc => ?_⟩
              have hcov := array_all_iff.mp hmemAll c hc
              simp only [Bool.or_eq_true] at hcov
              rcases hcov with hinc | hdel
              · exact hyK0 c (array_contains_iff.mp hinc)
              · exact deliveredByAllPrems_sound hax hroles hctxH
                  (fun i' s' hs' hlt' => hsubLT i' s' hs' (hrk ▸ hlt')) hx hry hdel
        | chainComp axIdx link1Idx rf1Idx link2Idx rf2Idx =>
          simp only [hj] at hchk
          cases hgetAx : norm.axioms[axIdx]? with
          | none => simp [hgetAx] at hchk
          | some ax =>
            cases hgetL1 : cert.linkFacts[link1Idx]? with
            | none => simp [hgetAx, hgetL1] at hchk
            | some l1 =>
              cases hgetRf1 : cert.roleFacts[rf1Idx]? with
              | none => simp [hgetAx, hgetL1, hgetRf1] at hchk
              | some rf1 =>
                cases hgetL2 : cert.linkFacts[link2Idx]? with
                | none => simp [hgetAx, hgetL1, hgetRf1, hgetL2] at hchk
                | some l2 =>
                  cases hgetRf2 : cert.roleFacts[rf2Idx]? with
                  | none => simp [hgetAx, hgetL1, hgetRf1, hgetL2, hgetRf2] at hchk
                  | some rf2 =>
                    simp only [hgetAx, hgetL1, hgetRf1, hgetL2, hgetRf2] at hchk
                    cases ax with
                    | roleChain s1 s2 s =>
                      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                        Option.isSome_iff_exists] at hchk
                      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hl1h⟩, hr1⟩, hrf1r⟩, hrf1s⟩, hl2h⟩, hl2k⟩, hr2⟩, hrf2r⟩, hrf2s⟩,
                        ⟨ctxK1, hctxK1⟩⟩ := hchk
                      obtain ⟨y, hr1y, hyK1⟩ :=
                        hlinkLT link1Idx l1 hgetL1 (hrk ▸ hr1) ctxH ctxK1 (hl1h.symm ▸ hctxH) hctxK1 x hx
                      obtain ⟨z, hr2z, hzK2⟩ :=
                        hlinkLT link2Idx l2 hgetL2 (hrk ▸ hr2) ctxK1 ctxK (hl2h.symm ▸ hctxK1) (hl2k.symm ▸ hctxK) y hyK1
                      have hs1y := hroles rf1Idx rf1 hgetRf1 x y (hrf1r.symm ▸ hr1y)
                      rw [hrf1s] at hs1y
                      have hs2z := hroles rf2Idx rf2 hgetRf2 y z (hrf2r.symm ▸ hr2z)
                      rw [hrf2s] at hs2z
                      have haxH := hax (.roleChain s1 s2 s) (mem_toList_of_getElem? hgetAx)
                      exact ⟨z, hs ▸ haxH x y z hs1y hs2z, hzK2⟩
                    | _ => cases hchk
        | reflLink reflAxIdx rfIdx =>
          simp only [hj] at hchk
          cases hgetR : norm.axioms[reflAxIdx]? with
          | none => simp [hgetR] at hchk
          | some axR =>
            cases hgetRf : cert.roleFacts[rfIdx]? with
            | none => simp [hgetR, hgetRf] at hchk
            | some rf =>
              simp only [hgetR, hgetRf] at hchk
              cases axR with
              | roleRefl r0 =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hchk
                obtain ⟨⟨hk, hrr⟩, hrs⟩ := hchk
                have hrefl := hax (.roleRefl r0) (mem_toList_of_getElem? hgetR) x
                have hrx := hroles rfIdx rf hgetRf x x (hrr.symm ▸ hrefl)
                rw [hrs] at hrx
                have heqCtx : ctxK = ctxH := by
                  rw [hk] at hctxK; rw [hctxK] at hctxH; exact Option.some.inj hctxH
                exact ⟨x, hrx, heqCtx ▸ hx⟩
              | _ => cases hchk
        | siblingMerge maxAxIdx subAIdx link1Idx rf1Idx subK1BIdx link2Idx rf2Idx subK2BIdx =>
          simp only [hj] at hchk
          cases hgetM : norm.axioms[maxAxIdx]? with
          | none => simp [hgetM] at hchk
          | some axM =>
            cases hgetA : cert.subFacts[subAIdx]? with
            | none => simp [hgetM, hgetA] at hchk
            | some sfA =>
              cases hgetL1 : cert.linkFacts[link1Idx]? with
              | none => simp [hgetM, hgetA, hgetL1] at hchk
              | some l1 =>
                cases hgetRf1 : cert.roleFacts[rf1Idx]? with
                | none => simp [hgetM, hgetA, hgetL1, hgetRf1] at hchk
                | some rf1 =>
                  cases hgetK1B : cert.subFacts[subK1BIdx]? with
                  | none => simp [hgetM, hgetA, hgetL1, hgetRf1, hgetK1B] at hchk
                  | some sfK1B =>
                    cases hgetL2 : cert.linkFacts[link2Idx]? with
                    | none => simp [hgetM, hgetA, hgetL1, hgetRf1, hgetK1B, hgetL2] at hchk
                    | some l2 =>
                      cases hgetRf2 : cert.roleFacts[rf2Idx]? with
                      | none => simp [hgetM, hgetA, hgetL1, hgetRf1, hgetK1B, hgetL2, hgetRf2] at hchk
                      | some rf2 =>
                        cases hgetK2B : cert.subFacts[subK2BIdx]? with
                        | none => simp [hgetM, hgetA, hgetL1, hgetRf1, hgetK1B, hgetL2, hgetRf2, hgetK2B] at hchk
                        | some sfK2B =>
                          simp only [hgetM, hgetA, hgetL1, hgetRf1, hgetK1B, hgetL2, hgetRf2, hgetK2B] at hchk
                          cases axM with
                          | maxOne a s b =>
                            cases hctx1 : cert.contexts[l1.k]? with
                            | none => simp [hctx1] at hchk
                            | some ctxK1 =>
                              cases hctx2 : cert.contexts[l2.k]? with
                              | none => simp [hctx1, hctx2] at hchk
                              | some ctxK2 =>
                                simp only [hctx1, hctx2, Bool.and_eq_true, beq_iff_eq,
                                  decide_eq_true_eq, and_assoc] at hchk
                                obtain ⟨hha, hca, hra, hl1h, hl1r, hl1rk, hrf1r, hrf1s,
                                  hk1H, hk1C, hk1R, hl2h, hl2rk, hrf2r, hrf2s,
                                  hk2H, hk2C, hk2R, hcov⟩ := hchk
                                have hxa := hsubLT subAIdx sfA hgetA (hrk ▸ hra) ctxH (hha.symm ▸ hctxH) x hx
                                rw [hca] at hxa
                                obtain ⟨y1, hr1y1, hy1K1⟩ :=
                                  hlinkLT link1Idx l1 hgetL1 (hrk ▸ hl1rk) ctxH ctxK1 (hl1h.symm ▸ hctxH) hctx1 x hx
                                have hsy1 := hroles rf1Idx rf1 hgetRf1 x y1 (hrf1r.symm ▸ hr1y1)
                                rw [hrf1s] at hsy1
                                have hy1b := hsubLT subK1BIdx sfK1B hgetK1B (hrk ▸ hk1R) ctxK1 (hk1H.symm ▸ hctx1) y1 hy1K1
                                rw [hk1C] at hy1b
                                obtain ⟨y2, hr2y2, hy2K2⟩ :=
                                  hlinkLT link2Idx l2 hgetL2 (hrk ▸ hl2rk) ctxH ctxK2 (hl2h.symm ▸ hctxH) hctx2 x hx
                                have hsy2 := hroles rf2Idx rf2 hgetRf2 x y2 (hrf2r.symm ▸ hr2y2)
                                rw [hrf2s] at hsy2
                                have hy2b := hsubLT subK2BIdx sfK2B hgetK2B (hrk ▸ hk2R) ctxK2 (hk2H.symm ▸ hctx2) y2 hy2K2
                                rw [hk2C] at hy2b
                                have hmax := hax (.maxOne a s b) (mem_toList_of_getElem? hgetM)
                                have heqY : y1 = y2 := hmax x hxa y1 y2 hsy1 hy1b hsy2 hy2b
                                refine ⟨y1, hl1r ▸ hr1y1, fun c hc => ?_⟩
                                have hmem := array_all_iff.mp hcov c hc
                                simp only [Bool.or_eq_true] at hmem
                                rcases hmem with h1 | h2
                                · exact hy1K1 c (array_contains_iff.mp h1)
                                · exact heqY ▸ hy2K2 c (array_contains_iff.mp h2)
                          | _ => cases hchk
  exact ⟨hroles,
         fun idx sf hsf => (hmut sf.rank).1 idx sf hsf rfl,
         fun idx lf hlf => (hmut lf.rank).2 idx lf hlf rfl⟩

/-! ### 4. Fast Worklist Saturator (`saturateHornSHI`) -/

private def insertSortedUnique (xs : Array Nat) (v : Nat) : Array Nat :=
  if xs.contains v then xs
  else (xs.push v).qsort (· < ·)

private def mergeSortedUnique (xs : Array Nat) (ys : Array Nat) : Array Nat := Id.run do
  let mut out := xs
  let mut changed := false
  for y in ys do
    if !out.contains y then
      out := out.push y
      changed := true
  if changed then out.qsort (· < ·) else out

/-- Worklist-driven Horn-$\mathcal{SHI}$ consequence-based saturator producing a
    rank-stratified `CBCert` suitable for kernel verification via `checkCBSound`.
    Uses:
    - global indexing of `owl:Thing ⊑ ∀s.d` (`ObjectPropertyRange`) so range axioms
      are never duplicated per context,
    - per-context role-indexed `ctxAlls` for non-`Thing` universals,
    - two-stage scheduling (class-hierarchy saturation before existential expansion)
      plus subsumption-aware filtering (`!(ctxSubIdx[k]).contains d`) to avoid
      allocating semantically redundant contexts,
    - configurable `maxContexts`, `maxCtxSize`, and `maxLinks` caps so lower-bound
      saturation is always fast and bounded even on cyclic non-Horn ontologies. -/
def saturateHornSHI (norm : NormResult)
    (maxContexts : Nat := 4096) (maxCtxSize : Nat := 10) (maxLinks : Nat := 32768) : CBCert := Id.run do
  let nCls := norm.table.classes.size
  let nRoles := norm.table.roles.size

  -- 1. Index normalized Horn axioms in O(|O|)
  let mut unarySubs : Array (Array (Nat × Nat)) := Array.replicate nCls #[]
  let mut conjWatch : Array (Array Nat) := Array.replicate nCls #[]
  let mut emptySubs : Array (Nat × Nat) := #[]
  let mut exRightByA : Array (Array (Nat × Nat × Nat)) := Array.replicate nCls #[]
  let mut exLeftByA : Array (Array (Nat × Nat × Nat)) := Array.replicate nCls #[]
  let mut allRightByA : Array (Array (Nat × Nat × Nat)) := Array.replicate nCls #[]
  let mut globalAllByRole : Array (Array (Nat × Nat)) := Array.replicate nRoles #[]
  let mut maxOneByA : Array (Array (Nat × Nat × Nat)) := Array.replicate nCls #[]
  let mut globalMaxByRole : Array (Array (Nat × Nat)) := Array.replicate nRoles #[]
  let mut isMaxFiller : Array Bool := Array.replicate nCls false
  let mut hasMaxOne : Bool := false
  let mut directRoleSub : Array (Array (Nat × Nat)) := Array.replicate nRoles #[]
  let mut chainsByS1 : Array (Array (Nat × Nat × Nat)) := Array.replicate nRoles #[]
  let mut chainsByS2 : Array (Array (Nat × Nat × Nat)) := Array.replicate nRoles #[]
  let mut reflRoleAxs : Array (Nat × Nat) := #[]

  for axIdx in [0:norm.axioms.size] do
    match norm.axioms[axIdx]! with
    | .sub lhs rhs =>
      if lhs.size == 0 then
        emptySubs := emptySubs.push (axIdx, rhs)
      else if lhs.size == 1 then
        let a := lhs[0]!
        if a < nCls then unarySubs := unarySubs.modify a (·.push (axIdx, rhs))
      else
        for a in lhs do
          if a < nCls then conjWatch := conjWatch.modify a (·.push axIdx)
    | .existR a r b =>
      if a < nCls then exRightByA := exRightByA.modify a (·.push (axIdx, r, b))
    | .existL s a b =>
      if a < nCls then exLeftByA := exLeftByA.modify a (·.push (axIdx, s, b))
    | .allR a s d =>
      if a == 0 then
        if s < nRoles then globalAllByRole := globalAllByRole.modify s (·.push (axIdx, d))
      else if a < nCls then
        allRightByA := allRightByA.modify a (·.push (axIdx, s, d))
    | .roleSub r s =>
      if r < nRoles && s < nRoles then
        directRoleSub := directRoleSub.modify r (·.push (s, axIdx))
    | .roleChain s1 s2 s =>
      if s1 < nRoles && s2 < nRoles && s < nRoles then
        chainsByS1 := chainsByS1.modify s1 (·.push (axIdx, s2, s))
        chainsByS2 := chainsByS2.modify s2 (·.push (axIdx, s1, s))
    | .roleRefl r =>
      if r < nRoles then reflRoleAxs := reflRoleAxs.push (axIdx, r)
    | .maxOne a s b =>
      if s < nRoles && b < nCls then
        hasMaxOne := true
        isMaxFiller := isMaxFiller.set! b true
        if a == 0 then
          globalMaxByRole := globalMaxByRole.modify s (·.push (axIdx, b))
        else if a < nCls then
          maxOneByA := maxOneByA.modify a (·.push (axIdx, s, b))

  -- 2. Compute reflexive-transitive role hierarchy closure with justifications
  let mut roleFacts : Array RoleFact := #[]
  let mut roleFactMap : Std.HashMap (Nat × Nat) Nat := {}
  let mut roleSups : Array (Array (Nat × Nat)) := Array.replicate nRoles #[]

  for r in [0:nRoles] do
    let reflIdx := roleFacts.size
    roleFacts := roleFacts.push { r := r, s := r, just := .refl }
    roleFactMap := roleFactMap.insert (r, r) reflIdx
    roleSups := roleSups.modify r (·.push (r, reflIdx))

  for r in [0:nRoles] do
    let mut bfsQueue : Array (Nat × Nat) := #[(r, roleFactMap.getD (r, r) 0)]
    let mut qHead : Nat := 0
    while qHead < bfsQueue.size do
      let (cur, curRfIdx) := bfsQueue[qHead]!
      qHead := qHead + 1
      for (nxt, axIdx) in directRoleSub[cur]! do
        if !roleFactMap.contains (r, nxt) then
          let directIdx ← do
            match roleFactMap[(cur, nxt)]? with
            | some di => pure di
            | none =>
              let di := roleFacts.size
              roleFacts := roleFacts.push { r := cur, s := nxt, just := .ax axIdx }
              roleFactMap := roleFactMap.insert (cur, nxt) di
              roleSups := roleSups.modify cur (·.push (nxt, di))
              pure di
          let newRfIdx ← do
            if cur == r then pure directIdx
            else
              let ti := roleFacts.size
              roleFacts := roleFacts.push { r := r, s := nxt, just := .trans curRfIdx directIdx }
              roleFactMap := roleFactMap.insert (r, nxt) ti
              roleSups := roleSups.modify r (·.push (nxt, ti))
              pure ti
          bfsQueue := bfsQueue.push (nxt, newRfIdx)

  -- Map each reflexive-entailed role `s` to one witness `(reflAxIdx, rfIdx)`
  let mut reflSupWitness : Std.HashMap Nat (Nat × Nat) := {}
  for (reflAxIdx, r0) in reflRoleAxs do
    for (s, rfIdx) in roleSups[r0]! do
      if !reflSupWitness.contains s then
        reflSupWitness := reflSupWitness.insert s (reflAxIdx, rfIdx)

  -- Pre-collect global universals that trigger on reflexive roles
  let mut globalReflD : Array (Nat × Nat × Nat × Nat) := #[]  -- `(reflAxIdx, rfIdx, allAxIdx, d)`
  for (s, (reflAxIdx, rfIdx)) in reflSupWitness.toList do
    if s < nRoles then
      for (allAxIdx, d) in globalAllByRole[s]! do
        globalReflD := globalReflD.push (reflAxIdx, rfIdx, allAxIdx, d)

  -- 3. Context table and worklist state
  let mut contexts : Array (Array Nat) := #[]
  let mut ctxMap : Std.HashMap (Array Nat) Nat := {}
  let mut subFacts : Array SubFact := #[]
  let mut linkFacts : Array LinkFact := #[]

  -- Per-context derived facts: `ctxSubIdx[h][c] = sfIdx`
  let mut ctxSubIdx : Array (Std.HashMap Nat Nat) := #[]
  let mut ctxSubList : Array (Array (Nat × Nat)) := #[]  -- `(c, sfIdx)`
  let mut ctxTopIdx : Array Nat := #[]                   -- `sfIdx` of `(h, 0)` (rank 0)
  -- Per-context active non-`Thing` universals indexed by role `s`: `(allAxIdx, sfIdx, d)`
  let mut ctxAlls : Array (Std.HashMap Nat (Array (Nat × Nat × Nat))) := #[]
  -- Per-context active non-`Thing` `maxOne` axioms indexed by role `s`: `(maxAxIdx, sfIdx, b)`
  let mut ctxMaxOnes : Array (Std.HashMap Nat (Array (Nat × Nat × Nat))) := #[]
  -- Outgoing/incoming links: `(r, k, linkIdx)` / `(h, r, linkIdx)` and dedup set `(h, r, k)`
  let mut outLinks : Array (Array (Nat × Nat × Nat)) := #[]
  let mut inLinks : Array (Array (Nat × Nat × Nat)) := #[]
  let mut linkSet : Std.HashSet (Nat × Nat × Nat) := {}

  -- Two sub-queues: `subQueue` drains pure class subsumptions before `exQueue` creates links
  let mut subQueue : Array Nat := #[]
  let mut subHead : Nat := 0
  let mut exQueue : Array Nat := #[]
  let mut exHead : Nat := 0
  let mut linkQueue : Array Nat := #[]
  let mut linkHead : Nat := 0

  let addSub := fun (h c rank : Nat) (just : SubJust)
      (subFacts : Array SubFact) (ctxSubIdx : Array (Std.HashMap Nat Nat))
      (ctxSubList : Array (Array (Nat × Nat))) (subQueue exQueue : Array Nat) =>
    if (ctxSubIdx[h]!).contains c then
      (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue)
    else
      let sfIdx := subFacts.size
      let subFacts' := subFacts.push { h := h, c := c, rank := rank, just := just }
      let ctxSubIdx' := ctxSubIdx.modify h (·.insert c sfIdx)
      let ctxSubList' := ctxSubList.modify h (·.push (c, sfIdx))
      let subQueue' := subQueue.push sfIdx
      let exQueue' := if c < nCls && !(exRightByA[c]!).isEmpty then exQueue.push sfIdx else exQueue
      (subFacts', ctxSubIdx', ctxSubList', subQueue', exQueue')

  let addLink := fun (h r k rank : Nat) (just : LinkJust)
      (linkFacts : Array LinkFact) (outLinks inLinks : Array (Array (Nat × Nat × Nat)))
      (linkSet : Std.HashSet (Nat × Nat × Nat)) (linkQueue : Array Nat) =>
    if linkFacts.size >= maxLinks || linkSet.contains (h, r, k) then
      (linkFacts, outLinks, inLinks, linkSet, linkQueue)
    else
      let lIdx := linkFacts.size
      let linkFacts' := linkFacts.push { h := h, r := r, k := k, rank := rank, just := just }
      let outLinks' := outLinks.modify h (·.push (r, k, lIdx))
      let inLinks' := inLinks.modify k (·.push (h, r, lIdx))
      let linkSet' := linkSet.insert (h, r, k)
      let linkQueue' := linkQueue.push lIdx
      (linkFacts', outLinks', inLinks', linkSet', linkQueue')

  let getOrCreateCtx := fun (elems : Array Nat)
      (contexts : Array (Array Nat)) (ctxMap : Std.HashMap (Array Nat) Nat)
      (subFacts : Array SubFact) (ctxSubIdx : Array (Std.HashMap Nat Nat))
      (ctxSubList : Array (Array (Nat × Nat))) (ctxTopIdx : Array Nat)
      (ctxAlls : Array (Std.HashMap Nat (Array (Nat × Nat × Nat))))
      (ctxMaxOnes : Array (Std.HashMap Nat (Array (Nat × Nat × Nat))))
      (outLinks inLinks : Array (Array (Nat × Nat × Nat)))
      (linkFacts : Array LinkFact) (linkSet : Std.HashSet (Nat × Nat × Nat))
      (subQueue exQueue linkQueue : Array Nat) =>
    match ctxMap[elems]? with
    | some cid =>
      (some cid, contexts, ctxMap, subFacts, ctxSubIdx, ctxSubList, ctxTopIdx, ctxAlls, ctxMaxOnes,
       outLinks, inLinks, linkFacts, linkSet, subQueue, exQueue, linkQueue)
    | none =>
      if contexts.size >= maxContexts || elems.size > maxCtxSize then
        (none, contexts, ctxMap, subFacts, ctxSubIdx, ctxSubList, ctxTopIdx, ctxAlls, ctxMaxOnes,
         outLinks, inLinks, linkFacts, linkSet, subQueue, exQueue, linkQueue)
      else Id.run do
        let cid := contexts.size
        let mut contexts' := contexts.push elems
        let mut ctxMap' := ctxMap.insert elems cid
        let mut subFacts' := subFacts
        let mut ctxSubIdx' := ctxSubIdx.push {}
        let mut ctxSubList' := ctxSubList.push #[]
        let mut ctxAlls' := ctxAlls.push {}
        let mut ctxMaxOnes' := ctxMaxOnes.push {}
        let mut outLinks' := outLinks.push #[]
        let mut inLinks' := inLinks.push #[]
        let mut linkFacts' := linkFacts
        let mut linkSet' := linkSet
        let mut subQueue' := subQueue
        let mut exQueue' := exQueue
        let mut linkQueue' := linkQueue
        -- Always insert `top` (`0`) first so we know its exact `sfIdx`
        let topIdx := subFacts'.size
        let ctxTopIdx' := ctxTopIdx.push topIdx
        (subFacts', ctxSubIdx', ctxSubList', subQueue', exQueue') :=
          addSub cid 0 0 .top subFacts' ctxSubIdx' ctxSubList' subQueue' exQueue'
        for pos in [0:elems.size] do
          let c := elems[pos]!
          (subFacts', ctxSubIdx', ctxSubList', subQueue', exQueue') :=
            addSub cid c 0 (.inCtx pos) subFacts' ctxSubIdx' ctxSubList' subQueue' exQueue'
        for (axIdx, rhs) in emptySubs do
          (subFacts', ctxSubIdx', ctxSubList', subQueue', exQueue') :=
            addSub cid rhs 1 (.conj axIdx #[]) subFacts' ctxSubIdx' ctxSubList' subQueue' exQueue'
        for (reflAxIdx, rfIdx, allAxIdx, d) in globalReflD do
          (subFacts', ctxSubIdx', ctxSubList', subQueue', exQueue') :=
            addSub cid d 1 (.reflAll reflAxIdx rfIdx allAxIdx topIdx)
              subFacts' ctxSubIdx' ctxSubList' subQueue' exQueue'
        for (reflAxIdx, r0) in reflRoleAxs do
          let rfIdx := roleFactMap.getD (r0, r0) 0
          (linkFacts', outLinks', inLinks', linkSet', linkQueue') :=
            addLink cid r0 cid 0 (.reflLink reflAxIdx rfIdx)
              linkFacts' outLinks' inLinks' linkSet' linkQueue'
        return (some cid, contexts', ctxMap', subFacts', ctxSubIdx', ctxSubList', ctxTopIdx',
                ctxAlls', ctxMaxOnes', outLinks', inLinks', linkFacts', linkSet', subQueue', exQueue', linkQueue')

  -- Seed one singleton context for every named class (except `owl:Nothing`)
  for (_, id) in norm.namedClassIds do
    if id != 1 then
      let (_, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
        getOrCreateCtx #[id] contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
          outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
      contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
      ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
      outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
      subQueue := sq1; exQueue := eq1; linkQueue := lq1

  -- Helper: collect all active `maxOne` constraints `(maxAxIdx, sfAIdx, b)` at `(h, s)`
  let getMaxOnesAt := fun (h s : Nat) (ctxTopIdx : Array Nat)
      (ctxMaxOnes : Array (Std.HashMap Nat (Array (Nat × Nat × Nat)))) =>
    let topIdx := ctxTopIdx[h]!
    let g := if s < nRoles then (globalMaxByRole[s]!).map fun (ax, b) => (ax, topIdx, b) else #[]
    let l := (ctxMaxOnes[h]!).getD s #[]
    if g.isEmpty then l else if l.isEmpty then g else g ++ l

  -- 4. Main worklist fixpoint (draining `subQueue` before `exQueue` so base subsumptions
  --    are already known when existential successor contexts are created)
  while subHead < subQueue.size || exHead < exQueue.size || linkHead < linkQueue.size do
    while subHead < subQueue.size do
      let sfIdx := subQueue[subHead]!
      subHead := subHead + 1
      let sf := subFacts[sfIdx]!
      let h := sf.h
      let c := sf.c
      let rk := sf.rank

      -- (a) Bottom propagation to predecessors
      if c == 1 then
        for (hPrev, _, lIdx) in inLinks[h]! do
          let lRk := linkFacts[lIdx]!.rank
          (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
            addSub hPrev 1 (max rk lRk + 1) (.botLink lIdx sfIdx)
              subFacts ctxSubIdx ctxSubList subQueue exQueue

      -- (b) Unary subsumptions `c ⊑ rhs`
      if c < nCls then
        for (axIdx, rhs) in unarySubs[c]! do
          (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
            addSub h rhs (rk + 1) (.conj axIdx #[sfIdx])
              subFacts ctxSubIdx ctxSubList subQueue exQueue

        -- (c) Multi-premise conjunctions `a1 ∧ ... ∧ an ⊑ rhs`
        for axIdx in conjWatch[c]! do
          if let .sub lhs rhs := norm.axioms[axIdx]! then
            if !(ctxSubIdx[h]!).contains rhs then
              let mut ok := true
              let mut prems : Array Nat := Array.mkEmpty lhs.size
              let mut maxRk := rk
              for a in lhs do
                match (ctxSubIdx[h]!)[a]? with
                | some pIdx =>
                  prems := prems.push pIdx
                  let prk := subFacts[pIdx]!.rank
                  if prk > maxRk then maxRk := prk
                | none =>
                  ok := false
                  break
              if ok then
                (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                  addSub h rhs (maxRk + 1) (.conj axIdx prems)
                    subFacts ctxSubIdx ctxSubList subQueue exQueue

        -- (e) Non-`Thing` universal right `c ⊑ ∀s.d`
        for (axIdx, s, d) in allRightByA[c]! do
          ctxAlls := ctxAlls.modify h fun m => m.insert s ((m.getD s #[]).push (axIdx, sfIdx, d))
          -- Reflexive self-propagation
          if let some (reflAxIdx, rfIdx) := reflSupWitness[s]? then
            (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
              addSub h d (rk + 1) (.reflAll reflAxIdx rfIdx axIdx sfIdx)
                subFacts ctxSubIdx ctxSubList subQueue exQueue
          -- Forward strengthening of existing outgoing links from `h`
          let curOut := outLinks[h]!
          for (r, k0, lIdx) in curOut do
            if let some rfIdx := roleFactMap[(r, s)]? then
              if !(ctxSubIdx[k0]!).contains d then
                let elems0 := contexts[k0]!
                let newElems := insertSortedUnique elems0 d
                let lRk := linkFacts[lIdx]!.rank
                let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
                  getOrCreateCtx newElems contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
                    outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
                contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
                ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
                outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
                subQueue := sq1; exQueue := eq1; linkQueue := lq1
                if let some kNew := k? then
                  (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                    addLink h r kNew (max rk lRk + 1) (.allProp lIdx #[(axIdx, sfIdx, rfIdx)])
                      linkFacts outLinks inLinks linkSet linkQueue
          -- Backward inverse-universal propagation along incoming links into `h`
          let sInv := invRole s
          for (hPrev, rPrev, lIdx) in inLinks[h]! do
            if let some rfIdx := roleFactMap[(rPrev, sInv)]? then
              let lRk := linkFacts[lIdx]!.rank
              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                addSub hPrev d (max rk lRk + 1) (.invAll axIdx lIdx rfIdx sfIdx)
                  subFacts ctxSubIdx ctxSubList subQueue exQueue

        -- (f) Existential left `∃s.c ⊑ b` along incoming links into `h`
        for (axIdx, s, b) in exLeftByA[c]! do
          for (hPrev, rPrev, lIdx) in inLinks[h]! do
            if let some rfIdx := roleFactMap[(rPrev, s)]? then
              let lRk := linkFacts[lIdx]!.rank
              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                addSub hPrev b (max rk lRk + 1) (.exElim axIdx lIdx rfIdx sfIdx)
                  subFacts ctxSubIdx ctxSubList subQueue exQueue

        -- (f2) Horn-SHIQ `maxOne` rules triggered by `(h, c)`
        if hasMaxOne then
          -- Activate non-`Thing` `maxOne c s b` on `h`
          for (maxAxIdx, s, b) in maxOneByA[c]! do
            ctxMaxOnes := ctxMaxOnes.modify h fun m => m.insert s ((m.getD s #[]).push (maxAxIdx, sfIdx, b))
            -- Sibling merges among existing outgoing links of `h`
            let curOut := outLinks[h]!
            for (r1, k1, l1Idx) in curOut do
              if linkFacts.size < maxLinks then
                if let some rf1Idx := roleFactMap[(r1, s)]? then
                  if let some sfK1B := (ctxSubIdx[k1]!)[b]? then
                    for (r2, k2, l2Idx) in curOut do
                      if k1 != k2 && linkFacts.size < maxLinks then
                        if let some rf2Idx := roleFactMap[(r2, s)]? then
                          if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                            if !(contexts[k2]!.all fun e => (ctxSubIdx[k1]!).contains e) then
                              let merged := mergeSortedUnique contexts[k1]! contexts[k2]!
                              let mRk := max (max rk (max linkFacts[l1Idx]!.rank linkFacts[l2Idx]!.rank))
                                             (max subFacts[sfK1B]!.rank subFacts[sfK2B]!.rank)
                              let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
                                getOrCreateCtx merged contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
                                  outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
                              contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
                              ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
                              outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
                              subQueue := sq1; exQueue := eq1; linkQueue := lq1
                              if let some kNew := k? then
                                (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                                  addLink h r1 kNew (mRk + 1)
                                    (.siblingMerge maxAxIdx sfIdx l1Idx rf1Idx sfK1B l2Idx rf2Idx sfK2B)
                                    linkFacts outLinks inLinks linkSet linkQueue
            -- Parent merges between `inLinks[h]` and `outLinks[h]`
            let sInv := invRole s
            for (hPrev, r1, l1Idx) in inLinks[h]! do
              if let some rf1Idx := roleFactMap[(r1, sInv)]? then
                if let some sfHB := (ctxSubIdx[hPrev]!)[b]? then
                  let baseRk := max (max rk linkFacts[l1Idx]!.rank) subFacts[sfHB]!.rank
                  for (r2, k2, l2Idx) in outLinks[h]! do
                    if let some rf2Idx := roleFactMap[(r2, s)]? then
                      if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                        let baseRk2 := max (max baseRk linkFacts[l2Idx]!.rank) subFacts[sfK2B]!.rank
                        for (c2, sfK2C) in ctxSubList[k2]! do
                          if !(ctxSubIdx[hPrev]!).contains c2 then
                            (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                              addSub hPrev c2 (max baseRk2 subFacts[sfK2C]!.rank + 1)
                                (.parentMerge maxAxIdx l1Idx rf1Idx sfHB sfIdx l2Idx rf2Idx sfK2B sfK2C)
                                subFacts ctxSubIdx ctxSubList subQueue exQueue
          -- If `c` is a `maxOne` filler: fire siblingMerge & parentMerge where `h` plays `k1`/`k2`/`hPrev`
          if isMaxFiller[c]! then
            for (hPar, r1, l1Idx) in inLinks[h]! do
              if r1 < nRoles then
                for (s, rf1Idx) in roleSups[r1]! do
                  for (maxAxIdx, sfAIdx, b) in getMaxOnesAt hPar s ctxTopIdx ctxMaxOnes do
                    if b == c then
                      -- Sibling merge at `hPar` between `(r1, h)` and other outgoing links
                      let curOut := outLinks[hPar]!
                      for (r2, k2, l2Idx) in curOut do
                        if h != k2 && linkFacts.size < maxLinks then
                          if let some rf2Idx := roleFactMap[(r2, s)]? then
                            if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                              if !(contexts[k2]!.all fun e => (ctxSubIdx[h]!).contains e) then
                                let merged := mergeSortedUnique contexts[h]! contexts[k2]!
                                let mRk := max (max subFacts[sfAIdx]!.rank (max linkFacts[l1Idx]!.rank linkFacts[l2Idx]!.rank))
                                               (max rk subFacts[sfK2B]!.rank)
                                let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
                                  getOrCreateCtx merged contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
                                    outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
                                contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
                                ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
                                outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
                                subQueue := sq1; exQueue := eq1; linkQueue := lq1
                                if let some kNew := k? then
                                  (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                                    addLink hPar r1 kNew (mRk + 1)
                                      (.siblingMerge maxAxIdx sfAIdx l1Idx rf1Idx sfIdx l2Idx rf2Idx sfK2B)
                                      linkFacts outLinks inLinks linkSet linkQueue
                      -- Parent merge with `h` as `k2` through `hPar`
                      let sInv := invRole s
                      for (hGrand, r0, l0Idx) in inLinks[hPar]! do
                        if let some rf0Idx := roleFactMap[(r0, sInv)]? then
                          if let some sfHB := (ctxSubIdx[hGrand]!)[b]? then
                            let baseRk := max (max subFacts[sfAIdx]!.rank (max linkFacts[l0Idx]!.rank linkFacts[l1Idx]!.rank))
                                              (max sfHB rk)
                            let baseRk' := max (max baseRk subFacts[sfHB]!.rank) rk
                            for (c2, sfK2C) in ctxSubList[h]! do
                              if !(ctxSubIdx[hGrand]!).contains c2 then
                                (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                                  addSub hGrand c2 (max baseRk' subFacts[sfK2C]!.rank + 1)
                                    (.parentMerge maxAxIdx l0Idx rf0Idx sfHB sfAIdx l1Idx rf1Idx sfIdx sfK2C)
                                    subFacts ctxSubIdx ctxSubList subQueue exQueue
            -- Parent merge with `h` as `hPrev` (gaining filler `b = c`)
            for (r1, kMid, l1Idx) in outLinks[h]! do
              if r1 < nRoles then
                for (sInv, rf1Idx) in roleSups[r1]! do
                  let s := invRole sInv
                  for (maxAxIdx, sfAIdx, b) in getMaxOnesAt kMid s ctxTopIdx ctxMaxOnes do
                    if b == c then
                      let baseRk := max (max rk subFacts[sfAIdx]!.rank) linkFacts[l1Idx]!.rank
                      for (r2, k2, l2Idx) in outLinks[kMid]! do
                        if let some rf2Idx := roleFactMap[(r2, s)]? then
                          if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                            let baseRk2 := max (max baseRk linkFacts[l2Idx]!.rank) subFacts[sfK2B]!.rank
                            for (c2, sfK2C) in ctxSubList[k2]! do
                              if !(ctxSubIdx[h]!).contains c2 then
                                (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                                  addSub h c2 (max baseRk2 subFacts[sfK2C]!.rank + 1)
                                    (.parentMerge maxAxIdx l1Idx rf1Idx sfIdx sfAIdx l2Idx rf2Idx sfK2B sfK2C)
                                    subFacts ctxSubIdx ctxSubList subQueue exQueue
          -- Propagate newly derived `(h, c)` upward via `parentMerge` (`h` plays `k2`)
          for (hMid, r2, l2Idx) in inLinks[h]! do
            if r2 < nRoles then
              for (s, rf2Idx) in roleSups[r2]! do
                let mList := getMaxOnesAt hMid s ctxTopIdx ctxMaxOnes
                if !mList.isEmpty then
                  let sInv := invRole s
                  for (maxAxIdx, sfAIdx, b) in mList do
                    if let some sfK2B := (ctxSubIdx[h]!)[b]? then
                      let baseRk := max (max rk subFacts[sfAIdx]!.rank) (max linkFacts[l2Idx]!.rank subFacts[sfK2B]!.rank)
                      for (hPrev, r1, l1Idx) in inLinks[hMid]! do
                        if !(ctxSubIdx[hPrev]!).contains c then
                          if let some rf1Idx := roleFactMap[(r1, sInv)]? then
                            if let some sfHB := (ctxSubIdx[hPrev]!)[b]? then
                              let mRk := max baseRk (max linkFacts[l1Idx]!.rank subFacts[sfHB]!.rank)
                              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                                addSub hPrev c (mRk + 1)
                                  (.parentMerge maxAxIdx l1Idx rf1Idx sfHB sfAIdx l2Idx rf2Idx sfK2B sfIdx)
                                  subFacts ctxSubIdx ctxSubList subQueue exQueue

    -- (d) Existential introduction `c ⊑ ∃r.b` (with O(|roleSups[r]|) global + local universal lookup)
    if subHead >= subQueue.size && exHead < exQueue.size then
      let sfIdx := exQueue[exHead]!
      exHead := exHead + 1
      let sf := subFacts[sfIdx]!
      let h := sf.h
      let c := sf.c
      let rk := sf.rank
      let topIdxH := ctxTopIdx[h]!
      let localAlls := ctxAlls[h]!
      for (axIdx, r, b) in exRightByA[c]! do
        if r < nRoles && linkFacts.size < maxLinks then
          let baseKnown? := (ctxMap[#[b]]?).map fun bid => ctxSubIdx[bid]!
          let mut targetElems : Array Nat := #[b]
          let mut allPrems : Array (Nat × Nat × Nat) := #[]
          let mut maxRk := rk
          for (s, rfIdx) in roleSups[r]! do
            for (allAxIdx, d) in globalAllByRole[s]! do
              let already := match baseKnown? with | some bm => bm.contains d | none => false
              if !already && !targetElems.contains d then
                targetElems := insertSortedUnique targetElems d
                allPrems := allPrems.push (allAxIdx, topIdxH, rfIdx)
            for (allAxIdx, sfAllIdx, d) in localAlls.getD s #[] do
              let already := match baseKnown? with | some bm => bm.contains d | none => false
              if !already && !targetElems.contains d then
                targetElems := insertSortedUnique targetElems d
                allPrems := allPrems.push (allAxIdx, sfAllIdx, rfIdx)
                let aRk := subFacts[sfAllIdx]!.rank
                if aRk > maxRk then maxRk := aRk
          let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
            getOrCreateCtx targetElems contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
              outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
          contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
          ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
          outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
          subQueue := sq1; exQueue := eq1; linkQueue := lq1
          if let some kId := k? then
            (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
              addLink h r kId (maxRk + 1) (.exIntro axIdx sfIdx allPrems)
                linkFacts outLinks inLinks linkSet linkQueue

    -- Process newly derived links
    while linkHead < linkQueue.size do
      let lIdx := linkQueue[linkHead]!
      linkHead := linkHead + 1
      let lf := linkFacts[lIdx]!
      let h := lf.h
      let r := lf.r
      let k := lf.k
      let lRk := lf.rank

      -- (g) Bottom propagation if `k` already entails `⊥`
      if let some botIdx := (ctxSubIdx[k]!)[1]? then
        let bRk := subFacts[botIdx]!.rank
        (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
          addSub h 1 (max lRk bRk + 1) (.botLink lIdx botIdx)
            subFacts ctxSubIdx ctxSubList subQueue exQueue

      -- (h) Apply global + local active universals on `h` to strengthen `(h, r, k)` if needed
      if r < nRoles && linkFacts.size < maxLinks then
        let kKnown := ctxSubIdx[k]!
        let elems0 := contexts[k]!
        let topIdxH := ctxTopIdx[h]!
        let localAlls := ctxAlls[h]!
        let mut extraDs : Array Nat := #[]
        let mut allPrems : Array (Nat × Nat × Nat) := #[]
        let mut maxAllRk := lRk
        for (s, rfIdx) in roleSups[r]! do
          for (allAxIdx, d) in globalAllByRole[s]! do
            if !kKnown.contains d && !extraDs.contains d then
              extraDs := extraDs.push d
              allPrems := allPrems.push (allAxIdx, topIdxH, rfIdx)
          for (allAxIdx, sfAllIdx, d) in localAlls.getD s #[] do
            if !kKnown.contains d && !extraDs.contains d then
              extraDs := extraDs.push d
              allPrems := allPrems.push (allAxIdx, sfAllIdx, rfIdx)
              let aRk := subFacts[sfAllIdx]!.rank
              if aRk > maxAllRk then maxAllRk := aRk
        if !extraDs.isEmpty then
          let newElems := mergeSortedUnique elems0 extraDs
          let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
            getOrCreateCtx newElems contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
              outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
          contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
          ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
          outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
          subQueue := sq1; exQueue := eq1; linkQueue := lq1
          if let some kNew := k? then
            (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
              addLink h r kNew (maxAllRk + 1) (.allProp lIdx allPrems)
                linkFacts outLinks inLinks linkSet linkQueue

      -- (i) Existential elimination & inverse-universal firing (global `0` + known facts in `k`)
      if r < nRoles then
        let topIdxK := ctxTopIdx[k]!
        for (sInv, rfIdx) in roleSups[r]! do
          let s := invRole sInv
          if s < nRoles then
            for (allAxIdx, d) in globalAllByRole[s]! do
              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                addSub h d (lRk + 1) (.invAll allAxIdx lIdx rfIdx topIdxK)
                  subFacts ctxSubIdx ctxSubList subQueue exQueue
      for (a, sfKIdx) in ctxSubList[k]! do
        if a < nCls then
          let aRk := subFacts[sfKIdx]!.rank
          for (axIdx, s, b) in exLeftByA[a]! do
            if let some rfIdx := roleFactMap[(r, s)]? then
              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                addSub h b (max lRk aRk + 1) (.exElim axIdx lIdx rfIdx sfKIdx)
                  subFacts ctxSubIdx ctxSubList subQueue exQueue
          for (axIdx, sInv, b) in allRightByA[a]! do
            if let some rfIdx := roleFactMap[(r, invRole sInv)]? then
              (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                addSub h b (max lRk aRk + 1) (.invAll axIdx lIdx rfIdx sfKIdx)
                  subFacts ctxSubIdx ctxSubList subQueue exQueue

      -- (j) Bidirectional role-chain link composition (`h -r1-> k1 -r2-> k2` ⇒ `h -s-> k2`)
      if r < nRoles && h != k && linkFacts.size < maxLinks then
        for (s1, rf1Idx) in roleSups[r]! do
          for (axIdx, s2, s) in chainsByS1[s1]! do
            for (r2, k2, l2Idx) in outLinks[k]! do
              if k != k2 then
                if let some rf2Idx := roleFactMap[(r2, s2)]? then
                  let r2Rk := linkFacts[l2Idx]!.rank
                  (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                    addLink h s k2 (max lRk r2Rk + 1) (.chainComp axIdx lIdx rf1Idx l2Idx rf2Idx)
                      linkFacts outLinks inLinks linkSet linkQueue
        for (s2, rf2Idx) in roleSups[r]! do
          for (axIdx, s1, s) in chainsByS2[s2]! do
            for (hPrev, r1, l1Idx) in inLinks[h]! do
              if hPrev != h then
                if let some rf1Idx := roleFactMap[(r1, s1)]? then
                  let r1Rk := linkFacts[l1Idx]!.rank
                  (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                    addLink hPrev s k (max lRk r1Rk + 1) (.chainComp axIdx l1Idx rf1Idx lIdx rf2Idx)
                      linkFacts outLinks inLinks linkSet linkQueue

      -- (k) Horn-SHIQ `maxOne` siblingMerge & parentMerge triggered by new link `(h, r, k)`
      if hasMaxOne && r < nRoles then
        for (s, rf1Idx) in roleSups[r]! do
          for (maxAxIdx, sfAIdx, b) in getMaxOnesAt h s ctxTopIdx ctxMaxOnes do
            if let some sfKB := (ctxSubIdx[k]!)[b]? then
              -- Sibling merge at `h` between `(r, k)` and existing outgoing links `(r2, k2)`
              let curOut := outLinks[h]!
              for (r2, k2, l2Idx) in curOut do
                if k != k2 && linkFacts.size < maxLinks then
                  if let some rf2Idx := roleFactMap[(r2, s)]? then
                    if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                      let merged := mergeSortedUnique contexts[k]! contexts[k2]!
                      let mRk := max (max subFacts[sfAIdx]!.rank (max lRk linkFacts[l2Idx]!.rank))
                                     (max subFacts[sfKB]!.rank subFacts[sfK2B]!.rank)
                      let need1 := !(contexts[k2]!.all fun e => (ctxSubIdx[k]!).contains e)
                      let need2 := !(contexts[k]!.all fun e => (ctxSubIdx[k2]!).contains e)
                      if need1 || need2 then
                        let (k?, c1, cm1, sf1, csi1, csl1, cti1, ca1, cmo1, ol1, il1, lf1, ls1, sq1, eq1, lq1) :=
                          getOrCreateCtx merged contexts ctxMap subFacts ctxSubIdx ctxSubList ctxTopIdx ctxAlls ctxMaxOnes
                            outLinks inLinks linkFacts linkSet subQueue exQueue linkQueue
                        contexts := c1; ctxMap := cm1; subFacts := sf1; ctxSubIdx := csi1
                        ctxSubList := csl1; ctxTopIdx := cti1; ctxAlls := ca1; ctxMaxOnes := cmo1
                        outLinks := ol1; inLinks := il1; linkFacts := lf1; linkSet := ls1
                        subQueue := sq1; exQueue := eq1; linkQueue := lq1
                        if let some kNew := k? then
                          if need1 then
                            (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                              addLink h r kNew (mRk + 1)
                                (.siblingMerge maxAxIdx sfAIdx lIdx rf1Idx sfKB l2Idx rf2Idx sfK2B)
                                linkFacts outLinks inLinks linkSet linkQueue
                          if need2 then
                            (linkFacts, outLinks, inLinks, linkSet, linkQueue) :=
                              addLink h r2 kNew (mRk + 1)
                                (.siblingMerge maxAxIdx sfAIdx l2Idx rf2Idx sfK2B lIdx rf1Idx sfKB)
                                linkFacts outLinks inLinks linkSet linkQueue
              -- Parent merge with `(h, r, k)` as `l2` (`hPrev -r1-> h -r-> k`)
              let sInv := invRole s
              for (hPrev, r1, l1Idx) in inLinks[h]! do
                if let some rf0Idx := roleFactMap[(r1, sInv)]? then
                  if let some sfHB := (ctxSubIdx[hPrev]!)[b]? then
                    let baseRk := max (max subFacts[sfAIdx]!.rank (max linkFacts[l1Idx]!.rank lRk))
                                      (max subFacts[sfHB]!.rank subFacts[sfKB]!.rank)
                    for (c2, sfK2C) in ctxSubList[k]! do
                      if !(ctxSubIdx[hPrev]!).contains c2 then
                        (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                          addSub hPrev c2 (max baseRk subFacts[sfK2C]!.rank + 1)
                            (.parentMerge maxAxIdx l1Idx rf0Idx sfHB sfAIdx lIdx rf1Idx sfKB sfK2C)
                            subFacts ctxSubIdx ctxSubList subQueue exQueue
        -- Parent merge with `(h, r, k)` as `l1` (`h -r-> k -r2-> k2`)
        for (sInv, rf1Idx) in roleSups[r]! do
          let s := invRole sInv
          for (maxAxIdx, sfAIdx, b) in getMaxOnesAt k s ctxTopIdx ctxMaxOnes do
            if let some sfHB := (ctxSubIdx[h]!)[b]? then
              let baseRk := max (max subFacts[sfAIdx]!.rank lRk) subFacts[sfHB]!.rank
              for (r2, k2, l2Idx) in outLinks[k]! do
                if let some rf2Idx := roleFactMap[(r2, s)]? then
                  if let some sfK2B := (ctxSubIdx[k2]!)[b]? then
                    let baseRk2 := max (max baseRk linkFacts[l2Idx]!.rank) subFacts[sfK2B]!.rank
                    for (c2, sfK2C) in ctxSubList[k2]! do
                      if !(ctxSubIdx[h]!).contains c2 then
                        (subFacts, ctxSubIdx, ctxSubList, subQueue, exQueue) :=
                          addSub h c2 (max baseRk2 subFacts[sfK2C]!.rank + 1)
                            (.parentMerge maxAxIdx lIdx rf1Idx sfHB sfAIdx l2Idx rf2Idx sfK2B sfK2C)
                            subFacts ctxSubIdx ctxSubList subQueue exQueue

  return {
    contexts := contexts
    roleFacts := roleFacts
    subFacts := subFacts
    linkFacts := linkFacts
  }

/-! ### 5. Certified Named-Class Extraction & Public Entry Point -/

/-- Certified lower-bound output of Horn-$\mathcal{SHI}$ saturation. -/
structure FastCBResult where
  subs : List (IRI × IRI)
  unsats : List IRI
  isPureHornSHIQ : Bool
  verified : Bool
  deriving Repr, Inhabited

/-- Extract all named-class subsumptions `(a, b)` from singleton contexts in `cert.subFacts`. -/
def extractNamedSubs (norm : NormResult) (cert : CBCert) : List (IRI × IRI) :=
  cert.subFacts.toList.filterMap fun sf =>
    match cert.contexts[sf.h]? with
    | some ctx =>
      if ctx.size == 1 then
        match (ctx[0]? : Option Nat) with
        | some idA =>
          match norm.table.classes[idA]?, norm.table.classes[sf.c]? with
          | some (ClassExpr.named a), some (ClassExpr.named b) => some (a, b)
          | _, _ => none
        | none => none
      else none
    | none => none

/-- Extract all named classes `a` whose singleton context entails `owl:Nothing` (`c = 1`). -/
def extractNamedUnsats (norm : NormResult) (cert : CBCert) : List IRI :=
  cert.subFacts.toList.filterMap fun sf =>
    if sf.c == 1 then
      match cert.contexts[sf.h]? with
      | some ctx =>
        if ctx.size == 1 then
          match (ctx[0]? : Option Nat) with
          | some idA =>
            match norm.table.classes[idA]? with
            | some (ClassExpr.named a) => some a
            | _ => none
          | none => none
        else none
      | none => none
    else none

/-- Run Horn-$\mathcal{SHIQ}$ extraction, Horn-$\mathcal{SHI}$ saturation, and parallel
    kernel-verified soundness checking on `o`. Only returns facts if `checkCBSound` passes.
    Automatically scales context and link budgets so all named-class singleton contexts
    are always covered even on 10k–50k class non-Horn ontologies. -/
def runFastCB (o : Ontology) (numWorkers : Nat := 8)
    (maxContexts : Nat := 4096) (maxCtxSize : Nat := 10) (maxLinks : Nat := 32768) : FastCBResult :=
  let norm := extractHornSHIQ o
  let effMaxContexts := max maxContexts (norm.namedClassIds.size + 4096)
  let effMaxLinks := max maxLinks (norm.namedClassIds.size * 8)
  let cert := saturateHornSHI norm effMaxContexts maxCtxSize effMaxLinks
  if checkCBSound norm cert numWorkers then
    { subs := extractNamedSubs norm cert
      unsats := extractNamedUnsats norm cert
      isPureHornSHIQ := norm.isPureHornSHIQ
      verified := true }
  else
    { subs := [], unsats := [], isPureHornSHIQ := false, verified := false }

private theorem ctxHolds_singleton_of_getElem? {dm : DatatypeMap} {t : CBTable}
    {i : Interpretation dm} {ctx : Array Nat} {idA : Nat} {a : IRI} {x : i.Object}
    (hsz : ctx.size = 1) (h0 : ctx[0]? = some idA)
    (heq : t.classes[idA]? = some (.named a)) (hx : i.classes a x) :
    ctxHolds t i x ctx := by
  intro c hc
  obtain ⟨j, hjlt, rfl⟩ := List.getElem_of_mem hc
  have hj0 : j = 0 := by
    have : j < ctx.size := by simpa using hjlt
    omega
  subst hj0
  have hlt0 : 0 < ctx.size := by omega
  have hget : ctx[0]? = some ctx[0] := Array.getElem?_eq_getElem hlt0
  rw [h0] at hget
  have hid : ctx[0] = idA := (Option.some.inj hget).symm
  change classHolds i x (t.exprOf ctx[0])
  rw [hid]
  simp only [CBTable.exprOf, heq, Option.getD_some, classHolds]
  exact hx

/-- Kernel soundness theorem for `runFastCB`: every returned `(a, b)` in `subs` is
    semantically entailed by `o` under arbitrary `DatatypeMap`. -/
theorem runFastCB_subs_sound {dm : DatatypeMap} {o : Ontology}
    {numWorkers maxContexts maxCtxSize maxLinks : Nat} {a b : IRI}
    (hmem : (a, b) ∈ (runFastCB o numWorkers maxContexts maxCtxSize maxLinks).subs) :
    Entails dm o [.subClassOf (.named a) (.named b)] := by
  dsimp only [runFastCB] at hmem
  split at hmem
  · rename_i hcheck
    simp only [extractNamedSubs, List.mem_filterMap] at hmem
    obtain ⟨sf, hsfMem, hsfEq⟩ := hmem
    intro i ⟨assign, hsat⟩
    let j := i.withAnonymous assign
    have ⟨hwf, hax, _⟩ := extractHornSHIQ_sound (i := j) hsat
    have ⟨_, hSubHolds, _⟩ := checkCBSound_holds hwf hax hcheck
    obtain ⟨idx, hidxLt, hidxEq⟩ := List.getElem_of_mem hsfMem
    let cert := saturateHornSHI (extractHornSHIQ o)
      (max maxContexts ((extractHornSHIQ o).namedClassIds.size + 4096)) maxCtxSize
      (max maxLinks ((extractHornSHIQ o).namedClassIds.size * 8))
    have hidxLt' : idx < cert.subFacts.size := by
      simpa using hidxLt
    have hsfGet : cert.subFacts[idx]? = some sf := by
      rw [Array.getElem?_eq_getElem hidxLt']; exact congrArg some hidxEq
    have hsfH := hSubHolds idx sf hsfGet
    cases hctx : (saturateHornSHI (extractHornSHIQ o)
        (max maxContexts ((extractHornSHIQ o).namedClassIds.size + 4096)) maxCtxSize
        (max maxLinks ((extractHornSHIQ o).namedClassIds.size * 8))).contexts[sf.h]? with
    | none => simp [hctx] at hsfEq
    | some ctx =>
      simp only [hctx] at hsfEq
      split at hsfEq
      · rename_i hsz
        have hsz' : ctx.size = 1 := beq_iff_eq.mp hsz
        cases h0 : (ctx[0]? : Option Nat) with
        | none => simp [h0] at hsfEq
        | some idA =>
          simp only [h0] at hsfEq
          cases hca : (extractHornSHIQ o).table.classes[idA]? with
          | none => simp [hca] at hsfEq
          | some ea =>
            cases hcb : (extractHornSHIQ o).table.classes[sf.c]? with
            | none => simp [hca, hcb] at hsfEq
            | some eb =>
              simp only [hca, hcb] at hsfEq
              cases ea with
              | named a' =>
                cases eb with
                | named b' =>
                  cases hsfEq
                  refine ⟨assign, fun q hq => ?_⟩
                  simp only [List.mem_singleton] at hq; subst hq
                  intro x hx
                  have hctxX := ctxHolds_singleton_of_getElem? hsz' h0 hca hx
                  have hres := hsfH ctx hctx x hctxX
                  simpa [CBTable.exprOf, hcb, classHolds] using hres
                | _ => cases hsfEq
              | _ => cases hsfEq
      · cases hsfEq
  · simp at hmem

/-- Kernel soundness theorem for `runFastCB`: every returned `a` in `unsats` is
    semantically unsatisfiable in `o` under arbitrary `DatatypeMap`. -/
theorem runFastCB_unsats_sound {dm : DatatypeMap} {o : Ontology}
    {numWorkers maxContexts maxCtxSize maxLinks : Nat} {a : IRI}
    (hmem : a ∈ (runFastCB o numWorkers maxContexts maxCtxSize maxLinks).unsats) :
    Entails dm o [.subClassOf (.named a) (.named nothing)] := by
  dsimp only [runFastCB] at hmem
  split at hmem
  · rename_i hcheck
    simp only [extractNamedUnsats, List.mem_filterMap] at hmem
    obtain ⟨sf, hsfMem, hsfEq⟩ := hmem
    intro i ⟨assign, hsat⟩
    let j := i.withAnonymous assign
    have ⟨hwf, hax, _⟩ := extractHornSHIQ_sound (i := j) hsat
    have ⟨_, hSubHolds, _⟩ := checkCBSound_holds hwf hax hcheck
    obtain ⟨idx, hidxLt, hidxEq⟩ := List.getElem_of_mem hsfMem
    let cert := saturateHornSHI (extractHornSHIQ o)
      (max maxContexts ((extractHornSHIQ o).namedClassIds.size + 4096)) maxCtxSize
      (max maxLinks ((extractHornSHIQ o).namedClassIds.size * 8))
    have hidxLt' : idx < cert.subFacts.size := by
      simpa using hidxLt
    have hsfGet : cert.subFacts[idx]? = some sf := by
      rw [Array.getElem?_eq_getElem hidxLt']; exact congrArg some hidxEq
    have hsfH := hSubHolds idx sf hsfGet
    split at hsfEq
    · rename_i hc1
      have hc1' : sf.c = 1 := beq_iff_eq.mp hc1
      cases hctx : (saturateHornSHI (extractHornSHIQ o)
        (max maxContexts ((extractHornSHIQ o).namedClassIds.size + 4096)) maxCtxSize
        (max maxLinks ((extractHornSHIQ o).namedClassIds.size * 8))).contexts[sf.h]? with
      | none => simp [hctx] at hsfEq
      | some ctx =>
        simp only [hctx] at hsfEq
        split at hsfEq
        · rename_i hsz
          have hsz' : ctx.size = 1 := beq_iff_eq.mp hsz
          cases h0 : (ctx[0]? : Option Nat) with
          | none => simp [h0] at hsfEq
          | some idA =>
            simp only [h0] at hsfEq
            cases hca : (extractHornSHIQ o).table.classes[idA]? with
            | none => simp [hca] at hsfEq
            | some ea =>
              simp only [hca] at hsfEq
              cases ea with
              | named a' =>
                cases hsfEq
                refine ⟨assign, fun q hq => ?_⟩
                simp only [List.mem_singleton] at hq; subst hq
                intro x hx
                have hctxX := ctxHolds_singleton_of_getElem? hsz' h0 hca hx
                have hres := hsfH ctx hctx x hctxX
                rw [hc1', CBTable.exprOf_one hwf] at hres
                exact hres
              | _ => cases hsfEq
        · cases hsfEq
    · cases hsfEq
  · simp at hmem

/-- Worker-count invariance of `runFastCB`: `checkCBSound` is independent of `numWorkers`. -/
theorem checkCBSound_workers_eq (norm : NormResult) (cert : CBCert) (w : Nat) :
    checkCBSound norm cert w = checkCBSound norm cert 1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkCBSound, Bool.and_eq_true, allRangePar_iff]

theorem runFastCB_workers_eq (o : Ontology) (w maxContexts maxCtxSize maxLinks : Nat) :
    runFastCB o w maxContexts maxCtxSize maxLinks =
      runFastCB o 1 maxContexts maxCtxSize maxLinks := by
  dsimp only [runFastCB]
  rw [checkCBSound_workers_eq]

end Sabrina.OWL2.FastCB
