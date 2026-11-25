import Sabrina.OWL2.SROIQD.Termination.SRIQDecidable
import Sabrina.OWL2.SROIQD.Termination.TextbookSRIQBridge

namespace Sabrina.OWL2.SROIQD.TextbookSRIQ

open Sabrina.OWL2.Datatypes (datatypeMap)
open Sabrina.RoleChains (Rank checkRegular findRank)
open Termination.BlockedBranch (decideSRIQBool decideSRIQBool_ontology_iff)

/-- Exact boundary of the decision adapter after translating the reference
syntax. Textbook well-formedness is specified separately in `WellFormed`. -/
def TBoxRBox.Admitted (o : TBoxRBox) : Prop :=
  ∃ (defs : Normalize.DatatypeDefs) (p : Problem) (rank : Rank),
    Normalize.normalizeWithDefs o.toOWL = some (defs, p) ∧
    p.root = .top ∧ p.isSRIQ rank = true

/-- Terminating satisfiability decision for an admitted typed TBox/RBox.
`none` means the adapter could not admit the input. -/
def TBoxRBox.decide? (o : TBoxRBox) : Option Bool :=
  (Normalize.normalizeWithDefs o.toOWL).bind fun (_, p) =>
    (findRank p.rules p.chains).bind fun rank =>
      if h : p.root = .top ∧ p.isSRIQ rank = true then
        some (decideSRIQBool h.2)
      else none

theorem decide_admitted_iff (o : TBoxRBox) :
    o.decide?.isSome = true ↔ o.Admitted := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    simp only [TBoxRBox.decide?, Option.bind_eq_some_iff] at hb
    obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := hb
    split at hb
    · rename_i hadmit
      exact ⟨defs, p, rank, hnorm, hadmit.1, hadmit.2⟩
    · contradiction
  · rintro ⟨defs, p, rank, hnorm, hroot, hadmit⟩
    have hregular := (Problem.sriqInput hadmit).regular
    obtain ⟨rank', hfound⟩ := Option.isSome_iff_exists.mp
      (Sabrina.RoleChains.findRank_complete (Sabrina.RoleChains.checkRegular_sound hregular))
    have hregular' : checkRegular rank' p.rules p.chains = true :=
      Sabrina.RoleChains.checkRegular_iff.mpr (Sabrina.RoleChains.findRank_sound hfound)
    have hadmit' : p.isSRIQ rank' = true := by
      simp only [Problem.isSRIQ, Bool.and_eq_true] at hadmit ⊢
      exact ⟨hadmit.1, hregular'⟩
    simp [TBoxRBox.decide?, hnorm, hfound, hroot, hadmit']

private theorem verdict_iff {o : TBoxRBox} {b : Bool} (h : o.decide? = some b) :
    b = true ↔ o.Sat := by
  simp only [TBoxRBox.decide?, Option.bind_eq_some_iff] at h
  obtain ⟨⟨defs, p⟩, hnorm, rank, _, hb⟩ := h
  split at hb
  · rename_i hadmit
    cases hb
    exact (decideSRIQBool_ontology_iff hadmit.2 hnorm hadmit.1).trans
      (satisfiable_toOWL_iff datatypeMap o)
  · contradiction

theorem decide_sat_iff {o : TBoxRBox} (h : o.Admitted) :
    o.decide? = some true ↔ o.Sat := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((decide_admitted_iff o).mpr h)
  rw [← verdict_iff hb, hb, Option.some.injEq]

theorem decide_unsat_iff {o : TBoxRBox} (h : o.Admitted) :
    o.decide? = some false ↔ ¬ o.Sat := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((decide_admitted_iff o).mpr h)
  rw [← verdict_iff hb, hb, Option.some.injEq]
  cases b <;> simp

#print axioms decide_admitted_iff
#print axioms decide_sat_iff
#print axioms decide_unsat_iff

end Sabrina.OWL2.SROIQD.TextbookSRIQ
