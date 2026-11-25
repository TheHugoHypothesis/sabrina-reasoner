import Sabrina.OWL2.FastEL
import Sabrina.OWL2.FastClassification

/-! Unit and cross-check tests for `Sabrina.OWL2.FastEL` (parallel integer-interned
    single-global-canonical-model $\mathcal{EL}^{++}$ classifier). -/

namespace SabrinaTests.FastELTests

open Sabrina.OWL2
open Sabrina.OWL2.EL
open Sabrina.OWL2.FastEL
open Sabrina.OWL2.FastClassification

private def iri (s : String) : IRI := s!"http://example.org/fastel#{s}"

-- 1. Full EL++ rule coverage: CR1, CR2, CR3, CR4, CR5, CR10, CR11, roleRefl
private def richELAxioms : List ELAxiom := [
  .sub1 (iri "A") (iri "B"),
  .sub1 (iri "B") (iri "C"),
  .sub2 (iri "B") (iri "C") (iri "D"),
  .existR (iri "D") (iri "r1") (iri "E"),
  .existR (iri "E") (iri "r2") (iri "F"),
  .roleSub (iri "r1") (iri "r1p"),
  .roleChain (iri "r1p") (iri "r2") (iri "s"),
  .existL (iri "s") (iri "F") (iri "G"),
  .roleRefl (iri "reflR"),
  .existL (iri "reflR") (iri "G") (iri "H"),
  -- Unsatisfiable class propagated via CR5
  .sub2 (iri "BadLeaf") (iri "BadLeaf") nothing,
  .existR (iri "BadParent") (iri "r1") (iri "BadLeaf")
]

private def richClasses : List IRI :=
  ["A", "B", "C", "D", "E", "F", "G", "H", "BadLeaf", "BadParent"].map iri

#guard
  match classifyFastELToHierarchy richELAxioms richClasses 4,
        classifyELSinglePass richELAxioms richClasses with
  | some hf, some hs =>
    hf.consistent == true && hs.consistent == true &&
    hf.unsatisfiable.length == 2 &&
    hf.unsatisfiable.contains (iri "BadLeaf") &&
    hf.unsatisfiable.contains (iri "BadParent") &&
    -- Exact pair-by-pair agreement with reference single-pass EL++ classifier
    hf.subsumptions.all (fun p => hs.subsumptions.contains p) &&
    hs.subsumptions.all (fun p => hf.subsumptions.contains p) &&
    -- Key multi-hop inferences (CR1 -> CR2 -> CR3 -> CR10 -> CR11 -> CR4 -> CRRefl -> CR4)
    hf.subsumptions.contains (iri "A", iri "G") &&
    hf.subsumptions.contains (iri "A", iri "H") &&
    !hf.subsumptions.contains (iri "G", iri "A")
  | _, _ => false

-- 2. Inconsistent EL++ ontology detection (Thing ⊑ Nothing)
private def inconsELAxioms : List ELAxiom := [
  .sub1 thing (iri "X"),
  .sub1 (iri "X") nothing
]

#guard
  match classifyFastEL inconsELAxioms [iri "X"] 4 with
  | some ch => ch.consistent == false && ch.unsatisfiable.size == 1
  | none => false

-- 3. Equivalence classes and direct-parent transitive reduction
private def equivELAxioms : List ELAxiom := [
  .sub1 (iri "P") (iri "Q"),
  .sub1 (iri "Q") (iri "P"),
  .sub1 (iri "Child") (iri "P"),
  .sub1 (iri "P") (iri "Root"),
  .sub1 (iri "Child") (iri "Root")
]

private def equivClasses : List IRI := ["Root", "P", "Q", "Child"].map iri

#guard
  match classifyFastELToHierarchy equivELAxioms equivClasses 2 with
  | some h =>
    h.consistent == true &&
    h.unsatisfiable.isEmpty &&
    h.equivalences.length == 3 &&
    -- Child's direct parents are {P, Q}, NOT Root (reduced transitively)
    (match h.directParents.find? (fun (c, _) => c == iri "Child") with
     | some (_, ps) => ps.contains (iri "P") && ps.contains (iri "Q") && !ps.contains (iri "Root")
     | none => false)
  | none => false

-- 4. Multi-worker parallel threshold (> 256 classes) agreement between 1 and 8 workers
private def genLargeEL (n : Nat) : List ELAxiom × List IRI := Id.run do
  let mut axs : Array ELAxiom := #[]
  let mut cls : Array IRI := #[]
  for i in [0:n] do
    cls := cls.push (iri s!"C{i}")
  for i in [1:n] do
    let parent := (i - 1) / 2
    axs := axs.push (.sub1 (iri s!"C{i}") (iri s!"C{parent}"))
    if i % 16 == 0 && i ≥ 16 then
      axs := axs.push (.existR (iri s!"C{i}") (iri "partOf") (iri s!"C{i - 16}"))
  axs := axs.push (.existL (iri "partOf") (iri "C0") (iri "HasRootPart"))
  cls := cls.push (iri "HasRootPart")
  return (axs.toList, cls.toList)

#guard
  let (axs, cls) := genLargeEL 320
  match classifyFastEL axs cls 1, classifyFastEL axs cls 8 with
  | some h1, some h8 =>
    let cnt1 := h1.superClasses.foldl (fun a b => a + b.size) 0
    let cnt8 := h8.superClasses.foldl (fun a b => a + b.size) 0
    h1.consistent == true && h8.consistent == true &&
    h1.classes.size == 321 && h8.classes.size == 321 &&
    h1.unsatisfiable.isEmpty && h8.unsatisfiable.isEmpty &&
    cnt1 == cnt8 &&
    -- C32 -> partOf C16 -> ... -> C0, so C32 ⊑ HasRootPart via CR3 + CR1 + CR4!
    (match classifyFastELCore axs cls 8 with
     | some (t, cert, _) =>
       cert.decidesSub t (iri "C32") (iri "HasRootPart") == some true &&
       cert.decidesSub t (iri "C0") (iri "HasRootPart") == some false
     | none => false)
  | _, _ => false

end SabrinaTests.FastELTests
