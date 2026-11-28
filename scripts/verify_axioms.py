#!/usr/bin/env python3
"""Standalone foundational-axiom and zero-sorry audit for LogicCore + SABRINA."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

HEADLINE_MODULES = [
    "Logic",
    "Sabrina",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence",
    "Sabrina.OWL2.Datatypes.XMLCorrespondence",
    "Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence",
    "Sabrina.OWL2.RDF.Graph",
    "Sabrina.OWL2.RDF.OWLMapping",
    "Sabrina.OWL2.SROIQD.Termination.ExtendedQueryDecision",
    "Sabrina.OWL2.Classification",
    "Sabrina.OWL2.FastEL",
    "Sabrina.OWL2.FastCB",
    "Sabrina.OWL2.FastClassification",
    "Sabrina.OWL2.Materialize",
    "Sabrina.OWL2.Justification",
    "Sabrina.OWL2.FastLocality",
    "Sabrina.OWL2.SROIQD.Termination.ObjectHierarchyBoundary",
    "Sabrina.OWL2.SROIQD.Termination.RegularObjectDecision",
    "Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLDecision",
    "Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLExamples",
    "Sabrina.OWL2.SWRL",
    "Sabrina.OWL2.SWRLBuiltins",
    "Sabrina.OWL2.SWRLReduction",
]

HEADLINE_THEOREMS = [
    "Sabrina.OWL2.SROIQD.Termination.BlockedForest.decideSROIQBool_ontology_iff",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarOntology_sat_iff",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarOntology_writtenRegular",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarSubclass_entails_iff",
    "Sabrina.OWL2.RoleHierarchy.Unified.decideRegularOWL2DLReal_ontology_iff",
    "Sabrina.OWL2.StrictOWL2DL.checkStrictOWL2DL_iff",
    "Sabrina.OWL2.StrictOWL2DL.diagnoseStrictOWL2DL_isNone_iff",
    "Sabrina.OWL2.StrictOWL2DL.decideStrictOWL2DLReal_iff",
    "Sabrina.OWL2.StrictTyping.checkTyping_iff",
    "Sabrina.OWL2.StrictTyping.diagnoseTyping_isNone_iff",
    "Sabrina.OWL2.StrictTyping.checkStrictTypedOWL2DL_iff",
    "Sabrina.OWL2.StrictTyping.diagnoseStrictTypedOWL2DL_isNone_iff",
    "Sabrina.OWL2.StrictTyping.decideStrictTypedOWL2DLReal_iff",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence.parseHexBinary_iff",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence.parseHexBinary_encodeHex",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence.roundTiesEven_iff",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence.parseDateTime_valid",
    "Sabrina.OWL2.Datatypes.StandardsCorrespondence.matchesLangRange_iff",
    "Sabrina.OWL2.Datatypes.XMLCorrespondence.renderExcC14N_simpleText_canonical",
    "Sabrina.OWL2.Datatypes.XMLCorrespondence.excC14N_normative_correspondence",
    "Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence.GrammarRegExp.compile_matches_iff",
    "Sabrina.OWL2.Datatypes.RegexGrammarCorrespondence.matchesPattern_denotes_iff",
    "Sabrina.OWL2.RDF.parseRDFList_encodeRDFListWith",
    "Sabrina.OWL2.RDF.OWLMapping.owl2_rdf_mapping_roundtrip_correspondence",
    "Sabrina.OWL2.SROIQD.Termination.ExtendedQuery.counterexample_branches_sat_iff",
    "Sabrina.OWL2.SROIQD.Termination.ExtendedQuery.classifyExtendedQueryWith_sound",
    "Sabrina.OWL2.SROIQD.Termination.ExtendedQuery.decideRealExtendedQuery_sound",
    "Sabrina.OWL2.Classification.classifyOntologyWith_sound_complete",
    "Sabrina.OWL2.Classification.classifyOntologyReal_sound_complete",
    "Sabrina.OWL2.Classification.realizeOntologyReal_sound_complete",
    "Sabrina.OWL2.FastEL.allRangePar_iff",
    "Sabrina.OWL2.FastEL.checkCertSound_entails_sub",
    "Sabrina.OWL2.FastEL.checkCertSound_inconsistent",
    "Sabrina.OWL2.FastEL.checkCanonicalModel_sound",
    "Sabrina.OWL2.FastEL.checkCanonicalModel_counter_sub",
    "Sabrina.OWL2.FastEL.classifyFastELCore_sound_complete",
    "Sabrina.OWL2.FastEL.classifyFastELToHierarchy_sound_complete",
    "Sabrina.OWL2.FastCB.extractHornSHIQ_sound",
    "Sabrina.OWL2.FastCB.checkCBSound_holds",
    "Sabrina.OWL2.FastCB.runFastCB_subs_sound",
    "Sabrina.OWL2.FastCB.runFastCB_unsats_sound",
    "Sabrina.OWL2.FastCB.runFastCB_workers_eq",
    "Sabrina.OWL2.FastCB.checkCBCanonicalModel_sound",
    "Sabrina.OWL2.FastCB.checkCBCanonicalModel_counter_sub",
    "Sabrina.OWL2.FastCB.checkCBCanonicalModel_witness_sat",
    "Sabrina.OWL2.FastCB.classifyFastCB_workers_eq",
    "Sabrina.OWL2.FastCB.checkCBPartialModel_sound",
    "Sabrina.OWL2.FastCB.checkCBPartialModel_counter_sub",
    "Sabrina.OWL2.FastCB.checkCBPartialModel_witness_sat",
    "Sabrina.OWL2.FastCB.runFastCBWithPartialModel_workers_eq",
    "Sabrina.OWL2.FastClassification.classifyELSinglePass_sound_complete",
    "Sabrina.OWL2.FastClassification.classifyDirectEL_sound_complete",
    "Sabrina.OWL2.FastClassification.classifyEnhancedWith_sound_complete",
    "Sabrina.OWL2.FastClassification.classifyEnhancedReal_sound_complete",
    "Sabrina.OWL2.FastClassification.harvestModelPairs_sound",
    "Sabrina.OWL2.FastClassification.classifyEnhancedStd_sound_complete",
    "Sabrina.OWL2.Materialize.decidesAxiomEntails_iff",
    "Sabrina.OWL2.Materialize.materializeWith_entailed",
    "Sabrina.OWL2.Materialize.materializeReal_entailed",
    "Sabrina.OWL2.Justification.findOneUnsatJustificationReal_sound",
    "Sabrina.OWL2.Justification.findAllUnsatJustificationsReal_sound",
    "Sabrina.OWL2.Justification.findOneJustificationReal_sound",
    "Sabrina.OWL2.Justification.findAllJustificationsReal_sound",
    "Sabrina.OWL2.Justification.findAllUnsatJustificationsParWith_workers_eq",
    "Sabrina.OWL2.Justification.findAllJustificationsParWith_workers_eq",
    "Sabrina.OWL2.Justification.findAllUnsatJustificationsParReal_sound",
    "Sabrina.OWL2.Justification.findAllJustificationsParReal_sound",
    "Sabrina.OWL2.SROIQD.Concept.absorptionPremises_sound",
    "Sabrina.OWL2.SROIQD.Concept.nominalDisj?_sound",
    "Sabrina.OWL2.SROIQD.Concept.nominalGuard?_sound",
    "Sabrina.OWL2.FastLocality.isBotLocalAxiom_antitone",
    "Sabrina.OWL2.FastLocality.extractBotModule_least",
    "Sabrina.OWL2.FastLocality.extractBotModuleFast_mem_iff",
    "Sabrina.OWL2.FastLocality.extractBotModuleFast_sat_iff",
    "Sabrina.OWL2.FastLocality.extractBotModuleFast_entails_iff",
    "Sabrina.OWL2.RDF.OWLMapping.owl2_rdf_swrl_roundtrip",
    "Sabrina.OWL2.SWRL.modelsWithRules_nil_iff",
    "Sabrina.OWL2.SWRL.atomHolds_subst_iff",
    "Sabrina.OWL2.SWRL.atomHolds_ground_irrel",
    "Sabrina.OWL2.SWRL.satisfiesDLSafeRule_ground_instance",
    "Sabrina.OWL2.SWRL.evalBuiltinRel_of_output",
    "Sabrina.OWL2.SWRL.builtinToDataRange_equal_iff",
    "Sabrina.OWL2.SWRL.builtinToDataRange_notEqual_iff",
    "Sabrina.OWL2.SWRL.builtinToDataRange_real_iff",
    "Sabrina.OWL2.SWRL.encodeGroundAtom_holds_iff",
    "Sabrina.OWL2.SWRL.encodeGroundRule_holds_iff",
    "Sabrina.OWL2.SWRL.encodeSingleIndGroundRule_holds_iff",
    "Sabrina.OWL2.SWRL.encodeUnaryRule_holds_iff",
    "Sabrina.OWL2.SWRL.rollupOneIndVar_holds_iff",
    "Sabrina.OWL2.SWRL.rollupLocalIndVars_holds_iff",
    "Sabrina.OWL2.SWRL.groundRuleAll_holds_iff",
    "Sabrina.OWL2.SWRL.encodeDLSafeRule_holds_iff",
    "Sabrina.OWL2.SWRL.groundAllRules_holds_iff",
    "Sabrina.OWL2.SWRL.groundAllRules_sat_iff",
    "Sabrina.OWL2.SWRL.groundAllRules_entails_iff",
    "Sabrina.OWL2.SWRL.rollupOneDataVar_holds_iff",
    "Sabrina.OWL2.SWRL.decideRealWithSWRL_iff",
]


def strip_lean_comments(text: str) -> str:
    """Remove Lean line comments (--) and nested block comments (/- ... -/) while preserving newlines."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0 and text[i:i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def scan_source() -> list[str]:
    violations: list[str] = []
    for pkg in ("packages/logic-core", "packages/sabrina"):
        for p in sorted((ROOT / pkg).rglob("*.lean")):
            if ".lake" in p.parts:
                continue
            cleaned = strip_lean_comments(p.read_text(encoding="utf-8"))
            for idx, line in enumerate(cleaned.splitlines(), 1):
                stripped = line.strip()
                if re.search(r"\b(?:sorry|admit)\b", stripped):
                    violations.append(f"{p.relative_to(ROOT)}:{idx}: contains sorry/admit")
                if re.match(r"^(?:private\s+|protected\s+)?axiom\s+", stripped):
                    violations.append(f"{p.relative_to(ROOT)}:{idx}: declares custom axiom")
    return violations


def check_kernel_axioms() -> list[str]:
    imports = "\n".join(f"import {m}" for m in ("Lean", *HEADLINE_MODULES))
    theorems = ", ".join(f"`{name}" for name in HEADLINE_THEOREMS)
    allowed = ", ".join(f"`{name}" for name in sorted(ALLOWED_AXIOMS))
    source = f"""{imports}

open Lean Elab Command

run_cmd do
  let allowed : List Name := [{allowed}]
  for name in ([{theorems}] : List Name) do
    unless (← getEnv).contains name do
      logError m!"Unknown declaration: {{name}}"
      continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun axiomName => !allowed.contains axiomName)
    if unexpected.isEmpty then
      logInfo m!"{{name}} depends on {{axioms}}"
    else
      logError m!"{{name}} depends on non-standard axioms: {{unexpected}}"
"""
    cmd = ["lake", "env", "lean", "--stdin"]
    proc = subprocess.run(cmd, input=source, cwd=ROOT, text=True, capture_output=True)
    if proc.returncode != 0:
        return [f"lean kernel axiom check failed:\n{proc.stderr}\n{proc.stdout}"]
    print(proc.stdout, end="")
    return []


def main() -> int:
    print("[1/2] Scanning all Lean source files for sorry/admit/custom axioms...")
    src_err = scan_source()
    if src_err:
        for e in src_err:
            print("ERROR:", e)
        return 1
    print("  OK: zero sorry/admit/custom axioms across LogicCore and SABRINA.")

    print("[2/2] Auditing Lean 4 kernel axiom dependencies for headline theorems...")
    ax_err = check_kernel_axioms()
    if ax_err:
        for e in ax_err:
            print("ERROR:", e)
        return 1
    print("  OK: strictly standard Lean core axioms (propext, Classical.choice, Quot.sound).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
