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
    "Sabrina.OWL2.SROIQD.Termination.ObjectHierarchyBoundary",
    "Sabrina.OWL2.SROIQD.Termination.RegularObjectDecision",
    "Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLDecision",
    "Sabrina.OWL2.SROIQD.Termination.RegularOWL2DLExamples",
]

HEADLINE_THEOREMS = [
    "Sabrina.OWL2.SROIQD.Termination.BlockedForest.decideSROIQBool_ontology_iff",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarOntology_sat_iff",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarOntology_writtenRegular",
    "Sabrina.OWL2.RoleHierarchy.GrammarBoundary.grammarSubclass_entails_iff",
    "Sabrina.OWL2.RoleHierarchy.Unified.decideRegularOWL2DLReal_ontology_iff",
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
