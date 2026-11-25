#!/usr/bin/env python3
"""Benchmark certified fast classification (single-pass EL++ and Enhanced Traversal SROIQ(D))."""

from __future__ import annotations

import json
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
QUERY_BIN = ROOT / ".lake" / "build" / "bin" / "sabrina-query"


def gen_el_hierarchy(n_classes: int) -> str:
    lines = ["Prefix(:=<http://bench.example/>)", "Ontology(<http://bench.example/el>"]
    for i in range(n_classes):
        lines.append(f"Declaration(Class(:C{i}))")
    lines.append("Declaration(ObjectProperty(:partOf))")
    # Tree of depth ~log2(n) + existential links
    for i in range(1, n_classes):
        parent = (i - 1) // 2
        lines.append(f"SubClassOf(:C{i} :C{parent})")
        if i % 10 == 0 and i >= 10:
            lines.append(f"SubClassOf(:C{i} ObjectSomeValuesFrom(:partOf :C{i - 10}))")
    lines.append(")")
    return "\n".join(lines)


def gen_sroiqd_taxonomy(n_groups: int) -> str:
    # 4 classes per group (4 * n_groups classes total) with disjoint branches & disjunctions
    lines = ["Prefix(:=<http://bench.example/>)", "Ontology(<http://bench.example/sroiqd>"]
    lines.append("Declaration(Class(:Root))")
    for g in range(n_groups):
        for tag in ("A", "B", "C", "D"):
            lines.append(f"Declaration(Class(:{tag}{g}))")
        lines.append(f"SubClassOf(:A{g} :Root)")
        lines.append(f"SubClassOf(:B{g} :A{g})")
        lines.append(f"SubClassOf(:C{g} :A{g})")
        lines.append(f"DisjointClasses(:B{g} :C{g})")
        lines.append(f"SubClassOf(:D{g} ObjectUnionOf(:B{g} :C{g}))")
    lines.append(")")
    return "\n".join(lines)


def run_classify(ont_id: str, ofn: str) -> tuple[dict, float]:
    req = json.dumps(["sabrina-classify-v1", ont_id, ofn])
    t0 = time.perf_counter()
    proc = subprocess.run([str(QUERY_BIN)], input=req, text=True, capture_output=True, check=True)
    dt = time.perf_counter() - t0
    return json.loads(proc.stdout), dt


def main() -> None:
    print("=== [1] Single-Pass Polynomial EL++ Classification ===")
    for n in (50, 150, 300):
        ofn = gen_el_hierarchy(n)
        out, dt = run_classify(f"el-{n}", ofn)
        cls = out["classification"]
        assert out["verdict"] == "CLASSIFIED" and out["lean_verified"] is True
        print(
            f"  EL++ {n:3d} classes ({n*n:6d} pairs): {dt*1000:7.1f}ms | "
            f"subsumptions={len(cls['subsumptions'])} | unsat={len(cls['unsatisfiable'])}"
        )

    print("\n=== [2] Enhanced Traversal + Model-Seeded SROIQ(D) Classification ===")
    for groups in (5, 10):
        n = 1 + 4 * groups
        ofn = gen_sroiqd_taxonomy(groups)
        out, dt = run_classify(f"sroiqd-{n}", ofn)
        cls = out["classification"]
        assert out["verdict"] == "CLASSIFIED" and out["lean_verified"] is True
        print(
            f"  SROIQ(D) {n:2d} classes ({n*n:4d} pairs): {dt*1000:7.1f}ms | "
            f"subsumptions={len(cls['subsumptions'])} | unsat={len(cls['unsatisfiable'])}"
        )

    print("\nALL FAST CLASSIFICATION BENCHMARKS PASSED!")


if __name__ == "__main__":
    main()
