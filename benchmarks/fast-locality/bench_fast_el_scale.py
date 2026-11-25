#!/usr/bin/env python3
"""Benchmark kernel-verified parallel EL++ classification at 1k–350k classes (SNOMED CT scale)."""

from __future__ import annotations

import json
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
QUERY_BIN = ROOT / ".lake" / "build" / "bin" / "sabrina-query"


def gen_snomed_like_el(n_classes: int, path: Path) -> int:
    """Generate a realistic SNOMED-CT-like EL++ ontology with:
       - DAG taxonomy (depth ~log2(n), avg 1.3 direct parents)
       - Existential restrictions (findingSite / associatedMorphology / partOf)
       - Conjunction definitions (Defined_i ≡ Parent ⊓ ∃partOf.Target)
       - Role hierarchy + transitive role chain (findingSite ∘ partOf ⊑ findingSite)
    """
    lines = [
        "Prefix(:=<http://bench.snomed.example/>)",
        "Ontology(<http://bench.snomed.example/el>",
        "Declaration(ObjectProperty(:partOf))",
        "Declaration(ObjectProperty(:findingSite))",
        "Declaration(ObjectProperty(:hasPartOf))",
        "SubObjectPropertyOf(:hasPartOf :partOf)",
        "SubObjectPropertyOf(ObjectPropertyChain(:findingSite :partOf) :findingSite)",
        "Declaration(Class(:RootFinding))",
        "SubClassOf(ObjectSomeValuesFrom(:findingSite :C0) :RootFinding)",
    ]
    n_axioms = 3
    for i in range(n_classes):
        lines.append(f"Declaration(Class(:C{i}))")
    for i in range(1, n_classes):
        p1 = (i - 1) // 2
        lines.append(f"SubClassOf(:C{i} :C{p1})")
        n_axioms += 1
        # Secondary DAG parent on 20% of classes
        if i >= 7 and i % 5 == 0:
            p2 = (i - 3) // 2
            if p2 != p1:
                lines.append(f"SubClassOf(:C{i} :C{p2})")
                n_axioms += 1
        # Existential role links on 15% of classes
        if i >= 20 and i % 7 == 0:
            tgt = (i // 3)
            role = ":findingSite" if (i % 14 == 0) else ":hasPartOf"
            lines.append(f"SubClassOf(:C{i} ObjectSomeValuesFrom({role} :C{tgt}))")
            n_axioms += 1
        # Conjunction GCI on 5% of classes
        if i >= 40 and i % 20 == 0:
            lines.append(
                f"SubClassOf(ObjectIntersectionOf(:C{p1} ObjectSomeValuesFrom(:partOf :C{i // 4})) :C{p1 // 2})"
            )
            n_axioms += 1
    lines.append(")")
    path.write_text("\n".join(lines), encoding="utf-8")
    return n_axioms


def run_bench(path: Path, workers: int) -> tuple[dict, float]:
    t0 = time.perf_counter()
    proc = subprocess.run(
        [str(QUERY_BIN), "--classify", str(path), "--summary-only", "--workers", str(workers)],
        text=True,
        capture_output=True,
        check=True,
    )
    dt = time.perf_counter() - t0
    return json.loads(proc.stdout), dt


def main() -> None:
    print("=== Kernel-Verified Parallel EL++ Scale Benchmark (1k → 350k classes) ===")
    with tempfile.TemporaryDirectory(prefix="sabrina-el-bench-") as tmp:
        tmp_dir = Path(tmp)
        for n in (1_000, 10_000, 50_000, 100_000, 350_000):
            ofn_path = tmp_dir / f"snomed_{n}.ofn"
            t_gen = time.perf_counter()
            n_ax = gen_snomed_like_el(n, ofn_path)
            gen_dt = time.perf_counter() - t_gen
            size_mb = ofn_path.stat().st_size / (1024 * 1024)
            # Run with 8 workers (and 1 worker on 10k/50k for speedup comparison)
            worker_list = [1, 8] if n in (10_000, 50_000) else [8]
            for w in worker_list:
                out, dt = run_bench(ofn_path, w)
                assert out["verdict"] == "CLASSIFIED" and out["lean_verified"] is True, out
                s = out["classification_summary"]
                assert s["engine"] == "fast-el-parallel", s
                assert s["consistent"] is True and s["unsatisfiable_count"] == 0, s
                print(
                    f"  N={n:7,d} cls | {n_ax:7,d} ax ({size_mb:5.1f} MB, gen {gen_dt:.2f}s) | "
                    f"w={w} | wall={dt:6.2f}s | subs={s['subsumption_count']:9,d} | "
                    f"direct={s['direct_parent_edges']:7,d} | equivs={s['equivalence_count']:7,d}"
                )
    print("\nALL PARALLEL EL++ SCALE BENCHMARKS PASSED!")


if __name__ == "__main__":
    main()
