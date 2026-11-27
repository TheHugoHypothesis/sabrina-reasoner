#!/usr/bin/env python3
"""Benchmark kernel-verified Horn-SHIQ consequence-based classification at 1k–50k classes."""

from __future__ import annotations

import json
import resource
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
QUERY_BIN = ROOT / ".lake" / "build" / "bin" / "sabrina-query"


def gen_horn_shiq_tbox(n_classes: int, path: Path) -> int:
    """Generate an expressive non-EL pure Horn-SHIQ ontology featuring:
       - Transitive object property (:partOf) + universal restriction (:Root ⊑ ∀partOf.:Tagged)
       - Functional object property (:hasCore) triggering sibling merges
       - Inverse object properties (:hasPart ≡ :partOf⁻) + inverse universal (:Core ⊑ ∀hasCore⁻.:HasCoreOwner)
       - Domain & range axioms
       - Disjoint classes + unsatisfiable class detection (:UnsatSeed)
       - Multi-level DAG taxonomy with conjunction and existential axioms
    """
    lines = [
        "Prefix(:=<http://bench.hornshiq.example/>)",
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)",
        "Ontology(<http://bench.hornshiq.example/shiq>",
        "  TransitiveObjectProperty(:partOf)",
        "  FunctionalObjectProperty(:hasCore)",
        "  InverseObjectProperties(:hasPart :partOf)",
        "  ObjectPropertyDomain(:hasCore :System)",
        "  ObjectPropertyRange(:hasCore :Core)",
        "  SubClassOf(:Root :System)",
        "  SubClassOf(:Root ObjectAllValuesFrom(:partOf :Tagged))",
        "  SubClassOf(:Core ObjectAllValuesFrom(ObjectInverseOf(:hasCore) :HasCoreOwner))",
        "  DisjointClasses(:DisjA :DisjB)",
        "  SubClassOf(:UnsatSeed ObjectIntersectionOf(:DisjA :DisjB))",
    ]
    n_axioms = 10
    n_groups = n_classes // 5
    for i in range(n_groups):
        a, b, c, d, e = f":A{i}", f":B{i}", f":C{i}", f":D{i}", f":E{i}"
        lines.append(f"  SubClassOf({a} :Root)")
        lines.append(f"  SubClassOf({a} ObjectSomeValuesFrom(:hasCore {b}))")
        lines.append(f"  SubClassOf({a} ObjectSomeValuesFrom(:hasCore {c}))")
        lines.append(f"  SubClassOf(ObjectIntersectionOf({b} {c}) {d})")
        lines.append(f"  SubClassOf(ObjectSomeValuesFrom(:hasCore {d}) {e})")
        n_axioms += 5
        if i % 10 == 0:
            lines.append(f"  SubClassOf({a} ObjectSomeValuesFrom(:partOf {b}))")
            lines.append(f"  SubClassOf(ObjectIntersectionOf({b} :Tagged) {c})")
            n_axioms += 2
        if i > 0 and i % 4 != 0:
            lines.append(f"  SubClassOf({a} :E{i - 1})")
            n_axioms += 1
    lines.append(")")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return n_axioms


def run_bench(path: Path, workers: int) -> tuple[dict, float, float]:
    t0 = time.perf_counter()
    proc = subprocess.run(
        [str(QUERY_BIN), "--classify", str(path), "--summary-only", "--workers", str(workers)],
        text=True,
        capture_output=True,
        check=True,
    )
    dt = time.perf_counter() - t0
    rss_mb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024.0
    return json.loads(proc.stdout), dt, rss_mb


def main() -> None:
    print("=== Kernel-Verified Horn-SHIQ Consequence-Based Scale Benchmark (1k → 50k classes) ===")
    with tempfile.TemporaryDirectory(prefix="sabrina-cb-bench-") as tmp:
        tmp_dir = Path(tmp)
        for n in (1_000, 5_000, 10_000, 25_000, 50_000):
            ofn_path = tmp_dir / f"horn_shiq_{n}.ofn"
            t_gen = time.perf_counter()
            n_ax = gen_horn_shiq_tbox(n, ofn_path)
            gen_dt = time.perf_counter() - t_gen
            size_mb = ofn_path.stat().st_size / (1024 * 1024)
            worker_list = [1, 8] if n == 10_000 else [8]
            for w in worker_list:
                out, dt, _ = run_bench(ofn_path, w)
                assert out["verdict"] == "CLASSIFIED" and out["lean_verified"] is True, out
                s = out["classification_summary"]
                assert s["consistent"] is True and s["unsatisfiable_count"] == 1, s
                print(
                    f"  N={s['class_count']:6,d} cls | {n_ax:7,d} ax ({size_mb:5.1f} MB, gen {gen_dt:.2f}s) | "
                    f"w={w} | wall={dt:6.2f}s | subs={s['subsumption_count']:8,d} | "
                    f"direct={s['direct_parent_edges']:7,d} | unsat={s['unsatisfiable_count']}"
                )
    print("\nALL HORN-SHIQ SCALE BENCHMARKS PASSED!")


if __name__ == "__main__":
    main()
