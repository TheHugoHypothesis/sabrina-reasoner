#!/usr/bin/env python3
"""SNOMED-scale (up to 350,000 axioms) benchmark for hash-indexed bot-locality extraction."""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
QUERY_BIN = ROOT / ".lake" / "build" / "bin" / "sabrina-query"
SESSION_BIN = ROOT / ".lake" / "build" / "bin" / "sabrina-session"


def gen_clinical_ofn(n_axioms: int, add_sroiqd: bool = False) -> tuple[str, int]:
    """Generate a synthetic SNOMED-CT-scale clinical ontology with `n_axioms` axioms.

    Organized into 500 clinical sub-hierarchies (chains of SubClassOf + ObjectSomeValuesFrom
    definitions) so queries over a target concept extract a realistic small module while
    forcing the locality extractor to scan and certify all `n_axioms` axioms.
    """
    lines = [
        "Prefix(:=<http://snomed.example/>)",
        "Ontology(<http://snomed.example/snomed-synth>",
    ]
    n_groups = 500
    per_group = n_axioms // n_groups
    count = 0
    for g in range(n_groups):
        for i in range(per_group):
            # Make chain length 15 segments separated by existential role links
            if i % 15 == 14:
                lines.append(f"SubClassOf(:C_{g}_{i} ObjectSomeValuesFrom(:r_{g % 50} :C_{g}_{i - 1}))")
            else:
                lines.append(f"SubClassOf(:C_{g}_{i + 1} :C_{g}_{i})")
            count += 1
    if add_sroiqd:
        lines.append(
            "SubClassOf(:ExpressiveA ObjectUnionOf(:ExpressiveB ObjectMinCardinality(2 :k :ExpressiveC)))"
        )
        count += 1
    lines.append(")")
    return "\n".join(lines), count


def bench_cold_query() -> None:
    print("=== [1] Cold End-to-End sabrina-query (OFN Parse + FastLocality + EL++ Proof) ===")
    for n in (10_000, 100_000, 350_000):
        ofn, cnt = gen_clinical_ofn(n, add_sroiqd=False)
        query = "SubClassOf(:C_42_12 :C_42_0)"
        req = json.dumps(["sabrina-ofn-query-v1", f"snomed-{cnt}", ofn, query])
        t0 = time.perf_counter()
        proc = subprocess.run(
            [str(QUERY_BIN)], input=req, text=True, capture_output=True, check=False
        )
        dt = time.perf_counter() - t0
        if proc.returncode != 0:
            print(f"FAIL n={cnt}: rc={proc.returncode} stderr={proc.stderr[:400]}")
            sys.exit(1)
        out = json.loads(proc.stdout)
        prof = out.get("profile", {})
        verdict = out.get("verdict")
        verified = out.get("lean_verified")
        mod_ax = prof.get("module_axioms")
        engine = prof.get("engine_used")
        print(
            f"  n={cnt:7d} axioms | total={dt:6.3f}s | verdict={verdict} "
            f"| verified={verified} | module={mod_ax} axioms | engine={engine}"
        )
        assert verdict == "ENTAILED", f"Expected ENTAILED, got {verdict}"
        assert verified is True, "Expected lean_verified=True"
        assert mod_ax is not None and mod_ax <= 20, f"Unexpected module size {mod_ax}"


def bench_warm_session() -> None:
    print("\n=== [2] Persistent sabrina-session (350,001 SROIQ(D) axioms, Cached LocalityIndex) ===")
    ofn, cnt = gen_clinical_ofn(350_000, add_sroiqd=True)
    proc = subprocess.Popen(
        [str(SESSION_BIN)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert proc.stdin is not None and proc.stdout is not None

    def send(obj: dict) -> tuple[dict, float]:
        t0 = time.perf_counter()
        proc.stdin.write(json.dumps(obj) + "\n")
        proc.stdin.flush()
        line = proc.stdout.readline()
        dt = time.perf_counter() - t0
        if not line:
            err = proc.stderr.read() if proc.stderr else ""
            raise RuntimeError(f"sabrina-session exited early: {err}")
        return json.loads(line), dt

    resp, load_dt = send({"cmd": "load_tbox", "id": "snomed-350k", "ofn": ofn})
    print(
        f"  load_tbox ({cnt} axioms): {load_dt:.3f}s | ok={resp.get('ok')} "
        f"| fragment={resp.get('fragment')} | mode={resp.get('mode')}"
    )
    assert resp.get("ok") is True, f"load_tbox failed: {resp}"

    query_times: list[float] = []
    for g in (10, 42, 123, 250, 499):
        q = f"SubClassOf(:C_{g}_5 :C_{g}_0)"
        qresp, qdt = send({"cmd": "query", "ofn": q})
        query_times.append(qdt)
        print(
            f"  warm query group={g:3d}: {qdt * 1000:6.1f}ms | verdict={qresp.get('verdict')} "
            f"| verified={qresp.get('lean_verified')} | module={qresp.get('module_axioms')} axioms"
        )
        assert qresp.get("verdict") == "ENTAILED", f"Unexpected query verdict: {qresp}"
        assert qresp.get("lean_verified") is True

    send({"cmd": "quit"})
    proc.wait(timeout=10)
    avg_ms = (sum(query_times) / len(query_times)) * 1000
    print(f"  => Mean warm query (350k-axiom cached extraction + SROIQ(D) proof): {avg_ms:.1f}ms")
    assert avg_ms < 1000.0, f"Expected sub-second warm extraction+query, got {avg_ms:.1f}ms"


if __name__ == "__main__":
    bench_cold_query()
    bench_warm_session()
    print("\nALL SNOMED-SCALE (350,000-AXIOM) BENCHMARKS PASSED!")
