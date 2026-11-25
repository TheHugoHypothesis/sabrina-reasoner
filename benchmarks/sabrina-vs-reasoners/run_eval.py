#!/usr/bin/env python3
"""SABRINA vs. HermiT 1.4.5 & ELK 0.6.0 Controlled Runtime Benchmark Suite.

Runs four reproducible benchmark tracks comparing:
  - SABRINA (Lean 4 compiled native binaries: cold `sabrina-query` & warm `sabrina-session`)
  - HermiT 1.4.5.519 (OWL API 5.1.20: cold JVM & warm JVM)
  - ELK 0.6.0 (OWL API 5.1.20: cold JVM & warm JVM; EL++ profile)

Tracks:
  1. Normative BFO 2020 Core Ontology (bfo-core.ofn, 192 axioms) & domain extensions (30 queries)
  2. Expressive SROIQ(D) Reasoning (24 queries: role chains, inverses, nominals, cardinality, HasKey, datatypes)
  3. EL++ Scaling & Syntactic bot-Locality Benchmark (N = 50, 100, 250, 500, 1000 axioms)
  4. Incremental ABox Assertion & Retraction (DRed): 10 multi-turn sessions (27 checkpoints) + 50-step stress session
"""

from __future__ import annotations

import argparse
import json
import platform
import statistics
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

BENCH_DIR = Path(__file__).resolve().parent
JAVA_DIR = BENCH_DIR / "java-harness"
WORKLOAD_DIR = BENCH_DIR / "workloads"
BFO_CORE_OFN_PATH = BENCH_DIR.parent / "data" / "bfo-core.ofn"

from sabrina_cli import (  # noqa: E402
    SabrinaSession,
    find_sabrina_binary,
    inject_ofn_extension,
    run_ofn_query,
)


class JavaHarnessDaemon:
    """Persistent warm-JVM driver for HermiT 1.4.5 and ELK 0.6.0."""

    def __init__(self, classpath: str) -> None:
        self.classpath = classpath
        self.cmd = [
            "java",
            "--add-opens",
            "java.base/java.lang=ALL-UNNAMED",
            "-cp",
            classpath,
            "bench.ReasonerHarness",
        ]
        self._proc = subprocess.Popen(
            self.cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
        )
        ping = self.send({"cmd": "ping"})
        if not ping.get("ok"):
            raise RuntimeError(f"Java harness failed to start: {ping}")
        self.java_version = ping.get("java", "unknown")

    def send(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        assert self._proc.stdin is not None and self._proc.stdout is not None
        self._proc.stdin.write(json.dumps(payload) + "\n")
        self._proc.stdin.flush()
        line = self._proc.stdout.readline()
        if not line:
            raise RuntimeError("Java harness terminated unexpectedly")
        return json.loads(line)

    def warmup(self, bfo_ofn: str, n_iters: int = 5) -> None:
        for _ in range(n_iters):
            self.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "hermit",
                    "ofn": bfo_ofn,
                    "source_iri": "http://purl.obolibrary.org/obo/BFO_0000030",
                    "target_iri": "http://purl.obolibrary.org/obo/BFO_0000002",
                    "mode": "3val",
                }
            )
            self.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "elk",
                    "ofn": "Prefix(:=<urn:warm#>)\nOntology(SubClassOf(:A :B) SubClassOf(:B :C))",
                    "source_iri": "urn:warm#A",
                    "target_iri": "urn:warm#C",
                    "mode": "3val",
                }
            )

    def close(self) -> None:
        if self._proc.poll() is None:
            try:
                self.send({"cmd": "quit"})
            except Exception:
                pass
            try:
                self._proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._proc.kill()


def run_java_oneshot(classpath: str, payload: Dict[str, Any]) -> Tuple[Dict[str, Any], float]:
    """Measure true cold JVM startup + OWL API parse + reasoning wall-clock time."""
    t0 = time.perf_counter()
    proc = subprocess.run(
        [
            "java",
            "--add-opens",
            "java.base/java.lang=ALL-UNNAMED",
            "-cp",
            classpath,
            "bench.ReasonerHarness",
            "--oneshot",
        ],
        input=json.dumps(payload) + "\n",
        capture_output=True,
        text=True,
        timeout=60,
    )
    wall_ms = (time.perf_counter() - t0) * 1000.0
    if proc.returncode != 0 or not proc.stdout.strip():
        return {"ok": False, "verdict": "ERROR", "error": proc.stderr.strip()}, wall_ms
    return json.loads(proc.stdout.strip().splitlines()[-1]), wall_ms


def run_sabrina_cold_3val(
    ofn_text: str,
    source_iri: str,
    target_iri: str,
    *,
    mode: str = "3val",
) -> Dict[str, Any]:
    """Run SABRINA single-shot native Lean binary (`sabrina-query`)."""
    t0 = time.perf_counter()
    sub_q = f"SubClassOf(<{source_iri}> <{target_iri}>)"
    _, res_sub = run_ofn_query(ofn_text=ofn_text, query_ofn=sub_q)
    sub_v = res_sub.get("verdict", "UNKNOWN")
    profile = res_sub.get("profile") or {}
    lean_verified = bool(res_sub.get("lean_verified"))

    if mode == "subclass":
        wall_ms = (time.perf_counter() - t0) * 1000.0
        verdict = "ENTAILED" if sub_v == "ENTAILED" else ("INCONSISTENT" if sub_v == "INCONSISTENT_ONTOLOGY" else "NOT_ENTAILED")
        return {
            "ok": lean_verified,
            "verdict": verdict,
            "raw_verdict": sub_v,
            "lean_verified": lean_verified,
            "total_ms": wall_ms,
            "profile": profile,
            "calls": 1,
        }

    if sub_v == "ENTAILED":
        wall_ms = (time.perf_counter() - t0) * 1000.0
        return {
            "ok": lean_verified,
            "verdict": "PROVABLY_TRUE",
            "lean_verified": lean_verified,
            "total_ms": wall_ms,
            "profile": profile,
            "calls": 1,
        }
    if sub_v == "INCONSISTENT_ONTOLOGY":
        wall_ms = (time.perf_counter() - t0) * 1000.0
        return {
            "ok": lean_verified,
            "verdict": "INCONSISTENT",
            "lean_verified": lean_verified,
            "total_ms": wall_ms,
            "profile": profile,
            "calls": 1,
        }

    disj_q = f"DisjointClasses(<{source_iri}> <{target_iri}>)"
    _, res_disj = run_ofn_query(ofn_text=ofn_text, query_ofn=disj_q)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    disj_v = res_disj.get("verdict", "UNKNOWN")
    both_verified = lean_verified and bool(res_disj.get("lean_verified"))
    if disj_v == "ENTAILED":
        verdict = "PROVABLY_DISJOINT"
    elif disj_v in {"SENTENCE_INDEPENDENT", "REFUTED"} and sub_v in {"SENTENCE_INDEPENDENT", "REFUTED"}:
        verdict = "SENTENCE_INDEPENDENT"
    else:
        verdict = "UNKNOWN"
    return {
        "ok": both_verified,
        "verdict": verdict,
        "lean_verified": both_verified,
        "total_ms": wall_ms,
        "profile": res_disj.get("profile") or profile,
        "calls": 2,
    }


def run_sabrina_warm_3val(
    sess: SabrinaSession,
    ofn_text: str,
    source_iri: str,
    target_iri: str,
    *,
    mode: str = "3val",
    reload_tbox: bool = True,
) -> Dict[str, Any]:
    """Run SABRINA inside persistent `sabrina-session` daemon (zero OS spawn overhead)."""
    t0 = time.perf_counter()
    if reload_tbox:
        load_res = sess.load_tbox(ofn_text=ofn_text)
        if not load_res.get("ok"):
            return {"ok": False, "verdict": "ERROR", "error": load_res.get("error"), "total_ms": (time.perf_counter() - t0) * 1000.0}
    t1 = time.perf_counter()

    sub_q = f"SubClassOf(<{source_iri}> <{target_iri}>)"
    res_sub = sess.query(sub_q)
    sub_v = res_sub.get("verdict", "UNKNOWN")
    lv = bool(res_sub.get("lean_verified"))

    if mode == "subclass":
        t2 = time.perf_counter()
        verdict = "ENTAILED" if sub_v == "ENTAILED" else ("INCONSISTENT" if sub_v == "INCONSISTENT_ONTOLOGY" else "NOT_ENTAILED")
        return {
            "ok": lv,
            "verdict": verdict,
            "lean_verified": lv,
            "load_ms": (t1 - t0) * 1000.0,
            "query_ms": (t2 - t1) * 1000.0,
            "total_ms": (t2 - t0) * 1000.0,
        }

    if sub_v == "ENTAILED":
        t2 = time.perf_counter()
        return {
            "ok": lv,
            "verdict": "PROVABLY_TRUE",
            "lean_verified": lv,
            "load_ms": (t1 - t0) * 1000.0,
            "query_ms": (t2 - t1) * 1000.0,
            "total_ms": (t2 - t0) * 1000.0,
        }
    if sub_v == "INCONSISTENT_ONTOLOGY":
        t2 = time.perf_counter()
        return {
            "ok": lv,
            "verdict": "INCONSISTENT",
            "lean_verified": lv,
            "load_ms": (t1 - t0) * 1000.0,
            "query_ms": (t2 - t1) * 1000.0,
            "total_ms": (t2 - t0) * 1000.0,
        }

    disj_q = f"DisjointClasses(<{source_iri}> <{target_iri}>)"
    res_disj = sess.query(disj_q)
    t2 = time.perf_counter()
    disj_v = res_disj.get("verdict", "UNKNOWN")
    both_lv = lv and bool(res_disj.get("lean_verified"))
    if disj_v == "ENTAILED":
        verdict = "PROVABLY_DISJOINT"
    elif disj_v in {"SENTENCE_INDEPENDENT", "REFUTED"} and sub_v in {"SENTENCE_INDEPENDENT", "REFUTED"}:
        verdict = "SENTENCE_INDEPENDENT"
    else:
        verdict = "UNKNOWN"
    return {
        "ok": both_lv,
        "verdict": verdict,
        "lean_verified": both_lv,
        "load_ms": (t1 - t0) * 1000.0,
        "query_ms": (t2 - t1) * 1000.0,
        "total_ms": (t2 - t0) * 1000.0,
    }


def materialize_item_ofn(item: Dict[str, Any], bfo_text: str) -> str:
    if item.get("preset") == "bfo-core":
        text = bfo_text
    else:
        text = item["ofn"]
    if item.get("extend_ofn"):
        text = inject_ofn_extension(text, item["extend_ofn"])
    return text


def generate_el_scaling_ontology(n_axioms: int) -> Tuple[str, str, str, str, str]:
    """Generate a deterministic modular EL++ biomedical-style ontology of `n_axioms` axioms.

    Structure:
      - Divided into 10 modular clusters (each ~n_axioms/10 axioms) with taxonomy chains,
        conjunction definitions (A ⊓ B ⊑ C), existential restrictions (C ⊑ ∃partOf.D,
        ∃partOf.E ⊑ F), and a transitive partOf role.
      - Returns (ofn_text, local_src, local_tgt, nonent_src, nonent_tgt)
        where local_src ⊑ local_tgt is entailed inside cluster 0 (testing syntactic ⊥-locality!)
        and nonent_src ⋢ nonent_tgt is open.
    """
    lines = [
        "Prefix(:=<http://example.org/elscale#>)",
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)",
        "Ontology(<http://example.org/elscale>",
        "  TransitiveObjectProperty(:partOf)",
    ]
    count = 1
    n_clusters = 10
    per_cluster = max(5, (n_axioms - 1) // n_clusters)

    for c in range(n_clusters):
        # 5-hop backbone with existential + conjunction inside each cluster
        base = f":C{c}_"
        cluster_axioms = [
            f"  SubClassOf({base}0 {base}1)",
            f"  SubClassOf({base}1 ObjectSomeValuesFrom(:partOf {base}2))",
            f"  SubClassOf(ObjectSomeValuesFrom(:partOf {base}2) {base}3)",
            f"  SubClassOf({base}3 {base}4)",
            f"  SubClassOf({base}4 {base}Root)",
        ]
        # Fill remaining axioms in this cluster as branching leaf/existential taxonomy
        idx = 5
        while len(cluster_axioms) < per_cluster and count + len(cluster_axioms) < n_axioms:
            parent = f"{base}{idx - 1}" if idx % 4 != 0 else f"{base}Root"
            if idx % 3 == 0:
                cluster_axioms.append(
                    f"  SubClassOf({base}{idx} ObjectSomeValuesFrom(:partOf {parent}))"
                )
            elif idx % 3 == 1:
                cluster_axioms.append(
                    f"  SubClassOf(ObjectIntersectionOf({base}{idx} {base}1) {parent})"
                )
            else:
                cluster_axioms.append(f"  SubClassOf({base}{idx} {parent})")
            idx += 1
        for ax in cluster_axioms:
            if count >= n_axioms:
                break
            lines.append(ax)
            count += 1

    # Pad if rounding left a few short
    pad = 0
    while count < n_axioms:
        lines.append(f"  SubClassOf(:Pad_{pad} :C9_Root)")
        count += 1
        pad += 1

    lines.append(")")
    ofn_text = "\n".join(lines) + "\n"
    return (
        ofn_text,
        "http://example.org/elscale#C0_0",
        "http://example.org/elscale#C0_Root",
        "http://example.org/elscale#C0_Root",
        "http://example.org/elscale#C0_0",
    )


def generate_dred_stress_session(n_tbox: int = 200) -> Dict[str, Any]:
    """Generate a 50-step incremental ABox assert/query/retract DRed stress session over a 200-axiom EL++ TBox."""
    ofn_text, _, _, _, _ = generate_el_scaling_ontology(n_tbox)
    # Add domain axioms for alternative-justification testing into the TBox
    extra = "\n".join(
        [
            "SubClassOf(:PathA :Target)",
            "SubClassOf(:PathB :Target)",
            "SubClassOf(:LeafA :PathA)",
            "SubClassOf(:LeafB :PathB)",
            "SubClassOf(ObjectSomeValuesFrom(:partOf :LeafA) :HasLeafA)",
            "SubClassOf(:HasLeafA :Target)",
        ]
    )
    tbox_ofn = inject_ofn_extension(ofn_text, extra)
    steps: List[Dict[str, Any]] = []
    # 10 individuals x 5 operations (assert PathA, assert PathB, query ENTAILED, retract PathA, query STILL ENTAILED)
    # Wait: let's do 50 steps total with both survival and stale-retraction checks!
    for i in range(1, 9):  # 8 * 6 = 48 steps + 2 baseline = 50 steps
        ind = f"<http://example.org/elscale#ind_{i}>"
        steps.append({"op": "assert", "id": f"a_{i}", "ofn": f"ClassAssertion(<http://example.org/elscale#LeafA> {ind})"})
        steps.append({"op": "assert", "id": f"b_{i}", "ofn": f"ClassAssertion(<http://example.org/elscale#LeafB> {ind})"})
        steps.append({"op": "query", "ofn": f"ClassAssertion(<http://example.org/elscale#Target> {ind})", "expected": "ENTAILED"})
        steps.append({"op": "retract", "id": f"a_{i}"})
        steps.append({"op": "query", "ofn": f"ClassAssertion(<http://example.org/elscale#Target> {ind})", "expected": "ENTAILED"})
        steps.append({"op": "retract", "id": f"b_{i}"})
    # Final 2 stale-retraction verification queries
    steps.append({"op": "query", "ofn": "ClassAssertion(<http://example.org/elscale#Target> <http://example.org/elscale#ind_1>)", "expected": "NOT_ENTAILED"})
    steps.append({"op": "query", "ofn": "ClassAssertion(<http://example.org/elscale#Target> <http://example.org/elscale#ind_8>)", "expected": "NOT_ENTAILED"})
    return {"id": "STRESS-50", "tbox_axioms": n_tbox + 6, "tbox_ofn": tbox_ofn, "steps": steps}


def summarize_ms(vals: List[float]) -> Dict[str, float]:
    if not vals:
        return {"mean_ms": 0.0, "median_ms": 0.0, "p95_ms": 0.0, "min_ms": 0.0, "max_ms": 0.0}
    sv = sorted(vals)
    p95_idx = min(len(sv) - 1, int(round(0.95 * (len(sv) - 1))))
    return {
        "mean_ms": round(statistics.mean(sv), 3),
        "median_ms": round(statistics.median(sv), 3),
        "p95_ms": round(sv[p95_idx], 3),
        "min_ms": round(sv[0], 3),
        "max_ms": round(sv[-1], 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Benchmark SABRINA vs. HermiT 1.4.5 and ELK 0.6.0")
    parser.add_argument("--out-dir", required=True, help="Output directory for raw JSON results")
    parser.add_argument("--cold-samples", type=int, default=6, help="Number of cold-start JVM samples per track")
    args = parser.parse_args()

    out_dir = Path(args.out_dir).resolve()
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    cp_file = JAVA_DIR / "target" / "classpath.txt"
    if not cp_file.is_file():
        raise FileNotFoundError(f"Missing Java classpath file {cp_file}. Build java-harness first.")
    classpath = f"{JAVA_DIR / 'target' / 'classes'}:{cp_file.read_text(encoding='utf-8').strip()}"

    bfo_text = BFO_CORE_OFN_PATH.read_text(encoding="utf-8")

    # Verify Lean binaries exist
    find_sabrina_binary("sabrina-query")
    find_sabrina_binary("sabrina-session")

    print("[1/5] Starting warm Java harness (HermiT 1.4.5 + ELK 0.6.0) & warming up JVM...")
    java_daemon = JavaHarnessDaemon(classpath)
    java_daemon.warmup(bfo_text, n_iters=5)

    sabrina_warm = SabrinaSession()

    try:
        # ======================================================================
        # TRACK 1: Normative BFO 2020 Core Ontology (192 axioms) + Domain Ext.
        # ======================================================================
        print("[2/5] Track 1: Normative BFO 2020 (30 queries, 192 axioms)...")
        s1_items = [
            json.loads(line)
            for line in (WORKLOAD_DIR / "suite1_bfo_foundational.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]

        t1_records: List[Dict[str, Any]] = []
        # Also test persistent batch on pure BFO 2020 (all 24 unmodified bfo-core items)
        pure_bfo_items = [it for it in s1_items if not it.get("extend_ofn")]
        # Warm batch on single loaded BFO ontology
        t0_sb_load = time.perf_counter()
        sabrina_warm.load_tbox(ofn_text=bfo_text)
        sb_bfo_load_ms = (time.perf_counter() - t0_sb_load) * 1000.0
        sb_bfo_batch_q_ms: List[float] = []
        sb_bfo_batch_verdicts: Dict[str, str] = {}
        for it in pure_bfo_items:
            r = run_sabrina_warm_3val(
                sabrina_warm, bfo_text, it["source_iri"], it["target_iri"], reload_tbox=False
            )
            sb_bfo_batch_q_ms.append(r["query_ms"])
            sb_bfo_batch_verdicts[it["id"]] = r["verdict"]

        batch_queries_payload = [
            {"id": it["id"], "source_iri": it["source_iri"], "target_iri": it["target_iri"], "mode": "3val"}
            for it in pure_bfo_items
        ]
        hermit_bfo_batch = java_daemon.send(
            {
                "cmd": "batch_same_ontology",
                "reasoner": "hermit",
                "ofn": bfo_text,
                "queries": batch_queries_payload,
                "precompute": True,
            }
        )
        elk_bfo_batch = java_daemon.send(
            {
                "cmd": "batch_same_ontology",
                "reasoner": "elk",
                "ofn": bfo_text,
                "queries": batch_queries_payload,
                "precompute": True,
            }
        )

        # Per-item evaluation across all 30 Suite 1 items
        hermit_cold_t1_ms: List[float] = []
        elk_cold_t1_ms: List[float] = []
        for idx, it in enumerate(s1_items):
            ofn_text = materialize_item_ofn(it, bfo_text)
            gold = it["expected_verdict"]

            sb_cold = run_sabrina_cold_3val(ofn_text, it["source_iri"], it["target_iri"])
            sb_warm = run_sabrina_warm_3val(sabrina_warm, ofn_text, it["source_iri"], it["target_iri"], reload_tbox=True)
            hm_warm = java_daemon.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "hermit",
                    "ofn": ofn_text,
                    "source_iri": it["source_iri"],
                    "target_iri": it["target_iri"],
                    "mode": "3val",
                }
            )
            elk_warm = java_daemon.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "elk",
                    "ofn": ofn_text,
                    "source_iri": it["source_iri"],
                    "target_iri": it["target_iri"],
                    "mode": "3val",
                }
            )

            hm_cold_ms: Optional[float] = None
            elk_cold_ms: Optional[float] = None
            if idx < args.cold_samples:
                _, hm_cold_ms = run_java_oneshot(
                    classpath,
                    {
                        "cmd": "query_3val",
                        "reasoner": "hermit",
                        "ofn": ofn_text,
                        "source_iri": it["source_iri"],
                        "target_iri": it["target_iri"],
                        "mode": "3val",
                    },
                )
                hermit_cold_t1_ms.append(hm_cold_ms)
                _, elk_cold_ms = run_java_oneshot(
                    classpath,
                    {
                        "cmd": "query_3val",
                        "reasoner": "elk",
                        "ofn": ofn_text,
                        "source_iri": it["source_iri"],
                        "target_iri": it["target_iri"],
                        "mode": "3val",
                    },
                )
                elk_cold_t1_ms.append(elk_cold_ms)

            prof = sb_cold.get("profile") or {}
            t1_records.append(
                {
                    "id": it["id"],
                    "gold": gold,
                    "full_axioms": prof.get("full_axioms", 192),
                    "module_axioms": prof.get("module_axioms"),
                    "full_fragment": prof.get("full_fragment"),
                    "module_fragment": prof.get("module_fragment"),
                    "engine_used": prof.get("engine_used"),
                    "sabrina_cold_verdict": sb_cold["verdict"],
                    "sabrina_cold_ms": round(sb_cold["total_ms"], 3),
                    "sabrina_warm_verdict": sb_warm["verdict"],
                    "sabrina_warm_ms": round(sb_warm["total_ms"], 3),
                    "hermit_warm_verdict": hm_warm["verdict"],
                    "hermit_warm_ms": round(hm_warm.get("total_ms", 0.0), 3),
                    "hermit_cold_ms": round(hm_cold_ms, 3) if hm_cold_ms is not None else None,
                    "elk_warm_verdict": elk_warm["verdict"],
                    "elk_warm_ms": round(elk_warm.get("total_ms", 0.0), 3),
                    "elk_cold_ms": round(elk_cold_ms, 3) if elk_cold_ms is not None else None,
                }
            )

        # ======================================================================
        # TRACK 2: Expressive SROIQ(D) Reasoning (24 queries from Suite 4)
        # ======================================================================
        print("[3/5] Track 2: Expressive SROIQ(D) Reasoning (24 queries)...")
        s4_items = [
            json.loads(line)
            for line in (WORKLOAD_DIR / "suite4_sroiqd_expressive.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        t2_records: List[Dict[str, Any]] = []
        hermit_cold_t2_ms: List[float] = []
        for idx, it in enumerate(s4_items):
            ofn_text = materialize_item_ofn(it, bfo_text)
            gold = it["expected_verdict"]

            sb_cold = run_sabrina_cold_3val(ofn_text, it["source_iri"], it["target_iri"])
            sb_warm = run_sabrina_warm_3val(sabrina_warm, ofn_text, it["source_iri"], it["target_iri"], reload_tbox=True)
            hm_warm = java_daemon.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "hermit",
                    "ofn": ofn_text,
                    "source_iri": it["source_iri"],
                    "target_iri": it["target_iri"],
                    "mode": "3val",
                }
            )
            elk_warm = java_daemon.send(
                {
                    "cmd": "query_3val",
                    "reasoner": "elk",
                    "ofn": ofn_text,
                    "source_iri": it["source_iri"],
                    "target_iri": it["target_iri"],
                    "mode": "3val",
                }
            )
            hm_cold_ms: Optional[float] = None
            if idx < args.cold_samples:
                _, hm_cold_ms = run_java_oneshot(
                    classpath,
                    {
                        "cmd": "query_3val",
                        "reasoner": "hermit",
                        "ofn": ofn_text,
                        "source_iri": it["source_iri"],
                        "target_iri": it["target_iri"],
                        "mode": "3val",
                    },
                )
                hermit_cold_t2_ms.append(hm_cold_ms)

            prof = sb_cold.get("profile") or {}
            t2_records.append(
                {
                    "id": it["id"],
                    "trap_type": it.get("trap_type"),
                    "gold": gold,
                    "full_axioms": prof.get("full_axioms"),
                    "module_axioms": prof.get("module_axioms"),
                    "module_fragment": prof.get("module_fragment"),
                    "sabrina_cold_verdict": sb_cold["verdict"],
                    "sabrina_cold_ms": round(sb_cold["total_ms"], 3),
                    "sabrina_warm_verdict": sb_warm["verdict"],
                    "sabrina_warm_ms": round(sb_warm["total_ms"], 3),
                    "hermit_warm_verdict": hm_warm["verdict"],
                    "hermit_warm_ms": round(hm_warm.get("total_ms", 0.0), 3),
                    "hermit_cold_ms": round(hm_cold_ms, 3) if hm_cold_ms is not None else None,
                    "elk_warm_verdict": elk_warm["verdict"],
                    "elk_warm_ms": round(elk_warm.get("total_ms", 0.0), 3),
                }
            )

        # ======================================================================
        # TRACK 3: EL++ Scaling & Syntactic bot-Locality (N = 50..1000 axioms)
        # ======================================================================
        print("[4/5] Track 3: EL++ Scaling & bot-Locality (N = 50, 100, 250, 500, 1000)...")
        t3_records: List[Dict[str, Any]] = []
        for n_ax in [50, 100, 250, 500, 1000]:
            ofn_text, src_pos, tgt_pos, src_neg, tgt_neg = generate_el_scaling_ontology(n_ax)
            # Average over 3 repeats for stable timing
            sb_cold_pos_ms, sb_cold_neg_ms = [], []
            sb_warm_pos_ms, hm_warm_pos_ms, elk_warm_pos_ms = [], [], []
            mod_axioms = None
            verdicts = {}
            for rep in range(3):
                r_sc_pos = run_sabrina_cold_3val(ofn_text, src_pos, tgt_pos, mode="subclass")
                r_sc_neg = run_sabrina_cold_3val(ofn_text, src_neg, tgt_neg, mode="subclass")
                sb_cold_pos_ms.append(r_sc_pos["total_ms"])
                sb_cold_neg_ms.append(r_sc_neg["total_ms"])
                mod_axioms = (r_sc_pos.get("profile") or {}).get("module_axioms")

                # Warm query on loaded TBox (measures incremental/cached query vs fresh parse+classify)
                r_sw_pos = run_sabrina_warm_3val(sabrina_warm, ofn_text, src_pos, tgt_pos, mode="subclass", reload_tbox=True)
                sb_warm_pos_ms.append(r_sw_pos["total_ms"])

                r_hm_pos = java_daemon.send(
                    {
                        "cmd": "query_3val",
                        "reasoner": "hermit",
                        "ofn": ofn_text,
                        "source_iri": src_pos,
                        "target_iri": tgt_pos,
                        "mode": "subclass",
                    }
                )
                hm_warm_pos_ms.append(r_hm_pos["total_ms"])

                r_elk_pos = java_daemon.send(
                    {
                        "cmd": "query_3val",
                        "reasoner": "elk",
                        "ofn": ofn_text,
                        "source_iri": src_pos,
                        "target_iri": tgt_pos,
                        "mode": "subclass",
                    }
                )
                elk_warm_pos_ms.append(r_elk_pos["total_ms"])

                if rep == 0:
                    verdicts = {
                        "sabrina_pos": r_sc_pos["verdict"],
                        "sabrina_neg": r_sc_neg["verdict"],
                        "hermit_pos": r_hm_pos["verdict"],
                        "elk_pos": r_elk_pos["verdict"],
                    }

            t3_records.append(
                {
                    "n_axioms": n_ax,
                    "module_axioms": mod_axioms,
                    "locality_reduction_pct": round(100.0 * (1.0 - (mod_axioms or n_ax) / n_ax), 1),
                    "sabrina_cold_pos_ms": round(statistics.median(sb_cold_pos_ms), 3),
                    "sabrina_cold_neg_ms": round(statistics.median(sb_cold_neg_ms), 3),
                    "sabrina_warm_pos_ms": round(statistics.median(sb_warm_pos_ms), 3),
                    "hermit_warm_pos_ms": round(statistics.median(hm_warm_pos_ms), 3),
                    "elk_warm_pos_ms": round(statistics.median(elk_warm_pos_ms), 3),
                    "verdicts": verdicts,
                }
            )

        # ======================================================================
        # TRACK 4: Incremental ABox Assertion & Retraction (DRed)
        # ======================================================================
        print("[5/5] Track 4: Incremental ABox DRed Sessions (10 Suite-5 sessions + 50-step stress)...")
        s5_sessions = [
            json.loads(line)
            for line in (WORKLOAD_DIR / "suite5_dred_sessions.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]

        def run_session_sabrina(tbox_ofn: str, steps: List[Dict[str, Any]]) -> Dict[str, Any]:
            t0 = time.perf_counter()
            ld = sabrina_warm.load_tbox(ofn_text=tbox_ofn)
            t1 = time.perf_counter()
            if not ld.get("ok"):
                return {"ok": False, "error": ld.get("error")}
            step_res = []
            step_ms_sum = 0.0
            for st in steps:
                st0 = time.perf_counter()
                op = st["op"]
                if op == "assert":
                    r = sabrina_warm.assert_fact(st["ofn"], fact_id=st["id"])
                    dt = (time.perf_counter() - st0) * 1000.0
                    step_res.append({"op": "assert", "id": st["id"], "ms": round(dt, 4), "ok": r.get("ok")})
                elif op == "retract":
                    r = sabrina_warm.retract_fact(st["id"])
                    dt = (time.perf_counter() - st0) * 1000.0
                    step_res.append({"op": "retract", "id": st["id"], "ms": round(dt, 4), "ok": r.get("ok")})
                elif op == "query":
                    r = sabrina_warm.query(st["ofn"])
                    dt = (time.perf_counter() - st0) * 1000.0
                    v = "ENTAILED" if r.get("verdict") == "ENTAILED" else "NOT_ENTAILED"
                    step_res.append({"op": "query", "verdict": v, "ms": round(dt, 4), "lean_verified": r.get("lean_verified")})
                step_ms_sum += dt
            return {
                "ok": True,
                "mode": ld.get("mode"),
                "load_ms": round((t1 - t0) * 1000.0, 3),
                "steps_ms": round(step_ms_sum, 3),
                "total_ms": round((t1 - t0) * 1000.0 + step_ms_sum, 3),
                "step_results": step_res,
            }

        t4_sessions: List[Dict[str, Any]] = []
        for sess_item in s5_sessions:
            tbox_ofn = bfo_text if sess_item.get("preset") == "bfo-core" else sess_item["ofn"]
            if sess_item.get("extend_ofn"):
                tbox_ofn = inject_ofn_extension(tbox_ofn, sess_item["extend_ofn"])
            steps = []
            expected_q = []
            for turn in sess_item["turns"]:
                act = turn["action"]
                if act == "assert":
                    steps.append({"op": "assert", "id": turn["fact_id"], "ofn": turn["ofn_axiom"]})
                elif act == "retract":
                    steps.append({"op": "retract", "id": turn["fact_id"]})
                elif act == "query":
                    steps.append({"op": "query", "ofn": turn["query_ofn"]})
                    expected_q.append(turn["expected_verdict"])

            sb_r = run_session_sabrina(tbox_ofn, steps)
            hm_r = java_daemon.send({"cmd": "session_run", "reasoner": "hermit", "tbox_ofn": tbox_ofn, "steps": steps})
            elk_r = java_daemon.send({"cmd": "session_run", "reasoner": "elk", "tbox_ofn": tbox_ofn, "steps": steps})

            sb_v = [s["verdict"] for s in sb_r.get("step_results", []) if s["op"] == "query"]
            hm_v = [s["verdict"] for s in hm_r.get("step_results", []) if s["op"] == "query"]
            elk_v = [s["verdict"] for s in elk_r.get("step_results", []) if s["op"] == "query"]

            t4_sessions.append(
                {
                    "id": sess_item["id"],
                    "preset": sess_item.get("preset") or "el-custom",
                    "n_steps": len(steps),
                    "n_queries": len(expected_q),
                    "expected": expected_q,
                    "sabrina": {
                        "mode": sb_r.get("mode"),
                        "load_ms": sb_r.get("load_ms"),
                        "steps_ms": sb_r.get("steps_ms"),
                        "total_ms": sb_r.get("total_ms"),
                        "matches_gold": sb_v == expected_q,
                        "verdicts": sb_v,
                    },
                    "hermit": {
                        "load_ms": round(hm_r.get("load_ms", 0.0), 3),
                        "steps_ms": round(hm_r.get("steps_ms", 0.0), 3),
                        "total_ms": round(hm_r.get("total_ms", 0.0), 3),
                        "matches_gold": hm_v == expected_q,
                        "verdicts": hm_v,
                    },
                    "elk": {
                        "load_ms": round(elk_r.get("load_ms", 0.0), 3),
                        "steps_ms": round(elk_r.get("steps_ms", 0.0), 3),
                        "total_ms": round(elk_r.get("total_ms", 0.0), 3),
                        "matches_gold": elk_v == expected_q,
                        "verdicts": elk_v,
                    },
                }
            )

        # Track 4b: 50-step stress session on 206-axiom EL++ TBox (3 repeats median)
        stress = generate_dred_stress_session(200)
        stress_expected = [s["expected"] for s in stress["steps"] if s["op"] == "query"]
        sb_st_steps, hm_st_steps, elk_st_steps = [], [], []
        sb_st_load, hm_st_load, elk_st_load = [], [], []
        stress_agree = {}
        for rep in range(3):
            sb_s = run_session_sabrina(stress["tbox_ofn"], stress["steps"])
            hm_s = java_daemon.send({"cmd": "session_run", "reasoner": "hermit", "tbox_ofn": stress["tbox_ofn"], "steps": stress["steps"]})
            elk_s = java_daemon.send({"cmd": "session_run", "reasoner": "elk", "tbox_ofn": stress["tbox_ofn"], "steps": stress["steps"]})
            sb_st_steps.append(sb_s["steps_ms"])
            hm_st_steps.append(hm_s["steps_ms"])
            elk_st_steps.append(elk_s["steps_ms"])
            sb_st_load.append(sb_s["load_ms"])
            hm_st_load.append(hm_s["load_ms"])
            elk_st_load.append(elk_s["load_ms"])
            if rep == 0:
                stress_agree = {
                    "sabrina": [s["verdict"] for s in sb_s["step_results"] if s["op"] == "query"] == stress_expected,
                    "hermit": [s["verdict"] for s in hm_s["step_results"] if s["op"] == "query"] == stress_expected,
                    "elk": [s["verdict"] for s in elk_s["step_results"] if s["op"] == "query"] == stress_expected,
                }

        t4_stress = {
            "id": stress["id"],
            "tbox_axioms": stress["tbox_axioms"],
            "n_steps": len(stress["steps"]),
            "n_queries": len(stress_expected),
            "agreement": stress_agree,
            "sabrina_load_ms": round(statistics.median(sb_st_load), 3),
            "sabrina_steps_ms": round(statistics.median(sb_st_steps), 3),
            "sabrina_per_step_ms": round(statistics.median(sb_st_steps) / len(stress["steps"]), 4),
            "hermit_load_ms": round(statistics.median(hm_st_load), 3),
            "hermit_steps_ms": round(statistics.median(hm_st_steps), 3),
            "hermit_per_step_ms": round(statistics.median(hm_st_steps) / len(stress["steps"]), 4),
            "elk_load_ms": round(statistics.median(elk_st_load), 3),
            "elk_steps_ms": round(statistics.median(elk_st_steps), 3),
            "elk_per_step_ms": round(statistics.median(elk_st_steps) / len(stress["steps"]), 4),
        }

        # Aggregate summary
        t1_sb_hm_agree = sum(1 for r in t1_records if r["sabrina_cold_verdict"] == r["hermit_warm_verdict"] == r["gold"])
        t1_elk_agree = sum(1 for r in t1_records if r["elk_warm_verdict"] == r["gold"])
        t2_sb_hm_agree = sum(1 for r in t2_records if r["sabrina_cold_verdict"] == r["hermit_warm_verdict"] == r["gold"])
        t2_elk_agree = sum(1 for r in t2_records if r["elk_warm_verdict"] == r["gold"])
        t1_mod_sizes = [r["module_axioms"] for r in t1_records if r["module_axioms"] is not None]
        t1_el_downgrades = sum(1 for r in t1_records if r["module_fragment"] == "EL++")

        payload_out = {
            "environment": {
                "platform": platform.platform(),
                "processor": platform.processor(),
                "python": platform.python_version(),
                "java": java_daemon.java_version,
                "lean": "4.35.0",
                "hermit": "1.4.5.519 (OWL API 5.1.20)",
                "elk": "0.6.0 (OWL API 5.1.20)",
            },
            "track1_bfo2020": {
                "n_items": len(t1_records),
                "sabrina_hermit_gold_agreement": f"{t1_sb_hm_agree}/{len(t1_records)}",
                "elk_gold_agreement": f"{t1_elk_agree}/{len(t1_records)}",
                "locality_module_median_axioms": statistics.median(t1_mod_sizes) if t1_mod_sizes else None,
                "locality_module_range": [min(t1_mod_sizes), max(t1_mod_sizes)] if t1_mod_sizes else None,
                "el_downgrade_count": t1_el_downgrades,
                "sabrina_cold": summarize_ms([r["sabrina_cold_ms"] for r in t1_records]),
                "sabrina_warm_reload": summarize_ms([r["sabrina_warm_ms"] for r in t1_records]),
                "hermit_warm_reload": summarize_ms([r["hermit_warm_ms"] for r in t1_records]),
                "hermit_cold_cli": summarize_ms(hermit_cold_t1_ms),
                "elk_warm_reload": summarize_ms([r["elk_warm_ms"] for r in t1_records]),
                "elk_cold_cli": summarize_ms(elk_cold_t1_ms),
                "batch_pure_bfo_24": {
                    "n_queries": len(pure_bfo_items),
                    "sabrina_load_ms": round(sb_bfo_load_ms, 3),
                    "sabrina_queries_total_ms": round(sum(sb_bfo_batch_q_ms), 3),
                    "sabrina_per_query_median_ms": round(statistics.median(sb_bfo_batch_q_ms), 3),
                    "hermit_parse_ms": round(hermit_bfo_batch.get("parse_ms", 0.0), 3),
                    "hermit_classify_ms": round(hermit_bfo_batch.get("classify_ms", 0.0), 3),
                    "hermit_queries_total_ms": round(hermit_bfo_batch.get("queries_total_ms", 0.0), 3),
                    "hermit_total_ms": round(hermit_bfo_batch.get("total_ms", 0.0), 3),
                    "elk_parse_ms": round(elk_bfo_batch.get("parse_ms", 0.0), 3),
                    "elk_classify_ms": round(elk_bfo_batch.get("classify_ms", 0.0), 3),
                    "elk_queries_total_ms": round(elk_bfo_batch.get("queries_total_ms", 0.0), 3),
                    "elk_total_ms": round(elk_bfo_batch.get("total_ms", 0.0), 3),
                },
                "records": t1_records,
            },
            "track2_sroiqd": {
                "n_items": len(t2_records),
                "sabrina_hermit_gold_agreement": f"{t2_sb_hm_agree}/{len(t2_records)}",
                "elk_gold_agreement": f"{t2_elk_agree}/{len(t2_records)}",
                "sabrina_cold": summarize_ms([r["sabrina_cold_ms"] for r in t2_records]),
                "sabrina_warm_reload": summarize_ms([r["sabrina_warm_ms"] for r in t2_records]),
                "hermit_warm_reload": summarize_ms([r["hermit_warm_ms"] for r in t2_records]),
                "hermit_cold_cli": summarize_ms(hermit_cold_t2_ms),
                "elk_warm_reload": summarize_ms([r["elk_warm_ms"] for r in t2_records]),
                "records": t2_records,
            },
            "track3_el_scaling": t3_records,
            "track4_dred": {
                "suite5_sessions": t4_sessions,
                "suite5_summary": {
                    "n_sessions": len(t4_sessions),
                    "sabrina_all_agree": all(s["sabrina"]["matches_gold"] for s in t4_sessions),
                    "hermit_all_agree": all(s["hermit"]["matches_gold"] for s in t4_sessions),
                    "elk_all_agree": all(s["elk"]["matches_gold"] for s in t4_sessions),
                    "sabrina_steps": summarize_ms([s["sabrina"]["steps_ms"] for s in t4_sessions]),
                    "hermit_steps": summarize_ms([s["hermit"]["steps_ms"] for s in t4_sessions]),
                    "elk_steps": summarize_ms([s["elk"]["steps_ms"] for s in t4_sessions]),
                    "sabrina_total": summarize_ms([s["sabrina"]["total_ms"] for s in t4_sessions]),
                    "hermit_total": summarize_ms([s["hermit"]["total_ms"] for s in t4_sessions]),
                    "elk_total": summarize_ms([s["elk"]["total_ms"] for s in t4_sessions]),
                },
                "stress_50": t4_stress,
            },
        }

        out_path = raw_dir / "reasoner_benchmark.json"
        out_path.write_text(json.dumps(payload_out, indent=2), encoding="utf-8")
        print(f"Saved raw benchmark results -> {out_path}")
    finally:
        sabrina_warm.close()
        java_daemon.close()


if __name__ == "__main__":
    main()
