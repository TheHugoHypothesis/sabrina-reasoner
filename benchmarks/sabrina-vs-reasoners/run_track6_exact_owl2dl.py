#!/usr/bin/env python3
"""Track 6: Exact Cyclic SROIQ(D), Wider Datatypes, String Facets, Built-In Properties,
and Unified Role-Hierarchy Admission Benchmark.

Evaluates SABRINA's unified kernel-verified cyclic OWL 2 DL solver (cold native CLI)
against warm-JVM HermiT 1.4.5 and ELK 0.6.0 across 18 curated OWL 2 DL items
covering six newly verified families:
  1. Infinite-model cyclic GCIs & unranked role-hierarchy fallbacks
  2. Irrational Dedekind-cut owl:real vs. owl:rational
  3. IEEE-754 xsd:float and xsd:dateTime order facets (signed +/-0.0, timezone bounds)
  4. String facets (xsd:pattern, rdf:langRange, length, DataOneOf)
  5. Built-in object & data properties (owl:topObjectProperty chains/restrictions,
     owl:bottomObjectProperty, owl:topDataProperty, owl:bottomDataProperty)
  6. Unified regular & acyclic role hierarchies (equal-rank composite-head cycles &
     full combined multi-feature ontologies)
"""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

BENCH_DIR = Path(__file__).resolve().parent
BFO_LEAN_ROOT = BENCH_DIR.parents[1]
JAVA_DIR = BENCH_DIR / "java-harness"

from sabrina_cli import find_sabrina_binary  # noqa: E402

PFX = (
    "Prefix(:=<http://example.org/t6#>)\n"
    "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
    "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n"
    "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n"
    "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
)

NS = "http://example.org/t6#"


def wrap(body: str) -> str:
    return f"{PFX}Ontology(\n{body}\n)\n"


def normalize_verdict(v: str) -> str:
    m = {
        "SATISFIABLE": "SATISFIABLE",
        "ENTAILED": "ENTAILED",
        "PROVABLY_TRUE": "ENTAILED",
        "REFUTED": "NOT_ENTAILED",
        "PROVABLY_DISJOINT": "NOT_ENTAILED",
        "SENTENCE_INDEPENDENT": "NOT_ENTAILED",
        "NOT_ENTAILED": "NOT_ENTAILED",
        "INCONSISTENT_ONTOLOGY": "INCONSISTENT",
        "INCONSISTENT": "INCONSISTENT",
    }
    return m.get(v, v)


# Infinite-model cyclic ontology (no finite model: n0 has no r-predecessor,
# every Node has an r-successor in Node, and r is inverse-functional).
INF_BODY = """
  Declaration(Class(:Node))
  Declaration(Class(:ChainNode))
  Declaration(ObjectProperty(:r))
  Declaration(NamedIndividual(:n0))
  InverseFunctionalObjectProperty(:r)
  ClassAssertion(:Node :n0)
  ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:r) owl:Nothing) :n0)
  SubClassOf(:Node ObjectSomeValuesFrom(:r :Node))
  SubClassOf(ObjectSomeValuesFrom(:r :Node) :ChainNode)
"""

COMBINED_BODY = """
  Declaration(Class(:Node))
  Declaration(Class(:HasReal))
  Declaration(Class(:Other))
  Declaration(ObjectProperty(:next))
  Declaration(ObjectProperty(:p))
  Declaration(ObjectProperty(:q))
  Declaration(ObjectProperty(:r))
  Declaration(DataProperty(:meas))
  Declaration(NamedIndividual(:n0))
  SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)
  SubClassOf(:Node ObjectSomeValuesFrom(:next :Node))
  SubClassOf(:Node ObjectMinCardinality(1 :next :Node))
  ClassAssertion(:Node :n0)
  SubClassOf(:Node DataSomeValuesFrom(:meas DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
  SubClassOf(DataSomeValuesFrom(:meas owl:real) :HasReal)
  SubClassOf(DataSomeValuesFrom(owl:bottomDataProperty xsd:string) owl:Nothing)
"""

ITEMS: List[Dict[str, Any]] = [
    # 1. Infinite-model cyclic GCIs & unranked role-hierarchy fallbacks
    {
        "id": "T6-INF-1",
        "family": "Cyclic & Unranked",
        "desc": "Infinite-only cyclic model entailment (no finite model)",
        "ofn": wrap(INF_BODY),
        "src": "Node",
        "tgt": "ChainNode",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-INF-2",
        "family": "Cyclic & Unranked",
        "desc": "Rankless converse-square chain r^- o r^- <= r (universal grounding)",
        "ofn": wrap("""
  Declaration(Class(:C))
  Declaration(Class(:D))
  Declaration(ObjectProperty(:r))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
  ClassAssertion(:C :a)
  ObjectPropertyAssertion(:r :b :a)
  ObjectPropertyAssertion(:r :b :b)
  SubClassOf(:D ObjectAllValuesFrom(:r owl:Nothing))
"""),
        "src": "C",
        "tgt": "D",
        "expected": "REFUTED",
    },
    {
        "id": "T6-INF-3",
        "family": "Cyclic & Unranked",
        "desc": "Rankless chain + qualified cardinality (ranked role bounds)",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:r)) :r)
  SubObjectPropertyOf(:s :r)
  SubClassOf(:A ObjectMinCardinality(2 :s :C))
  SubClassOf(ObjectSomeValuesFrom(:r :C) :B)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "ENTAILED",
    },
    # 2. Irrational Dedekind-cut owl:real
    {
        "id": "T6-REAL-1",
        "family": "Dedekind-Cut owl:real",
        "desc": "Irrational real implies owl:real",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:x))
  SubClassOf(:A DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))))
  SubClassOf(DataSomeValuesFrom(:x owl:real) :B)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-REAL-2",
        "family": "Dedekind-Cut owl:real",
        "desc": "Irrational witness refutes rational-only bound",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:a))
  Declaration(DataProperty(:x))
  ClassAssertion(:A :a)
  ClassAssertion(DataSomeValuesFrom(:x DataIntersectionOf(owl:real DataComplementOf(owl:rational))) :a)
  SubClassOf(:B DataAllValuesFrom(:x owl:rational))
"""),
        "src": "A",
        "tgt": "B",
        "expected": "REFUTED",
    },
    {
        "id": "T6-REAL-3",
        "family": "Dedekind-Cut owl:real",
        "desc": "Point [1,1] minus owl:rational is inconsistent",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:a))
  Declaration(DataProperty(:x))
  ClassAssertion(DataSomeValuesFrom(:x DataIntersectionOf(
    DatatypeRestriction(owl:real xsd:minInclusive "1"^^xsd:integer xsd:maxInclusive "1"^^xsd:integer)
    DataComplementOf(owl:rational))) :a)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    # 3. IEEE-754 xsd:float and xsd:dateTime order facets
    {
        "id": "T6-ORD-1",
        "family": "Float & DateTime Facets",
        "desc": "Distinct signed zeros -0.0 and +0.0 satisfy >=2 float",
        "ofn": wrap("""
  Declaration(Class(:S))
  Declaration(Class(:HasTwo))
  Declaration(NamedIndividual(:s))
  Declaration(DataProperty(:v))
  ClassAssertion(:S :s)
  SubClassOf(:S DataMinCardinality(2 :v DatatypeRestriction(xsd:float xsd:minInclusive "-0.0"^^xsd:float xsd:maxInclusive "0.0"^^xsd:float)))
  SubClassOf(DataMinCardinality(2 :v xsd:float) :HasTwo)
"""),
        "src": "S",
        "tgt": "HasTwo",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-ORD-2",
        "family": "Float & DateTime Facets",
        "desc": "Cardinality >=3 in [-0.0, +0.0] xsd:float is inconsistent",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:s))
  Declaration(DataProperty(:v))
  ClassAssertion(DataMinCardinality(3 :v DatatypeRestriction(xsd:float xsd:minInclusive "-0.0"^^xsd:float xsd:maxInclusive "0.0"^^xsd:float)) :s)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    {
        "id": "T6-ORD-3",
        "family": "Float & DateTime Facets",
        "desc": "Empty xsd:dateTime order interval is inconsistent",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:e))
  Declaration(DataProperty(:t))
  ClassAssertion(DataSomeValuesFrom(:t DatatypeRestriction(xsd:dateTime xsd:minInclusive "2026-01-01T12:00:00Z"^^xsd:dateTime xsd:maxInclusive "2026-01-01T11:00:00Z"^^xsd:dateTime)) :e)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    # 4. String facets (xsd:pattern, rdf:langRange, length)
    {
        "id": "T6-STR-1",
        "family": "String & Lang Facets",
        "desc": "xsd:pattern 'a|b' entails DataOneOf('a','b')",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:code))
  EquivalentClasses(:A DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern "a|b"^^xsd:string)))
  EquivalentClasses(:B DataSomeValuesFrom(:code DataOneOf("a"^^xsd:string "b"^^xsd:string)))
"""),
        "src": "A",
        "tgt": "B",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-STR-2",
        "family": "String & Lang Facets",
        "desc": "Disjoint rdf:langRange 'en' vs 'fr' under functional property",
        "ofn": wrap("""
  Declaration(Class(:EnDoc))
  Declaration(Class(:FrDoc))
  Declaration(NamedIndividual(:d))
  Declaration(DataProperty(:label))
  FunctionalDataProperty(:label)
  ClassAssertion(:EnDoc :d)
  SubClassOf(:EnDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange "en"^^xsd:string)))
  SubClassOf(:FrDoc DataSomeValuesFrom(:label DatatypeRestriction(rdf:PlainLiteral rdf:langRange "fr"^^xsd:string)))
"""),
        "src": "EnDoc",
        "tgt": "FrDoc",
        "expected": "REFUTED",
    },
    {
        "id": "T6-STR-3",
        "family": "String & Lang Facets",
        "desc": "xsd:pattern 'ab+' intersected with maxLength 1 is inconsistent",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:x))
  Declaration(DataProperty(:code))
  ClassAssertion(DataSomeValuesFrom(:code DatatypeRestriction(xsd:string xsd:pattern "ab+"^^xsd:string xsd:maxLength "1"^^xsd:nonNegativeInteger)) :x)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    # 5. Built-in object & data properties
    {
        "id": "T6-TOP-1",
        "family": "Built-In Properties",
        "desc": "owl:topObjectProperty chain body (p o topObj o q <= viaTop)",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(ObjectProperty(:p))
  Declaration(ObjectProperty(:q))
  Declaration(ObjectProperty(:viaTop))
  Declaration(NamedIndividual(:a))
  Declaration(NamedIndividual(:b))
  SubObjectPropertyOf(ObjectPropertyChain(:p owl:topObjectProperty :q) :viaTop)
  ObjectPropertyAssertion(:p :a :a)
  ObjectPropertyAssertion(:q :b :b)
  NegativeObjectPropertyAssertion(:viaTop :a :b)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    {
        "id": "T6-TOP-2",
        "family": "Built-In Properties",
        "desc": "owl:topDataProperty universal closure SubDataPropertyOf(topData, dp)",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:HasInt))
  Declaration(DataProperty(:dp))
  SubDataPropertyOf(owl:topDataProperty :dp)
  SubClassOf(DataSomeValuesFrom(:dp xsd:integer) :HasInt)
"""),
        "src": "A",
        "tgt": "HasInt",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-BOT-3",
        "family": "Built-In Properties",
        "desc": "owl:bottomObjectProperty & owl:bottomDataProperty emptiness clash",
        "ofn": wrap("""
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(NamedIndividual(:x))
  ClassAssertion(DataSomeValuesFrom(owl:bottomDataProperty xsd:string) :x)
"""),
        "src": "A",
        "tgt": "B",
        "expected": "INCONSISTENT_ONTOLOGY",
    },
    # 6. Unified regular & acyclic role hierarchies
    {
        "id": "T6-RH-1",
        "family": "Unified Regular OWL 2 DL",
        "desc": "Equal-rank unary cycle on composite head (r == s, a o b <= r)",
        "ofn": wrap("""
  Declaration(Class(:X))
  Declaration(Class(:Y))
  Declaration(Class(:Z))
  Declaration(ObjectProperty(:a))
  Declaration(ObjectProperty(:b))
  Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:s))
  SubObjectPropertyOf(:r :s)
  SubObjectPropertyOf(:s :r)
  SubObjectPropertyOf(ObjectPropertyChain(:a :b) :r)
  SubClassOf(:X ObjectSomeValuesFrom(:a ObjectSomeValuesFrom(:b :Y)))
  SubClassOf(ObjectSomeValuesFrom(:s :Y) :Z)
"""),
        "src": "X",
        "tgt": "Z",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-RH-2",
        "family": "Unified Regular OWL 2 DL",
        "desc": "Combined cyclic GCI + QCR + chain + owl:real + botData (entailed)",
        "ofn": wrap(COMBINED_BODY),
        "src": "Node",
        "tgt": "HasReal",
        "expected": "ENTAILED",
    },
    {
        "id": "T6-RH-3",
        "family": "Unified Regular OWL 2 DL",
        "desc": "Combined cyclic GCI + QCR + chain + owl:real + botData (open)",
        "ofn": wrap(COMBINED_BODY),
        "src": "Node",
        "tgt": "Other",
        "expected": "SENTENCE_INDEPENDENT",
    },
]


def run_sabrina(bin_path: Path, item: Dict[str, Any]) -> Tuple[Dict[str, Any], float]:
    q = f"SubClassOf(<{NS}{item['src']}> <{NS}{item['tgt']}>)"
    payload = ["sabrina-ofn-query-v1", item["id"], item["ofn"], q]
    t0 = time.perf_counter()
    try:
        p = subprocess.run(
            [str(bin_path)],
            input=json.dumps(payload),
            text=True,
            capture_output=True,
            timeout=15,
        )
        dt = (time.perf_counter() - t0) * 1000.0
        return json.loads(p.stdout), dt
    except subprocess.TimeoutExpired:
        dt = (time.perf_counter() - t0) * 1000.0
        return {"verdict": "TIMEOUT", "lean_verified": False}, dt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", required=True)
    args = parser.parse_args()

    out_dir = Path(args.out_dir).resolve()
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    sabrina_bin = Path(find_sabrina_binary("sabrina-alc-query"))
    cp_file = JAVA_DIR / "target" / "classpath.txt"
    classpath = f"{JAVA_DIR / 'target' / 'classes'}:{cp_file.read_text().strip()}"

    java_proc = subprocess.Popen(
        [
            "java",
            "--add-opens",
            "java.base/java.lang=ALL-UNNAMED",
            "-cp",
            classpath,
            "bench.ReasonerHarness",
        ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,
    )

    def java_send(req: Dict[str, Any]) -> Dict[str, Any]:
        assert java_proc.stdin is not None and java_proc.stdout is not None
        java_proc.stdin.write(json.dumps(req) + "\n")
        java_proc.stdin.flush()
        return json.loads(java_proc.stdout.readline())

    # Warmup JVM
    for _ in range(5):
        java_send({
            "cmd": "query_3val",
            "reasoner": "hermit",
            "ofn": wrap("SubClassOf(:A :B)"),
            "source_iri": f"{NS}A",
            "target_iri": f"{NS}B",
            "mode": "subclass",
        })

    rows = []
    try:
        for item in ITEMS:
            sb_res, sb_ms = run_sabrina(sabrina_bin, item)
            hm_res = java_send({
                "cmd": "query_3val",
                "reasoner": "hermit",
                "ofn": item["ofn"],
                "source_iri": f"{NS}{item['src']}",
                "target_iri": f"{NS}{item['tgt']}",
                "mode": "subclass",
            })
            elk_res = java_send({
                "cmd": "query_3val",
                "reasoner": "elk",
                "ofn": item["ofn"],
                "source_iri": f"{NS}{item['src']}",
                "target_iri": f"{NS}{item['tgt']}",
                "mode": "subclass",
            })

            exp_norm = normalize_verdict(item["expected"])
            sb_v = sb_res.get("verdict", "ERROR")
            hm_v = hm_res.get("verdict", "ERROR")
            elk_v = elk_res.get("verdict", "ERROR")

            sb_ok = sb_v == item["expected"] and bool(sb_res.get("lean_verified"))
            hm_ok = bool(hm_res.get("ok")) and normalize_verdict(hm_v) == exp_norm
            elk_ok = bool(elk_res.get("ok")) and normalize_verdict(elk_v) == exp_norm

            row = {
                "id": item["id"],
                "family": item["family"],
                "desc": item["desc"],
                "expected": item["expected"],
                "sabrina_verdict": sb_v,
                "sabrina_verified": bool(sb_res.get("lean_verified")),
                "sabrina_basis": sb_res.get("decision_basis") or (sb_res.get("certificate") or {}).get("basis"),
                "sabrina_cold_ms": round(sb_ms, 2),
                "sabrina_ok": sb_ok,
                "hermit_verdict": hm_v,
                "hermit_ok": hm_ok,
                "hermit_error": hm_res.get("error"),
                "hermit_warm_ms": round(float(hm_res.get("total_ms", 0.0)), 2) if hm_res.get("ok") else None,
                "elk_verdict": elk_v,
                "elk_ok": elk_ok,
                "elk_error": elk_res.get("error"),
                "elk_warm_ms": round(float(elk_res.get("total_ms", 0.0)), 2) if elk_res.get("ok") else None,
            }
            rows.append(row)
            print(
                f"{item['id']:10s} [{item['family']:24s}] "
                f"SABRINA={sb_v:21s} ({sb_ms:6.1f}ms, ok={sb_ok}, basis={row['sabrina_basis']}) | "
                f"HermiT={hm_v:12s} (ok={hm_ok}) | ELK={elk_v:12s} (ok={elk_ok})",
                flush=True,
            )
    finally:
        try:
            java_send({"cmd": "quit"})
        except Exception:
            pass
        java_proc.wait(timeout=5)

    summary = {
        "n_items": len(rows),
        "sabrina_correct": sum(1 for r in rows if r["sabrina_ok"]),
        "hermit_correct": sum(1 for r in rows if r["hermit_ok"]),
        "hermit_errors": sum(1 for r in rows if r["hermit_error"]),
        "elk_correct": sum(1 for r in rows if r["elk_ok"]),
        "sabrina_cold_median_ms": round(statistics.median(r["sabrina_cold_ms"] for r in rows), 2),
        "hermit_warm_median_ms": round(
            statistics.median(r["hermit_warm_ms"] for r in rows if r["hermit_warm_ms"] is not None), 2
        ) if any(r["hermit_warm_ms"] is not None for r in rows) else None,
        "items": rows,
    }
    (raw_dir / "track6_exact_owl2dl.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(
        f"\nTrack 6 Summary: SABRINA {summary['sabrina_correct']}/{summary['n_items']} "
        f"(median {summary['sabrina_cold_median_ms']} ms) | "
        f"HermiT {summary['hermit_correct']}/{summary['n_items']} "
        f"(errors={summary['hermit_errors']}, median {summary['hermit_warm_median_ms']} ms) | "
        f"ELK {summary['elk_correct']}/{summary['n_items']}"
    )


if __name__ == "__main__":
    main()
