#!/usr/bin/env python3
"""Cross-reasoner empirical audit of Proposition 1 role-hierarchy boundaries
and valid acyclic inverse-subproperty chains.

Tests T1, T1b, T2, T3, T3b, T4, T5 against:
  - OWL API 5.1.20 (OWL2DLProfile)
  - JFact 5.0.3 (FaCT++)
  - HermiT 1.4.5.519
  - Openllet 2.6.5 (Pellet)
  - SABRINA (Lean 4 kernel-verified CLI + exact admission check)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List

BENCH_DIR = Path(__file__).resolve().parent
BFO_LEAN_ROOT = BENCH_DIR.parents[1]
HARNESS_DIR = BENCH_DIR / "boundary-harness"

from sabrina_cli import find_sabrina_binary  # noqa: E402

PFX = (
    "Prefix(:=<http://example.org/cfg#>)\n"
    "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
)
Q = "SubClassOf(<http://example.org/cfg#mark> <http://example.org/cfg#mark>)"


def wrap(body: str) -> str:
    return f"{PFX}Ontology(\n{body}\n)\n"


CASES: List[Dict[str, Any]] = [
    {
        "id": "T1",
        "label": "Acyclic 1-way inverse chains (9 ax.)",
        "passes_literal_11_2": True,
        "valid_sroiq": True,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:h)) Declaration(ObjectProperty(:m)) Declaration(ObjectProperty(:l)) Declaration(ObjectProperty(:n))
  Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))
  ObjectPropertyAssertion(:p :a :b)
  ObjectPropertyAssertion(:q :b :c)
  ObjectPropertyAssertion(:r :c :d)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:q) ObjectInverseOf(:p)) :h)
  SubObjectPropertyOf(ObjectInverseOf(:h) :m)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:m)) :l)
  SubObjectPropertyOf(ObjectInverseOf(:l) :n)
  ClassAssertion(ObjectAllValuesFrom(:n :mark) :a)
  ClassAssertion(ObjectComplementOf(:mark) :d)
"""),
    },
    {
        "id": "T1b",
        "label": "Acyclic 2-way InverseObjectProperties (9 ax.)",
        "passes_literal_11_2": True,
        "valid_sroiq": True,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))
  Declaration(ObjectProperty(:h)) Declaration(ObjectProperty(:m)) Declaration(ObjectProperty(:l)) Declaration(ObjectProperty(:n))
  Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))
  ObjectPropertyAssertion(:p :a :b)
  ObjectPropertyAssertion(:q :b :c)
  ObjectPropertyAssertion(:r :c :d)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:q) ObjectInverseOf(:p)) :h)
  InverseObjectProperties(:h :m)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) ObjectInverseOf(:m)) :l)
  InverseObjectProperties(:l :n)
  ClassAssertion(ObjectAllValuesFrom(:n :mark) :a)
  ClassAssertion(ObjectComplementOf(:mark) :d)
"""),
    },
    {
        "id": "T2",
        "label": "Forward 4-step mixed cycle (explicit 0011)",
        "passes_literal_11_2": True,
        "valid_sroiq": False,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:t0)) Declaration(ObjectProperty(:t1))
  Declaration(ObjectProperty(:nA)) Declaration(ObjectProperty(:nB))
  Declaration(ObjectProperty(:hX)) Declaration(ObjectProperty(:mX))
  Declaration(ObjectProperty(:lS)) Declaration(ObjectProperty(:nS))
  Declaration(NamedIndividual(:root))
  Declaration(NamedIndividual(:x1)) Declaration(NamedIndividual(:x2))
  Declaration(NamedIndividual(:x3)) Declaration(NamedIndividual(:x4))
  ObjectPropertyAssertion(:t0 :root :x1)
  ObjectPropertyAssertion(:t0 :x1 :x2)
  ObjectPropertyAssertion(:t1 :x2 :x3)
  ObjectPropertyAssertion(:t1 :x3 :x4)
  SubObjectPropertyOf(:t0 :nA)
  SubObjectPropertyOf(:t1 :nB)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :nB) :lS)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :nS) :hX)
  SubObjectPropertyOf(:hX :mX)
  SubObjectPropertyOf(ObjectPropertyChain(:mX :nB) :lS)
  SubObjectPropertyOf(:lS :nS)
  ClassAssertion(ObjectAllValuesFrom(:nS :mark) :root)
  ClassAssertion(ObjectComplementOf(:mark) :x4)
"""),
    },
    {
        "id": "T3",
        "label": "Inverse 1-way 4-step mixed cycle (explicit 0011)",
        "passes_literal_11_2": True,
        "valid_sroiq": False,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:nA)) Declaration(ObjectProperty(:nB))
  Declaration(ObjectProperty(:hX)) Declaration(ObjectProperty(:mX))
  Declaration(ObjectProperty(:lS)) Declaration(ObjectProperty(:nS))
  Declaration(NamedIndividual(:x0)) Declaration(NamedIndividual(:x1))
  Declaration(NamedIndividual(:x2)) Declaration(NamedIndividual(:x3)) Declaration(NamedIndividual(:x4))
  ObjectPropertyAssertion(:nA :x0 :x1)
  ObjectPropertyAssertion(:nA :x1 :x2)
  ObjectPropertyAssertion(:nB :x2 :x3)
  ObjectPropertyAssertion(:nB :x3 :x4)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:nA)) :lS)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nS) ObjectInverseOf(:nA)) :hX)
  SubObjectPropertyOf(ObjectInverseOf(:hX) :mX)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:mX)) :lS)
  SubObjectPropertyOf(ObjectInverseOf(:lS) :nS)
  ClassAssertion(ObjectAllValuesFrom(:nS :mark) :x0)
  ClassAssertion(ObjectComplementOf(:mark) :x4)
"""),
    },
    {
        "id": "T3b",
        "label": "Inverse 2-way 4-step mixed cycle (explicit 0011)",
        "passes_literal_11_2": True,
        "valid_sroiq": False,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:nA)) Declaration(ObjectProperty(:nB))
  Declaration(ObjectProperty(:hX)) Declaration(ObjectProperty(:mX))
  Declaration(ObjectProperty(:lS)) Declaration(ObjectProperty(:nS))
  Declaration(NamedIndividual(:x0)) Declaration(NamedIndividual(:x1))
  Declaration(NamedIndividual(:x2)) Declaration(NamedIndividual(:x3)) Declaration(NamedIndividual(:x4))
  ObjectPropertyAssertion(:nA :x0 :x1)
  ObjectPropertyAssertion(:nA :x1 :x2)
  ObjectPropertyAssertion(:nB :x2 :x3)
  ObjectPropertyAssertion(:nB :x3 :x4)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:nA)) :lS)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nS) ObjectInverseOf(:nA)) :hX)
  InverseObjectProperties(:hX :mX)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:mX)) :lS)
  InverseObjectProperties(:lS :nS)
  ClassAssertion(ObjectAllValuesFrom(:nS :mark) :x0)
  ClassAssertion(ObjectComplementOf(:mark) :x4)
"""),
    },
    {
        "id": "T4",
        "label": "Exact Prop. 1 CFG intersection ({0^k 1^k} cap {0011})",
        "passes_literal_11_2": True,
        "valid_sroiq": False,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:t0)) Declaration(ObjectProperty(:t1)) Declaration(ObjectProperty(:i))
  Declaration(ObjectProperty(:nA)) Declaration(ObjectProperty(:nB))
  Declaration(ObjectProperty(:nS)) Declaration(ObjectProperty(:hS)) Declaration(ObjectProperty(:mS)) Declaration(ObjectProperty(:lS))
  Declaration(ObjectProperty(:nX)) Declaration(ObjectProperty(:hX)) Declaration(ObjectProperty(:mX)) Declaration(ObjectProperty(:lX))
  Declaration(ObjectProperty(:nT)) Declaration(ObjectProperty(:hT)) Declaration(ObjectProperty(:mT)) Declaration(ObjectProperty(:lT))
  Declaration(ObjectProperty(:nY)) Declaration(ObjectProperty(:hY)) Declaration(ObjectProperty(:mY)) Declaration(ObjectProperty(:lY))
  Declaration(ObjectProperty(:nZ)) Declaration(ObjectProperty(:hZ)) Declaration(ObjectProperty(:mZ)) Declaration(ObjectProperty(:lZ))
  Declaration(NamedIndividual(:root))
  SubClassOf(owl:Thing ObjectSomeValuesFrom(ObjectInverseOf(:t0) owl:Thing))
  SubClassOf(owl:Thing ObjectSomeValuesFrom(ObjectInverseOf(:t1) owl:Thing))
  SubClassOf(owl:Thing ObjectHasSelf(:i))
  SubObjectPropertyOf(ObjectInverseOf(:t0) :nA)
  SubObjectPropertyOf(ObjectInverseOf(:t1) :nB)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:nA)) :hS)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nX) ObjectInverseOf(:nA)) :hS)
  SubObjectPropertyOf(ObjectInverseOf(:hS) :mS)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:mS) ObjectInverseOf(:i)) :lS)
  SubObjectPropertyOf(ObjectInverseOf(:lS) :nS)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:nS)) :hX)
  SubObjectPropertyOf(ObjectInverseOf(:hX) :mX)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:mX) ObjectInverseOf(:i)) :lX)
  SubObjectPropertyOf(ObjectInverseOf(:lX) :nX)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nB) ObjectInverseOf(:nB)) :hZ)
  SubObjectPropertyOf(ObjectInverseOf(:hZ) :mZ)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:mZ) ObjectInverseOf(:i)) :lZ)
  SubObjectPropertyOf(ObjectInverseOf(:lZ) :nZ)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nZ) ObjectInverseOf(:nA)) :hY)
  SubObjectPropertyOf(ObjectInverseOf(:hY) :mY)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:mY) ObjectInverseOf(:i)) :lY)
  SubObjectPropertyOf(ObjectInverseOf(:lY) :nY)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:nY) ObjectInverseOf(:nA)) :hT)
  SubObjectPropertyOf(ObjectInverseOf(:hT) :mT)
  SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:mT) ObjectInverseOf(:i)) :lT)
  SubObjectPropertyOf(ObjectInverseOf(:lT) :nT)
  ClassAssertion(ObjectAllValuesFrom(:nS :mark) :root)
  ClassAssertion(ObjectAllValuesFrom(:nT ObjectComplementOf(:mark)) :root)
"""),
    },
    {
        "id": "T5",
        "label": "Forward full CFG intersection ({0^k 1^k} cap {0011})",
        "passes_literal_11_2": True,
        "valid_sroiq": False,
        "ground_truth": "INCONSISTENT",
        "ofn": wrap("""
  Declaration(Class(:mark))
  Declaration(ObjectProperty(:t0)) Declaration(ObjectProperty(:t1))
  Declaration(ObjectProperty(:nA)) Declaration(ObjectProperty(:nB))
  Declaration(ObjectProperty(:hX)) Declaration(ObjectProperty(:mX))
  Declaration(ObjectProperty(:lS)) Declaration(ObjectProperty(:nS))
  Declaration(ObjectProperty(:q1)) Declaration(ObjectProperty(:q2)) Declaration(ObjectProperty(:qT))
  Declaration(NamedIndividual(:root))
  SubClassOf(owl:Thing ObjectSomeValuesFrom(:t0 owl:Thing))
  SubClassOf(owl:Thing ObjectSomeValuesFrom(:t1 owl:Thing))
  SubObjectPropertyOf(:t0 :nA)
  SubObjectPropertyOf(:t1 :nB)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :nB) :lS)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :nS) :hX)
  SubObjectPropertyOf(:hX :mX)
  SubObjectPropertyOf(ObjectPropertyChain(:mX :nB) :lS)
  SubObjectPropertyOf(:lS :nS)
  SubObjectPropertyOf(ObjectPropertyChain(:nB :nB) :q1)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :q1) :q2)
  SubObjectPropertyOf(ObjectPropertyChain(:nA :q2) :qT)
  ClassAssertion(ObjectAllValuesFrom(:nS :mark) :root)
  ClassAssertion(ObjectAllValuesFrom(:qT ObjectComplementOf(:mark)) :root)
"""),
    },
]


def ensure_harness() -> str:
    cp_file = HARNESS_DIR / "target" / "classpath.txt"
    classes_dir = HARNESS_DIR / "target" / "classes"
    if not cp_file.is_file() or not (classes_dir / "BoundaryAudit.class").is_file():
        subprocess.run(["mvn", "-q", "compile", "dependency:build-classpath", f"-Dmdep.outputFile={cp_file}"],
                       cwd=HARNESS_DIR, check=True)
    return f"{classes_dir}:{cp_file.read_text(encoding='utf-8').strip()}"


def run_sabrina(bin_path: Path, case: Dict[str, Any]) -> Dict[str, Any]:
    payload = ["sabrina-ofn-query-v1", case["id"], case["ofn"], Q]
    t0 = time.perf_counter()
    try:
        p = subprocess.run([str(bin_path)], input=json.dumps(payload),
                           text=True, capture_output=True, timeout=6)
        dt = (time.perf_counter() - t0) * 1000.0
        res = json.loads(p.stdout)
        return {
            "verdict": res.get("verdict"),
            "lean_verified": bool(res.get("lean_verified", False)),
            "cold_ms": round(dt, 2),
        }
    except subprocess.TimeoutExpired:
        return {"verdict": "REJECTED_NON_REGULAR_OR_TIMEOUT", "lean_verified": False, "cold_ms": None}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    cp = ensure_harness()
    sabrina_bin = Path(find_sabrina_binary("sabrina-query"))
    rows = []

    with tempfile.TemporaryDirectory() as td:
        for c in CASES:
            ofn_path = Path(td) / f"{c['id']}.ofn"
            ofn_path.write_text(c["ofn"], encoding="utf-8")
            jp = subprocess.run(["java", "-cp", cp, "BoundaryAudit", str(ofn_path)],
                                text=True, capture_output=True, check=True)
            jres = json.loads(jp.stdout.strip().splitlines()[-1])
            sres = run_sabrina(sabrina_bin, c)
            row = {
                "id": c["id"],
                "label": c["label"],
                "passes_literal_11_2": c["passes_literal_11_2"],
                "valid_sroiq": c["valid_sroiq"],
                "ground_truth": c["ground_truth"],
                "owlapi_in_profile": jres["owlapi_in_profile"],
                "owlapi_violations": jres["owlapi_violations"],
                "jfact": jres["jfact"],
                "hermit": jres["hermit"],
                "openllet": jres["openllet"],
                "openllet_dropped_axioms": "Ignoring transitivity and/or complex subproperty axioms" in jp.stderr,
                "sabrina": sres,
            }
            rows.append(row)
            print(f"{c['id']:4s} | OWL2DL={str(row['owlapi_in_profile']):5s} | JFact={row['jfact'][:18]:18s} | "
                  f"HermiT={row['hermit'][:18]:18s} | Openllet={row['openllet']:12s}(drop={row['openllet_dropped_axioms']}) | "
                  f"SABRINA={sres['verdict']} ({sres['cold_ms']} ms)")

    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"boundary_audit": rows}, indent=2), encoding="utf-8")
    print(f"\nSaved boundary audit to {out_path}")


if __name__ == "__main__":
    main()
