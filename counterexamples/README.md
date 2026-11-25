# Role-Hierarchy Boundary Counterexamples (`T1`–`T5`)

Standalone OWL 2 Functional-Style Syntax (`.ofn`) ontologies accompanying the paper's Proposition on literal W3C §11.1–§11.2 undecidability and the cross-reasoner empirical audit. Every ontology in this directory is mathematically **UNSATISFIABLE** under W3C OWL 2 Direct Semantics.

| File | Valid W3C OWL 2 DL? | Passes Literal §11.1–§11.2? | Ground Truth | OWL API 5.1.20 | JFact 5.0.3 | HermiT 1.4.5.519 | Openllet 2.6.5 | SABRINA (Lean 4) |
|---|:---:|:---:|:---:|---|---|---|---|---|
| `T1_acyclic_valid_owl2dl.ofn` | **Yes** | **Yes** | **UNSAT** | `inProfile=true` | **UNSAT** | **CONSISTENT (bug)** | **CONSISTENT (bug)** | **UNSAT (20.0 ms)** |
| `T1b_acyclic_2way_inverse.ofn` | **Yes** | **Yes** | **UNSAT** | `inProfile=true` | **UNSAT** | **UNSAT** | **CONSISTENT (bug)** | **UNSAT (21.2 ms)** |
| `T2_fwd_mixed_cycle.ofn` | No (mixed cycle) | **Yes** | **UNSAT** | Rejects | Throws (cycle) | Throws (not reg.) | Warns/drops -> **CONS.** | Rejects (Thm. 2) |
| `T3b_inv_2way_mixed_cycle.ofn` | No (mixed cycle) | **Yes** | **UNSAT** | Rejects | Throws (cycle) | Throws (not reg.) | Warns/drops -> **CONS.** | Rejects (Thm. 2) |
| `T3_inv_1way_mixed_cycle.ofn` | No (mixed cycle) | **Yes** | **UNSAT** | Rejects | Throws (cycle) | **CONSISTENT (bug)** | Warns/drops -> **CONS.** | Rejects (Thm. 2) |
| `T4_prop1_cfg_intersection.ofn` | No (mixed cycle) | **Yes** | **UNSAT** | Rejects | Throws (cycle) | **CONSISTENT (bug)** | Warns/drops -> **CONS.** | Rejects (Thm. 2) |
| `T5_fwd_cfg_intersection.ofn` | No (mixed cycle) | **Yes** | **UNSAT** | Rejects | Throws (cycle) | Throws (not reg.) | Warns/drops -> **CONS.** | Rejects (Thm. 2) |

To reproduce all seven verdicts automatically:

```bash
python3 benchmarks/sabrina-vs-reasoners/run_boundary_audit.py --out /tmp/boundary_audit.json
```
