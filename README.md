# SABRINA

SABRINA is a Lean 4 reasoner for SROIQ(D) and OWL 2 DL. This repository accompanies Hugo Cardoso Ferreira de Araújo’s *Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified SROIQ(D) OWL 2 DL Reasoner*.

The decision procedure is proved sound and complete for admitted inputs under SABRINA’s formal semantics. The parser supports a subset of OWL 2 Functional-Style Syntax, and the datatype model has limited XML Schema coverage. The formalization characterizes which role hierarchies the compiler can rank and reduces context-free grammar intersection emptiness to satisfiability under the literal pairwise reading of OWL 2 sections 11.1 and 11.2.

## Build

Use Lean 4.35.0 via the pinned [toolchain](lean-toolchain). The axiom audit requires Python 3.

```sh
lake build
python3 scripts/verify_axioms.py
```

The default build checks the [verification modules](Verification.lean) and builds `sabrina-alc-query` and `sabrina-session`. The axiom script scans both packages and reports dependencies for selected theorems.

The reasoner and OWL formalization are in [packages/sabrina](packages/sabrina/README.md). The first-order logic library is in [packages/logic-core](packages/logic-core/README.md).

## Evaluation

The [counterexamples](counterexamples/) are standalone OWL ontologies. [T1](counterexamples/T1_acyclic_valid_owl2dl.ofn) is an inconsistent nine-axiom ontology. OWL API accepts it as OWL 2 DL. HermiT 1.4.5.519 and Openllet 2.6.5 report it as consistent.

Run the cross-reasoner audit after building SABRINA. It requires Java 17 or later and Maven.

```sh
python3 benchmarks/sabrina-vs-reasoners/run_boundary_audit.py --out /tmp/boundary_audit.json
```

The [benchmark guide](benchmarks/sabrina-vs-reasoners/README.md) explains how to rerun all six tracks with the original workloads and pinned inputs. The [recorded results](results/) include all six tracks and the boundary audit.

## Citation and license

Cite the archived software release [10.5281/zenodo.24521179](https://doi.org/10.5281/zenodo.24521179). See [CITATION.cff](CITATION.cff) for citation metadata and [LICENSE](LICENSE) for the MIT license.
