# SABRINA

SABRINA is a Lean 4 reasoner for SROIQ(D) and OWL 2 DL. This repository accompanies Hugo Cardoso Ferreira de Araújo’s *Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified SROIQ(D) OWL 2 DL Reasoner*.

The decision procedure is proved sound and complete for admitted inputs under SABRINA’s Direct Semantics with zero `sorry` and no custom axioms. It covers all 16 OWL 2 class constructors, TBox/RBox/ABox reasoning, regular and dependency-acyclic role hierarchies, 33 XML Schema and OWL datatypes (including Unicode 17.0.0 XSD 1.1 regular expressions and Exclusive XML Canonicalization), OWL 2 Functional-Style Syntax, RDF/XML 1.1, Turtle 1.1, OASIS XML import catalogs, strict W3C §5.8.1–§5.8.2 and §11.2 validation (`--strict-owl2dl`), single-pass $\mathcal{EL}^{++}$ and Enhanced Traversal TBox classification, ABox realization, inferred ontology materialization (`--materialize` to `.ofn`, `.ttl`, and `.owl`), minimal entailment/inconsistency justifications (`--explain`), and hash-indexed $\bot$-locality module extraction. The formalization also characterizes which role hierarchies the compiler can rank and reduces context-free grammar intersection emptiness to satisfiability under the literal pairwise reading of OWL 2 sections 11.1 and 11.2.

## Build

Use Lean 4.35.0 via the pinned [toolchain](lean-toolchain). The audit and test scripts require Python 3.

```sh
lake build
python3 scripts/verify_axioms.py
python3 benchmarks/w3c-owl2-conformance/run_w3c_conformance.py
python3 benchmarks/fast-locality/bench_snomed_scale.py
python3 benchmarks/fast-locality/bench_fast_classification.py
```

The default build checks [Verification.lean](Verification.lean) and builds `sabrina-query` and `sabrina-session`. The axiom script scans both packages and checks kernel axiom dependencies for 48 headline theorems. To materialize an inferred ontology or compute minimal justifications directly:

```sh
.lake/build/bin/sabrina-query --materialize input.ttl -o inferred.owl
.lake/build/bin/sabrina-query --explain input.owl --query "SubClassOf(:A :C)"
```

The reasoner and OWL 2 formalization are in [packages/sabrina](packages/sabrina/README.md). The first-order logic library is in [packages/logic-core](packages/logic-core/README.md). See [CHANGELOG.md](CHANGELOG.md) and [ROADMAP.md](ROADMAP.md) for release history and milestone coverage.

## Evaluation

The [counterexamples](counterexamples/) are standalone OWL ontologies. [T1](counterexamples/T1_acyclic_valid_owl2dl.ofn) is an inconsistent nine-axiom ontology. OWL API accepts it as OWL 2 DL. HermiT 1.4.5.519 and Openllet 2.6.5 report it as consistent.

Run the cross-reasoner audit after building SABRINA. It requires Java 17 or later and Maven.

```sh
python3 benchmarks/sabrina-vs-reasoners/run_boundary_audit.py --out /tmp/boundary_audit.json
```

The [benchmark guide](benchmarks/sabrina-vs-reasoners/README.md) explains how to rerun all six tracks with the original workloads and pinned inputs. The [recorded results](results/) include all six tracks and the boundary audit.

## Citation and license

Cite the archived software release [10.5281/zenodo.24521179](https://doi.org/10.5281/zenodo.24521179). See [CITATION.cff](CITATION.cff) for citation metadata and [LICENSE](LICENSE) for the MIT license.
