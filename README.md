# SABRINA

SABRINA is a kernel-verified Lean 4 reasoner for $\mathcal{SROIQ}(\mathcal{D})$ and W3C OWL 2 DL. This repository accompanies Hugo Cardoso Ferreira de Araújo’s *Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified SROIQ(D) OWL 2 DL Reasoner*.

All Lean 4 proofs build with **zero `sorry`**, **zero custom axioms**, and strictly standard Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`), audited across 35 headline theorems by [scripts/verify_axioms.py](scripts/verify_axioms.py).

## Capabilities (`v1.0.0`)

- **Verified $\mathcal{SROIQ}(\mathcal{D})$ Decision Core:** Soundness, completeness, and fuel-free blocked-forest termination across all 16 OWL 2 class constructors, TBox/RBox/ABox Direct Semantics, nominals, inverse roles, qualified cardinalities, mixed object/data `HasKey`, cyclic GCIs, universal/bottom properties, and dependency-acyclic / regular role hierarchies (`decideSROIQBool_ontology_iff`, `decideRegularOWL2DLReal_ontology_iff`).
- **Syntax, RDF Mapping & Strict OWL 2 DL Validation:** Native OWL 2 Functional-Style Syntax (`.ofn`), RDF/XML 1.1, and Turtle 1.1 parsers with W3C OWL 2 RDF-to-Structural mapping (`owl2_rdf_mapping_roundtrip_correspondence`), OASIS `catalog-v001.xml` / `--import-dir` import resolution, and `--strict-owl2dl` enforcement of W3C §5.8.1–§5.8.2 typing/punning and §11.2 global restrictions (`decideStrictTypedOWL2DLReal_iff`).
- **33-Datatype Exact Solver & XSD 1.1 Unicode Regex:** Mechanized 33-datatype map (`owl:real`, IEEE-754 `xsd:float`/`xsd:double`, `xsd:dateTime`/`xsd:dateTimeStamp`, `rdf:langRange`, `rdf:XMLLiteral` Exc-C14N, length/order facets), full Unicode 17.0.0 XSD 1.1 regex engine (`\d`, `\w`, `\p{...}`, nested subtraction), and independent declarative standards-correspondence proofs (`StandardsCorrespondence`, `XMLCorrespondence`, `RegexGrammarCorrespondence`).
- **Complete Reasoning Services:** Consistency checking, exact 4-way entailment across 29 OWL 2 DL axiom forms + existential anonymous-individual queries (`decideRealExtendedQuery_sound`), certified TBox classification (`sabrina-classify-v1`), and ABox realization (`sabrina-realize-v1`).
- **Clinical-Scale Performance:** Hash-indexed $\bot$-locality module extraction (`FastLocality.lean`, proved axiom-set-identical to `Profile.extractBotModule` via `extractBotModuleFast_mem_iff`), polynomial $\mathcal{EL}^{++}$ classification, and provenance-tracked DRed incremental ABox sessions (`sabrina-session`). Extracts and verifies queries on 350,000-axiom ontologies in **<0.9s** cold end-to-end and **~67 ms** warm cached.

## Build & Verification

Use Lean 4.35.0 via the pinned [toolchain](lean-toolchain). The audit and benchmark suites require Python 3.

```sh
lake build
python3 scripts/verify_axioms.py
python3 benchmarks/w3c-owl2-conformance/run_w3c_conformance.py
python3 benchmarks/fast-locality/bench_snomed_scale.py
```

The default build checks all [verification modules](Verification.lean) and compiles two native CLI executables:
- `.lake/build/bin/sabrina-query` — one-shot JSON query, consistency, classification, and realization CLI (`--strict-owl2dl`, `--import-dir`, `--catalog`).
- `.lake/build/bin/sabrina-session` — persistent JSON-lines session server with cached `LocalityIndex`, incremental $\mathcal{EL}^{++}$ ABox updates/retraction, classification, and realization.

The reasoner and OWL 2 formalization live in [packages/sabrina](packages/sabrina/README.md); the generic first-order logic library lives in [packages/logic-core](packages/logic-core/README.md). See [ROADMAP.md](ROADMAP.md) and [CHANGELOG.md](CHANGELOG.md) for milestone details.

## Evaluation & Counterexamples

The [counterexamples](counterexamples/) are standalone OWL ontologies. [T1](counterexamples/T1_acyclic_valid_owl2dl.ofn) is an inconsistent nine-axiom ontology accepted as OWL 2 DL by OWL API, on which HermiT 1.4.5.519 and Openllet 2.6.5 report consistency.

Run the cross-reasoner audit after building SABRINA (requires Java 17+ and Maven):

```sh
python3 benchmarks/sabrina-vs-reasoners/run_boundary_audit.py --out /tmp/boundary_audit.json
```

The [benchmark guide](benchmarks/sabrina-vs-reasoners/README.md) explains how to rerun all six tracks with the original workloads and pinned inputs. The [recorded results](results/) include all six tracks and the boundary audit.

## Citation and License

Cite the archived software release [10.5281/zenodo.24521179](https://doi.org/10.5281/zenodo.24521179). See [CITATION.cff](CITATION.cff) for citation metadata and [LICENSE](LICENSE) for the MIT license.
