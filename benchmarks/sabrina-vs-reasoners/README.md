# SABRINA benchmarks

The benchmark compares SABRINA with HermiT 1.4.5.519 and ELK 0.6.0. The role hierarchy audit also runs JFact 5.0.3 and Openllet 2.6.5. Both Java harnesses use OWL API 5.1.20.

## Run the suite

From the repository root, with Lean 4.35.0, Python 3, Java 17 or later, Maven, Bash, and curl:

```sh
lake build
./benchmarks/sabrina-vs-reasoners/run_benchmark.sh --out-dir /tmp/sabrina-eval
```

The runner builds the Java harnesses and writes fresh JSON to `/tmp/sabrina-eval/raw/`. The [published results](../../results/) provide reference verdicts. Wall-clock timings depend on the machine and runtime versions.

| Track | Workload | Output |
| --- | --- | --- |
| 1 | BFO 2020 core and domain extensions, 30 queries | `reasoner_benchmark.json` |
| 2 | Expressive SROIQ(D), 24 queries | `reasoner_benchmark.json` |
| 3 | Synthetic EL++ scaling, 50 to 1,000 axioms | `reasoner_benchmark.json` |
| 4 | Ten incremental sessions and a 50-step assertion/retraction workload | `reasoner_benchmark.json` |
| 5 | Four OBO Foundry corpora, 40 queries | `track5_obo_realworld.json` |
| 6 | Eighteen stress cases, including three Direct Semantics extensions | `track6_exact_owl2dl.json` |
| Role hierarchy audit | Seven counterexamples | `boundary_reasoner_audit.json` |

[run_eval.py](run_eval.py) runs Tracks 1 through 4 using the original [workloads](workloads/) and the [BFO 2020 core](../data/bfo-core.ofn). It generates the scaling and 50-step workloads deterministically. The runner and fixture sources come from the development commits `4c6687a` and `f3e015f`, respectively.

## Track 5 inputs

[track5_corpora.py](track5_corpora.py) pins Cell Ontology, Human Disease Ontology, and Uberon to dated upstream releases. It checks the SHA-256 digests of the downloaded OWL files and their Functional-Style Syntax conversions. The Track 5 runner also checks the OFN digests when run separately. All four OFN digests match the published benchmark results.

The [GO-basic snapshot](snapshots/go-basic.ofn.gz) contains the exact GO input used in the benchmark. It comes from the Gene Ontology Consortium’s [GO-basic download](https://current.geneontology.org/ontology/go-basic.owl), with embedded version IRI `http://purl.obolibrary.org/obo/go/releases/2026-07-26/go.owl`. The benchmark converted it to Functional-Style Syntax, retaining declarations and logical axioms and removing annotations and SWRL rules. The snapshot is distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See the [Gene Ontology citation policy](https://geneontology.org/docs/go-citation-policy/).
