# SABRINA vs. HermiT 1.4.5 & ELK 0.6.0 Runtime Benchmark

Reproducible empirical performance and agreement benchmark comparing **SABRINA** (Lean 4 kernel-verified OWL 2 DL reasoning engine) against two standard unverified Java production reasoners running on OWL API 5.1.20:

- **HermiT 1.4.5.519** (`net.sourceforge.owlapi:org.semanticweb.hermit:1.4.5.519`) — full OWL 2 DL hypertableau reasoner
- **ELK 0.6.0** (`io.github.liveontologies:elk-owlapi:0.6.0`) — polynomial OWL 2 EL consequence-based reasoner

## Benchmark Tracks

1. **Track 1 — Normative BFO 2020 Core Ontology (`bfo-core.ofn`, 192 axioms) & Domain Extensions (30 queries):** Cold single-shot CLI, warm persistent process, warm batch on a single loaded ontology, syntactic $\bot$-locality module reduction, and 3-valued agreement.
2. **Track 2 — Expressive $\mathcal{SROIQ}(\mathcal{D})$ Reasoning (24 queries):** Role chains, inverses + $\forall/\exists$, nominals without UNA, qualified cardinality, `HasKey`, and `xsd:integer` datatype facets.
3. **Track 3 — $\mathcal{EL}^{++}$ Scaling & Syntactic $\bot$-Locality ($N \in \{50, 100, 250, 500, 1000\}$ axioms):** Scaling curves on modular biomedical-style $\mathcal{EL}^{++}$ ontologies.
4. **Track 4 — Incremental ABox Assertion & Retraction (DRed):** 10 multi-turn Suite-5 sessions (27 query checkpoints) plus a 50-step incremental assert/retract stress session over a 206-axiom $\mathcal{EL}^{++}$ TBox.
5. **Track 5 — Real Consolidated OBO Foundry Biomedical Ontologies (5,657 to 71,501 Logical Axioms):** 40 balanced queries (5 multi-hop entailed + 5 reverse open per ontology) across **CL-basic** (Cell Ontology, 5,657 axioms), **DOID** (Human Disease Ontology, 28,247 axioms, full $\mathcal{SROIQ}(\mathcal{D})$), **UBERON-basic** (Anatomy, 30,459 axioms), and **GO-basic** (Gene Ontology, 71,501 axioms, 51,986 classes), downloaded reproducibly via `download_corpora.sh`.

## Usage

```bash
./benchmarks/sabrina-vs-reasoners/run_benchmark.sh \
  --out-dir "../bfo-papers/papers/02-sabrina-owl2dl/eval-results"
```
