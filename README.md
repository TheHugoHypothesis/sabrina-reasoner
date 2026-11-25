# SABRINA: Kernel-Verified $\mathcal{SROIQ}(\mathcal{D})$ and OWL 2 DL Reasoner (Lean 4)

Reproducible code, mechanized proofs, minimal counterexamples, and empirical benchmark harnesses accompanying:

> **Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified $\mathcal{SROIQ}(\mathcal{D})$ and OWL 2 Reasoner**  
> Hugo Cardoso Ferreira de Araújo (Universidade de São Paulo, Brazil)

## Repository Layout

- `packages/logic-core/` — Verified first-order natural-deduction proof bedrock (`LogicCore`, 33 Lean 4 modules).
- `packages/sabrina/` — Native OWL 2 DL / $\mathcal{SROIQ}(\mathcal{D})$ engine in Lean 4:
  - Functional-Style Syntax core parser & W3C Direct Semantics over $(\Delta_I, \Delta_D)$
  - Mechanized 33-datatype Venn-cell, Dedekind-cut `owl:real`, IEEE-754 float/double, timeline, and partial-derivative automaton solvers
  - Complete elimination of all four built-in universal/bottom properties
  - Total, fuel-free, rank-free cyclic blocked-forest decision procedure (`Sabrina/OWL2/SROIQD/Termination/`)
  - Exact weak/strict dependency-graph role-hierarchy rankability characterization and mechanized CFG-intersection undecidability reduction for literal pairwise W3C §11.1–§11.2 (`ObjectHierarchyBoundary.lean`, `OWLHierarchy.lean`)
  - Syntactic $\bot$-locality module extraction, polynomial $\mathcal{EL}^{++}$ completion, and provenance-tracked DRed incremental ABox engine
- `WorkspaceCLI/` — Native CLI executables (`sabrina-alc-query`, `sabrina-session`).
- `counterexamples/` — Standalone OWL 2 Functional-Style Syntax (`.ofn`) ontologies (`T1`, `T1b`, `T2`, `T3`, `T3b`, `T4`, `T5`) for direct reproduction in Protégé, HermiT, Openllet/Pellet, JFact/FaCT++, OWL API, and SABRINA.
- `benchmarks/` — Reproducible JSON benchmark harnesses (`benchmarks/sabrina-vs-reasoners/run_benchmark.sh`, `run_track5_obo.py`, `run_track6_exact_owl2dl.py`, `run_boundary_audit.py`, `java-harness/`, `boundary-harness/`) and the pinned ISO/IEC 21838-2 BFO 2020 core ontology (`benchmarks/data/bfo-core.ofn`).
- `results/` — Raw unaggregated JSON timing logs from all six benchmark tracks (`reasoner_benchmark.json`, `track5_obo_realworld.json`, `track6_exact_owl2dl.json`) and the cross-reasoner boundary audit (`boundary_reasoner_audit.json`), plus `summary.md`.
- `scripts/verify_axioms.py` — Automated zero-`sorry` and standard-foundational-axiom audit (`propext`, `Classical.choice`, `Quot.sound`).

## Quick Start

### 1. Build & Verify All Lean 4 Proofs and Native Binaries

Requires Lean `v4.35.0` (managed automatically via `elan` and `lean-toolchain`):

```bash
lake build
python3 scripts/verify_axioms.py
```

`lake build` builds the `@[default_target]` `Verification` umbrella module (importing `Logic`, `LogicTests`, `Sabrina`, `SabrinaTests`, and all standalone `SROIQD/Termination/` admission and undecidability modules) alongside the native `sabrina-alc-query` and `sabrina-session` binaries, so every Lean proof in the repository is kernel-checked with a single command.

### 2. Reproduce the Cross-Reasoner Role-Hierarchy Boundary Audit (`T1`–`T5`)

Requires Java 17+ and Maven (downloads OWL API 5.1.20, JFact 5.0.3, HermiT 1.4.5.519, and Openllet 2.6.5 automatically):

```bash
python3 benchmarks/sabrina-vs-reasoners/run_boundary_audit.py --out /tmp/boundary_audit.json
```

In particular, `counterexamples/T1_acyclic_valid_owl2dl.ofn` is a **9-axiom, 100% valid acyclic W3C OWL 2 DL ontology** (`OWL2DLProfile = true`, 0 violations) that is mathematically **UNSATISFIABLE**:
- **SABRINA (Lean 4):** `INCONSISTENT_ONTOLOGY` (`lean_verified = true`, ~20 ms)
- **JFact 5.0.3 (FaCT++):** `INCONSISTENT`
- **HermiT 1.4.5.519:** `CONSISTENT` *(silent soundness bug)*
- **Openllet 2.6.5 (Pellet):** `CONSISTENT` *(silent soundness bug)*

### 3. Reproduce Track 5, Track 6, and Boundary Audit Benchmarks (Raw JSON)

```bash
./benchmarks/sabrina-vs-reasoners/run_benchmark.sh --out-dir /tmp/sabrina-eval
```

This runs Track 5 (four consolidated OBO Foundry biomedical ontologies up to 71,501 axioms downloaded via `download_corpora.sh`), Track 6 (15 W3C OWL 2 DL conformant queries + 3 non-DL §11.2 extensions), and the Cross-Reasoner Boundary Audit (`T1`–`T5`), writing raw JSON logs into `/tmp/sabrina-eval/raw/`. Pre-recorded raw JSON logs for all six tracks (including Tracks 1–4) and the boundary audit are archived in `results/`.

## License

MIT License (see `LICENSE`).
