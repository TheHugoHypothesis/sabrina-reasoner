# SABRINA

Generic, BFO-independent Lean 4 OWL 2 DL reasoning and certificate verification library:

* **Complete certifying fragments:** `ALC`, `ALCH`, `ALCHI`, ranked `RoleChains`, and qualified cardinality (`Graded`).
* **Native W3C OWL 2 DL (`Sabrina/OWL2/`):** Functional-Style Syntax parser/serializer, structural validator, Direct Semantics, definitional normalizer, 16-datatype ground data checker, full 16-constructor `SROIQ(D)` soundness & budget-independent refutation completeness (`ontology_unsat_iff_sroiqdRefutation`), syntactic ⊥-locality module extraction (`extractBotModule_entails_iff`), polynomial `EL++` classifier + canonical models, and provenance-tracked DRed incremental ABox sessions (`IncrementalABox.lean`).
* **HermiT tools (`tools/hermit/`):** Optional external comparison & legacy trace-reconstruction utilities.

This directory is an independent Lake package. See [docs/PACKAGES.md](../../docs/PACKAGES.md) and [docs/notes/41-owl2dl-feature-registry.md](../../docs/notes/41-owl2dl-feature-registry.md).
