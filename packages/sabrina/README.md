# SABRINA

Generic Lean 4 OWL 2 DL reasoning and certificate verification library (`v1.0.0`):

* **Complete certifying fragments:** `ALC`, `ALCH`, `ALCHI`, ranked `RoleChains`, and qualified cardinality (`Graded`).
* **Native W3C OWL 2 DL (`Sabrina/OWL2/`):**
  * Functional-Style Syntax, RDF/XML 1.1, and Turtle 1.1 parsers with W3C OWL 2 RDF-to-Structural mapping (`RDF/OWLMapping.lean`) and OASIS XML catalog import resolution (`CLI/ImportCatalog.lean`).
  * Strict W3C §11.2 and §5.8.1–§5.8.2 typing/punning validators (`StrictOWL2DL.lean`, `StrictTyping.lean`).
  * Direct Semantics, 33-datatype exact solver, Unicode 17.0.0 XSD 1.1 regex engine, and independent declarative standards correspondence (`StandardsCorrespondence.lean`, `XMLCorrespondence.lean`, `RegexGrammarCorrespondence.lean`).
  * Full 16-constructor $\mathcal{SROIQ}(\mathcal{D})$ decision procedure with fuel-free blocked-forest termination (`decideSROIQBool_ontology_iff`, `decideRegularOWL2DLReal_ontology_iff`), 29-form exact entailment (`ExtendedQueryDecision.lean`), and certified TBox classification & ABox realization (`Classification.lean`).
  * Hash-indexed $\bot$-locality module extraction (`FastLocality.lean`, `extractBotModuleFast_mem_iff`), polynomial $\mathcal{EL}^{++}$ classification, and provenance-tracked DRed incremental ABox sessions (`IncrementalABox.lean`).

This directory is an independent Lake package. See the root [README](../../README.md) and [ROADMAP](../../ROADMAP.md) for build and verification commands.
