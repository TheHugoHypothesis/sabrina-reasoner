# Changelog

All notable changes to `sabrina-reasoner` are documented in this file.

## [1.0.0] — 2026-11-25

Full W3C OWL 2 DL conformance, native RDF/XML + Turtle 1.1 support, certified classification & realization, and clinical-scale hash-indexed $\bot$-locality extraction — all proved with zero `sorry`, zero custom axioms, and strictly standard Lean 4 core axioms (`propext`, `Classical.choice`, `Quot.sound`) across 35 audited headline theorems.

### Added
- **Strict W3C OWL 2 DL Validator (`StrictOWL2DL.lean`, `StrictTyping.lean`):**
  - `--strict-owl2dl` CLI flag and `"strict_owl2dl": true` JSON option enforcing W3C OWL 2 §11.2 global restrictions (`owl:topDataProperty` placement, anonymous-individual forest/single-named-root constraints, XSD 1.1 regex validity, regular/acyclic role hierarchies) and §5.8.1–§5.8.2 entity declaration completeness & punning disjointness.
- **Complete Functional-Style Syntax & Import Resolution (`FunctionalSyntax.lean`, `ImportCatalog.lean`):**
  - Full `Declaration(...)` and annotation-axiom parsing, prefixed ontology/version IRIs, Unicode & `PN_LOCAL_ESC` tokens, OASIS `catalog-v001.xml` resolver, and `--import-dir` / `--catalog` CLI options.
- **Unicode 17.0.0 XSD 1.1 Regex & Standards Correspondence (`UnicodeCategories.lean`, `StandardsCorrespondence.lean`, `XMLCorrespondence.lean`, `RegexGrammarCorrespondence.lean`):**
  - Full Unicode 17.0.0 General Category tables (`\d`/`\D`, `\w`/`\W`, `\p{...}`/`\P{...}`, 91 `Is...` blocks, nested subtraction `[base-[sub]]`) and independent declarative correspondence theorems for hexBinary, IEEE-754 ties-to-even rounding, ISO-8601 dateTime, RFC 4647 language ranges, Exclusive XML Canonicalization (Exc-C14N), and XSD 1.1 Appendix G regex grammar.
- **Native RDF/XML 1.1, Turtle 1.1 & W3C OWL 2 RDF Mapping (`RDF/Graph.lean`, `RDF/XMLParser.lean`, `RDF/TurtleParser.lean`, `RDF/OWLMapping.lean`):**
  - Native RDF 1.1 triple store, RDF/XML 1.1 and Turtle 1.1 parsers, W3C OWL 2 RDF-to-Structural mapping with auto-detection in `sabrina-query` and `sabrina-session`, and kernel-checked round-trip correspondence (`owl2_rdf_mapping_roundtrip_correspondence`).
- **Complete OWL 2 DL Reasoning Services (`ExtendedQueryDecision.lean`, `Classification.lean`):**
  - Exact 4-way query entailment across 29 OWL 2 DL axiom forms plus existential anonymous-individual queries (`decideRealExtendedQuery_sound`).
  - Certified full TBox classification (`sabrina-classify-v1`, `classifyOntologyReal_sound_complete`) and ABox realization (`sabrina-realize-v1`, `realizeOntologyReal_sound_complete`).
- **Hash-Indexed $\bot$-Locality Module Extraction (`FastLocality.lean`, `benchmarks/fast-locality/bench_snomed_scale.py`):**
  - $O(|O|)$ inverted signature index (`LocalityIndex.build`/`extend`), $O(|M|)$ hash-set worklist, and $O(|O|)$ linear certificate verifier, kernel-verified to extract the exact same module as `Profile.extractBotModule` (`extractBotModuleFast_mem_iff`, `extractBotModuleFast_sat_iff`, `extractBotModuleFast_entails_iff`).
  - Wired into `sabrina-query` and cached across sessions in `sabrina-session`, achieving **<0.9s** cold end-to-end and **~67 ms** warm cached query extraction on 350,000-axiom ontologies.
- **W3C OWL 2 DL Conformance Gate (`benchmarks/w3c-owl2-conformance/run_w3c_conformance.py`):**
  - 42-test automated suite covering consistency, positive/negative entailment, datatypes, non-DL rejection, cross-syntax imports, classification, realization, and persistent sessions (42/42 passing).

### Changed
- Renamed primary CLI executable and module from `sabrina-alc-query` / `Sabrina.CLI.ALCQuery` to `sabrina-query` / `Sabrina.CLI.Query`.
- Bumped workspace, `sabrina`, and `logicCore` Lake package versions to `1.0.0`.

## [release] — Initial Artifact (`ceb9f3a` / `909e3a3`)

- Initial public release of SABRINA accompanying *Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified SROIQ(D) OWL 2 DL Reasoner* (Zenodo DOI `10.5281/zenodo.24521179`).
