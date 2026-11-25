# Changelog

## Unreleased

### Added
- Kernel-verified inferred OWL file materialization (`Materialize.lean`, `RDF/Serialize.lean`) exporting asserted and entailed axioms (class hierarchy, object property hierarchy, class and object-property realization, `SameIndividual`) to `.ofn`, `.ttl`, and `.owl` (RDF/XML) via `sabrina-query --materialize <in> -o <out>` and `"sabrina-materialize-v1"`, proved sound and model-preserving (`materializeWith_entailed`, `materializeReal_entailed`).
- Kernel-verified fast classification (`FastClassification.lean`): single-pass polynomial $\mathcal{EL}^{++}$ classification (`classifyELSinglePass_sound_complete`, `classifyDirectEL_sound_complete`), Enhanced Traversal with pre-indexed `FastLocality.LocalityIndex` (`classifyEnhancedWith_sound_complete`, `classifyEnhancedReal_sound_complete`), and verified `SROIQDModel` countermodel seeding (`harvestModelPairs_sound`, `classifyEnhancedStd_sound_complete`).

## 1.0.0 (2026-11-25)

### Added
- Strict OWL 2 DL validation (`--strict-owl2dl`) covering W3C §11.2 global restrictions (`StrictOWL2DL.lean`) and §5.8.1–§5.8.2 entity declarations and punning (`StrictTyping.lean`).
- Complete Functional-Style Syntax declaration/annotation parsing (`FunctionalSyntax.lean`) and OASIS XML catalog / `--import-dir` import resolution (`ImportCatalog.lean`).
- Unicode 17.0.0 XSD 1.1 regular expression engine (`UnicodeCategories.lean`) and independent standards-correspondence proofs (`StandardsCorrespondence.lean`, `XMLCorrespondence.lean`, `RegexGrammarCorrespondence.lean`).
- Native RDF 1.1 graph, RDF/XML 1.1 and Turtle 1.1 parsers, and W3C OWL 2 RDF-to-Structural mapping with round-trip verification (`RDF/Graph.lean`, `RDF/XMLParser.lean`, `RDF/TurtleParser.lean`, `RDF/OWLMapping.lean`).
- Exact 4-way query entailment across 29 OWL 2 DL axiom forms and existential anonymous-individual queries (`ExtendedQueryDecision.lean`).
- Certified TBox classification (`sabrina-classify-v1`) and ABox realization (`sabrina-realize-v1`) in `Classification.lean`, `sabrina-query`, and `sabrina-session`.
- Hash-indexed $\bot$-locality module extraction (`FastLocality.lean`) proved axiom-set-identical to `Profile.extractBotModule`, wired into `sabrina-query` and cached in `sabrina-session`, with a 350,000-axiom benchmark (`benchmarks/fast-locality/bench_snomed_scale.py`).
- 42-test W3C OWL 2 DL conformance script (`benchmarks/w3c-owl2-conformance/run_w3c_conformance.py`).

### Changed
- Renamed `sabrina-alc-query` / `Sabrina.CLI.ALCQuery` to `sabrina-query` / `Sabrina.CLI.Query`.
- Updated Lake package versions to `1.0.0`.

## release (initial artifact)

- Initial release accompanying *Cycles at the Edge of Decidability: SABRINA, a Kernel-Verified SROIQ(D) OWL 2 DL Reasoner* (DOI `10.5281/zenodo.24521179`).
