# Changelog

## 1.2.0 (2026-11-27)

### Added
- **Kernel-verified DL-Safe SWRL rules (`SWRL.lean`, `SWRLBuiltins.lean`, `SWRLReduction.lean`, `FunctionalSyntax.lean`, `RDF/OWLMapping.lean`, `RDF/Serialize.lean`, `StrictTyping.lean`, `Materialize.lean`, `CLI/OFNQuery.lean`, `CLI/SessionMain.lean`):**
  - Orthogonal DL-Safe SWRL AST, Direct Semantics, and DL-safety validator preserving `Sabrina.OWL2.Axiom` compatibility.
  - W3C Functional-Style Syntax (`DLSafeRule`), Turtle 1.1, and RDF/XML 1.1 (`swrl:Imp`) parsing and serialization with kernel-verified RDF round-trip (`owl2_rdf_swrl_roundtrip`).
  - Kernel-verified local data-variable and facet built-in roll-up (`rollupOneDataVar_holds_iff`), body-only individual-variable tree roll-up (`rollupOneIndVar_holds_iff`), direct single-individual grounding (`encodeSingleIndGroundRule_holds_iff`), nominal-guarded unary encoding (`encodeUnaryRule_holds_iff`), smart partial grounding (`encodeDLSafeRule_holds_iff`, `groundAllRules_sat_iff`, `groundAllRules_entails_iff`, `decideRealWithSWRL_iff`), and verified lazy CEGAR grounding (`decideWithSWRLFast?`).
  - Multi-rule concrete fixpoint chaining across arbitrary rule ordering and data subproperties, plus rule-level source-property pre-filtering.
  - Extended `swrlb:*` built-in coverage: exact arithmetic (including `pow` and `roundHalfToEven`), string operations (including `normalizeSpace`, `translate`, `substringBefore`, `substringAfter`, and regex `replace` with capture groups and ordered alternation), temporal/duration built-ins, and unconditional `builtinToDataRange_real_iff` for order, `matches`, and `stringLength`.
  - Inferred `DataPropertyAssertion` materialization (with opt-out option), SWRL entity-declaration checks under `--strict-owl2dl`, and SWRL-aware minimal justifications surfacing `DLSafeRule(...)`.
- **Non-EL tableau and justification speedups (`SROIQD/Model.lean`, `SROIQD/Search.lean`, `SROIQD/Termination/SROIQSearch.lean`, `Classification.lean`, `FastClassification.lean`, `Justification.lean`):**
  - Generalized GCI absorption (`absorptionPremises_sound`) to arbitrary $n$-ary positive atomic/nominal/self/data-value conjunctions (`A₁ ⊓ … ⊓ Aₙ ⊑ C`) and nominal-anchored / disjunctive nominal-guarded axioms (`nominalDisj?_sound`, `nominalGuard?_sound`), with direct label and ABox-edge existential triggering and deferred splitting.
  - Dependency-directed backjumping in both bounded and exact tableaux.
  - Parallel non-EL TBox classification, ABox realization, and batch-parallel Reiter Hitting-Set Tree (HST) justification enumeration via `Task.spawn`, with kernel-proved worker-count invariance (`findAllUnsatJustificationsParWith_workers_eq`, `findAllJustificationsParWith_workers_eq`) and soundness (`findAllUnsatJustificationsParReal_sound`, `findAllJustificationsParReal_sound`).

### Changed
- Scaled default SROIQ(D) world limits (`Limits.forProblem`) with input individuals.
- Updated package versions and `CITATION.cff` to `1.2.0`; expanded `scripts/verify_axioms.py` to 84 headline theorems.

## 1.1.1 (2026-11-26)

### Added
- Parallel, integer-interned, kernel-verified $\mathcal{EL}^{++}$ classifier (`FastEL.lean`) using `Task.spawn` context-sharded BSP saturation, parallel $O(|S| + |R|)$ rank-stratified soundness verification (`checkCertSound_entails_sub`, `checkCertSound_inconsistent`), parallel $O(|\mathcal{O}| + |S| + |R|)$ single global canonical model completeness verification (`checkCanonicalModel_sound`, `checkCanonicalModel_counter_sub`), and parallel sparse transitive reduction (`classifyFastELCore_sound_complete`, `classifyFastELToHierarchy_sound_complete`).
- CLI file-mode classification flags `sabrina-query --classify <in> [--summary-only] [--workers <n>]`, unit/cross-check suite (`FastELTests.lean`), and 1k–350k class scale benchmark (`benchmarks/fast-locality/bench_fast_el_scale.py`, 350,000 classes / 487,495 axioms / 8.41M subsumptions certified in 8.25 s).

### Changed
- Replaced quadratic `List.contains` deduplication in `Classification.dedupIRIs` with $O(N)$ `Std.HashSet` deduplication and replaced quadratic `ontologySig` scanning in `EL.normalizeEL` with a linear structural prefix check.

### Fixed
- **RDF loader metadata & import-closure declarations (`RDF/OWLMapping.lean`):** Preserved all non-`rdf:type` triples on named and blank-node `owl:Ontology` headers as ontology annotations (W3C OWL 2 RDF Mapping Table 4) without requiring explicit `owl:AnnotationProperty` declarations; added standard metadata vocabulary fallback (`dcterms:`, `dc:`, `skos:`, `vann:`, `oboInOwl:`, `foaf:`) for undeclared entity annotations; implemented two-phase import-closure declaration sharing (`AllDecl(G)`, W3C §3.1.2 Table 5) across reachable imports.
- **Multi-datatype preparation & solver scaling (`WiderDataReduction.lean`, `WiderDataAlgebra.lean`, `WiderDataCore.lean`, `DataRangeExact.lean`, `DataCSP.lean`, `StringLengthCells.lean`, `DataRanges.lean`, `SROIQD/Search.lean`, `Classification.lean`, `CLI/OFNQuery.lean`):**
  - Replaced full $2^N$ `vennPartitions` with kernel-verified family-, subtype-, `oneOf`-, and interval-pruned partition builders (`prunedWiderPartitions`, `prunedExactPartitions`).
  - Filtered empty intervals in `subtractRatBoundsOne`, `subtractNatBoundsOne`, and `subtractBoundsOne` to prevent $O(2^m)$ interval-difference blowups.
  - Made `widerCandidates` and `vennCandidates` family-targeted with early-stopping distinct filtering (`takeDistinctFilter`), and capped/deduplicated character options in `StringLengthCells.substitutions` (`takeDistinctChars`) before Cartesian expansion.
  - Capped `SolvedRange.finiteValues?` integer-interval enumeration (`< 1024`) so wide subtypes (`xsd:int`, `xsd:long`) never materialize $2^{32}$ / $2^{64}$ elements.
  - Enabled verified `SROIQD.propose` + `checkEvidence` fast path ahead of exhaustive `decideRealOntology?` on ordered/string-facet/wider-admissible `owl:real` problems, skipped redundant model construction on deterministic same-node tableau steps, and avoided building `fallbackCandidates` when solved-range candidates suffice.
  - Added generic regression tests (`RDFAndDatatypeScalingTests.lean`) and CLI benchmark (`benchmarks/datatype-scaling/run_datatype_scaling.py`).

## 1.1.0 (2026-11-25)

### Added
- Kernel-verified inferred OWL file materialization (`Materialize.lean`, `RDF/Serialize.lean`) exporting asserted and entailed axioms (class hierarchy, object property hierarchy, class and object-property realization, `SameIndividual`) to `.ofn`, `.ttl`, and `.owl` (RDF/XML) via `sabrina-query --materialize <in> -o <out>` and `"sabrina-materialize-v1"`, proved sound and model-preserving (`materializeWith_entailed`, `materializeReal_entailed`).
- Kernel-verified fast classification (`FastClassification.lean`): single-pass polynomial $\mathcal{EL}^{++}$ classification (`classifyELSinglePass_sound_complete`, `classifyDirectEL_sound_complete`), Enhanced Traversal with pre-indexed `FastLocality.LocalityIndex` (`classifyEnhancedWith_sound_complete`, `classifyEnhancedReal_sound_complete`), and verified `SROIQDModel` countermodel seeding (`harvestModelPairs_sound`, `classifyEnhancedStd_sound_complete`).
- Kernel-verified minimal justifications/explanations (`Justification.lean`): `FastLocality` pre-filtering + QuickXplain binary-split shrink + certified minimality sweep + Reiter Hitting-Set Tree enumeration for inconsistency and entailment via `sabrina-query --explain`, `"sabrina-explain-v1"`, and `sabrina-session` `"explain"` (`findOneUnsatJustificationReal_sound`, `findAllUnsatJustificationsReal_sound`, `findOneJustificationReal_sound`, `findAllJustificationsReal_sound`).

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
