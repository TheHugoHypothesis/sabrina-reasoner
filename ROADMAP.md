# Roadmap

This document records the milestones completed for `v1.0.0`. Every Lean module builds with zero `sorry` and strictly standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), checked by `scripts/verify_axioms.py`.

## Completed milestones

- **A. Strict W3C §11.2 validator** (`StrictOWL2DL.lean`, `8e8a679`): `--strict-owl2dl` and `"strict_owl2dl": true` enforcing `owl:topDataProperty` placement, anonymous-individual forest and single-named-root restrictions, XSD 1.1 pattern syntax, and regular/acyclic role hierarchies.
- **B. Declarations, punning, FSS, and import catalogs** (`FunctionalSyntax.lean`, `StrictTyping.lean`, `ImportCatalog.lean`, `426516b`): `Declaration(...)` and annotation-axiom parsing, prefixed ontology/version IRIs, Unicode and `PN_LOCAL_ESC` tokens, W3C §5.8.1–§5.8.2 typing and punning checks, and OASIS `catalog-v001.xml` / `--import-dir` loading.
- **C.1. Unicode 17.0.0 XSD 1.1 regular expressions** (`UnicodeCategories.lean`, `8e8a679`): `\d`/`\D`, `\w`/`\W`, `\p{...}`/`\P{...}` categories and blocks, nested character-class subtraction, and full-Unicode boundary sampling.
- **C.2. Standards correspondence** (`StandardsCorrespondence.lean`, `XMLCorrespondence.lean`, `RegexGrammarCorrespondence.lean`, `65b241f`): independent declarative specifications and correspondence theorems for `xsd:hexBinary`, IEEE-754 ties-to-even rounding, `xsd:dateTime`, RFC 4647 language ranges, Exclusive XML Canonicalization, and the XSD 1.1 Appendix G regex grammar. Renamed primary CLI to `sabrina-query`.
- **D. RDF/XML, Turtle, reasoning services, and W3C suite** (`RDF/`, `ExtendedQueryDecision.lean`, `Classification.lean`, `benchmarks/w3c-owl2-conformance/`, `a0ca51b`): native RDF 1.1 graph, RDF/XML 1.1 and Turtle 1.1 parsers, W3C OWL 2 RDF-to-Structural mapping with round-trip proof, 4-way entailment across 29 axiom forms and anonymous-individual queries, certified TBox classification and ABox realization, and a 42-test conformance suite.
- **E.1. Hash-indexed $\bot$-locality extraction** (`FastLocality.lean`, `benchmarks/fast-locality/`, `e8bd449`): inverted signature index, worklist fixpoint, and linear certificate verifier proved axiom-set-identical to `Profile.extractBotModule` (`extractBotModuleFast_mem_iff`, `extractBotModuleFast_entails_iff`), wired into `sabrina-query` and cached in `sabrina-session`.
- **E.2. Release hygiene** (`v1.0.0`): package versions aligned to `1.0.0`, documentation updated, and `v1.0.0` tagged on GitHub.
