# SABRINA Roadmap to Full W3C OWL 2 DL Conformance

This roadmap tracks `sabrina-reasoner` from its archived `v0.1.0-alpha` release ([DOI 10.5281/zenodo.24521179](https://doi.org/10.5281/zenodo.24521179)) and post-release `main` (`8e8a679`) to **full W3C OWL 2 DL conformance (`v1.0.0`)**.

All Lean 4 proofs in this repository are required to build with **zero `sorry`**, **zero custom axioms**, and strictly standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), verified on every milestone by `lake build && python3 scripts/verify_axioms.py`.

---

## Completed Foundation (`v0.1.0-alpha` + `main` @ `8e8a679`)

| Area | Status | Key Modules & Verified Guarantees |
|---|---|---|
| **$\mathcal{SROIQ}(\mathcal{D})$ Logical Core** | Done | All 16 OWL 2 class constructors, TBox/RBox/ABox Direct Semantics, nominals, inverse roles, qualified cardinalities, mixed object/data `HasKey`, cyclic GCIs, and fuel-free blocked-forest termination (`decideSROIQBool_ontology_iff`, `decideRegularOWL2DLReal_ontology_iff`). |
| **Role Hierarchies & Built-in Properties** | Done | Exact dependency-acyclic admission (`AcyclicOWL2DLHierarchy`), W3C §11.1–§11.2 simple-role checks with universal roles, and complete elimination of `owl:topObjectProperty`, `owl:bottomObjectProperty`, `owl:topDataProperty`, and `owl:bottomDataProperty`. |
| **33-Datatype Exact Solver** | Done | Mechanized 33-datatype map: Dedekind-cut `owl:real`, IEEE-754 `xsd:float`/`xsd:double` order facets, 14h-shift `xsd:dateTime`/`xsd:dateTimeStamp`, length facets, `DataOneOf`, `rdf:langRange`, and `rdf:XMLLiteral`. |
| **Milestone C.1: W3C XSD 1.1 Unicode Regex** | Done (`8e8a679`) | Exact Unicode 17.0.0 General Category tables (`UnicodeCategories.lean`), `\d`/`\D` = `\p{Nd}`, `\w`/`\W` = `[^\p{P}\p{Z}\p{C}]`, `\p{...}`/`\P{...}` (30 subcategories, 7 major categories, 91 `Is...` blocks), nested character-class subtraction `[base-[sub]]`, and exact full-Unicode boundary sampling (`UnicodeStringSampling.sample_exact`). |
| **Milestone A: Strict W3C §11.2 Validator** | Done (`8e8a679`) | `StrictOWL2DL.lean` + `--strict-owl2dl` CLI flag / `"strict_owl2dl": true` JSON option: enforces `owl:topDataProperty` placement, anonymous-individual prohibitions & simple-forest/single-named-root rules, XSD 1.1 pattern syntax, and strict regular/acyclic role hierarchies (`checkStrictOWL2DL_iff`, `diagnoseStrictOWL2DL_isNone_iff`, `decideStrictOWL2DLReal_iff`). |
| **Milestone B: Declarations, Punning & FSS** | Done (`v0.2.0` ready) | `FunctionalSyntax.lean` + `StrictTyping.lean` + `ImportCatalog.lean`: full `Declaration(...)` and annotation-axiom parsing, prefixed ontology/version IRIs, Unicode & `PN_LOCAL_ESC` tokens, W3C §5.8.1–§5.8.2 typing completeness & punning disjointness (`checkTyping_iff`, `diagnoseTyping_isNone_iff`, `decideStrictTypedOWL2DLReal_iff`), and OASIS `catalog-v001.xml` / `--import-dir` CLI resolution. |
| **Performance & Incremental Stack** | Done | Syntactic $\bot$-locality module extraction (`extractBotModule_entails_iff`), polynomial $\mathcal{EL}^{++}$ classifier + canonical models, and provenance-tracked DRed incremental ABox sessions (`IncrementalABox.lean`). |

---

## Remaining Milestones

### Milestone B — Entity Declarations, Punning & Complete Functional-Style Syntax (`v0.2.0`) — COMPLETED
- [x] **B.1 Entity Declaration Parsing & Typing Closure (`FunctionalSyntax.lean`, `StrictTyping.lean`)**
- [x] **B.2 Complete Functional-Style Syntax Grammar (`FunctionalSyntax.lean`)**
- [x] **B.3 OASIS XML Catalog & Directory Import Resolution (`CLI/ImportCatalog.lean`, `CLI/ALCQuery.lean`)**

---

### Milestone C.2 — Datatype, Lexical-Decoder & `rdf:XMLLiteral` Standards Correspondence (`v0.3.0`)
**Goal:** Close the remaining datatype trust boundaries between SABRINA's internal 33-datatype model and the external W3C XSD 1.1 / RDF 2004 specifications.

- [ ] **C.2.1 Lexical Decoder Edge-Case Audit & Independent Reference Proofs (`Datatypes/`)**
  - Audit and formalize edge-case lexical forms across all 33 datatypes:
    - `xsd:anyURI` RFC 3987 IRI syntax validation.
    - `xsd:language` & `rdf:langRange` full BCP 47 / RFC 4647 syntax.
    - `xsd:float` / `xsd:double` exact IEEE-754 round-to-nearest-even lexical parsing for arbitrary decimal mantissas/exponents.
    - `xsd:dateTime` / `xsd:dateTimeStamp` proleptic Gregorian boundary cases (year `0000` in XSD 1.1 vs XSD 1.0, `24:00:00` normalization, leap years).
  - Prove round-trip / correspondence theorems relating executable decoders to declarative W3C lexical-space predicates.
- [ ] **C.2.2 Independent `rdf:XMLLiteral` / Exclusive XML Canonicalization Correspondence**
  - Relate `XMLLiteralValidation.lean` to an independent formalization of XML 1.0 Fifth Edition well-formedness, Namespaces in XML 1.0, and Exclusive XML Canonicalization (Exc-C14N: attribute sorting, namespace rendering, empty-element expansion, comment/PI handling).
- [ ] **C.2.3 Independent XSD 1.1 Regex Grammar Correspondence**
  - Formalize the W3C XSD 1.1 Part 2 Appendix G BNF grammar directly and prove `parseCompleteRegex` sound and complete with respect to that grammar (including full edge cases of `-`, `^`, escapes inside `[...]`, and quantifier precedence).

**Exit criteria:** Pass all W3C OWL 2 datatype/facet/XML conformance tests with kernel-checked correspondence theorems for lexical decoding, XSD 1.1 regex parsing, and Exc-C14N.

---

### Milestone D — Mandatory RDF/XML Serialization, Full Reasoning Services & Official W3C Test Suite (`v0.4.0`–`v1.0.0`)
**Goal:** Satisfy the W3C OWL 2 Conformance specification (§2.1), which requires **RDF/XML** support, complete OWL 2 DL reasoning services, and empirical validation on the official W3C OWL 2 test suite.

- [ ] **D.1 Verified RDF Graph Model & RDF/XML + Turtle Parsers**
  - Implement a native Lean 4 RDF/XML parser (and Turtle parser) producing typed RDF triple graphs (with blank-node scoping, `xml:base`, `rdf:List`, `rdf:datatype`, `xml:lang`).
  - Implement and verify the **W3C OWL 2 Mapping from RDF Graphs to the Structural Specification** (Tables 3–18: header/imports, declarations, reverse mapping of `owl:Restriction`, `owl:intersectionOf`/`unionOf`/`oneOf`, `owl:propertyChainAxiom`, `owl:AllDisjointClasses`, `owl:AllDifferent`, `owl:NegativePropertyAssertion`, `owl:hasKey`, `owl:withRestrictions`, and strict rejection of unconsumed/malformed RDF triples in OWL 2 DL).
  - Prove round-trip / semantic preservation for the RDF-to-Structural mapping.
- [ ] **D.2 Complete OWL 2 DL Reasoning & Query Services**
  - **Arbitrary Axiom Entailment:** Extend `ExactQueryDecision.lean` beyond the current 10 anonymous-free query axiom forms to support:
    - Object/data property queries (`SubObjectPropertyOf`, `SubObjectPropertyOf(ObjectPropertyChain ...)`, `EquivalentObjectProperties`, `DisjointObjectProperties`, `InverseObjectProperties`, `ObjectPropertyDomain/Range`, all role characteristics, `SubDataPropertyOf`, `EquivalentDataProperties`, `DisjointDataProperties`, `DataPropertyDomain/Range`, `FunctionalDataProperty`, `HasKey`).
    - Queries containing anonymous individuals (existential conjunctive/tree blank-node entailment).
  - **Ontology Classification & Realization:** Expose certified full TBox classification (complete named-class subsumption DAG + equivalence classes) and ABox realization (most specific named classes per individual) via `sabrina-alc-query` and `sabrina-session`.
- [ ] **D.3 Official W3C OWL 2 Conformance Test Suite Gate**
  - Add a reproducible harness in `benchmarks/` running the official W3C OWL 2 DL WebOnt / OWL 2 Test Cases (consistency, positive entailment, negative entailment, and non-DL syntax-rejection tests).
  - Make the W3C test suite a CI gate alongside `scripts/verify_axioms.py`.

**Exit criteria:** Native RDF/XML + FSS ingestion, full classification/realization/entailment services, and 100% pass rate on the official W3C OWL 2 DL conformance test suite under `--strict-owl2dl`.

---

### Milestone E — Production Scale & Ecosystem Integration (`v1.0.0+`)
**Goal:** Scale verified OWL 2 DL reasoning to 350,000+-axiom clinical terminologies and standard Semantic Web toolchains.

- [ ] **E.1 Hash-Indexed $\bot$-Locality Extraction (`Profile.lean`)**
  - Replace linear axiom scans in `extractBotModule` with an indexed signature-to-axiom worklist (while proving the indexed extractor returns the exact same module as the specification in `extractBotModule_entails_iff`), targeting sub-second extraction on full SNOMED CT (~350,000 axioms).
- [ ] **E.2 Persistent Reasoning Server & OWL API / OWLLink Adapter**
  - Extend `sabrina-session` with a persistent JSON-RPC / OWLLink protocol supporting batch classification, incremental updates, and strict mode without per-query cold-start overhead.
  - Provide a thin Java `OWLReasoner` wrapper (OWL API 5) delegating to the native `sabrina-session` binary for drop-in use in Protégé and ROBOT pipelines.
- [ ] **E.3 Release & Archival Hygiene**
  - Tag semantic releases (`v0.2.0`, `v0.3.0`, `v1.0.0`) on GitHub so Zenodo automatically mints versioned DOIs linked to the concept DOI.

---

## Suggested Release Sequence

1. **`v0.2.0`**: Milestone C.1 *(done)* + Milestone A *(done)* + **Milestone B** (Declarations, punning & complete FSS)
2. **`v0.3.0`**: **Milestone C.2** (Lexical, Exc-C14N & XSD 1.1 grammar correspondence)
3. **`v0.4.0`**: **Milestone D.1–D.2** (RDF/XML mapping + full axiom entailment, classification & realization)
4. **`v1.0.0`**: **Milestone D.3 + E.1** (Official W3C OWL 2 DL Conformance Test Suite + hash-indexed $\bot$-locality)
