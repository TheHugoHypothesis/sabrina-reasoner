# SABRINA

Lean 4 OWL 2 DL reasoning and certificate verification library (`v1.2.1`):

- Certifying fragments: `ALC`, `ALCH`, `ALCHI`, ranked `RoleChains`, and qualified cardinality (`Graded`).
- OWL 2 DL (`Sabrina/OWL2/`): Functional-Style Syntax, RDF/XML 1.1, and Turtle 1.1 parsers and serializers; W3C RDF-to-Structural mapping; OASIS XML import catalogs; strict §5.8.1–§5.8.2 and §11.2 validation; 33-datatype exact decision procedure with Unicode 17.0.0 XSD 1.1 regexes and Exc-C14N correspondence; 16-constructor SROIQ(D) soundness and completeness with n-ary and nominal-anchored GCI absorption and dependency-directed backjumping; kernel-verified DL-Safe SWRL rules with `swrlb:*` built-ins; 29-form query entailment; parallel $\mathcal{EL}^{++}$ (`FastEL.lean`) and Enhanced Traversal TBox classification; ABox realization; inferred ontology materialization (`.ofn`, `.ttl`, `.owl`); parallel minimal entailment/inconsistency justifications; hash-indexed $\bot$-locality extraction; and incremental DRed ABox sessions.

See the root [README](../../README.md) for build and verification commands.
