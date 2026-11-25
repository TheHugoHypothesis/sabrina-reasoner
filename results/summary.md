# SABRINA vs. HermiT 1.4.5 & ELK 0.6.0 — Benchmark Summary

- **Environment:** Linux-7.3.4-300.fc45.x86_64-x86_64-with-glibc2.44 | Java 27.0.1.0.3 | Lean 4.35.0
- **Reasoners:** SABRINA (Lean 4 compiled native) vs. HermiT 1.4.5.519 (OWL API 5.1.20) vs. ELK 0.6.0 (OWL API 5.1.20)

## Headline Results

1. **Track 1 — Normative BFO 2020 (30 queries, 192 axioms):**
   - SABRINA ↔ HermiT ↔ Gold agreement: **30/30** (100%)
   - ELK 0.6.0 agreement: **30/30**
   - Syntactic $\bot$-locality: shrank 192 axioms to median **5.0** axioms (range [3, 8]); **30/30** downgraded automatically to $\mathcal{EL}^{++}$
   - Cold CLI median: SABRINA **101.8 ms** vs. HermiT **394 ms** vs. ELK **442 ms**
   - Warm persistent median (with ontology load): SABRINA **33.5 ms** vs. HermiT **10.5 ms** vs. ELK **7.6 ms**
   - Warm batch on single loaded BFO 2020 (24 queries): SABRINA load 55.0 ms + queries **2.8 ms** (median 0.13 ms/q) vs. HermiT total **44.9 ms** (parse 8.7 + classify 24.5 + queries 11.7 ms) vs. ELK total **74.2 ms**

2. **Track 2 — Expressive $\mathcal{SROIQ}(\mathcal{D})$ (24 queries):**
   - SABRINA ↔ HermiT ↔ Gold agreement: **24/24** (100%)
   - ELK 0.6.0 agreement: **10/24** (expected: non-EL constructors unsupported)
   - Cold CLI median: SABRINA **39.5 ms** vs. HermiT **317 ms**
   - Warm median: SABRINA **0.4 ms** vs. HermiT **2.6 ms**

3. **Track 3 — $\mathcal{EL}^{++}$ Scaling ($N = 50 \dots 1000$ axioms):**

| Axioms ($N$) | $\bot$-Module ($M$) | Reduction | SABRINA Warm | SABRINA Cold | HermiT Warm | ELK Warm |
|---:|---:|---:|---:|---:|---:|---:|
| 50 | 6 | 88.0% | 0.8 ms | 20.3 ms | 3.1 ms | 3.0 ms |
| 100 | 6 | 94.0% | 1.2 ms | 20.3 ms | 3.3 ms | 3.0 ms |
| 250 | 6 | 97.6% | 2.5 ms | 20.5 ms | 4.7 ms | 3.9 ms |
| 500 | 6 | 98.8% | 5.3 ms | 21.2 ms | 7.1 ms | 5.4 ms |
| 1000 | 6 | 99.4% | 13.0 ms | 22.9 ms | 10.4 ms | 8.3 ms |

4. **Track 4 — Incremental ABox DRed Sessions:**
   - Suite 5 (10 sessions, 27 checkpoints): 100% agreement (SABRINA=True, HermiT=True, ELK=True).
   - Suite 5 median step latency: SABRINA **0.27 ms** vs. ELK **6.73 ms** vs. HermiT **5.58 ms**
   - 50-Step Stress (206-ax. $\mathcal{EL}^{++}$ TBox, 18 checkpoints): 100% agreement ({'sabrina': True, 'hermit': True, 'elk': True}).
   - 50-Step total mutation+query time: SABRINA **1.68 ms** (0.034 ms/step) vs. ELK **45.86 ms** (0.917 ms/step) vs. HermiT **60.89 ms** (1.218 ms/step).

5. **Track 5 — Real Consolidated OBO Foundry Ontologies (5,657 to 71,501 Logical Axioms, 40/40 Agreement):**

| Ontology | Axioms | Classes | Full Frag. | $\bot$-Mod ($M$) | Red. | Agree. | SABRINA Cold | HermiT Warm | ELK Warm | HermiT Classify | ELK Classify |
|---|---:|---:|:---:|---:|---:|:---:|---:|---:|---:|---:|---:|
| CL-basic (Cell Ontology) | 5,657 | 3,976 | EL++ | 23 | 99.59% | 10/10 | 60.4 ms | 62.6 ms | 57.3 ms | 292.8 ms | 155.1 ms |
| DOID (Human Disease) | 28,247 | 16,629 | SROIQ(D) | 15 | 99.95% | 10/10 | 213.9 ms | 255.3 ms | 189.9 ms | 1037.5 ms | 195.3 ms |
| UBERON-basic (Anatomy) | 30,459 | 16,434 | EL++ | 91 | 99.70% | 10/10 | 280.8 ms | 253.3 ms | 206.7 ms | 1089.0 ms | 140.1 ms |
| GO-basic (Gene Ontology) | 71,501 | 51,986 | EL++ | 8 | 99.99% | 10/10 | 580.8 ms | 670.8 ms | 501.2 ms | 1787.7 ms | 278.2 ms |

6. **Track 6 — Exact Cyclic $\mathcal{SROIQ}(\mathcal{D})$, Wider Datatypes, String Facets, Built-In Properties & Unified Role Hierarchies (18 items):**
   - SABRINA kernel-verified: **18/18** (100%, cold CLI median **26.16 ms**)
   - HermiT 1.4.5: **15/18** (100% agreement on all accepted items; **3** syntactic/regularity rejections, warm median **4.8 ms**)
   - ELK 0.6.0: **6/18** (non-EL features unsupported)
