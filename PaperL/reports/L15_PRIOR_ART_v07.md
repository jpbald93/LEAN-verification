# Layer 15 — prior-art verdict table re-run on draft v0.7

Re-run 2026-11-26 on `DRAFT.md` v0.7 (sha256 of the file at the time of this table is recorded in
`L15_PRIOR_ART_v07.md` alongside the draft copy). **No new search was run for this layer.** The
instrument is unchanged from the 2026-11-24 table: `SCOUT.md` §0 (26 search rows, run 2026-11-16/17
against Mathlib pin `0df444a3`, GitHub code search, Isabelle AFP, atlas-lean, lean-genius,
Rocq/GeoCoq/HighSchoolGeometry, HOL Light, HOL4, Metamath `set.mm`, Mizar MML listing, the
formal-conjectures/compfiles collections, ProofAtlas sitemap (751 URLs), arXiv, OpenAlex, Crossref,
Semantic Scholar, HAL, Zenodo, StackExchange math/MO, non-English web, and a local numeric check),
with verdict rows L1–L9b of `SCOUT.md` §1. What this layer re-does is the *expression* step: every
sentence of v0.7 that carries a prior-art obligation is mapped to the row that licenses it, and the
sentences that carry none are listed so that a reader can see the boundary.

Verdicts are the scout's. Where the draft and the scout disagree, the draft is wrong and is marked
**MISMATCH** below.

## 1. Claim-by-claim verdicts against the v0.7 text

| id | sentence in v0.7 (quoted or paraphrased) | where | prior art (mathematics) | formalisation | scout row | verdict |
|---|---|---|---|---|---|---|
| A | "the three pairwise second intersections … lie on a generalized circle" (level 3) | §2.3, Statement 7 | classical; Mathlib `Concyclic`/`Circumcenter` API, not stated as a chain base | API present, no named theorem | L1 `NONE-FOUND` as a named statement | not a novelty claim; base case |
| B | level 4 = Clifford's first theorem | §2.2 | Clifford 1871/1882; Coxeter 1969 | **ours**, Paper D (Zenodo 23653309) | L2 `EXISTS-FULL` (own work) | reuse, labelled (§1.2 bullet 4) |
| C | level 5 | §2.2 | classical; Paper D | **ours** | L3 `EXISTS-FULL` (own) | reuse, labelled |
| D | level 6, and the finite-plane failure at 6 | §2.2 | classical; Paper D records the failure | **ours** | L4 `EXISTS-FULL` (own) | reuse, labelled |
| E | "**first machine-checked treatment of the chain for arbitrary n**" | §1, last sentence | classical: Clifford, Morley 1900, Carver 1920, Longuet-Higgins 1972; Bobenko–Schief (arXiv:1509.04109) for the cross-ratio route | `NONE-FOUND` in any assistant at any n > 6 | L5 `NONE-FOUND` | **the one novelty claim**; formalisation only, and §1 says so |
| F | the uniform step / two-payload proof ("C6" in §1.1) | §1.1 | the Miquel + cross-ratio extension argument (Bobenko–Schief; Martini–Spirova 2008 for Cayley–Klein planes) | `NONE-FOUND` | L6 `NONE-FOUND` | second novelty claim, formalisation only; §1 states the mathematics is Bobenko–Schief's |
| G | Carver's key-matrix criterion and the ∞ case | §1, §1.2, §5.9 | **Carver 1920 §5–§6, Theorem 13** (read in full) | `NONE-FOUND`, **and not formalised here** | L7 `EXISTS-FULL` maths / `NONE-FOUND` formalisation | carried by Carver, never claimed; §1.2 and §5.9 both say it is not formalised |
| H | the chain in Carver's own form (n lines) | framing only, §1.2 | Clifford 1870; Morley 1900; Carver 1920 §1; Longuet-Higgins 1972 | `NONE-FOUND` | L7b `EXISTS-FULL` maths | framing reference only; no claim |
| I | five-circles theorem (not stated in this draft) | — | classical; Paper D has it | ours (Paper D) | L8 `EXISTS-FULL` (own) | not used |
| J | Cox's chain (not claimed) | — | — | `NONE-FOUND` | L9 `NONE-FOUND` | not claimed |
| K | Miquel as base case, with four named formalisations | §1, §1.2 | classical | **present**: AFP `Miquel.thy` (2026-08-11), atlas-lean `MiquelTheorem.lean`, Rocq `HighSchoolGeometry`, lean-genius `MiquelPivotTheoremOQ01.lean` | §2 competitor sources | draft explicitly disclaims first formalisation of Miquel — correct |
| L | "in `docs/1000.yaml` with no `decl`" | §1 | — | Mathlib declares Clifford's circle theorems in the 1000 list without a declaration | L5 note | correct as stated |

No row is **MISMATCH**: every prior-art-bearing sentence of v0.7 is licensed by a scout row, and the
two sentences that must not become claims (Carver's classification; first formalisation of Miquel)
are explicitly disclaimed in §1.2.

## 2. What v0.5–v0.7 added, and whether it creates a new prior-art obligation

| added in | claim | prior-art obligation | verdict |
|---|---|---|---|
| v0.5 | late-block mutation run (891 rows, 16 survivors, survivor triage) | none — a verification record about our own tree | no obligation |
| v0.5 | second-machine receipt (john, same 16 survivors) | none | no obligation |
| v0.6 | late-block contradiction probes (0 CONTRADICTORY), 16 re-run rows | none | no obligation |
| v0.7 | two-machine satisfiability passes + curated witness table (0/107 closed) | none — a failed search is reported as a failed search (§5.2 says explicitly it is not a refutation) | no obligation |
| v0.4–v0.7 | layer-13 bridge layer: informative direction **proved in Lean for S6 and S7**, S1 open | none **provided** it is worded as a proof about the writer's blind statements, not as "first bridge between a formalisation and prose" | correct in §5.3: the bridge is described as closing two rows of *this* comparison, with S1 explicitly open |
| v0.7 | `namegate.py` counts (143 occurrences / 98 distinct) | none | no obligation |

One wording risk, not a claim: §5.3's "Both depend only on std, with no sorry in their cone" is a
statement about axiom dependencies, and is correct as phrased. It must not be compressed, in an
abstract or a talk, into "the chain is verified in both directions" — S1 is open and rows S2/S3, S4/S5
are stated limits (§5.3).

## 3. What the draft is therefore allowed to say (unchanged from the 2026-11-24 table)

1. first machine-checked **treatment of the chain for arbitrary n** — no `NONE-FOUND` row has a
   formal counterpart, and the at-infinity cases are carried by the carrier rather than excluded;
2. the first formalisation of the **uniform step** in the two-payload form (Statements 2–3) — the
   mathematics is Bobenko–Schief's, the formalisation is ours;
3. a reusable API — generalized circles on the sphere, second intersections, the Morley interpolation
   matrix, the level readouts, and the 19 layer-10 bridges to `Matrix.det`, `Collinear ℝ`,
   `Cospherical` and `crossProduct`.

Not allowed: any claim about Carver's classification, any first-formalisation claim for Miquel, any
claim that the chain is bridged to prose in all seven rows, any claim that the unresolved
satisfiability rows are refuted or are vacuous.

## 4. Residual gaps a referee must be told (from `SCOUT.md` §4, unchanged)

MathSciNet and zbMATH were not searched (no subscription/API key). Morley 1900, F. Morley 1929,
Wagner 1929, Kobayashi 1958 were seen only as metadata behind the JSTOR paywall (Carver 1920 read in
full from archive.org OCR). HAL timed out twice; Google Scholar is not reachable from this runtime;
the non-English query returned nothing; the Mizar MML body was not full-text searched; LeanGeo,
LeanPool, Principia, TLMC, ACL2, PVS, Nuprl and Naproche were not searched individually. These are
recorded as *not searched*, not as *empty*. The novelty claim is therefore "no formal statement of the
chain for arbitrary n was found in the sources logged in `SCOUT.md` §0 (26 rows)", not "none exists".

## 5. Layer verdict

**PASS with recorded limits.** The v0.7 text claims exactly what rows L5 and L6 permit, plus one
formalisation-result statement (the S6/S7 bridge) that makes no prior-art claim; every other
prior-art-bearing sentence is a labelled reuse or an explicit disclaimer. No sentence of v0.7 was
found to claim more than its row allows. The universe is unchanged since 2026-11-17, so this table
inherits the gaps of §4 and no more.
