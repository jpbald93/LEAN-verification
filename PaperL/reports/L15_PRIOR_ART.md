# Layer 15 — prior-art verdict table for the Paper L draft

Compiled 2026-11-24 from `SCOUT.md` (§0 search log, §1 verdict table rows L1–L9, §2 competitor sources,
§3 published mathematics, §4 search gaps, §5 what may and may not be claimed). No new search was run
for this layer; every verdict below is the scout's, re-expressed claim by claim against the draft so
that no sentence of `DRAFT.md` claims more than a verdict row permits.

**Instrument:** the scout's own 26-row search log (`SCOUT.md` §0), run 2026-11-16/17 against the
Mathlib tree at pin `0df444a3`, GitHub code search (Lean and all languages), the Isabelle AFP,
atlas-lean, lean-genius, Rocq GeoCoq/HighSchoolGeometry, HOL Light, HOL4, Metamath `set.mm`, the Mizar
MML listing, the formal-conjectures/compfiles/ICML-26 collections, ProofAtlas, the 1000+ theorem list,
arXiv, OpenAlex, Crossref, Semantic Scholar, HAL, Zenodo, StackExchange (math/MO), the non-English web,
and a numeric check of the statement.

## 1. Claim-by-claim verdicts

| id | claim as it appears in the draft | prior art (mathematics) | formalisation | scout row | verdict for the draft |
|---|---|---|---|---|---|
| A | level 3: three circles through M give three second intersections on a generalized circle (§2.2, Statement 7) | classical; in Mathlib it is the `Concyclic`/`Circumcenter` API plus non-collinearity, not stated as a chain base | present as API, not as a named theorem | L1 `NONE-FOUND` as a named statement | **not a novelty claim**; state as base case |
| B | level 4 = Clifford's first theorem (§1.2, base cases) | Clifford 1871/1882; Coxeter 1969 p. 262 | **ours**, Paper D (Zenodo 23653309) | L2 `EXISTS-FULL` (own work) | reuse only, labelled |
| C | level 5 (§1.2, base cases) | classical; Paper D | **ours**, Paper D | L3 `EXISTS-FULL` (own) | reuse only, labelled |
| D | level 6 (§1.2, base cases) | classical; Paper D also records the finite-plane failure | **ours**, Paper D | L4 `EXISTS-FULL` (own) | reuse only, labelled |
| E | **the chain for all n on the Riemann sphere** (§1, Statement 1) | **classical**: Clifford (1871/1882), Morley (1900), Carver (1920), Longuet-Higgins (1972); cross-ratio route in Bobenko–Schief (arXiv:1509.04109) | **NONE-FOUND** in any assistant at any n > 6 | L5 `NONE-FOUND` | the paper's first novelty claim — *formalisation* only |
| F | **uniform step / two-side payload** (§1.1, Statements 2–3) | the Miquel + cross-ratio/hypercube extension argument (Bobenko–Schief 2016; Martini–Spirova 2008 for Minkowski/Cayley–Klein planes) | `NONE-FOUND` | L6 `NONE-FOUND` | second novelty claim — *formalisation* only |
| G | improper-set / at-infinity classification (§1.2, §5.6) | **Carver 1920 §6, Theorem 13** (read in full from the archive.org OCR); Kantor 1878 (deltoid), Morley 1900 ("Clifford line") | `NONE-FOUND`; **and not formalised in this paper** | L7 `EXISTS-FULL` maths / `NONE-FOUND` formalisation | **carried by Carver, never ours**, and OPEN here |
| H | the chain in Carver's own form (n lines) (§1, §2.2) | Clifford 1870; Morley 1900; Carver 1920 §1; Longuet-Higgins 1972 | `NONE-FOUND` | L7b `EXISTS-FULL` mathematics | framing reference only |
| I | five-circles theorem as a corollary (not stated in this draft) | classical; Paper D has it | **ours** (Paper D); no AFP/Coq entry | L8 `EXISTS-FULL` (own) | not used |
| J | Cox's chain (not claimed) | — | `NONE-FOUND` | L9 `NONE-FOUND` | not claimed |
| K | Miquel's theorem (base case, not claimed) | classical | **present**: AFP `Miquel.thy` (2026-08-11, pivot form), atlas-lean `MathlibExt/…/MiquelTheorem.lean` (complete-quadrilateral form), Rocq `HighSchoolGeometry:270`, lean-genius `MiquelPivotTheoremOQ01.lean` | §2 competitor sources | we must **not** claim first formalisation of Miquel |

## 2. What the draft is therefore allowed to say

*Claimed (and claimed only this way in the draft):*
1. first machine-checked **treatment of the chain for arbitrary n** — i.e. no `NONE-FOUND` row has a
   formal counterpart, and the at-infinity cases are carried by the carrier rather than excluded;
2. the first formalisation of the **uniform step** in the form of the two payloads (Statements 2–3) —
   the mathematics is Bobenko–Schief's cross-ratio/hypercube argument, the formalisation is ours;
3. a reusable API — generalized circles on `OnePoint ℂ`, second intersections, the Morley
   interpolation matrix, the level readouts, and the 19 layer-10 bridges to `Matrix.det`,
   `Collinear ℝ`, `Cospherical` and `crossProduct`.

*Not claimable, and not claimed:*
- the all-n theorem, the failure phenomena, the Möbius-plane repair, the analytic method, or the
  higher-polytope picture as **mathematics** — all classical (E, F, G, H);
- the improper-set classification as formalised here — it is not (G, and §5.6 of the draft);
- first formalisation of Miquel (K);
- that the finite-plane predicate failure is a counterexample to the chain — Paper D says it is not,
  and Carver explains why (D).

## 3. Limits of this layer

The verdict table is only as strong as the search behind it, and `SCOUT.md` §4 records the gaps:

- **MathSciNet and zbMATH were not searched** — the two indexes most likely to hold a 20th-century
  paper we would otherwise miss. The Carver find (row 17 of the log) shows the risk is real.
- **JSTOR paywall**: Morley 1900, F. Morley 1929, Wagner 1929, Kobayashi 1958 were seen as metadata
  only; Carver 1920 is the only one read in full. Their exact claims are unverified.
- **HAL timed out** twice, **Google Scholar** is unreachable from this runtime, the **non-English web**
  query returned nothing (German "Cliffordsche Kette", French "chaîne de Clifford"). Recorded as *not
  searched*, not as *empty*.
- **Mizar**: no article is named after the theorem in the 3,050-file MML listing, but the MML body was
  not full-text searched.
- LeanGeo, LeanPool, Principia, TLMC, ACL2, PVS, Nuprl and Naproche were not searched individually.
- Mathlib content searches ran on the default branch, not at the pin (the pin's file tree was read in
  full, 10,301 paths).

## 4. Layer verdict

**PASS with recorded limits.** No claim in `DRAFT.md` is contradicted by prior art; every novelty
statement in it is a formalisation claim matching a `NONE-FOUND` scout row (L5, L6), every classical
result it uses is attributed (Clifford, Morley, Carver, Longuet-Higgins, Bobenko–Schief), the
at-infinity classification is credited to Carver and marked unformalised, and the paper explicitly
declines the two claims the scout forbids (new mathematics; first formalisation of Miquel). The
residual risk is the unscanned indexes in §3, and it is carried in the draft's own §5.7.
