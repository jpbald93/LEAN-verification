# Paper L — novelty scout

- **Swept:** 2026-11-16 22:24–22:40 EST (UTC 2026-11-17 03:24–03:40). Machine log: `AFM/PaperL/scout_log.txt`.
- **Timing disclosure:** first pass 2026-11-17 03:24–03:40Z, **BEFORE** the round-1 dispatch (03:31Z). §0 rows
  17–26 and the L7/L7b verdicts were added at ~03:58Z, **after** that dispatch and **before** any paper framing,
  when Josh asked whether non-code sources had been searched. No verdict in this file was written after a proof.
  (Paper D's n=4,5,6 material is our own earlier work and is marked as such.)
- **Claim under test:** Clifford's chain of circle theorems for **all n**, stated in the inversive (Möbius) plane,
  where the level object alternates point / circle and "circle" includes lines (circles through ∞).
- **Classes:** (a) complete formal proof, no `sorry`/`Admitted`/axiom/assumed-theorem hypothesis — only (a) defeats
  novelty; (b) statement with `sorry`/`Admitted` or the theorem taken as a hypothesis; (c) benchmark entry.
- **Tools:** `gh api`/`gh search code` (GitHub code search, Lean and unfiltered), Mathlib tree at pin
  `0df444a3`, Mathlib `docs/1000.yaml`, Isabelle AFP mirror, Rocq HighSchoolGeometry source, HOL Light/HOL4 trees,
  ProofAtlas sitemap, arXiv API, general web search, and a local numeric check of the statement.

## 0. Log (order run)

| # | source | command / URL | result |
|---|---|---|---|
| 1 | Mathlib tree at pin | `gh api repos/leanprover-community/mathlib4/git/trees/0df444a3…?recursive=1` (10,301 paths) | `Geometry/Euclidean/{Inversion,Sphere/{Basic,Power,Ptolemy,SecondInter,Tangent},NinePointCircle,Circumcenter,Incenter}.lean`; **no** Miquel/Clifford file |
| 2 | Mathlib content | `gh search code "Concyclic"/"Cospherical"/"Miquel"/"Clifford circle" --repo leanprover-community/mathlib4` | `Concyclic`/`Cospherical` API and results exist; `Miquel` only in `docs/1000.yaml` (no decl); `Clifford circle` → nothing |
| 3 | Mathlib targets | `docs/1000.yaml` (fetched 2026-11-17) | `Clifford's circle theorems`, `Miquel's theorem`, `Five circles theorem`, `Six circles theorem`, `Mohr–Mascheroni`, `Poncelet–Steiner` listed **without `decl`** |
| 4 | GitHub, Lean | `gh search code "clifford circle theorem"/"clifford chain"/"miquel"/"five_circles"/"six_circles"/"Cox chain"/"Moebius plane" --language Lean` | only unrelated hits (Clifford algebra, QFT circuits, bibliography); **one miss** — atlas-lean's Miquel file was found only by repo-scoped search (#7) |
| 5 | GitHub, all languages | `gh search code "Clifford chain"/"Miquel theorem"` | quantum-computing "Clifford chain", Wikipedia mirrors, AoPS text dumps; no formal proof |
| 6 | Isabelle AFP | `gh search code "Clifford"/"Miquel" --repo isabelle-prover/mirror-afp-devel`; `isa-afp.org/entries/Miquel.html` | `thys/Miquel/Miquel.thy`, entry 2026-08-11 (Ramos–Hulak–Queiroz): **pivot form only** (circumcircles of AQR, BRP, CPQ concur). No Clifford entry |
| 7 | atlas-lean | `gh search code "Miquel"/"clifford" --repo facebookresearch/atlas-lean`; read `MathlibExt/Geometry/Euclidean/MiquelTheorem.lean` (611 lines) | `miquel_theorem` (six-point / complete-quadrilateral Miquel), MathlibExt only; no Clifford |
| 8 | lean-genius | `gh search code "miquel" --repo rjwalters/lean-genius` | `proofs/Proofs/MiquelPivotTheoremOQ01.lean` (pivot form) |
| 9 | Rocq | `gh search code "Miquel"/"Clifford" --repo GeoCoq/GeoCoq` (empty); read `rocq-community/HighSchoolGeometry/theories/applications_cocyclicite.v:270` | `Theorem Miquel` — complete-quadrilateral incidence form. No Clifford |
| 10 | HOL Light / HOL4 | `gh search code "miquel clifford" --repo jrh13/hol-light`; `"Miquel" --repo HOL-Theorem-Prover/HOL` | nothing |
| 11 | Benchmarks / collections | repo-scoped `gh search code` on `google-deepmind/formal-conjectures`, `dwrensha/compfiles`, `epfl-lara/icml-26-lean-challenges` | nothing for Miquel/Clifford |
| 12 | ProofAtlas (mandatory) | `proofatlas.ai/sitemap.xml` (751 URLs) grepped for `clifford|miquel|circle` | no Clifford/Miquel entry; only unrelated "no-retraction disk circle" |
| 13 | 1000+ list | `_thm/Q5132839.md` (Clifford), `Q2449984.md` (Miquel), `Q5456213.md` (five circles) | entries exist, no formalisation recorded |
| 14 | arXiv API | `all:"Clifford chain"`, `all:"Clifford's circle theorems"`, `abs:Miquel AND abs:formalization` | only quantum-circuit noise; no recent mathematics paper on the chain |
| 15 | general web | "Clifford's chain circles theorem general n proof Miquel induction" | key mathematics: Longuet-Higgins 1972, Martini–Spirova 2008, Bobenko–Schief 2016 (see §3) |
| 16 | numeric sanity check | `/tmp/chain/check.py` (python + numpy, 2026-11-17) | chain recursion for n=4…8, 3 random trials each: every level incidence closes, worst residual 2e-15 … 3e-9 |

| 17 | OpenAlex + Crossref | `api.openalex.org/works?search="Clifford chain"`; `api.crossref.org/works/10.2307/2370427` | **hit: W. B. Carver, "The Failure of the Clifford Chain", Amer. J. Math. 42(3) (1920) 137–167** (+ errata 1920); also Morley 1929, Wagner 1929, Kobayashi 1958, Longuet-Higgins 1972/73, Martini–Spirova 2008, Jurkin–Kovačević 2010, Rinchiusa 2025 |
| 18 | archive.org full text | `sim_american-journal-of-mathematics_1920-07_42_3_djvu.txt` (140 KB OCR) | **Carver's paper read in full**: states proper/improper sets, gives Kantor's deltoid failure, Morley's "Clifford line" condition, and in §6 classifies every improper set in the **inversion/Möbius plane** ("the plane has only one point at infinity … circle includes straight lines and point-circles"), with a necessary-and-sufficient "key matrix" criterion (Theorem 13) |
| 19 | Semantic Scholar | `api.semanticscholar.org/…/DOI:10.2307/2370427` | metadata only; JSTOR full text closed |
| 20 | HAL | `api.archives-ouvertes.fr/search?q="Clifford chain"` | timed out twice (recorded as not searched) |
| 21 | Zenodo | `zenodo.org/api/records?q="Clifford chain"` | 0 records |
| 22 | StackExchange (math, mathoverflow) | `api.stackexchange.com/…q=Clifford chain` | nothing on formalisation; one MO question "N-th closed chain of six circles" (different theorem) |
| 23 | Metamath `set.mm` | `raw.githubusercontent.com/metamath/set.mm/develop/set.mm` (52 MB) | `clifford` → 1 hit, a bibliography comment; `miquel` → 0 |
| 24 | Mizar MML | `mizar.uwb.edu.pl/version/current/mml/` listing (3,050 `.miz`) | no article named Miquel/Clifford; MML body not machine-searched |
| 25 | Isabelle distribution, Agda, Coq-wide | repo/lang-scoped `gh search code` (`mirror-isabelle`, `--language Agda`, `--language Coq`) | nothing (AFP `Miquel` is the only Isabelle item; Coq hits are Clifford algebra) |
| 26 | non-English web | German "Cliffordschen Kette", French "chaîne de Clifford" | search provider returned no results (recorded as a gap, not as evidence) |

## 1. Verdicts — one row per claim we intend to make

| # | claim | verdict | evidence |
|---|---|---|---|
| L1 | **C₃ (base):** three circles through a common point M; the three second intersections are concyclic (the circumcircle is the level-3 object) | `NONE-FOUND` as a named statement; **not a novelty claim** — in Mathlib this is the `Concyclic`/`circumsphere` API plus non-collinearity | Mathlib `Sphere/Basic.lean`, `Circumcenter.lean`; no one states it as the chain's base |
| L2 | **C₄ = Clifford's first theorem:** four circles through M ⟹ the four level-3 circles are concurrent | `EXISTS-FULL` for **our own** Paper D (`clifford` repo, `cliff3_*`/`cliff4_*`); `NONE-FOUND` third-party in this form (atlas/AFP/Coq are the pivot or complete-quadrilateral form) | Paper D `paperd.tex` §Contributions; `MathlibExt/…/MiquelTheorem.lean`; AFP `Miquel.thy` |
| L3 | **C₅:** five circles ⟹ the five level-4 points are concyclic | `EXISTS-FULL` (our Paper D, n=5) | Paper D |
| L4 | **C₆:** six circles ⟹ the six level-5 circles are concurrent | `EXISTS-FULL` (our Paper D, n=6) + D's finding that the *finite-plane predicate* admits a point at infinity at n≥6 | Paper D §chainfail |
| L5 | **Cₙ for all n, in the Möbius plane** (level object alternates point/circle; lines are circles through ∞) | **`NONE-FOUND`** | items 1–13: no statement in any assistant at any n > 6; no library has the chain |
| L6 | **Uniform propagation lemma** Cₙ ⟹ Cₙ₊₁ (the "hypercube extension" step) | **`NONE-FOUND`** (no formal version; the mathematics is the combinatorial/Miquel argument of §3) | items 4–13 |
| L7 | **At-infinity / improper-set classification:** the level-n object is a line (odd n) or ∞ (even n) exactly when a specific minor of the characteristic matrix vanishes | **`EXISTS-FULL` in the mathematics** — Carver 1920 §6 classifies every improper set in the inversion plane and proves a necessary-and-sufficient "key matrix" condition (Thm 13); **`NONE-FOUND` as a formalisation** | Carver 1920 (read in full, archive.org OCR); Kantor 1878 deltoid case; Morley 1900 "Clifford line" |
| L7b | **The chain in Carver's own form** (n lines; odd n a circle, even n a point; proper sets only) | **`EXISTS-FULL` in the mathematics** (Clifford 1870; Morley 1900; Carver 1920; Longuet-Higgins 1972) — this is the form the paper should state, with the inverted circles-through-a-point form as a corollary | Carver 1920 §1; Morley 1900 |
| L8 | **Five circles theorem** restated as a chain corollary | `EXISTS-FULL` (our Paper D `fivecircles`; Isabelle/Coq have no five-circles entry) | Paper D; AFP index |
| L9 | Cox's chain (optional corollary) | `NONE-FOUND` | item 4 (`"Cox chain"` Lean → nothing) |

**Gate result: PASS.** No intended claim is `not checked`; the only `EXISTS-FULL` rows are our own published Paper D
work (L2–L4, L8) and must be labelled as restatement/reuse, never as new. The paper's new claims are L5, L6, L7.

## 2. Competitor sources read in detail

- **Isabelle AFP `thys/Miquel/Miquel.thy`** (entry 2026-08-11, Ramos–Hulak–Queiroz, ~1 file): Miquel's *pivot*
  theorem — triangle ABC, points P∈BC, Q∈CA, R∈AB, circumcircles of AQR, BRP, CPQ concur at M. Complex
  coordinates; a cross-ratio product lemma (`miquel_complex_cross_ratio_product`) is in the file. **No chain, no
  n>3 statement**, and not the "circles through a common point" form.
- **`facebookresearch/atlas-lean MathlibExt/Geometry/Euclidean/MiquelTheorem.lean`** (611 lines, read): proves
  `miquel_theorem` for six points (complete-quadrilateral / Miquel form) using `Sphere.SecondInter` and angle
  lemmas. Read, not compiled here. **Base case only; no Clifford, no general n.** Note: it lives in `MathlibExt`,
  not in Mathlib, and a global `gh search code --language Lean "miquel"` did **not** return it — repo-scoped search
  did. That is a search failure mode recorded in §4.
- **`rjwalters/lean-genius proofs/Proofs/MiquelPivotTheoremOQ01.lean`**: pivot form, same class as AFP.
- **Paper D (ours)**: `clifford` 3 files / 1,271 lines for n=4,5,6 in an explicit complex model, plus
  `cliffordchain` (7 files / 1,679 lines) defining an existential chain predicate at every n, proving n=4,5 and
  exhibiting a six-circle configuration whose Clifford point is at infinity. Its own text: "We do not prove
  Clifford's chain for general n … the all-n chain in that form remains open here."

## 3. The published mathematics (not formalisation)

Read in full (OCR of the issue, archive.org):

- **W. B. Carver, "The Failure of the Clifford Chain", *Amer. J. Math.* 42(3) (1920) 137–167** (+ errata, *ibid.*
  42:?). States the chain for **n lines**: for odd n the n Clifford points lie on a circle, for even n > 2 the n
  Clifford circles pass through a point. Cites Kantor (1878): five lines touching a deltoid have their five
  Clifford points **collinear**; six lines touching a deltoid have the six "Clifford lines" **not concurrent** but
  tangent to a new deltoid. Cites **Morley (1900)**, who gives the analytic proof and shows that an odd number
  > 3 of lines whose characteristic constants satisfy an analytic condition determine a **Clifford line** rather
  than a circle. Carver's own contribution: *all* possibilities of failure ("improper sets"), the analytic
  conditions, and §6 in the **inversion plane** — "we assume that the plane has only one point at infinity, and
  understand the word circle to include straight lines and point-circles" — where each improper set is shown to be
  the limit of proper ones and the level figure is defined as that limit, with a necessary-and-sufficient
  **key-matrix** criterion (his Theorem 13). The machinery is Morley's circular coordinates and characteristic
  matrices (`a_k`, clinants `t_k`, solid determinants) — the same objects that appear as the "Morley-type formula"
  and the interpolation matrix in our own `GENERAL_REPORT.md`.

Metadata only (paywalled, not read): F. V. Morley, "Extensions of Clifford's Chain-Theorem", *Amer. J. Math.*
51 (1929), DOI 10.2307/2370734; P. S. Wagner, "An Extension to Clifford's Chain", *ibid.* 51 (1929), DOI
10.2307/2370735; K. Kobayashi, "An Analogue to Clifford's Chain" (1958); H. Lob, "Some chains of theorems derived
by successive projection" (1933); M. S. Longuet-Higgins, "Clifford's chain and its analogues in relation to the
higher polytopes", *Proc. R. Soc. London A* 330 (1972) 443–466, and "On a conjectured analogue to Clifford's chain
in [4]", *Math. Proc. Cambridge Philos. Soc.* (1973); H. Martini, M. Spirova, *Publ. Math. Debrecen* 72 (2008)
371–383 (strictly convex Minkowski planes) and *Period. Math. Hungar.* (2008) (affine Cayley–Klein planes);
E. Jurkin, N. Kovačević, "Clifford's chain of theorems in affine CK-planes" (2010); L. Labaciren, "Chain theorems of
lines, circles and planes" (2008); G. Rinchiusa, "The Clifford, Grace, and de Longchamps chains: historical
developments and inversive properties" (thesis, 2025 — cited by search snippet and by OpenAlex metadata; the PDF is
behind a Cloudflare challenge and could not be read).

Also: H. S. M. Coxeter, *Introduction to Geometry* (2nd ed. 1969) p. 262 (circles-through-a-point form);
A. I. Bobenko, W. K. Schief, "Circle complexes and the discrete CKP equation", arXiv:1509.04109 — "Clifford's
theorem … is a consequence of Miquel's theorem", by cross-ratio identities, with hypercube extension to Cₙ.

**Consequence for the paper:** the all-n theorem and the degenerate/at-infinity classification are *classical*
(Carver 1920 for the classification, Morley 1900 for the analytic method, Longuet-Higgins 1972 for the general
polytope picture). What is missing in every system is the formalisation, and in the literature a machine-checked
treatment of the characteristic matrices.

## 4. Gaps of this search

- **MathSciNet and zbMATH were not searched** (subscription/API key not available here); they are the two indexes
  most likely to hold a 20th-century paper we would otherwise miss, and the Carver find shows that risk is real.
- **JSTOR paywall:** Morley 1900 (Trans. AMS 1:97), F. Morley 1929, Wagner 1929, Kobayashi 1958 were seen only as
  metadata; their exact claims are unverified. Carver 1920 is the only one read in full.
- **HAL** API timed out twice; **Google Scholar** is not reachable from this runtime; the non-English web query
  returned no results. These are recorded as *not searched*, not as *empty*.
- Mizar: no article is *named* after the theorem in the 3,050-file MML listing, but the MML body was not
  full-text searched; Mizar stays *not verified*.
- Mathlib content searches ran on the **default branch**, not at the pin (the pin's file tree was read, 10,301
  paths). GitHub code search **missed** atlas-lean's Miquel file in a global query; every collection therefore got
  its own repo-scoped pass.
- LeanGeo, LeanPool, Principia, TLMC and ACL2/PVS/Nuprl/Naproche were not searched individually.
- The numeric check (`/tmp/chain/check.py`) verifies the statement, not any proof, and only on random
  non-degenerate configurations.

## 5. What the paper may claim — and may not

**May claim:** the first machine-checked proof of Clifford's chain for arbitrary n (in the Möbius plane, with the
line/∞ cases), and the first formalisation of the improper-set classification, including the characteristic-matrix
("key matrix") criterion; a reusable Lean API for second intersections, generalized circles on `OnePoint ℂ`,
inversion, and the circular-coordinate/characteristic-matrix method; a checked account of the deltoid examples.

**May not claim:** any of the mathematics as new — the all-n chain (Clifford 1870; Morley 1900; Carver 1920;
Longuet-Higgins 1972), the failure phenomena (Kantor 1878; Carver 1920), the Möbius-plane repair (Carver 1920 §6),
the analytic method (Morley 1900), or the higher-polytope picture (Longuet-Higgins 1972; Bobenko–Schief 2016).
Nor "first formalisation of Miquel" (atlas-lean, AFP 2026, Coq HSG, lean-genius). Nor that the finite-plane
predicate failure is a counterexample to the chain (Paper D already says it is not; Carver explains it).
