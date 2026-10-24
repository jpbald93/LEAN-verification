# Prior-art sweep: Lean 4 formalization of (A) inscribed parabola of a complete quadrilateral, (B) Poncelet point of a complete quadrangle

Run date: 2026-10-19. Everything was done inline. Clones were shallow and deleted after grepping.
Per-term raw outputs are in this directory: `zulip_sweep.txt`, `ghsearch.txt`, `afp_entries.txt`, `pa_urls.txt`, `mathlib_master_tree.txt`.

## Bottom line

No complete formal proof of any of A1, A2, A3, A4 (the parabola, focus-directrix and Lambert parts) or B1, B2, B3, B4 was found in any source that could be searched.
Nothing partial was found either.
Only the controls and near-misses turned up (nine-point circle, Feuerbach, Simson, Miquel pivot, orthocentric systems).

Caveats on how far this "nothing" reaches:

- **GitHub code search** is rate-limited (10 queries/min), and many queries were run from inside a loop. Rate-limited queries returned `ERR`, and I re-ran those after a wait. Final coverage is listed in the table. GitHub code search also only indexes default branches of indexed repos, so it is not exhaustive.
- **Zulip** was searched through the web-public API. Private streams are not covered.
- **Newclid / AlphaGeometry** was only checked at the level of their example/problem lists, not exhaustively.
- **Not checked at all:** HOL Light's `Multivariate/` was covered by the full-repo grep. Isabelle AFP was searched by entry names plus GitHub code search, not by a local full-text grep of all 1045 entries.

## Table: theorem × source

Legend: NOTHING = searched, no hit for this theorem. Hits listed are near-misses or controls, not the theorem.

| Theorem | Mathlib pinned 0df444a3 (local grep) | Mathlib master (tree + code search + PRs) | Zulip (web-public) | AFP / Isabelle | Mizar MML (1500 .miz, full) | HOL4 (full clone) | HOL Light (full clone) | ProofAtlas | GitHub code search | Metamath set.mm | GeoCoq | lean-genius | compfiles / formal-conjectures / FormalBook | AlphaGeometry / Newclid |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A1 Steiner / reflections of Miquel point | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (see own-repo note) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| A2 inscribed parabola, focus = Miquel pt, directrix = orthocentre line | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| A3 axis ∥ Newton–Gauss line | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | FOUND-PARTIAL, own repo only: `jpbald93/quadnewton` has orthocentre line ⟂ Newton–Gauss (Paper E), no parabola/axis | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| A4 parabola / focus-directrix / Lambert / focus on circumcircle | NOTHING (no `parabola`, `directrix`, conic section files; `Lambert` hit is number theory) | NOTHING (no new file in tree; PRs for "parabola" are unrelated) | NOTHING (parabola hits are exercises/analysis, no geometry formalization) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (`directrix` hits: dafny→Lean/Coq benchmark specs for `ParabolaDirectrix`, which is a numeric function, not geometry) | NOTHING (`Lambert` = Lambert W) | NOTHING | NOTHING (`parabola` hits are analytic lemmas, e.g. Erdős problems) | NOTHING (FormalBook Ch20 `parabola` is a comment about degree-2 polynomials) | NOTHING |
| B1 nine-point circles of 4 triangles concur (Poncelet point) | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| B2 Poncelet point on 4 pedal circles | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING (`pedal` hits are Erdős–Mordell, Simson) | NOTHING | NOTHING |
| B3 Poncelet point on circumcircle of diagonal triangle | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| B4 orthocentric system shares one nine-point circle | NOTHING (`OrthocentricSystem` def + lemmas exist, but nothing about nine-point circle; `NinePointCircle.lean` never mentions it) | NOTHING in `NinePointCircle.lean` on master | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING | NOTHING |
| B5 Feuerbach (near-miss control) | NOTHING (only the nine-point-circle definition) | FOUND-PARTIAL: Mathlib PR #44236 "prove Feuerbach's theorem" is OPEN (opened 2026-09-26, +682 lines, new `Mathlib/Geometry/Euclidean/Feuerbach.lean`), not merged. Upstreamed from github.com/wwylele/Feuerbach | PR-review thread "Towards Feuerbach's Theorem" (Weiyi Wang) | FOUND-COMPLETE: AFP `Feuerbach` (2026-05-08) | NOTHING | NOTHING | FOUND-COMPLETE: `100/feuerbach.ml` | NOTHING | n/a | FOUND-COMPLETE: Wiedijk #29 listed in `mm_100.html` (listed as formalized; theorem name not looked up) | NOTHING | FOUND-PARTIAL / axiomatized: `FeuerbachsTheoremOQ01.lean` etc. (lean-genius issue #243 "Wiedijk #29") | NOTHING | NOTHING |
| C1 nine-point circle (control) | FOUND-COMPLETE: `Affine.Simplex.ninePointCircle`, `altitudeFoot_mem_ninePointCircle`, `eulerPoint_mem_ninePointCircle`, `dist_ninePointCircle_center_sq` (`Mathlib/Geometry/Euclidean/NinePointCircle.lean`, copyright 2026) | same, plus PRs #34420, #44218 merged | | FOUND-COMPLETE: AFP Feuerbach `nine_point_circle_1`/`_2` | NOTHING | NOTHING | FOUND-COMPLETE: `100/feuerbach.ml` `NINE_POINT_CIRCLE_1`/`_2` | | | | | FOUND (lean-genius `FeuerbachsTheorem*`) | | |
| C2 triangle Simson line (control) | NOTHING | NOTHING | NOTHING (only name collisions) | FOUND-COMPLETE: AFP `Simson` (Arthur Freitas Ramos, 2026) | NOTHING | NOTHING | FOUND-PARTIAL: `Complex/grobner_examples.ml` has `SIMSON` (algebraic Gröbner proof of Chou's example 288) | NOTHING | FOUND (AFP `Simson.thy`) | NOTHING | NOTHING | FOUND: `proofs/Proofs/SimsonLineTheorem.lean` (see note) | NOTHING | NOTHING |

### What each control found

Controls are expected to hit; the ones that did prove the searches work. The Mathlib Simson hit is missing because Mathlib has no Simson line (confirmed by grep and by master tree).

- **Nine-point circle in Mathlib** (pinned and master):
  - `Affine.Simplex.ninePointCircle` is the 3(n+1)-point sphere of a simplex. Its centre is on the Euler line with `OG : GN = n : 1`, and its radius is `circumradius / n`.
  - It is shown to pass through the face-opposite centroids, the Euler points, and (for triangles) the altitude feet.
  - It is the circumsphere of the medial simplex.
  - `dist_ninePointCircle_center_sq` gives `‖AN‖² = (R² + b² + c² − a²)/4`.
  - There is no `sorry` in the file.
  - Nothing about concurrency over four triangles of a quadrangle.
- **`Affine.OrthocentricSystem`** (`MongePoint.lean:557`): a predicate on 4-point sets. The lemmas are `exists_of_range_subset_orthocentricSystem`, `OrthocentricSystem.affineIndependent`, `affineSpan_of_orthocentricSystem`, `exists_circumradius_eq` (all four triangles have equal circumradius), and `eq_insert_orthocenter`. It does not prove that the four nine-point circles coincide. That is B4 and it is not stated.
- **Mathlib Feuerbach**: in `docs/100.yaml` Feuerbach (#29) has no `decl`, so it is not in Mathlib as of master. A PR (#44236) is open. See table.
- **Mathlib `docs/1000.yaml`**: Poncelet's closure theorem, Poncelet–Steiner, Miquel's theorem, Feuerbach's theorem, and Steiner–Lehmus appear as entries without a `decl`, so none are in Mathlib.

## Hits that are name collisions or near-misses

- **Triangle Steiner line (A1 near-miss).** Not found as a standalone theorem in any source. `Steiner` hits in Zulip/formal-conjectures are Steiner systems and similar (no relation).
- **AFP `Miquel`** (https://github.com/isabelle-prover/mirror-afp-devel/tree/master/thys/Miquel): Miquel's pivot theorem for a triangle with a point on each side. Complex-number proof via cross-ratios. COMPLETE. Author Arthur Freitas Ramos, 2026. This is the triangle version, not the Miquel point of four lines, and it says nothing about the orthocentre line or Steiner line.
- **AFP `Simson`** (same author, 2026): Wallace–Simson line and converse. COMPLETE. Triangle Simson line, not A1.
- **lean-genius** (`rjwalters/lean-genius`):
  - `proofs/Proofs/MiquelPivotTheoremOQ01.lean`: conditional form of Miquel pivot via cross-ratio (114 lines, 1 `sorry` hit by grep, which may be in a comment). Merged in PR #25056. Its `problem.md` mentions complete quadrilaterals, but I found no statement of A1–A3 there.
  - `proofs/Proofs/SimsonLineTheorem.lean` (364 lines, 1 `sorry` hit by grep, not inspected further).
  - `proofs/Proofs/FeuerbachsTheoremOQ01.lean` etc.: incremental, with axioms in the base file.
  - No lean-genius PR or issue matched `parabola` for geometry, `Gauss`, or `Poncelet point`. The `parabola` PRs are about Erdős problems (parabola used as a point-set construction).
- **Rocq archive** `rocq-archive/projective-geometry` `Plane/P09_complete_quadrilateral.v` (Coq): a projective collinearity lemma for a hexamy configuration. It is the projective "complete quadrilateral" harmonic-type statement, unrelated to A1–A3.
- **Mizar**: `euclid13.miz` (altitude, orthocenter of a triangle, Coghetto) has `the_orthocenter`; `projdes1.miz`, `projpl_1.miz` define projective "quadrangle". No Simson, Miquel, nine-point or Feuerbach in MML.
- **HOL Light** `100/feuerbach.ml`: Feuerbach plus nine-point circle, complete (214 lines). This is the source of the AFP translation (https://www.isa-afp.org/entries/Feuerbach.html, which says it was AI-assisted).
- **Metamath**: `mm_100.html` lists #29 Feuerbach under formalized theorems. Searched `set.mm` for the other terms and found nothing.
- **GeoCoq**: `Lambert` hits are Lambert quadrilaterals (hyperbolic geometry), a name collision.
- **jjdishere/EG** `Plan_files/Plan.lean`: a to-do plan listing `SimsonLine -- Define the Simson line`. Not a proof.
- **Own prior work** (not prior art by third parties): `jpbald93/quadnewton` (created 2026-10-16; README: 35 declarations, no `sorry`): Newton–Gauss, Bodenmiller, the Miquel point, the Steiner circle, the Simson line, `orthocentre_line_perp` (orthocentre line ⟂ Newton–Gauss line). No parabola, directrix, or reflections-of-Miquel-point theorem found in it by grep. Also `jpbald93/poncelet-triangles` (Poncelet's porism for triangles). Excluded from the verdicts below since it is the user's own work and predates nothing relevant.
- **Zulip**: the thread "Six circle theorem" (2024-06-05) asked whether Miquel's six-circle theorem is in Mathlib; the single reply says higher-dimensional generalisations exist but gave no code. "Remaining 100 theorems" has the Feuerbach discussion (Joseph Myers, Weiyi Wang). No Zulip message mentions Poncelet point, Euler–Poncelet, Newton–Gauss, Bodenmiller, orthocentric system, pedal circle, rectangular hyperbola, complete quadrangle or directrix in a geometry context.
- **Newclid / AlphaGeometry** example lists: contain `orthocenter`, `euler` and similar basic benchmarks. Nothing for these theorems (checked example files only). These are machine proofs in a DSL, not kernel-checked in a proof assistant.
- **Synthetic / Wu-method provers (source h):** no specific hits found for these theorems, and I did not search the literature for Chou-style machine proofs (e.g. Chou's 1988 book collection) beyond the HOL Light `grobner_examples.ml` Simson example. This part is not exhaustively covered.

## Verdict per theorem

- **A1** (reflections of the Miquel point collinear on the orthocentre line): no complete formal proof found in any searched source.
- **A2** (inscribed parabola, focus = Miquel point, directrix = orthocentre line, Miquel point off the orthocentre line): no complete formal proof found in any searched source.
- **A3** (parabola axis ∥ Newton–Gauss line): no complete formal proof found in any searched source. Only the user's own `quadnewton` has orthocentre line ⟂ Newton–Gauss line.
- **A4** (parabola with tangents / focus–directrix / Lambert's theorem / focus on circumcircle): no complete formal proof found in any searched source. Mathlib has no parabola or conic-section geometry at all.
- **B1** (nine-point circles of the four triangles concur): no complete formal proof found in any searched source.
- **B2** (Poncelet point on the four pedal circles): no complete formal proof found in any searched source.
- **B3** (Poncelet point on the circumcircle of the diagonal triangle): no complete formal proof found in any searched source.
- **B4** (orthocentric system, four triangles share one nine-point circle): no complete formal proof found in any searched source. Mathlib has the `OrthocentricSystem` predicate and equal-circumradius lemma but not this.
- **B5** (Feuerbach, controls):
  - PRIOR ART (complete): https://github.com/jrh13/hol-light/blob/master/100/feuerbach.ml
  - PRIOR ART (complete): https://www.isa-afp.org/entries/Feuerbach.html
  - Mathlib: open PR https://github.com/leanprover-community/mathlib4/pull/44236, not merged as of this run.
  - Nine-point circle itself: PRIOR ART in Mathlib (`Mathlib/Geometry/Euclidean/NinePointCircle.lean`), HOL Light, AFP.
- **C** (controls): nine-point circle FOUND (Mathlib, HOL Light, AFP); triangle Simson line FOUND (AFP `Simson`; lean-genius). Both controls hit, so the search method works.

## Sources that were not fully reachable or covered, with exact reasons

| Source | Status |
|---|---|
| Lean Zulip live search UI | The unauthenticated `/json/messages` API with `channels:web-public` worked (that is what was searched). Private streams are not covered. The `leanprover-community.github.io/archive/` site has no search function. |
| AFP full-text | Only AFP's own search via GitHub code search (`repo:isabelle-prover/mirror-afp-devel`) and entry-name listing; no local full-text grep of all 1045 entries (disk is 95% full). |
| GitHub code search (Lean/Coq/Isabelle) | Rate-limited to 10 requests/min; first pass returned `ERR` for many queries. All terms in the brief were re-run, but a few terms (e.g. `CompleteQuadrilateral` in Lean/Coq) returned 0 results rather than exhaustive evidence, since the search index only covers default branches of indexed repos. |
| ProofAtlas | Its `/api/...` routes return 404 (`/api/search`, `/api/theorems`), and `/search/` is a client-side page. Searched via `sitemap.xml` instead (752 URLs, no relevant titles). The search page itself was not queried, so full-text content is not covered. A `site:proofatlas.ai` Google search was not possible with the available tools. |
| Mizar MML | Fully reachable: all 1500 `.miz` articles were downloaded and grepped. Deleted afterwards. |
| HOL4, HOL Light, set.mm, GeoCoq, FormalBook, compfiles, formal-conjectures, lean-genius | Cloned and grepped (lean-genius was cloned and grepped by name, then selected files fetched individually). All deleted. |
| Chou / Wu-method outputs, GeoGebra/Coq exports (source h) | Not searched beyond the examples above; this is not covered. |
| Mathlib 1000+ list on master | Checked `docs/1000.yaml` (current master): no `decl` for Poncelet, Miquel, Feuerbach. |

---
## CORRECTION (2026-10-20, recorded 2026-10-21) — supersedes the A1 "NOTHING" entry and the "triangle Steiner line not found" note above

An independent reviewer (layer 12, round 1) found a directly relevant entry this sweep missed:

- **AFP `Steiner_Line_Theorem`** — A. Freitas Ramos, D. Barros Hulak, R. J. G. B. de Queiroz, *Steiner's Line Theorem in Isabelle/HOL*, Archive of Formal Proofs, 6 October 2026. https://isa-afp.org/entries/Steiner_Line_Theorem.html (verified to exist 2026-10-20).
  Proves, for a nondegenerate triangle and a point on its circumcircle, that the reflections of the point in the three sidelines are collinear on a line through the orthocentre.
- **Verdict for A1: FOUND-PARTIAL / ingredient.** It is the triangle statement, not the four-line statement of Paper F (all four reflections of the Miquel point and all four orthocentres on one line, including H3 = H4). The paper cites it and scopes its claim accordingly.
- Consequence: the controls above did not show the AFP coverage was complete; recent AFP entries were missed. The paper lists this as a coverage gap.
