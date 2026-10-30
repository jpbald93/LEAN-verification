# SCOUT — prior-art search for Paper H ("Classical triangle inequalities in Lean 4")

- **Date of search:** 2026-10-28, about 17:00 UTC. Run inline with no subagents; about 1 h 15 min of the 2 h box used.
- **Tools:** `gh` (GitHub REST API, code search, PR search, repo search, raw file fetch), `curl` (AFP, Freek's list, Mizar MML, set.mm, arXiv API), and the WebSearch/WebFetch tools. These two tools **did not work** (see Gaps §5). Every GitHub file classified SAME or PARTIAL below was downloaded and read. The working copies are in `<work-dir>`.
- **Classification:** SAME means a complete formal proof (no `sorry` or custom axiom) of one of our statements, or of a trivially equivalent form. PARTIAL means related, weaker, an algebraic or side-length form, a different setting, or a statement with `sorry`/`axiom`. UNRELATED means a name clash or something different.
- **Caveat:** none of the external Lean files were compiled. "sorry-free" means `grep -w sorry` found nothing outside comments, plus no `axiom` or `admit`.

---

## 1. Headline

| Our result | Verdict |
|---|---|
| Euler's theorem OI² = R² − 2Rr | **CLOSED by prior art** (Lean 4, same Mathlib `Affine.Triangle` API) |
| Euler's inequality 2r ≤ R | **CLOSED by prior art** |
| Euler's inequality, equality ⇔ equilateral | **OPEN** (no formal proof found) |
| Euler for excircles OI_a² = R² + 2Rr_a | **CLOSED by prior art** |
| Weitzenböck (+ equality) | **PARTIAL prior art** (algebraic Heron-form only) |
| Hadwiger–Finsler (+ equality) | **PARTIAL prior art** (algebraic Heron-form only) |
| Gerretsen (both sides) | **OPEN** |
| Kooi (+ Kooi ≤ Gerretsen) | **OPEN** |
| OG² formula | **OPEN** (Mathlib has a related vertex–Euler-line formula) |
| OH² formula | **OPEN** |
| IG² formula | **OPEN** |
| Neuberg–Pedoe (+ equality ⇔ similar) | **OPEN** |
| Ptolemy's inequality | **CLOSED by prior art** (in Mathlib since 2022, identical statement) |
| Leibniz relation / centroid minimises Σ\|XPᵢ\|² (+ equality) | **OPEN** |
| Triangle isoperimetric 12√3Δ ≤ p² (+ equality) | **OPEN** |
| Erdős–Mordell inequality | **CLOSED by prior art** (two independent sorry-free Lean 4 proofs, plane only, interior P); ours is more general (see §4) |
| Erdős–Mordell key lemma | **CLOSED by prior art** (lean-genius `key_inequality_A/B/C`) |
| Erdős–Mordell equality case | **PARTIAL prior art** (stated as an `axiom` only); proof **OPEN** |
| Barrow's inequality | **OPEN** |
| Fermat–Torricelli point (existence, minimality) | **OPEN** |

**Most important finding:** Euler's theorem, Euler's inequality and the excircle version were already formalised by Weiyi Wang (`wwylele`). The proofs were in a public repo by 2026-01-27 and are now in **open Mathlib PR #44230** (opened 2026-09-26). The statements use exactly the same Mathlib objects as ours (`Affine.Triangle`, `incenter`, `circumcenter`, `inradius`, `exradius`). Erdős–Mordell is also done twice in Lean 4 (plby/lean-proofs, May 2026; lean-genius, June 2026). Paper H cannot claim "first formalisation" for H1.1, H1.2 (inequality), H1.3, Ptolemy, the Erdős–Mordell inequality or its key lemma.

---

## 2. Hits table (verified by opening the file)

| # | System | Location / URL | First public (commit date) | Exact statement (abridged where noted) | Class | Our item |
|---|---|---|---|---|---|---|
| 1 | Lean 4 (Mathlib, **open PR**) | https://github.com/leanprover-community/mathlib4/pull/44230 , file `Mathlib/Geometry/Euclidean/Volume/Incenter.lean` (in PR diff). Author wwylele. Labels: blocked-by-other-PR, merge-conflict | PR opened 2026-09-26. Euler commit af1075db99 dated 2026-09-26. Earliest commit in PR 2026-07-01 | `theorem dist_incenter_circumcenter_sq : dist t.incenter t.circumcenter ^ 2 = t.circumradius * (t.circumradius - 2 * t.inradius)`; `theorem two_mul_inradius_le_circumradius : 2 * t.inradius ≤ t.circumradius`; `theorem dist_excenter_singleton_circumcenter_sq (i : Fin 3) : dist (t.excenter {i}) t.circumcenter ^ 2 = t.circumradius * (t.circumradius + 2 * t.exradius {i})`; also `inradius_le_ninePointCircle_radius`. 0 `sorry` in diff. Also edits docs/100.yaml and 1000.yaml ("Euler's theorem in geometry") | SAME | H1.1, H1.2 (inequality), H1.3 |
| 2 | Lean 4 (standalone, Mathlib API) | https://github.com/wwylele/Feuerbach/blob/HEAD/Feuerbach/Basic.lean (lines 597–634) | file first commit 2026-01-27; repo created 2026-01-29 | `theorem dist_excenter_circumcenter (s : Affine.Triangle ℝ P) (signs) : dist (s.excenter signs) s.circumcenter ^ 2 = circumradius s * (s.circumradius - 2 * exradius s signs * (-1) ^ signs.card * \|∑ w\| / ∑ w)`; `theorem dist_incenter_circumcenter (s) : dist s.incenter s.circumcenter ^ 2 = circumradius s * (s.circumradius - 2 * inradius s)`; `theorem two_mul_inradius_le_circumradius (s) : 2 * s.inradius ≤ s.circumradius`. 0 sorry. No equality case (grep `equilateral`/`eq_iff` finds nothing) | SAME | H1.1, H1.2 (inequality), H1.3 |
| 3 | Lean 4 (atlas-lean, Meta) | https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/EulerOI.lean | 2026-10-05 | `theorem euler_oi : ∀ (P : Fin 3 → EuclideanSpace ℝ (Fin 2)) (O I F0 F1 F2) (R r w0 w1 w2 : ℝ), AffineIndependent ℝ P → (∀ i, dist O (P i) = R) → … dist I Fk = r, ⟪Fk - I, side⟫ = 0, I = Σ wᵢ•Pᵢ with wᵢ>0 → (dist O I)^2 = R * (R - 2*r) ∧ R ≥ 2*r`. Plane only, incircle given by explicit feet. 0 sorry. Mirrored in math-proof/lemma `Lemma/Set/Euclidean/EulerOI.lean` (2026-10-20) | SAME (different encoding) | H1.1, H1.2 (inequality) |
| 4 | Lean 4 / Lean 3 (Mathlib) | `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` in https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Geometry/Euclidean/Inversion/Basic.lean (line 179). Lean 3 original: mathlib PR #14692 (Y. Kudryashov) | Lean 3 2022-06-18; Lean 4 file 2023-07-15 (split #5868) | `theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) : dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d` | SAME (identical to ours) | Ptolemy inequality |
| 5 | Lean 4 (lean-genius) | https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/PtolemyInequalityInnerProduct.lean | 2026-06-24 | `theorem ptolemy_dist … (a b c d : P) : dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d`. 0 sorry | SAME | Ptolemy inequality |
| 6 | Lean 4 (Aristotle/Gemini, plby) | https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos898.lean (also v4.29.1, v4.30.0, v4.32.0 copies). Linked as `formal_proof` from formal-conjectures `ErdosProblems/898.lean` | v4.29.1 copy 2026-05-07 (earliest); `latest` 2026-06-24 | `variable {V} [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 2)]`; `theorem erdos_898 {A B C P : V} (h_triangle : ¬ Collinear ℝ {A, B, C}) (h_interior : P ∈ interior (convexHull ℝ {A, B, C})) : dist P A + dist P B + dist P C ≥ 2 * (dist_to_line P B C + dist_to_line P A C + dist_to_line P A B)`, where `dist_to_line P A B = dist P (orthogonalProjection (affineSpan ℝ {A,B}) P)`. 855 lines, 0 sorry, 0 axiom. No equality case | SAME (plane, interior) | H2.1 inequality |
| 7 | Lean 4 (lean-genius) | https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/ErdosMordellInequalityOQ01.lean + `ErdosMordellChordIdentity.lean` | first commit 2026-06-19; "close final sorry — fully verified" commit 7e404b2b9a on 2026-06-19 | `theorem erdos_mordell (A B C P : EuclideanSpace ℝ (Fin 2)) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ {A, B, C})) : 2 * (lineDist P B C + lineDist P C A + lineDist P A B) ≤ dist P A + dist P B + dist P C`; `theorem key_inequality_A … : dist C A * lineDist P A B + dist A B * lineDist P C A ≤ dist B C * dist P A` (and B, C). Also `erdos_mordell_reduction` (AM–GM algebraic core). 0 real `sorry`; the remaining hits are in docstrings. No equality case | SAME (plane, interior) | H2.1 inequality, H2.2 key lemma |
| 8 | Lean 4 (lean-genius) | https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos898Problem.lean | 2026-01-15 | `axiom erdos_mordell_equality … : vertexDistanceSum P A B C = 2 * sideDistanceSum P A B C ↔ IsEquilateral A B C ∧ P = centroid A B C`. File has 8 `sorry` and several axioms | PARTIAL (statement only) | H2.1 equality |
| 9 | Lean 4 (formal-conjectures) | https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/898.lean | 2026-08-04 | `theorem erdos_898 (A B C P L M N : ℝ²) … : dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L) := by sorry`, tagged `research solved` with a link to plby | PARTIAL (statement, sorry) | H2.1 |
| 10 | Lean 4 (atlas-lean Wanted) | https://github.com/facebookresearch/atlas-lean/blob/main/WantedExt/Geometry/ErdosProblem898Wanted.lean | (not dated) | `theorem_wanted conjecture_holds : conjecture`. "states the inequality but does not prove it" | PARTIAL (statement) | H2.1 |
| 11 | Lean 4 (Principia) | https://github.com/PrincipiaMathOrg/math-solutions/blob/main/mathdb/Principia/MathDB/Problem341671.lean | 2026-10-26 | Taxicab / any-normed-space variant with **constant 3/2**: `3 / 2 * (infDist P line[A2,A3] + …) ≤ ‖A1 - P‖ + ‖A2 - P‖ + ‖A3 - P‖`. 0 sorry | PARTIAL (weaker constant, other norm) | H2.1 (related) |
| 12 | Lean 4 (Compfiles) | https://github.com/dwrensha/compfiles/blob/main/Compfiles/Imo1961P2.lean | 2025-12-30 | `problem imo1961_p2a (a b c T : ℝ) (0<a,b,c) (h_area : 16 * T^2 = (a+b+c)(a+b-c)(a-b+c)(-a+b+c)) : a^2+b^2+c^2 ≥ 4 * √3 * T`; `imo1961_p2b … (0<T) : a^2+b^2+c^2 = 4*√3*T ↔ a = b ∧ b = c`. 0 sorry. Mirrored in competemath/tengoku | PARTIAL (algebraic, Heron-form) | Weitzenböck (+eq) |
| 13 | Lean 4 (lean-genius) | https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/WeitzenbockInequalityOQ01.lean | 2026-06-16 | `theorem weitzenbock (a b c T : ℝ) (0 ≤ T) (16 T² = heronArea16Sq a b c) : 4 * √3 * T ≤ a² + b² + c²`; `weitzenbock_eq_iff … ↔ a = b ∧ b = c`. 0 sorry | PARTIAL (algebraic) | Weitzenböck (+eq) |
| 14 | Lean 4 (lean-genius) | https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/WeitzenbockInequalityOQ01OQ01.lean | 2026-06-23 | `theorem hadwiger_finsler (a b c T : ℝ) (0 ≤ T) (triangle inequalities) (Heron) : 4 * √3 * T + finslerExcess a b c ≤ a² + b² + c²`, with `finslerExcess = (a-b)²+(b-c)²+(c-a)²`; `hadwiger_finsler_eq_iff … ↔ a = b ∧ b = c`. 0 sorry | PARTIAL (algebraic) | Hadwiger–Finsler (+eq) |
| 15 | Lean 4 (Mathlib master) | `Affine.Simplex.dist_lineMap_circumcenter_centroid_sq` in `Mathlib/Geometry/Euclidean/Circumcenter.lean:618` (merged via PR #44218, 2026-10) | 2026-10 | `dist (s.points i) (lineMap s.circumcenter s.centroid x) ^ 2 = (1-x)^2 R^2 + …` (vertex to a point on the Euler line). Not OG², OH² or IG² | PARTIAL (infrastructure) | OG²/OH² |
| 16 | Lean 4 (Mathlib master) | `Mathlib/Geometry/Euclidean/Incenter/Basic.lean`: `inradius`, `exradius`, `incenter`, `excenter` (first in Mathlib via PR #23752, 2025-04) | 2025 | Definitions and `dist_incenter`, `exradius_pos` etc. No R–r relation on master | UNRELATED (infrastructure) | — |
| 17 | Lean 4 (atlas-lean) | `MathlibExt/Geometry/Euclidean/FinslerHadwiger.lean` | 2026-10-05 | The Finsler–Hadwiger **squares** theorem (centres of squares on AB, AE form a square) | UNRELATED (name clash) | — |
| 18 | Lean 4 (Mathlib master) | `Mathlib/Geometry/Euclidean/NinePointCircle.lean`, `MongePoint.lean` | — | orthocenter reflection lemmas, `dist_ninePointCircle_center_sq` | UNRELATED / infrastructure | OH² |
| 19 | Lean 4 (Compfiles) | `Imo1964P2.lean`, `Imo1983P6.lean`, `Usa2001P4.lean` (uses Mathlib Ptolemy), `Imo1991P5.lean` | — | side-length olympiad inequalities, not ours | UNRELATED | — |
| 20 | Lean 3 (miniF2F) | `lean/src/test.lean`: `imo_1964_p2`, `imo_1983_p6` | — | algebraic side-length inequalities, statements only. IMO 1961 P2 is **not** in miniF2F | UNRELATED | — |
| 21 | Isabelle AFP | `Ptolemys_Theorem` (Bulwahn), `Triangle` (Eberl), `Feuerbach` (2026, Claude-assisted HOL Light port), `Stewart_Apollonius`, `Napoleon`, `Steiner_Line_Theorem`, … (full geometry topic list in §3) | — | Ptolemy **equality** (cyclic); laws of sines/cosines; Feuerbach tangency. No Euler OI, no triangle inequalities in the abstracts | UNRELATED | — |
| 22 | HOL Light | `100/ptolemy.ml` (PTOLEMY, equality for concyclic points), `100/feuerbach.ml`, `100/isoperimetric.ml`, `Multivariate/geom.ml` | — | Equalities and general isoperimetric. No R/r inequality, Erdős–Mordell or Fermat point (grep) | UNRELATED | — |
| 23 | Mizar | `EUCLID_6` (Riccardi 2008: Heron, Ptolemy equality), `EUCLID12` (Coghetto 2015: circumcenter, centroid), `EUCLID13` (orthocenter) | — | No inradius, Euler inequality or triangle inequalities found | UNRELATED | — |
| 24 | Metamath set.mm | `ptolemy` (complex-number Ptolemy equality), `heron` | — | No Euler, Erdős–Mordell or Weitzenböck | UNRELATED | — |
| 25 | GeoCoq (Rocq) | `theories/Main/Highschool/{Euler_line,incenter,circumcenter,orthocenter}.v` | — | Synthetic (Tarski/Hilbert) concurrency and collinearity. No metric quantities R, r, area, so none of our statements can be expressed | UNRELATED | — |
| 26 | Lean 4 | tejasvi/steiner-ratio-bound `lean_kernel/chain/n2m/S43Core/Geom.lean` | 2026-10-23 | `def smt3` is a computable upper bound for the 3-point Steiner tree, "exact Fermat–Torricelli value when angle tests decide". It is a definition for certificate checking, not a theorem | UNRELATED (only one file inspected) | Fermat–Torricelli |
| 27 | Freek's 100 list | https://www.cs.ru.nl/~freek/100/ | — | #95 Ptolemy (equality): HOL Light, Isabelle, Lean (Candales), Rocq, Metamath, Mizar. #29 Feuerbach; #43 Isoperimetric (HOL Light). Euler OI, Erdős–Mordell, Weitzenböck are not on the list | UNRELATED | — |

---

## 3. Every query run (unrecorded = not done)

### 3.1 GitHub code search, `--repo leanprover-community/mathlib4` (default branch = master)
`inradius` · `circumradius` · `dist_incenter` · `euler_inequality` · `Ptolemy` · `Erdos` · `Weitzenb` · `Fermat point` · `exradius` · `excenter` · `dist_incenter_circumcenter_sq` · `two_mul_inradius_le_circumradius` · `dist_excenter_singleton_circumcenter_sq` · `dist_circumcenter_centroid` · `centroid circumcenter` · `orthocenter circumcenter` · `volume_eq_inradius_mul` · `centroid dist_sq sum` · `centroid dist` · `Volume/Triangle`.
Also fetched and grepped: `docs/100.yaml`, `docs/1000.yaml`, `Inversion/Basic.lean`, `Incenter/Basic.lean`, `Circumcenter.lean`, `MongePoint.lean`, `NinePointCircle.lean`, `Triangle.lean`, `Volume/Triangle.lean`, `LinearAlgebra/AffineSpace/{Centroid,Simplex/Centroid}.lean`. Full master tree listing (`git/trees/master?recursive=1`) grepped for `Geometry/Euclidean/*` and `centroid`.

### 3.2 GitHub PR search, `--repo leanprover-community/mathlib4`
`Euler inequality` · `Euler's theorem geometry` · `inradius circumradius` · `Erdős–Mordell` · `Erdos Mordell` · `Fermat point` · `Weitzenböck` · `Leibniz` · `centroid minimizes` · `Pedoe` · `exradius` · `orthocenter distance` · `Feuerbach` · `centroid` · `Torricelli` · `isoperimetric`.
Also listed **all PRs labelled `t-euclidean-geometry`** (`gh pr list --label t-euclidean-geometry --state all --limit 400`, 214 PRs) and grepped titles for inequal|euler|centroid|fermat|ptolem|erd|mordell|weitz|isoperim|inradius|circumradius|area|heron|leibniz|apollon|pedoe|excent|orthocenter. Opened PR #44230 (full diff) and PR #44236 (Feuerbach, full diff; it contains the same Euler lemmas because it builds on #44230).

### 3.3 GitHub code search, global
`Erdos-Mordell` (lang lean) · `Mordell` (lean) · `erdos_mordell` · `Weitzenbock` (lean) · `Weitzenböck` (lean) · `hadwiger_finsler` · `Finsler` (lean) · `Gerretsen` (lean) · `Gerretsen` (all) · `Kooi inequality` · `Kooi` (lean) · `Neuberg-Pedoe` · `pedoe` (lean) · `Pedoe` (lean) · `Neuberg` (lean) · `pedoe_inequality` · `Torricelli` (lean) · `Fermat point` (lean) · `fermat_point` (lean) · `Fermat Torricelli` · `inradius` (lean) · `Euler inequality` (lean) · `two_mul_inradius_le_circumradius` · `dist_incenter_circumcenter` · `Barrow` (lean) · `mul_dist_le_mul_dist_add_mul_dist` · `erdos_mordell_eq` · `12 * Real.sqrt 3` (lean) · `perimeter area equilateral sqrt 3` (lean) · `isoperimetric triangle` (lean) · `Gergonne Nagel inradius` (lean) · `sum dist sq centroid minimum` (lean) · `orthocenter 9 * circumradius` (lean) · `Leibniz centroid` (lean) · `sum_dist_sq_centroid` · `orthocenter circumcenter dist_sq` (lean) · `inradius circumradius` (lang isabelle) · `Mordell` (isabelle) · `Mordell` (coq).
The first batch of eight (Erdos-Mordell, Erdős–Mordell, erdos_mordell, ErdosMordell, Weitzenbock, Weitzenböck, Hadwiger-Finsler, hadwiger_finsler) hit the rate limit (HTTP 403) and was **re-run** after pacing, except `ErdosMordell` and `Hadwiger-Finsler`, which were **not re-run** (see Gaps).

### 3.4 GitHub repo search
`MechGeo` · `erdos mordell` (found cozuya/taxicab-erdos-mordell, 2026-10-16, taxicab variant, **not opened**) · `triangle inequalities lean` (0) · `euclidean geometry lean4 olympiad` (0).

### 3.5 Repository scans (full tree listing + filename grep, then open relevant files)
- **Compfiles** (dwrensha/compfiles, 579 paths). Code search `EuclideanSpace` (19 files), `dist`, `inradius`, `circumradius`, `sides of a triangle`, `area`, `Erdős`, `Fermat`, `Ptolemy`, `centroid`, `R ≥ 2r`. Opened Imo1961P2, Imo1964P2, Imo1983P6, Imo1991P5, Usa2001P4, Imo1970P6.
- **lean-genius** (rjwalters/lean-genius, 39 377 paths, tree not truncated). Filename grep for euler|weitz|hadwig|finsler|gerret|kooi|ptolem|pedoe|neuberg|mordell|barrow|fermat|torricel|leibniz|centroid|isoperim|triangle|inradius|circum|orthocent|incent|apollon|stewart|heron|nesbitt|morley. Opened ErdosMordellInequalityOQ01, ErdosMordellChordIdentity, ErdosMordellChordReduction, ErdosMordellFeetAngleAristotle, Erdos898Problem, WeitzenbockInequalityOQ01, WeitzenbockInequalityOQ01OQ01, PtolemyInequalityInnerProduct, IsoperimetricTheoremOQ03 (cycle-graph isoperimetry, unrelated), FeuerbachsTheoremOQ04Circumcircle (spherical, unrelated).
- **atlas-lean** (facebookresearch/atlas-lean, 17 335 paths). Listed all `*/Geometry/Euclidean/*` (≈40 files) and `WantedExt/Geometry/*`. Opened EulerOI, FinslerHadwiger, ErdosProblem898Wanted. Grepped the whole tree for euler|inradius|mordell|weitz|ptolem|fermat|torric|isoperim|leibniz.
- **formal-conjectures**: tree grep for triang|euler|mordell|ptolem|fermat|torric|weitz|isoperim. Opened ErdosProblems/898.lean.
- **plby/lean-proofs**: opened `src/latest/ErdosProblems/Erdos898.lean`, plus commit history of the v4.29.1 copy.
- **math-proof/lemma**: tree grep of `Lemma/Set/Euclidean/` (found mirrors of atlas-lean: EulerOI, FinslerHadwiger, Pompeiu, CarnotInradius). Opened EulerOI.
- **wwylele/Feuerbach**: full tree (2 Lean files), opened Basic.lean.
- **MechMath/MechGeoBench** (benchmark for arXiv 2608.02295 MechGeo): tree listing. IMO problems 2000–2026 only, no IMO 1961 P2 and no triangle inequality.
- **tejasvi/steiner-ratio-bound**: opened `S43Core/Geom.lean`.
- **Lean 3 mathlib** (leanprover-community/mathlib master tree): `src/geometry/euclidean/*` and `archive/imo/*`. Opened inversion.lean (Ptolemy inequality) and commit history.
- **miniF2F** (openai/miniF2F): tree grep, `lean/src/test.lean` and `valid.lean` grep for imo_1961, imo_1964_p2, imo_1983_p6.
- **HOL Light** (jrh13/hol-light): tree grep. Opened 100/ptolemy.ml, 100/feuerbach.ml, 100/euler.ml (partition theorem, unrelated), Multivariate/geom.ml (grep ptolemy|fermat|torric|mordell|euler and TRIANGLE_* names).
- **GeoCoq**: tree grep for euler|ptolem|mordell|fermat|torric|inequal|triangle|incent|circumc|centroid|orthoc|heron.

### 3.6 Non-GitHub sources (curl)
- **Isabelle AFP:** https://www.isa-afp.org/topics/mathematics/geometry/ lists 33 entries: Banach_Tarski Buffons_Needle Buildings Ceva Chord_Segments Complex_Geometry Conway_Circle Cube_Dissection Feuerbach Foundation_of_geometry General_Weierstrass Gromov_Hyperbolicity Grothendieck_Schemes Hidden_Number_Problem Impossible_Geometry IsaGeoCoq Lie_Groups Minkowskis_Theorem Miquel Napoleon Nullstellensatz Octonions Picks_Theorem Platonic_Solids Poincare_Disc Projective_Geometry Ptolemys_Theorem Quaternions Schutz_Spacetime Simson Steiner_Deltoid Steiner_Line_Theorem Stewart_Apollonius Tarskis_Geometry Triangle. Read the abstracts of Triangle, Ptolemys_Theorem, Feuerbach, Napoleon, Steiner_Line_Theorem, Stewart_Apollonius. Checked https://www.isa-afp.org/entries/Euler_Triangle_Inequality.html (**404**; see Gaps).
- **Freek Wiedijk 100:** https://www.cs.ru.nl/~freek/100/ grep for Ptolemy|Isoperimetric|Feuerbach|Euler|Heron|Triangle.
- **Metamath set.mm** (develop branch, 51.7 MB): grep ptolemy|mordell|weitzenb|euler's theorem/inequality|inradius|circumradius|torricelli|fermat point|heron, then centroid|incent|"inequality … triangle".
- **Mizar MML** (mizar.uwb.edu.pl/version/current/html): index of 1500 articles. Fetched euclid_3, euclid_4, euclid_6, euclid_7, euclid_9, euclid10, euclid11, euclid12, euclid13 and grepped Ptolemy|Euler|Heron|inequalit|incircle|circumcircle|Stewart|Morley|Napoleon|Ceva|Menelaus|centroid|orthocent. Grepped index titles for inequalit|triangle|euler|ptolemy|heron|morley|incircle|incenter.
- **arXiv API** (export.arxiv.org): `all:"Erdos-Mordell"` · `all:Mordell AND all:formalization` · `all:"triangle inequalities" AND proof AND automated` · `all:Bottema AND inequalities` · `all:Lean AND "Euclidean geometry"` · `all:"geometric inequalities" AND Lean` · `all:Isabelle AND triangle AND geometry` · `ti:MechGeo` · `all:"Euler's inequality"` · `all:"Weitzenbock" AND inequality` · `all:Fermat AND Torricelli AND formal` · `abs:"Erdos-Mordell" AND abs:Lean` · `all:"olympiad geometry" AND Lean AND inequality`. (A first run over http:// returned nothing because of a redirect. It was re-run over https://, and those results are what's reported.) Relevant results: 2608.02295 *MechGeo* (Lean 4 IMO geometry 2000–2026, none of our theorems); 1708.02993 *On Euler's inequality and automated reasoning with dynamic geometry* (GeoGebra loci, not a formal proof); *On the Erdos-Mordell Inequality for Triangles in Taxicab Geometry* (2019-01-25; arXiv id not recorded) (informal source of Principia #11); 0708.2871 *Sharpness of the Finsler–Hadwiger inequality* (informal).
- **WebSearch** (tool): `Erdős–Mordell inequality formal proof Isabelle OR Coq OR "HOL Light" OR Lean` · `Euler inequality R ≥ 2r formalization theorem prover Isabelle triangle inradius circumradius` · `Weitzenböck inequality formalized proof assistant` · `"Erdős-Mordell" Lean formalization 2026` · `Bottema triangle inequalities automated proving Gerretsen Kooi formal verification`. **All unusable** (see Gaps).
- **WebFetch:** https://www.erdosproblems.com/898 returned HTTP 403.

---

## 4. Per-theorem novelty verdict (with comparison to our exact statement)

**H1.1 Euler OI² = R² − 2Rr — CLOSED.** wwylele/Feuerbach (2026-01-27), Mathlib PR #44230 (2026-09-26, open, not merged) and atlas-lean `euler_oi` (2026-10-05, ℝ² with explicit incircle data) all prove it. wwylele and PR #44230 use the *same* Mathlib definitions as ours: `Affine.Triangle ℝ P`, `t.incenter`, `t.circumcenter`, `t.inradius`. Their RHS `R * (R - 2r)` is ring-equal to our `R^2 - 2*R*r`. Our proof may differ in route; check PROGRESS.md before claiming any methodological novelty.

**H1.2 Euler inequality 2r ≤ R — CLOSED** (same three sources; the lemma name `two_mul_inradius_le_circumradius` is identical in wwylele and PR #44230). **Equality case ⇔ equilateral — OPEN.** None of the sources has it (grep for `equilateral`, `eq_iff` in wwylele, PR #44230 and atlas-lean found nothing).

**H1.3 Euler for excircles — CLOSED.** PR #44230 has `dist_excenter_singleton_circumcenter_sq (i : Fin 3) : dist (t.excenter {i}) t.circumcenter ^ 2 = R * (R + 2 * t.exradius {i})`, essentially our `euler_excenter` verbatim. wwylele has a general `signs` version with a sign factor.

**H1.4 Weitzenböck (+eq), Hadwiger–Finsler (+eq) — PARTIAL.** Compfiles IMO 1961 P2 (2025-12-30) and lean-genius (2026-06-16 / 2026-06-23) prove the *algebraic* forms: real a, b, c, T with Heron's relation `16T² = …` as hypothesis, plus triangle inequalities for H-F, and equality ⇔ a = b = c. None of them states the result for an `Affine.Triangle` with its actual area (Mathlib `volume`/our `area`), which needs a Heron bridge. Heron itself is in Mathlib (Archive, being promoted by PR #44148). Novelty is limited to the geometric packaging.

**H1.5 Gerretsen — OPEN.** No formal statement found in any system (code search `Gerretsen`, global and lean, gave only name-collision noise).

**H1.6 OG², OH², IG² — OPEN.** Mathlib master has `dist_lineMap_circumcenter_centroid_sq` (vertex to any point on line OG) and `dist_ninePointCircle_center_sq`. The OH² formula follows quickly from these, but no OG², OH² or IG² statement was found anywhere.

**Kooi (+ Kooi ≤ Gerretsen) — OPEN.**

**Neuberg–Pedoe (+ equality ⇔ similar) — OPEN.**

**Ptolemy inequality — CLOSED.** Mathlib `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`, Lean 3 since 2022-06-18 (Kudryashov), Lean 4 since the port. Identical statement and identical generality (any inner-product-space torsor). Our theorem is a reproof. lean-genius also has it (2026-06-24).

**Leibniz relation / minimum (+eq ⇔ centroid) — OPEN.** No Mathlib lemma on Σ dist² to the centroid was found (centroid files have no dist/norm lemmas). It may exist under an unexpected name in `Analysis/InnerProductSpace` (variance-type identities). Gap: not exhaustively grepped.

**Triangle isoperimetric 12√3Δ ≤ p² (+eq) — OPEN.** Only the general (Jordan-curve) isoperimetric theorem appears (HOL Light #43, kim-em/isoperimetric per Mathlib docs/100.yaml). These don't specialise to this statement.

**H2.1 Erdős–Mordell inequality — CLOSED** for the plane, interior-point version:
plby/lean-proofs `erdos_898` (first copy 2026-05-07, any 2-dim inner-product space, `P ∈ interior (convexHull …)`, distances via `orthogonalProjection` onto `affineSpan`) and lean-genius `ErdosMordellOQ01.erdos_mordell` (sorry-free 2026-06-19, `EuclideanSpace ℝ (Fin 2)`).
*How ours differs (a possible minor-novelty angle):* ours is for `Triangle ℝ P` in an **arbitrary-dimensional** inner-product torsor, and `X` is in the **closed** triangle (weights ≥ 0, boundary allowed). It is a mild generalisation, not new mathematics.

**H2.1 equality case (⇔ equilateral ∧ X = centroid) — OPEN as a proof.** It is only stated, as an `axiom`, in lean-genius `Erdos898Problem.lean` (2026-01-15).

**H2.2 key lemma — CLOSED.** lean-genius `key_inequality_A/B/C` (interior, ℝ²) has the same weighted form `b·d_c + c·d_b ≤ a·PA`. plby has an analogous internal lemma. Ours allows the closed triangle and any dimension.

**H2.3 Barrow — OPEN.** "Barrow" appears only in docstrings and references.

**H2.4 Fermat–Torricelli (existence under all angles < 120°, minimality) — OPEN.** The only Lean hit (steiner-ratio-bound) is a computable bound definition, not a theorem.

**Related but not ours:** taxicab / normed-space Erdős–Mordell with constant 3/2 (Principia 2026-10-26; cozuya repo 2026-10-16, not opened).

---

## 5. Gaps in the search (read before relying on "OPEN")

1. **WebSearch tool was unusable.** Two queries returned "no web search tool available", one timed out (HTTP 524), and two returned results with garbled markup. Those results included a **made-up AFP entry "Euler_Triangle_Inequality"**, and curl confirmed the URL returns 404. All web-search output was discarded. As a result, **Google Scholar, Lean Zulip, Isabelle mailing list, MathOverflow, blogs and conference proceedings (ITP, CICM, ADG, ThEdu) were NOT searched.** ADG/ThEdu papers on automated proofs of Euler/Weitzenböck/Erdős–Mordell (e.g. via quantifier elimination, Bottema, GeoGebra Discovery) are the most likely missed prior art, though they are usually not formal proofs in an ITP.
2. **erdosproblems.com/898** returned 403. Forum mentions of other formal proofs of the equality case may exist.
3. **GitHub code search** only indexes default branches and files under a size limit, and caps results (≤30 per query here). Forks, non-default branches, gists, GitLab, Codeberg and Hugging Face datasets were not covered. Two rate-limited queries (`ErdosMordell`, `Hadwiger-Finsler`) were not re-run. Their siblings `erdos_mordell` and `hadwiger_finsler` were re-run.
4. **No external file was compiled.** "sorry-free" claims for wwylele, plby, lean-genius, atlas-lean and Compfiles rest on grep plus the repos' own CI claims. The PR #44230 status (open, merge-conflict, blocked) means it is **not in Mathlib master** as of today. If it merges before Paper H, Euler/Euler-inequality/excircle become Mathlib lemmas.
5. **Isabelle AFP:** only the geometry topic list and six abstracts were read, not theory sources. Entries outside the geometry topic (e.g. in Analysis or Inequalities) were not listed. The AFP full-text search was not used.
6. **HOL Light:** only `100/*` and `Multivariate/geom.ml` were grepped, not `Examples/` or all of `Multivariate/`. **Coq/Rocq:** GeoCoq tree only. The coq-community 100-theorems repo, Coquelicot and Math Classes were not checked.
7. **Mizar:** only the EUCLID* articles were inspected. Other geometry articles (e.g. TOPREAL*, EUCLIDLP, GEOMTRAP, TRIANG_1) were not opened. **Metamath:** set.mm only (not iset.mm or mathboxes separately, though mathboxes are inside set.mm).
8. **Compfiles:** every file matching `EuclideanSpace` (19) was located, but only 7 were opened. Algebraic side-length inequalities without `EuclideanSpace` were found only via keyword search.
9. **Mathlib Leibniz/centroid identities** may exist in `Analysis/InnerProductSpace/*` under a variance-style name. Only Euclidean and AffineSpace centroid files were grepped.
10. **Other AI-proof aggregators** (Harmonic/Aristotle results pages, DeepMind AlphaProof/AlphaGeometry outputs, LeanPool/lean-pool, competemath/tengoku, Numina, Lean Workbook) were only covered as far as global code search reached. These are fast-growing in 2026 and likely to contain more triangle-inequality proofs, especially of Weitzenböck/IMO 1961 P2 variants.
11. **The time box was not exhausted** (about 1 h 15 min used). Items 1, 5 and 6 are the best uses of further time.
