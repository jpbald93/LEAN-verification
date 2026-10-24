# L15 classical comparison — Paper TriSimplex

Comparer: Claude (Opus 5.5), not blind. Inputs: `trisimplex.tex` (availability section → 5 repos at pinned commits), the blind writer file `/tmp/blindTriSimplex/Classical.lean` (25 `sorry` statements, namespace `ClassicalTriSimplex`), its `CLASSICAL_REPORT.md`, and `classical_statements.txt`.

## Setup (john, arm64 macOS)

| repo (github.com/jpbald93/…) | pinned commit (paper) | fresh clone | build | gate |
|---|---|---|---|---|
| carnot | 98e5614812f2fc2491a729adf9677bfce9b55217 | ~/lean/l15TriSimplex_carnot | rc=0 | **PASS (12 declarations, standard axioms only)** |
| viviani | 029aa3d464db2ac8b3eb2e8f57e79e80f5585803 | ~/lean/l15TriSimplex_viviani | rc=0 | **PASS (10 declarations, standard axioms only)** |
| degua | d46e6b20717012a9ca49fa3bffb08a5db0bdd2e7 | ~/lean/l15TriSimplex_degua | rc=0 | **PASS (10 declarations, standard axioms only)** |
| japanese-theorem | 34fd0a9c71c6efdca2f154043820f2a6aef7fb3a | ~/lean/l15TriSimplex_japanese-theorem | rc=0 | **PASS (51 declarations, standard axioms only)** |
| poncelet-triangles | 9affe6203bbf0ec0f42eeb8c8ce567159de19b40 | ~/lean/l15TriSimplex_poncelet-triangles | rc=0 | **PASS (22 declarations, standard axioms only)** |

All five use `leanprover/lean4:v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, so `.lake/packages` is a symlink to `~/lean/clifford/.lake/packages`. No `lake update` or `cache get` was run.
Gate note: plain `~/lean/jl gate` fails with `FAIL: axiom report` in all five repos. The cause is that `gate.sh` calls GNU `mktemp --suffix=.lean`, which the BSD `mktemp` on the wrapper's default PATH does not support. This is an environment issue, not a library issue. The gates were run with `~/lean/jl -g gate` (GNU tools), and the PASS lines above come from that run.

## Classification table

Writer statements are copied verbatim into `scratch/L15_compare.lean` of the relevant repo, each packaged as `def classical_X : Prop := ∀ …, <statement>`. Writer definitions (`signedDistLine`, `hullVol`, `triInradius`, `triIncenter`, `IsRectangle`, `IsConvexPolygon`, `IsTriangulation`, `IsConvexQuad`, `Interscribed`) are copied verbatim too.

| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| classical_TriSimplex1_a (Carnot, signed) | **E** | `cov_TriSimplex1_a` ← `Carnot.carnot` | — | Bridge (NEW): `signedDistLine_face_eq`: the writer's `SOppSide` signed distance equals Mathlib `signedInfDist` on the triangle's span, which equals `Carnot.signedSideDist` (`signedSideDist_eq_signedInfDist`). Any ambient dimension. |
| classical_TriSimplex1_b_signed (d = R cos) | **E** | `cov_TriSimplex1_b_signed` ← `Carnot.signedSideDist_circumcenter_eq` | — | same bridge; `angle_comm` |
| classical_TriSimplex1_b (cos sum) | **E** | `cov_TriSimplex1_b` ← `Carnot.cos_add_cos_add_cos` | — | |
| classical_TriSimplex1_b_acute (unsigned) | **E** | `cov_TriSimplex1_b_acute` | — | NEW short proof: acute ⇒ R cos > 0 ⇒ signed distance = `infDist` |
| classical_TriSimplex1_b_acute_inside | **E** (paper doesn't state it; proved) | `cov_TriSimplex1_b_acute_inside` | — | NEW: barycentric weights of O are `signedSideDist / height > 0` (`Carnot.signedSideDist_affineCombination`) |
| classical_TriSimplex2_a (De Gua 3D, `hullVol`) | **N** | `cov_TriSimplex2_a_part` ← `DeGua.de_gua_three`, `triAreaSq_eq_simplexVolSq` | the link `hullVol(·)^2 = simplexVolSq` (Lebesgue measure of the hull inside `vectorSpan` = Gram determinant / k!²) | The paper says explicitly (§De Gua, §limits) that `simplexVolSq` is a *definition* not linked to any measure. The part needs no affine independence. Not closed: it would need parallelotope volume = √det G and simplex = 1/k! of it inside a subspace measure, well over the time budget. |
| classical_TriSimplex2_a_coord | **N** | `cov_TriSimplex2_a_coord_part` (NEW evaluation, via cross product) | same `hullVol` link | holds for all real a, b, c |
| classical_TriSimplex2_b (n-simplex) | **N** | `cov_TriSimplex2_b_part` ← `DeGua.de_gua` | same `hullVol` link; also tuple-vs-image-set facet indexing | Part holds in any real inner product space, n ≥ 1 |
| classical_TriSimplex2_b_coord | **N** | covered by `cov_TriSimplex2_b_part` (coordinate vertices satisfy orthogonality) | same `hullVol` link | no separate Lean statement |
| classical_TriSimplex3_a (Viviani, interior) | **E** | `cov_TriSimplex3_a` ← `Viviani.equilateral_triangle'`, `Equilateral.height_eq` | — | NEW: `height_two_eq`: equilateral height = (√3/2)·\|AB\|; the repo stops at "= height". `interior ⊆ closedInterior`. |
| classical_TriSimplex3_b_closed | **E** | `cov_TriSimplex3_b_closed` | — | any ambient dimension |
| classical_TriSimplex3_b (signed, whole plane) | **E** | `cov_TriSimplex3_b` ← `Equilateral.sum_signedInfDist_eq_height` + `signedDistLine_face_eq` | — | under the writer's `finrank V = 2` |
| classical_TriSimplex4_a (Japanese n-gon, dissection form) | **N** | `cov_TriSimplex4_a_part` ← `Japanese.japanese_polygon_geometric` | (i) writer's `IsTriangulation` (cover + disjoint interiors, `Fin n`) vs repo's maximal sets of non-crossing chords on ℕ-indexed points; (ii) writer's side-line convexity vs repo's orientation hypothesis `hconv` (all triples a<b<c positive) | The paper lists both gaps as unformalised (§Japanese, §limits: "We have not shown that every dissection … arises this way; that needs an area or measure argument"; "hconv … not Mathlib's Convex"). Not closed: needs a measure/area argument. |
| classical_TriSimplex4_a_obligation | **E (NEW PROOF)** | `cov_TriSimplex4_a_obligation` | — | strict convexity ⇒ no vertex is between two others ⇒ non-collinear |
| classical_TriSimplex4_b (Japanese quadrilateral) | **E** (NEW PROOF of the reduction) | `cov_TriSimplex4_b` (any dimension) via `cov_TriSimplex4_b_part` (plane) ← `Japanese.japanese_quadrilateral` | — | NEW: crossing diagonals (`IsConvexQuad`) give the four orientation signs (`quad_signs`), after choosing the orientation that makes ABC positive. Degenerate cases (A=B or B=C) are 0 = 0. General dimension: restrict to the plane S = span(A,B,C); D ∈ S by the diagonals; the sphere centre projected to S gives a circle in S (`triInradius_subtype` via `inradius_map`). |
| classical_TriSimplex4_b_obligation | **D (writer's statement false)** | `not_classical_TriSimplex4_b_obligation`; corrected `cov_TriSimplex4_b_obligation_part` (NEW) | — | Counterexample in ℝ: A=B=0, C=D=1, X=½. `IsConvexQuad` (two `Sbtw`) does not force distinct vertices, and {0,1} is cospherical. The writer mis-stated the textbook ("convex quadrilateral" means 4 distinct vertices). With the vertices pairwise distinct it holds in any dimension. |
| classical_TriSimplex4_b_rectangle | **D as written / O** | `not_classical_TriSimplex4_b_rectangle` | the true (distinct-vertex) statement is not proved | Same degenerate counterexample: `triIncenter 0 0 1 = 0 = triIncenter 0 1 1` (junk values) violates `p₁ ≠ p₂`. The incentre rectangle is not claimed by the paper (out of scope), and the corrected version was not proved (not cheap). |
| classical_TriSimplex5_a (Euler OI²) | **E** | `cov_TriSimplex5_a` = `Feuerbach.dist_circumcenter_incenter_sq` (copied into poncelet-triangles/Poncelet3/Euler) | — | |
| classical_TriSimplex5_b (2r ≤ R, = ⇔ equilateral) | **E** (inequality from the repo; NEW PROOF of the equality case) | `cov_TriSimplex5_b` ← `Feuerbach.two_mul_inradius_le_circumradius` | — | Equality case not in the repo. NEW: `dist_face_sq` (R² = d(O,side)² + (side/2)²). R=2r ⇒ O=I ⇒ equal sides; equilateral ⇒ O equidistant from the sides ⇒ O is the incentre or an excentre; the excentre case is excluded by the excentral Euler formula. |
| classical_TriSimplex6_a (porism) | **E** | `cov_TriSimplex6_a` ← `exists_poncelet_triangle` + NEW `insphere_eq_of_isTangent` | — | The repo says "sides tangent"; the writer needs `insphere = γ`. Bridge adapted from `euler_of_isTangent`: three tangent sides + I inside Γ ⇒ γ is the incircle (excircle case excluded). |
| classical_TriSimplex6_a_construction | **E** | `cov_TriSimplex6_a_construction` ← `poncelet_construction` | — | NEW `mem_tangentsFrom_of_isTangent`: a tangent line XY lies in `tangentsFrom X` |
| classical_TriSimplex6_a_obligation (exactly two tangents, any d) | **N** | `cov_TriSimplex6_a_obligation_part` ← `tangentsFrom_eq_pair` | the case d² ≠ R² − 2Rr | The repo proves the two-tangent structure only under Euler's relation (the paper's Lemma pon-correct). The general case (every point of Γ lies outside γ, so there are two tangents) is true but was not proved. Carried as a hypothesis (`hd`) in the part. |
| classical_TriSimplex6_b (iff) | **E** | `cov_TriSimplex6_b` ← `exists_poncelet_triangle`, `Feuerbach.dist_circumcenter_incenter_sq` | — | (⇒) circumcircle = Γ and insphere = γ, then Euler; (⇐) porism + `insphere_eq_of_isTangent` |
| classical_TriSimplex6_b_converse | **E** | `cov_TriSimplex6_b_converse` | — | |
| classical_TriSimplex6_b_noclose | **E** | `cov_TriSimplex6_b_noclose` ← `Poncelet3.euler_of_isTangent` | — | |

Summary over 25 writer statements: **E 17** (1a, 1b_signed, 1b, 1b_acute, 1b_acute_inside, 3a, 3b_closed, 3b, 4a_obligation, 4b, 5a, 5b, 6a, 6a_construction, 6b, 6b_converse, 6b_noclose), **N 6** (2a, 2a_coord, 2b, 2b_coord, 4a, 6a_obligation), **D 2** (4b_obligation and 4b_rectangle are false as written because the writer's `IsConvexQuad` admits degenerate quadrilaterals; the rectangle is also outside the paper's scope).
Of the E entries, 1b_acute_inside, 4a_obligation and the equality half of 5b are not stated in the paper. They are covered by new proofs on top of repository lemmas.
Main gaps relative to the textbook: (a) De Gua's volume is the Gram-determinant definition `simplexVolSq`, not Lebesgue/Hausdorff measure (the paper says so explicitly); (b) the Japanese n-gon is proved for chord-maximal triangulations of an orientation-convex ℕ-indexed polygon, not for dissections (the paper says so explicitly); (c) the two-tangent structure from points of Γ is proved only under Euler's relation.

## NEW PROOFS (scratch only, no library edits)
- `signedDistLine_face_eq` (carnot, viviani): the writer's `SOppSide`-signed `infDist` to a facet equals Mathlib's `Affine.Simplex.signedInfDist` on the span, for any simplex.
- `cov_TriSimplex1_b_acute`, `cov_TriSimplex1_b_acute_inside`.
- `height_two_eq` (viviani): the altitude of an equilateral triangle is (√3/2)·side.
- `cov_TriSimplex2_a_coord_part`: coordinate evaluation of `simplexVolSq`.
- `areaForm_ne_zero_of_affineIndependent`, `quad_signs`, `cov_TriSimplex4_b_part` (japanese): crossing diagonals ⇒ the four orientation hypotheses of `japanese_quadrilateral`; `triInradius_subtype`, `cov_TriSimplex4_b`: reduction from any dimension to the plane of ABC.
- `cov_TriSimplex4_a_obligation`, `cov_TriSimplex4_b_obligation_part`; counterexamples `not_classical_TriSimplex4_b_obligation`, `not_classical_TriSimplex4_b_rectangle`.
- `dist_eq_half_of_mem_line`, `dist_face_sq`, `cov_TriSimplex5_b` (equality case of Euler's inequality).
- `insphere_eq_of_isTangent`, `mem_tangentsFrom_of_isTangent`, `euler_of_interscribed`, and all `cov_TriSimplex6_*`.

## Obligations
| obligation | status |
|---|---|
| 4a_obligation (triangles of a triangulation are non-degenerate) | **proved** (`cov_TriSimplex4_a_obligation`) |
| 4b_obligation (ABC, ACD, ABD, BCD non-degenerate) | **false as written** (degenerate `IsConvexQuad`); **proved** with distinct vertices (`cov_TriSimplex4_b_obligation_part`). `cov_TriSimplex4_b_part` does not need it (degenerate cases are handled directly). |
| 6a_obligation (two tangents from X ∈ Γ, each meeting Γ again) | **proved under Euler's relation** (`cov_TriSimplex6_a_obligation_part`, hypothesis `hd` carried explicitly); general d not proved. The 6a/6b statements that use the construction do not depend on it. |

No sorry, admit or axiom anywhere; no hypothesis was silently added to a `cov_` theorem (every extra hypothesis is listed in the "missing" column).

## Compile / forbidden grep / axioms
Each file was compiled with `~/lean/jl lake env lean scratch/L15_compare.lean` from inside its repo:
| repo | rc | errors | "declaration uses sorry" | forbidden grep (`sorry\|admit\|native_decide\|axiom`) |
|---|---|---|---|---|
| carnot | 0 | 0 | 0 | none |
| viviani | 0 | 0 | 0 | none |
| degua | 0 | 0 | 0 | none |
| japanese-theorem | 0 | 0 | 0 | none |
| poncelet-triangles | 0 | 0 | 0 | none |

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every theorem listed: cov_TriSimplex1_a, 1_b_signed, 1_b, 1_b_acute, 1_b_acute_inside; 3_a, 3_b_closed, 3_b, height_two_eq; 2_a_part, 2_a_coord_part, 2_b_part; 4_b_part, 4_b, not_…4_b_obligation, not_…4_b_rectangle, 4_b_obligation_part, 4_a_obligation, 4_a_part; 5_a, 5_b, 6_a, 6_a_construction, 6_a_obligation_part, 6_b, 6_b_converse, 6_b_noclose. The scripted check filtered for any line differing from that list and printed nothing.

## Library hashes (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`), before = after
| repo | hash |
|---|---|
| carnot | 0b16f1393c13891bed58a8a8564c6dadc878d1d796b3e657cee6db22d826e067 |
| viviani | 7de630aa31d8e9576d854d32bf4a14c6c324e9de026ae9db94f7a066f93e5c6c |
| degua | 10985e412b1fe1ca08f6c417b70f07b0882edaffe797c0cdfbf2b7af51e7d013 |
| japanese-theorem | e97a4fa504514ce21c72bbe0d0640e17150851b86def640585d409d6acfcd004 |
| poncelet-triangles | 7ecdb15d0ab43238de1b9061ad830b4d4d63855f4c7e867d5686af9e661b7937 |
`git status --porcelain` shows only `?? scratch/L15_compare.lean` in each clone.

## Scratch paths
- john:~/lean/l15TriSimplex_carnot/scratch/L15_compare.lean (sha256 422ead9b…)
- john:~/lean/l15TriSimplex_viviani/scratch/L15_compare.lean (e356af17…)
- john:~/lean/l15TriSimplex_degua/scratch/L15_compare.lean (fc7be336…)
- john:~/lean/l15TriSimplex_japanese-theorem/scratch/L15_compare.lean (e85feaf1…)
- john:~/lean/l15TriSimplex_poncelet-triangles/scratch/L15_compare.lean (ab263f45…)
- local copies: <oc>/tmp/overnight1022/l15c/TriSimplex/scratch/{carnot,viviani,degua,japanese,poncelet}.lean

## Wall time
Start 01:18 PDT (john). Core results 02:17; 4b closed in all dimensions and final checks at 02:22 PDT (≈1 h 05 min). The final compile, forbidden grep, axiom filter, hashes and `git status` were re-run after the last edit (japanese) and are unchanged elsewhere.
