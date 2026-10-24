# Layer 15 — classical comparer, Paper C (barbier + fourvertex)

Date 2026-10-22. Machine john (arm64 macOS). Wall time ≈ 0 h 50 min (02:32 → 03:22).
Inputs: `paperc.tex`; blind writer file `/tmp/blindC/Classical.lean` (md5 a624b3d5…, namespace
`PaperCClassical`, 17 `classical_*` statements + 2 obligations); `/tmp/blindC/CLASSICAL_REPORT.md`;
`/tmp/blindC/classical_statements.txt`.

## Repositories (fresh clones of the published pins)
| repo | clone | commit | toolchain / Mathlib | packages | gate |
|---|---|---|---|---|---|
| barbier | `~/lean/l15C_barbier` | 7baae0430954ce78ddf8d6e6bf5a4b841d7b2367 | v4.33.1 / 0df444a3 | symlink `~/lean/clifford/.lake/packages` | `PASS (62 declarations, standard axioms only)` rc=0 |
| fourvertex | `~/lean/l15C_fourvertex` | 14d10449dd1a206f5342099d65d5f4180830d423 | v4.33.1 / 0df444a3 | symlink `~/lean/clifford/.lake/packages` | `PASS (48 declarations, standard axioms only)` rc=0 |

Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`):
- barbier: before = after = `d2bc26e6d822aad0b93ce4f06cc742d0bffdf74510de0194d530190ad321f2a9`
- fourvertex: before = after = `f136271b917318e5a8efcff7d696f6decce7c0dbb1a6ebc9f55eacc6efd18d99`
`git status --porcelain` in both: only `?? scratch/L15_compare.lean`.

## Method
The writer file is copied **verbatim** (definitions untouched). Each `theorem classical_X … := by sorry`
is turned mechanically into `def classical_X : Prop := ∀ <binders>, <statement>` (Python script;
binders and statement text unchanged). The obligations become `obl_supportFn` / `obl_perimeter`. The
bridge from the repos' ℂ to the writer's `Plane = EuclideanSpace ℝ (Fin 2)` is Mathlib's linear isometry
`E := Complex.orthonormalBasisOneI.repr` (`z ↦ !₂[re z, im z]`). Bridge lemmas (all proved): `deriv_E_comp`,
`curveLength_E`, `eVariationOn_E`, `E_curve` (E ∘ Barbier.curve h = the writer's envelope `!₂[p cos − p' sin, p sin + p' cos]`),
`sc_E` (writer's `signedCurvature (E ∘ γ)` = `FourVertex.signedCurvature γ`), `supportFn_E_body`,
`hasConstantWidth_E_body`.

## Table
| statement | class | Lean theorem(s) | missing | note |
|---|---|---|---|---|
| `classical_C1_a` (Barbier, smooth, arbitrary C² simple convex closed curve) | N | `cov_C1_a_part` | the classical statement quantifies over **arbitrary** curves `γ` whose hull has constant width; the repo only treats curves *given by* a C² support function, γ = γ_h. Missing: every such γ is (a reparametrisation of) γ_h for a C² `h` with h+h''≥0, and `curveLength` is reparametrisation-invariant. | For `ConstWidthSupport h w`, `w>0`: `curveLength (E∘γ_h) (2π) = πw`, Mathlib `eVariationOn (E∘γ_h) [0,2π] = ofReal(πw)`, and `E '' K_h` has `HasConstantWidth … w` in the writer's sense. Paper §1 "What is not claimed" says exactly this. Paper narrower, not different. |
| `classical_C1_a_support` | **E** | `cov_C1_a_support : classical_C1_a_support` | — | From `Barbier.perimeter_eq_integral` + `integral_support_eq` (+ `E_curve`, `curveLength_E`). The writer's `p+p''>0` is stronger than the repo's `≥0`. |
| `classical_C1_b` (general convex body, writer's `perimeter` = sup of eVariation over boundary parametrisations) | N | `cov_C1_b_part` | (i) every constant-width convex body is `K_h` for a `PiecewiseConstWidth` `h`, i.e. the support function of an arbitrary constant-width body is C¹ with h+h'' a measure that has a density (paper: not claimed, §1/§9); (ii) `frontier K_h` = range γ_h, γ_h simple, so it is an `IsBoundaryParam` after rescaling [0,2π]→[0,1], and the writer's `perimeter` ⨆ equals `eVariationOn γ_h`; (iii) for the general piecewise class, Barbier `perimeter h` = eVariation (paper says left open, only proved smooth + Reuleaux). | For `PiecewiseConstWidth h w`, `w>0`: `E '' K_h` is compact, convex, `HasConstantWidth (E '' K_h) w` (writer's notion, NEW bridge proof from `support_body_piecewise` + `width`), and `Barbier.perimeter h = πw`. Nonempty interior not proved. |
| `classical_C1_b_equiv` | N | `cov_C1_b_equiv_part` | same as C1_b | `Barbier.perimeter h = Barbier.perimeter (fun _ => w/2)` (circle of diameter w) via `barbier_piecewise`, `circle_perimeter`. |
| `classical_C2_boundary` | N | `cov_C2_boundary_part` | the frontier = union of the three arcs (set equality on the writer's `⋂ closedBall`) | NEW PROOF (Mathlib only): the three angles are π/3. The repo's `reuleaux_arc` gives one arc of the **repo's** curve (radius w about γ(0)), see C2_b_part, but no theorem links the repo's γ_{R_w} to the writer's `⋂ closedBall A w ∩ …`. |
| `classical_C2_a` | N | `cov_C2_a_part`, `isPlaneConvexBody_reuleaux`, `reuleaux_not_disk`, `cov_C2_b_part` | `HasConstantWidth (reuleauxTriangle A B C w) w`, corner set = {A,B,C}, interior angles 2π/3 | NEW PROOFS: the writer's Reuleaux triangle is an `IsPlaneConvexBody` (centroid is interior), and it is not a closed disk (Apollonius argument). Constant width is proved in the repo only for `E '' K_{R_w}` (in `cov_C2_b_part`), and the repo does not identify `K_{R_w}` with `⋂ closedBall`. Corners/angles: not in the paper. |
| `classical_C2_b` | N | `cov_C2_b_part` | identification `E '' K_{R_w}` (or range γ_{R_w}) with the writer's `reuleauxTriangle A B C w` / its frontier, for some (in fact any, after an isometry) equilateral A,B,C; and writer's `perimeter` = eVariation of that parametrisation | For the repo's curve transported to ℝ²: vertices pairwise at distance w, arc of radius w about the first vertex on [5π/6,7π/6], Mathlib length `eVariationOn = ofReal(3(w·π/3)) = ofReal(πw)`, and `E '' K_{R_w}` compact, convex, of constant width w (writer's sense). |
| `classical_C2_c` (area) | O | — | everything | Paper does not claim the area. Not attempted (needs a measure computation of the lens decomposition). |
| `classical_C2_c_blaschke_lebesgue` | O | `cov_C2_c_disk_area` | Blaschke–Lebesgue min and isodiametric max | NEW PROOF (Mathlib only): `volume (closedBall 0 (w/2)) = ofReal(πw²/4)`. Paper claims nothing here. |
| `classical_C2_reuleaux_polygon` | O | `cov_C2_reuleaux_polygon_part` | constant width and perimeter of general Reuleaux polygons | NEW PROOF: `⋂ closedBall (v i) w` is an `IsPlaneConvexBody` (general `isPlaneConvexBody_iInter`). Paper treats only the triangle. |
| `classical_C3_a` (Mukhopadhyaya, arbitrary C² oval) | N | `cov_C3_a_part` | (i) arbitrary C² simple regular oval `α` with arbitrary period T vs. the repo's ovals given by a **C³** support function with ρ>0; missing: every oval is γ_h∘φ for such h (needs α ∈ C³ at least; for a C² oval, h is only C², and ρ = 1/k need not be differentiable, so the repo's argument through ρ' does not apply); (ii) reparametrisation invariance of vertices. | For C³ 2π-periodic h with ρ>0, α = E∘γ_h satisfies **all** hypotheses of `classical_C3_a` (`IsRegularClosedC2 α (2π)`, `InjOn` from `curve_injOn`, k>0 from `signedCurvature_curve`) **and** its conclusion (4 increasing vertices in [0,2π)). The constant-curvature alternative is handled (every point is then a local extremum, pick 0, π/2, π, 3π/2). Reduction of the repo's c₁<…<c₄<c₁+2π to [0,2π) via `toIcoMod` + periodicity of k, then sorting. Paper narrower (C³ support-function ovals; stated in §1). |
| `classical_C3_a_precise` | N | `cov_C3_a_precise_part` | as C3_a | two local max and two local min of the writer's curvature at 4 pairwise distinct points of [0,2π), for α = E∘γ_h. |
| `classical_C3_a_doCarmo` (C³ curve, k' = 0) | N | `cov_C3_a_doCarmo_part` | as C3_a(ii)/(i) except the C² issue (here α is C³, but h then is C³ only after proving the support function of a C³ oval with k>0 is C³ — not in the repo) | four increasing zeros of `deriv (signedCurvature α)` in [0,2π) for α = E∘γ_h (from the extrema, `IsLocalExtr.deriv_eq_zero`). ContDiff ℝ 3 α was not proved (it needs h ∈ C⁴); the statement is the conclusion for α = E∘γ_h. |
| `classical_C3_b` (Kneser, non-convex) | O | — | everything | Paper explicitly does not claim it (§1, §9). |
| `classical_C3_remark_ellipse` | **E** (O for the paper, proved) | `cov_C3_remark_ellipse : classical_C3_remark_ellipse` | — | NEW PROOF: k(t) = ab/(b²+(a²−b²)sin²t)^{3/2} (via `sc_E` + explicit derivatives); since a≠b the map s ↦ ab/(b²+(a²−b²)s)^{3/2} is strictly monotone on [0,1], so k has a local extremum at t iff sin² does, iff sin t = 0 ∨ cos t = 0; in [0,2π) that set is {0, π/2, π, 3π/2}. |
| `classical_C3_remark_circle` | **E** (O for the paper, proved) | `cov_C3_remark_circle : classical_C3_remark_circle` | — | NEW PROOF via `FourVertex.signedCurvature_curve` for the constant support function r: k ≡ 1/r, so every t is a local extremum. |
| `classical_C3_remark_nonsimple` | O | — | — | not claimed (limaçon); not attempted. |
| obligation `supportFn_obligation` | proved | `cov_supportFn_obligation : obl_supportFn` | — | compactness + `IsCompact.exists_isMaxOn`. |
| obligation `perimeter_obligation` | open (carried) | — | existence of a simple closed boundary parametrisation of a planar convex body | not proved; no `cov_` theorem depends on it. |

D (DIFFERENT): none found. I checked each classical statement against the textbook source, looking for
statements that are false as written. None is (see notes): C2_a's `interiorAngleAt` sSup gives 2π/3 at
the corners and π at smooth points; C2_boundary's angle-sum description is the minor arc; and in
`IsReuleauxPolygonData`, the hypotheses do not force the labels to be in cyclic order. I don't think that
matters: diameter segments of a planar set pairwise intersect, so the w-cycle is the "star" order and the
body `⋂ closedBall` does not depend on the labelling. That is an argument, not a proof.

## NEW PROOFS (scratch only, no library change)
`cov_C1_a_support` (full), `cov_C3_remark_circle` (full), `cov_C3_remark_ellipse` (full), `cov_supportFn_obligation` (full),
`hasConstantWidth_E_body` (repo body has constant width in the writer's sense),
`isPlaneConvexBody_iInter` / `isPlaneConvexBody_reuleaux`, `reuleaux_not_disk`, `angle_equilateral` /
`cov_C2_boundary_part`, `cov_C2_c_disk_area`, `cov_C2_reuleaux_polygon_part`, the four-vertex transport
(`sc_E`, `hyp_part`, `four_extr`, `sort4`, `toIcoMod` reduction) behind `cov_C3_a*_part`.

## Obligations
- `supportFn_obligation`: PROVED (`cov_supportFn_obligation`).
- `perimeter_obligation`: NOT proved. No theorem depends on it; it is not used as a hypothesis anywhere.
- No construction obligation is carried as a hypothesis in any `cov_` theorem. The `_part` theorems take
  only the repo's own hypotheses (`ConstWidthSupport`, `PiecewiseConstWidth`, `ContDiff ℝ 3 h`, periodic, ρ>0, `w>0`).

## Compile
- `~/lean/l15C_fourvertex`: `~/lean/jl lake env lean scratch/L15_compare.lean` → rc=0, 0 errors, 0 warnings
  (`set_option linter.unusedVariables false` set at the top, because the writer's binders are unused in a `Prop` def).
- `~/lean/l15C_barbier`: same → rc=0, 0 errors, 0 warnings.

## Forbidden grep
`grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|\baxiom "` on both scratch files → no match (rc=1).

## #print axioms (all → [propext, Classical.choice, Quot.sound])
fourvertex: cov_supportFn_obligation, cov_C3_a_part, cov_C3_a_precise_part, cov_C3_a_doCarmo_part, cov_C3_remark_circle, cov_C3_remark_ellipse.
barbier: cov_supportFn_obligation, cov_C1_a_support, cov_C1_b_part, cov_C1_a_part, cov_C1_b_equiv_part,
isPlaneConvexBody_reuleaux, reuleaux_not_disk, cov_C2_a_part, cov_C2_b_part, cov_C2_c_disk_area,
cov_C2_reuleaux_polygon_part, cov_C2_boundary_part.

## Scratch paths
- john `~/lean/l15C_fourvertex/scratch/L15_compare.lean` sha256 d13a9ee1b5dd28377b70e2a509e67e4e560d909a9fc7c21723a51825ba00aafc
- john `~/lean/l15C_barbier/scratch/L15_compare.lean` sha256 1b0ef7dbfc6334604115333d7d5c6a16a167b36c606b915f0a6a8ced2edb531c
- copies: `<ws>/AFM/L14L15/C/L15_scratch/L15_compare_{fourvertex,barbier}.lean`
- build helpers: `/tmp/l15c/` (conv.py, body.lean, common.lean, fv_tail2.lean (= fv_tail + ell.lean), bb_tail.lean)

## Summary
E: 3 (`C1_a_support`, `C3_remark_circle`, `C3_remark_ellipse`; the last two are not claimed in the paper) + obligation `supportFn` proved.
N: 9 (`C1_a`, `C1_b`, `C1_b_equiv`, `C2_boundary`, `C2_a`, `C2_b`, `C3_a`, `C3_a_precise`, `C3_a_doCarmo`). The shared gap: the repo works with curves *given* by support functions (C² / piecewise C¹ for Barbier, C³ with ρ>0 for four-vertex) and never identifies an arbitrary convex body or curve, or the writer's `⋂ closedBall` Reuleaux triangle, with such a curve. The paper states this limitation in §1 and §9, so the paper is narrower and not wrong.
D: 0.
O: 5 (`C2_c` area, `C2_c_blaschke_lebesgue` (disk area proved), `C2_reuleaux_polygon` (convex body proved), `C3_b` Kneser, `C3_remark_nonsimple`).
