# L10 — Paper K, Layer 10: definition bridges

Host jack, repo `~/paperK`, Lean v4.33.1. Every Lean/lake call ran under `flock ~/pi.lock`. No `lake update` and no cache fetch.

## Commit

- New commit: **`bb1241aa40fe6a7c8ee70f402d8857b6b4d9218f`** `Layer 10: definition bridges` (parent `7ba9b97`)
- Author and committer are both `Josh Bald <jpbald93@gmail.com>`, set with `git -c user.name=… -c user.email=…`. No git config was changed and there is no Co-Authored-By line.
- Tree is clean after the commit (`git status --short` prints 0 lines).

## −0 evidence

```
$ git show --numstat --format= HEAD
1	0	PaperK.lean
438	0	PaperK/Bridge.lean
1	0	gate.sh
$ git diff --shortstat 7ba9b97 HEAD
 3 files changed, 440 insertions(+)
```
- `PaperK.lean`: one added line, `import PaperK.Bridge`.
- `gate.sh`: one added line, `REQUIRED="$REQUIRED …36 names…"`. The original `REQUIRED=` line is unchanged.

## Gate and tamper

- Before (at `7ba9b97`, as given): `PASS (24 declarations, standard axioms only)`
- After (at `bb1241a`): **`PASS (60 declarations, standard axioms only)`**. That is 24 + 36 bridge lemmas, each reported as `[propext, Classical.choice, Quot.sound]` or a subset of it.
- `lake build`: `Build completed successfully (8711 jobs).`
- Tamper: all 9 defects rejected (sorry, ax2line, evalfake, macro → forbidden token; wrap → nonstandard axioms; falsehyp, falsestmt, falsehyp2, falsestmt2 → build). Final line: **`ALL TAMPERING TESTS REJECTED`**.
- `PaperK/Bridge.lean` contains none of the gate's forbidden tokens.

## sha256

```
24e803518794cc2a97087f1af7dcdadd9c6567e937e847ebc422b2a2b90f27b8  PaperK/Bridge.lean
```
The file has 438 lines. A byte-identical copy is at `/tmp/afmrun/paperK/l10/Bridge.lean`.

## Conventions and sign correction

- **Euclidean points.** `ℝ × ℝ` uses the sup metric in Mathlib, so every metric bridge goes through `EuclideanSpace ℝ (Fin n)` and writes points as `!₂[x, y]`. Collinearity stays in `ℝ × ℝ`, which is where Prop 3.1 states it.
- **Orientation.** An oriented cycle with signed radius `r < 0` has no Mathlib counterpart, because `Sphere.radius` is unsigned in the tangency predicates. The bridges therefore use `⟨c, r⟩` with `r ≥ 0`, and write the opposite orientation as `circ (−r') …` (or `⟨c_Y, −r_Y⟩`).
- **Sign: the brief's "B = −(·|·)" shorthand gives the wrong sign for these statements.** Lean confirmed this, because the first draft with that sign failed to typecheck. For normalised null cycles (`v = 1`), the proved identity is
  `2·B X Y = dist(c_X, c_Y)² − (r_X − r_Y)²`.
  So for a point cycle (`r = 0`), **`B = +½ · Sphere.power`**. The equal-power constant comes out as **`Sphere.power = −B(P,P)/P₃²`**, and the minus sign appears there.

## Bridge lemmas

| # | Lemma | Local notion | Standard / Mathlib counterpart | Notes |
|---|---|---|---|---|
| 1 | `PaperK.bridge_dist_sq` | coordinate squared distance | `dist` on `EuclideanSpace ℝ (Fin 2)` | helper used by everything below |
| 2 | `PaperK.bridge_B_toLinearMap₂` | `B`, `G` | `Matrix.toLinearMap₂' ℝ G` (the Mathlib bilinear map of the Gram matrix) | |
| 3 | `PaperK.bridge_cofactor_det` | `cofactor` | `Matrix.det` of `M` with `v` prepended: `v ⬝ᵥ cofactor M = det(cons v M)` | proved by Laplace expansion (`det_succ_row_zero`) |
| 4 | `PaperK.bridge_pt` | `pt` | `pt X = (c/v)` in coordinates | **`rfl`: both sides are literally the definition (commented in source)** |
| 5 | `PaperK.bridge_pt_normalised` | `pt` at `v = 1` | the centre `(X 1, X 2)` | real proof (`simp`) |
| 6 | `PaperK.bridge_B_dist` | `B` on affine cycles | `2·B = dist(c,c')² − (r−r')²` | sign stated |
| 7 | `PaperK.bridge_B_eq_zero_iff_dist` | `B X Y = 0` | oriented tangency equation `dist² = (r−r')²` | |
| 8 | `PaperK.bridge_B_isExtTangent` | `B X Y = 0`, opposite orientation | `Sphere.IsExtTangent ⟨c_X, r_X⟩ ⟨c_Y, −r_Y⟩` | |
| 9 | `PaperK.bridge_B_isIntTangent` | `B X Y = 0`, `0 ≤ r_X ≤ r_Y` | `Sphere.IsIntTangent ⟨c_X, r_X⟩ ⟨c_Y, r_Y⟩` | |
| 10 | `PaperK.bridge_B_power` | `B` with a radius-0 cycle | `B X Y = ½ · Sphere.power ⟨c_Y, r_Y⟩ c_X` | sign stated |
| 11 | `PaperK.bridge_power_sphere` | `power p ρ Y` (Laguerre power) | `Sphere.power ⟨c_Y, ρ − r_Y⟩ p` | holds for every `Y` |
| 12 | `PaperK.bridge_power_eq_const_sphere` | equal-power constant (`power_eq_of_B_eq_zero`) | `Sphere.power ⟨c_Y, ρ−r_Y⟩ P_X = −B(P,P)/P₃²` | sign stated |
| 13 | `PaperK.bridge_power_eq_const_sphere_rho0` | the same at `P 0 = 0` | `Sphere.power ⟨c_Y, r_Y⟩ P_X = −B(P,P)/P₃²` (each cycle's own sphere) | |
| 14 | `PaperK.bridge_collinear_iff_det` | coordinate sign/determinant collinearity | `Collinear ℝ {p, q, s}` in `ℝ × ℝ` | iff, both directions |
| 15 | `PaperK2.bridge_B_eq` | `PaperK2.B` | `PaperK.B` | **`rfl`: identical bodies (commented)** |
| 16 | `PaperK2.bridge_circ_null` | `circ` | null cone `B X X = 0` (it is a Lie cycle) | |
| 17 | `PaperK2.bridge_circ_centre_radius` | `circ` | centre `pt = (a,b)`, radius slot `r`, `v = 1` | |
| 18 | `PaperK2.bridge_B_circ_dist` | `B` on `circ` | `2·B = dist² − (r−r')²` | sign stated |
| 19 | `PaperK2.bridge_circ_mem_sphere` | point-cycle orthogonality | `!₂[x,y] ∈ ⟨!₂[a,b], r⟩` (Mathlib `Sphere` membership) | |
| 20 | `PaperK2.bridge_circ_power` | `B(circ 0 x y, circ r a b)` | `½ · Sphere.power` | sign stated |
| 21 | `PaperK2.bridge_circ_isExtTangent` | `B`-orthogonality of `circ r`, `circ (−r')` | `Sphere.IsExtTangent` | |
| 22 | `PaperK2.bridge_circ_isIntTangent` | `B`-orthogonality, `0 ≤ r ≤ r'` | `Sphere.IsIntTangent` | |
| 23 | `PaperK2.bridge_pw_sphere` | `pw` | `Sphere.power ⟨(a,b), ρ − r⟩ P_X` | |
| 24 | `PaperK2.bridge_pconst_neg_B` | `pconst` | `−B(P,P)/P₃²` | sign stated |
| 25 | `PaperK2.bridge_power_eq_const_sphere` | `power_eq_const` | `Sphere.power ⟨(a,b), ρ−r⟩ P_X = −B(P,P)/P₃²` | |
| 26 | `PaperK2.bridge_power_eq_const_sphere_rho0` | the same at `P 0 = 0` | `Sphere.power ⟨(a,b), r⟩ P_X = −B(P,P)/P₃²` | |
| 27 | `PaperK2.bridge_Equi_dist` | `Equi` | equality of `dist` to three points | |
| 28 | `PaperK2.bridge_D3_collinear` | `D3 = 0` | `Collinear ℝ` of the three centres | |
| 29 | `PaperK2.bridge_Tangent` | `Tangent` | `dist² = (ρ−r)²`, and `B(circ, circ) = 0` | |
| 30 | `PaperK3.bridge_dist_sq3` | coordinate squared distance in ℝ³ | `dist` on `EuclideanSpace ℝ (Fin 3)` | helper |
| 31 | `PaperK3.bridge_B_sph_dist` | `B` on `sph` | `2·B = dist² − (r−r')²` | sign stated |
| 32 | `PaperK3.bridge_sph_mem_sphere` | point-cycle orthogonality | `Sphere` membership in ℝ³ | |
| 33 | `PaperK3.bridge_sph_power` | `B(sph 0 …, sph r …)` | `½ · Sphere.power` | sign stated |
| 34 | `PaperK3.bridge_sph_isExtTangent` | `B`-orthogonality, opposite orientation | `Sphere.IsExtTangent` | |
| 35 | `PaperK3.bridge_sph_isIntTangent` | `B`-orthogonality, `0 ≤ r ≤ r'` | `Sphere.IsIntTangent` (covers `tetra_tangent_B`'s enclosing sphere) | |
| 36 | `PaperK3.bridge_equal_power_sphere` | ℝ³ `equal_power` constant | `Sphere.power ⟨c_i, ρ−r_i⟩ P_X = −B(P,P)/P₄²` | sign stated |

- Only #4 and #15 are `rfl`, and both say so in a source comment. The other 34 are real proofs.
- One private-style helper, `PaperK.eq_iff_sq_eq`, is also in the file but is not in `REQUIRED`. It is a generic square-root lemma, not a bridge.

## Dropped (recorded gaps)

- **`Sphere.IsTangent` (sphere vs affine subspace).** This would need line cycles (`v = 0`). Paper K's affine `pt`/`circ`/`sph` machinery only handles `v ≠ 0`, so there is no local notion to bridge. Every cycle–cycle tangency is bridged through `IsExtTangent`/`IsIntTangent` instead.
- **Negative (oriented) radii.** Mathlib spheres in the tangency predicates are unoriented. Orientation is encoded by negating the radius (#8, #21, #34) rather than through a Mathlib "oriented sphere" notion, because none exists.
- **`ccx`/`ccy` vs `Affine.Simplex.circumcenter`.** Not attempted within the 15-minute cap: it needs a `Simplex` built from `D3 ≠ 0`. #27 + #28 give the metric and non-collinearity halves, so `equi_iff` already reads as "unique equidistant point of three non-collinear points". The final identification with `circumcenter` (via `eq_circumcenter_of_dist_eq`) is left open.
- **`det4`, `Mrow`, `sq`, `sqa`/`sqb`, `tetraFam`/`tetraFamR`.** These are data or direct `Matrix.det` wrappers (`det4` is literally `Matrix.det` of `Matrix.of`), so there is no separate standard notion to bridge.
- **`pt` metric in `ℝ × ℝ`.** No `dist (pt X) (pt Y)` bridge is stated, because in Mathlib that is the sup distance, not the Euclidean one. The Euclidean form is #5 + #6, with points read into `EuclideanSpace`.

## Battery pinning

- The battery (`~/leancheck/reports/paperK_20261110_171742.md`, layers 1, 2, 4–9) was measured at `7ba9b97` with 24 gate declarations. It was not re-run.
- The new commit raises the gate to 60 declarations. Quote the battery at `7ba9b97` and the gate at `bb1241a` separately.
- **Recommendation:** pin the next battery run to `bb1241a`. Its Layer 9 inventory will still under-count, because it only spots name-pattern bridges (`<notion>_eq`, `mem_<notion>_iff`); among the new names only `PaperK2.bridge_B_eq` might match.
