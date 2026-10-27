# Layer 15 — Classical comparer, Paper G (Brocard), Group S

- Machine: the x86-64 machine, repo copy `~/l15_brocard` (copied from `~/paperg_brocard` without .lake/.git; packages symlinked to `~/barbier/.lake/packages`; `lake build` succeeded, 8713 jobs).
- Classical file: `PaperGClassical.lean`, sha256 `2bb545d76d505fe0db1a848362e9414fdd285239321dea37980b365755ae1b74` (prefix 2bb545d76d505fe0 matches; the x86-64 machine copy `~/PaperGClassical.lean` is identical to `/tmp/blindG15/Classical.lean`).
- Scratch file: `the x86-64 machine:~/l15_brocard/scratch/L15_compare.lean` (722 lines, sha256 `7e0af1324ccf7c8c08a4747e157c620d6061967275e90474f645d23e4413dd68`), namespace `L15CmpS`, starts with `import Brocard`. The Basic-definitions block and all 13 assigned statements were copied verbatim; only the namespace and `classical_` → `cov_` were changed, and a script checked that each copy occurs verbatim in the scratch file.
- The repository's triangle is instantiated as `t = ClassicalTri A B C h : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))`. `Fact (finrank = 2)` comes from `finrank_euclideanSpace_fin`.

## Result table

| classical | rel. | Lean theorem | what the repository lacks / what was added | note |
|---|---|---|---|---|
| S1a (symmedians concurrent at an interior point) | **E** (with a bridge) | `cov_S1a` | The repository's B1 (`symmedian_angles`) states the symmedian property as **angle equalities** ∠BAK = ∠M_aAC etc. It does not use the classical "reflection of the median in the bisector line" form, and its interior statement is "positive weights", not `interior (convexHull)`. Bridge lemmas (NEW, in scratch): `refl_vec` computes the reflection in the bisector line `line[A, ClassicalBisectorPoint]` in coordinates; `symm_mem` gives membership in `ClassicalSymmedian`; `interior_of_weights` turns positive barycentrics into membership in `interior (convexHull)`, via `AffineBasis.interior_convexHull`. | The witness is the repository's K = (a²:b²:c²). The bridge uses only the repository's coordinate lemmas (`inner_uu/vv/uv`, `gram_det_pos`, `affineCombination_vsub`). |
| S1b (every common point of the 3 symmedians is (a²:b²:c²)) | **N → completed, NEW PROOF** | `cov_S1b` | **The repository has no uniqueness statement for the symmedian concurrence point.** NEW PROOF: two symmedian lines (through A and through B) meet in exactly one point, because coordinates are unique (`Brocard.coords_eq` with Gram det > 0). That point is K. | Only the A- and B-symmedians are used; hC is unused. |
| S2a (K is the centroid of its pedal triangle) | **E** | `cov_S2a` | nothing missing | Direct: `l14_symmedianPoint_eq_centroid_pedal`. The definitions agree definitionally. |
| S2b (uniqueness, over all points of the plane) | **E** | `cov_S2b` | nothing missing | Direct: `l14_eq_symmedianPoint_of_eq_centroid_pedal` with `Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)`. Uniqueness holds over the whole plane, matching the classical AMBIGUOUS reading. |
| S3a (∃! interior Ω with ∠ΩAB = ∠ΩBC = ∠ΩCA) | **N → completed, NEW PROOF** | `cov_S3a` | Repository: existence only (explicit weights, `brocardPoint₁_angles`). **It does not prove that Ω is interior, and it has no uniqueness.** NEW: `brocard1_interior` (positive weights → interior). NEW: `brocard1_unique` — for an interior point with coordinates (y,z), x = 1−y−z > 0, equal angles ⇒ equal cotangents (`cot_angle_coords`), which gives g₁/z = g₂/x = g₃/y. Since g₁+g₂+g₃ = S/2, this forces gᵢ = (weight)·S/2, a linear system with determinant a²b²+b²c²+c²a² > 0, whose solution is the repository's Ω. | Uniqueness is proved inside the triangle only, as stated. |
| S3b (same, second point) | **N → completed, NEW PROOF** | `cov_S3b` | Same gaps as S3a. NEW: `brocard2_interior`, `brocard2_unique`. | |
| S3c (∠ΩAB = ∠Ω′BA for arbitrary interior Brocard points Ω, Ω′) | **N → completed** | `cov_S3c` | The repository states it only for its own explicit points (`brocardPoints_isogonal` + `brocardPoint₁_angles`). Transferring it to arbitrary Ω, Ω′ needs the S3a/S3b uniqueness (NEW). | |
| S3d (cot ω = cot A + cot B + cot C = (a²+b²+c²)/(4Δ)) | **N → completed** | `cov_S3d` | Repository: for its explicit Ω only (`cot_brocardAngle_eq_sum_cot`, `cot_brocardAngle_eq_div_area`). Transfer via `brocard1_unique` (NEW). | The repository's `area` and the classical `ClassicalArea` are the same formula; the repository writes ∠ABC where the classical file writes ∠CBA (`angle_comm`). |
| S3e (0 < ω ≤ π/6) | **N → completed** | `cov_S3e` | Same pattern: explicit point only (`brocardAngle_pos_le`), plus uniqueness (NEW). | |
| S4 (Ω, Ω′ isogonal conjugates; OΩ = OΩ′) | **N → completed, NEW PROOF** | `cov_S4` | (i) The repository states isogonality as **angle equalities** ∠Ω₁AB = ∠Ω₂AC etc. The classical definition (`ClassicalIsogonalConj`) asks that Ω′ lies on the reflection of line VΩ in the bisector at **each** vertex V. NEW: `isog_vertex` proves this at vertex A in coordinates. Vertices B and C follow by applying it to the rotated triangles (B,C,A) and (C,A,B), using `brocard1_unique`/`brocard2_unique` for the rotated triangle to identify Ω, Ω′ there. (ii) Equidistance is `dist_circumcenter_brocardPoint`, transferred via uniqueness. | |
| S5 (Ω, Ω′ on the circle with diameter OK) | **N → completed** | `cov_S5` | Repository `brocardCircle` (= the content of `l14_brocardCircle`) is for its explicit points; transfer via uniqueness (NEW). | K is (a²:b²:c²) in both files. |
| S6 (first Lemoine circle, for arbitrary points satisfying the incidences) | **N → completed, NEW PROOF** | `cov_S6` | The repository gives **six explicit points** (`lemoinePoints`, via `lineMap`) and proves that they satisfy the incidences (`lemoinePoints_mem`) and are equidistant from midpoint(O,K) (`lemoineCircle`). **It does not prove that a point satisfying the incidences must be that explicit point.** NEW: `meet_unique` + `lines_transverse` — a side line and a non-parallel line through K meet in at most one point (determinant ±1 ≠ 0). So each classical Pᵢ equals a repository point. | Same six points, indexed differently: P₁=L1, P₂=L0, P₃=L2, P₄=L3, P₅=L5, P₆=L4. Some classical side lines are reversed (A,C / B,A / C,B), which `Set.pair_comm` handles. Nothing is defined differently. |
| S7 (Droz-Farny) | **E** | `cov_S7` | nothing missing | Direct: `l14_drozFarny`. The six "not parallel to a side" hypotheses are identical to the repository's; side BC carries X, CA carries Y, AB carries Z, matching the repository's index 1/2/3. The classical `u ≠ 0`, `v ≠ 0` are redundant, since non-parallelism implies them (they are unused, hence linter warnings). |

No statement is **D** (different) and none is **O** (out of scope).

## NEW PROOFS (all in `scratch/L15_compare.lean`)
- `refl_vec`: coordinate formula for the reflection in the internal-bisector line through a vertex (the classical `ClassicalBisectorPoint`).
- `symm_mem`, `symm_dir`: the classical `ClassicalSymmedian` in coordinates.
- `interior_eq`, `coords_of_interior`, `interior_of_weights`: `interior (convexHull ℝ {A,B,C})` ⇔ all barycentrics positive.
- `K_vsub`: coordinates of the classical (a²:b²:c²) point from each vertex.
- **S1b uniqueness** of the symmedian concurrence point (inside `cov_S1b`).
- `brocard1_interior`, `brocard2_interior`: the repository's Brocard points are interior.
- **`brocard1_unique`, `brocard2_unique`**: uniqueness of the first and second Brocard points among interior points. These are missing from the repository and are the key to S3a–S5.
- `isog_vertex`, `indep_rot`, `hull_rot`: isogonal conjugacy in the reflected-line sense, at all three vertices.
- `meet_unique`, `lines_transverse`: uniqueness of the six Lemoine intersection points (S6).

## Checks
- Final compile: `cd ~/l15_brocard && flock ~/l15jack.lock lake env lean scratch/L15_compare.lean` → **exit code 0**. Output is in `the x86-64 machine:~/l15S_final.out`. There are only 3 unused-variable linter warnings: `hC` in `cov_S1b`, and `hu`/`hv` in `cov_S7`.
- Forbidden tokens: `grep -nE "sorry|admit|native_decide|axiom" scratch/L15_compare.lean | grep -v "#print axioms"` → no matches (grep exit 1).
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem: cov_S1a, cov_S1b, cov_S2a, cov_S2b, cov_S3a, cov_S3b, cov_S3c, cov_S3d, cov_S3e, cov_S4, cov_S5, cov_S6, cov_S7.
- Library hash (`find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | xargs sha256sum | sha256sum`):
  - before: `bf4e3546a06202ac6258d49068e13f3818909c0ff073a8a877234d605b101f33`
  - after:  `bf4e3546a06202ac6258d49068e13f3818909c0ff073a8a877234d605b101f33` (unchanged)
- No library files were edited. No `lake update` or `cache get` was run. No processes were killed. All work was done inline, without sub-agent.

## Summary
All 13 Group-S classical statements are now proved from repository results.
- Equivalent with direct transfer: S2a, S2b, S7. Equivalent with a definitional bridge: S1a.
- The repository is narrower for the remaining nine, and each gap was closed here:
  - Uniqueness of the symmedian concurrence point is missing (S1b).
  - Interior position and uniqueness of both Brocard points are missing (S3a, S3b). As a consequence, S3c, S3d, S3e and S5 hold in the repository only for its explicit points.
  - Isogonal conjugacy is stated only as angle equalities, not in the reflected-line sense (S4).
  - The six Lemoine points are not shown to be the only intersection points (S6).

The missing pieces were cheap and are proved as NEW PROOFS. No disagreement was found.
