# L14c — Paper K, Layer 14 part 3: the five ℝ³ claims of `PaperK3`, restated in Mathlib vocabulary

Deliverable: `paperK_l14c.lean` (namespace `PaperKL14c`, `import Mathlib` only, no Paper K import, 257 lines).
It compiled on john as `~/lean/x_paperi_circles/scratch/paperK_l14c.lean` (Lean v4.33.1, the project's Mathlib).
It contains no `sorry` / `admit` / `native_decide` / `axiom` token: `grep -cE` gives 0.

## Vocabulary (all thin wrappers over Mathlib)

- `G3 : Matrix (Fin 6) (Fin 6) ℝ` (a `!![…]` literal) and `lieB3 X Y := Matrix.toLinearMap₂' ℝ G3 X Y`.
  `lieB3_apply` proves `lieB3 X Y = X0Y0 − X1Y1 − X2Y2 − X3Y3 − X4Y5 − X5Y4`, which is the body of
  `PaperK3.B` character for character. Nothing imports Paper K, so `lieB3 = PaperK3.B` is the same polynomial
  but not a Lean theorem in this file.
- `η = ![1,−1,−1,−1]`. `minkowski := Matrix.toLinearMap₂' ℝ (diagonal η)` (a `BilinForm`) and
  `lorentzQ := QuadraticMap.weightedSumSquares ℝ η` (a `QuadraticForm`). They are linked by
  `lorentzQ_apply : lorentzQ v = v0² − (v1²+v2²+v3²)` and `lorentzQ_eq_minkowski : lorentzQ v = minkowski v v`.
  `lor X := ![X0, X1, X2, X3]`.
- `sph r c` with `c : EuclideanSpace ℝ (Fin 3)` is `![r, c0, c1, c2, 1, (r² − ‖c‖²)/2]`, the same as
  `PaperK3.sph r (c 0) (c 1) (c 2)`. `pX P := !₂[P1/P4, P2/P4, P3/P4]` is the affine centre, and
  `cen X := !₂[X1, X2, X3]`.
- `tv` gives the vertices `!₂[1,1,1], !₂[1,−1,−1], !₂[−1,1,−1], !₂[−1,−1,1]`, so `sph 1 (tv i)` is
  `PaperK3.tetraFam 0 0 0 0 (Fin.castSucc i)` coordinate-for-coordinate.
- Bridges: `two_lieB3_sph : 2·B(sph r c, sph r' c') = dist c c'² − (r−r')²`. `isIntTangent_of_lieB3` and
  `isExtTangent_of_lieB3` turn `B = 0` into Mathlib's `Sphere.IsIntTangent` (same orientation, `0 ≤ r' ≤ r`)
  or `Sphere.IsExtTangent` (opposite orientation, `r ≤ 0 ≤ r'`, the sphere carried with radius `−r`).
- Geometry is stated with `dist` on `EuclideanSpace ℝ (Fin 3)`, `EuclideanGeometry.Sphere`, `Sphere.power`,
  `Sphere.IsIntTangent` and `Sphere.IsExtTangent`.

## The five rows

Every row has a full proof. None was dropped.

| # | Source | Restated as | Verdict |
|---|---|---|---|
| 1 | `PaperK3.B_self_zero_iff` | `B_self_zero_iff X : lieB3 X X = 0 ↔ lorentzQ (lor X) = 2 * X 4 * X 5`, plus `lorentzQ_eq_minkowski` | **E**. The right side is the Lorentz quadratic form (`weightedSumSquares`, equal to the `toLinearMap₂'` Minkowski form on the diagonal) of the `(r, c)` part. It is the same equation. |
| 2 | `PaperK3.tangency_identity` | `tangency_identity X Y (hX : lieB3 X X = 0) (hY : lieB3 Y Y = 0) : −2·X4·Y4·lieB3 X Y = (X0Y4 − Y0X4)² − dist (Y4 • cen X) (X4 • cen Y)²`. The normalised corollary (`X4 = Y4 = 1`) is `−2·B = (r_X−r_Y)² − dist(c_X,c_Y)²`. | **E**. The three squared differences are exactly `dist²` between the scaled centres `Y4·c_X` and `X4·c_Y`. Both null hypotheses are kept, as in the source. |
| 3 | `PaperK3.equal_power` | `equal_power X hX4 hX5 P hP hP4 i j : Sphere.power ⟨cen (X i), ρ − X i 0⟩ (pX P) = Sphere.power ⟨cen (X j), ρ − X j 0⟩ (pX P)` with `ρ = P0/P4`. The common value is `power_eq_const : … = −lieB3 P P / P4²`, and `power_const_eq_source` shows this equals the source's `‖P_X‖² − ρ² + 2·P5/P4`. | **E**. The hypotheses are the source's (`X i 4 = 1`, the `X i 5` formula, `B P (X i) = 0`, `P4 ≠ 0`), over an arbitrary `ι`. The Laguerre power `‖P_X − c_i‖² − (ρ − r_i)²` is definitionally `Sphere.power` for the radius `ρ − r_i`, and the sign of the radius is irrelevant because it is squared. The source's two forms (equality to a constant, `equal_power_pair`) are both covered. |
| 4 | `PaperK3.tetra_tangent_B` | `tetra_tangent_B i`: both source conjuncts (`lieB3 (sph (√3+1) 0) (sph 1 (tv i)) = 0` and the same with `1−√3`), plus `Sphere.IsIntTangent ⟨tv i, 1⟩ ⟨0, √3+1⟩` and `Sphere.IsExtTangent ⟨0, −(1−√3)⟩ ⟨tv i, 1⟩` | **E**. This is a strengthening: the oriented `B` facts are kept and their Mathlib meaning is added. **Sign note:** Mathlib's tangency predicates are *unsigned*. `IsExtTangent` / `IsIntTangent` force `0 ≤ radius`, so the oriented sphere of signed radius `1 − √3 < 0` can only appear as `⟨0, −(1−√3)⟩ = ⟨0, √3−1⟩`. Its opposite orientation shows up as *external* contact (`√3 = (√3−1) + 1`), while the same-orientation sphere `√3+1` shows up as *internal* contact (`√3 = (√3+1) − 1`). The Mathlib predicates cannot express orientation, so the `B` conjuncts are the only place it survives. |
| 5 | `PaperK3.tetra_thm36` | `tetra_thm36 r c P (h : ∀ i, lieB3 P (sph 1 (tv i)) = 0) (_h5 : lieB3 P (sph r c) = 0) (_hP4 : P4 ≠ 0) : pX P = 0 ∧ ∀ i : Fin 4, [B = 0 for both spheres `sph (√3±1)` centred at `pX P`] ∧ IsIntTangent ⟨tv i,1⟩ ⟨pX P, √3+1⟩ ∧ IsExtTangent ⟨pX P, √3−1⟩ ⟨tv i,1⟩ ∧ Sphere.power ⟨tv i, 1⟩ (pX P) = 2`. The companion `tetra_apollonius x ρ : (∀ i, lieB3 (sph ρ x) (sph 1 (tv i)) = 0) ↔ x = 0 ∧ (ρ = 1+√3 ∨ ρ = 1−√3)` shows these two spheres are *the* Apollonius pair. | **E** as a restatement of the Lean theorem. Mathematically it is an **E1 fact, not the source's Theorem 3.6**. What it proves is that the Apollonius pair `A₅, A₅'` of `X∖X₅` (the four unit spheres) is centred at `P_X`, and that `P_X` has equal power `2` w.r.t. all four. As in the source, the fifth sphere hypothesis `_h5` and `P4 ≠ 0` are unused: `P_X = 0` follows from the four vertex conditions alone. No hyperplane appears anywhere in the statement. |

Verdict count: **E 5, W 0, O 0, N 0**. Row 5 is E only in the sense of a faithful restatement, with the E1 caveat above.

## Naming audit: `tetra_thm36`

Source Theorem 3.6 says that, for `P_X` not at infinity, there is a sphere centred at `P_X` tangent to every
hyperplane in every `T_i`, where `T_i` is the set of (oriented) hyperplanes tangent to both Apollonius cycles
`A_i, A_i'` of `X∖X_i`. The Lean `PaperK3.tetra_thm36` mentions no hyperplanes. Its conclusion is the E1
statement that the Apollonius pair of the four tetrahedron spheres is centred at `P_X`, and it only covers
`i = 5`. The other four `T_i` are never constructed, and the fifth sphere is an unused parameter.

To make it Theorem 3.6, the statement would need four additions:

(a) **Hyperplanes as cycles at infinity.** An oriented plane `{x | n·x = h}` with `‖n‖ = 1` is the null vector
`![1, n0, n1, n2, 0, h]`, i.e. `X4 = 0`. Tangency of a plane `H` to a cycle `Y` is the same relation
`lieB3 H Y = 0`, and a lemma like `two_lieB3_sph` is needed to identify it with `n·c − h = ±r`.

(b) **The families.** For each `i : Fin 5`, the Apollonius pair `A i, A' i` of `X∖X_i` (hypotheses
`∀ j ≠ i, B (A i) (X j) = 0` and the same for `A' i`), and
`T i := {H | H 4 = 0 ∧ B H H = 0 ∧ B H (A i) = 0 ∧ B H (A' i) = 0}`.

(c) **The "not at infinity" hypotheses.** `P 4 ≠ 0` (so `P_X` is a finite point, which the current statement
already has) and `A i 4 ≠ 0`, `A' i 4 ≠ 0` (finite Apollonius cycles).

(d) **The conclusion.** `∃ ρ, ∀ i, ∀ H ∈ T i, lieB3 (sph ρ (pX P)) H = 0`.

One observation was not proved in Lean. In this tetrahedron instance `A₅, A₅'` are concentric, with radii
`√3+1` and `√3−1`, so they have no common tangent plane (oriented or not). `T₅` is therefore empty, and
Theorem 3.6's clause for `i = 5` is vacuous. The current lemma is not even a special case of the `i = 5` part
of Theorem 3.6.

**Proposed minimal rename** (not applied; `~/paperK` was not touched): `PaperK3.tetra_thm36` →
`PaperK3.tetra_E1_apollonius`. The docstring should change from "Thm 3.6 conclusion…" to "E1, regular
tetrahedron: the Apollonius pair of the four unit spheres is centred at `P_X = 0` with radii `√3 ± 1`". This
file keeps the name `tetra_thm36` only so its row lines up with the source.

## `#print axioms` (temp copy `scratch/ax_l14c_tmp.lean`, deleted afterwards)

All 29 declarations print the same three standard axioms (`grep -c` on the output gives 29; no other lines):

```
'PaperKL14c.G3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lieB3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lieB3_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.η' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.minkowski' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lorentzQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lorentzQ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lorentzQ_eq_minkowski' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.lor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.sph' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.pX' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.cen' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.dist_sq3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.two_lieB3_sph' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.isIntTangent_of_lieB3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.isExtTangent_of_lieB3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.B_self_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tangency_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tangency_identity_normalised' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.power_eq_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.equal_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.power_const_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.one_lt_sqrt3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tetra_lieB3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tetra_tangent_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tetra_PX_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tetra_apollonius' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKL14c.tetra_thm36' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Compile, hashes, repo state

- `cd ~/lean/x_paperi_circles && timeout 85 lake env lean scratch/paperK_l14c.lean` gives **rc = 0**, with no
  warnings and no output. The axioms copy also gave rc = 0.
- sha256 on john (`scratch/paperK_l14c.lean`) and locally (`paperK_l14c.lean`) are identical:
  `cd82f7313ed9ebdc0999ea324c5904f0236e2f73788576cf16b71300e44b093d`.
- `git status --short` on john prints `?? scratch/` only, so no tracked file was modified. The temp file
  `scratch/ax_l14c_tmp.lean` is deleted. `scratch/` now holds `paperK_l14_2d.lean`, `paperK_l14c.lean` and
  `probe.lean`. `paperK_l14_2d.lean` and `probe.lean` were there before this job; `paperK_l14c.lean` is this
  job's deliverable copy.
