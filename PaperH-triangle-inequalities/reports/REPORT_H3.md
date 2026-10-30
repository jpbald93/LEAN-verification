# REPORT — Paper H, Group H3: Pedoe, Ptolemy, Kooi and the extremal problems

Repository: library `EulerIneq` (H1 is preserved as commit "H1 complete"; H3 adds `EulerIneq/Pedoe.lean`,
`EulerIneq/Ptolemy.lean`, `EulerIneq/Kooi.lean`, `EulerIneq/Extremal.lean`, one import line each in
`EulerIneq.lean`, 14 new REQUIRED names in `gate.sh`, and tamper case `falsehyp3`). No existing statement
was changed. Setting: `t : Affine.Triangle ℝ P` (and `t' : Affine.Triangle ℝ P'` for Pedoe), any real inner
product spaces, with Mathlib's `circumradius`, `inradius` and `centroid`. `area` and `semiperimeter` come
from H1.

## Summary
| Item | Lean name | Proved |
|---|---|---|
| H3.1 Neuberg–Pedoe inequality | `EulerIneq.pedoe` | Y |
| H3.1 equality iff similar | `EulerIneq.pedoe_eq_iff` | Y |
| H3.2 Ptolemy's inequality | `EulerIneq.ptolemy_inequality` | Y (already in Mathlib as `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`; restated) |
| H3.2 stretch: the equality case | — | not attempted |
| H3.3 Kooi | `EulerIneq.kooi` (+ `kooi_le_gerretsen`) | Y |
| H3.4 (i) Leibniz minimum + equality iff centroid | `EulerIneq.leibniz_min`, `leibniz_min_eq_iff` | Y |
| H3.4 (ii) isoperimetric + equality iff equilateral | `EulerIneq.isoperimetric`, `isoperimetric_eq_iff` | Y |
| H3.4 (iii) optional cross-check | `EulerIneq.gerretsen_cross_check` | Y. It proves only `(R−r)(R−2r) ≥ 0`, see below |

**Open items: none** (no `sorry` anywhere, so there is no `Open.lean`).

## Routes
* **Pedoe:** an explicit sum-of-squares certificate in `a², b², c², a'², b'², c'², Δ, Δ'`, valid modulo Heron
  for both triangles: `2ST(L − 16ΔΔ') = (4TΔ − 4SΔ')² + 2Σ(T a² − S a'²)²`, where `S = Σa²` and `T = Σa'²`.
  It gives both the inequality and the equality case (all squares vanish, so `k = √(T/S)`). No Lorentzian
  Cauchy–Schwarz step was needed.
* **Ptolemy:** Mathlib's inversion proof, in any real inner product space.
* **Kooi:** H1's fundamental quartic `f(s²) ≤ 0`, plus the identity
  `M² − (2(2R−r)(u−B))² = (r(R−2r)(4R+r))² − 4(2R−r)² f(u)` with `M = (R−2r)(8R²−12Rr+r²) ≥ 0` (uses `R ≥ 2r`).
  **Numerically, equality holds only for the equilateral triangle** (isosceles scan: zero only at apex π/3;
  2-D grid minimum at the equilateral apex). Algebraically, `f(K) = r²(R−2r)²(4R+r)²/(4(2R−r)²)`, which is 0
  iff `R = 2r`.
* **Leibniz:** H1's barycentric distance formula with the centroid weights gives
  `ΣXAᵢ² = 3XG² + Σa²/3`.
* **Isoperimetric:** Heron, then AM–GM via `(x+y+z)³ − 27xyz = ½(x+y+z)Σ(x−y)² + 3Σx(y−z)²`.
* **Cross-check (iii):** Gerretsen's two bounds give only `(R−r)(R−2r) ≥ 0`. They do not exclude `R ≤ r`, so
  Euler's inequality does **not** follow from Gerretsen alone. The theorem states exactly what does follow.

## Statements (exact Lean)
### pedoe_identity — EulerIneq/Pedoe.lean:28
```lean
theorem pedoe_identity {a b c a' b' c' D D' : ℝ} (hD : (2 * D) ^ 2 = gram a b c)
    (hD' : (2 * D') ^ 2 = gram a' b' c') :
    2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a' ^ 2 + b' ^ 2 + c' ^ 2) *
        (a' ^ 2 * (b ^ 2 + c ^ 2 - a ^ 2) + b' ^ 2 * (c ^ 2 + a ^ 2 - b ^ 2) +
          c' ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) - 16 * D * D') =
      (4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) * D - 4 * (a ^ 2 + b ^ 2 + c ^ 2) * D') ^ 2 +
        2 * (((a' ^ 2 + b' ^ 2 + c' ^ 2) * a ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * a' ^ 2) ^ 2 +
          ((a' ^ 2 + b' ^ 2 + c' ^ 2) * b ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * b' ^ 2) ^ 2 +
          ((a' ^ 2 + b' ^ 2 + c' ^ 2) * c ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * c' ^ 2) ^ 2)
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### pedoe — EulerIneq/Pedoe.lean:43
```lean
theorem pedoe (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * area t * area t' ≤
      dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 +
          dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2)
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### pedoe_eq_iff — EulerIneq/Pedoe.lean:75
```lean
theorem pedoe_eq_iff (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 +
          dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) =
      16 * area t * area t' ↔
    ∃ k : ℝ, 0 < k ∧ dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧
      dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧
      dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1)
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### ptolemy_inequality — EulerIneq/Ptolemy.lean:20
```lean
theorem ptolemy_inequality (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### kooi_of_quartic — EulerIneq/Kooi.lean:22
```lean
theorem kooi_of_quartic {R r u : ℝ} (hr : 0 < r) (hR : 2 * r ≤ R)
    (hq : u ^ 2 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * u + r * (4 * R + r) ^ 3 ≤ 0) :
    u ≤ R * (4 * R + r) ^ 2 / (2 * (2 * R - r))
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### kooi — EulerIneq/Kooi.lean:46
```lean
theorem kooi (t : Affine.Triangle ℝ P) :
    semiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius))
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### kooi_le_gerretsen — EulerIneq/Kooi.lean:54
```lean
theorem kooi_le_gerretsen (t : Affine.Triangle ℝ P) :
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### leibniz_relation — EulerIneq/Extremal.lean:23
```lean
theorem leibniz_relation (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
      3 * dist X t.centroid ^ 2 + (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### leibniz_min — EulerIneq/Extremal.lean:35
```lean
theorem leibniz_min (t : Affine.Triangle ℝ P) (X : P) :
    (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2) / 3 ≤
      dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### leibniz_min_eq_iff — EulerIneq/Extremal.lean:42
```lean
theorem leibniz_min_eq_iff (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
        (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) / 3 ↔
      X = t.centroid
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### amgm_three — EulerIneq/Extremal.lean:56
```lean
theorem amgm_three {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### isoperimetric — EulerIneq/Extremal.lean:65
```lean
theorem isoperimetric (t : Affine.Triangle ℝ P) :
    12 * Real.sqrt 3 * area t ≤
      (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1)) ^ 2
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### isoperimetric_eq_iff — EulerIneq/Extremal.lean:93
```lean
theorem isoperimetric_eq_iff (t : Affine.Triangle ℝ P) :
    12 * Real.sqrt 3 * area t =
        (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
          dist (t.points 0) (t.points 1)) ^ 2 ↔
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) ∧
        dist (t.points 2) (t.points 0) = dist (t.points 0) (t.points 1)
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

### gerretsen_cross_check — EulerIneq/Extremal.lean:153
```lean
theorem gerretsen_cross_check (t : Affine.Triangle ℝ P) :
    0 ≤ (t.circumradius - t.inradius) * (t.circumradius - 2 * t.inradius)
```
Proved: **Y**. Axioms: `[propext, Classical.choice, Quot.sound]`

## Checks
* Numerical sanity: `scripts/numerics_h3.py` (mpmath 30 digits, 3000 samples: generic, obtuse and
  near-degenerate triangles, and independent pairs for Pedoe). All inequalities hold. Pedoe is an
  equality for scaled copies (residual 2e-27).
* Certificates: `scripts/certs_h3.py` (sympy). Pedoe residual is 0; Kooi factorisations as stated.
* Gate: `PASS (60 declarations, standard axioms only)`. That is H1's 46 plus 14 new ones: every main
  theorem, plus the helper lemmas `pedoe_identity`, `kooi_of_quartic`, `leibniz_relation`, `amgm_three`.
  No new definitions or bridges were needed; H3 reuses H1's bridges, which are already in REQUIRED.
* Tamper: `ALL TAMPERING TESTS REJECTED` (9 tests; new `falsehyp3` drops Heron's hypothesis
  `hD'` from `pedoe_identity`, which gives `FAIL: build`).
* Lines: H3 Lean files 388 lines; whole library 1159 lines.

## Note
The falsehyp case was first planned for `hR : 2r ≤ R` in `kooi_of_quartic`. A random search found no
counterexample to that statement without `hR` (the proof uses it, but it may be redundant), so the tamper
case uses Pedoe's Heron hypothesis instead, which is certainly needed.
