# REPORT — Paper H, Group H1: Euler's theorem and the inequalities around it

Library `EulerIneq` (Lean 4 v4.33.1, Mathlib v4.33.1). Setting: `{V P} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]`, `t : Affine.Triangle ℝ P`, **no dimension hypothesis anywhere**. Every statement uses Mathlib's own `t.circumcenter`, `t.circumradius`, `t.incenter`, `t.inradius`, `t.excenter {i}`, `t.exradius {i}`, `t.centroid` and `t.orthocenter`. Side lengths are `dist`s. The only new definitions are `EulerIneq.area` (`½·AB·AC·sin∠BAC`) and `EulerIneq.semiperimeter` (EulerIneq/Basic.lean).

**Mathlib check:** the pinned Mathlib has no Euler distance formula, no `R ≥ 2r` and none of the other results below, so nothing is duplicated. Mathlib facts used: the excentre weight API, `dist_affineCombination`, `orthocenter_eq_smul_vsub_vadd_circumcenter`, the law of sines, and the altitude/height lemmas.

**Numerics:** every identity and inequality was checked first with mpmath at 30 digits on 2000 random triangles, including obtuse and near-degenerate ones (scripts/numerics.py). The maximum relative residual was 9e-14.

## Theorems (all PROVED, no open items)

### H1.1 Euler's theorem — `EulerIneq.euler` — proved: **Y** — EulerIneq/Main.lean:22
```lean
theorem euler (t : Affine.Triangle ℝ P) :
    dist t.incenter t.circumcenter ^ 2 = t.circumradius ^ 2 - 2 * t.circumradius * t.inradius
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.2 Euler's inequality — `EulerIneq.euler_inequality` — proved: **Y** — EulerIneq/Main.lean:73
```lean
theorem euler_inequality (t : Affine.Triangle ℝ P) : 2 * t.inradius ≤ t.circumradius
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.2 equality case — `EulerIneq.euler_inequality_eq_iff` — proved: **Y** — EulerIneq/Main.lean:91
```lean
theorem euler_inequality_eq_iff (t : Affine.Triangle ℝ P) :
    2 * t.inradius = t.circumradius ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.3 Euler for the excircles — `EulerIneq.euler_excenter` — proved: **Y** — EulerIneq/Main.lean:117
```lean
theorem euler_excenter (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (t.excenter {i}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {i}
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.4 Weitzenböck — `EulerIneq.weitzenboeck` — proved: **Y** — EulerIneq/Main.lean:236
```lean
theorem weitzenboeck (t : Affine.Triangle ℝ P) :
    4 * √3 * area t ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.4 Weitzenböck equality — `EulerIneq.weitzenboeck_eq_iff` — proved: **Y** — EulerIneq/Main.lean:246
```lean
theorem weitzenboeck_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * area t =
        dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.4 Hadwiger–Finsler — `EulerIneq.hadwiger_finsler` — proved: **Y** — EulerIneq/Main.lean:183
```lean
theorem hadwiger_finsler (t : Affine.Triangle ℝ P) :
    4 * √3 * area t + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.4 Hadwiger–Finsler equality — `EulerIneq.hadwiger_finsler_eq_iff` — proved: **Y** — EulerIneq/Main.lean:203
```lean
theorem hadwiger_finsler_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * area t + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 =
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.5 Gerretsen — `EulerIneq.gerretsen` — proved: **Y** — EulerIneq/Main.lean:329
```lean
theorem gerretsen (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤ semiperimeter t ^ 2 ∧
      semiperimeter t ^ 2 ≤
        4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.6 OG² — `EulerIneq.dist_circumcenter_centroid_sq` — proved: **Y** — EulerIneq/Main.lean:349
```lean
theorem dist_circumcenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.centroid ^ 2 =
      t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 9
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.6 OH² — `EulerIneq.dist_circumcenter_orthocenter_sq` — proved: **Y** — EulerIneq/Main.lean:358
```lean
theorem dist_circumcenter_orthocenter_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2)
```
Axioms: `[propext, Classical.choice, Quot.sound]`

### H1.6 IG² — `EulerIneq.dist_incenter_centroid_sq` — proved: **Y** — EulerIneq/Main.lean:370
```lean
theorem dist_incenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.incenter t.centroid ^ 2 =
      (semiperimeter t ^ 2 + 5 * t.inradius ^ 2 - 16 * t.circumradius * t.inradius) / 9
```
Axioms: `[propext, Classical.choice, Quot.sound]`

Notation: `t.points 0,1,2 = A,B,C`, so `dist (t.points 1) (t.points 2) = a`, `dist (t.points 2) (t.points 0) = b` and `dist (t.points 0) (t.points 1) = c`. "Equilateral" is stated as `dist A B = dist B C ∧ dist B C = dist C A`. In H1.6 the verified incentre–centroid formula is `IG² = (s² + 5r² − 16Rr)/9`.

## Bridges (EulerIneq/Bridges.lean, all proved, standard axioms)
`gram`, `sideLen` (+ simp lemmas), `side_pos`, `height_sq_mul` and `circumradius_sq_mul` (adapted from the Blundon development), `two_mul_area_sq` (Heron), `area_nonneg`, `area_pos`, `height_mul_sideLen` (`hᵢaᵢ = 2Δ`), `four_mul_circumradius_mul_area` (`4RΔ = abc`), `excenterWeightsUnnorm_eq`, `excenterWeights_eq` (Mathlib's excentre weights = `(±a : ±b : ±c)`), `exradius_eq`, `incenter_weights`, `inradius_eq`, `inradius_mul`, `sum_signed_sideLen_pos`, `triangle_pos`, `centroid_eq_affineCombination`. The barycentric distance lemmas, proved once and reused for H1.1, H1.3 and H1.6: `dist_affineCombination_sq` (Leibniz with an arbitrary point), `dist_affineCombination_circumcenter_sq` (`|ΣwᵢPᵢ − O|² = R² − Σ_{i<j} wᵢwⱼ|PᵢPⱼ|²`) and `dist_affineCombination_affineCombination_sq`.

Auxiliary lemmas in Main.lean: `four_mul_area_mul_circumradius_sub` (`4Δ(R−2r) = ½Σ(−a+b+c)(b−c)²`), `hf_identity`, `hf_L_nonneg`, `core_identity` (Blundon's certificate, copied with attribution), `fundamental_quartic`, `eq_zero_of_pos_mul_sq`, `sum_three_eq_zero`.

## Open items
None. No `Open.lean` was needed.

## Gate
`flock ~/l15jack.lock bash gate.sh` with REQUIRED = all 46 declarations (every main theorem, definition, bridge and auxiliary lemma, fully qualified):
```
PASS (46 declarations, standard axioms only)
```

## Tamper
`flock ~/l15jack.lock bash tests/tamper.sh`:
```
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: EulerIneq.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
Deviation: the brief asks `falsehyp` to drop a needed hypothesis from a main theorem, but every main theorem's only hypothesis is `t : Affine.Triangle`. So `falsehyp` drops `(hw : ∑ i, w i = 1)` from the barycentric distance lemma `dist_affineCombination_circumcenter_sq`, through which `euler`, `euler_excenter` and `dist_circumcenter_centroid_sq` are proved. `falsehyp2` does the same for `dist_affineCombination_affineCombination_sq`. `falsestmt` changes Euler's theorem to `R² − 3Rr`. All three fail at the build stage, as required.

## Size
Lean: EulerIneq.lean 3 + Basic 32 + Bridges 330 + Main 402 = **767 lines**.
