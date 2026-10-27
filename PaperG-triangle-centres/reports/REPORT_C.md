
---

# REPORT — Paper G, Group C: Extensions (de Longchamps point, anticomplementary triangle, medial Nagel point, Spieker radical centre)

New file `NagelLine/Extensions.lean` (362 lines), imported from `NagelLine.lean` with one line.
Other changes: REQUIRED in `gate.sh` was extended by 29 names. `tests/tamper.sh` gained the
`falsehyp_ext` case. README got an "Extensions" section and PROGRESS/REPORT were appended. No
existing statement or proof was modified. The only hypothesis of every new theorem is
`t : Affine.Triangle ℝ P`, and there is no dimension assumption.

## Definitions
- `Affine.Triangle.deLongchampsPoint t := (2 : ℝ) • (t.circumcenter -ᵥ t.orthocenter) +ᵥ t.orthocenter` (Extensions.lean:24)
- `Affine.Triangle.anticomplementary t : Triangle ℝ P := t.map (homothety (Finset.univ.centroid ℝ t.points) (-2 : ℝ)) (homothety_injective _ (by norm_num))` (Extensions.lean:30)
  This is a genuine `Triangle`. Its vertices are `B+C−A, C+A−B, A+B−C`, proved in `anticomplementary_points_zero/one/two`.

## Main theorems — every one: proved Y, axioms: [propext, Classical.choice, Quot.sound]

| # | Exact Lean statement (namespace `NagelLine`) | Proved | file:line |
|---|---|---|---|
| C1 | `theorem midpoint_orthocenter_deLongchampsPoint (t : Triangle ℝ P) : midpoint ℝ t.orthocenter t.deLongchampsPoint = t.circumcenter` | Y | NagelLine/Extensions.lean:228 |
| C1 | `theorem collinear_deLongchampsPoint_circumcenter_orthocenter (t : Triangle ℝ P) : Collinear ℝ {t.deLongchampsPoint, t.circumcenter, t.orthocenter}` | Y | Extensions.lean:237 |
| C1 | `theorem collinear_centroid_circumcenter_deLongchampsPoint (t : Triangle ℝ P) : Collinear ℝ {Finset.univ.centroid ℝ t.points, t.circumcenter, t.deLongchampsPoint}` | Y | Extensions.lean:249 |
| C1 | `theorem anticomplementary_orthocenter (t : Triangle ℝ P) : t.anticomplementary.orthocenter = t.deLongchampsPoint` | Y | Extensions.lean:261 |
| C2 | `theorem medial_nagelPoint (t : Triangle ℝ P) : Triangle.nagelPoint t.medial = t.incenter` | Y | Extensions.lean:274 |
| C2 | `theorem midpoint_touchpoint_zero (t : Triangle ℝ P) : midpoint ℝ (t.touchpoint ∅ 0) (t.touchpoint {0} 0) = midpoint ℝ (t.points 1) (t.points 2)` | Y | Extensions.lean:297 |
| C2 | `theorem midpoint_touchpoint_one (t : Triangle ℝ P) : midpoint ℝ (t.touchpoint ∅ 1) (t.touchpoint {1} 1) = midpoint ℝ (t.points 2) (t.points 0)` | Y | Extensions.lean:308 |
| C2 | `theorem midpoint_touchpoint_two (t : Triangle ℝ P) : midpoint ℝ (t.touchpoint ∅ 2) (t.touchpoint {2} 2) = midpoint ℝ (t.points 0) (t.points 1)` | Y | Extensions.lean:319 |
| C3 | `theorem nagelPoint_eq_anticomplementary_incenter (t : Triangle ℝ P) : t.nagelPoint = t.anticomplementary.incenter` | Y | Extensions.lean:332 |
| C4 | `theorem spiekerCenter_power_exsphere (t : Triangle ℝ P) (i j : Fin 3) : dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 = dist t.spiekerCenter (t.exsphere {j}).center ^ 2 - t.exradius {j} ^ 2` | Y | Extensions.lean:357 |
| C4 value | `theorem spiekerCenter_power_exsphere_eq (i : Fin 3) : dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 = (semiperimeter t ^ 2 + (semiperimeter t - sideA t) * (semiperimeter t - sideB t) * (semiperimeter t - sideC t) / semiperimeter t) / 4` | Y | Extensions.lean:201 |

Notes on how the statements were written:
- C2 uses `Triangle.nagelPoint t.medial` rather than `t.medial.nagelPoint`. `Simplex.medial` returns a `Simplex ℝ P 2`, so
  field notation looks for `Affine.Simplex.nagelPoint` and fails. The term is the same.
- C3: the brief said to prove the anticomplementary triangle is a Triangle. This holds by construction: it is defined as a value of type
  `Triangle ℝ P` via `Simplex.map` and an injective homothety.
- C4: the brief asked for equal power for i = 0, 1, 2. It is stated for all `i j : Fin 3`, and the common value
  `(s² + r²)/4` is proved as well.

## Bridge lemmas — all proved, axioms [propext, Classical.choice, Quot.sound]
`anticomplementary_points` (57), `anticomplementary_points_zero/one/two` (63/71/79), `centroid_anticomplementary` (86),
`anticomplementary_medial : t.anticomplementary.medial = t` (93), `orthocenter_vsub_circumcenter` (104),
`deLongchampsPoint_vsub_circumcenter` (108), `anticomplementary_circumcenter : t.anticomplementary.circumcenter = t.orthocenter` (116),
`dist_sq_of_vsub` (145), `sum_excenterWeightsUnnorm_singleton` (160), `exradius_singleton_sq` (172),
`excenter_singleton_vsub_zero` (181), `spiekerCenter_vsub_zero` (189), plus the helpers `norm_comb_sq` (41) and
`midpoint_lineMap_lineMap` (47). All line numbers refer to Extensions.lean.

## Open items
None. Every target C1–C4, including the C4 stretch goal, is proved. No `Open.lean` was created.

## Gate
`PASS (77 declarations, standard axioms only)` (48 original + 29 new).

## Tamper
`ALL TAMPERING TESTS REJECTED` (7 cases: sorry, ax2line, evalfake, macro → FAIL: forbidden token; wrap → FAIL: nonstandard axioms;
falsehyp, falsehyp_ext → FAIL: build). falsehyp_ext removes `(t : Triangle ℝ P)` from `spiekerCenter_power_exsphere`.

## Size
Basic.lean 285, Main.lean 414, Extensions.lean 362, root 3 = 1064 lines in total (Extensions adds 362 lines plus 1 import line).

## Method
mpmath numerical scout (30 digits, max error 2e-25). The anticomplementary triangle is built as a homothety image of `t`, so
centroid, medial and span facts come from Mathlib's `map` lemmas. The circumcentre is handled by `eq_circumcenter_of_dist_eq`.
The remaining identities are A-based barycentric coordinates closed by Ravi substitution plus `field_simp; ring` / `match_scalars`.
