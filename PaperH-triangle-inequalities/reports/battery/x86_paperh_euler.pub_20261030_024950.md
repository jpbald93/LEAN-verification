# leancheck — paperh_euler.pub (2026-10-30 02:49 UTC)

- path: ~/paperh_euler.pub
- HEAD: 0c95102c792b8d47d2720f4e9fbc39aa5f21a424
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'EulerIneq.Classical.cov_P1_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerIneq.Classical.cov_P1_false' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (243 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: EulerIneq.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (x86-64 machine)

Generated 2026-10-30 03:49 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 177, "mut": 503, "killed": 497, "surv": 6, "tout": 2, "contra": 0, "sat": 74, "unres": 103, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## paperh_euler.pub
- theorems: 177
- step 1 mutants: 503 | killed 495 | killed-timeout 2 | SURVIVED 6 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 16 | no-hyp 161 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 74 | unresolved 103 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: own proof compiled; downstream errors at lines [51]
  - SURVIVOR `kooi_of_quartic` [lit4->5@14]: `u ≤ R * (4 * R + r) ^ 2 / (2 * (2 * R - r))` -> `u ≤ R * (5 * R + r) ^ 2 / (2 * (2 * R - r))`
  - SURVIVED detail: 
  - SURVIVOR `kooi_le_gerretsen` [lit2->3@71]: `t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t` -> `t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (3 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t`
  - SURVIVED detail: own proof compiled; downstream errors at lines [276]
  - SURVIVOR `l14_sqrt3_lt` [lit7->8@6]: `√3 < 7 / 4` -> `√3 < 8 / 4`
  - SURVIVED detail: 
  - SURVIVOR `l14w_pedoe` [eq->ne@208]: `∃ t t' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    t'.points = ![!₂[0, 0], !₂[1, 0], !₂[0, 1]] ∧
    (¬ ∃ k` -> `∃ t t' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    t'.points = ![!₂[0, 0], !₂[1, 0], !₂[0, 1]] ∧
    (¬ ∃ k`
  - SURVIVED detail: 
  - SURVIVOR `l14w_pedoe` [lt->ge@169]: `∃ t t' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    t'.points = ![!₂[0, 0], !₂[1, 0], !₂[0, 1]] ∧
    (¬ ∃ k` -> `∃ t t' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    t'.points = ![!₂[0, 0], !₂[1, 0], !₂[0, 1]] ∧
    (¬ ∃ k`
  - SURVIVED detail: own proof compiled; downstream errors at lines [199, 232]
  - SURVIVOR `hf_L_nonneg` [lit2->3@9]: `0 ≤ 2 * (dist (t.points 1) (t.points 2) * dist (t.points 2) (t.points 0) +
          dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1) +
         ` -> `0 ≤ 3 * (dist (t.points 1) (t.points 2) * dist (t.points 2) (t.points 0) +
          dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1) +
         `
  - killed by timeout `core_identity` [lit3->4@19] (heartbeat limit)
  - killed by timeout `core_identity` [lit2->3@32] (heartbeat limit)
  - needs manual satisfiability check: `sideLen_one` (unresolved)
  - needs manual satisfiability check: `sideLen_zero` (unresolved)
  - needs manual satisfiability check: `sideLen_two` (unresolved)
  - needs manual satisfiability check: `side_pos` (unresolved)
  - needs manual satisfiability check: `height_sq_mul` (unresolved)
  - needs manual satisfiability check: `circumradius_sq_mul` (unresolved)
  - needs manual satisfiability check: `two_mul_area_sq` (unresolved)
  - needs manual satisfiability check: `area_nonneg` (unresolved)
  - needs manual satisfiability check: `height_mul_sideLen` (unresolved)
  - needs manual satisfiability check: `area_pos` (unresolved)
  - needs manual satisfiability check: `four_mul_circumradius_mul_area` (unresolved)
  - needs manual satisfiability check: `excenterWeightsUnnorm_eq` (unresolved)
  - needs manual satisfiability check: `excenterWeights_eq` (unresolved)
  - needs manual satisfiability check: `exradius_eq` (unresolved)
  - needs manual satisfiability check: `incenter_weights` (unresolved)
  - needs manual satisfiability check: `inradius_eq` (unresolved)
  - needs manual satisfiability check: `sum_signed_sideLen_pos` (unresolved)
  - needs manual satisfiability check: `dist_affineCombination_circumcenter_sq` (unresolved)
  - needs manual satisfiability check: `centroid_eq_affineCombination` (unresolved)
  - needs manual satisfiability check: `triangle_pos` (unresolved)
  - needs manual satisfiability check: `inradius_mul` (unresolved)
  - needs manual satisfiability check: `leibniz_relation` (unresolved)
  - needs manual satisfiability check: `leibniz_min` (unresolved)
  - needs manual satisfiability check: `leibniz_min_eq_iff` (unresolved)
  - needs manual satisfiability check: `isoperimetric` (unresolved)
  - needs manual satisfiability check: `isoperimetric_eq_iff` (unresolved)
  - needs manual satisfiability check: `gerretsen_cross_check` (unresolved)
  - needs manual satisfiability check: `kooi_of_quartic` (unresolved)
  - needs manual satisfiability check: `kooi` (unresolved)
  - needs manual satisfiability check: `kooi_le_gerretsen` (unresolved)
  - needs manual satisfiability check: `agree_area` (unresolved)
  - needs manual satisfiability check: `agree_semiperimeter` (unresolved)
  - needs manual satisfiability check: `agree_centroid` (unresolved)
  - needs manual satisfiability check: `agree_equilateral` (unresolved)
  - needs manual satisfiability check: `agree_equilateral'` (unresolved)
  - needs manual satisfiability check: `l14_euler` (unresolved)
  - needs manual satisfiability check: `l14_euler_inequality` (unresolved)
  - needs manual satisfiability check: `l14_euler_inequality_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_euler_excenter` (unresolved)
  - needs manual satisfiability check: `l14_dist_circumcenter_centroid_sq` (unresolved)
  - needs manual satisfiability check: `l14_dist_circumcenter_orthocenter_sq` (unresolved)
  - needs manual satisfiability check: `l14_dist_incenter_centroid_sq` (unresolved)
  - needs manual satisfiability check: `l14_fundamental_quartic` (unresolved)
  - needs manual satisfiability check: `l14_gerretsen` (unresolved)
  - needs manual satisfiability check: `l14_kooi` (unresolved)
  - needs manual satisfiability check: `l14_kooi_le_gerretsen` (unresolved)
  - needs manual satisfiability check: `l14_weitzenboeck` (unresolved)
  - needs manual satisfiability check: `l14_weitzenboeck_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_hadwiger_finsler` (unresolved)
  - needs manual satisfiability check: `l14_hadwiger_finsler_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_isoperimetric` (unresolved)
  - needs manual satisfiability check: `l14_isoperimetric_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_leibniz_relation` (unresolved)
  - needs manual satisfiability check: `l14_leibniz_min` (unresolved)
  - needs manual satisfiability check: `l14_leibniz_min_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_pedoe` (unresolved)
  - needs manual satisfiability check: `l14_pedoe_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_dist` (unresolved)
  - needs manual satisfiability check: `l14_not_collinear` (unresolved)
  - needs manual satisfiability check: `l14_ne` (unresolved)
  - needs manual satisfiability check: `cov_E1` (unresolved)
  - needs manual satisfiability check: `cov_E2a` (unresolved)
  - needs manual satisfiability check: `cov_E2b` (unresolved)
  - needs manual satisfiability check: `cov_E3` (unresolved)
  - needs manual satisfiability check: `cov_E4a` (unresolved)
  - needs manual satisfiability check: `cov_E4b` (unresolved)
  - needs manual satisfiability check: `cov_E4c` (unresolved)
  - needs manual satisfiability check: `cov_E5` (unresolved)
  - needs manual satisfiability check: `cov_E6a` (unresolved)
  - needs manual satisfiability check: `cov_E6b` (unresolved)
  - needs manual satisfiability check: `cov_E7` (unresolved)
  - needs manual satisfiability check: `cov_E8a` (unresolved)
  - needs manual satisfiability check: `cov_E8b` (unresolved)
  - needs manual satisfiability check: `cov_E9a` (unresolved)
  - needs manual satisfiability check: `cov_E9b` (unresolved)
  - needs manual satisfiability check: `cov_E10a` (unresolved)
  - needs manual satisfiability check: `cov_E10b` (unresolved)
  - needs manual satisfiability check: `cov_E11a` (unresolved)
  - needs manual satisfiability check: `cov_E11b` (unresolved)
  - needs manual satisfiability check: `cov_E12a` (unresolved)
  - needs manual satisfiability check: `cov_E12b` (unresolved)
  - needs manual satisfiability check: `euler` (unresolved)
  - needs manual satisfiability check: `four_mul_area_mul_circumradius_sub` (unresolved)
  - needs manual satisfiability check: `euler_inequality` (unresolved)
  - needs manual satisfiability check: `eq_zero_of_pos_mul_sq` (unresolved)
  - needs manual satisfiability check: `sum_three_eq_zero` (unresolved)
  - needs manual satisfiability check: `euler_inequality_eq_iff` (unresolved)
  - needs manual satisfiability check: `euler_excenter` (unresolved)
  - needs manual satisfiability check: `hf_identity` (unresolved)
  - needs manual satisfiability check: `hf_L_nonneg` (unresolved)
  - needs manual satisfiability check: `hadwiger_finsler` (unresolved)
  - needs manual satisfiability check: `hadwiger_finsler_eq_iff` (unresolved)
  - needs manual satisfiability check: `weitzenboeck` (unresolved)
  - needs manual satisfiability check: `weitzenboeck_eq_iff` (unresolved)
  - needs manual satisfiability check: `core_identity` (unresolved)
  - needs manual satisfiability check: `fundamental_quartic` (unresolved)
  - needs manual satisfiability check: `gerretsen` (unresolved)
  - needs manual satisfiability check: `dist_circumcenter_centroid_sq` (unresolved)
  - needs manual satisfiability check: `dist_circumcenter_orthocenter_sq` (unresolved)
  - needs manual satisfiability check: `dist_incenter_centroid_sq` (unresolved)
  - needs manual satisfiability check: `pedoe` (unresolved)
  - needs manual satisfiability check: `pedoe_identity` (unresolved)
  - needs manual satisfiability check: `pedoe_eq_iff` (unresolved)
  - no mutants generated (manual look): br_1, br_10, br_11_12, br_13, br_14, br_15, br_16, br_17, br_18, br_19, br_2, br_20, br_21, br_22, br_23, br_24, br_25, br_26, br_27, br_3, br_456, br_7, br_8, br_9, rb_1, rb_10, rb_11, rb_12, rb_13, rb_14, rb_15, rb_16, rb_17, rb_18, rb_19, rb_2, rb_20, rb_21, rb_22, rb_23

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 33 | UNUSED 0 | NEEDED 33 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 9 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (243 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 9 of 9 files ok |
| conclusion mutations (layer 4) | **497/503 rejected** (495 by error, 2 by timeout/heartbeat); 6 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 16 probed ok — no-hyp 161 |
| satisfiability (layer 8) | 74/177 certified [3 with hypotheses, 5 hypothesis-free binders, 66 closed], 103 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 74/177 credited, 103 unresolved |
| hypothesis ablation (layer 6) | 33 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 9 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 64 notions, 0 has-bridge, 64 NO-BRIDGE (see inventory.md) |

mutation survivors (classify by hand): `kooi_of_quartic` [lit4->5@14] own proof compiled; downstream errors at lines [51]; `kooi_le_gerretsen` [lit2->3@71] ; `l14_sqrt3_lt` [lit7->8@6] own proof compiled; downstream errors at lines [276]; `l14w_pedoe` [eq->ne@208] ; `l14w_pedoe` [lt->ge@169] ; `hf_L_nonneg` [lit2->3@9] own proof compiled; downstream errors at lines [199, 232]

satisfiability not certified (recorded as unresolved, not success): `sideLen_one` (unresolved), `sideLen_zero` (unresolved), `sideLen_two` (unresolved), `side_pos` (unresolved), `height_sq_mul` (unresolved), `circumradius_sq_mul` (unresolved), `two_mul_area_sq` (unresolved), `area_nonneg` (unresolved), `height_mul_sideLen` (unresolved), `area_pos` (unresolved), `four_mul_circumradius_mul_area` (unresolved), `excenterWeightsUnnorm_eq` (unresolved), `excenterWeights_eq` (unresolved), `exradius_eq` (unresolved), `incenter_weights` (unresolved), `inradius_eq` (unresolved), `sum_signed_sideLen_pos` (unresolved), `dist_affineCombination_circumcenter_sq` (unresolved), `centroid_eq_affineCombination` (unresolved), `triangle_pos` (unresolved), `inradius_mul` (unresolved), `leibniz_relation` (unresolved), `leibniz_min` (unresolved), `leibniz_min_eq_iff` (unresolved), `isoperimetric` (unresolved), `isoperimetric_eq_iff` (unresolved), `gerretsen_cross_check` (unresolved), `kooi_of_quartic` (unresolved), `kooi` (unresolved), `kooi_le_gerretsen` (unresolved)
LEANCHECK DONE Fri Oct 30 03:53:44 AM UTC 2026
