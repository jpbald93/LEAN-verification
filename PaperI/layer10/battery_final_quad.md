# leancheck — final_quad (2026-11-10 18:00 UTC)

- path: /home/jackagent/final_quad
- HEAD: 0c372061edd32cc7935cf1521d404dfbc3993ac5
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'Quadrilaterals.isIncircle_iff_isTangent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quadrilaterals.tangential_iff_exists_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (133 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Quadrilaterals.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ok    fusshyp   rejected (exit 1): FAIL: build
ok    fussstmt  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-11-10 19:09 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 118, "mut": 273, "killed": 272, "surv": 1, "tout": 0, "contra": 0, "sat": 35, "unres": 83, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## final_quad
- theorems: 118
- step 1 mutants: 273 | killed 272 | killed-timeout 0 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 55 | no-hyp 63 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 35 | unresolved 80 | stmt-invalid 3 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: 
  - SURVIVOR `l14w_fuss` [lit0->1@185]: `∃ (A B C D O I : ℂ) (R r : ℝ), (∃ X : ℂ, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧
      ¬ Collinear ℝ ({A, B, C} : Set ℂ) ∧
      dist A O = R ∧ dist B O = R ∧ dist C O =` -> `∃ (A B C D O I : ℂ) (R r : ℝ), (∃ X : ℂ, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧
      ¬ Collinear ℝ ({A, B, C} : Set ℂ) ∧
      dist A O = R ∧ dist B O = R ∧ dist C O =`
  - needs manual satisfiability check: `pitot_core` (unresolved)
  - needs manual satisfiability check: `cross_eq_areaForm` (unresolved)
  - needs manual satisfiability check: `abs_cross_eq_abs_areaForm` (unresolved)
  - needs manual satisfiability check: `ConvexQuad.quadArea_eq_areaForm` (unresolved)
  - needs manual satisfiability check: `cx_eq_repr` (unresolved)
  - needs manual satisfiability check: `cy_eq_repr` (unresolved)
  - needs manual satisfiability check: `cross_eq_det` (unresolved)
  - needs manual satisfiability check: `ConvexQuad.quadSign_eq_sign` (unresolved)
  - needs manual satisfiability check: `infDist_line` (unresolved)
  - needs manual satisfiability check: `mem_line_iff` (unresolved)
  - needs manual satisfiability check: `sSameSide_line_iff` (unresolved)
  - needs manual satisfiability check: `sOppSide_line_iff` (unresolved)
  - needs manual satisfiability check: `triArea_eq` (unresolved)
  - needs manual satisfiability check: `sin_angle_mul` (unresolved)
  - needs manual satisfiability check: `collinear_of_cross_eq_zero` (unresolved)
  - needs manual satisfiability check: `convex_frame` (unresolved)
  - needs manual satisfiability check: `cx_add` (unresolved)
  - needs manual satisfiability check: `cy_add` (unresolved)
  - needs manual satisfiability check: `cx_sub` (unresolved)
  - needs manual satisfiability check: `cy_sub` (unresolved)
  - needs manual satisfiability check: `cx_neg` (unresolved)
  - needs manual satisfiability check: `cy_neg` (unresolved)
  - needs manual satisfiability check: `cx_smul` (unresolved)
  - needs manual satisfiability check: `cy_smul` (unresolved)
  - needs manual satisfiability check: `cx_zero` (unresolved)
  - needs manual satisfiability check: `cy_zero` (unresolved)
  - needs manual satisfiability check: `eq_coord` (unresolved)
  - needs manual satisfiability check: `ext_coord` (unresolved)
  - needs manual satisfiability check: `inner_coord` (unresolved)
  - needs manual satisfiability check: `norm_sq_coord` (unresolved)
  - needs manual satisfiability check: `dist_sq_coord` (unresolved)
  - needs manual satisfiability check: `cross_self` (unresolved)
  - needs manual satisfiability check: `lagrange` (unresolved)
  - needs manual satisfiability check: `cramer` (unresolved)
  - needs manual satisfiability check: `cross_zero_right` (unresolved)
  - needs manual satisfiability check: `eq_smul_of_cross_eq_zero` (unresolved)
  - needs manual satisfiability check: `cross_smul_right` (unresolved)
  - needs manual satisfiability check: `cross_sub_right` (unresolved)
  - needs manual satisfiability check: `cross_add_right` (unresolved)
  - needs manual satisfiability check: `cross_smul_left` (unresolved)
  - needs manual satisfiability check: `cx_vsub` (unresolved)
  - needs manual satisfiability check: `cy_vsub` (unresolved)
  - needs manual satisfiability check: `dist_sq_px` (unresolved)
  - needs manual satisfiability check: `px_vadd` (unresolved)
  - needs manual satisfiability check: `py_vadd` (unresolved)
  - needs manual satisfiability check: `px_midpoint` (unresolved)
  - needs manual satisfiability check: `px_self` (unresolved)
  - needs manual satisfiability check: `py_midpoint` (unresolved)
  - needs manual satisfiability check: `py_self` (unresolved)
  - needs manual satisfiability check: `eq_of_px_py` (unresolved)
  - needs manual satisfiability check: `cx_swapBasis` (unresolved)
  - needs manual satisfiability check: `cy_swapBasis` (unresolved)
  - needs manual satisfiability check: `cross_swapBasis` (unresolved)
  - needs manual satisfiability check: `cross_comm` (unresolved)
  - needs manual satisfiability check: `IsFrame.chord` (unresolved)
  - needs manual satisfiability check: `cross_px` (unresolved)
  - needs manual satisfiability check: `IsFrame.crosses` (stmt-invalid)
  - needs manual satisfiability check: `IsFrame.pos` (stmt-invalid)
  - needs manual satisfiability check: `IsFrame.ne` (stmt-invalid)
  - needs manual satisfiability check: `IsFrame.cyclic_sides` (unresolved)
  - needs manual satisfiability check: `signed_dist` (unresolved)
  - needs manual satisfiability check: `IsFrame.incircle` (unresolved)
  - needs manual satisfiability check: `fuss` (unresolved)
  - needs manual satisfiability check: `fuss_side` (unresolved)
  - needs manual satisfiability check: `fuss_power` (unresolved)
  - needs manual satisfiability check: `fuss_closure` (unresolved)
  - needs manual satisfiability check: `fuss_opposite` (unresolved)
  - needs manual satisfiability check: `fuss_final` (unresolved)
  - needs manual satisfiability check: `l14_bretschneider` (unresolved)
  - needs manual satisfiability check: `l14_brahmagupta` (unresolved)
  - needs manual satisfiability check: `l14_pitot` (unresolved)
  - needs manual satisfiability check: `l14_pitot_converse` (unresolved)
  - needs manual satisfiability check: `l14_ptolemy_second` (unresolved)
  - needs manual satisfiability check: `l14_newton_line` (unresolved)
  - needs manual satisfiability check: `l14_fuss` (unresolved)
  - needs manual satisfiability check: `l14h_incircle_side` (unresolved)
  - needs manual satisfiability check: `bretschneider` (unresolved)
  - needs manual satisfiability check: `brahmagupta` (unresolved)
  - needs manual satisfiability check: `side_of_signed_dist` (unresolved)
  - needs manual satisfiability check: `pitot` (unresolved)
  - needs manual satisfiability check: `pitot_converse` (unresolved)
  - needs manual satisfiability check: `ptolemy_second` (unresolved)
  - needs manual satisfiability check: `newton_line` (unresolved)
  - no mutants generated (manual look): collinear_of_cross_eq_zero, convexQuad_iff_sOppSide, cospherical_four_iff_exists_sphere, cospherical_iff_concyclic, l14_newton_line, l14h_cyclic, l14h_not_collinear, l14h_sbtw, l14h_tangential, newton_line, pitot_converse

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 132 | UNUSED 1 | NEEDED 131 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `fuss_opposite` : `(hr : 0 < r)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 10 files
linter (scratch): 0 warnings in 10 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (133 declarations, standard axioms only) |
| tamper (layer 2) | 11/11 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 10 of 10 files ok |
| conclusion mutations (layer 4) | **272/273 rejected** (272 by error, 0 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 55 probed ok — no-hyp 63 |
| satisfiability (layer 8) | 35/118 certified [6 with hypotheses, 20 hypothesis-free binders, 9 closed], 80 unresolved, 3 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 35/118 credited, 83 unresolved |
| hypothesis ablation (layer 6) | 131 needed, **1 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 10 files |
| linter, scratch (layer 7) | 0 warnings in 10 files, nonzero exit: scratch/P.lean |
| bridge inventory (layer 9) | 7 notions, 3 has-bridge, 4 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `fuss_opposite`: (hr : 0 < r)

mutation survivors (classify by hand): `l14w_fuss` [lit0->1@185] 

satisfiability not certified (recorded as unresolved, not success): `pitot_core` (unresolved), `cross_eq_areaForm` (unresolved), `abs_cross_eq_abs_areaForm` (unresolved), `ConvexQuad.quadArea_eq_areaForm` (unresolved), `cx_eq_repr` (unresolved), `cy_eq_repr` (unresolved), `cross_eq_det` (unresolved), `ConvexQuad.quadSign_eq_sign` (unresolved), `infDist_line` (unresolved), `mem_line_iff` (unresolved), `sSameSide_line_iff` (unresolved), `sOppSide_line_iff` (unresolved), `triArea_eq` (unresolved), `sin_angle_mul` (unresolved), `collinear_of_cross_eq_zero` (unresolved), `convex_frame` (unresolved), `cx_add` (unresolved), `cy_add` (unresolved), `cx_sub` (unresolved), `cy_sub` (unresolved), `cx_neg` (unresolved), `cy_neg` (unresolved), `cx_smul` (unresolved), `cy_smul` (unresolved), `cx_zero` (unresolved), `cy_zero` (unresolved), `eq_coord` (unresolved), `ext_coord` (unresolved), `inner_coord` (unresolved), `norm_sq_coord` (unresolved)
LEANCHECK DONE Tue Nov 10 07:22:38 PM UTC 2026
