# leancheck — paperh_fermat.pub (2026-10-30 03:53 UTC)

- path: ~/paperh_fermat.pub
- HEAD: 8f680c86b068196a4d27201209c856a5d038aaa4
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'FermatNapoleon.Classical.cov_F2d' depends on axioms: [propext, Classical.choice, Quot.sound]
'FermatNapoleon.Classical.cov_F3' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (171 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: FermatNapoleon.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (x86-64 machine)

Generated 2026-10-30 04:56 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 118, "mut": 313, "killed": 304, "surv": 9, "tout": 0, "contra": 0, "sat": 57, "unres": 61, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## paperh_fermat.pub
- theorems: 118
- step 1 mutants: 313 | killed 304 | killed-timeout 0 | SURVIVED 9 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 56 | no-hyp 62 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 57 | unresolved 59 | stmt-invalid 2 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: own proof compiled; downstream errors at lines [291]
  - SURVIVOR `l14_angle_lt` [lit2->3@11]: `∠ A B C < 2 * π / 3` -> `∠ A B C < 3 * π / 3`
  - SURVIVED detail: own proof compiled; downstream errors at lines [279, 284, 289]
  - SURVIVOR `l14T_sign` [neg1->1@126]: `(if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else -1) = 1` -> `(if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else 1) = 1`
  - SURVIVED detail: 
  - SURVIVOR `cov_F2d` [eq->ne@71]: `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ` -> `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) ≠ π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) `
  - SURVIVED detail: 
  - SURVIVOR `cov_F2d` [eq->ne@237]: `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ` -> `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) `
  - SURVIVED detail: 
  - SURVIVOR `cov_F2d` [eq->ne@403]: `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ` -> `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) `
  - SURVIVED detail: 
  - SURVIVOR `cov_F2d` [lit0->1@49]: `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ` -> `(InnerProductGeometry.angle (A' -ᵥ t.points 1) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) `
  - SURVIVED detail: 
  - SURVIVOR `cov_F2d` [lit1->2@68]: `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ` -> `(InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 2) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) `
  - SURVIVED detail: 
  - SURVIVOR `inner_gt_of_angle_lt` [lit1->2@7]: `-(1 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫` -> `-(2 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫`
  - SURVIVED detail: 
  - SURVIVOR `weight_pos` [lit1->2@5]: `0 < 1 + 2 * α * m` -> `0 < 2 + 2 * α * m`
  - needs manual satisfiability check: `triSign_mul_pos` (unresolved)
  - needs manual satisfiability check: `triSign_sq` (unresolved)
  - needs manual satisfiability check: `outerApex_vsub` (unresolved)
  - needs manual satisfiability check: `napoleonApex_zero` (unresolved)
  - needs manual satisfiability check: `napoleonApex_one` (unresolved)
  - needs manual satisfiability check: `napoleonApex_two` (unresolved)
  - needs manual satisfiability check: `gram_pos` (unresolved)
  - needs manual satisfiability check: `apex_frame` (unresolved)
  - needs manual satisfiability check: `apex_inner` (unresolved)
  - needs manual satisfiability check: `apex_sum` (unresolved)
  - needs manual satisfiability check: `napoleonCenter_vsub` (unresolved)
  - needs manual satisfiability check: `fermat_frame` (unresolved)
  - needs manual satisfiability check: `agree_sign` (unresolved)
  - needs manual satisfiability check: `agree_outerApex` (unresolved)
  - needs manual satisfiability check: `agree_apexA` (unresolved)
  - needs manual satisfiability check: `agree_apexB` (unresolved)
  - needs manual satisfiability check: `agree_apexC` (unresolved)
  - needs manual satisfiability check: `agree_centerA` (unresolved)
  - needs manual satisfiability check: `agree_centerB` (unresolved)
  - needs manual satisfiability check: `agree_centroid` (stmt-invalid)
  - needs manual satisfiability check: `agree_centerC` (unresolved)
  - needs manual satisfiability check: `agree_orders` (stmt-invalid)
  - needs manual satisfiability check: `l14b_outerApex_eq` (unresolved)
  - needs manual satisfiability check: `l14b_apexes` (unresolved)
  - needs manual satisfiability check: `l14_apex_outward` (unresolved)
  - needs manual satisfiability check: `l14_napoleon_dist_eq` (unresolved)
  - needs manual satisfiability check: `l14_napoleon_concurrent` (unresolved)
  - needs manual satisfiability check: `l14_napoleon_fermat` (unresolved)
  - needs manual satisfiability check: `l14_napoleon` (unresolved)
  - needs manual satisfiability check: `l14_napoleon_angle` (unresolved)
  - needs manual satisfiability check: `l14_ptolemy_collinear` (unresolved)
  - needs manual satisfiability check: `l14_ne_of_angle` (unresolved)
  - needs manual satisfiability check: `col_iff` (unresolved)
  - needs manual satisfiability check: `coplanar_of_cross` (unresolved)
  - needs manual satisfiability check: `sbtw_of_concyclic` (unresolved)
  - needs manual satisfiability check: `inner_of_angle'` (unresolved)
  - needs manual satisfiability check: `vne_of_angle` (unresolved)
  - needs manual satisfiability check: `vne_of_angle'` (unresolved)
  - needs manual satisfiability check: `unit_sum` (unresolved)
  - needs manual satisfiability check: `fermat_unique_vec` (unresolved)
  - needs manual satisfiability check: `fermat_unique` (unresolved)
  - needs manual satisfiability check: `apex_eq` (unresolved)
  - needs manual satisfiability check: `classical_apexes` (unresolved)
  - needs manual satisfiability check: `cov_F2a` (unresolved)
  - needs manual satisfiability check: `cov_F2b` (unresolved)
  - needs manual satisfiability check: `cov_F2c` (unresolved)
  - needs manual satisfiability check: `cov_F2d` (unresolved)
  - needs manual satisfiability check: `cov_F3` (unresolved)
  - needs manual satisfiability check: `angle_eq_of_inner` (unresolved)
  - needs manual satisfiability check: `inner_gt_of_angle_lt` (unresolved)
  - needs manual satisfiability check: `weight_pos` (unresolved)
  - needs manual satisfiability check: `apex_outward` (unresolved)
  - needs manual satisfiability check: `napoleon_dist_eq` (unresolved)
  - needs manual satisfiability check: `fermat_point_spec` (unresolved)
  - needs manual satisfiability check: `napoleon_concurrent` (unresolved)
  - needs manual satisfiability check: `napoleon_fermat` (unresolved)
  - needs manual satisfiability check: `napoleon` (unresolved)
  - needs manual satisfiability check: `napoleon_angle` (unresolved)
  - needs manual satisfiability check: `ptolemy_collinear` (unresolved)
  - needs manual satisfiability check: `norm_sub_eq_of_inner` (unresolved)
  - needs manual satisfiability check: `sphere_vec` (unresolved)
  - no mutants generated (manual look): agree_orders, agree_orders_real, br_28, br_37_38_39, br_40_41, br_42, br_43_44, br_45_46_47, br_48_49_50, col_iff, coplanar_of_cross, cov_F3, l14_not_collinear, l14_sbtw, rb_28, rb_37, rb_38, rb_39, rb_40, rb_41, rb_42, rb_43, rb_44, rb_45, rb_46, rb_47, rb_48, rb_49, rb_50, real_order_iff, sOppSide_of_areaForm, sbtw_of_concyclic

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 182 | UNUSED 0 | NEEDED 182 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 7 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (171 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 7 of 7 files ok |
| conclusion mutations (layer 4) | **304/313 rejected** (304 by error, 0 by timeout/heartbeat); 9 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 56 probed ok — no-hyp 62 |
| satisfiability (layer 8) | 57/118 certified [22 with hypotheses, 6 hypothesis-free binders, 29 closed], 59 unresolved, 2 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 57/118 credited, 61 unresolved |
| hypothesis ablation (layer 6) | 182 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 7 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 49 notions, 0 has-bridge, 49 NO-BRIDGE (see inventory.md) |

mutation survivors (classify by hand): `l14_angle_lt` [lit2->3@11] own proof compiled; downstream errors at lines [291]; `l14T_sign` [neg1->1@126] own proof compiled; downstream errors at lines [279, 284, 289]; `cov_F2d` [eq->ne@71] ; `cov_F2d` [eq->ne@237] ; `cov_F2d` [eq->ne@403] ; `cov_F2d` [lit0->1@49] ; `cov_F2d` [lit1->2@68] ; `inner_gt_of_angle_lt` [lit1->2@7] ; `weight_pos` [lit1->2@5] 

satisfiability not certified (recorded as unresolved, not success): `triSign_mul_pos` (unresolved), `triSign_sq` (unresolved), `outerApex_vsub` (unresolved), `napoleonApex_zero` (unresolved), `napoleonApex_one` (unresolved), `napoleonApex_two` (unresolved), `gram_pos` (unresolved), `apex_frame` (unresolved), `apex_inner` (unresolved), `apex_sum` (unresolved), `napoleonCenter_vsub` (unresolved), `fermat_frame` (unresolved), `agree_sign` (unresolved), `agree_outerApex` (unresolved), `agree_apexA` (unresolved), `agree_apexB` (unresolved), `agree_apexC` (unresolved), `agree_centerA` (unresolved), `agree_centerB` (unresolved), `agree_centroid` (stmt-invalid), `agree_centerC` (unresolved), `agree_orders` (stmt-invalid), `l14b_outerApex_eq` (unresolved), `l14b_apexes` (unresolved), `l14_apex_outward` (unresolved), `l14_napoleon_dist_eq` (unresolved), `l14_napoleon_concurrent` (unresolved), `l14_napoleon_fermat` (unresolved), `l14_napoleon` (unresolved), `l14_napoleon_angle` (unresolved)
LEANCHECK DONE Fri Oct 30 05:16:19 AM UTC 2026
