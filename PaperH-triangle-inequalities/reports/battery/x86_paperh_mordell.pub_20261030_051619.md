# leancheck — paperh_mordell.pub (2026-10-30 05:16 UTC)

- path: ~/paperh_mordell.pub
- HEAD: 7b2270146195cf2a4c589e403143dba0abd0f6a7
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'ErdosMordell.Classical.cov_F1a' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMordell.Classical.cov_F1b' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (144 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: ErdosMordell.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp_ext rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (x86-64 machine)

Generated 2026-10-30 05:59 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 101, "mut": 314, "killed": 310, "surv": 4, "tout": 0, "contra": 0, "sat": 36, "unres": 65, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## paperh_mordell.pub
- theorems: 101
- step 1 mutants: 314 | killed 310 | killed-timeout 0 | SURVIVED 4 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 65 | no-hyp 36 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 36 | unresolved 61 | stmt-invalid 4 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: own proof compiled; downstream errors at lines [219, 227, 236]
  - SURVIVOR `inner_gt_of_angle_lt` [lit1->2@7]: `-(1 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫` -> `-(2 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫`
  - SURVIVED detail: own proof compiled; downstream errors at lines [372]
  - SURVIVOR `l14_angle_lt` [lit2->3@11]: `∠ A B C < 2 * π / 3` -> `∠ A B C < 3 * π / 3`
  - SURVIVED detail: 
  - SURVIVOR `l14w_erdos_mordell` [eq->ne@1524]: `∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧ X = !₂[1, 1] ∧
    X ∈ t.interio` -> `∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧ X = !₂[1, 1] ∧
    X ∈ t.interio`
  - SURVIVED detail: 
  - SURVIVOR `l14w_erdos_mordell` [eq->ne@1590]: `∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧ X = !₂[1, 1] ∧
    X ∈ t.interio` -> `∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧ X = !₂[1, 1] ∧
    X ∈ t.interio`
  - needs manual satisfiability check: `barrow_T` (unresolved)
  - needs manual satisfiability check: `barrow_halfangle` (unresolved)
  - needs manual satisfiability check: `barrow_bound` (unresolved)
  - needs manual satisfiability check: `barrow_scalar` (unresolved)
  - needs manual satisfiability check: `gram_pos_of_not_collinear` (unresolved)
  - needs manual satisfiability check: `bisector_dist` (unresolved)
  - needs manual satisfiability check: `barrow_vec` (unresolved)
  - needs manual satisfiability check: `weighted_vsub_eq_zero` (unresolved)
  - needs manual satisfiability check: `proj_eq_lineMap` (unresolved)
  - needs manual satisfiability check: `barrow` (unresolved)
  - needs manual satisfiability check: `proj_congr` (unresolved)
  - needs manual satisfiability check: `affineCombination_vsub` (unresolved)
  - needs manual satisfiability check: `affineCombination_vsub_zero` (unresolved)
  - needs manual satisfiability check: `affineCombination_vsub_one` (unresolved)
  - needs manual satisfiability check: `affineCombination_vsub_two` (unresolved)
  - needs manual satisfiability check: `gram_pos` (unresolved)
  - needs manual satisfiability check: `points_ne` (unresolved)
  - needs manual satisfiability check: `inner_of_angle` (unresolved)
  - needs manual satisfiability check: `ne_of_angle` (unresolved)
  - needs manual satisfiability check: `fermat_min` (unresolved)
  - needs manual satisfiability check: `fermat_alg` (unresolved)
  - needs manual satisfiability check: `inner_gt_of_angle_lt` (unresolved)
  - needs manual satisfiability check: `angle_of_alg` (unresolved)
  - needs manual satisfiability check: `x_pos` (unresolved)
  - needs manual satisfiability check: `vsub_F_eq` (unresolved)
  - needs manual satisfiability check: `fermat_exists` (unresolved)
  - needs manual satisfiability check: `fermat_torricelli` (unresolved)
  - needs manual satisfiability check: `agree_distToLine` (unresolved)
  - needs manual satisfiability check: `agree_closed` (stmt-invalid)
  - needs manual satisfiability check: `agree_distToLine'` (unresolved)
  - needs manual satisfiability check: `agree_inside` (stmt-invalid)
  - needs manual satisfiability check: `agree_equilateral` (stmt-invalid)
  - needs manual satisfiability check: `l14_of_mem_closedInterior` (unresolved)
  - needs manual satisfiability check: `l14_of_mem_interior` (unresolved)
  - needs manual satisfiability check: `l14_key_lemma_zero` (unresolved)
  - needs manual satisfiability check: `l14_key_lemma_one` (unresolved)
  - needs manual satisfiability check: `l14_key_lemma_two` (unresolved)
  - needs manual satisfiability check: `l14_erdos_mordell` (unresolved)
  - needs manual satisfiability check: `l14_erdos_mordell_eq_iff` (unresolved)
  - needs manual satisfiability check: `l14_barrow` (unresolved)
  - needs manual satisfiability check: `l14_fermat_min` (unresolved)
  - needs manual satisfiability check: `l14_fermat_exists` (unresolved)
  - needs manual satisfiability check: `l14_fermat_torricelli` (unresolved)
  - needs manual satisfiability check: `l14_dist` (unresolved)
  - needs manual satisfiability check: `l14_not_collinear` (unresolved)
  - needs manual satisfiability check: `l14_ne` (unresolved)
  - needs manual satisfiability check: `l14_ac` (unresolved)
  - needs manual satisfiability check: `l14_angle_eq` (unresolved)
  - needs manual satisfiability check: `cov_M1a` (unresolved)
  - needs manual satisfiability check: `cov_M1b` (unresolved)
  - needs manual satisfiability check: `cov_F1a` (unresolved)
  - needs manual satisfiability check: `cov_M2` (unresolved)
  - needs manual satisfiability check: `cov_F1b` (unresolved)
  - needs manual satisfiability check: `key_scalar_sq` (unresolved)
  - needs manual satisfiability check: `key_scalar` (unresolved)
  - needs manual satisfiability check: `key_scalar_eq_iff` (unresolved)
  - needs manual satisfiability check: `key_facts` (unresolved)
  - needs manual satisfiability check: `key_lemma_zero` (unresolved)
  - needs manual satisfiability check: `key_aux` (unresolved)
  - needs manual satisfiability check: `key_lemma_one` (unresolved)
  - needs manual satisfiability check: `key_lemma_two` (unresolved)
  - needs manual satisfiability check: `erdos_mordell` (unresolved)
  - needs manual satisfiability check: `em_eq_scalar` (stmt-invalid)
  - needs manual satisfiability check: `erdos_mordell_eq_iff` (unresolved)
  - needs manual satisfiability check: `eq_pos` (unresolved)
  - no mutants generated (manual look): b36_to_exists, br_29, br_30, br_31, br_32, br_33, br_34, br_35, br_36, l14_mem_line, rb_29, rb_30, rb_31, rb_32, rb_33, rb_34, rb_35, rb_36

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 246 | UNUSED 0 | NEEDED 246 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 7 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (144 declarations, standard axioms only) |
| tamper (layer 2) | 7/7 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 7 of 7 files ok |
| conclusion mutations (layer 4) | **310/314 rejected** (310 by error, 0 by timeout/heartbeat); 4 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 65 probed ok — no-hyp 36 |
| satisfiability (layer 8) | 36/101 certified [6 with hypotheses, 4 hypothesis-free binders, 26 closed], 61 unresolved, 4 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 36/101 credited, 65 unresolved |
| hypothesis ablation (layer 6) | 246 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 7 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 43 notions, 1 has-bridge, 42 NO-BRIDGE (see inventory.md) |

mutation survivors (classify by hand): `inner_gt_of_angle_lt` [lit1->2@7] own proof compiled; downstream errors at lines [219, 227, 236]; `l14_angle_lt` [lit2->3@11] own proof compiled; downstream errors at lines [372]; `l14w_erdos_mordell` [eq->ne@1524] ; `l14w_erdos_mordell` [eq->ne@1590] 

satisfiability not certified (recorded as unresolved, not success): `barrow_T` (unresolved), `barrow_halfangle` (unresolved), `barrow_bound` (unresolved), `barrow_scalar` (unresolved), `gram_pos_of_not_collinear` (unresolved), `bisector_dist` (unresolved), `barrow_vec` (unresolved), `weighted_vsub_eq_zero` (unresolved), `proj_eq_lineMap` (unresolved), `barrow` (unresolved), `proj_congr` (unresolved), `affineCombination_vsub` (unresolved), `affineCombination_vsub_zero` (unresolved), `affineCombination_vsub_one` (unresolved), `affineCombination_vsub_two` (unresolved), `gram_pos` (unresolved), `points_ne` (unresolved), `inner_of_angle` (unresolved), `ne_of_angle` (unresolved), `fermat_min` (unresolved), `fermat_alg` (unresolved), `inner_gt_of_angle_lt` (unresolved), `angle_of_alg` (unresolved), `x_pos` (unresolved), `vsub_F_eq` (unresolved), `fermat_exists` (unresolved), `fermat_torricelli` (unresolved), `agree_distToLine` (unresolved), `agree_closed` (stmt-invalid), `agree_distToLine'` (unresolved)
LEANCHECK DONE Fri Oct 30 06:39:48 AM UTC 2026
