# leancheck — final_circles (2026-11-10 19:22 UTC)

- path: /home/jackagent/final_circles
- HEAD: 6c714e57d5cf41a43838d2a0e380fdc028e9b15b
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'CircleSystems.cross_eq_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'CircleSystems.cross_eq_areaForm' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (121 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: CircleSystems.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-11-10 19:58 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 110, "mut": 298, "killed": 292, "surv": 6, "tout": 7, "contra": 0, "sat": 47, "unres": 63, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## final_circles
- theorems: 110
- step 1 mutants: 298 | killed 285 | killed-timeout 7 | SURVIVED 6 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 50 | no-hyp 60 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 47 | unresolved 63 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `l14_steiner_line` [lit2->3@32] (heartbeat limit)
  - killed by timeout `l14_steiner_line_orthocenter` [lit1->2@62] (heartbeat limit)
  - killed by timeout `l14_steiner_line_orthocenter` [lit2->3@114] (heartbeat limit)
  - killed by timeout `l14_steiner_line_orthocenter` [lit2->3@74] (heartbeat limit)
  - SURVIVED detail: 
  - SURVIVOR `l14w_radical_center_concurrent` [lit2->3@114]: `∃ (O₁ O₂ O₃ : ℂ) (R₁ R₂ R₃ : ℝ), ¬ Collinear ℝ ({O₁, O₂, O₃} : Set ℂ) ∧
      ∀ X : ℂ, (dist X O₁ ^ 2 - R₁ ^ 2 = dist X O₂ ^ 2 - R₂ ^ 2 ∧
        dist X O₂ ^ 2 ` -> `∃ (O₁ O₂ O₃ : ℂ) (R₁ R₂ R₃ : ℝ), ¬ Collinear ℝ ({O₁, O₂, O₃} : Set ℂ) ∧
      ∀ X : ℂ, (dist X O₁ ^ 2 - R₁ ^ 3 = dist X O₂ ^ 2 - R₂ ^ 2 ∧
        dist X O₂ ^ 2 `
  - SURVIVED detail: 
  - SURVIVOR `l14w_isOrthogonal_iff` [lit0->1@34]: `∃ (O₁ O₂ X : ℂ) (R₁ R₂ : ℝ), 0 < R₁ ∧ 0 < R₂ ∧
      (dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ∧
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2` -> `∃ (O₁ O₂ X : ℂ) (R₁ R₂ : ℝ), 1 < R₁ ∧ 0 < R₂ ∧
      (dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ∧
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2`
  - SURVIVED detail: 
  - SURVIVOR `l14w_isOrthogonal_iff` [lit0->1@43]: `∃ (O₁ O₂ X : ℂ) (R₁ R₂ : ℝ), 0 < R₁ ∧ 0 < R₂ ∧
      (dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ∧
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2` -> `∃ (O₁ O₂ X : ℂ) (R₁ R₂ : ℝ), 0 < R₁ ∧ 1 < R₂ ∧
      (dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ∧
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2`
  - SURVIVED detail: own proof compiled; downstream errors at lines [235]
  - SURVIVOR `l14w_johnson_circle` [lit0->1@81]: `∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 0 < R ∧
      ¬ Collinear ℝ ({O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H} : Set ℂ) ∧
    ` -> `∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 1 < R ∧
      ¬ Collinear ℝ ({O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H} : Set ℂ) ∧
    `
  - SURVIVED detail: own proof compiled; downstream errors at lines [235]
  - SURVIVOR `l14w_johnson_circle` [lit2->3@183]: `∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 0 < R ∧
      ¬ Collinear ℝ ({O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H} : Set ℂ) ∧
    ` -> `∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 0 < R ∧
      ¬ Collinear ℝ ({O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H} : Set ℂ) ∧
    `
  - SURVIVED detail: 
  - SURVIVOR `l14w_steiner_line` [lit2->3@141]: `∃ (A B C O P : ℂ) (R : ℝ), dist A O = R ∧ dist B O = R ∧ dist C O = R ∧ dist P O = R ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
      A + B + C - (2 : ℝ) • O = ⟨2, 1⟩ ∧ re` -> `∃ (A B C O P : ℂ) (R : ℝ), dist A O = R ∧ dist B O = R ∧ dist C O = R ∧ dist P O = R ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
      A + B + C - (3 : ℝ) • O = ⟨2, 1⟩ ∧ re`
  - killed by timeout `steiner_line_orthocenter` [lit1->2@62] (heartbeat limit)
  - killed by timeout `steiner_line_orthocenter` [lit2->3@74] (heartbeat limit)
  - killed by timeout `steiner_line_orthocenter` [lit2->3@114] (heartbeat limit)
  - needs manual satisfiability check: `mul_dist_eq_abs_powPt` (unresolved)
  - needs manual satisfiability check: `sphere_inter_subset_radicalAxis` (unresolved)
  - needs manual satisfiability check: `johnson_center_eq_orthocenter` (unresolved)
  - needs manual satisfiability check: `cx_eq_repr` (unresolved)
  - needs manual satisfiability check: `cy_eq_repr` (unresolved)
  - needs manual satisfiability check: `cross_eq_det` (unresolved)
  - needs manual satisfiability check: `cross_eq_areaForm` (unresolved)
  - needs manual satisfiability check: `cx_add` (unresolved)
  - needs manual satisfiability check: `orthogonal_of_center_on_radicalAxis` (unresolved)
  - needs manual satisfiability check: `cy_add` (unresolved)
  - needs manual satisfiability check: `cx_sub` (unresolved)
  - needs manual satisfiability check: `cx_smul` (unresolved)
  - needs manual satisfiability check: `cy_sub` (unresolved)
  - needs manual satisfiability check: `cy_smul` (unresolved)
  - needs manual satisfiability check: `cx_zero'` (unresolved)
  - needs manual satisfiability check: `cy_zero'` (unresolved)
  - needs manual satisfiability check: `cx_b0` (unresolved)
  - needs manual satisfiability check: `cy_b0` (unresolved)
  - needs manual satisfiability check: `cx_b1` (unresolved)
  - needs manual satisfiability check: `cy_b1` (unresolved)
  - needs manual satisfiability check: `eq_coord` (unresolved)
  - needs manual satisfiability check: `inner_coord` (unresolved)
  - needs manual satisfiability check: `ext_coord` (unresolved)
  - needs manual satisfiability check: `norm_sq_coord` (unresolved)
  - needs manual satisfiability check: `dist_sq_coord` (unresolved)
  - needs manual satisfiability check: `eq_smul_of_cross_eq_zero` (unresolved)
  - needs manual satisfiability check: `collinear_of_forall_smul` (unresolved)
  - needs manual satisfiability check: `collinear_iff_cross` (unresolved)
  - needs manual satisfiability check: `collinear_four_of_cross` (unresolved)
  - needs manual satisfiability check: `johnson_mem_circles` (unresolved)
  - needs manual satisfiability check: `johnson_circle` (unresolved)
  - needs manual satisfiability check: `johnson_orthocenter` (unresolved)
  - needs manual satisfiability check: `johnson_orthocenter_eq` (unresolved)
  - needs manual satisfiability check: `l14_radical_center_concurrent` (unresolved)
  - needs manual satisfiability check: `l14_johnson_circle` (unresolved)
  - needs manual satisfiability check: `l14_johnson_orthocenter_eq` (unresolved)
  - needs manual satisfiability check: `l14_simson_det_eq_circumcircle_power` (unresolved)
  - needs manual satisfiability check: `l14_simson_wallace` (unresolved)
  - needs manual satisfiability check: `l14_steiner_line_orthocenter` (unresolved)
  - needs manual satisfiability check: `l14_steiner_line` (unresolved)
  - needs manual satisfiability check: `l14h_dist` (unresolved)
  - needs manual satisfiability check: `l14h_foot` (unresolved)
  - needs manual satisfiability check: `l14h_reflection` (unresolved)
  - needs manual satisfiability check: `mem_radicalAxis_of_mem_circles` (unresolved)
  - needs manual satisfiability check: `inner_sub_eq_zero_of_mem_radicalAxis` (unresolved)
  - needs manual satisfiability check: `mem_radicalAxis_trans` (unresolved)
  - needs manual satisfiability check: `powPt_coord` (unresolved)
  - needs manual satisfiability check: `cx_mk` (unresolved)
  - needs manual satisfiability check: `cy_mk` (unresolved)
  - needs manual satisfiability check: `foot_alg_x` (unresolved)
  - needs manual satisfiability check: `radical_center_concurrent` (unresolved)
  - needs manual satisfiability check: `foot_alg_y` (unresolved)
  - needs manual satisfiability check: `simson_alg` (unresolved)
  - needs manual satisfiability check: `steiner_alg_AB` (unresolved)
  - needs manual satisfiability check: `steiner_alg_AC` (unresolved)
  - needs manual satisfiability check: `steiner_alg_BC` (unresolved)
  - needs manual satisfiability check: `foot_props` (unresolved)
  - needs manual satisfiability check: `foot_coord` (unresolved)
  - needs manual satisfiability check: `R_ne_zero` (unresolved)
  - needs manual satisfiability check: `simson_det_eq_circumcircle_power` (unresolved)
  - needs manual satisfiability check: `simson_wallace` (unresolved)
  - needs manual satisfiability check: `steiner_line_orthocenter` (unresolved)
  - needs manual satisfiability check: `steiner_line` (unresolved)
  - no mutants generated (manual look): collinear_four_of_cross, collinear_of_forall_smul, johnson_congruent, johnson_reflection, l14_johnson_congruent, l14h_feet, mem_radicalAxis_of_mem_circles, mem_radicalAxis_trans, pencilCenter_mem_line, radBase_mem, radical_center_concurrent, sphere_inter_subset_radicalAxis

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 149 | UNUSED 6 | NEEDED 143 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `steiner_alg_AB` : `(_hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1))`
- UNUSED `steiner_alg_AB` : `(_hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2))`
- UNUSED `steiner_alg_AC` : `(_hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1))`
- UNUSED `steiner_alg_AC` : `(_hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2))`
- UNUSED `steiner_alg_BC` : `(_hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1))`
- UNUSED `steiner_alg_BC` : `(_hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 7 files
linter (scratch): 0 warnings in 1 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (121 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 7 of 7 files ok |
| conclusion mutations (layer 4) | **292/298 rejected** (285 by error, 7 by timeout/heartbeat); 6 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 50 probed ok — no-hyp 60 |
| satisfiability (layer 8) | 47/110 certified [12 with hypotheses, 26 hypothesis-free binders, 9 closed], 63 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 47/110 credited, 63 unresolved |
| hypothesis ablation (layer 6) | 143 needed, **6 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 7 files |
| linter, scratch (layer 7) | 0 warnings in 1 files |
| bridge inventory (layer 9) | 11 notions, 4 has-bridge, 7 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `steiner_alg_AB`: (_hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1)), `steiner_alg_AB`: (_hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2)), `steiner_alg_AC`: (_hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1)), `steiner_alg_AC`: (_hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2)), `steiner_alg_BC`: (_hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1)), `steiner_alg_BC`: (_hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))

mutation survivors (classify by hand): `l14w_radical_center_concurrent` [lit2->3@114] ; `l14w_isOrthogonal_iff` [lit0->1@34] ; `l14w_isOrthogonal_iff` [lit0->1@43] ; `l14w_johnson_circle` [lit0->1@81] own proof compiled; downstream errors at lines [235]; `l14w_johnson_circle` [lit2->3@183] own proof compiled; downstream errors at lines [235]; `l14w_steiner_line` [lit2->3@141] 

satisfiability not certified (recorded as unresolved, not success): `mul_dist_eq_abs_powPt` (unresolved), `sphere_inter_subset_radicalAxis` (unresolved), `johnson_center_eq_orthocenter` (unresolved), `cx_eq_repr` (unresolved), `cy_eq_repr` (unresolved), `cross_eq_det` (unresolved), `cross_eq_areaForm` (unresolved), `cx_add` (unresolved), `orthogonal_of_center_on_radicalAxis` (unresolved), `cy_add` (unresolved), `cx_sub` (unresolved), `cx_smul` (unresolved), `cy_sub` (unresolved), `cy_smul` (unresolved), `cx_zero'` (unresolved), `cy_zero'` (unresolved), `cx_b0` (unresolved), `cy_b0` (unresolved), `cx_b1` (unresolved), `cy_b1` (unresolved), `eq_coord` (unresolved), `inner_coord` (unresolved), `ext_coord` (unresolved), `norm_sq_coord` (unresolved), `dist_sq_coord` (unresolved), `eq_smul_of_cross_eq_zero` (unresolved), `collinear_of_forall_smul` (unresolved), `collinear_iff_cross` (unresolved), `collinear_four_of_cross` (unresolved), `johnson_mem_circles` (unresolved)
LEANCHECK DONE Tue Nov 10 08:14:04 PM UTC 2026
