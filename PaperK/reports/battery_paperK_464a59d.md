# leancheck — paperK (2026-11-16 21:14 UTC)

- path: /home/jackagent/paperK
- HEAD: 464a59df987e149e1e545cbd5299196ecce354ed
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'PaperKn.simplex_circumradius' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperKn.brief_E_false' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (73 declarations, standard axioms only)
ok    sorry      rejected (exit 1): FAIL: forbidden token
ok    ax2line    rejected (exit 1): FAIL: forbidden token
ok    evalfake   rejected (exit 1): FAIL: forbidden token
ok    macro      rejected (exit 1): FAIL: forbidden token
ok    wrap       rejected (exit 1): FAIL: nonstandard axioms: PaperK.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp   rejected (exit 1): FAIL: build
ok    falsestmt  rejected (exit 1): FAIL: build
ok    falsehyp2  rejected (exit 1): FAIL: build
ok    falsestmt2 rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-11-16 21:51 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 148, "mut": 460, "killed": 444, "surv": 16, "tout": 0, "contra": 0, "sat": 73, "unres": 54, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## paperK
- theorems: 148
- step 1 mutants: 460 | killed 444 | killed-timeout 0 | SURVIVED 16 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 75 | no-hyp 52 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 73 | unresolved 54 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: own proof compiled; downstream errors at lines [278]
  - SURVIVOR `cex_pt_ne` [lit0->1@12]: `pt cex_P ≠ 0` -> `pt cex_P ≠ 1`
  - SURVIVED detail: 
  - SURVIVOR `tetra_centre_norm` [neg1->1@71]: `Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real` -> `Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.`
  - SURVIVED detail: 
  - SURVIVOR `tetra_centre_norm` [neg1->1@80]: `Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real` -> `Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.`
  - SURVIVED detail: 
  - SURVIVOR `tetra_centre_norm` [lit2->3@18]: `Real.sqrt (1^2 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real` -> `Real.sqrt (1^3 + 1^2 + 1^2) = Real.sqrt 3 ∧
    Real.sqrt (1^2 + (-1)^2 + (-1)^2) = Real.sqrt 3 ∧
    Real.sqrt ((-1)^2 + 1^2 + (-1)^2) = Real.sqrt 3 ∧
    Real`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@58]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, 1, -1], ![-1, 1, -1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@62]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, 1], ![-1, 1, -1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@69]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![1, 1, -1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@76]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, 1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@83]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [neg1->1@87]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, 1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [lit1->2@30]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![2, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `tetra_affineIndependent` [lit1->2@33]: `AffineIndependent ℝ ![(![1, 1, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]` -> `AffineIndependent ℝ ![(![1, 2, 1] : Fin 3 → ℝ), ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]`
  - SURVIVED detail: 
  - SURVIVOR `equilateral_centre_unique` [lit2->3@10]: `(x ^ 2 + y ^ 2 = (x - 2) ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 = (x - 1) ^ 2 + (y - Real.sqrt 3) ^ 2)
    ↔ (x = 1 ∧ y = Real.sqrt 3 / 3)` -> `(x ^ 3 + y ^ 2 = (x - 2) ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 = (x - 1) ^ 2 + (y - Real.sqrt 3) ^ 2)
    ↔ (x = 1 ∧ y = Real.sqrt 3 / 3)`
  - SURVIVED detail: 
  - SURVIVOR `square_apollonius_radii_ne` [lit1->2@2]: `(1 + Real.sqrt 2 : ℝ) ≠ 1 - Real.sqrt 2` -> `(2 + Real.sqrt 2 : ℝ) ≠ 1 - Real.sqrt 2`
  - SURVIVED detail: 
  - SURVIVOR `square_PX` [lit1->2@8]: `(P 1 / P 3, P 2 / P 3) = ((0 : ℝ), (0 : ℝ))` -> `(P 2 / P 3, P 2 / P 3) = ((0 : ℝ), (0 : ℝ))`
  - SURVIVED detail: 
  - SURVIVOR `square_PX` [lit3->4@14]: `(P 1 / P 3, P 2 / P 3) = ((0 : ℝ), (0 : ℝ))` -> `(P 1 / P 4, P 2 / P 3) = ((0 : ℝ), (0 : ℝ))`
  - needs manual satisfiability check: `bridge_B_eq_zero_iff_dist` (unresolved)
  - needs manual satisfiability check: `bridge_B_dist` (unresolved)
  - needs manual satisfiability check: `bridge_B_isExtTangent` (unresolved)
  - needs manual satisfiability check: `bridge_B_isIntTangent` (unresolved)
  - needs manual satisfiability check: `bridge_B_power` (unresolved)
  - needs manual satisfiability check: `bridge_power_eq_const_sphere` (unresolved)
  - needs manual satisfiability check: `bridge_power_eq_const_sphere_rho0` (unresolved)
  - needs manual satisfiability check: `bridge_pconst_neg_B` (unresolved)
  - needs manual satisfiability check: `bridge_equal_power_sphere` (unresolved)
  - needs manual satisfiability check: `B_comm` (unresolved)
  - needs manual satisfiability check: `B_add_right` (unresolved)
  - needs manual satisfiability check: `B_smul_right` (unresolved)
  - needs manual satisfiability check: `B_add_left` (unresolved)
  - needs manual satisfiability check: `B_smul_left` (unresolved)
  - needs manual satisfiability check: `tangency_identity` (unresolved)
  - needs manual satisfiability check: `tangency_of_B_eq_zero` (unresolved)
  - needs manual satisfiability check: `B_eq_zero_iff_tangent` (unresolved)
  - needs manual satisfiability check: `power_eq_const` (unresolved)
  - needs manual satisfiability check: `equal_power` (unresolved)
  - needs manual satisfiability check: `pt_affine_comb` (unresolved)
  - needs manual satisfiability check: `prop31` (unresolved)
  - needs manual satisfiability check: `dist_sq_const` (unresolved)
  - needs manual satisfiability check: `eq_zero_of_orth_affineIndependent` (unresolved)
  - needs manual satisfiability check: `simplex_E1` (unresolved)
  - needs manual satisfiability check: `simplex_circumradius` (unresolved)
  - needs manual satisfiability check: `tangency_identity` (unresolved)
  - needs manual satisfiability check: `tangency_of_B_eq_zero` (unresolved)
  - needs manual satisfiability check: `B_eq_zero_iff_tangent` (unresolved)
  - needs manual satisfiability check: `prop31` (unresolved)
  - needs manual satisfiability check: `prop31_cofactor` (unresolved)
  - needs manual satisfiability check: `power_eq_of_B_eq_zero` (unresolved)
  - needs manual satisfiability check: `equal_power` (unresolved)
  - needs manual satisfiability check: `explicit_power` (unresolved)
  - needs manual satisfiability check: `explicit_power_indep` (unresolved)
  - needs manual satisfiability check: `tangency_identity` (unresolved)
  - needs manual satisfiability check: `equal_power` (unresolved)
  - needs manual satisfiability check: `equal_power_pair` (unresolved)
  - needs manual satisfiability check: `tetra_equidistant_unique` (unresolved)
  - needs manual satisfiability check: `tetra_PX_origin` (unresolved)
  - needs manual satisfiability check: `tetra_E1_apollonius` (unresolved)
  - needs manual satisfiability check: `tetraR_PX_origin` (unresolved)
  - needs manual satisfiability check: `power_eq_const` (unresolved)
  - needs manual satisfiability check: `equal_power` (unresolved)
  - needs manual satisfiability check: `equi_unique` (unresolved)
  - needs manual satisfiability check: `cc_generic` (unresolved)
  - needs manual satisfiability check: `equi_cc` (unresolved)
  - needs manual satisfiability check: `equi_iff` (unresolved)
  - needs manual satisfiability check: `equal_power_point_unique` (unresolved)
  - needs manual satisfiability check: `PX_circumcentre` (unresolved)
  - needs manual satisfiability check: `equilateral_PX_param` (unresolved)
  - needs manual satisfiability check: `equilateral_PX` (unresolved)
  - needs manual satisfiability check: `square_PX` (unresolved)
  - needs manual satisfiability check: `square_null_indep` (unresolved)
  - needs manual satisfiability check: `square_PX_via_equal_power` (unresolved)
  - no mutants generated (manual look): cex_affInd, equi_cc, explicit_power, explicit_power_indep, prop31_cofactor

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 242 | UNUSED 4 | NEEDED 238 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `bridge_pconst_neg_B` : `(hP : P 3 ≠ 0)`
- UNUSED `simplex_E1` : `(_hP0 : B P X₀ = 0)`
- UNUSED `equilateral_PX_param` : `(_h4 : B P (circ r a b) = 0)`
- UNUSED `square_PX` : `(_hP : P 3 ≠ 0)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 5 files
linter (scratch): 0 warnings in 1 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (73 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 5 of 5 files ok |
| conclusion mutations (layer 4) | **444/460 rejected** (444 by error, 0 by timeout/heartbeat); 16 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 75 probed ok — no-hyp 52 |
| satisfiability (layer 8) | 73/127 certified [9 with hypotheses, 53 hypothesis-free binders, 11 closed], 54 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 73/127 credited, 54 unresolved |
| hypothesis ablation (layer 6) | 238 needed, **4 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 5 files |
| linter, scratch (layer 7) | 0 warnings in 1 files, nonzero exit: scratch/paperK_l14b.lean |
| bridge inventory (layer 9) | 24 notions, 3 has-bridge, 21 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `bridge_pconst_neg_B`: (hP : P 3 ≠ 0), `simplex_E1`: (_hP0 : B P X₀ = 0), `equilateral_PX_param`: (_h4 : B P (circ r a b) = 0), `square_PX`: (_hP : P 3 ≠ 0)

mutation survivors (classify by hand): `cex_pt_ne` [lit0->1@12] own proof compiled; downstream errors at lines [278]; `tetra_centre_norm` [neg1->1@71] ; `tetra_centre_norm` [neg1->1@80] ; `tetra_centre_norm` [lit2->3@18] ; `tetra_affineIndependent` [neg1->1@58] ; `tetra_affineIndependent` [neg1->1@62] ; `tetra_affineIndependent` [neg1->1@69] ; `tetra_affineIndependent` [neg1->1@76] ; `tetra_affineIndependent` [neg1->1@83] ; `tetra_affineIndependent` [neg1->1@87] ; `tetra_affineIndependent` [lit1->2@30] ; `tetra_affineIndependent` [lit1->2@33] 

satisfiability not certified (recorded as unresolved, not success): `bridge_B_eq_zero_iff_dist` (unresolved), `bridge_B_dist` (unresolved), `bridge_B_isExtTangent` (unresolved), `bridge_B_isIntTangent` (unresolved), `bridge_B_power` (unresolved), `bridge_power_eq_const_sphere` (unresolved), `bridge_power_eq_const_sphere_rho0` (unresolved), `bridge_pconst_neg_B` (unresolved), `bridge_equal_power_sphere` (unresolved), `B_comm` (unresolved), `B_add_right` (unresolved), `B_smul_right` (unresolved), `B_add_left` (unresolved), `B_smul_left` (unresolved), `tangency_identity` (unresolved), `tangency_of_B_eq_zero` (unresolved), `B_eq_zero_iff_tangent` (unresolved), `power_eq_const` (unresolved), `equal_power` (unresolved), `pt_affine_comb` (unresolved), `prop31` (unresolved), `dist_sq_const` (unresolved), `eq_zero_of_orth_affineIndependent` (unresolved), `simplex_E1` (unresolved), `simplex_circumradius` (unresolved), `tangency_identity` (unresolved), `tangency_of_B_eq_zero` (unresolved), `B_eq_zero_iff_tangent` (unresolved), `prop31` (unresolved), `prop31_cofactor` (unresolved)
LEANCHECK DONE Mon Nov 16 10:13:22 PM UTC 2026
