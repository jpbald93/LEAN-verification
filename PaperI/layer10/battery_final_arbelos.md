# leancheck — final_arbelos (2026-11-10 16:12 UTC)

- path: /Users/john/final_arbelos
- HEAD: 0dddc6e05fc14ad3d25325aecfc1ca225837ae6b
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'Arbelos.bridge_powC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Arbelos.bridge_exists_inversion_concentric' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (138 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Arbelos.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp_ext rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-11-10 08:58 PST

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 115, "mut": 321, "killed": 317, "surv": 4, "tout": 5, "contra": 0, "sat": 77, "unres": 38, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## final_arbelos
- theorems: 115
- step 1 mutants: 321 | killed 312 | killed-timeout 5 | SURVIVED 4 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 82 | no-hyp 33 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 77 | unresolved 37 | stmt-invalid 1 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `bridge_exists_inversion_concentric` [lit1->2@110] (heartbeat limit)
  - killed by timeout `l14_inversion_bigS` [lit2->3@24] (heartbeat limit)
  - killed by timeout `l14_inversion_bigS` [lit0->1@16] (heartbeat limit)
  - killed by timeout `l14_inversion_leftS` [lit2->3@24] (heartbeat limit)
  - killed by timeout `l14_inversion_leftS` [lit0->1@16] (heartbeat limit)
  - SURVIVED detail: 
  - SURVIVOR `l14w_twin` [lit3->4@12]: `(⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac` -> `(⟨⟨4 / 4, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac`
  - SURVIVED detail: 
  - SURVIVOR `l14w_twin` [lit4->5@8]: `(⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac` -> `(⟨⟨5 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac`
  - SURVIVED detail: 
  - SURVIVOR `l14w_twin` [lit2->3@15]: `(⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac` -> `(⟨⟨4 / 3, 3 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspac`
  - SURVIVED detail: 
  - SURVIVOR `twin_left_exists` [lit2->3@53]: `∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 2 * a ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s` -> `∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 3 * a ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s`
  - needs manual satisfiability check: `two_mul_volume_inter_upperHalf` (unresolved)
  - needs manual satisfiability check: `arbelos_area` (unresolved)
  - needs manual satisfiability check: `extTangentAt_eq` (unresolved)
  - needs manual satisfiability check: `incircle_eq` (unresolved)
  - needs manual satisfiability check: `bankoff` (unresolved)
  - needs manual satisfiability check: `bankoff_exists` (unresolved)
  - needs manual satisfiability check: `bankoff_center` (unresolved)
  - needs manual satisfiability check: `bridge_bankoff` (unresolved)
  - needs manual satisfiability check: `bridge_exists_inversion_concentric` (unresolved)
  - needs manual satisfiability check: `l14_twin_left` (unresolved)
  - needs manual satisfiability check: `l14_twin_right` (unresolved)
  - needs manual satisfiability check: `l14_arbelos_area` (unresolved)
  - needs manual satisfiability check: `l14_pappus_unique` (unresolved)
  - needs manual satisfiability check: `l14_bankoff` (unresolved)
  - needs manual satisfiability check: `l14h_mem_sphere` (stmt-invalid)
  - needs manual satisfiability check: `l14_steiner_porism` (unresolved)
  - needs manual satisfiability check: `eq_famCircle` (unresolved)
  - needs manual satisfiability check: `pappus_unique` (unresolved)
  - needs manual satisfiability check: `concentric_tangent` (unresolved)
  - needs manual satisfiability check: `steiner_concentric` (unresolved)
  - needs manual satisfiability check: `invSphere_center_sub` (unresolved)
  - needs manual satisfiability check: `invSphere_radius` (unresolved)
  - needs manual satisfiability check: `invSphere_sub_re` (unresolved)
  - needs manual satisfiability check: `invSphere_sub_im` (unresolved)
  - needs manual satisfiability check: `powC_invSphere` (unresolved)
  - needs manual satisfiability check: `invSphere_invSphere` (unresolved)
  - needs manual satisfiability check: `invSphere_isExtTangent` (unresolved)
  - needs manual satisfiability check: `invSphere_isIntTangent` (unresolved)
  - needs manual satisfiability check: `powC_pos_of_isIntTangent` (unresolved)
  - needs manual satisfiability check: `steiner_porism` (unresolved)
  - needs manual satisfiability check: `hasDisjointDiscs_iff` (unresolved)
  - needs manual satisfiability check: `invSphere_sep` (unresolved)
  - needs manual satisfiability check: `steiner_concentric_strong` (unresolved)
  - needs manual satisfiability check: `steiner_porism_strong` (unresolved)
  - needs manual satisfiability check: `steiner_porism_simple` (unresolved)
  - needs manual satisfiability check: `steiner_porism_disjoint` (unresolved)
  - needs manual satisfiability check: `twin_left` (unresolved)
  - needs manual satisfiability check: `twin_right` (unresolved)
  - no mutants generated (manual look): conj_mem_ball_iff, conj_mem_closedBall_iff, famCircle_tangent_big, famCircle_tangent_famCircle, famCircle_tangent_left, inversion_mem_invSphere_iff, l14h_mem_sphere, l14h_wbtw, l14w_bankoff, l14w_steiner_porism, measurableSet_upperHalf, pappus_tangent_big, pappus_tangent_left, rotSphere_injective

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 198 | UNUSED 1 | NEEDED 197 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `steiner_porism` : `(hs₀ : 0 < s₀.radius)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 9 files
linter (scratch): 0 warnings in 1 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (138 declarations, standard axioms only) |
| tamper (layer 2) | 7/7 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 9 of 9 files ok |
| conclusion mutations (layer 4) | **317/321 rejected** (312 by error, 5 by timeout/heartbeat); 4 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 82 probed ok — no-hyp 33 |
| satisfiability (layer 8) | 77/115 certified [46 with hypotheses, 21 hypothesis-free binders, 10 closed], 37 unresolved, 1 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 77/115 credited, 38 unresolved |
| hypothesis ablation (layer 6) | 197 needed, **1 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 9 files |
| linter, scratch (layer 7) | 0 warnings in 1 files |
| bridge inventory (layer 9) | 23 notions, 2 has-bridge, 21 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `steiner_porism`: (hs₀ : 0 < s₀.radius)

mutation survivors (classify by hand): `l14w_twin` [lit3->4@12] ; `l14w_twin` [lit4->5@8] ; `l14w_twin` [lit2->3@15] ; `twin_left_exists` [lit2->3@53] 

satisfiability not certified (recorded as unresolved, not success): `two_mul_volume_inter_upperHalf` (unresolved), `arbelos_area` (unresolved), `extTangentAt_eq` (unresolved), `incircle_eq` (unresolved), `bankoff` (unresolved), `bankoff_exists` (unresolved), `bankoff_center` (unresolved), `bridge_bankoff` (unresolved), `bridge_exists_inversion_concentric` (unresolved), `l14_twin_left` (unresolved), `l14_twin_right` (unresolved), `l14_arbelos_area` (unresolved), `l14_pappus_unique` (unresolved), `l14_bankoff` (unresolved), `l14h_mem_sphere` (stmt-invalid), `l14_steiner_porism` (unresolved), `eq_famCircle` (unresolved), `pappus_unique` (unresolved), `concentric_tangent` (unresolved), `steiner_concentric` (unresolved), `invSphere_center_sub` (unresolved), `invSphere_radius` (unresolved), `invSphere_sub_re` (unresolved), `invSphere_sub_im` (unresolved), `powC_invSphere` (unresolved), `invSphere_invSphere` (unresolved), `invSphere_isExtTangent` (unresolved), `invSphere_isIntTangent` (unresolved), `powC_pos_of_isIntTangent` (unresolved), `steiner_porism` (unresolved)
LEANCHECK DONE Tue Nov 10 17:20:39 UTC 2026
