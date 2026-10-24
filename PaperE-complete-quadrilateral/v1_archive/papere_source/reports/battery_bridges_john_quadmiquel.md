# leancheck — quadmiquel (2026-10-15 13:49 UTC)

- path: ~/quadmiquel
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.foot_perp' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.mem_line_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (51 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: QuadMiquel.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-15 07:50 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 128, "mut": 259, "killed": 259, "surv": 0, "tout": 2, "contra": 0, "sat": 83, "unres": 45, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadmiquel
- theorems: 128
- step 1 mutants: 259 | killed 257 | killed-timeout 2 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 97 | no-hyp 31 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 83 | unresolved 45 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - killed by timeout `foot_shift0` [lit0->1@99] (heartbeat limit)
  - needs manual satisfiability check: `fr_one` (unresolved)
  - needs manual satisfiability check: `solve_A34` (unresolved)
  - needs manual satisfiability check: `circC_eq` (unresolved)
  - needs manual satisfiability check: `circ_den_ne` (unresolved)
  - needs manual satisfiability check: `circ_dist` (unresolved)
  - needs manual satisfiability check: `circ_eq_circumcenter` (unresolved)
  - needs manual satisfiability check: `centroid_triangle` (unresolved)
  - needs manual satisfiability check: `ortho_eq_orthocenter` (unresolved)
  - needs manual satisfiability check: `cr_of_collinear` (unresolved)
  - needs manual satisfiability check: `mem_of_collinear` (unresolved)
  - needs manual satisfiability check: `no123` (unresolved)
  - needs manual satisfiability check: `no124` (unresolved)
  - needs manual satisfiability check: `no134` (unresolved)
  - needs manual satisfiability check: `no234` (unresolved)
  - needs manual satisfiability check: `genPos_vertices_ne` (unresolved)
  - needs manual satisfiability check: `genPos_triangles` (unresolved)
  - needs manual satisfiability check: `mul_conj_of_dist_eq` (unresolved)
  - needs manual satisfiability check: `miquelPt_ne_vertices` (unresolved)
  - needs manual satisfiability check: `A12_not_on_circ` (unresolved)
  - needs manual satisfiability check: `A12_not_mem_centres` (unresolved)
  - needs manual satisfiability check: `miquelPt_spec` (unresolved)
  - needs manual satisfiability check: `miquelPt_unique` (unresolved)
  - needs manual satisfiability check: `foot_mem` (unresolved)
  - needs manual satisfiability check: `foot_perp` (unresolved)
  - needs manual satisfiability check: `eq_zero_of_perp` (unresolved)
  - needs manual satisfiability check: `eq_meet_of_foot_eq` (unresolved)
  - needs manual satisfiability check: `simson_feet_ne` (unresolved)
  - needs manual satisfiability check: `ortho34_eq_iff` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_affine` (unresolved)
  - needs manual satisfiability check: `diff_mem` (unresolved)
  - needs manual satisfiability check: `on_line` (unresolved)
  - needs manual satisfiability check: `not_mem_ne` (unresolved)
  - needs manual satisfiability check: `frame_pts` (unresolved)
  - needs manual satisfiability check: `frame` (unresolved)
  - needs manual satisfiability check: `miquelPt_frame` (unresolved)
  - needs manual satisfiability check: `circ_frame` (unresolved)
  - needs manual satisfiability check: `miquel_norm` (unresolved)
  - needs manual satisfiability check: `miquel` (unresolved)
  - needs manual satisfiability check: `steiner_circle_dist` (unresolved)
  - needs manual satisfiability check: `steiner_circle` (unresolved)
  - needs manual satisfiability check: `foot_eq` (unresolved)
  - needs manual satisfiability check: `feet_frame` (unresolved)
  - needs manual satisfiability check: `simson_cr` (unresolved)
  - needs manual satisfiability check: `simson` (unresolved)
  - needs manual satisfiability check: `steiner_parallel` (unresolved)
  - no mutants generated (manual look): collinear_of_cr, conc_iff, foot_mem, genPos_triangles, meet_mem_left, meet_mem_right, mem_of_collinear, miquel, not_collinear_iff_affineIndependent, simson, steiner_circle, steiner_parallel_affine

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 204 | UNUSED 17 | NEEDED 187 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `circC_T4` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `circC_T3` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `circC_scaled` : `(hq : q ≠ 0)`
- UNUSED `circC_scaled` : `(hD : B * γ - β * G ≠ 0)`
- UNUSED `simF2` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF2` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF2` : `(hE : s * U - t * V - U + V ≠ 0)`
- UNUSED `simF2` : `(hu : u ≠ 0)`
- UNUSED `simF2` : `(hv : v ≠ 0)`
- UNUSED `simF3` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF3` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF3` : `(hu : u ≠ 0)`
- UNUSED `simF3` : `(huv : v - u ≠ 0)`
- UNUSED `simF4` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF4` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF4` : `(hu : u ≠ 0)`
- UNUSED `simF4` : `(h4 : t * v - s * u ≠ 0)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 5 files
linter (scratch): 0 warnings in 5 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (51 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 5 of 5 files ok |
| conclusion mutations (layer 4) | **259/259 rejected** (257 by error, 2 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 97 probed ok — no-hyp 31 |
| satisfiability (layer 8) | 83/128 certified [53 with hypotheses, 30 hypothesis-free binders, 0 closed], 45 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 83/128 credited, 45 unresolved |
| hypothesis ablation (layer 6) | 187 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 5 files |
| linter, scratch (layer 7) | 0 warnings in 5 files, nonzero exit: scratch/Core.lean |
| bridge inventory (layer 9) | 11 notions, 1 has-bridge, 10 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

satisfiability not certified (recorded as unresolved, not success): `fr_one` (unresolved), `solve_A34` (unresolved), `circC_eq` (unresolved), `circ_den_ne` (unresolved), `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `centroid_triangle` (unresolved), `ortho_eq_orthocenter` (unresolved), `cr_of_collinear` (unresolved), `mem_of_collinear` (unresolved), `no123` (unresolved), `no124` (unresolved), `no134` (unresolved), `no234` (unresolved), `genPos_vertices_ne` (unresolved), `genPos_triangles` (unresolved), `mul_conj_of_dist_eq` (unresolved), `miquelPt_ne_vertices` (unresolved), `A12_not_on_circ` (unresolved), `A12_not_mem_centres` (unresolved), `miquelPt_spec` (unresolved), `miquelPt_unique` (unresolved), `foot_mem` (unresolved), `foot_perp` (unresolved), `eq_zero_of_perp` (unresolved), `eq_meet_of_foot_eq` (unresolved), `simson_feet_ne` (unresolved), `ortho34_eq_iff` (unresolved), `steiner_parallel_affine` (unresolved), `diff_mem` (unresolved)
LEANCHECK DONE Thu Oct 15 15:28:54 UTC 2026
