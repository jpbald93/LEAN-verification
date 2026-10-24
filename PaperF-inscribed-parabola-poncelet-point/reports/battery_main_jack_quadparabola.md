# leancheck — quadparabola (2026-10-16 02:46 UTC)

- path: /home/jack/quadparabola
- HEAD: not a git repo
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.newton_perp_cr' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.newton_perp_orthoLine' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (92 declarations, standard axioms only)
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

Generated 2026-10-16 04:00 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 174, "mut": 375, "killed": 374, "surv": 1, "tout": 2, "contra": 0, "sat": 100, "unres": 74, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadparabola
- theorems: 174
- step 1 mutants: 375 | killed 372 | killed-timeout 2 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 141 | no-hyp 33 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 100 | unresolved 74 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [261]
  - SURVIVOR `orthocentres_not_all_eq'` [eq->ne@153]: `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) = ortho (mee` -> `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (mee`
  - killed by timeout `foot_shift0` [lit0->1@99] (heartbeat limit)
  - needs manual satisfiability check: `solve_A34` (unresolved)
  - needs manual satisfiability check: `circC_eq` (unresolved)
  - needs manual satisfiability check: `meet_eq_iff` (unresolved)
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
  - needs manual satisfiability check: `miquelPt_ne_vertices` (unresolved)
  - needs manual satisfiability check: `mul_conj_of_dist_eq` (unresolved)
  - needs manual satisfiability check: `A12_not_on_circ` (unresolved)
  - needs manual satisfiability check: `A12_not_mem_centres` (unresolved)
  - needs manual satisfiability check: `miquelPt_spec` (unresolved)
  - needs manual satisfiability check: `miquelPt_unique` (unresolved)
  - needs manual satisfiability check: `foot_mem` (unresolved)
  - needs manual satisfiability check: `eq_meet_of_foot_eq` (unresolved)
  - needs manual satisfiability check: `simson_feet_ne` (unresolved)
  - needs manual satisfiability check: `ortho34_eq_iff` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_affine` (unresolved)
  - needs manual satisfiability check: `diff_mem` (unresolved)
  - needs manual satisfiability check: `on_line` (unresolved)
  - needs manual satisfiability check: `not_mem_ne` (unresolved)
  - needs manual satisfiability check: `frame` (unresolved)
  - needs manual satisfiability check: `frame_pts` (unresolved)
  - needs manual satisfiability check: `circ_frame` (unresolved)
  - needs manual satisfiability check: `miquelPt_frame` (unresolved)
  - needs manual satisfiability check: `miquel_norm` (unresolved)
  - needs manual satisfiability check: `miquel` (unresolved)
  - needs manual satisfiability check: `steiner_circle_dist` (unresolved)
  - needs manual satisfiability check: `steiner_circle` (unresolved)
  - needs manual satisfiability check: `parab_frame` (unresolved)
  - needs manual satisfiability check: `dist_reflPt` (unresolved)
  - needs manual satisfiability check: `simson_dir_ne` (unresolved)
  - needs manual satisfiability check: `existsUnique_parabola` (unresolved)
  - needs manual satisfiability check: `orthoLine_eq` (unresolved)
  - needs manual satisfiability check: `mem_orthoLine` (unresolved)
  - needs manual satisfiability check: `infDist_orthoLine` (unresolved)
  - needs manual satisfiability check: `reflPt_cr` (unresolved)
  - needs manual satisfiability check: `reflections_collinear_orthos` (unresolved)
  - needs manual satisfiability check: `reflPt_mem_orthoLine` (unresolved)
  - needs manual satisfiability check: `reflections_collinear` (unresolved)
  - needs manual satisfiability check: `miquel_cr_ne` (unresolved)
  - needs manual satisfiability check: `miquel_not_mem_orthoLine` (unresolved)
  - needs manual satisfiability check: `line_not_perp` (unresolved)
  - needs manual satisfiability check: `parabola_tangent` (unresolved)
  - needs manual satisfiability check: `parabola_tangent₁` (unresolved)
  - needs manual satisfiability check: `parabola_tangent₂` (unresolved)
  - needs manual satisfiability check: `parabola_tangent₃` (unresolved)
  - needs manual satisfiability check: `parabola_tangent₄` (unresolved)
  - needs manual satisfiability check: `newton_frame` (unresolved)
  - needs manual satisfiability check: `newton_perp_cr` (unresolved)
  - needs manual satisfiability check: `newton_perp_orthoLine` (unresolved)
  - needs manual satisfiability check: `reflections_mem_affineSpan` (unresolved)
  - needs manual satisfiability check: `miquel_not_mem_affineSpan` (unresolved)
  - needs manual satisfiability check: `ortho_frame` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_all` (unresolved)
  - needs manual satisfiability check: `ortho12_ne_of_eq34` (unresolved)
  - needs manual satisfiability check: `orthocentres_not_all_eq'` (unresolved)
  - needs manual satisfiability check: `parallel_of_real_mul` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_line` (unresolved)
  - needs manual satisfiability check: `orthocentres_collinear'` (unresolved)
  - needs manual satisfiability check: `foot_eq` (unresolved)
  - needs manual satisfiability check: `feet_frame` (unresolved)
  - needs manual satisfiability check: `simson_cr` (unresolved)
  - needs manual satisfiability check: `simson` (unresolved)
  - needs manual satisfiability check: `steiner_parallel` (unresolved)
  - no mutants generated (manual look): collinear_of_cr, conc_iff, foot_mem, genPos_triangles, meet_mem_left, meet_mem_right, mem_of_collinear, miquel, miquel_not_mem_affineSpan, miquel_not_mem_orthoLine, not_collinear_iff_affineIndependent, orthocentres_collinear', parabola_tangent, parabola_tangent₁, parabola_tangent₂, parabola_tangent₃, parabola_tangent₄, parallel_of_real_mul, reflPt_mem_orthoLine, reflections_collinear, reflections_mem_affineSpan, simson, steiner_circle, steiner_parallel_affine, steiner_parallel_line

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 258 | UNUSED 17 | NEEDED 241 | SKIP 0 | timeout 0 | bad-control decls 0

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
linter (library): 0 warnings in 7 files
linter (scratch): 0 warnings in 3 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (92 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 7 of 7 files ok |
| conclusion mutations (layer 4) | **374/375 rejected** (372 by error, 2 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 141 probed ok — no-hyp 33 |
| satisfiability (layer 8) | 100/174 certified [68 with hypotheses, 32 hypothesis-free binders, 0 closed], 74 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 100/174 credited, 74 unresolved |
| hypothesis ablation (layer 6) | 241 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 7 files |
| linter, scratch (layer 7) | 0 warnings in 3 files, nonzero exit: scratch/alg.lean |
| bridge inventory (layer 9) | 15 notions, 1 has-bridge, 14 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

mutation survivors (classify by hand): `orthocentres_not_all_eq'` [eq->ne@153] own proof compiled; downstream errors at lines [261]

satisfiability not certified (recorded as unresolved, not success): `solve_A34` (unresolved), `circC_eq` (unresolved), `meet_eq_iff` (unresolved), `circ_den_ne` (unresolved), `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `centroid_triangle` (unresolved), `ortho_eq_orthocenter` (unresolved), `cr_of_collinear` (unresolved), `mem_of_collinear` (unresolved), `no123` (unresolved), `no124` (unresolved), `no134` (unresolved), `no234` (unresolved), `genPos_vertices_ne` (unresolved), `genPos_triangles` (unresolved), `miquelPt_ne_vertices` (unresolved), `mul_conj_of_dist_eq` (unresolved), `A12_not_on_circ` (unresolved), `A12_not_mem_centres` (unresolved), `miquelPt_spec` (unresolved), `miquelPt_unique` (unresolved), `foot_mem` (unresolved), `eq_meet_of_foot_eq` (unresolved), `simson_feet_ne` (unresolved), `ortho34_eq_iff` (unresolved), `steiner_parallel_affine` (unresolved), `diff_mem` (unresolved), `on_line` (unresolved), `not_mem_ne` (unresolved)
LEANCHECK DONE Fri Oct 16 04:55:08 AM UTC 2026
