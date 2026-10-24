# leancheck — quadrangle_ext (2026-10-19 18:10 UTC)

- path: ~/quadrangle_ext
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.poncelet_S4' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.poncelet_on_pedal_c'' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (106 declarations, standard axioms only)
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

Generated 2026-10-19 15:55 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 266, "mut": 553, "killed": 552, "surv": 1, "tout": 29, "contra": 0, "sat": 161, "unres": 105, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadrangle_ext
- theorems: 266
- step 1 mutants: 553 | killed 523 | killed-timeout 29 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 201 | no-hyp 65 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 161 | unresolved 105 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [261]
  - SURVIVOR `orthocentres_not_all_eq'` [eq->ne@153]: `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) = ortho (mee` -> `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (mee`
  - killed by timeout `nineC` [eq->ne@171] (heartbeat limit)
  - killed by timeout `nineC` [lit2->3@24] (heartbeat limit)
  - killed by timeout `nineC` [lit2->3@80] (heartbeat limit)
  - killed by timeout `nineC` [lit2->3@112] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@19] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@21] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@39] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@67] (heartbeat limit)
  - killed by timeout `diagC` [eq->ne@464] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@69] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@87] (heartbeat limit)
  - killed by timeout `diagC` [lit2->3@403] (heartbeat limit)
  - killed by timeout `diagC` [lit2->3@443] (heartbeat limit)
  - killed by timeout `nine0` [eq->ne@171] (heartbeat limit)
  - killed by timeout `nine0` [lit0->1@73] (heartbeat limit)
  - killed by timeout `radC` [eq->ne@485] (heartbeat limit)
  - killed by timeout `radC` [lit2->3@41] (heartbeat limit)
  - killed by timeout `radC` [lit0->1@54] (heartbeat limit)
  - killed by timeout `radC` [lit0->1@72] (heartbeat limit)
  - killed by timeout `footC_frac` [lit2->3@26] (heartbeat limit)
  - killed by timeout `footC_frac` [lit2->3@86] (heartbeat limit)
  - killed by timeout `pedK` [lit0->1@13] (heartbeat limit)
  - killed by timeout `pedK` [lit0->1@15] (heartbeat limit)
  - killed by timeout `pedK` [lit0->1@33] (heartbeat limit)
  - killed by timeout `diagK` [eq->ne@703] (heartbeat limit)
  - killed by timeout `diagK` [lit2->3@709] (heartbeat limit)
  - killed by timeout `crossC_ne` [lit0->1@45] (heartbeat limit)
  - killed by timeout `foot_shift0` [lit0->1@99] (heartbeat limit)
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
  - needs manual satisfiability check: `miquelPt_ne_vertices` (unresolved)
  - needs manual satisfiability check: `A12_not_on_circ` (unresolved)
  - needs manual satisfiability check: `A12_not_mem_centres` (unresolved)
  - needs manual satisfiability check: `miquelPt_spec` (unresolved)
  - needs manual satisfiability check: `foot_mem` (unresolved)
  - needs manual satisfiability check: `miquelPt_unique` (unresolved)
  - needs manual satisfiability check: `foot_perp` (unresolved)
  - needs manual satisfiability check: `eq_meet_of_foot_eq` (unresolved)
  - needs manual satisfiability check: `simson_feet_ne` (unresolved)
  - needs manual satisfiability check: `ortho34_eq_iff` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_affine` (unresolved)
  - needs manual satisfiability check: `parallel_iff_cr` (unresolved)
  - needs manual satisfiability check: `conc_iff` (unresolved)
  - needs manual satisfiability check: `diff_mem` (unresolved)
  - needs manual satisfiability check: `on_line` (unresolved)
  - needs manual satisfiability check: `frame` (unresolved)
  - needs manual satisfiability check: `frame_pts` (unresolved)
  - needs manual satisfiability check: `miquelPt_frame` (unresolved)
  - needs manual satisfiability check: `circ_frame` (unresolved)
  - needs manual satisfiability check: `miquel_norm` (unresolved)
  - needs manual satisfiability check: `miquel` (unresolved)
  - needs manual satisfiability check: `steiner_circle_dist` (unresolved)
  - needs manual satisfiability check: `steiner_circle` (unresolved)
  - needs manual satisfiability check: `ortho_frame` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_all` (unresolved)
  - needs manual satisfiability check: `ortho12_ne_of_eq34` (unresolved)
  - needs manual satisfiability check: `orthocentres_not_all_eq'` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_line` (unresolved)
  - needs manual satisfiability check: `orthocentres_collinear'` (unresolved)
  - needs manual satisfiability check: `npc_eq_ninePointCircle_center` (unresolved)
  - needs manual satisfiability check: `ninePointCircle_radius_eq` (unresolved)
  - needs manual satisfiability check: `uniq_lin` (unresolved)
  - needs manual satisfiability check: `K_ne_of_cr` (unresolved)
  - needs manual satisfiability check: `ne_zero_of_cr_left` (unresolved)
  - needs manual satisfiability check: `ne_zero_of_cr_right` (unresolved)
  - needs manual satisfiability check: `frame_of_QGen` (unresolved)
  - needs manual satisfiability check: `pD_conj_ne` (unresolved)
  - needs manual satisfiability check: `dist_frame` (unresolved)
  - needs manual satisfiability check: `kxy_form` (unresolved)
  - needs manual satisfiability check: `kxy_form'` (unresolved)
  - needs manual satisfiability check: `frame_swap` (unresolved)
  - needs manual satisfiability check: `frame_cyc` (unresolved)
  - needs manual satisfiability check: `nine_frame_d` (unresolved)
  - needs manual satisfiability check: `nine_frame_0` (unresolved)
  - needs manual satisfiability check: `QGen.ncol_abc` (unresolved)
  - needs manual satisfiability check: `QGen.ncol_abd` (unresolved)
  - needs manual satisfiability check: `QGen.ncol_acd` (unresolved)
  - needs manual satisfiability check: `QGen.ncol_bcd` (unresolved)
  - needs manual satisfiability check: `frame_of_QGen'` (unresolved)
  - needs manual satisfiability check: `frame_prod` (unresolved)
  - needs manual satisfiability check: `ponDen_eq_zero_iff` (unresolved)
  - needs manual satisfiability check: `ponDen_ne` (unresolved)
  - needs manual satisfiability check: `poncelet_on_ninepoint` (unresolved)
  - needs manual satisfiability check: `ninepoint_concur` (unresolved)
  - needs manual satisfiability check: `mem_ninePointCircle_iff` (unresolved)
  - needs manual satisfiability check: `pow_of_dist` (unresolved)
  - needs manual satisfiability check: `ninepoint_unique` (unresolved)
  - needs manual satisfiability check: `cospherical_of_crossC` (unresolved)
  - needs manual satisfiability check: `orthocentric_npc_eq` (unresolved)
  - needs manual satisfiability check: `cosph_shift` (unresolved)
  - needs manual satisfiability check: `crossC_ne` (unresolved)
  - needs manual satisfiability check: `Frame.x_ne` (unresolved)
  - needs manual satisfiability check: `Frame.y_ne` (unresolved)
  - needs manual satisfiability check: `Frame.yx` (unresolved)
  - needs manual satisfiability check: `Frame.z_ne` (unresolved)
  - needs manual satisfiability check: `Frame.zx` (unresolved)
  - needs manual satisfiability check: `Frame.zy` (unresolved)
  - needs manual satisfiability check: `pedal_frame_d` (unresolved)
  - needs manual satisfiability check: `pedal_frame_z` (unresolved)
  - needs manual satisfiability check: `poncelet_on_pedal_c` (unresolved)
  - needs manual satisfiability check: `poncelet_on_pedal_d` (unresolved)
  - needs manual satisfiability check: `poncelet_on_pedal_b` (unresolved)
  - needs manual satisfiability check: `poncelet_on_pedal_a` (unresolved)
  - needs manual satisfiability check: `meet_lineThrough` (unresolved)
  - needs manual satisfiability check: `cr_ne_of_not_parallel` (unresolved)
  - needs manual satisfiability check: `diagPt_frame` (unresolved)
  - needs manual satisfiability check: `lin_frac` (unresolved)
  - needs manual satisfiability check: `poncelet_on_diagonal_circle` (unresolved)
  - needs manual satisfiability check: `QGen.swap_cd` (unresolved)
  - needs manual satisfiability check: `ortho_swap_iff` (unresolved)
  - needs manual satisfiability check: `orthocentric_ninePointCircle_eq` (unresolved)
  - needs manual satisfiability check: `poncelet_swap_cd_of_ne` (unresolved)
  - needs manual satisfiability check: `poncelet_swap_cd` (unresolved)
  - needs manual satisfiability check: `poncelet_S4` (unresolved)
  - needs manual satisfiability check: `poncelet_on_pedal_c'` (unresolved)
  - needs manual satisfiability check: `foot_eq` (unresolved)
  - needs manual satisfiability check: `feet_frame` (unresolved)
  - needs manual satisfiability check: `simson_cr` (unresolved)
  - needs manual satisfiability check: `simson` (unresolved)
  - needs manual satisfiability check: `steiner_parallel` (unresolved)
  - no mutants generated (manual look): QGen.ncol_abc, QGen.ncol_abd, QGen.ncol_acd, QGen.ncol_bcd, QGen.swap_cd, collinear_of_cr, conc_iff, cosph_shift, cospherical_of_crossC, foot_mem, frame_cyc, frame_of_QGen, frame_of_QGen', frame_swap, genPos_triangles, meet_mem_left, meet_mem_right, mem_of_collinear, miquel, ncol_of_cr, ninepoint_concur, not_collinear_iff_affineIndependent, orthocentres_collinear', parallel_of_real_mul, pedal_frame_d, pedal_frame_z, poncelet_on_diagonal_circle, poncelet_on_pedal_a, poncelet_on_pedal_b, poncelet_on_pedal_c, poncelet_on_pedal_c', poncelet_on_pedal_d, simson, steiner_circle, steiner_parallel_affine, steiner_parallel_line

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 395 | UNUSED 17 | NEEDED 378 | SKIP 0 | timeout 0 | bad-control decls 0

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
linter (library): 0 warnings in 8 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (106 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 8 of 8 files ok |
| conclusion mutations (layer 4) | **552/553 rejected** (523 by error, 29 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 201 probed ok — no-hyp 65 |
| satisfiability (layer 8) | 161/266 certified [97 with hypotheses, 62 hypothesis-free binders, 2 closed], 105 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 161/266 credited, 105 unresolved |
| hypothesis ablation (layer 6) | 378 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 8 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 22 notions, 3 has-bridge, 19 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

mutation survivors (classify by hand): `orthocentres_not_all_eq'` [eq->ne@153] own proof compiled; downstream errors at lines [261]

satisfiability not certified (recorded as unresolved, not success): `solve_A34` (unresolved), `circC_eq` (unresolved), `circ_den_ne` (unresolved), `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `centroid_triangle` (unresolved), `ortho_eq_orthocenter` (unresolved), `cr_of_collinear` (unresolved), `mem_of_collinear` (unresolved), `no123` (unresolved), `no124` (unresolved), `no134` (unresolved), `no234` (unresolved), `genPos_vertices_ne` (unresolved), `genPos_triangles` (unresolved), `miquelPt_ne_vertices` (unresolved), `A12_not_on_circ` (unresolved), `A12_not_mem_centres` (unresolved), `miquelPt_spec` (unresolved), `foot_mem` (unresolved), `miquelPt_unique` (unresolved), `foot_perp` (unresolved), `eq_meet_of_foot_eq` (unresolved), `simson_feet_ne` (unresolved), `ortho34_eq_iff` (unresolved), `steiner_parallel_affine` (unresolved), `parallel_iff_cr` (unresolved), `conc_iff` (unresolved), `diff_mem` (unresolved), `on_line` (unresolved)
LEANCHECK DONE Tue Oct 20 02:10:58 UTC 2026
