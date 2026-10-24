# leancheck — quadrangle_final (2026-10-21 18:48 UTC)

- path: ~/quadrangle_final
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.Classical.degen_of_k0' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.Classical.cov_classical_D1_d' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (220 declarations, standard axioms only)
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

Generated 2026-10-21 17:10 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 380, "mut": 798, "killed": 797, "surv": 1, "tout": 38, "contra": 0, "sat": 186, "unres": 194, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadrangle_final
- theorems: 380
- step 1 mutants: 798 | killed 759 | killed-timeout 38 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 278 | no-hyp 102 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 186 | unresolved 194 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - killed by timeout `setup_i` [lit0->1@43] (heartbeat limit)
  - killed by timeout `setup_i` [lit1->2@68] (heartbeat limit)
  - killed by timeout `diagV_eq` [lit0->1@45] (heartbeat limit)
  - killed by timeout `diagV_eq` [lit1->2@58] (heartbeat limit)
  - killed by timeout `feet_ne` [ne->eq@63] (heartbeat limit)
  - killed by timeout `foot_orth` [lit0->1@36] (heartbeat limit)
  - killed by timeout `foot_orth` [lit1->2@59] (heartbeat limit)
  - killed by timeout `d3_feet_ne` [lit2->3@66] (heartbeat limit)
  - killed by timeout `d3_feet_ne` [lit1->2@40] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [261]
  - SURVIVOR `orthocentres_not_all_eq'` [eq->ne@153]: `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) = ortho (mee` -> `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (mee`
  - killed by timeout `nineC` [lit2->3@24] (heartbeat limit)
  - killed by timeout `nineC` [eq->ne@171] (heartbeat limit)
  - killed by timeout `nineC` [lit2->3@112] (heartbeat limit)
  - killed by timeout `nineC` [lit2->3@80] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@21] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@19] (heartbeat limit)
  - killed by timeout `pedC` [lit0->1@39] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@67] (heartbeat limit)
  - killed by timeout `diagC` [eq->ne@464] (heartbeat limit)
  - killed by timeout `diagC` [lit2->3@403] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@87] (heartbeat limit)
  - killed by timeout `pedC'` [lit0->1@69] (heartbeat limit)
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
  - needs manual satisfiability check: `eq_meet_of_foot_eq` (unresolved)
  - needs manual satisfiability check: `simson_feet_ne` (unresolved)
  - needs manual satisfiability check: `ortho34_eq_iff` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_affine` (unresolved)
  - needs manual satisfiability check: `conc_iff` (unresolved)
  - needs manual satisfiability check: `diff_mem` (unresolved)
  - needs manual satisfiability check: `on_line` (unresolved)
  - needs manual satisfiability check: `not_mem_ne` (unresolved)
  - needs manual satisfiability check: `frame_pts` (unresolved)
  - needs manual satisfiability check: `frame` (unresolved)
  - needs manual satisfiability check: `l14b_cr_ne` (unresolved)
  - needs manual satisfiability check: `l14b_QGen` (unresolved)
  - needs manual satisfiability check: `l14b_tri` (unresolved)
  - needs manual satisfiability check: `l14b_orthocenter` (unresolved)
  - needs manual satisfiability check: `l14b_mem_npc` (unresolved)
  - needs manual satisfiability check: `l14b_npc` (unresolved)
  - needs manual satisfiability check: `l14b_diag` (unresolved)
  - needs manual satisfiability check: `l14b_ne_of_ncol` (unresolved)
  - needs manual satisfiability check: `l14b_range3` (unresolved)
  - needs manual satisfiability check: `l14b_ninePointCircle_eq_of_range_eq` (unresolved)
  - needs manual satisfiability check: `l14b_cosph` (unresolved)
  - needs manual satisfiability check: `l14b_range_sub` (unresolved)
  - needs manual satisfiability check: `l14b_tri_cases` (unresolved)
  - needs manual satisfiability check: `l14b_transfer` (unresolved)
  - needs manual satisfiability check: `l14b_poncelet_mem` (unresolved)
  - needs manual satisfiability check: `l14b_poncelet_eq` (unresolved)
  - needs manual satisfiability check: `l14_ninepoint_concur` (unresolved)
  - needs manual satisfiability check: `l14_ninepoint_unique` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_ninepoint` (unresolved)
  - needs manual satisfiability check: `l14_orthocentric_ninePointCircle_eq` (unresolved)
  - needs manual satisfiability check: `l14_ponDen_eq_zero_iff` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_pedal_d` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_pedal_c` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_pedal_b` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_pedal_a` (unresolved)
  - needs manual satisfiability check: `l14_poncelet_on_diagonal_circle` (unresolved)
  - needs manual satisfiability check: `l14b_npc_center` (unresolved)
  - needs manual satisfiability check: `tp3` (unresolved)
  - needs manual satisfiability check: `tp2` (unresolved)
  - needs manual satisfiability check: `tp1` (unresolved)
  - needs manual satisfiability check: `tp0` (unresolved)
  - needs manual satisfiability check: `tpi` (unresolved)
  - needs manual satisfiability check: `ncol_of_pts` (unresolved)
  - needs manual satisfiability check: `ncol_perm` (unresolved)
  - needs manual satisfiability check: `ncolQ` (unresolved)
  - needs manual satisfiability check: `rangeQ` (unresolved)
  - needs manual satisfiability check: `onNPC_iff` (unresolved)
  - needs manual satisfiability check: `tri_sub` (unresolved)
  - needs manual satisfiability check: `range_tri_eq` (unresolved)
  - needs manual satisfiability check: `pall` (unresolved)
  - needs manual satisfiability check: `setup_i` (unresolved)
  - needs manual satisfiability check: `sub4` (unresolved)
  - needs manual satisfiability check: `diag_ncol` (unresolved)
  - needs manual satisfiability check: `intersection_mem` (unresolved)
  - needs manual satisfiability check: `diagV_eq` (unresolved)
  - needs manual satisfiability check: `qgen` (unresolved)
  - needs manual satisfiability check: `meets` (unresolved)
  - needs manual satisfiability check: `diagonal_triangle_independent` (unresolved)
  - needs manual satisfiability check: `top_span` (unresolved)
  - needs manual satisfiability check: `ncol_eq` (unresolved)
  - needs manual satisfiability check: `circ_of_dist` (unresolved)
  - needs manual satisfiability check: `onCirc_of_cosph` (unresolved)
  - needs manual satisfiability check: `cosph_of_onCirc` (unresolved)
  - needs manual satisfiability check: `foot_vertex` (unresolved)
  - needs manual satisfiability check: `feet_ne` (unresolved)
  - needs manual satisfiability check: `pedalFeet_eq` (unresolved)
  - needs manual satisfiability check: `span_face` (unresolved)
  - needs manual satisfiability check: `d3_of_cosph` (unresolved)
  - needs manual satisfiability check: `foot_orth` (unresolved)
  - needs manual satisfiability check: `foot_mem_vertex_orth` (unresolved)
  - needs manual satisfiability check: `foot_mem_face` (unresolved)
  - needs manual satisfiability check: `cov_classical_D1_a` (unresolved)
  - needs manual satisfiability check: `cov_classical_D1_b` (unresolved)
  - needs manual satisfiability check: `cov_classical_D2` (unresolved)
  - needs manual satisfiability check: `orth_core` (unresolved)
  - needs manual satisfiability check: `cov_classical_D5_a` (unresolved)
  - needs manual satisfiability check: `d3_cosph_nonorth` (unresolved)
  - needs manual satisfiability check: `cov_classical_D5_b` (unresolved)
  - needs manual satisfiability check: `d3_feet_ne` (unresolved)
  - needs manual satisfiability check: `orth_xy` (unresolved)
  - needs manual satisfiability check: `orth_xz` (unresolved)
  - needs manual satisfiability check: `orth_yz` (unresolved)
  - needs manual satisfiability check: `conic_core` (unresolved)
  - needs manual satisfiability check: `tpar_generic` (unresolved)
  - needs manual satisfiability check: `dist_mc` (unresolved)
  - needs manual satisfiability check: `orth_all` (unresolved)
  - needs manual satisfiability check: `tpar_orth` (unresolved)
  - needs manual satisfiability check: `d3_cosph_orth` (unresolved)
  - needs manual satisfiability check: `d3_cosph` (unresolved)
  - needs manual satisfiability check: `cov_classical_D3_a` (unresolved)
  - needs manual satisfiability check: `cov_classical_D3_b` (unresolved)
  - needs manual satisfiability check: `cov_classical_D4` (unresolved)
  - needs manual satisfiability check: `d1c_of_tpar` (unresolved)
  - needs manual satisfiability check: `cov_classical_D1_c` (unresolved)
  - needs manual satisfiability check: `degen_of_k0` (unresolved)
  - needs manual satisfiability check: `degen_of` (unresolved)
  - needs manual satisfiability check: `cov_classical_D1_d` (unresolved)
  - needs manual satisfiability check: `miquel_den` (unresolved)
  - needs manual satisfiability check: `miquel_den'` (unresolved)
  - needs manual satisfiability check: `circ_frame` (unresolved)
  - needs manual satisfiability check: `miquelPt_frame` (unresolved)
  - needs manual satisfiability check: `miquel_norm` (unresolved)
  - needs manual satisfiability check: `miquel` (unresolved)
  - needs manual satisfiability check: `steiner_circle_dist` (unresolved)
  - needs manual satisfiability check: `steiner_circle` (unresolved)
  - needs manual satisfiability check: `ortho_frame` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_all` (unresolved)
  - needs manual satisfiability check: `ortho12_ne_of_eq34` (unresolved)
  - needs manual satisfiability check: `orthocentres_not_all_eq'` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_line` (unresolved)
  - needs manual satisfiability check: `parallel_of_real_mul` (unresolved)
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
## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 538 | UNUSED 17 | NEEDED 521 | SKIP 0 | timeout 0 | bad-control decls 0

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
linter (library): 0 warnings in 10 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (220 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 10 of 10 files ok |
| conclusion mutations (layer 4) | **797/798 rejected** (759 by error, 38 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 278 probed ok — no-hyp 102 |
| satisfiability (layer 8) | 186/380 certified [105 with hypotheses, 71 hypothesis-free binders, 10 closed], 194 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 186/380 credited, 194 unresolved |
| hypothesis ablation (layer 6) | 521 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 10 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 54 notions, 10 has-bridge, 44 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

mutation survivors (classify by hand): `orthocentres_not_all_eq'` [eq->ne@153] own proof compiled; downstream errors at lines [261]

satisfiability not certified (recorded as unresolved, not success): `solve_A34` (unresolved), `circC_eq` (unresolved), `circ_den_ne` (unresolved), `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `centroid_triangle` (unresolved), `ortho_eq_orthocenter` (unresolved), `cr_of_collinear` (unresolved), `mem_of_collinear` (unresolved), `no123` (unresolved), `no124` (unresolved), `no134` (unresolved), `no234` (unresolved), `genPos_vertices_ne` (unresolved), `genPos_triangles` (unresolved), `miquelPt_ne_vertices` (unresolved), `A12_not_on_circ` (unresolved), `A12_not_mem_centres` (unresolved), `miquelPt_spec` (unresolved), `foot_mem` (unresolved), `miquelPt_unique` (unresolved), `eq_meet_of_foot_eq` (unresolved), `simson_feet_ne` (unresolved), `ortho34_eq_iff` (unresolved), `steiner_parallel_affine` (unresolved), `conc_iff` (unresolved), `diff_mem` (unresolved), `on_line` (unresolved), `not_mem_ne` (unresolved), `frame_pts` (unresolved)
LEANCHECK DONE Thu Oct 22 03:55:02 UTC 2026
