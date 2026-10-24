# leancheck — quadparabola_final (2026-10-22 03:55 UTC)

- path: ~/quadparabola_final
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.Classical.classical_C7_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.Classical.classical_C7_b' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (240 declarations, standard axioms only)
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

Generated 2026-10-22 00:26 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 324, "mut": 710, "killed": 709, "surv": 1, "tout": 2, "contra": 0, "sat": 126, "unres": 198, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadparabola_final
- theorems: 324
- step 1 mutants: 710 | killed 707 | killed-timeout 2 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 220 | no-hyp 104 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 126 | unresolved 198 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [261]
  - SURVIVOR `orthocentres_not_all_eq'` [eq->ne@153]: `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) = ortho (mee` -> `¬ (ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (mee`
  - killed by timeout `foot_shift0` [lit0->1@99] (heartbeat limit)
  - needs manual satisfiability check: `fr_frac` (unresolved)
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
  - needs manual satisfiability check: `eq_meet_of_foot_eq` (unresolved)
  - needs manual satisfiability check: `simson_feet_ne` (unresolved)
  - needs manual satisfiability check: `ortho34_eq_iff` (unresolved)
  - needs manual satisfiability check: `steiner_parallel_affine` (unresolved)
  - needs manual satisfiability check: `parallel_iff_cr` (unresolved)
  - needs manual satisfiability check: `diff_mem` (unresolved)
  - needs manual satisfiability check: `on_line` (unresolved)
  - needs manual satisfiability check: `not_mem_ne` (unresolved)
  - needs manual satisfiability check: `frame_pts` (unresolved)
  - needs manual satisfiability check: `frame` (unresolved)
  - needs manual satisfiability check: `l14b_genPos` (unresolved)
  - needs manual satisfiability check: `l14b_meet` (unresolved)
  - needs manual satisfiability check: `l14b_setup` (unresolved)
  - needs manual satisfiability check: `l14b_tri` (unresolved)
  - needs manual satisfiability check: `l14b_orthocenter` (unresolved)
  - needs manual satisfiability check: `l14b_circumcenter` (unresolved)
  - needs manual satisfiability check: `l14b_mem_circumsphere` (unresolved)
  - needs manual satisfiability check: `l14b_setupT` (unresolved)
  - needs manual satisfiability check: `l14b_miquel` (unresolved)
  - needs manual satisfiability check: `l14b_miquel_mem` (unresolved)
  - needs manual satisfiability check: `l14b_finrank` (unresolved)
  - needs manual satisfiability check: `l14b_tanPt_proj` (unresolved)
  - needs manual satisfiability check: `l14b_vertex_eq` (unresolved)
  - needs manual satisfiability check: `l14b_vertex` (unresolved)
  - needs manual satisfiability check: `l14b_nearest_unique` (unresolved)
  - needs manual satisfiability check: `l14b_noconc` (unresolved)
  - needs manual satisfiability check: `l14_newton_perp_orthoLine` (unresolved)
  - needs manual satisfiability check: `l14_directrix_finrank` (unresolved)
  - needs manual satisfiability check: `l14_miquel_existsUnique` (unresolved)
  - needs manual satisfiability check: `l14_lambert` (unresolved)
  - needs manual satisfiability check: `l14_miquel_not_mem_orthoLine` (unresolved)
  - needs manual satisfiability check: `l14_reflPt_mem_orthoLine` (unresolved)
  - needs manual satisfiability check: `l14_parabola_tangent` (unresolved)
  - needs manual satisfiability check: `l14_parabola_tangent₁` (unresolved)
  - needs manual satisfiability check: `l14_parabola_tangent₂` (unresolved)
  - needs manual satisfiability check: `l14_parabola_tangent₃` (unresolved)
  - needs manual satisfiability check: `l14_parabola_tangent₄` (unresolved)
  - needs manual satisfiability check: `l14_tanPt_all` (unresolved)
  - needs manual satisfiability check: `l14_vertex` (unresolved)
  - needs manual satisfiability check: `l14_vertex_onParabola` (unresolved)
  - needs manual satisfiability check: `l14_dist_vertex` (unresolved)
  - needs manual satisfiability check: `l14_vertex_closest` (unresolved)
  - needs manual satisfiability check: `l14b_transfer` (unresolved)
  - needs manual satisfiability check: `l15_cr_ne` (unresolved)
  - needs manual satisfiability check: `l15_meet_spec` (unresolved)
  - needs manual satisfiability check: `l15_meet_eq` (unresolved)
  - needs manual satisfiability check: `l15_meet_comm` (unresolved)
  - needs manual satisfiability check: `l15_range_tv` (unresolved)
  - needs manual satisfiability check: `l15_tris` (unresolved)
  - needs manual satisfiability check: `l15_indep_of_range` (unresolved)
  - needs manual satisfiability check: `quadrilateral_triangle_independent` (unresolved)
  - needs manual satisfiability check: `l15_circumsphere_eq` (unresolved)
  - needs manual satisfiability check: `l15_onCirc_iff` (unresolved)
  - needs manual satisfiability check: `l15_tri_range` (unresolved)
  - needs manual satisfiability check: `l15_miquel_iff` (unresolved)
  - needs manual satisfiability check: `cov_classical_C1` (unresolved)
  - needs manual satisfiability check: `l15_ortho_range` (unresolved)
  - needs manual satisfiability check: `l15_setup` (unresolved)
  - needs manual satisfiability check: `l15_isLine_finrank` (unresolved)
  - needs manual satisfiability check: `l15_orthoLine_isLine` (unresolved)
  - needs manual satisfiability check: `l15_eq_of_le` (unresolved)
  - needs manual satisfiability check: `l15_orthoLine_unique` (unresolved)
  - needs manual satisfiability check: `cov_classical_C2` (unresolved)
  - needs manual satisfiability check: `cov_classical_C3` (unresolved)
  - needs manual satisfiability check: `cov_classical_C4_c` (unresolved)
  - needs manual satisfiability check: `l15_foot_spec` (unresolved)
  - needs manual satisfiability check: `l15_foot_eq` (unresolved)
  - needs manual satisfiability check: `l15_dir_mem` (unresolved)
  - needs manual satisfiability check: `l15_focus_ne_foot` (unresolved)
  - needs manual satisfiability check: `cov_classical_C5_a` (unresolved)
  - needs manual satisfiability check: `l15_not_parallel_axis` (unresolved)
  - needs manual satisfiability check: `l15_infDist_eq` (unresolved)
  - needs manual satisfiability check: `l15_vertex_foot` (unresolved)
  - needs manual satisfiability check: `l15_vertex_dists` (unresolved)
  - needs manual satisfiability check: `cov_classical_C7_a` (unresolved)
  - needs manual satisfiability check: `cov_classical_C7_b` (unresolved)
  - needs manual satisfiability check: `l15_dirLine_carrier` (unresolved)
  - needs manual satisfiability check: `l15_lines_not_parallel_axis` (unresolved)
  - needs manual satisfiability check: `l15_inscribed` (unresolved)
  - needs manual satisfiability check: `l15_parabola_dir_isOrtho` (unresolved)
  - needs manual satisfiability check: `cov_classical_C4_a` (unresolved)
  - needs manual satisfiability check: `cov_classical_C4_b_part` (unresolved)
  - needs manual satisfiability check: `cov_classical_C6_b_part` (unresolved)
  - needs manual satisfiability check: `cov_classical_C5_b_part` (unresolved)
  - needs manual satisfiability check: `l15_quad` (unresolved)
  - needs manual satisfiability check: `l15_disc_real` (unresolved)
  - needs manual satisfiability check: `l15_mem_dir` (unresolved)
  - needs manual satisfiability check: `l15_tangent_refl` (unresolved)
  - needs manual satisfiability check: `l15_c6_alg` (unresolved)
  - needs manual satisfiability check: `cov_classical_C6_a` (unresolved)
  - needs manual satisfiability check: `l15_side_mem` (unresolved)
  - needs manual satisfiability check: `l15_side_eq` (unresolved)
  - needs manual satisfiability check: `l15_pair_eq` (unresolved)
  - needs manual satisfiability check: `cov_classical_C6_b` (unresolved)
  - needs manual satisfiability check: `l15_inscribed_directrix` (unresolved)
  - needs manual satisfiability check: `cov_classical_C4_b` (unresolved)
  - needs manual satisfiability check: `cov_classical_C5_b` (unresolved)
  - needs manual satisfiability check: `classical_C1` (unresolved)
  - needs manual satisfiability check: `classical_C2` (unresolved)
  - needs manual satisfiability check: `classical_C3` (unresolved)
  - needs manual satisfiability check: `classical_C4_a` (unresolved)
  - needs manual satisfiability check: `classical_C4_b` (unresolved)
  - needs manual satisfiability check: `classical_C4_c` (unresolved)
  - needs manual satisfiability check: `classical_C5_a` (unresolved)
  - needs manual satisfiability check: `classical_C5_b` (unresolved)
  - needs manual satisfiability check: `classical_C6_a` (unresolved)
  - needs manual satisfiability check: `classical_C6_b` (unresolved)
  - needs manual satisfiability check: `classical_C7_a` (unresolved)
  - needs manual satisfiability check: `classical_C7_b` (unresolved)
  - needs manual satisfiability check: `miquel_den` (unresolved)
  - needs manual satisfiability check: `miquel_den'` (unresolved)
  - needs manual satisfiability check: `circ_frame` (unresolved)
  - needs manual satisfiability check: `miquelPt_frame` (unresolved)
  - needs manual satisfiability check: `miquel_norm` (unresolved)
  - needs manual satisfiability check: `miquel` (unresolved)
  - needs manual satisfiability check: `steiner_circle_dist` (unresolved)
  - needs manual satisfiability check: `steiner_circle` (unresolved)
  - needs manual satisfiability check: `parab_frame` (unresolved)
  - needs manual satisfiability check: `dist_reflPt` (unresolved)
  - needs manual satisfiability check: `cr_zero_of_perp` (unresolved)
  - needs manual satisfiability check: `existsUnique_parabola` (unresolved)
  - needs manual satisfiability check: `simson_dir_ne` (unresolved)
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
  - needs manual satisfiability check: `perpMeet_mem` (unresolved)
  - needs manual satisfiability check: `perpMeet_perp` (unresolved)
  - needs manual satisfiability check: `norm_sub_foot` (unresolved)
  - needs manual satisfiability check: `perpMeet_spec` (unresolved)
  - needs manual satisfiability check: `dirW_ne` (unresolved)
  - needs manual satisfiability check: `onParabola_iff` (unresolved)
  - needs manual satisfiability check: `tanPt_spec` (unresolved)
  - needs manual satisfiability check: `tanPt_mem` (unresolved)
  - needs manual satisfiability check: `tanPt_onParabola` (unresolved)
  - needs manual satisfiability check: `tanPt_unique` (unresolved)
  - needs manual satisfiability check: `tanPt_all` (unresolved)
  - needs manual satisfiability check: `directrix_carrier` (unresolved)
  - needs manual satisfiability check: `foot_directrix_mem` (unresolved)
## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 412 | UNUSED 17 | NEEDED 395 | SKIP 0 | timeout 0 | bad-control decls 0

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
| gate (layer 1) | PASS (240 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 10 of 10 files ok |
| conclusion mutations (layer 4) | **709/710 rejected** (707 by error, 2 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 220 probed ok — no-hyp 104 |
| satisfiability (layer 8) | 126/324 certified [73 with hypotheses, 38 hypothesis-free binders, 15 closed], 198 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 126/324 credited, 198 unresolved |
| hypothesis ablation (layer 6) | 395 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 10 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 54 notions, 12 has-bridge, 42 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

mutation survivors (classify by hand): `orthocentres_not_all_eq'` [eq->ne@153] own proof compiled; downstream errors at lines [261]

satisfiability not certified (recorded as unresolved, not success): `fr_frac` (unresolved), `solve_A34` (unresolved), `circC_eq` (unresolved), `circ_den_ne` (unresolved), `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `centroid_triangle` (unresolved), `ortho_eq_orthocenter` (unresolved), `cr_of_collinear` (unresolved), `mem_of_collinear` (unresolved), `no123` (unresolved), `no124` (unresolved), `no134` (unresolved), `no234` (unresolved), `genPos_vertices_ne` (unresolved), `genPos_triangles` (unresolved), `mul_conj_of_dist_eq` (unresolved), `miquelPt_ne_vertices` (unresolved), `A12_not_on_circ` (unresolved), `A12_not_mem_centres` (unresolved), `miquelPt_spec` (unresolved), `miquelPt_unique` (unresolved), `foot_mem` (unresolved), `foot_perp` (unresolved), `eq_meet_of_foot_eq` (unresolved), `simson_feet_ne` (unresolved), `ortho34_eq_iff` (unresolved), `steiner_parallel_affine` (unresolved), `parallel_iff_cr` (unresolved), `diff_mem` (unresolved)
LEANCHECK DONE Thu Oct 22 09:16:39 UTC 2026
