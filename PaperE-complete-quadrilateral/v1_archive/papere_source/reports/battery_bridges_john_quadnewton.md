# leancheck — quadnewton (2026-10-15 15:28 UTC)

- path: ~/quadnewton
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadNewton.parallel_iff_cr' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadNewton.genPos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (35 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: QuadNewton.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-15 08:53 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 69, "mut": 149, "killed": 149, "surv": 0, "tout": 0, "contra": 0, "sat": 51, "unres": 18, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadnewton
- theorems: 69
- step 1 mutants: 149 | killed 149 | killed-timeout 0 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 40 | no-hyp 29 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 51 | unresolved 18 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - needs manual satisfiability check: `circ_dist` (unresolved)
  - needs manual satisfiability check: `circ_eq_circumcenter` (unresolved)
  - needs manual satisfiability check: `ortho_eq_orthocenter` (unresolved)
  - needs manual satisfiability check: `genPos_triangles` (unresolved)
  - needs manual satisfiability check: `bodenmiller_coaxal` (unresolved)
  - needs manual satisfiability check: `orthocentre_line_perp_inner` (unresolved)
  - needs manual satisfiability check: `ortho_eq_of` (unresolved)
  - needs manual satisfiability check: `r_ne` (unresolved)
  - needs manual satisfiability check: `GenPos.mem` (unresolved)
  - needs manual satisfiability check: `normal_coords` (unresolved)
  - needs manual satisfiability check: `orthos_nc` (unresolved)
  - needs manual satisfiability check: `newton_gauss` (unresolved)
  - needs manual satisfiability check: `diag_midpoints_ne` (unresolved)
  - needs manual satisfiability check: `orthocentres_collinear` (unresolved)
  - needs manual satisfiability check: `orthocentres_not_all_eq` (unresolved)
  - needs manual satisfiability check: `orthos_on_line` (unresolved)
  - needs manual satisfiability check: `bodenmiller` (unresolved)
  - needs manual satisfiability check: `orthocentre_line_perp` (unresolved)
  - no mutants generated (manual look): GenPos.mem, collinear_of_param, meet_mem_left, meet_mem_right, not_concurrent_iff, orthocentres_collinear

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 51 | UNUSED 0 | NEEDED 51 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 4 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (35 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 4 of 4 files ok |
| conclusion mutations (layer 4) | **149/149 rejected** (149 by error, 0 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 40 probed ok — no-hyp 29 |
| satisfiability (layer 8) | 51/69 certified [22 with hypotheses, 29 hypothesis-free binders, 0 closed], 18 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 51/69 credited, 18 unresolved |
| hypothesis ablation (layer 6) | 51 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 4 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 10 notions, 1 has-bridge, 9 NO-BRIDGE (see inventory.md) |

satisfiability not certified (recorded as unresolved, not success): `circ_dist` (unresolved), `circ_eq_circumcenter` (unresolved), `ortho_eq_orthocenter` (unresolved), `genPos_triangles` (unresolved), `bodenmiller_coaxal` (unresolved), `orthocentre_line_perp_inner` (unresolved), `ortho_eq_of` (unresolved), `r_ne` (unresolved), `GenPos.mem` (unresolved), `normal_coords` (unresolved), `orthos_nc` (unresolved), `newton_gauss` (unresolved), `diag_midpoints_ne` (unresolved), `orthocentres_collinear` (unresolved), `orthocentres_not_all_eq` (unresolved), `orthos_on_line` (unresolved), `bodenmiller` (unresolved), `orthocentre_line_perp` (unresolved)
LEANCHECK DONE Thu Oct 15 15:58:36 UTC 2026
