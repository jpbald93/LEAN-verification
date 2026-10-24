# leancheck — quadnewton (2026-10-15 00:40 UTC)

- path: ~/quadnewton
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadNewton.dv_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadNewton.r_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (22 declarations, standard axioms only)
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

Generated 2026-10-14 18:00 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 52, "mut": 110, "killed": 110, "surv": 0, "tout": 0, "contra": 0, "sat": 38, "unres": 14, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadnewton
- theorems: 52
- step 1 mutants: 110 | killed 110 | killed-timeout 0 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 29 | no-hyp 23 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 38 | unresolved 14 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - needs manual satisfiability check: `ortho_eq_of` (unresolved)
  - needs manual satisfiability check: `r_ne` (unresolved)
  - needs manual satisfiability check: `diff_of_mem` (unresolved)
  - needs manual satisfiability check: `GenPos.mem` (unresolved)
  - needs manual satisfiability check: `normal_coords` (unresolved)
  - needs manual satisfiability check: `collinear_of_param` (unresolved)
  - needs manual satisfiability check: `orthos_nc` (unresolved)
  - needs manual satisfiability check: `newton_gauss` (unresolved)
  - needs manual satisfiability check: `diag_midpoints_ne` (unresolved)
  - needs manual satisfiability check: `orthocentres_collinear` (unresolved)
  - needs manual satisfiability check: `orthocentres_not_all_eq` (unresolved)
  - needs manual satisfiability check: `orthos_on_line` (unresolved)
  - needs manual satisfiability check: `bodenmiller` (unresolved)
  - needs manual satisfiability check: `orthocentre_line_perp` (unresolved)
  - no mutants generated (manual look): GenPos.mem, collinear_of_param, meet_mem_left, meet_mem_right, orthocentres_collinear

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 41 | UNUSED 0 | NEEDED 41 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 3 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (22 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 3 of 3 files ok |
| conclusion mutations (layer 4) | **110/110 rejected** (110 by error, 0 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 29 probed ok — no-hyp 23 |
| satisfiability (layer 8) | 38/52 certified [15 with hypotheses, 23 hypothesis-free binders, 0 closed], 14 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 38/52 credited, 14 unresolved |
| hypothesis ablation (layer 6) | 41 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 3 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 8 notions, 1 has-bridge, 7 NO-BRIDGE (see inventory.md) |

satisfiability not certified (recorded as unresolved, not success): `ortho_eq_of` (unresolved), `r_ne` (unresolved), `diff_of_mem` (unresolved), `GenPos.mem` (unresolved), `normal_coords` (unresolved), `collinear_of_param` (unresolved), `orthos_nc` (unresolved), `newton_gauss` (unresolved), `diag_midpoints_ne` (unresolved), `orthocentres_collinear` (unresolved), `orthocentres_not_all_eq` (unresolved), `orthos_on_line` (unresolved), `bodenmiller` (unresolved), `orthocentre_line_perp` (unresolved)
LEANCHECK DONE Thu Oct 15 01:05:11 UTC 2026
