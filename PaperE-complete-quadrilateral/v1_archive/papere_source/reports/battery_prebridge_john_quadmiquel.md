# leancheck — quadmiquel (2026-10-14 23:31 UTC)

- path: ~/quadmiquel
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.circC_T4' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.solve_A34' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (32 declarations, standard axioms only)
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

Generated 2026-10-14 17:09 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 75, "mut": 152, "killed": 152, "surv": 0, "tout": 2, "contra": 0, "sat": 57, "unres": 18, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## quadmiquel
- theorems: 75
- step 1 mutants: 152 | killed 150 | killed-timeout 2 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 51 | no-hyp 24 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 57 | unresolved 18 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `steinM` [eq->ne@67] (heartbeat limit)
  - killed by timeout `foot_shift0` [lit0->1@99] (heartbeat limit)
  - needs manual satisfiability check: `solve_A34` (unresolved)
  - needs manual satisfiability check: `circC_eq` (unresolved)
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
  - no mutants generated (manual look): meet_mem_left, meet_mem_right, miquel, simson, steiner_circle

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 142 | UNUSED 17 | NEEDED 125 | SKIP 0 | timeout 0 | bad-control decls 0

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
linter (library): 0 warnings in 4 files
linter (scratch): 0 warnings in 5 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (32 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 4 of 4 files ok |
| conclusion mutations (layer 4) | **152/152 rejected** (150 by error, 2 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 51 probed ok — no-hyp 24 |
| satisfiability (layer 8) | 57/75 certified [33 with hypotheses, 24 hypothesis-free binders, 0 closed], 18 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 57/75 credited, 18 unresolved |
| hypothesis ablation (layer 6) | 125 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 4 files |
| linter, scratch (layer 7) | 0 warnings in 5 files, nonzero exit: scratch/Core.lean |
| bridge inventory (layer 9) | 11 notions, 1 has-bridge, 10 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

satisfiability not certified (recorded as unresolved, not success): `solve_A34` (unresolved), `circC_eq` (unresolved), `diff_mem` (unresolved), `on_line` (unresolved), `not_mem_ne` (unresolved), `frame_pts` (unresolved), `frame` (unresolved), `miquelPt_frame` (unresolved), `circ_frame` (unresolved), `miquel_norm` (unresolved), `miquel` (unresolved), `steiner_circle_dist` (unresolved), `steiner_circle` (unresolved), `foot_eq` (unresolved), `feet_frame` (unresolved), `simson_cr` (unresolved), `simson` (unresolved), `steiner_parallel` (unresolved)
LEANCHECK DONE Thu Oct 15 00:40:54 UTC 2026
