# leancheck — SteinerLehmus (2026-10-13 17:36 UTC)

- path: ~/SteinerLehmus
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'SteinerLehmus.bisector_foot_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SteinerLehmus.algebraic_core' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (3 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: SteinerLehmus.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-13 10:39 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 3, "mut": 6, "killed": 6, "surv": 0, "tout": 0, "contra": 0, "sat": 0, "unres": 3, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## SteinerLehmus
- theorems: 3
- step 1 mutants: 6 | killed 6 | killed-timeout 0 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 3 | no-hyp 0 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 0 | unresolved 3 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - needs manual satisfiability check: `bisector_foot_sq` (unresolved)
  - needs manual satisfiability check: `algebraic_core` (unresolved)
  - needs manual satisfiability check: `steiner_lehmus` (unresolved)

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 11 | UNUSED 0 | NEEDED 11 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 1 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (3 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 1 of 1 files ok |
| conclusion mutations (layer 4) | **6/6 rejected** (6 by error, 0 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 3 probed ok |
| satisfiability (layer 8) | 0/3 certified [0 with hypotheses, 0 hypothesis-free binders, 0 closed], 3 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 0/3 credited, 3 unresolved |
| hypothesis ablation (layer 6) | 11 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 1 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 0 notions, 0 has-bridge, 0 NO-BRIDGE (see inventory.md) |

satisfiability not certified (recorded as unresolved, not success): `bisector_foot_sq` (unresolved), `algebraic_core` (unresolved), `steiner_lehmus` (unresolved)
LEANCHECK DONE Tue Oct 13 17:40:19 UTC 2026
