# leancheck — Fivecircles (2026-10-13 18:12 UTC)

- path: ~/Fivecircles
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'Fivecircles.concyclic_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fivecircles.collinear_of' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (6 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Fivecircles.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-13 11:23 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 20, "mut": 36, "killed": 36, "surv": 0, "tout": 0, "contra": 0, "sat": 15, "unres": 5, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## Fivecircles
- theorems: 20
- step 1 mutants: 36 | killed 36 | killed-timeout 0 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 16 | no-hyp 4 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 15 | unresolved 5 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - needs manual satisfiability check: `col3_of_collinear` (unresolved)
  - needs manual satisfiability check: `cd_of_concyclic` (unresolved)
  - needs manual satisfiability check: `concyclic_of` (unresolved)
  - needs manual satisfiability check: `core` (unresolved)
  - needs manual satisfiability check: `fivecircles` (unresolved)
  - no mutants generated (manual look): collinear_of, concyclic_of, fivecircles

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 38 | UNUSED 0 | NEEDED 38 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 1 files
linter (scratch): 0 warnings in 8 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (6 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 1 of 1 files ok |
| conclusion mutations (layer 4) | **36/36 rejected** (36 by error, 0 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 16 probed ok — no-hyp 4 |
| satisfiability (layer 8) | 15/20 certified [11 with hypotheses, 4 hypothesis-free binders, 0 closed], 5 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 15/20 credited, 5 unresolved |
| hypothesis ablation (layer 6) | 38 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 1 files |
| linter, scratch (layer 7) | 0 warnings in 8 files, nonzero exit: scratch/Basic2.lean, scratch/Basic3.lean, scratch/Basic4.lean, scratch/core_hdr.lean, scratch/main_tail.lean |
| bridge inventory (layer 9) | 3 notions, 1 has-bridge, 2 NO-BRIDGE (see inventory.md) |

satisfiability not certified (recorded as unresolved, not success): `col3_of_collinear` (unresolved), `cd_of_concyclic` (unresolved), `concyclic_of` (unresolved), `core` (unresolved), `fivecircles` (unresolved)
LEANCHECK DONE Tue Oct 13 18:30:24 UTC 2026
