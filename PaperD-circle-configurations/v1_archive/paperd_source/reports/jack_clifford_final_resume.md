# leancheck — clifford (resumed after OOM fix, Tue Oct 13 09:03:53 PM UTC 2026)

## Layers 1-2 — gate and tamper
```
'Clifford.TT_five_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Clifford.cross54' depends on axioms: [propext, Quot.sound]
PASS (20 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Clifford.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-13 22:27 UTC

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 103, "mut": 129, "killed": 129, "surv": 0, "tout": 27, "contra": 0, "sat": 73, "unres": 30, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## clifford
- theorems: 103
- step 1 mutants: 129 | killed 102 | killed-timeout 27 | SURVIVED 0 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 38 | no-hyp 65 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 73 | unresolved 30 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `resultant_NN` [eq->ne@281] (heartbeat limit)
  - killed by timeout `den3_sec` [lit2->3@155] (heartbeat limit)
  - killed by timeout `resultant_NN` [lit2->3@250] (heartbeat limit)
  - killed by timeout `cross32` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross54` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross53` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross31` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross42` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross41` [eq->ne@119] (heartbeat limit)
  - killed by timeout `cross43` [eq->ne@119] (heartbeat limit)
  - killed by timeout `lap_cc` [lit2->3@8] (heartbeat limit)
  - killed by timeout `lap_cc` [lit2->3@92] (heartbeat limit)
  - killed by timeout `lap_cc` [lit2->3@50] (heartbeat limit)
  - killed by timeout `ZD_p45` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_p45` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_p345` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_o1` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_p345` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_o1` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_o2` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_o3` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_o2` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_o3` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_o4` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_o4` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZD_o5` [eq->ne@40] (heartbeat limit)
  - killed by timeout `ZN_o5` [eq->ne@40] (heartbeat limit)
  - needs manual satisfiability check: `circ_aux` (unresolved)
  - needs manual satisfiability check: `den3_ne_zero` (unresolved)
  - needs manual satisfiability check: `mem_circumcircle_of_TT` (unresolved)
  - needs manual satisfiability check: `mem_circumcircle_middle` (unresolved)
  - needs manual satisfiability check: `mem_circumcircle_right` (unresolved)
  - needs manual satisfiability check: `secondInter_ne_zero_iff'` (unresolved)
  - needs manual satisfiability check: `cliffordPoint_mem_gam` (unresolved)
  - needs manual satisfiability check: `clifford_one` (unresolved)
  - needs manual satisfiability check: `TT_five_2` (unresolved)
  - needs manual satisfiability check: `TT_five_1` (unresolved)
  - needs manual satisfiability check: `TT_Q` (unresolved)
  - needs manual satisfiability check: `den3_mul` (unresolved)
  - needs manual satisfiability check: `den3_of_ZD` (unresolved)
  - needs manual satisfiability check: `eq_of_cross` (unresolved)
  - needs manual satisfiability check: `ne_of_cross` (unresolved)
  - needs manual satisfiability check: `conj_ne_zero_left` (unresolved)
  - needs manual satisfiability check: `conj_ne_zero_right` (unresolved)
  - needs manual satisfiability check: `NN_ne_zero'` (unresolved)
  - needs manual satisfiability check: `triple_LL_DD` (unresolved)
  - needs manual satisfiability check: `den3_eq_zero_of_collinear` (unresolved)
  - needs manual satisfiability check: `collinear_of_TT` (unresolved)
  - needs manual satisfiability check: `cliffordPoint_mem_gams` (unresolved)
  - needs manual satisfiability check: `clifford_two_explicit` (unresolved)
  - needs manual satisfiability check: `clifford_two` (unresolved)
  - needs manual satisfiability check: `five_NN` (unresolved)
  - needs manual satisfiability check: `WW_ne_zero_of` (unresolved)
  - needs manual satisfiability check: `cliffordPoint₃_mem` (unresolved)
  - needs manual satisfiability check: `five_mem_circumcircle` (unresolved)
  - needs manual satisfiability check: `ZD_ne_zero` (unresolved)
  - needs manual satisfiability check: `clifford_three` (unresolved)
  - no mutants generated (manual look): circ_throughOrigin, cliffordPoint_mem_gam, cliffordPoint_mem_gams, cliffordPoint₃_mem, clifford_one, clifford_three, clifford_two, clifford_two_explicit, collinear_of_TT, collinear_of_den3_eq_zero, five_mem_circumcircle, mem_circumcircle_left, mem_circumcircle_middle, mem_circumcircle_of_TT, mem_circumcircle_right, secondInter_mem_left, secondInter_mem_right

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 325 | UNUSED 15 | NEEDED 310 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `clifford_two_explicit` : `(n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))`
- UNUSED `clifford_two_explicit` : `(n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `clifford_two_explicit` : `(n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))`
- UNUSED `clifford_two_explicit` : `(n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `clifford_two_explicit` : `(n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `five_NN` : `(n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))`
- UNUSED `ZD_ne_zero` : `(n156 : ¬ Collinear ℝ ({secondInter c₁ c₅, secondInter c₁ c₆, secondInter c₅ c₆} : Set ℂ))`
- UNUSED `ZD_ne_zero` : `(n256 : ¬ Collinear ℝ ({secondInter c₂ c₅, secondInter c₂ c₆, secondInter c₅ c₆} : Set ℂ))`
- UNUSED `ZD_ne_zero` : `(n356 : ¬ Collinear ℝ ({secondInter c₃ c₅, secondInter c₃ c₆, secondInter c₅ c₆} : Set ℂ))`
- UNUSED `ZD_ne_zero` : `(n456 : ¬ Collinear ℝ ({secondInter c₄ c₅, secondInter c₄ c₆, secondInter c₅ c₆} : Set ℂ))`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 2 files
linter (scratch): 0 warnings in 10 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (20 declarations, standard axioms only) |
| tamper (layer 2) | 8/8 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 2 of 2 files ok |
| conclusion mutations (layer 4) | **129/129 rejected** (102 by error, 27 by timeout/heartbeat); 0 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 38 probed ok — no-hyp 65 |
| satisfiability (layer 8) | 73/103 certified [8 with hypotheses, 65 hypothesis-free binders, 0 closed], 30 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 73/103 credited, 30 unresolved |
| hypothesis ablation (layer 6) | 310 needed, **15 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 2 files |
| linter, scratch (layer 7) | 0 warnings in 10 files, nonzero exit: scratch/MasterTest.lean, scratch/T3.lean, scratch/T4.lean, scratch/T6.lean, scratch/TB.lean |
| bridge inventory (layer 9) | 27 notions, 2 has-bridge, 25 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `clifford_two_explicit`: (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ)), `clifford_two_explicit`: (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ)), `clifford_two_explicit`: (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ)), `clifford_two_explicit`: (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ)), `clifford_two_explicit`: (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)), `five_NN`: (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ)), `five_NN`: (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ)), `five_NN`: (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ)), `five_NN`: (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ)), `five_NN`: (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ)), `five_NN`: (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)), `ZD_ne_zero`: (n156 : ¬ Collinear ℝ ({secondInter c₁ c₅, secondInter c₁ c₆, secondInter c₅ c₆} : Set ℂ))

satisfiability not certified (recorded as unresolved, not success): `circ_aux` (unresolved), `den3_ne_zero` (unresolved), `mem_circumcircle_of_TT` (unresolved), `mem_circumcircle_middle` (unresolved), `mem_circumcircle_right` (unresolved), `secondInter_ne_zero_iff'` (unresolved), `cliffordPoint_mem_gam` (unresolved), `clifford_one` (unresolved), `TT_five_2` (unresolved), `TT_five_1` (unresolved), `TT_Q` (unresolved), `den3_mul` (unresolved), `den3_of_ZD` (unresolved), `eq_of_cross` (unresolved), `ne_of_cross` (unresolved), `conj_ne_zero_left` (unresolved), `conj_ne_zero_right` (unresolved), `NN_ne_zero'` (unresolved), `triple_LL_DD` (unresolved), `den3_eq_zero_of_collinear` (unresolved), `collinear_of_TT` (unresolved), `cliffordPoint_mem_gams` (unresolved), `clifford_two_explicit` (unresolved), `clifford_two` (unresolved), `five_NN` (unresolved), `WW_ne_zero_of` (unresolved), `cliffordPoint₃_mem` (unresolved), `five_mem_circumcircle` (unresolved), `ZD_ne_zero` (unresolved), `clifford_three` (unresolved)
LEANCHECK DONE Wed Oct 14 02:13:50 AM UTC 2026
