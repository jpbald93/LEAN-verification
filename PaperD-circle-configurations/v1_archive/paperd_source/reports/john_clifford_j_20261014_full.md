# leancheck — clifford_j (2026-10-14 15:59 UTC)

- path: ~/clifford_j
- HEAD: not a git repo
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'Clifford.not_cliffordChain_of_six_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Clifford.cliffordChain_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (32 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Clifford.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    cleanand  rejected (exit 1): FAIL: build
ok    classify6 rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-10-14 10:19 PDT

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 161, "mut": 284, "killed": 283, "surv": 1, "tout": 4, "contra": 0, "sat": 112, "unres": 49, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## clifford_j
- theorems: 161
- step 1 mutants: 284 | killed 279 | killed-timeout 4 | SURVIVED 1 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 68 | no-hyp 93 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 112 | unresolved 49 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - killed by timeout `det5_mul_det3` [eq->ne@125] (heartbeat limit)
  - killed by timeout `kK_expand` [eq->ne@42] (heartbeat limit)
  - killed by timeout `cross_second` [lit2->3@283] (heartbeat limit)
  - SURVIVED detail: own proof compiled; downstream errors at lines [233]
  - SURVIVOR `cliffordChain_one` [lit1->2@15]: `CliffordChain 1` -> `CliffordChain 2`
  - killed by timeout `det4_col1` [lit1->2@113] (heartbeat limit)
  - needs manual satisfiability check: `Transversal.left_ne_zero` (unresolved)
  - needs manual satisfiability check: `Transversal.ne` (unresolved)
  - needs manual satisfiability check: `Transversal.right_ne_zero` (unresolved)
  - needs manual satisfiability check: `second_ne_zero` (unresolved)
  - needs manual satisfiability check: `mD_ne_zero` (unresolved)
  - needs manual satisfiability check: `miquel_mul` (unresolved)
  - needs manual satisfiability check: `cd_symm` (unresolved)
  - needs manual satisfiability check: `conj_miquel_mul` (unresolved)
  - needs manual satisfiability check: `gamma_cospherical` (unresolved)
  - needs manual satisfiability check: `clifford_one` (unresolved)
  - needs manual satisfiability check: `cliffordEq_miquel` (unresolved)
  - needs manual satisfiability check: `GenPos5.pos4_abcd` (unresolved)
  - needs manual satisfiability check: `GenPos5.pos4_abce` (unresolved)
  - needs manual satisfiability check: `GenPos5.pos4_abde` (unresolved)
  - needs manual satisfiability check: `GenPos5.pos4_acde` (unresolved)
  - needs manual satisfiability check: `GenPos5.pos4_bcde` (unresolved)
  - needs manual satisfiability check: `GenPos4.mD_ne_zero` (unresolved)
  - needs manual satisfiability check: `GenPos4.cliffordEq_miquel` (unresolved)
  - needs manual satisfiability check: `cycP_ne_zero_iff` (unresolved)
  - needs manual satisfiability check: `clifford_two` (unresolved)
  - needs manual satisfiability check: `genTriple_iff` (unresolved)
  - needs manual satisfiability check: `finite_roots` (unresolved)
  - needs manual satisfiability check: `pT_ne_zero` (unresolved)
  - needs manual satisfiability check: `pC_ne_zero` (unresolved)
  - needs manual satisfiability check: `GenPosN.exists_snoc` (unresolved)
  - needs manual satisfiability check: `clifford_points_on` (unresolved)
  - needs manual satisfiability check: `miquel_eq_of_kK_zero` (unresolved)
  - needs manual satisfiability check: `miquel_all_eq` (unresolved)
  - needs manual satisfiability check: `clifford_two_clean` (unresolved)
  - needs manual satisfiability check: `chain3_of` (unresolved)
  - needs manual satisfiability check: `chain4_of` (unresolved)
  - needs manual satisfiability check: `GenPosN.pos4` (unresolved)
  - needs manual satisfiability check: `GenPosN.pos5` (unresolved)
  - needs manual satisfiability check: `exists_gcircle` (unresolved)
  - needs manual satisfiability check: `q0134` (unresolved)
  - needs manual satisfiability check: `q0135` (unresolved)
  - needs manual satisfiability check: `q0234` (unresolved)
  - needs manual satisfiability check: `q0235` (unresolved)
  - needs manual satisfiability check: `q1234` (unresolved)
  - needs manual satisfiability check: `q1235` (unresolved)
  - needs manual satisfiability check: `q1245` (unresolved)
  - needs manual satisfiability check: `q1345` (unresolved)
  - needs manual satisfiability check: `q2345` (unresolved)
  - needs manual satisfiability check: `chain2_eq` (unresolved)
  - needs manual satisfiability check: `cD_eq_zero` (unresolved)
  - needs manual satisfiability check: `chain3_mem` (unresolved)
  - needs manual satisfiability check: `chain4_cD` (unresolved)
  - needs manual satisfiability check: `second_eq` (unresolved)
  - needs manual satisfiability check: `chain5_mem` (unresolved)
  - no mutants generated (manual look): GenPos5.pos4_abcd, GenPos5.pos4_abce, GenPos5.pos4_abde, GenPos5.pos4_acde, GenPos5.pos4_bcde, cd_symm, chain3_mem, clifford_one, clifford_two, clifford_two_clean, collinear_of_line, cospherical_of_eq, cospherical_or_collinear, cx_genPosN, cx_genTriple, cx_transversal, exists_gcircle, gamma_cospherical, genTriple_iff, not_cliffordChain_of_six_le, onCircleM_iff_mem_sphere, resD_id, second_onCircleM_left, second_onCircleM_right

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 63 | UNUSED 0 | NEEDED 63 | SKIP 0 | timeout 0 | bad-control decls 0


see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 6 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (32 declarations, standard axioms only) |
| tamper (layer 2) | 8/8 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 6 of 6 files ok |
| conclusion mutations (layer 4) | **283/284 rejected** (279 by error, 4 by timeout/heartbeat); 1 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 68 probed ok — no-hyp 93 |
| satisfiability (layer 8) | 112/161 certified [19 with hypotheses, 68 hypothesis-free binders, 25 closed], 49 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 112/161 credited, 49 unresolved |
| hypothesis ablation (layer 6) | 63 needed, **0 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 6 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 39 notions, 7 has-bridge, 32 NO-BRIDGE (see inventory.md) |

mutation survivors (classify by hand): `cliffordChain_one` [lit1->2@15] own proof compiled; downstream errors at lines [233]

satisfiability not certified (recorded as unresolved, not success): `Transversal.left_ne_zero` (unresolved), `Transversal.ne` (unresolved), `Transversal.right_ne_zero` (unresolved), `second_ne_zero` (unresolved), `mD_ne_zero` (unresolved), `miquel_mul` (unresolved), `cd_symm` (unresolved), `conj_miquel_mul` (unresolved), `gamma_cospherical` (unresolved), `clifford_one` (unresolved), `cliffordEq_miquel` (unresolved), `GenPos5.pos4_abcd` (unresolved), `GenPos5.pos4_abce` (unresolved), `GenPos5.pos4_abde` (unresolved), `GenPos5.pos4_acde` (unresolved), `GenPos5.pos4_bcde` (unresolved), `GenPos4.mD_ne_zero` (unresolved), `GenPos4.cliffordEq_miquel` (unresolved), `cycP_ne_zero_iff` (unresolved), `clifford_two` (unresolved), `genTriple_iff` (unresolved), `finite_roots` (unresolved), `pT_ne_zero` (unresolved), `pC_ne_zero` (unresolved), `GenPosN.exists_snoc` (unresolved), `clifford_points_on` (unresolved), `miquel_eq_of_kK_zero` (unresolved), `miquel_all_eq` (unresolved), `clifford_two_clean` (unresolved), `chain3_of` (unresolved)
LEANCHECK DONE Wed Oct 14 17:32:09 UTC 2026
